module

public import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction
import CFSG.LocalAnalysis.SolvableSignalizer.Compatible

public section

namespace CFSG.SolvableSignalizer

open scoped Pointwise

section Restriction

variable {A G : Type*} [Group A] [Group G]

private theorem isSolvable_map_subtype_iff (H : Subgroup G) (U : Subgroup H) :
    Group.IsSolvable (U.map H.subtype) ↔ Group.IsSolvable U := by
  let e := U.equivMapOfInjective H.subtype H.subtype_injective
  exact ⟨fun _ => Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective,
    fun _ => Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective⟩

private theorem map_fixedIn_restrictAction (α : A →* MulAut G) (H : Subgroup G)
    (hH : IsInvariant α H) (U : Subgroup H) (a : A) :
    (fixedIn (restrictAction α H hH) U a).map H.subtype = fixedIn α (U.map H.subtype) a := by
  rw [fixedIn, fixedIn, Subgroup.map_inf _ _ _ H.subtype_injective,
    fixedSubgroup_restrictAction_map_subtype, fixedIn, ← inf_assoc,
    inf_eq_left.mpr (Subgroup.map_subtype_le U)]

theorem compatible_restrict_iff {p : ℕ} {α : A →* MulAut G} {θ : A → Subgroup G}
    {H : Subgroup G} (hH : IsInvariant α H) (U : Subgroup H) :
    Compatible p (restrictAction α H hH) (restrictTheta θ H) U ↔
      Compatible p α θ (U.map H.subtype) := by
  rw [Compatible, Compatible, isInvariant_restrictAction_iff, isSolvable_map_subtype_iff,
    Subgroup.card_map_of_injective H.subtype_injective]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    forall₂_congr fun a ha => ?_
  rw [← Subgroup.map_le_map_iff_of_injective H.subtype_injective, map_fixedIn_restrictAction,
    restrictTheta_map_subtype, le_inf_iff, and_iff_left]
  exact inf_le_left.trans (Subgroup.map_subtype_le U)

end Restriction

universe u v

section Datum

variable {A : Type u} {G : Type v} [CommGroup A] [Finite A] [Group G] [Finite G]
variable {p : ℕ} {α : A →* MulAut G} {θ : A → Subgroup G}

theorem Datum.restrict (d : Datum p α θ)
    (H : Subgroup G) (hH : IsInvariant α H) :
    Datum p (restrictAction α H hH) (restrictTheta θ H) ∧
      (fun U : Subgroup H => U.map H.subtype) ''
        {U : Subgroup H | Compatible p (restrictAction α H hH) (restrictTheta θ H) U} =
      {U : Subgroup G | Compatible p α θ U ∧ U ≤ H} := by
  refine ⟨⟨d.prime, d.exponent, d.rank_two, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
    fun a ha x hx => ?_, fun a b ha hb => ?_⟩, ?_⟩
  · rw [isInvariant_restrictAction_iff, restrictTheta_map_subtype]
    exact (d.invariant a ha).inf hH
  · rw [← isSolvable_map_subtype_iff, restrictTheta_map_subtype]
    have := d.solvable a ha
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left)
  · rw [card_restrictTheta]
    exact (d.coprime a ha).of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  · exact Subtype.ext (d.central a ha hx)
  · rw [← Subgroup.map_le_map_iff_of_injective H.subtype_injective, map_fixedIn_restrictAction,
      restrictTheta_map_subtype, restrictTheta_map_subtype]
    exact le_inf ((inf_le_inf_right _ inf_le_left).trans (d.balance a b ha hb))
      (inf_le_left.trans inf_le_right)
  · ext V
    constructor
    · rintro ⟨U, hU, rfl⟩
      exact ⟨(compatible_restrict_iff hH U).mp hU, Subgroup.map_subtype_le U⟩
    · rintro ⟨hV, hVH⟩
      refine ⟨V.subgroupOf H, ?_, Subgroup.map_subgroupOf_eq_of_le hVH⟩
      rwa [Set.mem_ofPred_eq, compatible_restrict_iff, Subgroup.map_subgroupOf_eq_of_le hVH]

theorem IsComplete.restrict (d : Datum p α θ)
    (complete : IsComplete p α θ) (H : Subgroup G) (hH : IsInvariant α H) :
    IsComplete p (restrictAction α H hH) (restrictTheta θ H) ∧
      (completion (restrictTheta θ H)).map H.subtype = completion θ ⊓ H := by
  have hM : Compatible p (restrictAction α H hH) (restrictTheta θ H)
      ((completion θ).subgroupOf H) := by
    rw [compatible_restrict_iff, Subgroup.subgroupOf_map_subtype]
    exact Compatible.of_le_of_isInvariant d complete inf_le_left (complete.1.inf hH)
  have heq : completion (restrictTheta θ H) = (completion θ).subgroupOf H :=
    le_antisymm (iSup₂_le fun a ha => Subgroup.subgroupOf_mono H
        (le_iSup₂ (f := fun a (_ : a ≠ 1) => θ a) a ha))
      (eq_completionIn_and_le_completion (Datum.restrict d H hH).1 hM).2
  rw [IsComplete, heq, Subgroup.subgroupOf_map_subtype]
  exact ⟨hM, rfl⟩

end Datum

section Quotient

variable {A G : Type*} [Group A] [Group G]

private theorem isInvariant_map_mk {α : A →* MulAut G} (N : Subgroup G) [N.Normal]
    (hN : IsInvariant α N) {H : Subgroup G} (hH : IsInvariant α H) :
    IsInvariant (quotientAction α N hN) (H.map (QuotientGroup.mk' N)) := fun a => by
  have heq : (quotientAction α N hN a).toMonoidHom.comp (QuotientGroup.mk' N) =
      (QuotientGroup.mk' N).comp (α a).toMonoidHom := rfl
  rw [Subgroup.map_map, heq, ← Subgroup.map_map, hH a]

private noncomputable def zpowersAction (α : A →* MulAut G) (a : A) :
    Subgroup.zpowers a →* MulAut G :=
  α.comp (Subgroup.zpowers a).subtype

private theorem actionFixedAll_zpowersAction (α : A →* MulAut G) (a : A) :
    actionFixedAll (zpowersAction α a) = fixedSubgroup α a := by
  ext g
  rw [actionFixedAll, mem_fixedBySubgroup, mem_fixedSubgroup]
  refine ⟨fun h => h ⟨a, Subgroup.mem_zpowers a⟩ (Subgroup.mem_top _), fun h b _ => ?_⟩
  have hle : Subgroup.zpowers a ≤ (MulAction.stabilizer (MulAut G) g).comap α :=
    Subgroup.zpowers_le.mpr h
  exact hle b.property

private theorem isPGroup_zpowers {p : ℕ} (a : A) (ha : a ^ p = 1) :
    IsPGroup p (Subgroup.zpowers a) := by
  apply IsPGroup.of_card_dvd_pow (n := 1)
  rw [Nat.card_zpowers, pow_one]
  exact orderOf_dvd_of_pow_eq_one ha

end Quotient

section Datum

variable {A : Type u} {G : Type v} [CommGroup A] [Finite A] [Group G] [Finite G]
variable {p : ℕ} {α : A →* MulAut G} {θ : A → Subgroup G}

private theorem fixedIn_map_mk_le (d : Datum p α θ)
    (N : Subgroup G) [N.Normal] (hN : IsInvariant α N)
    (H : Subgroup G) (hH : IsInvariant α H) (hcop : Nat.Coprime p (Nat.card H)) (a : A) :
    fixedIn (quotientAction α N hN) (H.map (QuotientGroup.mk' N)) a ≤
      (fixedIn α H a).map (QuotientGroup.mk' N) := by
  let Q := H.map (QuotientGroup.mk' N)
  let B := Subgroup.zpowers a
  let _ : MulDistribMulAction B H :=
    MulDistribMulAction.compHom H ((restrictAction α H hH).comp B.subtype)
  let _ : MulDistribMulAction B Q := MulDistribMulAction.compHom Q
    ((restrictAction (quotientAction α N hN) Q (isInvariant_map_mk N hN hH)).comp B.subtype)
  have hB : IsPGroup p B := fun b => ⟨1, by rw [pow_one]; exact Subtype.ext (d.exponent b.val)⟩
  let f : H →* Q := (QuotientGroup.mk' N).subgroupMap H
  have hk : Nat.Coprime p (Nat.card f.ker) :=
    hcop.of_dvd_right (Subgroup.card_subgroup_dvd_card f.ker)
  rintro x ⟨hxH, hxa⟩
  have hfixed (b : B) : b • (⟨x, hxH⟩ : Q) = ⟨x, hxH⟩ := by
    obtain ⟨k, hkb⟩ := Subgroup.mem_zpowers_iff.mp b.property
    apply Subtype.ext
    change quotientAction α N hN b.val x = x
    rw [← hkb, map_zpow]
    exact MulAction.mem_fixedBy_zpow (α := G ⧸ N) (G := MulAut (G ⧸ N)) hxa k
  obtain ⟨y, hy, hyfixed⟩ := CFSG.SignalizerFunctor.Helpers.fixed_point_lifts p d.prime
    hB f ((QuotientGroup.mk' N).subgroupMap_surjective H) (fun _ _ => rfl) hk _ hfixed
  exact ⟨y.val, ⟨y.property, congrArg Subtype.val (hyfixed ⟨a, Subgroup.mem_zpowers a⟩)⟩,
    congrArg Subtype.val hy⟩

theorem Datum.quotient (d : Datum p α θ)
    (N : Subgroup G) [N.Normal] (hN : IsInvariant α N) :
    Datum p (quotientAction α N hN) (quotientTheta θ N) ∧
      (∀ H : Subgroup G, Compatible p α θ H →
        Compatible p (quotientAction α N hN) (quotientTheta θ N)
          (H.map (QuotientGroup.mk' N))) ∧
      spectrum (quotientTheta θ N) ⊆ spectrum θ := by
  refine ⟨⟨d.prime, d.exponent, d.rank_two, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
    fun a ha x hx => ?_, fun a b ha hb => ?_⟩, ?_, ?_⟩
  · exact isInvariant_map_mk N hN (d.invariant a ha)
  · have := d.solvable a ha
    exact Group.isSolvable_of_surjective ((QuotientGroup.mk' N).subgroupMap_surjective (θ a))
  · exact (d.coprime a ha).of_dvd_right ((θ a).card_map_dvd (QuotientGroup.mk' N))
  · obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact congrArg (QuotientGroup.mk' N) (d.central a ha hy)
  · exact (fixedIn_map_mk_le d N hN (θ a) (d.invariant a ha) (d.coprime a ha) b).trans
      (Subgroup.map_mono (d.balance a b ha hb))
  · rintro H ⟨hH, hsol, hcop, hfix⟩
    exact ⟨isInvariant_map_mk N hN hH,
      Group.isSolvable_of_surjective ((QuotientGroup.mk' N).subgroupMap_surjective H),
      hcop.of_dvd_right (H.card_map_dvd (QuotientGroup.mk' N)),
      fun a ha => (fixedIn_map_mk_le d N hN H hH hcop a).trans (Subgroup.map_mono (hfix a ha))⟩
  · rintro q ⟨hq, a, ha, hqa⟩
    exact ⟨hq, a, ha, hqa.trans ((θ a).card_map_dvd (QuotientGroup.mk' N))⟩

theorem compatible_iff_compatible_map_quotient (d : Datum p α θ)
    (N : Subgroup G) [N.Normal] (hN : Compatible p α θ N)
    (U : Subgroup G) (hNU : N ≤ U) :
    Compatible p α θ U ↔
      Compatible p (quotientAction α N hN.1) (quotientTheta θ N)
        (U.map (QuotientGroup.mk' N)) := by
  refine ⟨(Datum.quotient d N hN.1).2.1 U, ?_⟩
  rintro ⟨hUinv, hUsolv, hUcop, hUfix⟩
  have hUeq : (U.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = U :=
    Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])
  refine ⟨fun a => ?_, ?_, ?_, fun a ha => ?_⟩
  · rw [← hUeq]
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      have h : quotientAction α N hN.1 a (QuotientGroup.mk' N y) ∈
          (U.map (QuotientGroup.mk' N)).map (quotientAction α N hN.1 a).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hy
      rwa [hUinv a, quotientAction_apply_mk] at h
    · intro x hx
      refine ⟨α a⁻¹ x, ?_, by simp⟩
      have h : quotientAction α N hN.1 a⁻¹ (QuotientGroup.mk' N x) ∈
          (U.map (QuotientGroup.mk' N)).map (quotientAction α N hN.1 a⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rwa [hUinv a⁻¹, quotientAction_apply_mk] at h
  · have : Group.IsSolvable N := hN.2.1
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNU)
      ((QuotientGroup.mk' N).subgroupMap U) ?_
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk', Subgroup.inclusion_range]
  · have hcard : Nat.card U = Nat.card N * Nat.card (U.map (QuotientGroup.mk' N)) := by
      have h := Subgroup.card_ker_mul_card_of_surjective
        ((QuotientGroup.mk' N).subgroupMap_surjective U)
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk',
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNU).toEquiv] at h
      exact h.symm
    rw [hcard]
    exact hN.2.2.1.mul_right hUcop
  ·
    intro u hu
    rw [mem_fixedIn] at hu
    obtain ⟨huU, hufix⟩ := hu
    have hθ := hUfix a ha ((mem_fixedIn _ _ _ _).mpr
      ⟨Subgroup.mem_map_of_mem _ huU, by rw [quotientAction_apply_mk, hufix]⟩)
    rw [quotientTheta, Subgroup.mem_map] at hθ
    obtain ⟨t, htθ, ht⟩ := hθ
    obtain ⟨z, hzN, htz⟩ := (QuotientGroup.mk'_eq_mk' (N := N)).mp ht
    have hprod : u ∈ (N : Set G) * (θ a : Set G) := by
      rw [← Subgroup.set_mul_normal_comm (θ a : Set G) N]
      exact ⟨t, htθ, z, hzN, htz⟩
    have hcop : ¬ p ∣ Nat.card (N ⊓ θ a : Subgroup G) := fun hd =>
      (d.prime.coprime_iff_not_dvd.mp hN.2.2.1) (hd.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hmem : u ∈ ((N : Set G) * (θ a : Set G)) ∩
        (actionFixedAll (zpowersAction α a) : Set G) :=
      ⟨hprod, by rwa [SetLike.mem_coe, actionFixedAll_zpowersAction]⟩
    rw [mul_inter_actionFixedAll_eq p d.prime (isPGroup_zpowers a (d.exponent a))
      (zpowersAction α a) N (θ a) (fun x => hN.1 x) (fun x => d.invariant a ha x) hcop] at hmem
    obtain ⟨n, hn, t', ht', rfl⟩ := hmem
    rw [actionFixedAllIn, actionFixedAll_zpowersAction] at hn ht'
    exact (θ a).mul_mem (hN.2.2.2 a ha hn) ht'.1

theorem isComplete_quotient_iff (d : Datum p α θ)
    (N : Subgroup G) [N.Normal] (hN : Compatible p α θ N) :
    (IsComplete p α θ ↔
      IsComplete p (quotientAction α N hN.1) (quotientTheta θ N)) ∧
    completion (quotientTheta θ N) = (completion θ).map (QuotientGroup.mk' N) ∧
    (IsComplete p α θ →
      completion θ = (completion (quotientTheta θ N)).comap (QuotientGroup.mk' N)) := by
  have hgen : completion (quotientTheta θ N) = (completion θ).map (QuotientGroup.mk' N) := by
    simp only [completion, quotientTheta, Subgroup.map_iSup]
  have hNle : N ≤ completion θ := (eq_completionIn_and_le_completion d hN).2
  refine ⟨?_, hgen, fun _ => ?_⟩
  · rw [IsComplete, IsComplete, hgen]
    exact compatible_iff_compatible_map_quotient d N hN (completion θ) hNle
  · rw [hgen]
    exact (Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])).symm

end Datum

end CFSG.SolvableSignalizer
