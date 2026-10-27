module

public import CFSG.RankThree.PartTwo.Sec14.Item1411Strong
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.KFacts.KS14HJLocal
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec17.Item1730Glue
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Star

omit [Finite G] in
theorem scriptQPiStar_two_eq {A L : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hQ : ∀ U ∈ invariantPiSubgroups L A (piOf 2), U ∈ scriptQ A LB) :
    scriptQPiStar A LB L (piOf 2) = maxInvariantPiSubgroups L A (piOf 2) := by
  have h : scriptQPi A LB L (piOf 2) = invariantPiSubgroups L A (piOf 2) := by
    ext U
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h2, h3, h1.1.2.2⟩, fun hU => ⟨⟨hQ U hU, hU.1⟩, hU.2.1⟩⟩
  simp only [scriptQPiStar, maxInvariantPiSubgroups, h]

omit [Finite G] in
theorem isPiSubgroup_piCompl_three_of_piOf_two {U : Subgroup G}
    (hU : IsPiSubgroup (piOf 2) U) : IsPiSubgroup (piCompl 3) U := by
  intro q hq
  have h2 : (q : ℕ) = 2 := hU q hq
  show (q : ℕ) ≠ 3
  omega

theorem mem_scriptQ_of_first142 {A L : Subgroup G} {LB : Subgroup G → Subgroup G} {c : G}
    (h142 : ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3), Q ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {c}))
    (hLc : L ≤ Subgroup.centralizer {c}) {U : Subgroup G}
    (hU : U ∈ invariantPiSubgroups L A (piOf 2)) : U ∈ scriptQ A LB := by
  have hU' : U ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3) :=
    ⟨hU.1.trans (hLc.trans (centralizer_singleton_le_normalizer_zpowers c)),
      isPiSubgroup_piCompl_three_of_piOf_two hU.2.1, hU.2.2⟩
  obtain ⟨Q, hQ, hUQ⟩ := exists_le_mem_maxInvariantPiSubgroups hU'
  exact mem_scriptQ_of_le (h142 Q hQ).1 hUQ hU.2.2

end Star

section Transport

variable {A L : Subgroup G} {X : Type} [Group X] (π : ↥L →* X)

omit [Finite G] in
theorem subgroupOf_le_normalizer_subgroupOf {U : Subgroup G}
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) :
    A.subgroupOf L ≤ Subgroup.normalizer ((U.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa using Subgroup.mem_normalizer_iff.mp (hAU (Subgroup.mem_subgroupOf.mp ha)) (h : G)

omit [Finite G] in
theorem map_le_normalizer_map {U : Subgroup G} (hAU : A ≤ Subgroup.normalizer (U : Set G)) :
    (A.subgroupOf L).map π ≤
      Subgroup.normalizer (((U.subgroupOf L).map π : Subgroup X) : Set X) :=
  (Subgroup.map_mono (subgroupOf_le_normalizer_subgroupOf hAU)).trans
    (Subgroup.le_normalizer_map π)

omit [Finite G] in
theorem inf_le_normalizer_map_comap {W : Subgroup X}
    (hW : (A.subgroupOf L).map π ≤ Subgroup.normalizer (W : Set X)) :
    A ⊓ L ≤ Subgroup.normalizer (((W.comap π).map L.subtype : Subgroup G) : Set G) := by
  intro a ha
  have ha' : (⟨a, ha.2⟩ : ↥L) ∈ Subgroup.normalizer ((W.comap π : Subgroup ↥L) : Set ↥L) :=
    Subgroup.le_normalizer_comap π (hW ⟨⟨a, ha.2⟩, Subgroup.mem_subgroupOf.mpr ha.1, rfl⟩)
  exact Subgroup.le_normalizer_map L.subtype ⟨⟨a, ha.2⟩, ha', rfl⟩

omit [Finite G] in
theorem isPGroup_map_subgroupOf {U : Subgroup G} (hUL : U ≤ L) (hU : IsPGroup 2 U) :
    IsPGroup 2 ((U.subgroupOf L).map π) :=
  (hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUL).symm).map π

omit [Finite G] in
theorem isPGroup_map_comap {W : Subgroup X} (hW : IsPGroup 2 W) (hker : IsPGroup 2 π.ker) :
    IsPGroup 2 ((W.comap π).map L.subtype) :=
  (hW.comap_of_ker_isPGroup π hker).map L.subtype

omit [Finite G] in
theorem map_subgroupOf_map_comap (hπ : Function.Surjective π) (W : Subgroup X) :
    (((W.comap π).map L.subtype).subgroupOf L).map π = W := by
  have h : ((W.comap π).map L.subtype).subgroupOf L = W.comap π :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  rw [h, Subgroup.map_comap_eq_self_of_surjective hπ]

omit [Finite G] in
theorem le_map_comap_map {U : Subgroup G} (hUL : U ≤ L) :
    U ≤ (((U.subgroupOf L).map π).comap π).map L.subtype := by
  intro u hu
  exact ⟨⟨u, hUL hu⟩, Subgroup.le_comap_map π _ (Subgroup.mem_subgroupOf.mpr hu), rfl⟩

theorem maxInvariant_two_transport (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    (hAinv : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G)) :
    (∀ U ∈ maxInvariantPiSubgroups L A (piOf 2),
      (U.subgroupOf L).map π ∈ maxInvariantPiSubgroups ⊤ ((A.subgroupOf L).map π) (piOf 2) ∧
        (((U.subgroupOf L).map π).comap π).map L.subtype = U) ∧
    (∀ W ∈ maxInvariantPiSubgroups ⊤ ((A.subgroupOf L).map π) (piOf 2),
      (W.comap π).map L.subtype ∈ maxInvariantPiSubgroups L A (piOf 2)) := by
  have : Finite X := Finite.of_surjective π hπ
  have hf : ∀ U ∈ invariantPiSubgroups L A (piOf 2),
      (U.subgroupOf L).map π ∈ invariantPiSubgroups ⊤ ((A.subgroupOf L).map π) (piOf 2) := by
    intro U hU
    refine ⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr ?_, map_le_normalizer_map π hU.2.2⟩
    exact isPGroup_map_subgroupOf π hU.1 ((isPiSubgroup_piOf_iff Nat.prime_two _).mp hU.2.1)
  have hg : ∀ W ∈ invariantPiSubgroups ⊤ ((A.subgroupOf L).map π) (piOf 2),
      (W.comap π).map L.subtype ∈ invariantPiSubgroups L A (piOf 2) := by
    intro W hW
    refine ⟨Subgroup.map_subtype_le _, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr ?_,
      hAinv _ (Subgroup.map_subtype_le _) (inf_le_normalizer_map_comap π hW.2.2)⟩
    exact isPGroup_map_comap π ((isPiSubgroup_piOf_iff Nat.prime_two _).mp hW.2.1) hker
  have hfg := map_subgroupOf_map_comap π hπ
  have hgf : ∀ U ∈ maxInvariantPiSubgroups L A (piOf 2),
      (((U.subgroupOf L).map π).comap π).map L.subtype = U := fun U hU =>
    (hU.eq_of_le (hg _ (hf U hU.prop)) (le_map_comap_map π hU.prop.1)).symm
  refine ⟨fun U hU => ⟨⟨hf U hU.prop, fun W hW hUW => ?_⟩, hgf U hU⟩,
    fun W hW => ⟨hg W hW.prop, fun U hU hWU => ?_⟩⟩
  ·
    have h1 : U ≤ (W.comap π).map L.subtype := by
      rw [← hgf U hU]
      exact Subgroup.map_mono (Subgroup.comap_mono hUW)
    have h2 := hU.eq_of_le (hg W hW) h1
    rw [← hfg W, ← h2]
  ·
    have h1 : W ≤ (U.subgroupOf L).map π := by
      rw [← hfg W]
      exact Subgroup.map_mono (Subgroup.comap_mono hWU)
    have h2 := hW.eq_of_le (hf U hU) h1
    calc U ≤ (((U.subgroupOf L).map π).comap π).map L.subtype := le_map_comap_map π hU.1
      _ = (W.comap π).map L.subtype := by rw [← h2]

theorem maxInvariant_two_ncard_eq (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    (hAinv : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G)) :
    (maxInvariantPiSubgroups L A (piOf 2)).ncard =
        (maxInvariantPiSubgroups ⊤ ((A.subgroupOf L).map π) (piOf 2)).ncard ∧
      ((∀ V₁ ∈ maxInvariantPiSubgroups ⊤ ((A.subgroupOf L).map π) (piOf 2),
          ∀ V₂ ∈ maxInvariantPiSubgroups ⊤ ((A.subgroupOf L).map π) (piOf 2),
            V₁ ≠ V₂ → V₁ ⊓ V₂ ≠ ⊥) →
        ∀ U₁ ∈ maxInvariantPiSubgroups L A (piOf 2), ∀ U₂ ∈ maxInvariantPiSubgroups L A (piOf 2),
          U₁ ≠ U₂ → U₁ ⊓ U₂ ≠ ⊥) := by
  obtain ⟨hf, hg⟩ := maxInvariant_two_transport π hπ hker hAinv
  have hfg := map_subgroupOf_map_comap π hπ
  refine ⟨Set.ncard_congr (fun U _ => (U.subgroupOf L).map π) (fun U hU => (hf U hU).1)
    (fun U₁ U₂ hU₁ hU₂ h => by
      have h' : (U₁.subgroupOf L).map π = (U₂.subgroupOf L).map π := h
      rw [← (hf U₁ hU₁).2, ← (hf U₂ hU₂).2, h'])
    (fun W hW => ⟨_, hg W hW, hfg W⟩), fun hmeet U₁ hU₁ U₂ hU₂ hne hbot => ?_⟩
  have hne' : (U₁.subgroupOf L).map π ≠ (U₂.subgroupOf L).map π := fun h =>
    hne (by rw [← (hf U₁ hU₁).2, ← (hf U₂ hU₂).2, h])
  apply hmeet _ (hf U₁ hU₁).1 _ (hf U₂ hU₂).1 hne'
  rw [eq_bot_iff]
  rintro w ⟨hw₁, ⟨u, hu, rfl⟩⟩
  have huU₁ : (u : G) ∈ U₁ := by
    rw [← (hf U₁ hU₁).2]
    exact ⟨u, hw₁, rfl⟩
  have hu1 : (u : G) ∈ U₁ ⊓ U₂ := ⟨huU₁, Subgroup.mem_subgroupOf.mp hu⟩
  rw [hbot, Subgroup.mem_bot] at hu1
  rw [Subgroup.mem_bot, show u = 1 from Subtype.ext hu1, map_one]

end Transport

section J2

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem conjugate_one_eq_self (H : Subgroup X) : conjugate H 1 = H := by
  show H.map (MulAut.conj (1 : X)⁻¹).toMonoidHom = H
  rw [inv_one]
  exact Late.map_conj_one H

omit [Finite X] in
theorem eq_of_conjugate_eq_conjugate {H K : Subgroup X} {x : X}
    (h : conjugate H x = conjugate K x) : H = K := by
  have h' := congrArg (fun V => conjugate V x⁻¹) h
  simp only [KFacts.KS14.conjugate_conjugate_eq_mul, mul_inv_cancel, conjugate_one_eq_self] at h'
  exact h'

omit [Finite X] in
theorem conjugate_inf_eq_inf (H K : Subgroup X) (x : X) :
    conjugate (H ⊓ K) x = conjugate H x ⊓ conjugate K x :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj x⁻¹).injective

omit [Finite X] in
theorem conjugate_ne_bot_of_ne_bot {H : Subgroup X} (hH : H ≠ ⊥) (x : X) : conjugate H x ≠ ⊥ :=
  fun h => hH ((Subgroup.map_eq_bot_iff_of_injective H (MulAut.conj x⁻¹).injective).mp h)

theorem j2_maxInvariant_two_pairwise (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) {B : Subgroup X}
    (hBP : B ≤ P) (hB9 : Nat.card B = 9) :
    (maxInvariantPiSubgroups ⊤ B (piOf 2)).ncard = 3 ∧
      ∀ V₁ ∈ maxInvariantPiSubgroups ⊤ B (piOf 2), ∀ V₂ ∈ maxInvariantPiSubgroups ⊤ B (piOf 2),
        V₁ ≠ V₂ → V₁ ⊓ V₂ ≠ ⊥ := by
  have h3 := KFacts.KS14.j2_maxInvariant_two_ncard h415 hX P hBP hB9
  refine ⟨h3, ?_⟩
  obtain ⟨U, hU, U', hU', hne, hmeet⟩ :=
    KFacts.KS14.j2_exists_maxInvariant_ne_inf_ne_bot h415 hX P hBP hB9
  obtain ⟨x, hxP, -, rfl⟩ := KFacts.KS14.j2_maxInvariant_two_transitive h415 hX P hBP hB9 hU hU'
  obtain ⟨⟨hHeis, -⟩, -, -, -, h5⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨-, -, hexp⟩ := hHeis
  have hx3 : x * x * x = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨x, hxP⟩ : ↥(P : Subgroup X))
    rw [hexp] at h
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_succ, pow_two] at h'
    exact h'
  obtain ⟨S, -, hSP, -⟩ := h5 B ⟨hBP, hB9⟩
  have hstab : ∀ V ∈ maxInvariantPiSubgroups ⊤ B (piOf 2), ∀ y ∈ (P : Subgroup X),
      conjugate V y ∈ maxInvariantPiSubgroups ⊤ B (piOf 2) := by
    intro V hV y hy
    rw [hSP] at hV ⊢
    obtain ⟨z, hz, rfl⟩ := hV
    exact ⟨z * y, mul_mem hz hy, (KFacts.KS14.conjugate_conjugate_eq_mul S z y).symm⟩
  generalize hU₁ : conjugate U x = U₁ at hU' hne hmeet
  obtain ⟨U₂, hU₂⟩ : ∃ V, conjugate U₁ x = V := ⟨_, rfl⟩
  have hU₂mem : U₂ ∈ maxInvariantPiSubgroups ⊤ B (piOf 2) := hU₂ ▸ hstab U₁ hU' x hxP
  have hU₂x : conjugate U₂ x = U := by
    rw [← hU₂, ← hU₁, KFacts.KS14.conjugate_conjugate_eq_mul,
      KFacts.KS14.conjugate_conjugate_eq_mul, ← mul_assoc, hx3, conjugate_one_eq_self]
  have h21 : U₂ ≠ U₁ := fun h =>
    hne (eq_of_conjugate_eq_conjugate ((hU₂.trans h).trans hU₁.symm)).symm
  have h20 : U₂ ≠ U := fun h => hne (by rw [← hU₂x, h, hU₁])
  have hall : maxInvariantPiSubgroups ⊤ B (piOf 2) ⊆ {U, U₁, U₂} := by
    have hsub : ({U, U₁, U₂} : Set (Subgroup X)) ⊆ maxInvariantPiSubgroups ⊤ B (piOf 2) := by
      intro V hV
      rcases hV with rfl | rfl | rfl
      · exact hU
      · exact hU'
      · exact hU₂mem
    have hcard : ({U, U₁, U₂} : Set (Subgroup X)).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨U, U₁, U₂, hne, h20.symm, h21.symm, rfl⟩
    exact (Set.eq_of_subset_of_ncard_le hsub (h3.trans hcard.symm).le
      (Set.finite_of_ncard_ne_zero (by rw [h3]; norm_num))).symm.le
  have m01 : U ⊓ U₁ ≠ ⊥ := hmeet
  have m12 : U₁ ⊓ U₂ ≠ ⊥ := by
    have := conjugate_ne_bot_of_ne_bot m01 x
    rwa [conjugate_inf_eq_inf, hU₁, hU₂] at this
  have m20 : U₂ ⊓ U ≠ ⊥ := by
    have := conjugate_ne_bot_of_ne_bot m12 x
    rwa [conjugate_inf_eq_inf, hU₂, hU₂x] at this
  intro V₁ hV₁ V₂ hV₂ hV
  rcases hall hV₁ with h₁ | h₁ | h₁ <;> rcases hall hV₂ with h₂ | h₂ | h₂ <;>
    rw [h₁, h₂] at hV ⊢
  · exact absurd rfl hV
  · exact m01
  · rw [inf_comm]; exact m20
  · rw [inf_comm]; exact m01
  · exact absurd rfl hV
  · exact m12
  · exact m20
  · rw [inf_comm]; exact m12
  · exact absurd rfl hV

end J2

section FixedPoint

omit [Finite G] in
theorem exists_mem_le_normalizer_of_ncard_eq_three {X : Subgroup G} (hX : ¬ 3 ∣ Nat.card X)
    {Ω : Set (Subgroup G)} (hΩ : Ω.ncard = 3)
    (hXΩ : ∀ U ∈ Ω, ∀ x ∈ X, U.map (MulAut.conj x).toMonoidHom ∈ Ω) :
    ∃ U ∈ Ω, X ≤ Subgroup.normalizer (U : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Ω.Finite := Set.finite_of_ncard_ne_zero (by rw [hΩ]; norm_num)
  have : Finite Ω := hfin.to_subtype
  let _ : MulAction X Ω :=
    { smul := fun x U => ⟨(U : Subgroup G).map (MulAut.conj (x : G)).toMonoidHom,
        hXΩ U U.2 x x.2⟩
      one_smul := fun U => Subtype.ext (Late.map_conj_one (U : Subgroup G))
      mul_smul := fun x y U => Subtype.ext (Late.map_conj_map_conj (U : Subgroup G) x y).symm }
  set ρ := MulAction.toPermHom X Ω
  have hcardΩ : Nat.card Ω = 3 := by rw [Nat.card_coe_set_eq, hΩ]
  have hR1 : Nat.card ρ.range ∣ Nat.card X := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  have hR2 : Nat.card ρ.range ∣ 2 * 3 := by
    have h := Subgroup.card_subgroup_dvd_card ρ.range
    rw [Nat.card_perm, hcardΩ] at h
    simpa [Nat.factorial] using h
  have hR3 : Nat.Coprime (Nat.card ρ.range) 3 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
      hX (h3.trans hR1))
  have hRp : IsPGroup 2 ρ.range := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (hR3.dvd_of_dvd_mul_right hR2) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [h, pow_one])
  obtain ⟨U, hU⟩ := hRp.nonempty_fixed_point_of_prime_not_dvd_card Ω (by rw [hcardΩ]; norm_num)
  refine ⟨U, U.2, fun x hx => mem_normalizer_of_map_conj_eq ?_⟩
  have h : ((⟨x, hx⟩ : X) • U : Ω) = U := hU ⟨ρ ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩
  exact congrArg Subtype.val h

end FixedPoint

section Facts


theorem j2_point_facts {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hcL : c ∉ L := by
    obtain ⟨φ⟩ := hJ
    exact Sec13.not_mem_of_center_eq_bot hD
      (Sec13.center_eq_bot_of_mulEquiv φ (KFacts.KS14.center_nativeJ2_eq_bot h415))
  have hFE : partTwoF G = partTwoE G :=
    (hD.toTheoremFourHyp.partTwoF_eq_partTwoE hD.partTwoS_eq).1
  have hAL : A ≤ Subgroup.zpowers c ⊔ L := Sec17.le_zpowers_sup_of_j2 h415
    KFacts.ks17J2AutThree hFE hJ hcL hA.1 hA.2 hD.mem_A hD.le_normalizer
  have hcA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hD.mem_A
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (L : Set G) := hcA.trans hD.le_normalizer
  have hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
    refine le_antisymm (fun a ha => ?_) (sup_le hcA inf_le_left)
    have haL : a ∈ ((Subgroup.zpowers c ⊔ L : Subgroup G) : Set G) := hAL ha
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at haL
    obtain ⟨z, hz, l, hl, rfl⟩ := Set.mem_mul.mp haL
    have hlA : l ∈ A := by
      have hl' : l = z⁻¹ * (z * l) := by group
      rw [hl']
      exact mul_mem (inv_mem (hcA hz)) ha
    exact Subgroup.mul_mem_sup hz ⟨hlA, hl⟩
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ A ⊓ L, x * y = y * x := fun x hx y hy =>
    hD.commute (hcA hx) hy.1
  have hdisj : Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ := by
    rw [eq_bot_iff, ← Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hD.orderOf_eq hcL]
    exact fun x hx => ⟨hx.2.2, hx.1⟩
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [← hAc, hdisj, Subgroup.card_bot, mul_one, hA.2, Nat.card_zpowers, hD.orderOf_eq] at hcard
  exact ⟨hcL, by omega, hAc⟩

end Facts

section HJ


theorem exists_scriptQPiStar_two_of_j2 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h142 : ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3), Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer {c}))
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ∃ U₁ ∈ scriptQPiStar A (lB A) L (piOf 2), ∃ U₂ ∈ scriptQPiStar A (lB A) L (piOf 2),
      U₁ ≠ U₂ ∧ U₁ ⊓ U₂ ≠ ⊥ ∧ xA A ≤ Subgroup.normalizer (U₂ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hD : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hLc : L ≤ Subgroup.centralizer {c} := hD.le_centralizer
  have hLtop : L ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hD.ne_one (top_le_iff.mp (htop ▸ hLc))
  have hJ2 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    Sec12.gap128OTwoHJ ↥L (h.toTheoremFourHyp.sectionFourHyp hLtop)
      (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) hJ
  obtain ⟨-, h9, hAc⟩ := j2_point_facts hD hJ
  obtain ⟨φ⟩ := hJ
  have hAinv : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G) := by
    intro V hVL hV
    rw [hAc]
    refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (V : Set G) ?_)) hV
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc (hVL hv))
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hT3 : IsPGroup 3 (A.subgroupOf L) :=
    hA.isPGroup.comap_of_ker_isPGroup L.subtype
      (IsPGroup.ker_isPGroup_of_injective L.subtype_injective)
  have hTcard : Nat.card (A.subgroupOf L) = 9 := by
    rw [← Subgroup.inf_subgroupOf_right, ← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv
  have hB9 : Nat.card ((A.subgroupOf L).map π) = 9 := by
    rw [← hTcard]
    refine Nat.card_congr (Equiv.ofBijective (π.subgroupMap (A.subgroupOf L))
      ⟨fun x y hxy => ?_, π.subgroupMap_surjective _⟩).symm
    have hdisj : Disjoint (A.subgroupOf L) π.ker := by
      refine Subgroup.disjoint_of_coprime_natCard ?_
      rw [hTcard]
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hker
      rw [hk]
      exact Nat.Coprime.pow_right k (by norm_num)
    have hmem : (x : ↥L)⁻¹ * (y : ↥L) ∈ A.subgroupOf L ⊓ π.ker := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem x.2) y.2, MonoidHom.mem_ker.mpr ?_⟩
      rw [map_mul, map_inv, inv_mul_eq_one]
      exact congrArg Subtype.val hxy
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
    exact Subtype.ext (eq_of_inv_mul_eq_one hmem)
  obtain ⟨P, hBP⟩ := (hT3.map π).exists_le_sylow
  obtain ⟨hn3, hpair⟩ := j2_maxInvariant_two_pairwise h415 hJ2 P hBP hB9
  obtain ⟨hncard, hmeet⟩ := maxInvariant_two_ncard_eq π hπs hker hAinv
  rw [hn3] at hncard
  have hpairL := hmeet hpair
  have hstar : scriptQPiStar A (lB A) L (piOf 2) = maxInvariantPiSubgroups L A (piOf 2) :=
    scriptQPiStar_two_eq fun U hU => mem_scriptQ_of_first142 h142 hLc hU
  rw [hstar]
  have hXC : xA A ≤ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
  have hXL : xA A ≤ Subgroup.normalizer (L : Set G) := by
    intro x hx
    have hxc : x ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hD.mem_A) (hXC hx)
    have hL3 : 3 ∣ Nat.card L := by
      have h1 := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥L)
      rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2] at h1
      exact (by norm_num : (3 : ℕ) ∣ 604800).trans h1
    refine mem_normalizer_of_map_conj_eq
      ((h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).2 _
        (Sec6.map_conj_mem_thetaComponentsAt hxc hD.mem_thetaComponentsAt) ?_)
    rwa [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  have hXΩ : ∀ U ∈ maxInvariantPiSubgroups L A (piOf 2), ∀ x ∈ xA A,
      U.map (MulAut.conj x).toMonoidHom ∈ maxInvariantPiSubgroups L A (piOf 2) := by
    refine fun U hU x hx => Late.maximal_map_conj (fun V hV y hy => ?_) hU hx
    refine ⟨?_, ?_, ?_⟩
    · rw [← Late.map_conj_eq_of_mem_normalizer (hXL hy)]
      exact Subgroup.map_mono hV.1
    · intro q hq
      refine hV.2.1 q ?_
      rwa [Subgroup.card_map_of_injective (MulAut.conj y).injective] at hq
    · intro a ha
      refine mem_normalizer_of_map_conj_eq ?_
      have hya : y * a = a * y := (Subgroup.mem_centralizer_iff.mp (hXC hy) a ha).symm
      rw [Late.map_conj_map_conj, ← hya, ← Late.map_conj_map_conj,
        Late.map_conj_eq_of_mem_normalizer (hV.2.2 ha)]
  obtain ⟨U₂, hU₂, hXU₂⟩ := exists_mem_le_normalizer_of_ncard_eq_three
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _))
    hncard hXΩ
  obtain ⟨U₁, hU₁, hne⟩ : ∃ U₁ ∈ maxInvariantPiSubgroups L A (piOf 2), U₁ ≠ U₂ := by
    by_contra hall
    push Not at hall
    have hsub : maxInvariantPiSubgroups L A (piOf 2) ⊆ {U₂} := fun U hU => hall U hU
    have := Set.ncard_le_ncard hsub (Set.finite_singleton U₂)
    rw [hncard, Set.ncard_singleton] at this
    omega
  exact ⟨U₁, hU₁, U₂, hU₂, hne, hpairL U₁ hU₁ U₂ hU₂ hne, hXU₂⟩

theorem rank3II_14_11_3_strong_HJ_of {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h142 : ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3), Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer {c}))
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Item1411_3Strong A (lB A) := by
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  intro _
  by_contra hno
  have hfail : ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A →
      CFSG.Open.pCoreOf 2 Y ≠ ⊥ → inSubgroup perfectResidual Y ≠ ⊥ →
        TransOn A (lB A) (xA A) Y := by
    intro Y hYΔ hY hO2 hres
    by_contra hT
    by_cases hO3 : oPrimeResidualOf 3 Y = ⊥
    · exact hT (transOn_of_not_three_dvd hA h146 hbot hYΔ hY
        (not_three_dvd_of_oPrimeResidualOf_eq_bot hO3))
    · exact hno ⟨Y, hYΔ, hY, hO2, hres, hO3, hT⟩
  obtain ⟨U₁, hU₁, U₂, hU₂, hne, hmeet, hXU⟩ := exists_scriptQPiStar_two_of_j2 h h142 hJ
  exact rank3II_14_16_false_std h h146 hbot hfail hU₁ hU₂ hne hmeet hXU

theorem rank3II_14_11_3_HJ_of {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h142 : ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3), Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer {c}))
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Item1411_3 A (lB A) :=
  item1411_3_of_strong (rank3II_14_11_3_strong_HJ_of h h146 hbot h142 hJ)

end HJ

end CFSG.RankThree.PartTwo.Sec14
