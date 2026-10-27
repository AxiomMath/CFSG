module

public import CFSG.Assembly.Defs
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155T51

variable {M : Type*} [Group M] [Finite M]

theorem injective_mk_comp_subtype (N : Subgroup M) [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    {S : Subgroup M} (hS : IsPGroup 3 S) :
    Function.Injective ((QuotientGroup.mk' N).comp S.subtype) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  have hdisj : Disjoint S N := Subgroup.disjoint_of_coprime_natCard (by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN))
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxN : (x : M) ∈ N := (QuotientGroup.eq_one_iff (x : M)).mp hx
  have hx1 : (x : M) ∈ S ⊓ N := ⟨x.2, hxN⟩
  rw [hdisj.eq_bot, Subgroup.mem_bot] at hx1
  exact Subtype.ext hx1

theorem card_map_mk (N : Subgroup M) [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    {S : Subgroup M} (hS : IsPGroup 3 S) :
    Nat.card (S.map (QuotientGroup.mk' N)) = Nat.card S := by
  have hrange : S.map (QuotientGroup.mk' N) = ((QuotientGroup.mk' N).comp S.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective (injective_mk_comp_subtype N hN hS)).toEquiv).symm

theorem exists_elemAbelian_lift_le (N : Subgroup M) [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    {A : Subgroup M} (hA : IsPGroup 3 A) {E : Subgroup (M ⧸ N)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hAE : A.map (QuotientGroup.mk' N) ≤ E) :
    ∃ S : Subgroup M, A ≤ S ∧ S.map (QuotientGroup.mk' N) = E ∧
      CFSG.Assembly.IsElemAbelian 3 S ∧ Nat.card S = Nat.card E := by
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hE.2 _ x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  set P : Subgroup M := E.comap (QuotientGroup.mk' N)
  have hPcard : Nat.card P = Nat.card N * 3 ^ k := by
    rw [← hk]
    exact QuotientGroup.card_preimage_mk N (E : Set (M ⧸ N))
  have hAP : A ≤ P := Subgroup.map_le_iff_le_comap.mp hAE
  obtain ⟨Q, hAQ⟩ := (hA.comap_of_injective P.subtype P.subtype_injective).exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup P) = 3 ^ k := by
    rw [Sylow.card_eq_multiplicity, hPcard, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero _ Nat.prime_three.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same, zero_add]
  set S : Subgroup M := (Q : Subgroup P).map P.subtype with hS
  have hScard : Nat.card S = 3 ^ k := by
    rw [hS, Subgroup.card_map_of_injective P.subtype_injective, hQcard]
  have hSP : S ≤ P := Subgroup.map_subtype_le _
  have hS3 : IsPGroup 3 S := Q.isPGroup'.map P.subtype
  have hAS : A ≤ S := fun a ha => ⟨⟨a, hAP ha⟩, hAQ (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hSE : S.map (QuotientGroup.mk' N) ≤ E := Subgroup.map_le_iff_le_comap.mpr hSP
  have hmap : S.map (QuotientGroup.mk' N) = E :=
    Subgroup.eq_of_le_of_card_ge hSE (by rw [card_map_mk N hN hS3, hScard, hk])
  have hinj : ∀ a ∈ S, ∀ b ∈ S, QuotientGroup.mk' N a = QuotientGroup.mk' N b → a = b := by
    intro a ha b hb hab
    exact congrArg Subtype.val
      (injective_mk_comp_subtype N hN hS3 (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
  refine ⟨S, hAS, hmap, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, hScard.trans hk.symm⟩
  · refine hinj _ (S.mul_mem a.2 b.2) _ (S.mul_mem b.2 a.2) ?_
    show (QuotientGroup.mk' N) ((a : M) * b) = (QuotientGroup.mk' N) ((b : M) * a)
    rw [map_mul, map_mul]
    have ha : (QuotientGroup.mk' N) a ∈ E := hSE (Subgroup.mem_map_of_mem _ a.2)
    have hb : (QuotientGroup.mk' N) b ∈ E := hSE (Subgroup.mem_map_of_mem _ b.2)
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨_, ha⟩ : E) ⟨_, hb⟩)
  · refine hinj _ (S.pow_mem hx 3) _ S.one_mem ?_
    rw [map_pow, map_one]
    exact hE.2 _ (hSE (Subgroup.mem_map_of_mem _ hx))

theorem exists_two_subgroup_of_map_le_normalizer (N : Subgroup M) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {E : Subgroup M} (hE : IsPGroup 3 E) {T : Subgroup (M ⧸ N)}
    (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hET : E.map (QuotientGroup.mk' N) ≤ Subgroup.normalizer (T : Set (M ⧸ N))) :
    ∃ U : Subgroup M, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set M) := by
  set D : Subgroup M := T.comap (QuotientGroup.mk' N)
  have hED : E ≤ Subgroup.normalizer (D : Set M) := by
    intro s hs
    have hsT : (QuotientGroup.mk' N) s ∈ Subgroup.normalizer (T : Set (M ⧸ N)) :=
      hET (Subgroup.mem_map_of_mem _ hs)
    rw [Subgroup.mem_normalizer_iff] at hsT ⊢
    intro d
    change (QuotientGroup.mk' N) d ∈ T ↔ (QuotientGroup.mk' N) (s * d * s⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact hsT _
  have hDcard : Nat.card D = Nat.card N * Nat.card T :=
    QuotientGroup.card_preimage_mk N (T : Set (M ⧸ N))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hT
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hT1 (Subgroup.card_eq_one.mp hm)
  have hcop : Nat.Coprime 3 (Nat.card D) := by
    rw [hDcard, hm]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN)
      (Nat.Coprime.pow_right m (by norm_num))
  have h2 : 2 ∣ Nat.card D := by
    rw [hDcard, hm]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hm0) _
  obtain ⟨T₀, hET₀, hT₀⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
      3 2 Nat.prime_three Nat.prime_two E D hE hED hcop h2
  exact ⟨(T₀ : Subgroup D).map D.subtype, hT₀, T₀.isPGroup'.map D.subtype, hET₀⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155T51
