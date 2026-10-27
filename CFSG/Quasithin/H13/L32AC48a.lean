module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Alg
public import CFSG.LieType.SteinbergBRSmallAltSylow
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)

@[expose] def IsList47 (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, IsPSL n 2 1 X) ∨ (∃ n : ℕ, IsAlt n X) ∨ IsPSU 3 3 1 X

theorem center_eq_bot_of_isSimpleGroup {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have hb : b ∈ Subgroup.center X := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem exists_noncomm_of_isQuasisimple {X : Type*} [Group X] (hq : CFSG.IsQuasisimple X) :
    ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, b, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem isSimpleGroup_of_list47 {X : Type} [Group X] (hq : CFSG.IsQuasisimple X)
    (h : IsList47 X) : IsSimpleGroup X := by
  rcases h with ⟨n, hn⟩ | ⟨n, ⟨e⟩⟩ | hu
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X n 2 1 hn).2
  · have h5 : 5 ≤ n := L246C127.alt_five_le_of_quasisimple e hq
    have := alternatingGroup.isSimpleGroup (α := Fin n)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact h5)
    exact e.isSimpleGroup
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 3 1 hu).2

theorem center_eq_bot_of_list47 {X : Type} [Group X] (hq : CFSG.IsQuasisimple X)
    (h : IsList47 X) : Subgroup.center X = ⊥ :=
  center_eq_bot_of_isSimpleGroup (isSimpleGroup_of_list47 hq h)
    (exists_noncomm_of_isQuasisimple hq)

theorem isPGroup_two_outer_of_dvd_two {X : Type*} [Group X] [Finite X]
    (h : Nat.card (Outer X) ∣ 2) : IsPGroup 2 (Outer X) := by
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
  · exact IsPGroup.of_card (n := 0) (by rw [h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [h2, pow_one])

theorem isPGroup_two_outer_of_list47 {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (h : IsList47 X) : IsPGroup 2 (Outer X) := by
  have : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective
  rcases h with ⟨n, hn⟩ | ⟨n, ⟨e⟩⟩ | hu
  · have hn3 : 3 ≤ n := by
      obtain ⟨⟨-, -, hn2, h22, -⟩, -⟩ := hn
      by_contra h3
      exact h22 (by rw [show n = 2 by omega]; rfl)
    have hb := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inl rfl) hn3 Nat.prime_two le_rfl hn).1
    refine isPGroup_two_outer_of_dvd_two (hb.trans ?_)
    simp [CFSG.RankThree.OuterOrder.determinantParameter]
  · have h5 : 5 ≤ n := L246C127.alt_five_le_of_quasisimple e hq
    by_cases h6 : n = 6
    · subst h6
      have h := CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six
      obtain ⟨m, hm⟩ := h.exists_card_eq
      refine IsPGroup.of_card (n := m) ?_
      rw [Nat.card_congr
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv, hm]
    · exact isPGroup_two_outer_of_dvd_two (outer_card_dvd_two_of_equiv_outside_six (by omega) e)
  · have hb := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inr rfl) le_rfl Nat.prime_three le_rfl hu).1
    refine isPGroup_two_outer_of_dvd_two (hb.trans ?_)
    simp [CFSG.RankThree.OuterOrder.determinantParameter]

end CFSG.Quasithin.H13.L32A.C
