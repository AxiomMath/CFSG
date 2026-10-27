module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSL2
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.C126.Nat

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
open scoped MatrixGroups LinearAlgebra.Projectivization

section Dickson

variable {k : Type} [Field k] [Finite k]

theorem eq_top_or_le_normalizer_of_rootGrp_le {p : ℙ k (Fin 2 → k)}
    {X : Subgroup SL(2, k)} (h : rootGrp p ≤ X) :
    X = ⊤ ∨ X ≤ Subgroup.normalizer (rootGrp p : Set SL(2, k)) := by
  by_cases hX : X ≤ Subgroup.normalizer (rootGrp p : Set SL(2, k))
  · exact Or.inr hX
  · left
    obtain ⟨g, hgX, hgN⟩ := Set.not_subset.1 hX
    have hgp : g • p ≠ p := fun hh => hgN (mem_normalizer_rootGrp_iff.2 hh)
    have h1 : rootGrp (g • p) ≤ X := by
      rw [rootGrp_smul_eq_map]
      rintro _ ⟨u, hu, rfl⟩
      exact X.mul_mem (X.mul_mem hgX (h hu)) (X.inv_mem hgX)
    exact top_le_iff.1 ((rootGrp_sup_rootGrp (Ne.symm hgp)).symm.le.trans (sup_le h h1))

end Dickson

section Sylow

variable {F : Type} [Field F] [Finite F]

theorem factorization_card_sl2 {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) :
    (Nat.card SL(2, F)).factorization 2 = n := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  have h2 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero
  have h1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hodd : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 := fun hd => by omega
  have hne : (2 ^ n) ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ (2 ^ n) ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 2) 2
    omega
  rw [Nat.factorization_mul (by positivity) hne, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hodd]
  simp

theorem dichotomy_sl2 {A : Type*} [Group A] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (e : A ≃* SL(2, F)) {S X : Subgroup A} (hS : Nat.card S = Nat.card F) (hSX : S ≤ X) :
    X = ⊤ ∨ X ≤ Subgroup.normalizer (S : Set A) := by
  have hP : Nat.card (S.map e.toMonoidHom) = Nat.card F := by
    rw [Subgroup.card_map_of_injective e.injective, hS]
  obtain ⟨x, hx⟩ := exists_point_eq_rootGrp Nat.prime_two hF hP
  have hle : rootGrp x ≤ X.map e.toMonoidHom := hx ▸ Subgroup.map_mono hSX
  rcases eq_top_or_le_normalizer_of_rootGrp_le hle with h | h
  · left
    have h1 : X.map e.toMonoidHom = ⊤ := h
    refine eq_top_iff.2 fun a _ => ?_
    have : e a ∈ X.map e.toMonoidHom := h1 ▸ Subgroup.mem_top _
    obtain ⟨b, hb, hba⟩ := this
    exact (e.injective hba) ▸ hb
  · right
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 : e a ∈ Subgroup.normalizer (rootGrp x : Set SL(2, F)) := h ⟨a, ha, rfl⟩
    rw [← hx] at h1
    have h2 := Subgroup.mem_normalizer_iff.1 h1 (e y)
    rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv,
      MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h2
    exact h2

theorem sylow_dichotomy_of_equiv_sl2 {Γ : Type*} [Group Γ] [Finite Γ] {L S X : Subgroup Γ}
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (e : ↥L ≃* SL(2, F))
    (hS : IsSylowTwoOf S L) (hXL : X ≤ L) (hSX : S ≤ X) :
    X = L ∨ X ≤ Subgroup.normalizer (S : Set Γ) := by
  have hSL : S ≤ L := hS.1
  have hcard : Nat.card (S.subgroupOf L) = Nat.card F := by
    have h1 : Nat.card (S.subgroupOf L) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv
    rw [h1, hS.card_eq]
    unfold twoPart
    rw [Nat.card_congr e.toEquiv, factorization_card_sl2 hn hF, hF]
  have hSX' : S.subgroupOf L ≤ X.subgroupOf L := fun a ha => hSX ha
  rcases dichotomy_sl2 hF e hcard hSX' with h | h
  · left
    have : L ≤ X := Subgroup.subgroupOf_eq_top.1 h
    exact le_antisymm hXL this
  · right
    intro x hx
    have hxL : x ∈ L := hXL hx
    have hN := h (show (⟨x, hxL⟩ : ↥L) ∈ X.subgroupOf L from hx)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have key : ∀ y : Γ, y ∈ L → (y ∈ S ↔ x * y * x⁻¹ ∈ S) := by
      intro y hyL
      have := Subgroup.mem_normalizer_iff.1 hN ⟨y, hyL⟩
      simpa [Subgroup.mem_subgroupOf] using this
    constructor
    · intro hy
      exact (key y (hSL hy)).1 hy
    · intro hy
      have hyL : y ∈ L := by
        have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem hxL) (hSL hy)) hxL
        simpa [mul_assoc] using h1
      exact (key y hyL).2 hy

end Sylow

end CFSG.Quasithin.C126.Nat
