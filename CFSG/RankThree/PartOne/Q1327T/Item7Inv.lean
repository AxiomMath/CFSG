module

public import CFSG.RankThree.PartOne.Q1327T.Item7Basic
public import CFSG.RankThree.PartOne.KFR4.At
public import CFSG.RankThree.PartOne.S11d.OutCentral

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree.PartOne

theorem mem_normalizer_of_conj_inv {Q : Type} [Group Q] {Ē : Subgroup Q} {g : Q}
    (h : ∀ e ∈ Ē, g * e * g⁻¹ = e⁻¹) : g ∈ Subgroup.normalizer (Ē : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h x hx]
    exact Ē.inv_mem hx
  · intro hs
    have h1 : g * (g * x * g⁻¹)⁻¹ * g⁻¹ = g * x * g⁻¹ := by
      rw [h _ (Ē.inv_mem hs), inv_inv]
    have h2 : (g * x * g⁻¹)⁻¹ = x := mul_left_cancel (mul_right_cancel h1)
    rw [← h2]
    exact Ē.inv_mem hs

theorem Row8Conf.concl_of_inv {p g : ℕ} {Q : Type} [Group Q] {Ē : Subgroup Q}
    (h : Row8Conf p g Q Ē) (hZ : Subgroup.center Q = ⊥)
    (hinv : ∃ g₀ : Q, ∀ e ∈ Ē, g₀ * e * g₀⁻¹ = e⁻¹) : Row8U3Concl g Q Ē := by
  refine ⟨hZ, fun hW => ?_⟩
  exfalso
  obtain ⟨g₀, hg₀⟩ := hinv
  have hp2 : p ≠ 2 := by have := h.five_le; omega
  have hne : Nat.card Ē ≠ 1 := by
    rw [h.card]
    exact (Nat.one_lt_pow (by norm_num) h.prime.one_lt).ne'
  exact not_nonempty_perm3_of_inv h.prime hp2 h.elem hne (mem_normalizer_of_conj_inv hg₀) hg₀ hW

theorem exists_inv_of_equiv {Q C : Type} [Group Q] [Group C] (eQ : Q ≃* C) {Ē : Subgroup Q}
    (h : ∃ g : C, ∀ e ∈ Ē.map eQ.toMonoidHom, g * e * g⁻¹ = e⁻¹) :
    ∃ g : Q, ∀ e ∈ Ē, g * e * g⁻¹ = e⁻¹ := by
  obtain ⟨g, hg⟩ := h
  refine ⟨eQ.symm g, fun e he => ?_⟩
  apply eQ.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, map_inv]
  exact hg _ (Subgroup.mem_map_of_mem eQ.toMonoidHom he)

section SL2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_inv_of_isPGroup_sl2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hE : IsPGroup p E) :
    ∃ w : Matrix.SpecialLinearGroup (Fin 2) K, ∀ y ∈ E, w * y * w⁻¹ = y⁻¹ := by
  have hrk : CFSG.pRank p ↥(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) ≤ 1 :=
    KFR4.pRank_le_one_of_equiv_sl2 hp hp2 Subgroup.topEquiv
  have hcyc : IsCyclic E := isCyclic_of_pRank_le_one hp hp2 (le_top : E ≤ ⊤) hE hrk
  obtain ⟨z, hz⟩ := hcyc.exists_generator
  obtain ⟨w, hw⟩ := KF132.exists_inv_conj_sl2 (z : Matrix.SpecialLinearGroup (Fin 2) K)
  refine ⟨w, fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hz ⟨y, hy⟩)
  have hyk : y = (z : Matrix.SpecialLinearGroup (Fin 2) K) ^ k := by
    simpa using (congrArg Subtype.val hk).symm
  rw [hyk]
  calc w * (z : Matrix.SpecialLinearGroup (Fin 2) K) ^ k * w⁻¹
      = (w * (z : Matrix.SpecialLinearGroup (Fin 2) K) * w⁻¹) ^ k := by
        rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    _ = ((z : Matrix.SpecialLinearGroup (Fin 2) K) ^ k)⁻¹ := by rw [hw, inv_zpow]

theorem exists_inv_of_isPGroup_prod {K₂ : Type} [Field K₂] [Finite K₂] [CharP K₂ 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K₂)}
    (hE : IsPGroup p E) :
    ∃ w : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K₂,
      ∀ y ∈ E, w * y * w⁻¹ = y⁻¹ := by
  obtain ⟨w₁, h₁⟩ := exists_inv_of_isPGroup_sl2 hp hp2
    (E := E.map (MonoidHom.fst _ _)) (hE.map _)
  obtain ⟨w₂, h₂⟩ := exists_inv_of_isPGroup_sl2 hp hp2
    (E := E.map (MonoidHom.snd _ _)) (hE.map _)
  refine ⟨(w₁, w₂), fun y hy => Prod.ext ?_ ?_⟩
  · exact h₁ y.1 (Subgroup.mem_map_of_mem (MonoidHom.fst _ _) hy)
  · exact h₂ y.2 (Subgroup.mem_map_of_mem (MonoidHom.snd _ _) hy)

theorem exists_inv_of_prod_sl2 {K₂ : Type} [Field K₂] [Finite K₂] [CharP K₂ 2] {C : Type}
    [Group C] [Finite C]
    (μ : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K₂ →* C)
    (hμ : Function.Injective μ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hord : (Nat.card C).factorization p =
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)).factorization p +
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K₂)).factorization p)
    {E : Subgroup C} (hE : IsPGroup p E) : ∃ g : C, ∀ e ∈ E, g * e * g⁻¹ = e⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain PH : Sylow p
      (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K₂) := default
  have hP₀card : Nat.card ((PH : Subgroup _).map μ) = p ^ (Nat.card C).factorization p := by
    rw [Subgroup.card_map_of_injective hμ, Sylow.card_eq_multiplicity PH, Nat.card_prod,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hord]
  have hPH : IsPGroup p (PH : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K₂)) := PH.isPGroup'
  obtain ⟨w, hw⟩ := exists_inv_of_isPGroup_prod hp hp2 hPH
  refine exists_inv_of_sylow (Sylow.ofCard _ hP₀card) (g₀ := μ w) (fun y hy => ?_) hE
  rw [Sylow.coe_ofCard] at hy
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
  calc μ w * μ y' * (μ w)⁻¹ = μ (w * y' * w⁻¹) := by simp [map_mul, map_inv]
    _ = μ y'⁻¹ := by rw [hw y' hy']
    _ = (μ y')⁻¹ := map_inv μ y'

end SL2

end CFSG.RankThree.PartOne.Q1327T
