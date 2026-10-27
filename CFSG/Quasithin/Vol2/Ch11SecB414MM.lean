module

public import CFSG.Quasithin.Vol2.Ch11SecB414MK

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix

variable {F : Type} [Field F] {G : Type} [Group G] {Γ V Z L X : Subgroup G} {k : ℕ}
  {α : ↥Γ →* PGL3 F} (m : Model Γ V Z F k α)

theorem Model.pre_bot : m.pre ⊥ = Z := by
  refine le_antisymm (fun v ⟨hv, hW⟩ => ?_) (m.le_pre ⊥)
  rw [AddSubgroup.mem_bot] at hW
  exact (m.toAdd_eq_zero ⟨v, hv⟩).mp hW

theorem Model.pre_Wsl : m.pre Wsl = V :=
  le_antisymm (m.pre_le_V _) fun v hv => ⟨hv, m.sl ⟨v, hv⟩⟩

theorem Model.isLabFactor_pre {Y K : Subgroup G} {x : G} {α₀ : ↥K →* ↥(StatedSL 2 F)}
    {W W' : AddSubgroup (Matrix (Fin 3) (Fin 3) F)} (hle : W ≤ W')
    {M : Matrix (Fin 3) (Fin 3) F} (hM : M ∈ W') (hMt : M.trace = 0) (hMW : M ∉ W)
    (hYW : Y ≤ Subgroup.normalizer (m.pre W : Set G))
    (hYW' : Y ≤ Subgroup.normalizer (m.pre W' : Set G))
    (hmin : ∀ J : Subgroup G, m.pre W ≤ J → J ≤ m.pre W' →
      m.pre W' ≤ Subgroup.normalizer (J : Set G) → Y ≤ Subgroup.normalizer (J : Set G) →
        J = m.pre W ∨ J = m.pre W')
    {e : Option F}
    (he : e.elim (∀ l ∈ K, ∀ s ∈ m.pre W', l * s * l⁻¹ * s⁻¹ ∈ m.pre W)
      (fun a => IsNatEigSection K x α₀ (m.pre W) (m.pre W') a)) :
    IsLabFactor Y K x α₀ (m.pre W) (m.pre W') e :=
  ⟨m.pre_lt hle hM hMt hMW, m.pre_le_normalizer W W', hYW, hYW', hmin, he⟩

theorem Model.comm_mem_pre_L (hLΓ : L ≤ Γ) (hL : (L.subgroupOf Γ).map α = Ptheta F 0)
    {W W' : AddSubgroup (Matrix (Fin 3) (Fin 3) F)}
    (hsub : ∀ A : Matrix (Fin 3) (Fin 3) F, A 1 0 = 0 → A 2 0 = 0 → A.det = 1 →
      ∀ M ∈ W', cnj A M - M ∈ W) :
    ∀ l ∈ L, ∀ s ∈ m.pre W', l * s * l⁻¹ * s⁻¹ ∈ m.pre W := by
  intro l hl s ⟨hs, hsW'⟩
  obtain ⟨A, h10, h20, hA⟩ := exists_rep_of_mem_L hLΓ hL hl
  have hmem : l * s * l⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (m.normV (hLΓ hl)) s).mp hs
  have hmem' : l * s * l⁻¹ * s⁻¹ ∈ V := V.mul_mem hmem (V.inv_mem hs)
  refine ⟨hmem', ?_⟩
  have e : (⟨l * s * l⁻¹ * s⁻¹, hmem'⟩ : ↥V) = ⟨l * s * l⁻¹, hmem⟩ * (⟨s, hs⟩ : ↥V)⁻¹ := rfl
  rw [e, map_mul m.β, map_inv m.β, toAdd_mul, toAdd_inv,
    m.act ⟨l, hLΓ hl⟩ ⟨s, hs⟩ ⟨_, hmem⟩ rfl _ hA, twAdj_toGL, ← sub_eq_add_neg]
  exact hsub _ h10 h20 A.prop _ hsW'

theorem Model.le_normalizer_Y (hLΓ : L ≤ Γ) (hXΓ : X ≤ Γ)
    (hL : (L.subgroupOf Γ).map α = Ptheta F 0) {ν : Fˣ}
    (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν)))
    {W : AddSubgroup (Matrix (Fin 3) (Fin 3) F)}
    (hcnj : ∀ A : Matrix (Fin 3) (Fin 3) F, A 1 0 = 0 → A 2 0 = 0 → A.det = 1 →
      ∀ M ∈ W, cnj A M ∈ W)
    (hdg : ∀ c : Fˣ, ∀ M ∈ W, twAdj k (dgHom c) M ∈ W) :
    L ⊔ X ≤ Subgroup.normalizer (m.pre W : Set G) :=
  sup_le (le_normalizer_pre_L m hLΓ hL hcnj) (le_normalizer_pre_X m hXΓ hX hdg)

abbrev hatI (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F := diagonal ![0, 1, 1]

abbrev dD (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F := diagonal ![1, 1, 0]

theorem twAdj_dg_diagonal (k : ℕ) (c : Fˣ) (d : Fin 3 → F) :
    twAdj k (dgHom c) (diagonal d) = ((c : F) ^ k) • diagonal d := by
  ext i j
  rw [twAdj_dg_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    rw [mul_comm (dgv (c : F) i), mul_assoc, dgv_inv, mul_one]
  · ring

variable [CharP F 2]

omit [CharP F 2] in
theorem hatI_mem_W2 : hatI F ∈ (W2 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hatI]

theorem hatI_trace : (hatI F).trace = 0 := by
  rw [Matrix.trace_diagonal, Fin.sum_univ_three]
  simp [one_add_one_eq_two, CharTwo.two_eq_zero]

theorem dD_mem_W4 : dD F ∈ (W4 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.trace_diagonal, Fin.sum_univ_three]
    simp [one_add_one_eq_two, CharTwo.two_eq_zero]
  · simp [dD]
  · simp [dD]

omit [CharP F 2] in
theorem sub_hatI_mem_Wp {M : Matrix (Fin 3) (Fin 3) F}
    (hM : M ∈ (W2 : AddSubgroup (Matrix (Fin 3) (Fin 3) F))) :
    M - M 1 1 • hatI F ∈ (Wp : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hM
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [hatI]

theorem sub_dD_mem_W3 {M : Matrix (Fin 3) (Fin 3) F}
    (hM : M ∈ (W4 : AddSubgroup (Matrix (Fin 3) (Fin 3) F))) :
    M - M 0 0 • dD F ∈ (W3 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  obtain ⟨h1, h2, h3⟩ := hM
  rw [Matrix.trace_fin_three] at h1
  refine ⟨by simp [dD], by simp [dD, h2], by simp [dD, h3], ?_⟩
  simp only [Matrix.sub_apply, Matrix.smul_apply, dD, Matrix.diagonal_apply_eq,
    smul_eq_mul]
  simp
  linear_combination h1 - (M 0 0 + M 2 2) * CharTwo.two_eq_zero (R := F)

end CFSG.Quasithin.H13.Ch4.B414.M
