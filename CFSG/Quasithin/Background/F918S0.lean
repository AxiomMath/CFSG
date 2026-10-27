module

public import CFSG.Quasithin.Background.SmithB51LnModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Assembly.LowTwoRank Matrix Module
open scoped Matrix

theorem card_le_sym_count {n d : ℕ} (B : Subgroup ↥(StatedSL n (ZMod 2)))
    (hexp : ∀ g ∈ B, g * g = 1) (P : GL (Fin n) (ZMod 2))
    (hPs : (P : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = (P : Matrix (Fin n) (Fin n) (ZMod 2)))
    (hP : ∀ γ ∈ B, (P : Matrix (Fin n) (Fin n) (ZMod 2)) * mat γ =
      dmat γ * (P : Matrix (Fin n) (Fin n) (ZMod 2)))
    (hd : finrank (ZMod 2) ↥(fixN B) + d = n) :
    Nat.card ↥B ≤ 2 ^ (d * (d + 1) / 2) := by
  classical
  let R : ↥B → Matrix (Fin n) (Fin n) (ZMod 2) := fun γ =>
    (P : Matrix (Fin n) (Fin n) (ZMod 2)) * (mat (γ : ↥(StatedSL n (ZMod 2))) - 1)
  have hRsymm : ∀ γ : ↥B, (R γ)ᵀ = R γ := by
    intro γ
    have hinv : (γ : ↥(StatedSL n (ZMod 2)))⁻¹ = γ := inv_eq_of_mul_eq_one_right (hexp γ γ.2)
    have hdm : dmat (γ : ↥(StatedSL n (ZMod 2))) = (mat (γ : ↥(StatedSL n (ZMod 2))))ᵀ := by
      rw [dmat, hinv]
    simp only [R]
    rw [transpose_mul, transpose_sub, transpose_one, hPs, sub_mul, one_mul, ← hdm, ← hP γ γ.2,
      mul_sub, mul_one]
  have hRfix : ∀ γ : ↥B, ∀ x ∈ fixN B, R γ *ᵥ x = 0 := by
    intro γ x hx
    simp only [R]
    rw [← mulVec_mulVec, sub_mulVec, one_mulVec, hx γ γ.2, sub_self, mulVec_zero]
  have hRinj : Function.Injective R := by
    intro γ γ' h
    have h1 := congrArg (((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) * ·) h
    simp only [R, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h1
    exact Subtype.ext (mat_injective (sub_left_injective h1))
  have hsymR : ∀ γ : ↥B, ∀ x y, x ⬝ᵥ R γ *ᵥ y = y ⬝ᵥ R γ *ᵥ x := by
    intro γ x y
    rw [dotProduct_mulVec, ← mulVec_transpose, hRsymm, dotProduct_comm]
  obtain ⟨T, hCT⟩ := Submodule.exists_isCompl (fixN B)
  have hTd : finrank (ZMod 2) T = d := by
    have := Submodule.finrank_add_eq_of_isCompl hCT
    rw [Module.finrank_fin_fun (ZMod 2)] at this
    omega
  let b := Module.finBasisOfFinrankEq (ZMod 2) T hTd
  have key : ∀ S : Matrix (Fin n) (Fin n) (ZMod 2), Sᵀ = S → (∀ x ∈ fixN B, S *ᵥ x = 0) →
      (∀ i j, (b i : Fin n → ZMod 2) ⬝ᵥ S *ᵥ (b j : Fin n → ZMod 2) = 0) → S = 0 := by
    intro S hS hSC hSb
    have hsym : ∀ x y, x ⬝ᵥ S *ᵥ y = y ⬝ᵥ S *ᵥ x := fun x y => by
      rw [dotProduct_mulVec, ← mulVec_transpose, hS, dotProduct_comm]
    have hTT : ∀ x ∈ T, ∀ y ∈ T, x ⬝ᵥ S *ᵥ y = 0 := by
      have hβ : (Matrix.toLinearMap₂' (ZMod 2) S).compl₁₂ T.subtype T.subtype = 0 :=
        LinearMap.ext_basis b b fun i j => by
          simp [LinearMap.compl₁₂_apply, Matrix.toLinearMap₂'_apply', hSb i j]
      intro x hx y hy
      have := LinearMap.congr_fun₂ hβ ⟨x, hx⟩ ⟨y, hy⟩
      simpa [LinearMap.compl₁₂_apply, Matrix.toLinearMap₂'_apply'] using this
    have hall : ∀ x y, x ⬝ᵥ S *ᵥ y = 0 := by
      intro x y
      have hx : x ∈ fixN B ⊔ T := by rw [hCT.sup_eq_top]; exact Submodule.mem_top
      have hy : y ∈ fixN B ⊔ T := by rw [hCT.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨c, hc, τ, hτ, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨c', hc', τ', hτ', rfl⟩ := Submodule.mem_sup.1 hy
      rw [mulVec_add, hSC c' hc', zero_add, add_dotProduct, hsym c τ', hSC c hc, dotProduct_zero,
        zero_add]
      exact hTT τ hτ τ' hτ'
    ext i j
    simpa using hall (Pi.single i 1) (Pi.single j 1)
  let f : ↥B → Sym2 (Fin d) → ZMod 2 := fun γ =>
    Sym2.lift ⟨fun i j => (b i : Fin n → ZMod 2) ⬝ᵥ R γ *ᵥ (b j : Fin n → ZMod 2),
      fun i j => hsymR γ _ _⟩
  have hf : Function.Injective f := by
    intro γ γ' h
    apply hRinj
    have h0 : R γ - R γ' = 0 := by
      apply key
      · rw [transpose_sub, hRsymm, hRsymm]
      · intro x hx
        rw [sub_mulVec, hRfix γ x hx, hRfix γ' x hx, sub_self]
      · intro i j
        have := congrFun h s(i, j)
        simp only [f, Sym2.lift_mk] at this
        rw [sub_mulVec, dotProduct_sub, this, sub_self]
    exact sub_eq_zero.1 h0
  calc Nat.card ↥B ≤ Nat.card (Sym2 (Fin d) → ZMod 2) := Nat.card_le_card_of_injective f hf
    _ = 2 ^ (d * (d + 1) / 2) := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Sym2.card, Fintype.card_fin,
        Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]

theorem sym_rank_bound {n : ℕ} (hn : n = 4 ∨ n = 5) (B : Subgroup ↥(StatedSL n (ZMod 2)))
    (hexp : ∀ g ∈ B, g * g = 1) (hcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g)
    (P : GL (Fin n) (ZMod 2))
    (hPs : (P : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = (P : Matrix (Fin n) (Fin n) (ZMod 2)))
    (hP : ∀ γ ∈ B, (P : Matrix (Fin n) (Fin n) (ZMod 2)) * mat γ =
      dmat γ * (P : Matrix (Fin n) (Fin n) (ZMod 2))) :
    Nat.card ↥B * 2 ^ finrank (ZMod 2) ↥(fixN B) ≤ 2 ^ (2 * n - 2) := by
  have hB2 : IsPGroup 2 ↥B := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, sq]
    exact hexp g g.2)⟩
  have hc0 : finrank (ZMod 2) ↥(fixN B) ≠ 0 := fun h =>
    fixN_ne_bot_of_isPGroup hB2 (by omega) (Submodule.finrank_eq_zero.1 h)
  have hcn := finrank_fixN_le B
  obtain ⟨c, hc⟩ : ∃ c, finrank (ZMod 2) ↥(fixN B) = c := ⟨_, rfl⟩
  rw [hc] at hc0 hcn ⊢
  by_cases hc1 : c = 1
  · subst hc1
    have h1 := card_le_of_finrank_fixN_eq_one hcomm hB2 hc
    calc Nat.card ↥B * 2 ^ 1 ≤ 2 ^ (n - 1) * 2 ^ 1 := Nat.mul_le_mul_right _ h1
      _ = 2 ^ (n - 1 + 1) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (2 * n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · obtain ⟨d, hd⟩ : ∃ d, c + d = n := ⟨n - c, by omega⟩
    have h1 := card_le_sym_count B hexp P hPs hP (hc ▸ hd)
    have hd3 : d ≤ 3 := by omega
    calc Nat.card ↥B * 2 ^ c ≤ 2 ^ (d * (d + 1) / 2) * 2 ^ c := Nat.mul_le_mul_right _ h1
      _ = 2 ^ (d * (d + 1) / 2 + c) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (2 * n - 2) := Nat.pow_le_pow_right (by norm_num) (by interval_cases d <;> omega)

end CFSG.Quasithin.B5.Ln
