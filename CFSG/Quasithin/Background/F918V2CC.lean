module

public import CFSG.Quasithin.Background.F918V2CB
public import CFSG.Quasithin.EmptyFaithful.S153ZH

public section

namespace CFSG.Quasithin.Z391

open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem v2c_isInv_of_smul_eq {A : Subgroup Γ} {P : Subgroup Q} (h : ∀ a ∈ A, a • P = P) :
    XMod.IsInv ↥A P := by
  intro a x hx
  rw [← h a a.2]
  exact Subgroup.smul_mem_pointwise_smul _ _ _ hx

section TwoTypeCounts

variable {Λ T₀ : Subgroup Γ} {Vq : Subgroup Q} {t : Γ}

theorem v2c_inv_fix (hD : TwoTypeBase Λ T₀ Vq t) {B : Subgroup Γ} (hBT : B ≤ T₀)
    (hfix : ∀ b ∈ B, b • Vq = Vq) :
    XMod.IsInv ↥B Vq ∧ XMod.IsInv ↥B (t • Vq) ∧ XMod.IsInv ↥B (v2cCopies Λ Vq) ∧
      XMod.IsInv ↥B (v2cCopies Λ (t • Vq)) :=
  ⟨v2c_isInv_of_smul_eq hfix, v2c_isInv_of_smul_eq fun b hb => v2c_fix_fix hD (hBT hb) (hfix b hb),
    v2c_isInv_of_smul_eq fun b hb => (v2c_smul_copies_fix hD (hBT hb) (hfix b hb)).1,
    v2c_isInv_of_smul_eq fun b hb => (v2c_smul_copies_fix hD (hBT hb) (hfix b hb)).2⟩

theorem v2c_assemble [Finite Q] (hD : TwoType Λ T₀ Vq t) {A : Subgroup Γ} (hAT : A ≤ T₀)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : ∀ x ∈ A, x ^ 2 = 1) (k : ℕ)
    (hcore : ∀ B : Subgroup Γ, B ≤ A → (∀ b ∈ B, b • Vq = Vq) →
      k * nB B Vq ≤ nB B (v2cCopies Λ Vq) ∧
        k * nB B (t • Vq) ≤ nB B (v2cCopies Λ (t • Vq)))
    (hrk : k * rk ↥Vq ≤ rk ↥(v2cCopies Λ Vq)) :
    k * nB A (Vq ⊔ t • Vq) ≤ nB A (⊤ : Subgroup Q) := by
  have hB := hD.toTwoTypeBase
  have hQtop := v2c_copies_sup_eq_top hD
  have hQdisj := v2c_copies_inf_eq_bot_tVq hB
  by_cases hcase : ∀ a ∈ A, a • Vq = Vq
  ·
    obtain ⟨hVA, htVA, hQ₀A, hQ₁A⟩ := v2c_inv_fix hB hAT hcase
    obtain ⟨h1, h2⟩ := hcore A le_rfl hcase
    have hX : nB A (Vq ⊔ t • Vq) = nB A Vq + nB A (t • Vq) :=
      nB_sup_of_disjoint A hVA htVA (v2c_inf_tVq hB)
    have hT := nB_sup_of_disjoint A hQ₀A hQ₁A hQdisj
    rw [hQtop] at hT
    rw [hX, hT, Nat.mul_add]
    omega
  ·
    push Not at hcase
    obtain ⟨a, haA, hanf⟩ := hcase
    have haVq : a • Vq = t • Vq := (hD.stab a (hAT haA)).resolve_left hanf
    set A₀ : Subgroup Γ := A ⊓ MulAction.stabilizer Γ Vq with hA₀
    have hA₀A : A₀ ≤ A := inf_le_left
    have hfix₀ : ∀ b ∈ A₀, b • Vq = Vq := fun b hb => MulAction.mem_stabilizer_iff.1 hb.2
    have hsplit : ∀ x ∈ A, x ∈ A₀ ∨ a⁻¹ * x ∈ A₀ := by
      intro x hx
      rcases hD.stab x (hAT hx) with h | h
      · exact Or.inl ⟨hx, MulAction.mem_stabilizer_iff.2 h⟩
      · right
        refine ⟨A.mul_mem (A.inv_mem haA) hx, MulAction.mem_stabilizer_iff.2 ?_⟩
        rw [mul_smul, h, ← haVq, inv_smul_smul]
    have ha2 : a ^ 2 = 1 := hA2 a haA
    obtain ⟨hVA₀, -, hQ₀A₀, -⟩ := v2c_inv_fix hB (hA₀A.trans hAT) hfix₀
    have hdisjV : Vq ⊓ a • Vq = ⊥ := by
      rw [haVq]
      exact v2c_inf_tVq hB
    have h1 := nB_index_two haA ha2 hAc hA₀A hsplit hVA₀ hdisjV
    have haQ₀ : a • v2cCopies Λ Vq = v2cCopies Λ (t • Vq) :=
      (v2c_smul_copies_swap hB (hAT haA) haVq).1
    have hdisjQ : v2cCopies Λ Vq ⊓ a • v2cCopies Λ Vq = ⊥ := by
      rw [haQ₀]
      exact hQdisj
    have h2 := nB_index_two haA ha2 hAc hA₀A hsplit hQ₀A₀ hdisjQ
    rw [haQ₀, hQtop] at h2
    rw [haVq] at h1
    have h3 := (hcore A₀ hA₀A hfix₀).1
    rw [h1, Nat.mul_add]
    omega

theorem two_type_count2 [Finite Γ] [Finite Q] {Λ T₀ : Subgroup Γ} {Vq : Subgroup Q} {t : Γ}
    (hD : TwoType Λ T₀ Vq t) {A : Subgroup Γ} (hAT : A ≤ T₀)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hnot : ∃ g : Γ, ¬ g • Vq ≤ Vq ⊔ t • Vq) :
    2 * nB A (Vq ⊔ t • Vq) ≤ nB A (⊤ : Subgroup Q) := by
  have hB := hD.toTwoTypeBase
  obtain ⟨S₀, hS₀, hiso, hdisj, -⟩ := v2c_second_copy hD hnot
  have hQtop := v2c_copies_sup_eq_top hD
  have hQdisj := v2c_copies_inf_eq_bot_tVq hB
  have hVQ : Vq ≤ v2cCopies Λ Vq := v2c_le_copies hB.irr (XMod.Iso.refl _)
  have hSQ : S₀ ≤ v2cCopies Λ Vq := v2c_le_copies hS₀ hiso
  have hS₀t : XMod.IsIrr ↥Λ (t • S₀) := isIrr_smul (v2c_normalizes hB) t hS₀
  have hisot : XMod.Iso ↥Λ (t • S₀) (t • Vq) := XMod.iso_smul (v2c_normalizes hB) t hiso
  refine v2c_assemble hD hAT hAc hA2 2 ?_ ?_
  · intro B hBA hfix
    have hBp : IsPGroup 2 ↥B :=
      isPGroup_two_of_sq_eq_one fun x : ↥B => Subtype.ext (by simpa using hA2 _ (hBA x.2))
    have hBΛ : ∀ b ∈ B, ∀ l ∈ Λ, b * l * b⁻¹ ∈ Λ := fun b _ l hl => hB.normal b l hl
    obtain ⟨hVB, htVB, hQ₀B, hQ₁B⟩ := v2c_inv_fix hB (hBA.trans hAT) hfix
    refine ⟨v2c_core2 hB.exp hBp hBΛ hB.irr hVB (v2c_isInv_copies _) hQ₁B hQ₀B hQdisj hQtop hVQ
      hSQ hS₀ hiso hdisj, ?_⟩
    refine v2c_core2 hB.exp hBp hBΛ (v2c_isIrr_smul hB t) htVB (v2c_isInv_copies _) hQ₀B hQ₁B
      (by rw [inf_comm]; exact hQdisj) (by rw [sup_comm]; exact hQtop)
      (v2c_le_copies (v2c_isIrr_smul hB t) (XMod.Iso.refl _)) (v2c_le_copies hS₀t hisot) hS₀t
      hisot ?_
    rw [← Subgroup.smul_inf, hdisj, Subgroup.smul_bot]
  · have h1 := rk_sup_add_rk_inf Vq S₀
    rw [hdisj, rk_bot] at h1
    have h2 := v2c_rk_eq_of_iso hiso
    have h3 := rk_mono (sup_le hVQ hSQ)
    omega

theorem two_type_count3 [Finite Γ] [Finite Q] {Λ T₀ : Subgroup Γ} {Vq : Subgroup Q} {t : Γ}
    (hD : TwoType Λ T₀ Vq t) {A : Subgroup Γ} (hAT : A ≤ T₀)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (h3 : ThreeCopies Λ Vq) :
    3 * nB A (Vq ⊔ t • Vq) ≤ nB A (⊤ : Subgroup Q) := by
  have hB := hD.toTwoTypeBase
  obtain ⟨S₀, S₁, hS₀, hS₁, hiso₀, hiso₁, hd₀, hd₁⟩ := h3
  have hQtop := v2c_copies_sup_eq_top hD
  have hQdisj := v2c_copies_inf_eq_bot_tVq hB
  have hVQ : Vq ≤ v2cCopies Λ Vq := v2c_le_copies hB.irr (XMod.Iso.refl _)
  have hSQ₀ : S₀ ≤ v2cCopies Λ Vq := v2c_le_copies hS₀ hiso₀
  have hSQ₁ : S₁ ≤ v2cCopies Λ Vq := v2c_le_copies hS₁ hiso₁
  have hN := v2c_normalizes hB
  have hS₀t : XMod.IsIrr ↥Λ (t • S₀) := isIrr_smul hN t hS₀
  have hS₁t : XMod.IsIrr ↥Λ (t • S₁) := isIrr_smul hN t hS₁
  have hiso₀t : XMod.Iso ↥Λ (t • S₀) (t • Vq) := XMod.iso_smul hN t hiso₀
  have hiso₁t : XMod.Iso ↥Λ (t • S₁) (t • Vq) := XMod.iso_smul hN t hiso₁
  refine v2c_assemble hD hAT hAc hA2 3 ?_ ?_
  · intro B hBA hfix
    have hBp : IsPGroup 2 ↥B :=
      isPGroup_two_of_sq_eq_one fun x : ↥B => Subtype.ext (by simpa using hA2 _ (hBA x.2))
    have hBΛ : ∀ b ∈ B, ∀ l ∈ Λ, b * l * b⁻¹ ∈ Λ := fun b _ l hl => hB.normal b l hl
    obtain ⟨hVB, htVB, hQ₀B, hQ₁B⟩ := v2c_inv_fix hB (hBA.trans hAT) hfix
    refine ⟨v2c_core3 hB.exp hBp hBΛ hB.irr hVB (v2c_isInv_copies _) hQ₁B hQ₀B hQdisj hQtop hVQ
      hSQ₀ hSQ₁ hS₀ hS₁ hiso₀ hiso₁ hd₀ hd₁, ?_⟩
    refine v2c_core3 hB.exp hBp hBΛ (v2c_isIrr_smul hB t) htVB (v2c_isInv_copies _) hQ₀B hQ₁B
      (by rw [inf_comm]; exact hQdisj) (by rw [sup_comm]; exact hQtop)
      (v2c_le_copies (v2c_isIrr_smul hB t) (XMod.Iso.refl _)) (v2c_le_copies hS₀t hiso₀t)
      (v2c_le_copies hS₁t hiso₁t) hS₀t hS₁t hiso₀t hiso₁t ?_ ?_
    · rw [← Subgroup.smul_inf, hd₀, Subgroup.smul_bot]
    · rw [← Subgroup.smul_sup, ← Subgroup.smul_inf, hd₁, Subgroup.smul_bot]
  · have h1 := rk_sup_add_rk_inf Vq S₀
    rw [hd₀, rk_bot] at h1
    have h2 := rk_sup_add_rk_inf (Vq ⊔ S₀) S₁
    rw [hd₁, rk_bot] at h2
    have h4 := v2c_rk_eq_of_iso hiso₀
    have h5 := v2c_rk_eq_of_iso hiso₁
    have h6 := rk_mono (sup_le (sup_le hVQ hSQ₀) hSQ₁)
    omega

end TwoTypeCounts

end CFSG.Quasithin.Z391
