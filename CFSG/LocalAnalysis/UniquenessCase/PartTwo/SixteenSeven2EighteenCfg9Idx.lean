module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c167_rk_le_mQuot_of_inf_map_eq_bot (hW : ∀ w : W, w ^ 2 = 1) (t : MulAut W)
    {J R : Subgroup W} (hRJ : R ≤ J) (h : R ⊓ R.map t.toMonoidHom = ⊥) :
    rk ↥R ≤ E3.mQuot J (J ⊓ fixV (Subgroup.zpowers t)) := by
  have hCR : fixV (Subgroup.zpowers t) ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hx1 : t x = x := (mem_fixV_zpowers t x).mp hx.1
    have hmem : x ∈ R ⊓ R.map t.toMonoidHom :=
      ⟨hx.2, Subgroup.mem_map.mpr ⟨x, hx.2, hx1⟩⟩
    rw [h, Subgroup.mem_bot] at hmem
    simpa using hmem
  have hinf : R ⊓ (J ⊓ fixV (Subgroup.zpowers t)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hx' : x ∈ fixV (Subgroup.zpowers t) ⊓ R := ⟨hx.2.2, hx.1⟩
    rw [hCR, Subgroup.mem_bot] at hx'
    simpa using hx'
  have h1 := rk_sup_add_rk_inf R (J ⊓ fixV (Subgroup.zpowers t))
  rw [hinf, rk_bot] at h1
  have h2 : rk ↥(R ⊔ (J ⊓ fixV (Subgroup.zpowers t))) ≤ rk ↥J :=
    rk_mono (sup_le hRJ inf_le_left)
  have h3 : rk ↥J = E3.mQuot J (J ⊓ fixV (Subgroup.zpowers t)) +
      rk ↥(J ⊓ fixV (Subgroup.zpowers t)) := by
    have hh := E3.card_eq_two_pow_mul ((isPGroup_two_of_sq_eq_one hW).to_subgroup J)
      (inf_le_left : J ⊓ fixV (Subgroup.zpowers t) ≤ J)
    rw [card_eq_two_pow hW, card_eq_two_pow hW, ← pow_add] at hh
    exact Nat.pow_right_injective (le_refl 2) hh
  omega

theorem s16c167_mQuot_sup_split (hW : ∀ w : W, w ^ 2 = 1) (t : MulAut W) {A B : Subgroup W}
    (hdisj : A ⊓ B = ⊥) (hA : A.map t.toMonoidHom = A) (hB : B.map t.toMonoidHom = B) :
    E3.mQuot (A ⊔ B) ((A ⊔ B) ⊓ fixV (Subgroup.zpowers t)) =
      E3.mQuot A (A ⊓ fixV (Subgroup.zpowers t)) + E3.mQuot B (B ⊓ fixV (Subgroup.zpowers t)) := by
  have hdec : ∀ w ∈ A ⊔ B, ∃ x₁ ∈ A, ∃ x₂ ∈ B, x₁ * x₂ = w := by
    intro w hw
    rwa [Subgroup.mem_sup] at hw
  have htA : ∀ x ∈ A, t x ∈ A := fun x hx => by
    have h : t x ∈ A.map t.toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rwa [hA] at h
  have htB : ∀ x ∈ B, t x ∈ B := fun x hx => by
    have h : t x ∈ B.map t.toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rwa [hB] at h
  have huniq : ∀ {a a' b b' : W}, a ∈ A → a' ∈ A → b ∈ B → b' ∈ B →
      a * b = a' * b' → a = a' ∧ b = b' := by
    intro a a' b b' ha ha' hb hb' h
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      have h2 : a'⁻¹ * a * b = b' := by
        rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [← h2, mul_assoc, mul_inv_cancel, mul_one]
    have hmem : a'⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem ha') ha,
        by rw [h1]; exact B.mul_mem hb' (B.inv_mem hb)⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    have hb1 : b' * b⁻¹ = 1 := by rw [← h1]; exact hmem
    exact ⟨(inv_mul_eq_one.mp hmem).symm, (mul_inv_eq_one.mp hb1).symm⟩
  have hfix : ∀ x₁ ∈ A, ∀ x₂ ∈ B,
      (x₁ * x₂ ∈ fixV (Subgroup.zpowers t) ↔
        x₁ ∈ fixV (Subgroup.zpowers t) ∧ x₂ ∈ fixV (Subgroup.zpowers t)) := by
    intro x₁ hx₁ x₂ hx₂
    rw [mem_fixV_zpowers, mem_fixV_zpowers, mem_fixV_zpowers]
    constructor
    · intro h
      have h' : t x₁ * t x₂ = x₁ * x₂ := by rw [← map_mul, h]
      exact huniq (htA x₁ hx₁) hx₁ (htB x₂ hx₂) hx₂ h'
    · rintro ⟨h₁', h₂'⟩
      rw [map_mul, h₁', h₂']
  have hCsup : (A ⊔ B) ⊓ fixV (Subgroup.zpowers t) =
      (A ⊓ fixV (Subgroup.zpowers t)) ⊔ (B ⊓ fixV (Subgroup.zpowers t)) := by
    apply le_antisymm
    · intro w hw
      rw [Subgroup.mem_inf] at hw
      obtain ⟨x₁, hx₁, x₂, hx₂, hwx⟩ := hdec w hw.1
      rw [← hwx] at hw ⊢
      have hmem := (hfix x₁ hx₁ x₂ hx₂).mp hw.2
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hx₁, hmem.1⟩)
        (Subgroup.mem_inf.mpr ⟨hx₂, hmem.2⟩)
    · refine sup_le ?_ ?_
      · exact le_inf (le_trans inf_le_left le_sup_left) inf_le_right
      · exact le_inf (le_trans inf_le_left le_sup_right) inf_le_right
  have hCdisj : (A ⊓ fixV (Subgroup.zpowers t)) ⊓ (B ⊓ fixV (Subgroup.zpowers t)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxInf : x ∈ A ⊓ B := ⟨hx.1.1, hx.2.1⟩
    rw [hdisj, Subgroup.mem_bot] at hxInf
    simpa using hxInf
  have hdisjI : rk ↥(A ⊔ B) = rk ↥A + rk ↥B := by
    have h := rk_sup_add_rk_inf A B
    rw [hdisj, rk_bot] at h
    omega
  have hdisjC : rk ↥((A ⊔ B) ⊓ fixV (Subgroup.zpowers t)) =
      rk ↥(A ⊓ fixV (Subgroup.zpowers t)) + rk ↥(B ⊓ fixV (Subgroup.zpowers t)) := by
    have h := rk_sup_add_rk_inf (A ⊓ fixV (Subgroup.zpowers t))
      (B ⊓ fixV (Subgroup.zpowers t))
    rw [← hCsup, hCdisj, rk_bot] at h
    omega
  have hcardJ : rk ↥(A ⊔ B) =
      E3.mQuot (A ⊔ B) ((A ⊔ B) ⊓ fixV (Subgroup.zpowers t)) +
        rk ↥((A ⊔ B) ⊓ fixV (Subgroup.zpowers t)) := by
    have hh := E3.card_eq_two_pow_mul ((isPGroup_two_of_sq_eq_one hW).to_subgroup (A ⊔ B))
      (inf_le_left : (A ⊔ B) ⊓ fixV (Subgroup.zpowers t) ≤ A ⊔ B)
    rw [card_eq_two_pow hW, card_eq_two_pow hW, ← pow_add] at hh
    exact Nat.pow_right_injective (le_refl 2) hh
  have hcardA : rk ↥A = E3.mQuot A (A ⊓ fixV (Subgroup.zpowers t)) +
      rk ↥(A ⊓ fixV (Subgroup.zpowers t)) := by
    have hh := E3.card_eq_two_pow_mul ((isPGroup_two_of_sq_eq_one hW).to_subgroup A)
      (inf_le_left : A ⊓ fixV (Subgroup.zpowers t) ≤ A)
    rw [card_eq_two_pow hW, card_eq_two_pow hW, ← pow_add] at hh
    exact Nat.pow_right_injective (le_refl 2) hh
  have hcardB : rk ↥B = E3.mQuot B (B ⊓ fixV (Subgroup.zpowers t)) +
      rk ↥(B ⊓ fixV (Subgroup.zpowers t)) := by
    have hh := E3.card_eq_two_pow_mul ((isPGroup_two_of_sq_eq_one hW).to_subgroup B)
      (inf_le_left : B ⊓ fixV (Subgroup.zpowers t) ≤ B)
    rw [card_eq_two_pow hW, card_eq_two_pow hW, ← pow_add] at hh
    exact Nat.pow_right_injective (le_refl 2) hh
  omega

theorem s16c167_one_le_mQuot_of_not_le (hW : ∀ w : W, w ^ 2 = 1) (t : MulAut W)
    {A : Subgroup W} (h : ¬ A ≤ fixV (Subgroup.zpowers t)) :
    1 ≤ E3.mQuot A (A ⊓ fixV (Subgroup.zpowers t)) := by
  by_contra hcon
  have hlt : E3.mQuot A (A ⊓ fixV (Subgroup.zpowers t)) < 1 := not_le.1 hcon
  have h0 : E3.mQuot A (A ⊓ fixV (Subgroup.zpowers t)) = 0 := by omega
  have hiff := E3.mQuot_eq_zero_iff ((isPGroup_two_of_sq_eq_one hW).to_subgroup A)
    (inf_le_left : A ⊓ fixV (Subgroup.zpowers t) ≤ A)
  exact h (inf_eq_left.mp (hiff.mp h0))

theorem s16c167_three_le_mQuot_of_blocks (hW : ∀ w : W, w ^ 2 = 1) (t : MulAut W)
    {A B C : Subgroup W} (hAB : A ⊓ B = ⊥) (hABC : (A ⊔ B) ⊓ C = ⊥)
    (hA : A.map t.toMonoidHom = A) (hB : B.map t.toMonoidHom = B) (hC : C.map t.toMonoidHom = C)
    (hA' : ¬ A ≤ fixV (Subgroup.zpowers t)) (hB' : ¬ B ≤ fixV (Subgroup.zpowers t))
    (hC' : ¬ C ≤ fixV (Subgroup.zpowers t)) :
    3 ≤ E3.mQuot (A ⊔ B ⊔ C) ((A ⊔ B ⊔ C) ⊓ fixV (Subgroup.zpowers t)) := by
  have hABm : (A ⊔ B).map t.toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup, hA, hB]
  have hs1 := s16c167_mQuot_sup_split hW t (A := A ⊔ B) (B := C)
    (hdisj := hABC) (hA := hABm) (hB := hC)
  have hs2 := s16c167_mQuot_sup_split hW t (A := A) (B := B)
    (hdisj := hAB) (hA := hA) (hB := hB)
  have h1 := s16c167_one_le_mQuot_of_not_le hW t (A := A) hA'
  have h2 := s16c167_one_le_mQuot_of_not_le hW t (A := B) hB'
  have h3 := s16c167_one_le_mQuot_of_not_le hW t (A := C) hC'
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
