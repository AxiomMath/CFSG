module

public import CFSG.Quasithin.EmptyFaithful.S152O4Mod
public import CFSG.Quasithin.Background.G2Omega4PlusModel

public section

namespace CFSG.Quasithin

namespace S153E54

open CFSG.Quasithin.S152O4 CFSG.Quasithin.Om4Model Matrix
open scoped MatrixGroups

@[expose] def bit (v : Vec) (k : ℕ) : ZMod 2 := ((Vec.code v / 2 ^ k % 2 : ℕ) : ZMod 2)

@[expose] def toMt (v : Vec) : Mt := !![bit v 0, bit v 1; bit v 2, bit v 3]

theorem toMt_mul : ∀ v w : Vec, toMt (v * w) = toMt v + toMt w := by decide +kernel

theorem toMt_inj : Function.Injective toMt := by decide +kernel

theorem toMt_surj : Function.Surjective toMt := by decide +kernel

theorem toMt_det : ∀ v : Vec, detQ v = (toMt v).det := by decide +kernel

@[expose] noncomputable def thetaV : Vec ≃* Multiplicative Mt :=
  MulEquiv.ofBijective
    (MonoidHom.mk' (fun v => Multiplicative.ofAdd (toMt v)) fun v w => by
      rw [toMt_mul]
      rfl)
    ⟨fun v w h => toMt_inj (Multiplicative.ofAdd.injective h), fun X => by
      obtain ⟨v, hv⟩ := toMt_surj (Multiplicative.toAdd X)
      exact ⟨v, by simp [hv]⟩⟩

theorem toAdd_thetaV (v : Vec) : Multiplicative.toAdd (thetaV v) = toMt v := rfl

@[expose] def matSL : DihedralGroup 3 → SL(2, ZMod 2)
  | DihedralGroup.r i =>
      if i = 0 then ⟨!![1, 0; 0, 1], by decide⟩
      else if i = 1 then ⟨!![0, 1; 1, 1], by decide⟩ else ⟨!![1, 1; 1, 0], by decide⟩
  | DihedralGroup.sr i =>
      if i = 0 then ⟨!![0, 1; 1, 0], by decide⟩
      else if i = 1 then ⟨!![1, 1; 0, 1], by decide⟩ else ⟨!![1, 0; 1, 1], by decide⟩

theorem matSL_mul : ∀ a b : DihedralGroup 3, matSL (a * b) = matSL a * matSL b := by decide +kernel

theorem matSL_inj : Function.Injective matSL := by decide +kernel

theorem matSL_surj : Function.Surjective matSL := by decide +kernel

@[expose] noncomputable def dihSL : DihedralGroup 3 ≃* SL(2, ZMod 2) :=
  MulEquiv.ofBijective (MonoidHom.mk' matSL matSL_mul) ⟨matSL_inj, matSL_surj⟩

@[expose] def slT (A : SL(2, ZMod 2)) : SL(2, ZMod 2) :=
  ⟨(A : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ, by rw [Matrix.det_transpose]; exact A.2⟩

@[expose] def PsiFun (γ : Gam) : OmG := (matSL γ.1, slT (matSL γ.2⁻¹))

theorem PsiFun_mul : ∀ γ δ : Gam, PsiFun (γ * δ) = PsiFun γ * PsiFun δ := by decide +kernel

theorem PsiFun_inj : Function.Injective PsiFun := by decide +kernel

theorem PsiFun_surj : Function.Surjective PsiFun := by decide +kernel

@[expose] noncomputable def Psi : Gam ≃* OmG :=
  MulEquiv.ofBijective (MonoidHom.mk' PsiFun PsiFun_mul) ⟨PsiFun_inj, PsiFun_surj⟩

theorem toMt_act : ∀ (γ : Gam) (v : Vec), toMt (act γ v) = omSmul (PsiFun γ) (toMt v) := by
  decide +kernel

theorem orbit_span_mt : ∀ X : Mt, X ≠ 0 → X.det = 0 → ∀ Y : Mt,
    ∃ l₁ l₂ : OmG, l₁ ^ 3 = 1 ∧ l₂ ^ 3 = 1 ∧ Y = omSmul l₁ X + omSmul l₂ X := by
  decide +kernel

theorem swap_fact₁ : ∀ a : DihedralGroup 3, ∃ b : DihedralGroup 3, ∀ v : Vec,
    transV (act (a, 1) (transV v)) = act (1, b) v := by
  decide +kernel

theorem swap_fact₂ : ∀ b : DihedralGroup 3, ∃ a : DihedralGroup 3, ∀ v : Vec,
    transV (act (1, b) (transV v)) = act (a, 1) v := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem lemmaG : ∀ A : Gam, A ≠ 1 → A ^ 3 = 1 → ∀ S : Gam, S ≠ 1 → S ^ 2 = 1 → S * A * S⁻¹ = A⁻¹ →
    ∀ B : Gam, B ≠ 1 → B ^ 3 = 1 → A * B = B * A → S * B = B * S →
    ∀ T : Gam, T ≠ 1 → T ^ 2 = 1 → T * B * T⁻¹ = B⁻¹ → A * T = T * A → S * T = T * S →
    (A.2 = 1 ∧ S.2 = 1 ∧ B.1 = 1 ∧ T.1 = 1) ∨ (A.1 = 1 ∧ S.1 = 1 ∧ B.2 = 1 ∧ T.2 = 1) := by
  decide +kernel

theorem dih_cases : ∀ x : DihedralGroup 3, ∃ k : Fin 3, x = DihedralGroup.r 1 ^ (k : ℕ) ∨
    x = DihedralGroup.r 1 ^ (k : ℕ) * DihedralGroup.sr 0 := by
  decide +kernel

theorem dih_rel : (DihedralGroup.r 1 : DihedralGroup 3) ≠ 1 ∧
    (DihedralGroup.r 1 : DihedralGroup 3) ^ 3 = 1 ∧
    (DihedralGroup.sr 0 : DihedralGroup 3) ≠ 1 ∧ (DihedralGroup.sr 0 : DihedralGroup 3) ^ 2 = 1 ∧
    (DihedralGroup.sr 0 : DihedralGroup 3) * DihedralGroup.r 1 * (DihedralGroup.sr 0)⁻¹ =
      (DihedralGroup.r 1)⁻¹ := by
  decide +kernel

theorem nat_card_dih : Nat.card (DihedralGroup 3) = 6 := by
  rw [DihedralGroup.nat_card]

end S153E54

end CFSG.Quasithin
