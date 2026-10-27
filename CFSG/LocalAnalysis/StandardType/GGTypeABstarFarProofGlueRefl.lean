module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueVec

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix

section LamHom

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
  {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}

theorem GGFarCtx.eq_of_vecEq (hC : GGFarCtx p Bs φ₁ φ₂ x y) {b b' : G} (hb : b ∈ Bs)
    (hb' : b' ∈ Bs) {h₁ h₁' h₂ h₂' : Fin (n + 1) → Fˣ} (a₁ : GGActsVec φ₁ b h₁)
    (a₁' : GGActsVec φ₁ b' h₁') (a₂ : GGActsVec φ₂ b h₂) (a₂' : GGActsVec φ₂ b' h₂')
    (e₁ : GGVecEq h₁ h₁') (e₂ : GGVecEq h₂ h₂') : b = b' := by
  have hmem : b * b'⁻¹ ∈ Bs := Subgroup.mul_mem _ hb (Subgroup.inv_mem _ hb')
  have e₁' : GGVecEq (h₁ * h₁'⁻¹) 1 := fun k l => by
    simpa only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply, inv_one, mul_one] using e₁ k l
  have e₂' : GGVecEq (h₂ * h₂'⁻¹) 1 := fun k l => by
    simpa only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply, inv_one, mul_one] using e₂ k l
  have c₁ := GGActsVec.commute_of_vecEq_one (GGActsVec.mul a₁ (GGActsVec.inv a₁')) e₁'
  have c₂ := GGActsVec.commute_of_vecEq_one (GGActsVec.mul a₂ (GGActsVec.inv a₂')) e₂'
  exact mul_inv_eq_one.mp (hC.inj (b * b'⁻¹) hmem c₁ c₂)

@[expose] noncomputable def GGFarCtx.lamFun (hC : GGFarCtx p Bs φ₁ φ₂ x y) (k l : Fin (n + 1))
    (b : ↥Bs) : Fˣ :=
  (Classical.choose (hC.lifts.diag₁ (b : G) b.2)) l *
    ((Classical.choose (hC.lifts.diag₁ (b : G) b.2)) k)⁻¹

theorem GGFarCtx.lamFun_eq (hC : GGFarCtx p Bs φ₁ φ₂ x y) (k l : Fin (n + 1)) {b : ↥Bs}
    {h : Fin (n + 1) → Fˣ} (a : GGActsVec φ₁ (b : G) h) : hC.lamFun k l b = h l * (h k)⁻¹ := by
  let c : Fin (n + 1) → Fˣ := Classical.choose (hC.lifts.diag₁ (b : G) b.2)
  have hc : GGActsVec φ₁ (b : G) c := Classical.choose_spec (hC.lifts.diag₁ (b : G) b.2)
  have e := GGActsVec.vecEq hC.lifts.ker₁ a hc
  have h1 : h k * c l = h l * c k := by
    have h2 := e k l
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul] at h2
    exact h2
  show c l * (c k)⁻¹ = h l * (h k)⁻¹
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
  rw [mul_comm (c l) (h k)]
  exact h1

@[expose] noncomputable def GGFarCtx.lamHom (hC : GGFarCtx p Bs φ₁ φ₂ x y) (k l : Fin (n + 1)) :
    ↥Bs →* Fˣ where
  toFun := hC.lamFun k l
  map_one' := by
    have h := hC.lamFun_eq k l (b := 1) (h := 1)
      (GGActsVec.one_of_commute (g := ((1 : ↥Bs) : G)) (fun s => by simp))
    simpa only [Pi.one_apply, inv_one, mul_one] using h
  map_mul' b b' := by
    have hb := Classical.choose_spec (hC.lifts.diag₁ (b : G) b.2)
    have hb' := Classical.choose_spec (hC.lifts.diag₁ (b' : G) b'.2)
    have hmul := GGActsVec.mul hb hb'
    rw [hC.lamFun_eq k l (b := b * b') hmul, hC.lamFun_eq k l (b := b) hb,
      hC.lamFun_eq k l (b := b') hb']
    simp only [Pi.mul_apply, Pi.inv_apply, _root_.mul_inv_rev]
    ac_rfl

theorem GGFarCtx.lamHom_apply (hC : GGFarCtx p Bs φ₁ φ₂ x y) (k l : Fin (n + 1)) (b : ↥Bs) :
    hC.lamHom k l b = hC.lamFun k l b :=
  rfl

end LamHom

end CFSG.StandardType
