module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalExtTwistSetup

import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalExtAut
import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointVertex
import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalExtAutField

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par
open CFSG.Quasithin.H13.Sec53F.Unit (fieldAut fieldHom_mul fieldHom_one)

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem U4qExtLocalReduction.exists_twist_of_iso (R : U4qExtLocalReduction L1 L2 S f)
    (hH : Hyp111 L1 L2 S) (hf : 2 ≤ f) {K : Type} [Field K] (hU : UnitaryFieldData 2 f K)
    (Φ : (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 (S ⊓ L1))
      (L2 ⊔ bigB L1 L2 (S ⊓ L1))).Iso (RankTwoAmalgam.ofSubgroups (parP hU) (parP2 hU)))
    {τ : G} (hτS : τ ∈ S) (hτL : τ ∉ L1) :
    ∃ b₀ : hypSU hU 2 0, b₀ ∈ hypBorel hU 2 0 ∧
      (∀ x y : ↥(L1 ⊔ bigB L1 L2 (S ⊓ L1)), (y : G) = τ * x * τ⁻¹ →
        Subtype.val (Φ.φ1 y) = b₀ * u4FieldInvol hU (Subtype.val (Φ.φ1 x)) * b₀⁻¹) ∧
      ∀ x y : ↥(L2 ⊔ bigB L1 L2 (S ⊓ L1)), (y : G) = τ * x * τ⁻¹ →
        Subtype.val (Φ.φ2 y) = b₀ * u4FieldInvol hU (Subtype.val (Φ.φ2 x)) * b₀⁻¹ := by
  let φ₁ : ↥(L1 ⊔ bigB L1 L2 (S ⊓ L1)) ≃* ↥(parP hU) := Φ.φ1
  let φ₂ : ↥(L2 ⊔ bigB L1 L2 (S ⊓ L1)) ≃* ↥(parP2 hU) := Φ.φ2
  let c₁ : MulAut ↥(L1 ⊔ bigB L1 L2 (S ⊓ L1)) :=
    (L1 ⊔ bigB L1 L2 (S ⊓ L1)).normalizerMonoidHom ⟨τ, R.le_normalizer_sup_left hτS⟩
  let c₂ : MulAut ↥(L2 ⊔ bigB L1 L2 (S ⊓ L1)) :=
    (L2 ⊔ bigB L1 L2 (S ⊓ L1)).normalizerMonoidHom ⟨τ, R.le_normalizer_sup_right hτS⟩
  have hc₁ : ∀ a, ((c₁ a : ↥(L1 ⊔ bigB L1 L2 (S ⊓ L1))) : G) = τ * a * τ⁻¹ := fun _ => rfl
  have hc₂ : ∀ a, ((c₂ a : ↥(L2 ⊔ bigB L1 L2 (S ⊓ L1))) : G) = τ * a * τ⁻¹ := fun _ => rfl
  let θ₁ : MulAut ↥(parP hU) := (φ₁.symm.trans c₁).trans φ₁
  let θ₂ : MulAut ↥(parP2 hU) := (φ₂.symm.trans c₂).trans φ₂
  have hθ₁ : ∀ a, θ₁ (φ₁ a) = φ₁ (c₁ a) := fun a => by
    show φ₁ (c₁ (φ₁.symm (φ₁ a))) = φ₁ (c₁ a)
    rw [MulEquiv.symm_apply_apply]
  have hθ₂ : ∀ a, θ₂ (φ₂ a) = φ₂ (c₂ a) := fun a => by
    show φ₂ (c₂ (φ₂.symm (φ₂ a))) = φ₂ (c₂ a)
    rw [MulEquiv.symm_apply_apply]
  have hθ : ∀ (x : ↥(parP hU)) (y : ↥(parP2 hU)), (x : hypSU hU 2 0) = y →
      ((θ₁ x : ↥(parP hU)) : hypSU hU 2 0) = θ₂ y := by
    intro x y hxy
    have hab : ((φ₁.symm x : ↥(L1 ⊔ bigB L1 L2 (S ⊓ L1))) : G) =
        ((φ₂.symm y : ↥(L2 ⊔ bigB L1 L2 (S ⊓ L1))) : G) :=
      coe_ofSubgroupsIso_φ1_symm_eq_φ2_symm Φ hxy
    have e : ((c₁ (φ₁.symm x) : ↥(L1 ⊔ bigB L1 L2 (S ⊓ L1))) : G) =
        ((c₂ (φ₂.symm y) : ↥(L2 ⊔ bigB L1 L2 (S ⊓ L1))) : G) := by
      rw [hc₁, hc₂, hab]
    exact coe_ofSubgroupsIso_φ1_eq_φ2 Φ e
  obtain ⟨e, d, ρ, hdT, h1, h2⟩ := exists_stdAut_eq_of_agree_inf_u4 hU hf θ₁ θ₂ hθ
  obtain ⟨b₀, hb₀def⟩ : ∃ b₀ : hypSU hU 2 0, b₀ = (e : hypSU hU 2 0)⁻¹ * d := ⟨_, rfl⟩
  have hb₀ : b₀ ∈ parP hU ⊓ parP2 hU := by
    rw [hb₀def]
    exact mul_mem (inv_mem e.2) (hypTorus_le_inf_u4 hU hdT)
  have hΨ : ∀ g : hypSU hU 2 0, (MulAut.conj (e : hypSU hU 2 0)⁻¹ * u4StdAut hU d ρ) g =
      b₀ * fieldAut hU ρ g * b₀⁻¹ := by
    intro g
    rw [MulAut.mul_apply, MulAut.conj_apply, u4StdAut_apply, hb₀def]
    group
  have k₁ : ∀ x : ↥(parP hU), ((θ₁ x : ↥(parP hU)) : hypSU hU 2 0) =
      b₀ * fieldAut hU ρ x * b₀⁻¹ := fun x => (h1 x).trans (hΨ x)
  have k₂ : ∀ x : ↥(parP2 hU), ((θ₂ x : ↥(parP2 hU)) : hypSU hU 2 0) =
      b₀ * fieldAut hU ρ x * b₀⁻¹ := fun x => (h2 x).trans (hΨ x)
  have hsq : τ * τ ∈ S ⊓ L1 := by
    rw [← pow_two]
    exact R.sq_mem_inf hτS
  let g : ↥(L1 ⊔ bigB L1 L2 (S ⊓ L1)) := ⟨τ * τ, Subgroup.mem_sup_left hsq.2⟩
  have hcc : ∀ a, c₁ (c₁ a) = g * a * g⁻¹ := fun a => Subtype.ext (by
    show τ * (τ * (a : G) * τ⁻¹) * τ⁻¹ = τ * τ * a * (τ * τ)⁻¹
    group)
  have hθθ : ∀ x, θ₁ (θ₁ x) = φ₁ g * x * (φ₁ g)⁻¹ := by
    intro x
    show φ₁ (c₁ (φ₁.symm (φ₁ (c₁ (φ₁.symm x))))) = _
    rw [MulEquiv.symm_apply_apply, hcc, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hρ2 : ρ * ρ = RingEquiv.refl K := by
    have hg' : (b₀ * fieldAut hU ρ b₀)⁻¹ * ((φ₁ g : ↥(parP hU)) : hypSU hU 2 0) ∈ parP hU :=
      mul_mem (inv_mem (mul_mem hb₀.1 ((fieldAut_mem_parP_iff_u4 hU ρ b₀).mpr hb₀.1)))
        (φ₁ g).2
    refine eq_refl_of_stdAut_eq_conj_u4 hU (one_mem _) hg' fun x hx => ?_
    have hxP : x ∈ parP hU := (radQ_le_inf_u4 hU hx).1
    have e1 := k₁ (θ₁ ⟨x, hxP⟩)
    rw [hθθ, k₁, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk, map_mul,
      map_mul, map_inv] at e1
    rw [u4StdAut_apply, show fieldAut hU (ρ * ρ) x = fieldAut hU ρ (fieldAut hU ρ x) from
      fieldHom_mul hU ρ ρ x]
    calc 1 * fieldAut hU ρ (fieldAut hU ρ x) * 1⁻¹
        = (b₀ * fieldAut hU ρ b₀)⁻¹ * (b₀ * (fieldAut hU ρ b₀ * fieldAut hU ρ (fieldAut hU ρ x) *
            (fieldAut hU ρ b₀)⁻¹) * b₀⁻¹) * (b₀ * fieldAut hU ρ b₀) := by group
      _ = (b₀ * fieldAut hU ρ b₀)⁻¹ * (((φ₁ g : ↥(parP hU)) : hypSU hU 2 0) * x *
            ((φ₁ g : ↥(parP hU)) : hypSU hU 2 0)⁻¹) * (b₀ * fieldAut hU ρ b₀) := by rw [e1]
      _ = (b₀ * fieldAut hU ρ b₀)⁻¹ * ((φ₁ g : ↥(parP hU)) : hypSU hU 2 0) * x *
            ((b₀ * fieldAut hU ρ b₀)⁻¹ * ((φ₁ g : ↥(parP hU)) : hypSU hU 2 0))⁻¹ := by group
  have hρρ : ∀ x, ρ (ρ x) = x := fun x => by
    have h := RingEquiv.congr_fun hρ2 x
    rwa [RingAut.mul_apply, RingEquiv.refl_apply] at h
  rcases eq_refl_or_eq_bar_of_involutive_u4 hU ρ hρρ with hρ1 | hρσ
  ·
    have hid : ∀ y : hypSU hU 2 0, fieldAut hU ρ y = y := fun y => by
      rw [hρ1]
      exact fieldHom_one hU y
    refine (R.false_of_conj_eq_conj hH Φ hτS hτL hb₀ (fun x y hxy => ?_)
      (fun x y hxy => ?_)).elim
    · obtain rfl : y = c₁ x := Subtype.ext hxy
      show ((φ₁ (c₁ x) : ↥(parP hU)) : hypSU hU 2 0) =
        b₀ * ((φ₁ x : ↥(parP hU)) : hypSU hU 2 0) * b₀⁻¹
      rw [← hθ₁, k₁, hid]
    · obtain rfl : y = c₂ x := Subtype.ext hxy
      show ((φ₂ (c₂ x) : ↥(parP2 hU)) : hypSU hU 2 0) =
        b₀ * ((φ₂ x : ↥(parP2 hU)) : hypSU hU 2 0) * b₀⁻¹
      rw [← hθ₂, k₂, hid]
  ·
    have hσ : fieldAut hU ρ = u4FieldInvol hU := fieldAut_eq_u4FieldInvol hU hρσ
    refine ⟨b₀, ?_, fun x y hxy => ?_, fun x y hxy => ?_⟩
    · rw [← parP_inf_parP2_eq_u4 hU]
      exact hb₀
    · obtain rfl : y = c₁ x := Subtype.ext hxy
      show ((φ₁ (c₁ x) : ↥(parP hU)) : hypSU hU 2 0) =
        b₀ * u4FieldInvol hU ((φ₁ x : ↥(parP hU)) : hypSU hU 2 0) * b₀⁻¹
      rw [← hθ₁, k₁, hσ]
    · obtain rfl : y = c₂ x := Subtype.ext hxy
      show ((φ₂ (c₂ x) : ↥(parP2 hU)) : hypSU hU 2 0) =
        b₀ * u4FieldInvol hU ((φ₂ x : ↥(parP2 hU)) : hypSU hU 2 0) * b₀⁻¹
      rw [← hθ₂, k₂, hσ]

theorem U4qLocalData.exists_twist_of_ext (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    ∃ (K : Type) (_ : Field K) (hU : UnitaryFieldData 2 f K)
      (Φ : (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 (S ⊓ L1))
        (L2 ⊔ bigB L1 L2 (S ⊓ L1))).Iso (RankTwoAmalgam.ofSubgroups (parP hU) (parP2 hU)))
      (τ : G) (b₀ : hypSU hU 2 0), τ ∈ S ∧ τ ∉ L1 ⊔ bigB L1 L2 (S ⊓ L1) ∧
      τ ∉ L2 ⊔ bigB L1 L2 (S ⊓ L1) ∧ b₀ ∈ hypBorel hU 2 0 ∧
      (∀ x y : ↥(L1 ⊔ bigB L1 L2 (S ⊓ L1)), (y : G) = τ * x * τ⁻¹ →
        Subtype.val (Φ.φ1 y) = b₀ * u4FieldInvol hU (Subtype.val (Φ.φ1 x)) * b₀⁻¹) ∧
      ∀ x y : ↥(L2 ⊔ bigB L1 L2 (S ⊓ L1)), (y : G) = τ * x * τ⁻¹ →
        Subtype.val (Φ.φ2 y) = b₀ * u4FieldInvol hU (Subtype.val (Φ.φ2 x)) * b₀⁻¹ := by
  have R := hD.extension_reduction hH hf hS2
  obtain ⟨F, hF, -, ⟨c₁⟩⟩ := R.data.exists_coordLeft R.hyp R.card_inf
  obtain ⟨K, hK, -, ⟨c₂⟩⟩ := R.data.exists_coordRight R.hyp R.card_inf
  letI := hF
  letI := hK
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hD.one_le, c₂.card⟩
  obtain ⟨ψ₁, hψ₁Q, hψ₁N⟩ := R.data.exists_mulEquiv_parP hf R.hyp R.card_inf c₁ c₂ hU
  obtain ⟨ψ₂, hψ₂Q, -, hψ₂N⟩ := R.data.exists_mulEquiv_parP2 R.hyp R.card_inf c₁ c₂ hU
  obtain ⟨Φ⟩ :=
    amalgamIso_psu4_of_mulEquiv hf R.hyp R.data R.card_inf hU ψ₁ hψ₁Q hψ₁N ψ₂ hψ₂Q hψ₂N
  obtain ⟨τ, hτS, hτL⟩ := R.exists_mem_notMem_left
  obtain ⟨b₀, hb₀, h1, h2⟩ := R.exists_twist_of_iso hH hf hU Φ hτS hτL
  exact ⟨K, hK, hU, Φ, τ, b₀, hτS, R.notMem_sup_bigB_left hτS hτL,
    R.notMem_sup_bigB_right hτS hτL, hb₀, h1, h2⟩

end CFSG.Quasithin.F112R.St84

end
