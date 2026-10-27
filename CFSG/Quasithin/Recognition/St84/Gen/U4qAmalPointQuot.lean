module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointMaps
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointSylow
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalForm

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par

variable {G : Type} [Group G] {L1 L2 S : Subgroup G} {f : ℕ} {F : Type*} [Field F]
  {K : Type} [Field K]

private theorem matrix_row_add (A B : Matrix (Fin 2) (Fin 2) F) (i : Fin 2) :
    (A + B) i = A i + B i :=
  rfl

@[expose] noncomputable def U4qCoordLeft.pointPhi (c₁ : U4qCoordLeft L1 L2 S f F)
    (φ : (Fin 2 → F) →+ K) : ↥(pCoreOf 2 L1) →* Multiplicative (K × K) where
  toFun u := Multiplicative.ofAdd
    (φ (Multiplicative.toAdd (c₁.β u) 0), φ (Multiplicative.toAdd (c₁.β u) 1))
  map_one' := by
    apply Multiplicative.toAdd.injective
    have h0 : (0 : Matrix (Fin 2) (Fin 2) F) 0 = 0 := rfl
    have h1 : (0 : Matrix (Fin 2) (Fin 2) F) 1 = 0 := rfl
    rw [toAdd_ofAdd, map_one, toAdd_one, h0, h1, map_zero, toAdd_one, Prod.mk_zero_zero]
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    have e : Multiplicative.toAdd (c₁.β (u * v)) =
        Multiplicative.toAdd (c₁.β u) + Multiplicative.toAdd (c₁.β v) := by
      rw [map_mul, toAdd_mul]
    rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd, e, matrix_row_add, matrix_row_add,
      map_add, map_add, Prod.mk_add_mk]

theorem U4qCoordLeft.toAdd_pointPhi (c₁ : U4qCoordLeft L1 L2 S f F) (φ : (Fin 2 → F) →+ K)
    (u : ↥(pCoreOf 2 L1)) :
    Multiplicative.toAdd (c₁.pointPhi φ u) =
      (φ (Multiplicative.toAdd (c₁.β u) 0), φ (Multiplicative.toAdd (c₁.β u) 1)) :=
  rfl

theorem U4qCoordLeft.pointPhi_surjective (c₁ : U4qCoordLeft L1 L2 S f F)
    {φ : (Fin 2 → F) →+ K} (hφ : Function.Bijective φ) : Function.Surjective (c₁.pointPhi φ) := by
  intro w
  obtain ⟨r₀, hr₀⟩ := hφ.2 (Multiplicative.toAdd w).1
  obtain ⟨r₁, hr₁⟩ := hφ.2 (Multiplicative.toAdd w).2
  obtain ⟨u, hu⟩ := c₁.surjective_β (Multiplicative.ofAdd (Matrix.of ![r₀, r₁]))
  refine ⟨u, Multiplicative.toAdd.injective ?_⟩
  have e0 : Multiplicative.toAdd (Multiplicative.ofAdd (Matrix.of ![r₀, r₁])) 0 = r₀ := rfl
  have e1 : Multiplicative.toAdd (Multiplicative.ofAdd (Matrix.of ![r₀, r₁])) 1 = r₁ := rfl
  rw [c₁.toAdd_pointPhi, hu, e0, e1, hr₀, hr₁]

theorem U4qCoordLeft.pointPhi_eq_one_iff (c₁ : U4qCoordLeft L1 L2 S f F)
    {φ : (Fin 2 → F) →+ K} (hφ : Function.Injective φ) (u : ↥(pCoreOf 2 L1)) :
    c₁.pointPhi φ u = 1 ↔ (u : G) ∈ centerOf (pCoreOf 2 L1) := by
  have hker : (u : G) ∈ centerOf (pCoreOf 2 L1) ↔ c₁.β u = 1 := by
    rw [← Subgroup.mem_subgroupOf, ← c₁.ker_β, MonoidHom.mem_ker]
  rw [hker]
  constructor
  · intro h1
    have h1' := congrArg Multiplicative.toAdd h1
    rw [c₁.toAdd_pointPhi, toAdd_one] at h1'
    obtain ⟨h0, h1⟩ := Prod.mk.inj h1'
    have r0 : Multiplicative.toAdd (c₁.β u) 0 = 0 := hφ (h0.trans (map_zero φ).symm)
    have r1 : Multiplicative.toAdd (c₁.β u) 1 = 0 := hφ (h1.trans (map_zero φ).symm)
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    funext i
    fin_cases i
    · exact r0
    · exact r1
  · intro h1
    apply Multiplicative.toAdd.injective
    rw [c₁.toAdd_pointPhi, h1, toAdd_one, toAdd_one]
    have z0 : (0 : Matrix (Fin 2) (Fin 2) F) 0 = 0 := rfl
    have z1 : (0 : Matrix (Fin 2) (Fin 2) F) 1 = 0 := rfl
    rw [z0, z1, map_zero, Prod.mk_zero_zero]

theorem U4qCoordLeft.toAdd_pointPhi_conj (c₁ : U4qCoordLeft L1 L2 S f F)
    {φ : (Fin 2 → F) →+ K} {ρ : F →+* K} (hρ : ∀ (τ : F) (v : Fin 2 → F), φ (τ • v) = ρ τ * φ v)
    (x : ↥L1) (u v : ↥(pCoreOf 2 L1)) (hv : (v : G) = x * u * x⁻¹) :
    Multiplicative.toAdd (c₁.pointPhi φ v) =
      (ρ ((c₁.α x : Matrix (Fin 2) (Fin 2) F) 0 0) * (Multiplicative.toAdd (c₁.pointPhi φ u)).1 +
          ρ ((c₁.α x : Matrix (Fin 2) (Fin 2) F) 0 1) * (Multiplicative.toAdd (c₁.pointPhi φ u)).2,
        ρ ((c₁.α x : Matrix (Fin 2) (Fin 2) F) 1 0) * (Multiplicative.toAdd (c₁.pointPhi φ u)).1 +
          ρ ((c₁.α x : Matrix (Fin 2) (Fin 2) F) 1 1) *
            (Multiplicative.toAdd (c₁.pointPhi φ u)).2) := by
  have h := c₁.equivariant x u v hv
  set A : Matrix (Fin 2) (Fin 2) F := (c₁.α x : Matrix (Fin 2) (Fin 2) F)
  set X : Matrix (Fin 2) (Fin 2) F := Multiplicative.toAdd (c₁.β u)
  have hrow : ∀ i, Multiplicative.toAdd (c₁.β v) i = A i 0 • X 0 + A i 1 • X 1 := by
    intro i
    rw [h]
    funext j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [c₁.toAdd_pointPhi, c₁.toAdd_pointPhi, hrow 0, hrow 1, map_add, map_add, hρ, hρ, hρ, hρ]

instance centerOf_subgroupOf_normal_u4 (Q : Subgroup G) : ((centerOf Q).subgroupOf Q).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (g : G) * n * (g : G)⁻¹ = n := by
      rw [Subgroup.mem_centralizer_iff.mp hn.2 (g : G) g.2, mul_inv_cancel_right]
    simpa [hc] using hn⟩

variable (h : UnitaryFieldData 2 f K)

instance zRad_subgroupOf_radQ_normal_u4 : ((zRad h).subgroupOf (radQ h)).Normal := by
  rw [← centerOf_radQ h]
  infer_instance

theorem U4qCoordLeft.ker_pointPhi (c₁ : U4qCoordLeft L1 L2 S f F) {φ : (Fin 2 → F) →+ K}
    (hφ : Function.Injective φ) :
    (c₁.pointPhi φ).ker = (centerOf (pCoreOf 2 L1)).subgroupOf (pCoreOf 2 L1) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, c₁.pointPhi_eq_one_iff hφ]

theorem ker_radPhi_u4 : (radPhi h).ker = (zRad h).subgroupOf (radQ h) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, radPhi_eq_one_iff]

@[expose] noncomputable def U4qCoordLeft.pointQuotK (c₁ : U4qCoordLeft L1 L2 S f F)
    {φ : (Fin 2 → F) →+ K} (hφ : Function.Bijective φ) :
    ↥(pCoreOf 2 L1) ⧸ (centerOf (pCoreOf 2 L1)).subgroupOf (pCoreOf 2 L1) ≃*
      Multiplicative (K × K) :=
  (QuotientGroup.quotientMulEquivOfEq (c₁.ker_pointPhi hφ.1)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (c₁.pointPhi_surjective hφ))

@[expose] noncomputable def radQuotK :
    ↥(radQ h) ⧸ (zRad h).subgroupOf (radQ h) ≃* Multiplicative (K × K) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_radPhi_u4 h)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (radPhi_surjective h))

theorem U4qCoordLeft.pointQuotK_mk (c₁ : U4qCoordLeft L1 L2 S f F) {φ : (Fin 2 → F) →+ K}
    (hφ : Function.Bijective φ) (u : ↥(pCoreOf 2 L1)) :
    c₁.pointQuotK hφ (QuotientGroup.mk u) = c₁.pointPhi φ u :=
  rfl

theorem radQuotK_mk (g : ↥(radQ h)) : radQuotK h (QuotientGroup.mk g) = radPhi h g :=
  rfl

@[expose] noncomputable def U4qCoordLeft.pointQuotEquiv (c₁ : U4qCoordLeft L1 L2 S f F)
    {φ : (Fin 2 → F) →+ K} (hφ : Function.Bijective φ) :
    ↥(pCoreOf 2 L1) ⧸ (centerOf (pCoreOf 2 L1)).subgroupOf (pCoreOf 2 L1) ≃*
      ↥(radQ h) ⧸ (zRad h).subgroupOf (radQ h) :=
  (c₁.pointQuotK hφ).trans (radQuotK h).symm

theorem U4qCoordLeft.pointQuotEquiv_mk_eq_mk_iff (c₁ : U4qCoordLeft L1 L2 S f F)
    {φ : (Fin 2 → F) →+ K} (hφ : Function.Bijective φ) (u : ↥(pCoreOf 2 L1))
    (v' : ↥(radQ h)) :
    c₁.pointQuotEquiv h hφ (QuotientGroup.mk u) = QuotientGroup.mk v' ↔
      c₁.pointPhi φ u = radPhi h v' := by
  rw [U4qCoordLeft.pointQuotEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_eq, radQuotK_mk,
    c₁.pointQuotK_mk]

@[expose] noncomputable def PointFormData.centerEquiv {Q Z L : Subgroup G} {F' : Type*} [Field F']
    (D : PointFormData Q Z L F') : Multiplicative F' ≃* ↥Z :=
  (MonoidHom.ofInjective D.ζ_injective).trans (MulEquiv.subgroupCongr D.range_ζ)

theorem PointFormData.coe_centerEquiv {Q Z L : Subgroup G} {F' : Type*} [Field F']
    (D : PointFormData Q Z L F') (t : Multiplicative F') : (D.centerEquiv t : G) = D.ζ t := by
  simp [PointFormData.centerEquiv, MonoidHom.ofInjective_apply]

@[expose] noncomputable def pointCenterEquiv {Q Z L : Subgroup G} (D : PointFormData Q Z L F)
    (ρ : F ≃+* h.fixedField) (δ : h.fixedField) (hδ : δ ≠ 0) : ↥Z ≃* ↥(zRad h) :=
  D.centerEquiv.symm.trans
    ((AddEquiv.toMultiplicative (ρ.toAddEquiv.trans
      { toFun := fun t => δ * t
        invFun := fun t => δ⁻¹ * t
        left_inv := fun t => by
          show δ⁻¹ * (δ * t) = t
          rw [← mul_assoc, inv_mul_cancel₀ hδ, one_mul]
        right_inv := fun t => by
          show δ * (δ⁻¹ * t) = t
          rw [← mul_assoc, mul_inv_cancel₀ hδ, one_mul]
        map_add' := fun a b => mul_add δ a b })).trans (zRadEquiv h))

theorem pointCenterEquiv_centerEquiv {Q Z L : Subgroup G} (D : PointFormData Q Z L F)
    (ρ : F ≃+* h.fixedField) (δ : h.fixedField) (hδ : δ ≠ 0) (t : F) :
    pointCenterEquiv h D ρ δ hδ (D.centerEquiv (Multiplicative.ofAdd t)) =
      zRadEquiv h (Multiplicative.ofAdd (δ * ρ t)) := by
  simp only [pointCenterEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem U4qCoordLeft.pointCenterEquiv_sq (c₁ : U4qCoordLeft L1 L2 S f F)
    (D : PointFormData (pCoreOf 2 L1) (centerOf (pCoreOf 2 L1)) L1 F) (hDβ : D.β = c₁.β)
    (ρ : F ≃+* h.fixedField) {φ : (Fin 2 → F) →+ K} (hφ : Function.Bijective φ)
    (hρ : ∀ (τ : F) (v : Fin 2 → F), φ (τ • v) = (ρ τ : K) * φ v) (δ : h.fixedField)
    (hδv : (δ : K) = h.bar (φ (Pi.single 0 1)) * φ (Pi.single 1 1) +
      φ (Pi.single 0 1) * h.bar (φ (Pi.single 1 1))) (hδ : δ ≠ 0)
    (u : ↥(pCoreOf 2 L1)) (v' : ↥(radQ h)) (huv : c₁.pointPhi φ u = radPhi h v')
    (hz : (u : G) ^ 2 ∈ centerOf (pCoreOf 2 L1)) :
    ((pointCenterEquiv h D ρ δ hδ ⟨(u : G) ^ 2, hz⟩ : ↥(zRad h)) : hypSU h 2 0) =
      (v' : hypSU h 2 0) ^ 2 := by
  have := h.charP
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [c₁.card]; positivity)
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c₁.card])
  set X : Matrix (Fin 2) (Fin 2) F := Multiplicative.toAdd (c₁.β u)
  have hsq : (⟨(u : G) ^ 2, hz⟩ : ↥(centerOf (pCoreOf 2 L1))) =
      D.centerEquiv (Multiplicative.ofAdd X.det) := by
    apply Subtype.ext
    show (u : G) ^ 2 = (D.centerEquiv (Multiplicative.ofAdd X.det) : G)
    rw [D.coe_centerEquiv, pow_two, D.mul_self_eq, hDβ]
  rw [hsq, pointCenterEquiv_centerEquiv]
  obtain ⟨x, y, c, -, hv'⟩ := v'.2
  have hxy : radPhi h v' = Multiplicative.ofAdd (x, y) := radPhi_apply h hv'
  rw [hxy] at huv
  have hxy' := congrArg Multiplicative.toAdd huv
  rw [c₁.toAdd_pointPhi, toAdd_ofAdd] at hxy'
  obtain ⟨hx, hy⟩ := Prod.mk.inj hxy'
  apply hypSU_ext h
  rw [coe_zRadEquiv, pow_two, coe_mul_hypSU, hv', sMat_mul_self_u4]
  congr 1
  let ρK : F →+* K := h.fixedField.subtype.comp ρ.toRingHom
  have hρK : ∀ a, h.bar (ρK a) = ρK a := fun a => (h.mem_fixedField).mp (ρ a).2
  have htw := twistForm_eq_smul_det h.bar ρK hρK φ hρ (X 0) (X 1)
  simp only [toAdd_ofAdd]
  rw [Subfield.coe_mul, hδv, ← hx, ← hy]
  have hdet : X.det = X 0 0 * X 1 1 + X 0 1 * X 1 0 := by
    rw [Matrix.det_fin_two, sub_eq_add_neg, CharTwo.neg_eq]
  have hρdet : ((ρ X.det : h.fixedField) : K) = ρK (X 0 0 * X 1 1 + X 0 1 * X 1 0) := by
    rw [hdet]; rfl
  rw [hρdet, ← htw]
  ring

theorem PointFormData.exists_mul_self_eq {Q Z L : Subgroup G}
    (D : PointFormData Q Z L F) {z : G} (hz : z ∈ Z) : ∃ u : ↥Q, (u : G) * u = z := by
  obtain ⟨t, rfl⟩ : ∃ t, D.ζ t = z := by
    rw [← D.range_ζ] at hz
    exact hz
  obtain ⟨u, hu⟩ := D.β_surjective
    (Multiplicative.ofAdd (Matrix.of ![![Multiplicative.toAdd t, 0], ![0, 1]]))
  refine ⟨u, ?_⟩
  rw [D.mul_self_eq, hu]
  congr 1
  simp [Matrix.det_fin_two]

end CFSG.Quasithin.F112R.St84

end
