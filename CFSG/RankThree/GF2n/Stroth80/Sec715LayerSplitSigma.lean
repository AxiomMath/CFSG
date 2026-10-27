module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplitTorus

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix

variable {K : Type} [Field K]

local notation "M8" => Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K
local notation "GL8" => GL (Fin 4 ⊕ Fin 4) K

variable {u w : Fin 4 ⊕ Fin 4 → K}

theorem sq_sub_one_eq_zero (huw : IsTSLine8 u w) {g : GL8} (hg : IsLongRoot8 u w g) :
    ((g : M8) - 1) * ((g : M8) - 1) = 0 := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
  set x := ((g : M8) - 1) *ᵥ Pi.single j 1 with hxdef
  have hx : x ∈ Submodule.span K {u, w} := by
    have := hg.1 (Pi.single j 1)
    rw [hxdef, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact this
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx
  have hperp : ∀ y ∈ Submodule.span K {u, w}, (g : M8) *ᵥ y = y := by
    intro y hy
    obtain ⟨a', b', rfl⟩ := Submodule.mem_span_pair.mp hy
    refine hg.2 _ ?_ ?_
    · rw [statedQuadPlus_polar, polar_add_left, polar_smul_left, polar_smul_left, polar_self,
        quadPlus_u huw, polar_comm _ w u, polar_u_w huw]
      simp
    · rw [statedQuadPlus_polar, polar_add_left, polar_smul_left, polar_smul_left, polar_self,
        quadPlus_w huw, polar_u_w huw]
      simp
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hperp x hx, sub_self]

section Root

variable {X H : Type} [AddCommGroup X] [Module K X] [Group H]

theorem exists_root_param [Finite K] [CharP K 2] (φ : H →* GL8)
    (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)) (huw : IsTSLine8 u w) {r₀ : H}
    (hr₀ : IsLongRoot8 u w (φ r₀)) (κ : K) :
    ∃ r : H, IsLongRoot8 u w (φ r) ∧ ((φ r : M8) - 1) = κ • ((φ r₀ : M8) - 1) := by
  by_cases hκ : κ = 0
  · subst hκ
    refine ⟨1, ⟨fun v => ?_, fun v _ _ => ?_⟩, ?_⟩
    · rw [map_one φ, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec, sub_self]
      exact Submodule.zero_mem _
    · rw [map_one φ, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    · rw [map_one φ, Matrix.GeneralLinearGroup.coe_one, sub_self, zero_smul]
  · have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    obtain ⟨A, hAΩ, hAu, hAw⟩ := exists_torus8 h2 huw (Units.mk0 κ hκ)
    obtain ⟨s, hs⟩ : A ∈ φ.range := hφ ▸ hAΩ
    have hφr₀ : φ r₀ ∈ StatedOmega (StatedQuadPlus 4 K) := hφ ▸ ⟨r₀, rfl⟩
    obtain ⟨hconj, hlr⟩ := conj_longRoot8 huw (isometry_of_mem_statedOmega hφr₀) hr₀
      (isometry_of_mem_statedOmega hAΩ) hAu hAw
    refine ⟨s * r₀ * s⁻¹, ?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, hs]
      exact hlr
    · rw [map_mul, map_mul, map_inv, hs, hconj, Units.val_mk0]

theorem act_eq_of_phi_eq (φ : H →* GL8) (act : H →* (X ≃ₗ[K] X))
    (hker : ∀ h, φ h = 1 → act h = 1) {r r' : H} (h : φ r = φ r') : act r = act r' := by
  have h1 : φ (r * r'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 := hker _ h1
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  exact h2

end Root

theorem add_self_eq_zero' [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V] (x : V) : x + x = 0 := by
  rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]

theorem sq_eq_one_of_longRoot8 [CharP K 2] (huw : IsTSLine8 u w) {g : GL8} (hg : IsLongRoot8 u w g) :
    g * g = 1 := by
  have hD2 := sq_sub_one_eq_zero huw hg
  refine Units.ext (Matrix.ext_of_mulVec_single fun j => ?_)
  set v : Fin 4 ⊕ Fin 4 → K := Pi.single j 1
  have h := congrArg (· *ᵥ v) hD2
  simp only [Matrix.zero_mulVec] at h
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_sub] at h
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, Units.val_one, Matrix.one_mulVec]
  have e1 : (g : M8) *ᵥ ((g : M8) *ᵥ v) = ((g : M8) *ᵥ v + (g : M8) *ᵥ v) - v := by
    have := sub_eq_zero.mp h
    rw [sub_eq_iff_eq_add] at this
    rw [this]
    abel
  rw [e1, add_self_eq_zero' (K := K), zero_sub, neg_eq_of_add_eq_zero_left (add_self_eq_zero' (K := K) v)]

section Sigma

variable {X H : Type} [AddCommGroup X] [Module K X] [Group H]

theorem act_sub_sq_eq_zero [CharP K 2] (φ : H →* GL8) (act : H →* (X ≃ₗ[K] X))
    (hker : ∀ h, φ h = 1 → act h = 1) (huw : IsTSLine8 u w) {r₀ : H}
    (hr₀ : IsLongRoot8 u w (φ r₀)) (y : X) : act r₀ (act r₀ y - y) - (act r₀ y - y) = 0 := by
  have hsq : act r₀ * act r₀ = 1 := by
    rw [← map_mul]
    exact hker _ (by rw [map_mul]; exact sq_eq_one_of_longRoot8 huw hr₀)
  have h1 : act r₀ (act r₀ y) = y := by
    rw [← LinearEquiv.mul_apply, hsq, linEquiv_one_apply]
  rw [map_sub, h1]
  calc y - act r₀ y - (act r₀ y - y) = (y + y) - (act r₀ y + act r₀ y) := by abel
    _ = 0 := by rw [add_self_eq_zero' (K := K) y, add_self_eq_zero' (K := K) (act r₀ y), sub_zero]

theorem exists_ringEquiv_root [Finite K] [CharP K 2] (φ : H →* GL8)
    (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)) (act : H →* (X ≃ₗ[K] X))
    (hker : ∀ h, φ h = 1 → act h = 1) {Y : Submodule K X} (hY : IsInvSub act Y)
    (huw : IsTSLine8 u w)
    (hroot : ∀ r r' : H, IsLongRoot8 u w (φ r) → IsLongRoot8 u w (φ r') → φ r ≠ 1 →
      ∃ c : K, ∀ y ∈ Y, act r' y - y = c • (act r y - y))
    {r₀ : H} (hr₀ : IsLongRoot8 u w (φ r₀)) (hne : ∃ y ∈ Y, act r₀ y ≠ y) :
    ∃ σ : K ≃+* K, ∀ r : H, IsLongRoot8 u w (φ r) → ∀ κ : K,
      ((φ r : M8) - 1) = κ • ((φ r₀ : M8) - 1) → ∀ y ∈ Y, act r y - y = σ κ • (act r₀ y - y) := by
  classical
  have hr₀1 : φ r₀ ≠ 1 := by
    intro h
    obtain ⟨y, -, hy⟩ := hne
    exact hy (by rw [hker r₀ h]; rfl)
  have hφeq : ∀ r r' : H, (φ r : M8) - 1 = (φ r' : M8) - 1 → act r = act r' := fun r r' h =>
    act_eq_of_phi_eq φ act hker (Units.ext (sub_left_inj.mp h))
  let P : K → K → Prop := fun κ c => ∀ r : H, IsLongRoot8 u w (φ r) →
    ((φ r : M8) - 1) = κ • ((φ r₀ : M8) - 1) → ∀ y ∈ Y, act r y - y = c • (act r₀ y - y)
  have hPex : ∀ κ, ∃ c, P κ c := by
    intro κ
    obtain ⟨r₁, hr₁, hr₁κ⟩ := exists_root_param φ hφ huw hr₀ κ
    obtain ⟨c, hc⟩ := hroot r₀ r₁ hr₀ hr₁ hr₀1
    exact ⟨c, fun r hr hrκ y hy => by rw [hφeq r r₁ (hrκ.trans hr₁κ.symm)]; exact hc y hy⟩
  have hPuniq : ∀ κ c c', P κ c → P κ c' → c = c' := by
    intro κ c c' hc hc'
    obtain ⟨r₁, hr₁, hr₁κ⟩ := exists_root_param φ hφ huw hr₀ κ
    obtain ⟨y, hy, hy0⟩ := hne
    have h1 := hc r₁ hr₁ hr₁κ y hy
    have h2 := hc' r₁ hr₁ hr₁κ y hy
    have h3 : (c - c') • (act r₀ y - y) = 0 := by rw [sub_smul, ← h1, ← h2, sub_self]
    rcases smul_eq_zero.mp h3 with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd (sub_eq_zero.mp h0) hy0
  let cf : K → K := fun κ => Classical.choose (hPex κ)
  have hcf : ∀ κ, P κ (cf κ) := fun κ => Classical.choose_spec (hPex κ)
  have hcf_apply : ∀ κ (r : H), IsLongRoot8 u w (φ r) → ((φ r : M8) - 1) = κ • ((φ r₀ : M8) - 1) →
      ∀ y ∈ Y, act r y - y = cf κ • (act r₀ y - y) := fun κ => hcf κ
  have hPof : ∀ κ c (r₁ : H), ((φ r₁ : M8) - 1) = κ • ((φ r₀ : M8) - 1) →
      (∀ y ∈ Y, act r₁ y - y = c • (act r₀ y - y)) → P κ c := fun κ c r₁ h1 h2 r _ hrκ y hy => by
    rw [hφeq r r₁ (hrκ.trans h1.symm)]
    exact h2 y hy
  have hcf_of : ∀ κ c (r₁ : H), ((φ r₁ : M8) - 1) = κ • ((φ r₀ : M8) - 1) →
      (∀ y ∈ Y, act r₁ y - y = c • (act r₀ y - y)) → cf κ = c := fun κ c r₁ h1 h2 =>
    hPuniq κ _ _ (hcf κ) (hPof κ c r₁ h1 h2)
  have he2 : ∀ y : X, act r₀ (act r₀ y - y) - (act r₀ y - y) = 0 :=
    act_sub_sq_eq_zero φ act hker huw hr₀
  have heY : ∀ y ∈ Y, act r₀ y - y ∈ Y := fun y hy => Y.sub_mem (hY r₀ y hy) hy
  have hDD := sq_sub_one_eq_zero huw hr₀
  have hcf0 : cf 0 = 0 := hcf_of 0 0 1 (by rw [map_one φ, Units.val_one, sub_self, zero_smul])
    (fun y _ => by rw [map_one, linEquiv_one_apply, sub_self, zero_smul])
  have hcf1 : cf 1 = 1 := hcf_of 1 1 r₀ (one_smul _ _).symm (fun y _ => (one_smul _ _).symm)
  have hcfadd : ∀ κ₁ κ₂, cf (κ₁ + κ₂) = cf κ₁ + cf κ₂ := by
    intro κ₁ κ₂
    obtain ⟨r₁, hr₁, hr₁κ⟩ := exists_root_param φ hφ huw hr₀ κ₁
    obtain ⟨r₂, hr₂, hr₂κ⟩ := exists_root_param φ hφ huw hr₀ κ₂
    refine hcf_of _ _ (r₁ * r₂) ?_ fun y hy => ?_
    · have e1 : (φ r₁ : M8) = 1 + κ₁ • ((φ r₀ : M8) - 1) := by rw [← hr₁κ]; abel
      have e2 : (φ r₂ : M8) = 1 + κ₂ • ((φ r₀ : M8) - 1) := by rw [← hr₂κ]; abel
      rw [map_mul, Units.val_mul, e1, e2, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul,
        smul_mul_smul_comm, hDD, smul_zero, add_zero, add_smul]
      abel
    · have h2 := hcf_apply κ₂ r₂ hr₂ hr₂κ y hy
      have h1 := hcf_apply κ₁ r₁ hr₁ hr₁κ y hy
      have h1e := hcf_apply κ₁ r₁ hr₁ hr₁κ _ (heY y hy)
      rw [he2, smul_zero, sub_eq_zero] at h1e
      rw [map_mul, LinearEquiv.mul_apply, eq_add_of_sub_eq h2, map_add, map_smul, h1e,
        eq_add_of_sub_eq h1, add_smul]
      abel
  have hcfmul : ∀ κ₁ κ₂, cf (κ₁ * κ₂) = cf κ₁ * cf κ₂ := by
    intro κ₁ κ₂
    by_cases hκ : κ₁ = 0
    · rw [hκ, zero_mul, hcf0, zero_mul]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    obtain ⟨A, hAΩ, hAu, hAw⟩ := exists_torus8 h2 huw (Units.mk0 κ₁ hκ)
    obtain ⟨s, hs⟩ : A ∈ φ.range := hφ ▸ hAΩ
    obtain ⟨r₂, hr₂, hr₂κ⟩ := exists_root_param φ hφ huw hr₀ κ₂
    have hiso : ∀ r : H, ∀ v, quadPlus 4 K ((φ r : M8) *ᵥ v) = quadPlus 4 K v := fun r =>
      isometry_of_mem_statedOmega (hφ ▸ ⟨r, rfl⟩)
    obtain ⟨hc₀, hl₀⟩ := conj_longRoot8 huw (hiso r₀) hr₀ (isometry_of_mem_statedOmega hAΩ) hAu hAw
    obtain ⟨hc₂, -⟩ := conj_longRoot8 huw (hiso r₂) hr₂ (isometry_of_mem_statedOmega hAΩ) hAu hAw
    have hconj : ∀ r : H, φ (s * r * s⁻¹) = A * φ r * A⁻¹ := fun r => by
      rw [map_mul, map_mul, map_inv, hs]
    rw [Units.val_mk0] at hc₀ hc₂
    have hl₀' : IsLongRoot8 u w (φ (s * r₀ * s⁻¹)) := by rw [hconj]; exact hl₀
    have hc₀' : (φ (s * r₀ * s⁻¹) : M8) - 1 = κ₁ • ((φ r₀ : M8) - 1) := by rw [hconj]; exact hc₀
    have hact : ∀ (r : H) (y : X), act (s * r * s⁻¹) y = act s (act r (act s⁻¹ y)) := fun r y => by
      rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have hss : ∀ y : X, act s (act s⁻¹ y) = y := fun y => by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, linEquiv_one_apply]
    refine hcf_of _ _ (s * r₂ * s⁻¹) ?_ fun y hy => ?_
    · rw [hconj, hc₂, hr₂κ, smul_smul]
    · have hy' : act s⁻¹ y ∈ Y := hY _ _ hy
      have h2 := hcf_apply κ₂ r₂ hr₂ hr₂κ _ hy'
      have h0 := hcf_apply κ₁ _ hl₀' hc₀' y hy
      rw [hact, eq_add_of_sub_eq h2, map_add, map_smul, hss, map_sub, ← hact, hss, h0, smul_smul,
        mul_comm]
      abel
  let σ' : K →+* K :=
    { toFun := cf
      map_one' := hcf1
      map_mul' := hcfmul
      map_zero' := hcf0
      map_add' := hcfadd }
  have hbij : Function.Bijective σ' :=
    ⟨σ'.injective, Finite.surjective_of_injective σ'.injective⟩
  exact ⟨RingEquiv.ofBijective σ' hbij, fun r hr κ hrκ y hy => hcf κ r hr hrκ y hy⟩

end Sigma

end CFSG.RankThree.GF2n.Stroth80.S715L
