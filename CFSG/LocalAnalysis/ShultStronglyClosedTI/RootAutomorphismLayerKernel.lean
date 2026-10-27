module

public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.LocalAnalysis.ComponentInitial

variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
  [MulAction.IsPretransitive G Ω] [FaithfulSMul G Ω]

theorem regular_root_automorphism_layer_kernel_of_normalizes (hΩ : 3 ≤ Nat.card Ω)
    {p : ℕ} [Fact p.Prime] {ξ η : Ω} (hξη : ξ ≠ η) (P : Sylow p G)
    (hPξ : (P : Subgroup G) ≤ MulAction.stabilizer G ξ)
    (hPn : ((P : Subgroup G).subgroupOf (MulAction.stabilizer G ξ)).Normal)
    (htr : ∀ ω ω' : Ω, ω ≠ ξ → ω' ≠ ξ → ∃ u : (P : Subgroup G), (u : G) • ω = ω')
    (V : Subgroup G) [(V.subgroupOf (P : Subgroup G)).Normal]
    (hVZ : ∀ v ∈ V, ∀ x ∈ (P : Subgroup G), v * x = x * v)
    (hPV : ∀ x y : (P : Subgroup G) ⧸ V.subgroupOf (P : Subgroup G), x * y = y * x)
    (hVT : ∀ t ∈ MulAction.stabilizer G ξ ⊓ MulAction.stabilizer G η, ∀ v ∈ V, t * v * t⁻¹ ∈ V)
    (hlayer : V = P ∨
      ((∀ t ∈ MulAction.stabilizer G ξ ⊓ MulAction.stabilizer G η,
          (∀ x ∈ (P : Subgroup G), x⁻¹ * (t * x * t⁻¹) ∈ V) → t = 1) ∧
        ∀ ℓ : (P : Subgroup G) ⧸ V.subgroupOf (P : Subgroup G) →* V,
          (∀ t ∈ MulAction.stabilizer G ξ ⊓ MulAction.stabilizer G η,
            ∀ x y : (P : Subgroup G), (y : G) = t * x * t⁻¹ → (ℓ y : G) = t * ℓ x * t⁻¹) →
          ℓ = 1))
    (γ : MulAut G) (hγP : (P : Subgroup G).map γ.toMonoidHom = P)
    (hγV : ∀ v ∈ V, γ v = v) (hγPV : ∀ x ∈ (P : Subgroup G), x⁻¹ * γ x ∈ V) :
    ∃ b ∈ (P : Subgroup G), γ = MulAut.conj b := by
  obtain ⟨-, -, -, -, φ, -, hφξ, -, τ, hτφ, hτinj, hτsmul, hτconj⟩ :=
    Suzuki_Sylow_point_recovery hΩ ξ P hPξ hPn htr
  have hconj : ∀ t ∈ MulAction.stabilizer G ξ, ∀ x ∈ (P : Subgroup G),
      t * x * t⁻¹ ∈ (P : Subgroup G) :=
    fun t ht x hx => (Subgroup.normal_subgroupOf_iff hPξ).1 hPn x t hx ht
  have hγξ : τ γ ξ = ξ := by
    apply φ.injective
    rw [hτφ, hφξ]
    exact Sylow.ext (by rw [coe_mulAut_smul_sylow', hγP])
  have hγη : τ γ η ≠ ξ := fun h => hξη ((τ γ).injective (hγξ.trans h.symm))
  obtain ⟨b, hb⟩ := htr (τ γ η) η hγη hξη.symm
  set γ' := MulAut.conj (b : G) * γ with hγ'
  have hγ'_apply : ∀ g, γ' g = b * γ g * (b : G)⁻¹ := fun g => rfl
  have hτ' : ∀ ω, τ γ' ω = (b : G) • τ γ ω := fun ω => by
    rw [hγ', map_mul, Equiv.Perm.mul_apply, hτconj]
  have hγ'ξ : τ γ' ξ = ξ := by
    rw [hτ', hγξ]
    exact hPξ b.2
  have hγ'η : τ γ' η = η := by rw [hτ', hb]
  have hb' : ∀ x ∈ (P : Subgroup G), x⁻¹ * ((b : G) * x * (b : G)⁻¹) ∈ V := by
    intro x hx
    have h := hPV (QuotientGroup.mk ⟨(b : G)⁻¹, inv_mem b.2⟩) (QuotientGroup.mk ⟨x, hx⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h
    convert h using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]
  have hγ'V : ∀ v ∈ V, γ' v = v := by
    intro v hv
    rw [hγ'_apply, hγV v hv, ← hVZ v hv _ b.2, mul_inv_cancel_right]
  have hγ'PV : ∀ x ∈ (P : Subgroup G), x⁻¹ * γ' x ∈ V := by
    intro x hx
    have hd := hγPV x hx
    have hdb : x⁻¹ * γ x * (b : G)⁻¹ = (b : G)⁻¹ * (x⁻¹ * γ x) := hVZ _ hd _ (inv_mem b.2)
    have heq : x⁻¹ * γ' x = x⁻¹ * ((b : G) * x * (b : G)⁻¹) * (x⁻¹ * γ x) := by
      rw [hγ'_apply]
      calc x⁻¹ * ((b : G) * γ x * (b : G)⁻¹)
          = x⁻¹ * (b : G) * x * (x⁻¹ * γ x * (b : G)⁻¹) := by group
        _ = x⁻¹ * ((b : G) * x * (b : G)⁻¹) * (x⁻¹ * γ x) := by rw [hdb]; group
    rw [heq]
    exact mul_mem (hb' x hx) hd
  have hfixP : ∀ x ∈ (P : Subgroup G), γ' x = x := by
    rcases hlayer with hVPeq | ⟨hfaith, hhom⟩
    · intro x hx
      exact hγ'V x (hVPeq ▸ hx)
    have hγ'T : ∀ t ∈ MulAction.stabilizer G ξ ⊓ MulAction.stabilizer G η,
        γ' t ∈ MulAction.stabilizer G ξ ⊓ MulAction.stabilizer G η := by
      intro t ht
      obtain ⟨ht1, ht2⟩ := Subgroup.mem_inf.1 ht
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have h := hτsmul γ' t ξ
        rw [show t • ξ = ξ from ht1, hγ'ξ] at h
        exact h.symm
      · have h := hτsmul γ' t η
        rw [show t • η = η from ht2, hγ'η] at h
        exact h.symm
    have hγ'Tfix : ∀ t ∈ MulAction.stabilizer G ξ ⊓ MulAction.stabilizer G η, γ' t = t := by
      intro t ht
      have hs := hγ'T t ht
      have key : ∀ x ∈ (P : Subgroup G),
          x⁻¹ * ((t⁻¹ * γ' t) * x * (t⁻¹ * γ' t)⁻¹) ∈ V := by
        intro x hx
        have hy : t * x * t⁻¹ ∈ (P : Subgroup G) := hconj t (Subgroup.mem_inf.1 ht).1 x hx
        have h1 := hγ'PV _ hy
        have h2 := hVT _ hs _ (hγ'PV x hx)
        have h3 : (t * x * t⁻¹)⁻¹ * (γ' t * x * (γ' t)⁻¹) ∈ V := by
          have heq : (t * x * t⁻¹)⁻¹ * (γ' t * x * (γ' t)⁻¹) =
              (t * x * t⁻¹)⁻¹ * γ' (t * x * t⁻¹) *
                (γ' t * (x⁻¹ * γ' x) * (γ' t)⁻¹)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
            group
          rw [heq]
          exact mul_mem h1 (inv_mem h2)
        have h4 := hVT _ (inv_mem ht) _ h3
        convert h4 using 1
        group
      exact (inv_mul_eq_one.1 (hfaith _ (mul_mem (inv_mem ht) hs) key)).symm
    let δ : (P : Subgroup G) →* V :=
      { toFun := fun x => ⟨(x : G)⁻¹ * γ' x, hγ'PV x x.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by
          have hc := hVZ _ (hγ'PV x x.2) _ (inv_mem y.2)
          change ((x : G) * y)⁻¹ * γ' ((x : G) * y) =
            (x : G)⁻¹ * γ' x * ((y : G)⁻¹ * γ' y)
          calc ((x : G) * y)⁻¹ * γ' ((x : G) * y)
              = (y : G)⁻¹ * ((x : G)⁻¹ * γ' x) * γ' y := by rw [map_mul]; group
            _ = (x : G)⁻¹ * γ' x * ((y : G)⁻¹ * γ' y) := by rw [← hc]; group) }
    have hδ : ∀ x : (P : Subgroup G), (δ x : G) = (x : G)⁻¹ * γ' x := fun x => rfl
    have hδV : V.subgroupOf (P : Subgroup G) ≤ δ.ker := fun v hv => by
      rw [MonoidHom.mem_ker]
      refine Subtype.ext ?_
      rw [hδ, hγ'V _ (Subgroup.mem_subgroupOf.1 hv), inv_mul_cancel]
      rfl
    have hℓ := hhom (QuotientGroup.lift (V.subgroupOf (P : Subgroup G)) δ hδV)
      (fun t ht x y hy => by
        rw [QuotientGroup.lift_mk, QuotientGroup.lift_mk, hδ, hδ, hy, map_mul, map_mul,
          map_inv, hγ'Tfix t ht]
        group)
    intro x hx
    have h := congrArg (fun f => (f (QuotientGroup.mk ⟨x, hx⟩) : G)) hℓ
    simp only [QuotientGroup.lift_mk, hδ, MonoidHom.one_apply, OneMemClass.coe_one] at h
    exact (inv_mul_eq_one.1 h).symm
  have hτ1 : τ γ' = 1 := by
    refine Equiv.ext fun ω => ?_
    rw [Equiv.Perm.one_apply]
    by_cases hω : ω = ξ
    · rw [hω, hγ'ξ]
    · obtain ⟨x, hx⟩ := htr η ω hξη.symm hω
      rw [← hx, hτsmul, hfixP _ x.2, hγ'η]
  have hγ'1 : γ' = 1 := hτinj (hτ1.trans (map_one τ).symm)
  refine ⟨(b : G)⁻¹, inv_mem b.2, ?_⟩
  calc γ = (MulAut.conj (b : G))⁻¹ * γ' := by rw [hγ', inv_mul_cancel_left]
    _ = MulAut.conj (b : G)⁻¹ := by rw [hγ'1, mul_one, map_inv]

theorem regular_root_automorphism_layer_kernel (hΩ : 3 ≤ Nat.card Ω)
    {p : ℕ} [Fact p.Prime] {ξ η : Ω} (hξη : ξ ≠ η) (P : Sylow p G)
    (hPξ : (P : Subgroup G) ≤ MulAction.stabilizer G ξ)
    (hPn : ((P : Subgroup G).subgroupOf (MulAction.stabilizer G ξ)).Normal)
    (htr : ∀ ω ω' : Ω, ω ≠ ξ → ω' ≠ ξ → ∃ u : (P : Subgroup G), (u : G) • ω = ω')
    (V : Subgroup G) (hVP : V ≤ P) [(V.subgroupOf (P : Subgroup G)).Characteristic]
    (hVZ : ∀ v ∈ V, ∀ x ∈ (P : Subgroup G), v * x = x * v)
    (hPV : ∀ x y : (P : Subgroup G) ⧸ V.subgroupOf (P : Subgroup G), x * y = y * x)
    (hlayer : V = P ∨
      ((∀ t ∈ MulAction.stabilizer G ξ ⊓ MulAction.stabilizer G η,
          (∀ x ∈ (P : Subgroup G), x⁻¹ * (t * x * t⁻¹) ∈ V) → t = 1) ∧
        ∀ ℓ : (P : Subgroup G) ⧸ V.subgroupOf (P : Subgroup G) →* V,
          (∀ t ∈ MulAction.stabilizer G ξ ⊓ MulAction.stabilizer G η,
            ∀ x y : (P : Subgroup G), (y : G) = t * x * t⁻¹ → (ℓ y : G) = t * ℓ x * t⁻¹) →
          ℓ = 1))
    (γ : MulAut G) (hγP : (P : Subgroup G).map γ.toMonoidHom = P)
    (hγV : ∀ v ∈ V, γ v = v) (hγPV : ∀ x ∈ (P : Subgroup G), x⁻¹ * γ x ∈ V) :
    ∃ b ∈ (P : Subgroup G), γ = MulAut.conj b := by
  refine regular_root_automorphism_layer_kernel_of_normalizes hΩ hξη P hPξ hPn htr V hVZ hPV
    (fun t ht v hv => ?_) hlayer γ hγP hγV hγPV
  have hconj : ∀ s ∈ MulAction.stabilizer G ξ, ∀ x ∈ (P : Subgroup G),
      s * x * s⁻¹ ∈ (P : Subgroup G) :=
    fun s hs x hx => (Subgroup.normal_subgroupOf_iff hPξ).1 hPn x s hx hs
  have ht' : t ∈ MulAction.stabilizer G ξ := (Subgroup.mem_inf.1 ht).1
  let e : (P : Subgroup G) ≃* (P : Subgroup G) :=
    { toFun := fun x => ⟨t * x * t⁻¹, hconj t ht' x x.2⟩
      invFun := fun x => ⟨t⁻¹ * x * t⁻¹⁻¹, hconj t⁻¹ (inv_mem ht') x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have h := (Subgroup.Characteristic.fixed (inferInstance :
    (V.subgroupOf (P : Subgroup G)).Characteristic) e).ge
    (Subgroup.mem_subgroupOf.2 hv : (⟨v, hVP hv⟩ : (P : Subgroup G)) ∈ V.subgroupOf P)
  exact Subgroup.mem_subgroupOf.1 h

end CFSG.ShultStronglyClosedTI
