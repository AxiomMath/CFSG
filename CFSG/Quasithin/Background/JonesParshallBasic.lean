module

public import CFSG.Quasithin.Background.B4ModelsWitness

public section

namespace CFSG.Quasithin.JonesParshall

section Binary

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def Z1 (ρ : Representation (ZMod 2) G V) : Submodule (ZMod 2) (G → V) where
  carrier := {f | ∀ g h, f (g * h) = f g + ρ g (f h)}
  add_mem' {f f'} hf hf' g h := by
    simp only [Pi.add_apply, hf g h, hf' g h, map_add]
    abel
  zero_mem' g h := by simp
  smul_mem' c f hf g h := by
    simp only [Pi.smul_apply, hf g h, map_smul, smul_add]

@[expose] def coboundary (ρ : Representation (ZMod 2) G V) : V →ₗ[ZMod 2] (G → V) where
  toFun v g := ρ g v - v
  map_add' v w := by
    funext g
    simp only [map_add, Pi.add_apply]
    abel
  map_smul' c v := by
    funext g
    simp [smul_sub]

@[expose] def B1 (ρ : Representation (ZMod 2) G V) : Submodule (ZMod 2) (G → V) :=
  LinearMap.range (coboundary ρ)

theorem B1_le_Z1 (ρ : Representation (ZMod 2) G V) : B1 ρ ≤ Z1 ρ := by
  rintro _ ⟨v, rfl⟩ g h
  simp only [coboundary, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Module.End.mul_apply,
    map_sub]
  abel

abbrev H1 (ρ : Representation (ZMod 2) G V) : Type _ :=
  ↥(Z1 ρ) ⧸ (B1 ρ).comap (Z1 ρ).subtype

end Binary

section Additive

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M]

@[expose] def Z1A (μ : G →* AddMonoid.End M) : AddSubgroup (G → M) where
  carrier := {f | ∀ g h, f (g * h) = f g + μ g (f h)}
  add_mem' {f f'} hf hf' g h := by
    simp only [Pi.add_apply, hf g h, hf' g h, map_add]
    abel
  zero_mem' g h := by simp
  neg_mem' {f} hf g h := by
    simp only [Pi.neg_apply, hf g h, map_neg]
    abel

@[expose] def coboundaryA (μ : G →* AddMonoid.End M) : M →+ (G → M) where
  toFun m g := μ g m - m
  map_zero' := by
    funext g
    simp
  map_add' m m' := by
    funext g
    simp only [map_add, Pi.add_apply]
    abel

@[expose] def B1A (μ : G →* AddMonoid.End M) : AddSubgroup (G → M) :=
  (coboundaryA μ).range

theorem mem_Z1A {μ : G →* AddMonoid.End M} {f : G → M} :
    f ∈ Z1A μ ↔ ∀ g h, f (g * h) = f g + μ g (f h) := Iff.rfl

theorem coboundaryA_apply (μ : G →* AddMonoid.End M) (m : M) (g : G) :
    coboundaryA μ m g = μ g m - m := rfl

theorem B1A_le_Z1A (μ : G →* AddMonoid.End M) : B1A μ ≤ Z1A μ := by
  rintro _ ⟨m, rfl⟩ g h
  change μ (g * h) m - m = (μ g m - m) + μ g (μ h m - m)
  rw [map_mul]
  change μ g (μ h m) - m = (μ g m - m) + μ g (μ h m - m)
  rw [map_sub]
  abel

variable {μ : G →* AddMonoid.End M}

theorem Z1A_one {f : G → M} (hf : f ∈ Z1A μ) : f 1 = 0 := by
  have h := hf 1 1
  rw [one_mul, map_one, AddMonoid.End.coe_one, id_eq] at h
  exact left_eq_add.mp h

theorem Z1A_mul_vanish {f : G → M} (hf : f ∈ Z1A μ) {g h : G} (hh : f h = 0) :
    f (g * h) = f g := by
  rw [hf, hh, map_zero, add_zero]

theorem Z1A_conj {f : G → M} (hf : f ∈ Z1A μ) (g h : G) :
    f (g * h * g⁻¹) = μ g (f h) + f g - μ (g * h * g⁻¹) (f g) := by
  have h1 : f (g * h * g⁻¹ * g) = f (g * h * g⁻¹) + μ (g * h * g⁻¹) (f g) := hf _ _
  rw [inv_mul_cancel_right, hf] at h1
  rw [eq_sub_iff_add_eq, ← h1]
  abel

theorem mem_B1A_of_vanish [Finite G] (h2 : ∀ m : M, m + m = 0) {H : Subgroup G}
    (hodd : Odd H.index) {f : G → M} (hf : f ∈ Z1A μ) (hH : ∀ h ∈ H, f h = 0) :
    f ∈ B1A μ := by
  classical
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hconst : ∀ x y : G, (x : G ⧸ H) = y → f x = f y := fun x y hxy => by
    have hxy' : x⁻¹ * y ∈ H := QuotientGroup.eq.mp hxy
    calc f x = f (x * (x⁻¹ * y)) := (Z1A_mul_vanish hf (hH _ hxy')).symm
      _ = f y := by rw [mul_inv_cancel_left]
  let u : M := ∑ c : G ⧸ H, f c.out
  have hcard : Fintype.card (G ⧸ H) = H.index := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  refine ⟨-u, funext fun g => ?_⟩
  have hsum : ∑ c : G ⧸ H, f (g * c.out) = u := by
    have hc : ∀ c : G ⧸ H, f (g * c.out) = f (g • c).out := fun c => by
      apply hconst
      rw [QuotientGroup.out_eq']
      calc ((g * c.out : G) : G ⧸ H) = g • ((c.out : G) : G ⧸ H) := rfl
        _ = g • c := by rw [QuotientGroup.out_eq']
    simp only [hc]
    exact Equiv.sum_comp (MulAction.toPerm g) (fun c : G ⧸ H => f c.out)
  have hgu : μ g u = u - Fintype.card (G ⧸ H) • f g := by
    have : μ g u = ∑ c : G ⧸ H, (f (g * c.out) - f g) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hf]
      abel
    rw [this, Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ]
  have hodd' : Fintype.card (G ⧸ H) • f g = f g := by
    rw [hcard]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, add_nsmul, one_nsmul, mul_nsmul, two_nsmul, h2, nsmul_zero, zero_add]
  rw [coboundaryA_apply, map_neg, hgu, hodd']
  abel

theorem mem_B1A_of_restrict [Finite G] (h2 : ∀ m : M, m + m = 0) {H : Subgroup G}
    (hodd : Odd H.index) {f : G → M} (hf : f ∈ Z1A μ) {m : M}
    (hH : ∀ h ∈ H, f h = μ h m - m) : f ∈ B1A μ := by
  have hf' : f - coboundaryA μ m ∈ Z1A μ := sub_mem hf (B1A_le_Z1A μ ⟨m, rfl⟩)
  have hv := mem_B1A_of_vanish h2 hodd hf' fun h hh => by
    rw [Pi.sub_apply, coboundaryA_apply, hH h hh, sub_self]
  have := add_mem hv ⟨m, rfl⟩
  rwa [sub_add_cancel] at this

end Additive

section Transport

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {G : Type*} [Group G] {M : Type*} [AddCommGroup M]

@[expose] def transportFun (θ : Γ ≃* G) (β : W ≃+ M) : (Γ → W) ≃+ (G → M) where
  toFun f g := β (f (θ.symm g))
  invFun f γ := β.symm (f (θ γ))
  left_inv f := by
    funext γ
    simp
  right_inv f := by
    funext g
    simp
  map_add' f f' := by
    funext g
    simp

variable {ρ : Representation (ZMod 2) Γ W} {μ : G →* AddMonoid.End M} {θ : Γ ≃* G} {β : W ≃+ M}

theorem transport_mem_Z1A (hβ : ∀ γ w, β (ρ γ w) = μ (θ γ) (β w)) {f : Γ → W} :
    transportFun θ β f ∈ Z1A μ ↔ f ∈ Z1 ρ := by
  constructor
  · intro hf γ δ
    have h := hf (θ γ) (θ δ)
    change β (f (θ.symm (θ γ * θ δ))) = β (f (θ.symm (θ γ))) + μ (θ γ) (β (f (θ.symm (θ δ))))
      at h
    rw [← map_mul, θ.symm_apply_apply, θ.symm_apply_apply, θ.symm_apply_apply, ← hβ,
      ← map_add] at h
    exact β.injective h
  · intro hf g h
    change β (f (θ.symm (g * h))) = β (f (θ.symm g)) + μ g (β (f (θ.symm h)))
    rw [map_mul, hf, map_add]
    congr 1
    conv_rhs => rw [← θ.apply_symm_apply g]
    rw [hβ]

theorem transport_mem_B1A (hβ : ∀ γ w, β (ρ γ w) = μ (θ γ) (β w)) {f : Γ → W} :
    transportFun θ β f ∈ B1A μ ↔ f ∈ B1 ρ := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨β.symm m, funext fun γ => ?_⟩
    have h := congrFun hm (θ γ)
    change μ (θ γ) m - m = β (f (θ.symm (θ γ))) at h
    rw [θ.symm_apply_apply] at h
    apply β.injective
    change β (ρ γ (β.symm m) - β.symm m) = β (f γ)
    rw [map_sub, hβ, AddEquiv.apply_symm_apply, h]
  · rintro ⟨w, rfl⟩
    refine ⟨β w, funext fun g => ?_⟩
    change μ g (β w) - β w = β (ρ (θ.symm g) w - w)
    rw [map_sub, hβ, MulEquiv.apply_symm_apply]

theorem card_Z1_eq (hβ : ∀ γ w, β (ρ γ w) = μ (θ γ) (β w)) :
    Nat.card (Z1 ρ) = Nat.card (Z1A μ) :=
  Nat.card_congr ((transportFun θ β).toEquiv.subtypeEquiv fun _ =>
    (transport_mem_Z1A hβ).symm)

theorem card_B1_eq (hβ : ∀ γ w, β (ρ γ w) = μ (θ γ) (β w)) :
    Nat.card (B1 ρ) = Nat.card (B1A μ) :=
  Nat.card_congr ((transportFun θ β).toEquiv.subtypeEquiv fun _ =>
    (transport_mem_B1A hβ).symm)

theorem card_H1_mul (ρ : Representation (ZMod 2) Γ W) [Finite Γ] [Finite W] :
    Nat.card (H1 ρ) * Nat.card (B1 ρ) = Nat.card (Z1 ρ) := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup
  have hB : Nat.card ((B1 ρ).comap (Z1 ρ).subtype) = Nat.card (B1 ρ) :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : Γ → W), x.2⟩
        invFun := fun x => ⟨⟨x.1, B1_le_Z1 ρ x.2⟩, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [h, ← hB]
  rfl

theorem finrank_H1_of_card (ρ : Representation (ZMod 2) Γ W) [Finite Γ] [Finite W] {d : ℕ}
    (h : Nat.card (H1 ρ) = 2 ^ d) : Module.finrank (ZMod 2) (H1 ρ) = d := by
  have hfin : Finite (H1 ρ) := by
    have : Finite (Γ → W) := Pi.finite
    have : Finite ↥(Z1 ρ) := Subtype.finite
    exact Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have h' := FiniteField.pow_finrank_eq_natCard 2 (H1 ρ)
  rw [h] at h'
  exact Nat.pow_right_injective le_rfl h'

theorem card_H1_eq_of_card (ρ : Representation (ZMod 2) Γ W) [Finite Γ] [Finite W]
    (hβ : ∀ γ w, β (ρ γ w) = μ (θ γ) (β w)) {k : ℕ}
    (hk : Nat.card (Z1A μ) = k * Nat.card (B1A μ)) : Nat.card (H1 ρ) = k := by
  have h := card_H1_mul ρ
  rw [card_Z1_eq hβ, hk, card_B1_eq hβ] at h
  have hpos : 0 < Nat.card (B1A μ) := by
    have : Finite (G → M) := by
      have : Finite G := Finite.of_equiv Γ θ.toEquiv
      have : Finite M := Finite.of_equiv W β.toEquiv
      exact Pi.finite
    exact Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h

end Transport

section TopBot

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def secEquivAmb (D : FFModel) (hs : D.sec = ⊤) (hk : D.ker = ⊥) :
    D.Sec ≃* D.Amb :=
  MulEquiv.ofBijective (QuotientGroup.lift _ D.sec.subtype fun x hx => by
      rw [Subgroup.mem_subgroupOf, hk, Subgroup.mem_bot] at hx
      exact hx)
    ⟨fun x y hxy => by
      induction x using QuotientGroup.induction_on with
      | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
      rw [QuotientGroup.lift_mk, QuotientGroup.lift_mk] at hxy
      exact congrArg _ (Subtype.ext hxy),
    fun a => ⟨QuotientGroup.mk ⟨a, (Subgroup.eq_top_iff' D.sec).mp hs a⟩, rfl⟩⟩

theorem secEquivAmb_mk (D : FFModel) (hs : D.sec = ⊤) (hk : D.ker = ⊥) (m : ↥D.sec) :
    secEquivAmb D hs hk (QuotientGroup.mk m) = m :=
  rfl

theorem Witness.ambient {D : FFModel} (hs : D.sec = ⊤) (hk : D.ker = ⊥)
    {ρ : Representation (ZMod 2) Γ W} {θ : Γ ≃* D.Gam} {β : W ≃+ Additive D.Sec}
    (h : D.Witness ρ θ β) :
    ∀ γ w, (β.trans (secEquivAmb D hs hk).toAdditive) (ρ γ w) =
      Additive.ofMul (D.act (θ γ)
        (Additive.toMul ((β.trans (secEquivAmb D hs hk).toAdditive) w))) := by
  intro γ w
  obtain ⟨-, -, -, hint⟩ := h
  set e := secEquivAmb D hs hk
  let m : ↥D.sec := ⟨e (Additive.toMul (β w)), (Subgroup.eq_top_iff' D.sec).mp hs _⟩
  have hm : D.act (θ γ) m ∈ D.sec := (Subgroup.eq_top_iff' D.sec).mp hs _
  have hw : β w = Additive.ofMul (QuotientGroup.mk m : D.Sec) := by
    apply Additive.toMul.injective
    apply e.injective
    rfl
  change Additive.ofMul (e (Additive.toMul (β (ρ γ w)))) = _
  rw [hint γ w m hm hw]
  rfl

end TopBot

end CFSG.Quasithin.JonesParshall
