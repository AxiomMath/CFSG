module

public import CFSG.Quasithin.EmptyFaithful.SzN28X0Form

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN28

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem card_linearEquiv_three {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (hW : Module.finrank (ZMod 2) W = 3) : Nat.card (W ≃ₗ[ZMod 2] W) = 168 := by
  have : Module.Finite (ZMod 2) W := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 3) (ZMod 2) W := Module.finBasisOfFinrankEq (ZMod 2) W hW
  let e : GL (Fin 3) (ZMod 2) ≃* (W ≃ₗ[ZMod 2] W) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W)
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  simp [Fin.prod_univ_three, ZMod.card]

theorem card_dvd_linearEquiv {D : Subgroup (GLV V)} {J : Submodule (ZMod 2) V}
    (hinv : ∀ d ∈ D, ∀ j ∈ J, d j ∈ J) (hinj : ∀ d ∈ D, (∀ j ∈ J, d j = j) → d = 1) :
    Nat.card D ∣ Nat.card (J ≃ₗ[ZMod 2] J) := by
  let res : D →* (J ≃ₗ[ZMod 2] J) :=
    { toFun := fun d =>
        LinearEquiv.ofLinearMap ((d : GLV V).toLinearMap.restrict (hinv d d.2))
          (((d⁻¹ : D) : GLV V).toLinearMap.restrict (hinv _ (d⁻¹).2))
          (LinearMap.ext fun j => Subtype.ext (by
            have := congrArg (fun g : GLV V => g (j : V)) (mul_inv_cancel (d : GLV V))
            exact this))
          (LinearMap.ext fun j => Subtype.ext (by
            have := congrArg (fun g : GLV V => g (j : V)) (inv_mul_cancel (d : GLV V))
            exact this))
      map_one' := LinearEquiv.ext fun j => Subtype.ext rfl
      map_mul' := fun a b => LinearEquiv.ext fun j => Subtype.ext rfl }
  refine Subgroup.card_dvd_of_injective res fun a b hab => ?_
  have hab' : ∀ j ∈ J, (a : GLV V) j = (b : GLV V) j := by
    intro j hj
    have := congrArg (fun g : J ≃ₗ[ZMod 2] J => ((g ⟨j, hj⟩ : J) : V)) hab
    exact this
  have h1 : ((a⁻¹ * b : D) : GLV V) = 1 := by
    apply hinj _ (a⁻¹ * b).2
    intro j hj
    show (a : GLV V)⁻¹ ((b : GLV V) j) = j
    rw [← hab' j hj]
    have := congrArg (fun g : GLV V => g j) (inv_mul_cancel (a : GLV V))
    exact this
  exact inv_mul_eq_one.1 (Subtype.ext h1)

namespace F8Form

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ A : Subgroup (GLV V)} {I I' : Submodule (ZMod 2) V}
  {x : GLV V} (c : F8Form B Γ A I I' x)

include c in
theorem B_e_f_zero {v₁ e₀ f₀ : V} (hv₁ : v₁ = e₀ + f₀) (he : e₀ ∈ I) (hf : f₀ ∈ I')
    (hodd : Odd (MulAction.stabilizer Γ v₁).index) : B e₀ f₀ = 0 := by
  by_contra hB
  have key2 : ∀ y : ZMod 2, y ≠ 0 → y = 1 := by decide
  have hB1 : B e₀ f₀ = 1 := key2 _ hB
  have hfix_iff : ∀ γ ∈ Γ, γ v₁ = v₁ → (γ ∈ A → γ e₀ = e₀ ∧ γ f₀ = f₀) := by
    intro γ hγ hfix hγA
    rcases c.act_fix hγ he hf (by rw [← hv₁]; exact hfix) with h | h
    · exact ⟨h.2.1, h.2.2⟩
    · exact absurd hγA h.1
  let φ : V →ₗ[ZMod 2] ZMod 2 := B.flip f₀
  have hφ : ∀ v, φ v = B v f₀ := fun v => rfl
  let If : Submodule (ZMod 2) V := I ⊓ LinearMap.ker φ
  have hIf_mem : ∀ i, i ∈ If ↔ i ∈ I ∧ B i f₀ = 0 := fun i => by
    simp only [If, Submodule.mem_inf, LinearMap.mem_ker, hφ]
  have hIf3 : Module.finrank (ZMod 2) If = 3 := by
    have : Module.Finite (ZMod 2) I :=
      Module.finite_of_finrank_pos (by rw [c.data.rank4]; omega)
    let ψ : ↥I →ₗ[ZMod 2] ZMod 2 := φ.domRestrict I
    have hrange : LinearMap.range ψ = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro y
      have hy : y = 0 ∨ y = 1 := by revert y; decide
      rcases hy with rfl | rfl
      · exact ⟨0, map_zero _⟩
      · exact ⟨⟨e₀, he⟩, hB1⟩
    have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    rw [hrange, finrank_top, Module.finrank_self, c.data.rank4] at h1
    have h2 : If = (LinearMap.ker ψ).map I.subtype := by
      ext v
      rw [hIf_mem, Submodule.mem_map]
      constructor
      · rintro ⟨hv, hv0⟩
        exact ⟨⟨v, hv⟩, by simpa [ψ, hφ] using hv0, rfl⟩
      · rintro ⟨⟨v', hv'⟩, hker, rfl⟩
        exact ⟨hv', by simpa [ψ, hφ] using hker⟩
    rw [h2, Submodule.finrank_map_subtype_eq]
    omega
  let D : Subgroup (GLV V) :=
    { carrier := {d | d ∈ A ∧ d e₀ = e₀ ∧ d f₀ = f₀}
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
        show a (b e₀) = e₀
        rw [hb.2.1, ha.2.1], by
        show a (b f₀) = f₀
        rw [hb.2.2, ha.2.2]⟩
      one_mem' := ⟨A.one_mem, rfl, rfl⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by
        have h1 : a e₀ = e₀ := ha.2.1
        have h2 : (a⁻¹ * a) e₀ = e₀ := by rw [inv_mul_cancel]; rfl
        calc a⁻¹ e₀ = a⁻¹ (a e₀) := by rw [h1]
          _ = e₀ := h2, by
        have h1 : a f₀ = f₀ := ha.2.2
        have h2 : (a⁻¹ * a) f₀ = f₀ := by rw [inv_mul_cancel]; rfl
        calc a⁻¹ f₀ = a⁻¹ (a f₀) := by rw [h1]
          _ = f₀ := h2⟩ }
  have hDA : D ≤ A := fun d hd => hd.1
  have hinv : ∀ d ∈ D, ∀ j ∈ If, d j ∈ If := by
    intro d hd j hj
    rw [hIf_mem] at hj ⊢
    refine ⟨c.data.A_inv_I d hd.1 j hj.1, ?_⟩
    have := c.isom d (c.data.A_le hd.1) j f₀
    rw [hd.2.2] at this
    rw [this, hj.2]
  have hinj : ∀ d ∈ D, (∀ j ∈ If, d j = j) → d = 1 := by
    intro d hd hfix
    refine c.data.faithful_I d hd.1 fun i hi => ?_
    have hi1 : i + B i f₀ • e₀ ∈ If := by
      rw [hIf_mem]
      refine ⟨I.add_mem hi (I.smul_mem _ he), ?_⟩
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hB1,
        mul_one]
      exact (by decide : ∀ y : ZMod 2, y + y = 0) _
    have := hfix _ hi1
    rw [map_add, map_smul, hd.2.1] at this
    exact add_right_cancel this
  have hdvd : Nat.card D ∣ 168 := by
    have := card_dvd_linearEquiv hinv hinj
    rwa [card_linearEquiv_three hIf3] at this
  let A' : Subgroup ↥Γ := A.subgroupOf Γ
  let C : Subgroup ↥Γ := MulAction.stabilizer ↥Γ v₁
  have hDΓ : D ≤ Γ := hDA.trans c.data.A_le
  let D' : Subgroup ↥Γ := D.subgroupOf Γ
  have hA'n : A'.Normal := ⟨fun n hn g => by
    show ((g * n * g⁻¹ : ↥Γ) : GLV V) ∈ A
    have := c.data.A_normal g g.2 n hn
    simpa using this⟩
  have hD'A' : D' ≤ A' := fun d hd => hDA hd
  have hD'C : D' ≤ C := by
    intro d hd
    show (d : GLV V) v₁ = v₁
    have e1 : (d : GLV V) e₀ = e₀ := hd.2.1
    have e2 : (d : GLV V) f₀ = f₀ := hd.2.2
    rw [hv₁, map_add, e1, e2]
  have hCA'D' : C ⊓ A' ≤ D' := by
    intro g hg
    have hfix : (g : GLV V) v₁ = v₁ := hg.1
    have := hfix_iff g g.2 hfix hg.2
    exact ⟨hg.2, this.1, this.2⟩
  have hD'eq : D' = A' ⊓ C := le_antisymm (le_inf hD'A' hD'C) (by rw [inf_comm]; exact hCA'D')
  have hcardA' : Nat.card A' = 20160 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.data.A_le).toEquiv]
    exact c.data.card_A
  have hcardD' : Nat.card D' = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDΓ).toEquiv
  have h1 := Subgroup.relIndex_mul_index hD'C
  have h2 := Subgroup.relIndex_mul_index hD'A'
  rw [c.data.index_two] at h2
  have h3 : D'.relIndex C ∣ 2 := by
    have h : D'.relIndex C = A'.relIndex C := by rw [hD'eq, Subgroup.inf_relIndex_right]
    rw [h]
    have := Subgroup.relIndex_dvd_index_of_normal (H := A') (K := C)
    rwa [c.data.index_two] at this
  have h4 : Nat.card D' * D'.relIndex A' = 20160 := by
    have := Subgroup.card_mul_index (D'.subgroupOf A')
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD'A').toEquiv, hcardA'] at this
    exact this
  have h5 : D'.relIndex C * C.index = D'.relIndex A' * 2 := by rw [h1, h2]
  obtain ⟨k, hk⟩ := hodd
  have hk' : C.index = 2 * k + 1 := hk
  rcases (Nat.dvd_prime Nat.prime_two).1 h3 with hc | hc
  · rw [hc, one_mul] at h5
    omega
  · rw [hc] at h5
    have hak : D'.relIndex A' = C.index := by omega
    have hcop : Nat.Coprime (2 ^ 6) (D'.relIndex A') := by
      apply Nat.Coprime.pow_left
      apply (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      omega
    have h64 : 2 ^ 6 ∣ Nat.card D' * D'.relIndex A' := by rw [h4]; norm_num
    have h64' : 2 ^ 6 ∣ Nat.card D' := hcop.dvd_of_dvd_mul_right h64
    rw [hcardD'] at h64'
    have := Nat.dvd_trans h64' hdvd
    omega

end F8Form

end CFSG.Quasithin.SzN28
