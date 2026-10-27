module

public import CFSG.Quasithin.Background.G2SL2
public import CFSG.Quasithin.Background.G1Basic

public section

open Matrix CFSG.Quasithin.SL2Model
open scoped MatrixGroups

namespace CFSG.Quasithin.G1

variable {F : Type*} [Field F]

@[expose] def wmat (F : Type*) [Field F] [CharP F 2] : SL(2, F) :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    simp [CharTwo.neg_eq]⟩

section Wmat

variable [CharP F 2]

@[simp] theorem wmat_coe : (wmat F : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl

theorem wmat_smul (v : Fin 2 → F) : wmat F • v = ![v 1, v 0] := by
  rw [smul_eq_mulVec']
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem wmat_mul_self : wmat F * wmat F = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem wmat_inv : (wmat F)⁻¹ = wmat F := inv_eq_of_mul_eq_one_right wmat_mul_self

theorem wmat_lower_left : (wmat F).1 1 0 ≠ 0 := by simp

theorem e12_wmat_e12_wmat_e12 (a : Fˣ) :
    e12 (a : F) * wmat F * e12 ((a⁻¹ : Fˣ) : F) * wmat F * e12 (a : F) = dgm a * wmat F := by
  apply Subtype.ext
  have h3 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> exact h3

end Wmat

section Halves

variable [CharP F 2] {U : Type*} [AddCommGroup U] [DistribMulAction SL(2, F) U]

theorem wmat_smul_smul (u : U) : wmat F • wmat F • u = u := by
  rw [← mul_smul, wmat_mul_self, one_smul]

@[expose] def th (c : F) (u : U) : U := e12 c • wmat F • u - wmat F • u

theorem e12_wmat_smul (c : F) (u : U) : e12 c • wmat F • u = wmat F • u + th c u := by
  simp [th]

theorem th_zero_left (u : U) : th (0 : F) u = 0 := by
  simp [th, e12_zero]

theorem th_zero_right (c : F) : th c (0 : U) = 0 := by
  simp [th]

theorem th_add_right (c : F) (u v : U) : th c (u + v) = th c u + th c v := by
  simp only [th, smul_add]
  abel

variable (F) in
structure G13Pre (Y : AddSubgroup U) : Prop where
  stab : ∀ (d : Fˣ) (y : U), y ∈ Y → dgm d • y ∈ Y
  fix : ∀ (c : F) (y : U), y ∈ Y → e12 c • y = y
  comm : ∀ (c : F) (u : U), e12 c • u - u ∈ Y
  disj : ∀ z : U, z ∈ Y → wmat F • z ∈ Y → z = 0

variable (F) in
structure G13Halves (Y : AddSubgroup U) : Prop extends G13Pre F Y where
  sup : ∀ u : U, ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, u = y₁ + wmat F • y₂

namespace G13Pre

variable {Y : AddSubgroup U} (h : G13Pre F Y)

include h

theorem th_mem (c : F) (u : U) : th c u ∈ Y := h.comm c (wmat F • u)

theorem e12_th (c c' : F) (u : U) : e12 c' • th c u = th c u := h.fix c' _ (h.th_mem c u)

theorem th_add_left (c d : F) (u : U) : th (c + d) u = th c u + th d u := by
  have e : e12 (c + d) • wmat F • u = wmat F • u + (th c u + th d u) := by
    rw [e12_add, mul_smul, e12_wmat_smul d u, smul_add, e12_wmat_smul c u, h.e12_th d c u,
      add_assoc]
  have h2 := e12_wmat_smul (c + d) u
  rw [e] at h2
  exact (add_left_cancel h2).symm

theorem th_eq_dgm (hsq : ∀ u : U, u + u = 0) (a : Fˣ) {y : U} (hy : y ∈ Y) :
    th (a : F) y = dgm a • y := by
  set θ : U := th (a : F) y with hθ
  have hθY : θ ∈ Y := h.th_mem _ _
  set θ' : U := th ((a⁻¹ : Fˣ) : F) θ with hθ'
  have hθ'Y : θ' ∈ Y := h.th_mem _ _
  have hid := congrArg (fun g : SL(2, F) => g • (wmat F • y))
    (e12_wmat_e12_wmat_e12 (F := F) a)
  simp only [mul_smul, wmat_smul_smul] at hid
  have s1 : e12 (a : F) • wmat F • y = wmat F • y + θ := e12_wmat_smul _ _
  have s2 : wmat F • (e12 (a : F) • wmat F • y) = y + wmat F • θ := by
    rw [s1, smul_add, wmat_smul_smul]
  have s3 : e12 ((a⁻¹ : Fˣ) : F) • (y + wmat F • θ) = y + (wmat F • θ + θ') := by
    rw [smul_add, h.fix _ y hy, e12_wmat_smul _ θ]
  have s4 : wmat F • (y + (wmat F • θ + θ')) = wmat F • y + (θ + wmat F • θ') := by
    rw [smul_add, smul_add, wmat_smul_smul]
  have s5 : e12 (a : F) • (wmat F • y + (θ + wmat F • θ')) =
      wmat F • (y + θ') + th (a : F) θ' := by
    rw [smul_add, smul_add, e12_wmat_smul _ y, h.fix _ θ hθY, e12_wmat_smul _ θ', smul_add]
    calc wmat F • y + θ + (θ + (wmat F • θ' + th (a : F) θ'))
        = (wmat F • y + wmat F • θ' + th (a : F) θ') + (θ + θ) := by abel
      _ = wmat F • y + wmat F • θ' + th (a : F) θ' := by rw [hsq θ, add_zero]
  rw [s2, s3, s4, s5] at hid
  have hz : y + θ' ∈ Y := Y.add_mem hy hθ'Y
  have hw : wmat F • (y + θ') ∈ Y := by
    have : wmat F • (y + θ') = dgm a • y - th (a : F) θ' := eq_sub_of_add_eq hid
    rw [this]
    exact Y.sub_mem (h.stab a y hy) (h.th_mem _ _)
  have hz0 : y + θ' = 0 := h.disj _ hz hw
  have hθ'y : θ' = y := add_left_cancel (hz0.trans (hsq y).symm)
  rw [hz0, smul_zero, zero_add, hθ'y] at hid
  exact hid

theorem th_one (hsq : ∀ u : U, u + u = 0) {y : U} (hy : y ∈ Y) : th (1 : F) y = y := by
  have := h.th_eq_dgm hsq 1 hy
  rw [Units.val_one] at this
  rw [this, dgm_one, one_smul]

theorem th_mul (hsq : ∀ u : U, u + u = 0) (c d : F) {y : U} (hy : y ∈ Y) :
    th (c * d) y = th c (th d y) := by
  by_cases hc : c = 0
  · rw [hc, zero_mul, th_zero_left, th_zero_left]
  by_cases hd : d = 0
  · rw [hd, mul_zero, th_zero_left, th_zero_right]
  have hdy : th d y ∈ Y := h.th_mem d y
  have e1 := h.th_eq_dgm hsq (Units.mk0 c hc) hdy
  have e2 := h.th_eq_dgm hsq (Units.mk0 d hd) hy
  have e3 := h.th_eq_dgm hsq (Units.mk0 c hc * Units.mk0 d hd) hy
  rw [Units.val_mk0] at e1 e2
  rw [Units.val_mul, Units.val_mk0, Units.val_mk0] at e3
  rw [e3, e1, e2, ← mul_smul, dgm_mul]

@[expose] def thEnd (c : F) : AddMonoid.End ↥Y :=
  AddMonoidHom.mk' (fun y : ↥Y => (⟨th c (y : U), h.th_mem c y⟩ : ↥Y))
    (fun x y => Subtype.ext (th_add_right c (x : U) (y : U)))

@[expose] def thRing (hsq : ∀ u : U, u + u = 0) : F →+* AddMonoid.End ↥Y where
  toFun := h.thEnd
  map_one' := AddMonoidHom.ext fun y => Subtype.ext (h.th_one hsq y.2)
  map_mul' c d := AddMonoidHom.ext fun y => Subtype.ext (h.th_mul hsq c d y.2)
  map_zero' := AddMonoidHom.ext fun y => Subtype.ext (th_zero_left (y : U))
  map_add' c d := AddMonoidHom.ext fun y => Subtype.ext (h.th_add_left c d (y : U))

@[expose, instance_reducible] def module (hsq : ∀ u : U, u + u = 0) : Module F ↥Y :=
  Module.compHom ↥Y (h.thRing hsq)

end G13Pre

end Halves

section Equiv

variable [CharP F 2] {U : Type*} [AddCommGroup U] [DistribMulAction SL(2, F) U]
  {Y : AddSubgroup U} [Module F ↥Y]

@[expose] def phiMap {s : ℕ} (β : (Fin s → F) ≃ₗ[F] ↥Y) : (Fin s → Fin 2 → F) →+ U where
  toFun x := ((β (fun j => x j 0) : ↥Y) : U) + wmat F • ((β (fun j => x j 1) : ↥Y) : U)
  map_zero' := by
    show ((β (fun j => (0 : Fin s → Fin 2 → F) j 0) : ↥Y) : U) +
      wmat F • ((β (fun j => (0 : Fin s → Fin 2 → F) j 1) : ↥Y) : U) = 0
    rw [show (fun j => (0 : Fin s → Fin 2 → F) j 0) = 0 from rfl,
      show (fun j => (0 : Fin s → Fin 2 → F) j 1) = 0 from rfl, map_zero]
    simp
  map_add' x y := by
    simp only [Pi.add_apply]
    rw [show (fun j => x j 0 + y j 0) = (fun j => x j 0) + (fun j => y j 0) from rfl,
      show (fun j => x j 1 + y j 1) = (fun j => x j 1) + (fun j => y j 1) from rfl, map_add,
      map_add]
    simp only [AddSubgroup.coe_add, smul_add]
    abel

variable (h : G13Halves F Y)
  (hmod : ∀ (c : F) (y : ↥Y), ((c • y : ↥Y) : U) = th c (y : U))

include h hmod

theorem phiMap_e12 {s : ℕ} (β : (Fin s → F) ≃ₗ[F] ↥Y) (c : F) (x : Fin s → Fin 2 → F) :
    phiMap β (fun j => e12 c • x j) = e12 c • phiMap β x := by
  have h0 : (fun j => (e12 c • x j) 0) = (fun j => x j 0) + c • (fun j => x j 1) := by
    funext j
    simp [e12_smul]
  have h1 : (fun j => (e12 c • x j) 1) = (fun j => x j 1) := by
    funext j
    simp [e12_smul]
  show ((β (fun j => (e12 c • x j) 0) : ↥Y) : U) +
      wmat F • ((β (fun j => (e12 c • x j) 1) : ↥Y) : U)
    = e12 c • (((β (fun j => x j 0) : ↥Y) : U) + wmat F • ((β (fun j => x j 1) : ↥Y) : U))
  rw [h0, h1, map_add, map_smul, AddSubgroup.coe_add, hmod, smul_add, h.fix _ _ (β _).2,
    e12_wmat_smul]
  abel

omit h hmod in
theorem phiMap_wmat {s : ℕ} (β : (Fin s → F) ≃ₗ[F] ↥Y) (x : Fin s → Fin 2 → F) :
    phiMap β (fun j => wmat F • x j) = wmat F • phiMap β x := by
  have h0 : (fun j => (wmat F • x j) 0) = (fun j => x j 1) := by
    funext j
    simp [wmat_smul]
  have h1 : (fun j => (wmat F • x j) 1) = (fun j => x j 0) := by
    funext j
    simp [wmat_smul]
  show ((β (fun j => (wmat F • x j) 0) : ↥Y) : U) +
      wmat F • ((β (fun j => (wmat F • x j) 1) : ↥Y) : U)
    = wmat F • (((β (fun j => x j 0) : ↥Y) : U) + wmat F • ((β (fun j => x j 1) : ↥Y) : U))
  rw [h0, h1, smul_add, wmat_smul_smul]
  abel

theorem phiMap_equivariant {s : ℕ} (β : (Fin s → F) ≃ₗ[F] ↥Y) (k : SL(2, F))
    (x : Fin s → Fin 2 → F) : phiMap β (fun j => k • x j) = k • phiMap β x := by
  let S : Subgroup SL(2, F) :=
    { carrier := {k | ∀ x : Fin s → Fin 2 → F, phiMap β (fun j => k • x j) = k • phiMap β x}
      one_mem' := fun x => by simp
      mul_mem' := fun {k l} hk hl x => by
        have e : (fun j => (k * l) • x j) = fun j => k • (l • x j) := by
          funext j
          exact mul_smul k l (x j)
        rw [e, hk (fun j => l • x j), hl x, mul_smul]
      inv_mem' := fun {k} hk x => by
        have := hk (fun j => k⁻¹ • x j)
        have e : (fun j => k • k⁻¹ • x j) = x := by
          funext j
          exact smul_inv_smul k (x j)
        rw [e] at this
        rw [this, inv_smul_smul] }
  have hR : Rg F ≤ S := by
    intro t ht
    obtain ⟨b, rfl⟩ := mem_Rg.1 ht
    exact fun x => phiMap_e12 h hmod β b x
  have hw : wmat F ∈ S := fun x => phiMap_wmat β x
  have hconj : (Rg F).map (MulAut.conj (wmat F)⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨t, ht, rfl⟩
    exact S.mul_mem (S.mul_mem (S.inv_mem hw) (hR ht)) (by simpa using hw)
  have htop : Rg F ⊔ (Rg F).map (MulAut.conj (wmat F)⁻¹).toMonoidHom = ⊤ :=
    Rg_sup_conj_eq_top (wmat F) wmat_lower_left
  have hk : k ∈ S := by
    have : k ∈ Rg F ⊔ (Rg F).map (MulAut.conj (wmat F)⁻¹).toMonoidHom := by
      rw [htop]
      exact Subgroup.mem_top k
    exact sup_le hR hconj this
  exact hk x

omit hmod in
theorem phiMap_injective {s : ℕ} (β : (Fin s → F) ≃ₗ[F] ↥Y) :
    Function.Injective (phiMap β) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  change ((β (fun j => x j 0) : ↥Y) : U) + wmat F • ((β (fun j => x j 1) : ↥Y) : U) = 0 at hx
  have hz : ((β (fun j => x j 1) : ↥Y) : U) = 0 := by
    refine h.disj _ (β _).2 ?_
    have : wmat F • ((β (fun j => x j 1) : ↥Y) : U) = -((β (fun j => x j 0) : ↥Y) : U) :=
      eq_neg_of_add_eq_zero_right hx
    rw [this]
    exact Y.neg_mem (β _).2
  rw [hz, smul_zero, add_zero] at hx
  have h1 : (fun j => x j 1) = 0 := by
    apply β.injective
    rw [map_zero]
    exact Subtype.ext hz
  have h0 : (fun j => x j 0) = 0 := by
    apply β.injective
    rw [map_zero]
    exact Subtype.ext hx
  funext j i
  fin_cases i
  · exact congrFun h0 j
  · exact congrFun h1 j

omit hmod in
theorem phiMap_surjective {s : ℕ} (β : (Fin s → F) ≃ₗ[F] ↥Y) :
    Function.Surjective (phiMap β) := by
  intro u
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := h.sup u
  refine ⟨fun j => ![β.symm ⟨y₁, hy₁⟩ j, β.symm ⟨y₂, hy₂⟩ j], ?_⟩
  change ((β (fun j => ![β.symm ⟨y₁, hy₁⟩ j, β.symm ⟨y₂, hy₂⟩ j] 0) : ↥Y) : U) +
    wmat F • ((β (fun j => ![β.symm ⟨y₁, hy₁⟩ j, β.symm ⟨y₂, hy₂⟩ j] 1) : ↥Y) : U) = _
  simp

end Equiv

section Main

variable [CharP F 2] {U : Type*} [AddCommGroup U] [DistribMulAction SL(2, F) U]

theorem exists_equiv_of_halves_core [Finite U] (hsq : ∀ u : U, u + u = 0)
    {Y : AddSubgroup U} (h : G13Halves F Y) :
    ∃ (s : ℕ) (Θ : (Fin s → Fin 2 → F) ≃+ U),
      (∀ (k : SL(2, F)) (x : Fin s → Fin 2 → F), Θ (fun j => k • x j) = k • Θ x) ∧
      Nat.card ↥Y = Nat.card F ^ s ∧ ∀ u : U, (∀ t ∈ Rg F, t • u = u) → u ∈ Y := by
  let _ : Module F ↥Y := h.module hsq
  have hmod : ∀ (c : F) (y : ↥Y), ((c • y : ↥Y) : U) = th c (y : U) := fun c y => rfl
  have : Module.Finite F ↥Y := Module.Finite.of_finite
  let β : (Fin (Module.finrank F ↥Y) → F) ≃ₗ[F] ↥Y := (Module.finBasis F ↥Y).equivFun.symm
  refine ⟨Module.finrank F ↥Y,
    AddEquiv.ofBijective (phiMap β) ⟨phiMap_injective h β, phiMap_surjective h β⟩,
    fun k x => phiMap_equivariant h hmod β k x, ?_, ?_⟩
  · rw [← Nat.card_congr β.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _),
      Fintype.card_fin]
  · intro u hu
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := h.sup u
    have h1 := hu (e12 1) (e12_mem_Rg 1)
    rw [smul_add, h.fix _ _ hy₁, e12_wmat_smul] at h1
    have h2 : th (1 : F) y₂ = 0 := by simpa using add_left_cancel h1
    have h3 : y₂ = 0 := by rw [← h.th_one hsq hy₂]; exact h2
    rw [h3, smul_zero, add_zero]
    exact hy₁

end Main

end CFSG.Quasithin.G1
