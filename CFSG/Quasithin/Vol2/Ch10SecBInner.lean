module

public import CFSG.Quasithin.Background.B4L3Coord

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin Matrix

theorem exists_L3_of_injective (F : Multiplicative L3.Vec →* Multiplicative L3.Vec)
    (hF : Function.Injective F) :
    ∃ A : L3.Γ, ∀ v : L3.Vec,
      Multiplicative.toAdd (F (Multiplicative.ofAdd v)) = L3.act A v := by
  classical
  let f : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) := fun v =>
    Multiplicative.toAdd (F (Multiplicative.ofAdd v))
  have hadd : ∀ x y, f (x + y) = f x + f y := fun x y => by
    simp only [f]
    rw [show Multiplicative.ofAdd (x + y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y
      from rfl, map_mul]
    rfl
  let fl : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    { toFun := f
      map_add' := hadd
      map_smul' := fun c x => by
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        have h0 : f 0 = 0 := by
          have := hadd 0 0
          simp only [add_zero] at this
          exact left_eq_add.mp this
        rcases hc with rfl | rfl
        · simp [h0]
        · simp }
  let M : Matrix (Fin 3) (Fin 3) (ZMod 2) := LinearMap.toMatrix' fl
  have hMv : ∀ v, M *ᵥ v = f v := fun v => LinearMap.toMatrix'_mulVec fl v
  have hinj : Function.Injective M.mulVec := by
    intro v w hvw
    rw [hMv, hMv] at hvw
    exact Multiplicative.ofAdd.injective (hF (Multiplicative.toAdd.injective hvw))
  have hdet : M.det = 1 := by
    have hu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp
      (Matrix.mulVec_injective_iff_isUnit.mp hinj)
    have h0 : M.det ≠ 0 := hu.ne_zero
    generalize M.det = d at h0 ⊢
    revert d
    decide
  exact ⟨⟨M, hdet⟩, fun v => (hMv v).symm⟩

theorem eq_conj_of_act {A γ γ' : L3.Γ}
    (h : ∀ v, L3.act A (L3.act γ v) = L3.act γ' (L3.act A v)) : γ' = A * γ * A⁻¹ :=
  L3.act_ext fun v => by rw [L3.act_mul, L3.act_mul, h, L3.act_act_inv]

@[expose] def tr12 : L3.Γ := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

@[expose] def tr23 : L3.Γ := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩

@[expose] def tr31 : L3.Γ := ⟨!![1, 0, 0; 0, 1, 0; 1, 0, 1], by decide⟩

theorem eq_one_of_commute_gens : ∀ A : L3.Γ, A * tr12 = tr12 * A → A * tr23 = tr23 * A →
    A * tr31 = tr31 * A → A = 1 := by
  unfold tr12 tr23 tr31
  decide +kernel

section Data

variable {V : Type*} [CommGroup V] {Λ : Subgroup (MulAut V)} {U Z : Subgroup V}

@[expose] def restrictHom (c : MulAut V) (hcU : ∀ u ∈ U, c u ∈ U) : ↥U →* ↥U where
  toFun u := ⟨c (u : V), hcU (u : V) u.2⟩
  map_one' := Subtype.ext (map_one c)
  map_mul' u w := Subtype.ext (map_mul c (u : V) (w : V))

theorem exists_section_map (D : L3Data Λ U Z) {c : MulAut V} (hcU : ∀ u ∈ U, c u ∈ U)
    (hcZ : ∀ u ∈ U, (c u ∈ Z ↔ u ∈ Z)) :
    ∃ A : L3.Γ, ∀ u : ↥U, Multiplicative.toAdd (D.β (restrictHom c hcU u)) =
      L3.act A (Multiplicative.toAdd (D.β u)) := by
  let φ : ↥U →* Multiplicative L3.Vec := D.β.comp (restrictHom c hcU)
  have hker : D.β.ker ≤ φ.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    exact (D.ker_β _).mpr ((hcZ u u.2).mpr ((D.ker_β u).mp hu))
  let F := D.β.liftOfRightInverse (Function.surjInv D.β_surj)
    (Function.rightInverse_surjInv D.β_surj) ⟨φ, hker⟩
  have hF : ∀ u, F (D.β u) = D.β (restrictHom c hcU u) := fun u =>
    D.β.liftOfRightInverse_comp_apply _ _ ⟨φ, hker⟩ u
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro w hw
    obtain ⟨u, rfl⟩ := D.β_surj w
    rw [hF] at hw
    exact (D.ker_β u).mpr ((hcZ u u.2).mp ((D.ker_β _).mp hw))
  obtain ⟨A, hA⟩ := exists_L3_of_injective F hFinj
  refine ⟨A, fun u => ?_⟩
  rw [← hA, ofAdd_toAdd, hF]

theorem exists_conj_rho (D : L3Data Λ U Z) {c : MulAut V} (hcU : ∀ u ∈ U, c u ∈ U)
    (hcZ : ∀ u ∈ U, (c u ∈ Z ↔ u ∈ Z)) (hcΛ : ∀ g ∈ Λ, c * g * c⁻¹ ∈ Λ) :
    ∃ A : L3.Γ, ∀ γ : L3.Γ, c * D.rho γ * c⁻¹ = D.rho A * D.rho γ * (D.rho A)⁻¹ := by
  obtain ⟨A, hA⟩ := exists_section_map D hcU hcZ
  refine ⟨A, fun γ => ?_⟩
  obtain ⟨γ', hγ'⟩ := D.exists_rho (hcΛ _ (D.rho_mem γ))
  have hact : ∀ v, L3.act A (L3.act γ v) = L3.act γ' (L3.act A v) := by
    intro v
    obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd v)
    have hmem : D.rho γ (u : V) ∈ U := D.inv_U _ (D.rho_mem γ) _ u.2
    have h1 := D.β_rho γ (u : V) u.2 hmem
    have h2 : c (D.rho γ (u : V)) = D.rho γ' (c (u : V)) := by
      rw [hγ']
      simp [MulAut.mul_apply]
    have hmem' : D.rho γ' (c (u : V)) ∈ U := D.inv_U _ (D.rho_mem γ') _ (hcU _ u.2)
    have h3 := D.β_rho γ' (c (u : V)) (hcU _ u.2) hmem'
    have h4 := hA ⟨D.rho γ (u : V), hmem⟩
    have h5 := hA u
    simp only [restrictHom, MonoidHom.coe_mk, OneHom.coe_mk] at h4 h5
    rw [hu, toAdd_ofAdd] at h1 h5
    rw [h1, toAdd_ofAdd] at h4
    have h6 : (⟨c (D.rho γ (u : V)), hcU _ hmem⟩ : ↥U) = ⟨D.rho γ' (c (u : V)), hmem'⟩ :=
      Subtype.ext h2
    rw [h6, h3, toAdd_ofAdd, h5] at h4
    exact h4.symm
  rw [← hγ', eq_conj_of_act hact, map_mul, map_mul, map_inv]

theorem trivial_on_section_of_commute (D : L3Data Λ U Z) {c : MulAut V}
    (hcU : ∀ u ∈ U, c u ∈ U) (hcZ : ∀ u ∈ U, (c u ∈ Z ↔ u ∈ Z))
    (hcΛ : ∀ g ∈ Λ, c * g = g * c) : ∀ u ∈ U, c u * u⁻¹ ∈ Z := by
  obtain ⟨A, hA⟩ := exists_section_map D hcU hcZ
  have hcomm : ∀ γ : L3.Γ, A * γ = γ * A := by
    intro γ
    have hact : ∀ v, L3.act A (L3.act γ v) = L3.act γ (L3.act A v) := by
      intro v
      obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd v)
      have hmem : D.rho γ (u : V) ∈ U := D.inv_U _ (D.rho_mem γ) _ u.2
      have h1 := D.β_rho γ (u : V) u.2 hmem
      have h2 : c (D.rho γ (u : V)) = D.rho γ (c (u : V)) := by
        have := hcΛ _ (D.rho_mem γ)
        rw [← MulAut.mul_apply, this, MulAut.mul_apply]
      have hmem' : D.rho γ (c (u : V)) ∈ U := D.inv_U _ (D.rho_mem γ) _ (hcU _ u.2)
      have h3 := D.β_rho γ (c (u : V)) (hcU _ u.2) hmem'
      have h4 := hA ⟨D.rho γ (u : V), hmem⟩
      have h5 := hA u
      simp only [restrictHom, MonoidHom.coe_mk, OneHom.coe_mk] at h4 h5
      rw [hu, toAdd_ofAdd] at h1 h5
      rw [h1, toAdd_ofAdd] at h4
      have h6 : (⟨c (D.rho γ (u : V)), hcU _ hmem⟩ : ↥U) = ⟨D.rho γ (c (u : V)), hmem'⟩ :=
        Subtype.ext h2
      rw [h6, h3, toAdd_ofAdd, h5] at h4
      exact h4.symm
    have h := eq_conj_of_act hact
    calc A * γ = A * γ * A⁻¹ * A := by group
      _ = γ * A := by rw [← h]
  have hA1 : A = 1 := eq_one_of_commute_gens A (hcomm _) (hcomm _) (hcomm _)
  intro u hu
  have h := hA ⟨u, hu⟩
  rw [hA1, L3.act_one] at h
  have h' : D.β (restrictHom c hcU ⟨u, hu⟩) = D.β ⟨u, hu⟩ := Multiplicative.toAdd.injective h
  have hmem : c u * u⁻¹ ∈ U := U.mul_mem (hcU u hu) (U.inv_mem hu)
  have heq : (⟨c u * u⁻¹, hmem⟩ : ↥U) = restrictHom c hcU ⟨u, hu⟩ * (⟨u, hu⟩ : ↥U)⁻¹ := rfl
  have h1 : D.β ⟨c u * u⁻¹, hmem⟩ = 1 := by
    rw [heq, map_mul, map_inv, h']
    exact mul_inv_cancel _
  exact (D.ker_β _).mp h1

end Data

end CFSG.Quasithin.Vol2.Ch10.SecB
