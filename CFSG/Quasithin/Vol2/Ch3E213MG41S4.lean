module

public import CFSG.Quasithin.Vol2.Ch3E213MG41S3

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.Ch3E213M.G41.Refl

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OutcomeLocal (tv tv_apply tv_ne_one sumZero sumZeroRep
  sumZeroEquiv onesLine heartRep heartRep_apply_mk permCoord permCoord_apply permCoord_mul
  permCoord_swap coe_sumZeroEquiv mem_onesLine)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)

local notation "V₀" => Fin 4 → ZMod 2
local notation "GL₀" => LinearMap.GeneralLinearGroup (ZMod 2) (Fin 4 → ZMod 2)

variable {k : Type} [Field k] [CharP k 2] {G₀ : Subgroup (antiSp k)} {b : Fin 4 → Fin 4 → k}

theorem quad_of_preserved (Q : QuadraticForm (ZMod 2) V₀)
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q y x = 0) → x = 0) {u : V₀} (hu : u ≠ 0)
    (φ : Module.Dual (ZMod 2) V₀) (hφ : ∃ x, φ x = 1) (hpres : ∀ x, Q (x + φ x • u) = Q x) :
    Q u = 1 ∧ ∀ x, QuadraticMap.polar Q x u = φ x := by
  obtain ⟨x₁, hx₁⟩ := hφ
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h1 : ∀ x, φ x = 1 → QuadraticMap.polar Q x u = Q u := by
    intro x hx
    have hp := hpres x
    rw [hx, one_smul] at hp
    unfold QuadraticMap.polar
    rw [hp]
    linear_combination (-Q u) * h2
  have h0 : ∀ x, φ x = 0 → QuadraticMap.polar Q x u = Q u - Q u := by
    intro x hx
    have hx' : φ (x + x₁) = 1 := by rw [map_add, hx, hx₁, zero_add]
    have hsplit := QuadraticMap.polar_add_left Q x x₁ u
    rw [h1 _ hx', h1 _ hx₁] at hsplit
    linear_combination -hsplit
  have hQu : Q u = 1 := by
    rcases zmod2_cases (Q u) with h | h
    · refine absurd (hnd u fun y => ?_) hu
      rcases zmod2_cases (φ y) with hy | hy
      · rw [h0 y hy, sub_self]
      · rw [h1 y hy, h]
    · exact h
  refine ⟨hQu, fun x => ?_⟩
  rcases zmod2_cases (φ x) with hx | hx
  · rw [hx, h0 x hx, sub_self]
  · rw [hx, h1 x hx, hQu]

theorem polar_eq_f0 (hb : ∀ j, b j ∈ normC G₀) (hli : LinearIndependent k b)
    (Q : QuadraticForm (ZMod 2) V₀)
    (h : ∀ r ∈ normC G₀, ∀ x, QuadraticMap.polar Q x (pre b r) = f0 b (pre b r) x)
    (x y : V₀) : QuadraticMap.polar Q x y = f0 b x y := by
  have hpb : QuadraticMap.polarBilin Q = f0 b := by
    refine LinearMap.BilinForm.ext_basis (Pi.basisFun (ZMod 2) (Fin 4)) fun i j => ?_
    have hj : Pi.basisFun (ZMod 2) (Fin 4) j = pre b (b j) := by
      rw [Pi.basisFun_apply, ← emb_single (b := b) j, pre_emb hli]
    rw [QuadraticMap.polarBilin_apply_apply, hj, h _ (hb j), f0_symm]
  rw [← QuadraticMap.polarBilin_apply_apply, hpb]

theorem quad_of_tau (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀) (hli : LinearIndependent k b)
    (Q : QuadraticForm (ZMod 2) V₀) (hnd : ∀ x, (∀ y, QuadraticMap.polar Q y x = 0) → x = 0)
    (hpres : ∀ r ∈ normC G₀, ∀ x, Q (((tau b r : GL₀) : V₀ →ₗ[ZMod 2] V₀) x) = Q x) :
    (∀ x y, QuadraticMap.polar Q x y = f0 b x y) ∧ ∀ r ∈ normC G₀, Q (pre b r) = 1 := by
  have key : ∀ r ∈ normC G₀, Q (pre b r) = 1 ∧
      ∀ x, QuadraticMap.polar Q x (pre b r) = f0 b (pre b r) x := by
    intro r hr
    have hu := pre_ne_zero hF hb hli hr
    refine quad_of_preserved Q hnd hu (f0 b (pre b r)) ?_ fun x => ?_
    · by_contra hne
      push Not at hne
      exact hu (eq_zero_of_f0 hF hb hli fun y => (zmod2_cases _).resolve_right (hne y))
    · rw [← tau_apply]
      exact hpres r hr x
  exact ⟨polar_eq_f0 hb hli Q fun r hr => (key r hr).2, fun r hr => (key r hr).1⟩

theorem all_of_top [Finite k] (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀)
    (hli : LinearIndependent k b) (h : grp G₀ b = ⊤) (v : V₀) (hv : v ≠ 0) :
    emb b v ∈ normC G₀ := by
  have hφ : f0 b v ≠ 0 := fun h0 => hv (eq_zero_of_f0 hF hb hli fun y => LinearMap.congr_fun h0 y)
  have hmem : tv (f0 b v) v (f0_self v) ∈ grp G₀ b := by
    rw [h]
    exact Subgroup.mem_top _
  exact mem_normC_of_lift hF hb hli (grp_le_liftSub hF hb hli hmem) (tv_ne_one _ hφ hv) hv
    fun x => ⟨f0 b v x, by rw [tv_apply]⟩

theorem all_of_sp [Finite k] (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀)
    (hli : LinearIndependent k b) {f : LinearMap.BilinForm (ZMod 2) V₀} (hnd : f.Nondegenerate)
    (halt : f.IsAlt) (h : grp G₀ b = bilinIsometryGroup f) (v : V₀) (hv : v ≠ 0) :
    emb b v ∈ normC G₀ := by
  have hfv : f v v = 0 := halt v
  have hφ : f v ≠ 0 := fun h0 => hv (hnd.1 v fun y => LinearMap.congr_fun h0 y)
  have hmem : tv (f v) v hfv ∈ grp G₀ b := by
    rw [h]
    intro x y
    have hskew : f x v = f v x := by
      rw [← LinearMap.IsAlt.neg halt v x, CharTwo.neg_eq]
    simp only [tv_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hfv, mul_zero, add_zero, hskew]
    have h2 : (2 : ZMod 2) = 0 := by decide
    linear_combination (f v x * f v y) * h2
  exact mem_normC_of_lift hF hb hli (grp_le_liftSub hF hb hli hmem) (tv_ne_one _ hφ hv) hv
    fun x => ⟨f v x, by rw [tv_apply]⟩

theorem quad_of_orth (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀) (hli : LinearIndependent k b)
    {Q : QuadraticForm (ZMod 2) V₀} (hnd : LinearMap.Nondegenerate (QuadraticMap.polarBilin Q))
    (h : grp G₀ b = (TauCeti.QuadraticMap.orthogonalGroup Q).comap
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V₀).toMonoidHom) :
    (∀ x y, QuadraticMap.polar Q x y = f0 b x y) ∧ ∀ r ∈ normC G₀, Q (pre b r) = 1 := by
  refine quad_of_tau hF hb hli Q (fun x hx => hnd.2 x fun y => ?_) fun r hr x => ?_
  · rw [QuadraticMap.polarBilin_apply_apply]
    exact hx y
  · have hmem := tau_mem_grp (b := b) hr
    rw [h] at hmem
    exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (Subgroup.mem_comap.mp hmem)) x

@[expose] def e2 (x : Fin 5 → ZMod 2) : ZMod 2 :=
  x 0 * x 1 + x 0 * x 2 + x 0 * x 3 + x 0 * x 4 + x 1 * x 2 + x 1 * x 3 + x 1 * x 4 +
    x 2 * x 3 + x 2 * x 4 + x 3 * x 4

@[expose] def q5 : QuadraticForm (ZMod 2) (Fin 5 → ZMod 2) :=
  (Matrix.toBilin' (Matrix.of fun i j : Fin 5 => if i < j then (1 : ZMod 2) else 0)).toQuadraticMap

theorem q5_apply (x : Fin 5 → ZMod 2) : q5 x = e2 x := by
  simp only [q5, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply, Matrix.of_apply,
    Fin.sum_univ_five, e2]
  simp
  ring

theorem e2_swap : ∀ (i j : Fin 5) (x : Fin 5 → ZMod 2),
    e2 (fun l => x (Equiv.swap i j l)) = e2 x := by
  decide

theorem e2_nondeg : ∀ x : Fin 5 → ZMod 2, x 0 + x 1 + x 2 + x 3 + x 4 = 0 →
    (∀ y : Fin 5 → ZMod 2, y 0 + y 1 + y 2 + y 3 + y 4 = 0 → e2 (x + y) - e2 x - e2 y = 0) →
    x = 0 := by
  decide

theorem q5_perm (σ : Equiv.Perm (Fin 5)) : ∀ x, q5 (permCoord σ x) = q5 x := by
  refine Equiv.Perm.swap_induction_on σ (fun x => rfl) fun f i j _ ih x => ?_
  rw [permCoord_mul, q5_apply, q5_apply]
  have he : permCoord (Equiv.swap i j) (permCoord f x) =
      fun l => permCoord f x (Equiv.swap i j l) :=
    funext fun l => by rw [permCoord_apply, Equiv.swap_inv]
  rw [he, e2_swap, ← q5_apply, ih, q5_apply]

theorem mem_sum5 {x : Fin 5 → ZMod 2} : x ∈ sumZero 5 ↔ x 0 + x 1 + x 2 + x 3 + x 4 = 0 := by
  change ∑ i, x i = 0 ↔ _
  rw [Fin.sum_univ_five]

theorem quad_of_sym5 (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀) (hli : LinearIndependent k b)
    {β : V₀ ≃ₗ[ZMod 2] sumZero 5}
    (hβ : (grp G₀ b).map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
      (sumZeroRep 5).range) :
    ∃ Q : QuadraticForm (ZMod 2) V₀,
      (∀ x y, QuadraticMap.polar Q x y = f0 b x y) ∧ ∀ r ∈ normC G₀, Q (pre b r) = 1 := by
  let Q : QuadraticForm (ZMod 2) V₀ := q5.comp ((sumZero 5).subtype ∘ₗ β.toLinearMap)
  have hQ : ∀ x, Q x = e2 (β x : Fin 5 → ZMod 2) := fun x => q5_apply _
  refine ⟨Q, quad_of_tau hF hb hli Q (fun x hx => ?_) fun r hr x => ?_⟩
  · apply β.injective
    rw [map_zero]
    refine Subtype.ext (?_ : (β x : Fin 5 → ZMod 2) = 0)
    refine e2_nondeg _ (mem_sum5.mp (β x).2) fun y hy => ?_
    have h := hx (β.symm ⟨y, mem_sum5.mpr hy⟩)
    unfold QuadraticMap.polar at h
    rw [hQ, hQ, hQ, map_add, LinearEquiv.apply_symm_apply, Submodule.coe_add,
      Submodule.coe_mk] at h
    rw [add_comm]
    linear_combination h
  · have hmem : LinearMap.GeneralLinearGroup.congrLinearEquiv β (tau b r) ∈
        (sumZeroRep 5).range := by
      rw [← hβ]
      exact ⟨_, tau_mem_grp hr, rfl⟩
    obtain ⟨σ, hσ⟩ := hmem
    have hact : β (((tau b r : GL₀) : V₀ →ₗ[ZMod 2] V₀) x) = sumZeroEquiv σ (β x) := by
      have h := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 5) =>
        (g : sumZero 5 →ₗ[ZMod 2] sumZero 5) (β x)) hσ
      change sumZeroEquiv σ (β x) =
        β (((tau b r : GL₀) : V₀ →ₗ[ZMod 2] V₀) (β.symm (β x))) at h
      rw [h, LinearEquiv.symm_apply_apply]
    rw [hQ, hQ, hact, coe_sumZeroEquiv, ← q5_apply, ← q5_apply, q5_perm]

end CFSG.Quasithin.Ch3E213M.G41.Refl
