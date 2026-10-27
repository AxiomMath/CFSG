module

public import CFSG.Quasithin.Vol2.Ch3E213MSp4G41

public section

namespace CFSG.Quasithin.Ch3E213M.G41

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ClassicalGroups.Alternating (symplecticTransvection symplecticTransvection_apply)

variable {k : Type} [Field k]

theorem act_add (g : antiSp k) (u v : Fin 4 → k) : natAct g (u + v) = natAct g u + natAct g v :=
  Matrix.mulVec_add _ _ _

theorem act_smul (g : antiSp k) (r : k) (v : Fin 4 → k) : natAct g (r • v) = r • natAct g v :=
  Matrix.mulVec_smul _ _ _

theorem act_zero (g : antiSp k) : natAct g 0 = 0 :=
  Matrix.mulVec_zero _

theorem act_act_inv (g : antiSp k) (x : Fin 4 → k) : natAct g (natAct g⁻¹ x) = x := by
  rw [← natAct_mul, mul_inv_cancel, natAct_one]

theorem act_inv_act (g : antiSp k) (x : Fin 4 → k) : natAct g⁻¹ (natAct g x) = x := by
  rw [← natAct_mul, inv_mul_cancel, natAct_one]

theorem act_injective (g : antiSp k) : Function.Injective (natAct g) := fun x y h => by
  rw [← act_inv_act g x, h, act_inv_act]

theorem natLin_apply' (g : antiSp k) (x : Fin 4 → k) : natLin g x = natAct g x :=
  Matrix.toLin'_apply _ _

theorem act_single_apply (g : antiSp k) (i j : Fin 4) :
    natAct g (Pi.single j 1) i = glMat (g : GL (Fin 4) k) i j := by
  simp [natAct]

theorem ext_act {g h : antiSp k} (H : ∀ x, natAct g x = natAct h x) : g = h := by
  apply antiSp_ext
  ext i j
  rw [← act_single_apply, ← act_single_apply, H]

theorem bil_apply (x y : Fin 4 → k) :
    spBil x y = x 0 * y 3 + x 1 * y 2 + x 2 * y 1 + x 3 * y 0 :=
  minorForm_apply x y

theorem bil_symm (x y : Fin 4 → k) : spBil x y = spBil y x := by
  rw [bil_apply, bil_apply]
  ring

theorem bil_act (g : antiSp k) (x y : Fin 4 → k) :
    spBil (natAct g x) (natAct g y) = spBil x y := by
  have hJ : (glMat (g : GL (Fin 4) k)).transpose * minorJ k * glMat (g : GL (Fin 4) k) =
      minorJ k := mem_antiSp.mp g.2
  simp only [spBil, natAct, Matrix.toBilin'_apply']
  rw [← Matrix.vecMul_transpose _ x, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hJ]

theorem bil_act_inv (g : antiSp k) (x y : Fin 4 → k) :
    spBil (natAct g⁻¹ x) y = spBil x (natAct g y) := by
  rw [← bil_act g, act_act_inv]

theorem exists_bil_ne_zero {v : Fin 4 → k} (hv : v ≠ 0) : ∃ x, spBil x v ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hv
  have h0 := h (Pi.single 3 1)
  have h1 := h (Pi.single 2 1)
  have h2 := h (Pi.single 1 1)
  have h3 := h (Pi.single 0 1)
  simp [bil_apply] at h0 h1 h2 h3
  funext i
  fin_cases i <;> simp_all

theorem eq_zero_of_bil_eq_zero {v : Fin 4 → k} (h : ∀ x, spBil x v = 0) : v = 0 := by
  by_contra hv
  obtain ⟨x, hx⟩ := exists_bil_ne_zero hv
  exact hx (h x)

theorem toLin'_sub_one_apply (g : antiSp k) (x : Fin 4 → k) :
    Matrix.toLin' (glMat (g : GL (Fin 4) k) - 1) x = natAct g x - x := by
  rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  rfl

section CharTwo

variable [CharP k 2]

theorem bil_self (x : Fin 4 → k) : spBil x x = 0 :=
  minorForm_isAlt x

theorem bil_add_smul_self (x v : Fin 4 → k) (r : k) : spBil (x + r • v) v = spBil x v := by
  rw [LinearMap.map_add₂, LinearMap.map_smul₂, bil_self, smul_zero, add_zero]

@[expose] def trv (v : Fin 4 → k) (c : k) : antiSp k :=
  ⟨Matrix.GeneralLinearGroup.toLin.symm
      (symplecticTransvection (minorForm k) minorForm_isAlt v c), by
    rw [antiSp_eq_closure]
    exact Subgroup.subset_closure ⟨v, c, rfl⟩⟩

theorem act_trv (v : Fin 4 → k) (c : k) (x : Fin 4 → k) :
    natAct (trv v c) x = x + (c * spBil x v) • v := by
  have h1 : Matrix.GeneralLinearGroup.toLin ((trv v c : antiSp k) : GL (Fin 4) k) =
      symplecticTransvection (minorForm k) minorForm_isAlt v c :=
    MulEquiv.apply_symm_apply _ _
  have h2 := congrArg (fun f : LinearMap.GeneralLinearGroup k (Fin 4 → k) =>
    (f : (Fin 4 → k) →ₗ[k] (Fin 4 → k)) x) h1
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply,
    symplecticTransvection_apply] at h2
  exact h2

theorem glMat_trv (v : Fin 4 → k) (c : k) :
    glMat ((trv v c : antiSp k) : GL (Fin 4) k) = transvMat v c :=
  glMat_transvection v c

theorem act_trv_of_bil_eq_zero {v x : Fin 4 → k} (c : k) (hx : spBil x v = 0) :
    natAct (trv v c) x = x := by
  rw [act_trv, hx, mul_zero, zero_smul, add_zero]

theorem trv_add (v : Fin 4 → k) (c d : k) : trv v (c + d) = trv v c * trv v d := by
  apply ext_act
  intro x
  rw [natAct_mul, act_trv, act_trv, act_trv, bil_add_smul_self, add_mul, add_smul]
  abel

theorem trv_zero (v : Fin 4 → k) : trv v 0 = 1 := by
  apply ext_act
  intro x
  rw [act_trv, zero_mul, zero_smul, add_zero, natAct_one]

theorem trv_zero_left (c : k) : trv (0 : Fin 4 → k) c = 1 := by
  apply ext_act
  intro x
  rw [act_trv, smul_zero, add_zero, natAct_one]

theorem trv_mul_self (v : Fin 4 → k) (c : k) : trv v c * trv v c = 1 := by
  rw [← trv_add, CharTwo.add_self_eq_zero, trv_zero]

theorem trv_inv (v : Fin 4 → k) (c : k) : (trv v c)⁻¹ = trv v c :=
  inv_eq_of_mul_eq_one_right (trv_mul_self v c)

theorem trv_smul (v : Fin 4 → k) (μ c : k) : trv (μ • v) c = trv v (μ ^ 2 * c) := by
  apply ext_act
  intro x
  rw [act_trv, act_trv, LinearMap.map_smul, smul_eq_mul, smul_smul]
  congr 2
  ring

theorem conj_trv (g : antiSp k) (v : Fin 4 → k) (c : k) :
    g * trv v c * g⁻¹ = trv (natAct g v) c := by
  apply ext_act
  intro x
  rw [natAct_mul, natAct_mul, act_trv, act_add, act_smul, act_act_inv, act_trv, bil_act_inv]

theorem trv_param_inj {v : Fin 4 → k} (hv : v ≠ 0) {c d : k} (h : trv v c = trv v d) : c = d := by
  obtain ⟨x, hx⟩ := exists_bil_ne_zero hv
  have h1 := congrArg (fun g => natAct g x) h
  simp only [act_trv, add_right_inj] at h1
  exact mul_right_cancel₀ hx (smul_left_injective k hv h1)

theorem trv_eq_trv {v w : Fin 4 → k} {c d : k} (hv : v ≠ 0) (hc : c ≠ 0)
    (h : trv w d = trv v c) : ∃ μ : k, μ ≠ 0 ∧ w = μ • v ∧ μ ^ 2 * d = c := by
  obtain ⟨x, hx⟩ := exists_bil_ne_zero hv
  have h1 := congrArg (fun g => natAct g x) h
  simp only [act_trv, add_right_inj] at h1
  have hne : (c * spBil x v) • v ≠ 0 := smul_ne_zero (mul_ne_zero hc hx) hv
  have hd : d * spBil x w ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h1
    exact hne h1.symm
  set μ := (c * spBil x v) / (d * spBil x w) with hμ
  have hμ0 : μ ≠ 0 := div_ne_zero (mul_ne_zero hc hx) hd
  have hw : w = μ • v := by
    rw [hμ, div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hd, one_smul]
  refine ⟨μ, hμ0, hw, ?_⟩
  rw [hw, trv_smul] at h
  exact trv_param_inj hv h

theorem commSpace_trv {v : Fin 4 → k} (hv : v ≠ 0) {c : k} (hc : c ≠ 0) :
    commSpace (trv v c) = Submodule.span k {v} := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [toLin'_sub_one_apply, act_trv, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    obtain ⟨x, hx⟩ := exists_bil_ne_zero hv
    refine LinearMap.mem_range.mpr ⟨(c * spBil x v)⁻¹ • x, ?_⟩
    rw [toLin'_sub_one_apply, act_trv, add_sub_cancel_left, LinearMap.map_smul₂, smul_eq_mul,
      show c * ((c * spBil x v)⁻¹ * spBil x v) = 1 by field_simp, one_smul]

theorem isTransvection_trv {v : Fin 4 → k} (hv : v ≠ 0) {c : k} (hc : c ≠ 0) :
    IsTransvection (trv v c) := by
  refine ⟨fun h1 => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := exists_bil_ne_zero hv
    have h2 := congrArg (fun g => natAct g x) h1
    simp only [act_trv, natAct_one, add_eq_left] at h2
    exact smul_ne_zero (mul_ne_zero hc hx) hv h2
  · rw [commSpace_trv hv hc, finrank_span_singleton hv]

theorem exists_eq_trv {g : antiSp k} (hg : IsTransvection g) :
    ∃ v c, v ≠ 0 ∧ c ≠ 0 ∧ g = trv v c := by
  obtain ⟨hg1, hrank⟩ := hg
  obtain ⟨⟨w, hwmem⟩, hw0, hspan⟩ := finrank_eq_one_iff'.mp hrank
  have hw : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hφ : ∀ x, ∃ a : k, natAct g x = x + a • w := by
    intro x
    obtain ⟨a, ha⟩ := hspan ⟨_, LinearMap.mem_range_self _ x⟩
    refine ⟨a, ?_⟩
    have h1 : a • w = Matrix.toLin' (glMat (g : GL (Fin 4) k) - 1) x := congrArg Subtype.val ha
    rw [toLin'_sub_one_apply] at h1
    rw [h1, add_sub_cancel]
  choose φ hφ using hφ
  have key : ∀ x y, φ y * spBil x w = φ x * spBil y w := by
    intro x y
    have h := bil_act g x y
    rw [hφ x, hφ y] at h
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, bil_self, mul_zero,
      add_zero] at h
    rw [bil_symm w y] at h
    linear_combination h - (φ x * spBil y w) * (CharTwo.two_eq_zero : (2 : k) = 0)
  obtain ⟨x₀, hx₀⟩ := exists_bil_ne_zero hw
  set c := φ x₀ / spBil x₀ w with hcdef
  have hφc : ∀ y, φ y = c * spBil y w := by
    intro y
    rw [hcdef, div_mul_eq_mul_div, eq_div_iff hx₀]
    exact key x₀ y
  have hg : g = trv w c := by
    apply ext_act
    intro y
    rw [hφ y, act_trv, hφc y]
  refine ⟨w, c, hw, fun hc0 => hg1 ?_, hg⟩
  rw [hg, hc0, trv_zero]

theorem isTransvection_conj {d : antiSp k} (hd : IsTransvection d) (g : antiSp k) :
    IsTransvection (g * d * g⁻¹) := by
  obtain ⟨v, c, hv, hc, rfl⟩ := exists_eq_trv hd
  rw [conj_trv]
  exact isTransvection_trv (fun h => hv (act_injective g (by rw [h, act_zero]))) hc

theorem trace_trv_mul_trv (v w : Fin 4 → k) (a b : k) :
    Matrix.trace (glMat ((trv v a * trv w b : antiSp k) : GL (Fin 4) k)) =
      a * b * spBil v w ^ 2 := by
  have h : glMat ((trv v a * trv w b : antiSp k) : GL (Fin 4) k) =
      transvMat v a * transvMat w b := by
    rw [← glMat_trv, ← glMat_trv]
    rfl
  rw [h, bil_apply]
  simp [Matrix.trace, Fin.sum_univ_four, transvMat]
  linear_combination (2 + b * (w 0 * w 3 + w 1 * w 2) + a * (v 0 * v 3 + v 1 * v 2)) *
    (CharTwo.two_eq_zero : (2 : k) = 0)

@[expose] def Lam (G₀ : Subgroup (antiSp k)) (v : Fin 4 → k) : AddSubgroup k where
  carrier := {c | trv v c ∈ G₀}
  zero_mem' := by
    change trv v 0 ∈ G₀
    rw [trv_zero]
    exact G₀.one_mem
  add_mem' {c d} hc hd := by
    change trv v (c + d) ∈ G₀
    rw [trv_add]
    exact G₀.mul_mem hc hd
  neg_mem' {c} hc := by
    change trv v (-c) ∈ G₀
    rw [CharTwo.neg_eq]
    exact hc

variable {G₀ : Subgroup (antiSp k)}

theorem mem_Lam {v : Fin 4 → k} {c : k} : c ∈ Lam G₀ v ↔ trv v c ∈ G₀ :=
  Iff.rfl

theorem mem_Lam_smul {v : Fin 4 → k} {μ c : k} : c ∈ Lam G₀ (μ • v) ↔ μ ^ 2 * c ∈ Lam G₀ v := by
  rw [mem_Lam, mem_Lam, trv_smul]

theorem mem_Lam_act {g : antiSp k} (hg : g ∈ G₀) {v : Fin 4 → k} {c : k} :
    c ∈ Lam G₀ (natAct g v) ↔ c ∈ Lam G₀ v := by
  rw [mem_Lam, mem_Lam, ← conj_trv]
  constructor
  · intro h
    have := G₀.mul_mem (G₀.mul_mem (G₀.inv_mem hg) h) hg
    simpa [mul_assoc] using this
  · intro h
    exact G₀.mul_mem (G₀.mul_mem hg h) (G₀.inv_mem hg)

theorem trv_mem_transvSet {v : Fin 4 → k} (hv : v ≠ 0) {c : k} (hc : c ≠ 0)
    (hcL : c ∈ Lam G₀ v) : trv v c ∈ transvSet G₀ :=
  ⟨hcL, isTransvection_trv hv hc⟩

theorem exists_of_mem_transvSet {d : antiSp k} (hd : d ∈ transvSet G₀) :
    ∃ v c, v ≠ 0 ∧ c ≠ 0 ∧ c ∈ Lam G₀ v ∧ d = trv v c := by
  obtain ⟨v, c, hv, hc, rfl⟩ := exists_eq_trv hd.2
  exact ⟨v, c, hv, hc, hd.1, rfl⟩

theorem conj_mem_transvSet {d : antiSp k} (hd : d ∈ transvSet G₀) {g : antiSp k} (hg : g ∈ G₀) :
    g * d * g⁻¹ ∈ transvSet G₀ :=
  ⟨G₀.mul_mem (G₀.mul_mem hg hd.1) (G₀.inv_mem hg), isTransvection_conj hd.2 g⟩

end CharTwo

end CFSG.Quasithin.Ch3E213M.G41
