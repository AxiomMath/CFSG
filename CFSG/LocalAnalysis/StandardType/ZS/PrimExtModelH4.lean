module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelH4Data
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelH3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.PrimModel

@[expose] def h4bMatFun {K : Type} [Field K] (α : K) : Fin 5 → Matrix (Fin 4) (Fin 4) K :=
  ![Matrix.blockSucc (diagSignMat 0), Matrix.blockSucc (diagSignMat 1),
    Matrix.blockSucc (diagSignMat 2), Matrix.blockSucc (h3BlockMat α), h4BlockMat α]

theorem range_h4bMatFun {K : Type} [Field K] (α : K) :
    Set.range (h4bMatFun α) = h4BlockMats α := by
  ext M
  simp [h4bMatFun, h4BlockMats, h3Mats, h3BlockMats]
  tauto

@[expose] def h45MatFun {K : Type} [Field K] (α : K) : Fin 5 → Matrix (Fin 5) (Fin 5) K :=
  fun k => Matrix.blockSucc (h4bMatFun α k)

theorem range_h45MatFun {K : Type} [Field K] (α : K) : Set.range (h45MatFun α) = h4Mats α := by
  rw [show h45MatFun α = Matrix.blockSucc ∘ h4bMatFun α from rfl, Set.range_comp,
    range_h4bMatFun]
  rfl

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem blockSucc_apply {R : Type} [Semiring R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (i j : Fin (n + 1)) :
    Matrix.blockSucc M i j =
      if hi : i = Fin.last n then (if j = Fin.last n then (1 : R) else 0)
      else if hj : j = Fin.last n then 0
      else M (Fin.castPred i hi) (Fin.castPred j hj) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [Matrix.blockSucc_last_last]; simp
    | cast j => rw [Matrix.blockSucc_last_castSucc]; simp
  | cast i =>
    induction j using Fin.lastCases with
    | last => rw [Matrix.blockSucc_castSucc_last]; simp
    | cast j => rw [Matrix.blockSucc_castSucc_castSucc]; simp

private theorem castPred_four_two (h : (2 : Fin 4) ≠ Fin.last 3) :
    Fin.castPred (2 : Fin 4) h = (2 : Fin 3) := rfl

theorem evMat_h4bG (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) (k : Fin 5) :
    evMat (evalAl hα) 1 (h4bG k) = h4bMatFun α k := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  fin_cases k <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [h4bMatFun, h4bG, evMat, h4BlockMat, h3BlockMat, diagSignMat, evalAl_qa,
      blockSucc_apply, castPred_four_two] <;> (try field_simp [h2]) <;> (try ring_nf) <;> simp

private def blockSuccTwo {R : Type} [Semiring R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of (Fin.snoc (fun i => Fin.snoc (M i) 0) (Fin.snoc 0 2))

private theorem blockSuccTwo_apply {R : Type} [Semiring R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (i j : Fin (n + 1)) :
    blockSuccTwo M i j =
      if hi : i = Fin.last n then (if j = Fin.last n then (2 : R) else 0)
      else if hj : j = Fin.last n then 0
      else M (Fin.castPred i hi) (Fin.castPred j hj) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [blockSuccTwo]
    | cast j => simp [blockSuccTwo]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [blockSuccTwo]
    | cast j => simp [blockSuccTwo]

private theorem evMat_blockSuccTwo {R : Type} [CommRing R] (hp : p ≠ 2)
    (φ : R →+* ZMod p) {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    evMat φ 1 (blockSuccTwo M) = Matrix.blockSucc (evMat φ 1 M) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  ext i j
  simp only [evMat, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [blockSuccTwo_apply, blockSucc_apply]
  by_cases hi : i = Fin.last n <;> by_cases hj : j = Fin.last n <;>
    simp [hi, hj, h2, map_ofNat]

theorem evMat_h45G (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) (k : Fin 5) :
    evMat (evalAl hα) 1 (h45G k) = h45MatFun α k := by
  have hG : h45G k = blockSuccTwo (h4bG k) := by
    fin_cases k <;> decide +kernel
  rw [hG, evMat_blockSuccTwo hp (evalAl hα), evMat_h4bG hp hα k]
  rfl

theorem h4b_basisClosure_eq (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) : basisClosure f (h4BlockMats α) = h4bTab.group (evalAl hα) f := by
  rw [← range_h4bMatFun α]
  exact ReflTable.basisClosure_eq_group h4bTab_valid hp
    (fun k => by rw [h4bTab_gen k]; exact evMat_h4bG hp hα k)

theorem h45_basisClosure_eq (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) : basisClosure f (h4Mats α) = h45Tab.group (evalAl hα) f := by
  rw [← range_h45MatFun α]
  exact ReflTable.basisClosure_eq_group h45Tab_valid hp
    (fun k => by rw [h45Tab_gen k]; exact evMat_h45G hp hα k)

theorem h4b_transvectionFree (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) : QTwoLin.TransvectionFree (h4bTab.group (evalAl hα) f) := by
  exact ReflTable.transvectionFree_group h4bTab_valid (fun x hx => evalAl_ne_zero hp hα hx) hp
    h4bD h4bD_good h4bTab_form

theorem h45_transvectionFree (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) : QTwoLin.TransvectionFree (h45Tab.group (evalAl hα) f) := by
  exact ReflTable.transvectionFree_group h45Tab_valid (fun x hx => evalAl_ne_zero hp hα hx) hp
    h45D h45D_good h45Tab_form

theorem h4b_toMatrix_diag (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) (i : Fin 4) :
    LinearMap.toMatrix f f (h4bTab.refl (evalAl hα) f
        ((![0, 21, 18, 59] : Fin 4 → Fin 60) i) : U →ₗ[ZMod p] U) = diagSignMat i := by
  fin_cases i
  · rw [ReflTable.toMatrix_refl h4bTab_valid hp]
    simp
    rw [h4bTab_diag.1, evMat_diagZ hp]
  · rw [ReflTable.toMatrix_refl h4bTab_valid hp]
    simp
    rw [h4bTab_diag.2.1, evMat_diagZ hp]
  · rw [ReflTable.toMatrix_refl h4bTab_valid hp]
    simp
    rw [h4bTab_diag.2.2.1, evMat_diagZ hp]
  · rw [ReflTable.toMatrix_refl h4bTab_valid hp]
    simp
    rw [h4bTab_diag.2.2.2, evMat_diagZ hp]

theorem h45_toMatrix_diag (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) (i : Fin 4) :
    LinearMap.toMatrix f f (h45Tab.refl (evalAl hα) f
        ((![0, 21, 18, 59] : Fin 4 → Fin 60) i) : U →ₗ[ZMod p] U) =
      diagSignMat i.castSucc := by
  fin_cases i
  · rw [ReflTable.toMatrix_refl h45Tab_valid hp]
    simp
    rw [h45Tab_diag.1, evMat_diagZ hp]
  · rw [ReflTable.toMatrix_refl h45Tab_valid hp]
    simp
    rw [h45Tab_diag.2.1, evMat_diagZ hp]
  · rw [ReflTable.toMatrix_refl h45Tab_valid hp]
    simp
    rw [h45Tab_diag.2.2.1, evMat_diagZ hp]
  · rw [ReflTable.toMatrix_refl h45Tab_valid hp]
    simp
    rw [h45Tab_diag.2.2.2, evMat_diagZ hp]

theorem oneClass_basisClosure_h4BlockMats (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) : OneClass p (basisClosure f (h4BlockMats α)) := by
  rw [h4b_basisClosure_eq hp f hα]
  refine oneClass_of_forall_conj (a₀ := h4bTab.refl (evalAl hα) f 0) ?_
  intro x hx hxr
  obtain ⟨j, rfl⟩ := ReflTable.exists_eq_refl h4bTab_valid hp (h4b_transvectionFree hp f hα) hx hxr
  exact ReflTable.exists_conj_of_cls_eq h4bTab_valid hp (j := 0) (j' := j)
    (by fin_cases j <;> rfl)

private theorem h4b_refl_apply_diag (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) (i j : Fin 4) :
    h4bTab.refl (evalAl hα) f ((![0, 21, 18, 59] : Fin 4 → Fin 60) i) (f j) =
      (if j = i then (-1 : ZMod p) else 1) • f j := by
  have hmat : LinearMap.toMatrix f f (h4bTab.refl (evalAl hα) f
      ((![0, 21, 18, 59] : Fin 4 → Fin 60) i) : U →ₗ[ZMod p] U) =
      Matrix.diagonal (fun j => if j = i then (-1 : ZMod p) else 1) := by
    rw [h4b_toMatrix_diag hp f hα i]
    rfl
  exact apply_basis_of_toMatrix_eq_diagonal
    (d := fun j => if j = i then (-1 : ZMod p) else 1) f hmat j

theorem irredOnSection_basisClosure_h4BlockMats (hp : p ≠ 2)
    (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    IrredOnSection (basisClosure f (h4BlockMats α)) ⊥ ⊤ := by
  rw [h4b_basisClosure_eq hp f hα]
  rw [show (⊤ : Submodule (ZMod p) U) =
      Submodule.span (ZMod p) (f '' ↑(Finset.univ : Finset (Fin 4))) from by
    rw [Finset.coe_univ, Set.image_univ, f.span_eq]]
  refine irredOnSection_span_of_hub (t := h4bTab.refl (evalAl hα) f 15)
    (r := h4bTab.vecU (evalAl hα) f 15) (c := h4bTab.covecU (evalAl hα) f 15)
    hp f (Finset.univ : Finset (Fin 4)) ?_ ?_ ?_ ?_ ?_
  · intro i _
    refine ⟨h4bTab.refl (evalAl hα) f ((![0, 21, 18, 59] : Fin 4 → Fin 60) i),
      ReflTable.refl_mem_group h4bTab_valid hp _, ?_, ?_⟩
    · rw [h4b_refl_apply_diag hp f hα i i]; simp
    · intro j hj; rw [h4b_refl_apply_diag hp f hα i j]; simp [hj]
  · exact ReflTable.refl_mem_group h4bTab_valid hp 15
  · intro v; exact ReflTable.refl_apply h4bTab_valid hp 15 v
  · intro i _
    rw [show h4bTab.vecU (evalAl hα) f 15 = vecR (evalAl hα) f (h4bTab.root 15) from rfl,
      coord_vecR]
    exact evalAl_ne_zero hp hα (h4b_hub i).1
  · intro i _
    rw [show h4bTab.covecU (evalAl hα) f 15 = covecR (evalAl hα) f (h4bTab.coroot 15)
        from rfl, covecR_basis]
    exact mul_ne_zero (inv_ne_zero (ZMod.prime_ne_zero p 2 hp))
      (evalAl_ne_zero hp hα (h4b_hub i).2)

private theorem toMatrix_mul_three {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (a b c : U ≃ₗ[ZMod p] U) :
    LinearMap.toMatrix f f (↑(a * b * c) : U →ₗ[ZMod p] U) =
      LinearMap.toMatrix f f (↑a) * LinearMap.toMatrix f f (↑b) *
        LinearMap.toMatrix f f (↑c) := by
  rw [show (↑(a * b * c) : U →ₗ[ZMod p] U) = (↑a : U →ₗ[ZMod p] U) * (↑b) * (↑c) from by
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]]
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul]

private theorem coe_toLinearMap_pow (a : U ≃ₗ[ZMod p] U) (k : ℕ) :
    (↑(a ^ k) : U →ₗ[ZMod p] U) = (↑a : U →ₗ[ZMod p] U) ^ k :=
  map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom) a k

theorem h45_primFrameData (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) {h₁ z τ : U ≃ₗ[ZMod p] U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    (hz : LinearMap.toMatrix f f (z : U →ₗ[ZMod p] U) =
      diagSignMat 0 * diagSignMat 1 * diagSignMat 2)
    (hτ : LinearMap.toMatrix f f (τ : U →ₗ[ZMod p] U) = diagSignMat 3) :
    PrimFrameData p (basisClosure f (h4Mats α)) h₁ z τ := by
  have hh₁' : h₁ = h45Tab.refl (evalAl hα) f 0 := by
    refine eq_of_toMatrix_eq f ?_
    rw [hh₁]
    simpa using (h45_toMatrix_diag hp f hα 0).symm
  have hz' : z = h45Tab.refl (evalAl hα) f ((![0, 21, 18, 59] : Fin 4 → Fin 60) 0) *
      h45Tab.refl (evalAl hα) f ((![0, 21, 18, 59] : Fin 4 → Fin 60) 1) *
      h45Tab.refl (evalAl hα) f ((![0, 21, 18, 59] : Fin 4 → Fin 60) 2) := by
    refine eq_of_toMatrix_eq f ?_
    rw [hz, toMatrix_mul_three, h45_toMatrix_diag hp f hα 0, h45_toMatrix_diag hp f hα 1,
      h45_toMatrix_diag hp f hα 2]
    rfl
  have hτ' : τ = h45Tab.refl (evalAl hα) f ((![0, 21, 18, 59] : Fin 4 → Fin 60) 3) := by
    refine eq_of_toMatrix_eq f ?_
    rw [hτ]
    simpa using (h45_toMatrix_diag hp f hα 3).symm
  have hzG : z ∈ h45Tab.group (evalAl hα) f := by
    rw [hz']
    exact mul_mem (mul_mem (ReflTable.refl_mem_group h45Tab_valid hp _)
      (ReflTable.refl_mem_group h45Tab_valid hp _)) (ReflTable.refl_mem_group h45Tab_valid hp _)
  have hh₁G : h₁ ∈ h45Tab.group (evalAl hα) f := by
    rw [hh₁']; exact ReflTable.refl_mem_group h45Tab_valid hp 0
  have hτG : ∃ g ∈ h45Tab.group (evalAl hα) f, τ = g * h₁ * g⁻¹ := by
    rw [hτ', hh₁']
    exact ReflTable.exists_conj_of_cls_eq h45Tab_valid hp (j := 0)
      (j' := ((![0, 21, 18, 59] : Fin 4 → Fin 60) 3)) (by decide)
  have hfix := ReflTable.exists_conj_le_inf_ker h45Tab_valid
    (fun x hx => evalAl_ne_zero hp hα hx) hp (h45_transvectionFree hp f hα)
    ({0, 1, 2} : Finset (Fin 5)) 0 h45Wit h45Tab_wit
  rw [h45_basisClosure_eq hp f hα]
  refine primFrameData_of_diagonal hp f ({0, 1, 2} : Finset (Fin 5)) (i₁ := 0) (iτ := 3)
    (by decide) (by decide) (by decide) ?_ hh₁ hτ hzG hh₁G hτG ?_
  · rw [hz, diagSignMat_mul_diagSignMat_mul_diagSignMat (by decide) (by decide) (by decide)]
  · intro x hx hxr hmov
    simpa only [hh₁'] using hfix x hx hxr hmov

theorem fixReflSubgroup_h4b_eq (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) :
    fixReflSubgroup p (basisClosure f (h4BlockMats α)) (f 0) =
      basisClosure (f.reindex h4Perm) (h3Mats α) := by
  rw [fixReflSubgroup, h4b_basisClosure_eq hp f hα,
    ReflTable.setOf_isRefl_apply_basis h4bTab_valid (fun x hx => evalAl_ne_zero hp hα hx) hp
      (h4b_transvectionFree hp f hα) 0]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [h3_basisClosure_eq hp (f.reindex h4Perm) hα]
    change h4bTab.refl (evalAl hα) f j ∈ h3Tab.group (evalAl hα) (f.reindex h4Perm)
    rw [ReflTable.refl_eq_refl_reindex h4bTab_valid h3Tab_valid hp h4Perm
        (h4b_mu j hj).1 (h4b_mu j hj).2]
    exact ReflTable.refl_mem_group h3Tab_valid hp (h4bMu j)
  · rw [h3_basisClosure_eq hp (f.reindex h4Perm) hα, ReflTable.group, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    refine Subgroup.subset_closure ⟨h4bNu (h3Tab.gen k), (h4b_nu (h3Tab.gen k)).1, ?_⟩
    change h4bTab.refl (evalAl hα) f (h4bNu (h3Tab.gen k)) =
      h3Tab.refl (evalAl hα) (f.reindex h4Perm) (h3Tab.gen k)
    rw [ReflTable.refl_eq_refl_reindex h4bTab_valid h3Tab_valid hp h4Perm
        (h4b_mu (h4bNu (h3Tab.gen k)) (h4b_nu (h3Tab.gen k)).1).1
        (h4b_mu (h4bNu (h3Tab.gen k)) (h4b_nu (h3Tab.gen k)).1).2,
      (h4b_nu (h3Tab.gen k)).2]

theorem reflSubgroupIn_h45_eq (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) :
    reflSubgroupIn p (basisClosure f (h4Mats α)) (LinearMap.ker (f.coord 0)) =
      Subgroup.closure
        ((fun j => h45Tab.refl (evalAl hα) f j) '' {j | h45Tab.root j 0 = 0}) := by
  rw [reflSubgroupIn, h45_basisClosure_eq hp f hα,
    ReflTable.setOf_isRefl_sub_mem_ker_coord h45Tab_valid (fun x hx => evalAl_ne_zero hp hα hx) hp
      (h45_transvectionFree hp f hα) 0]

private theorem h45_basis_mem_commutator (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) (t : Fin 3) :
    f (t.succ.castSucc) ∈ Submodule.span (ZMod p)
      ((fun j => h45Tab.vecU (evalAl hα) f j) '' {j | h45Tab.root j 0 = 0}) := by
  have hmem : f (t.succ.castSucc) ∈ Submodule.span (ZMod p) (Set.range fun l : Fin 1 =>
      vecR (evalAl hα) f ((fun _ => h45Tab.root (h45UnitIdx t)) l)) := by
    refine mem_span_of_sum_smul_eq (s := 1) hp (evalAl hα) f
      (fun _ : Fin 1 => h45UnitCoef t) t.succ.castSucc ?_
    simpa [Fin.sum_univ_one] using (h45_unit t).2
  refine Submodule.span_mono ?_ hmem
  rintro _ ⟨l, rfl⟩
  exact ⟨h45UnitIdx t, (h45_unit t).1, rfl⟩

theorem commutatorSpace_reflSubgroupIn_h45 (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) :
    HardMathSupport.Kantor79.commutatorSpace
        (reflSubgroupIn p (basisClosure f (h4Mats α)) (LinearMap.ker (f.coord 0))) =
      Submodule.span (ZMod p) (f '' ↑({1, 2, 3} : Finset (Fin 5))) := by
  rw [reflSubgroupIn_h45_eq hp f hα,
    ReflTable.commutatorSpace_closure_image_refl h45Tab_valid hp]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    change vecR (evalAl hα) f (h45Tab.root j) ∈
      Submodule.span (ZMod p) (f '' ↑({1, 2, 3} : Finset (Fin 5)))
    refine (vecR_mem_span_image_iff (fun x hx => evalAl_ne_zero hp hα hx) f
      ({1, 2, 3} : Finset (Fin 5)) (h45Tab_valid.root_good j)).2 ?_
    intro i hi
    fin_cases i <;> simp_all [h45_last]
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    fin_cases i <;> simp at hi
    · exact h45_basis_mem_commutator hp f hα 0
    · exact h45_basis_mem_commutator hp f hα 1
    · exact h45_basis_mem_commutator hp f hα 2

private theorem h45_refl_apply_diag (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) (i : Fin 4) (j : Fin 5) :
    h45Tab.refl (evalAl hα) f ((![0, 21, 18, 59] : Fin 4 → Fin 60) i) (f j) =
      (if j = i.castSucc then (-1 : ZMod p) else 1) • f j := by
  have hmat : LinearMap.toMatrix f f (h45Tab.refl (evalAl hα) f
      ((![0, 21, 18, 59] : Fin 4 → Fin 60) i) : U →ₗ[ZMod p] U) =
      Matrix.diagonal (fun j => if j = i.castSucc then -1 else 1) := by
    rw [h45_toMatrix_diag hp f hα i]
    rfl
  exact apply_basis_of_toMatrix_eq_diagonal (d := fun j => if j = i.castSucc then -1 else 1)
    f hmat j

private theorem evMat_neg {R : Type} [CommRing R] (φ : R →+* ZMod p) (k : ℕ)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : evMat φ k (-M) = -evMat φ k M := by
  ext i j
  simp [evMat, map_neg]

private theorem h45_signChange_mem (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) (i : Fin 5)
    (hi : i ∈ ({1, 2, 3} : Finset (Fin 5))) :
    ∃ d ∈ Subgroup.closure
        ((fun j => h45Tab.refl (evalAl hα) f j) '' {j | h45Tab.root j 0 = 0}),
      d (f i) = -f i ∧ ∀ j, j ≠ i → d (f j) = f j := by
  fin_cases i <;> simp at hi
  · refine ⟨h45Tab.refl (evalAl hα) f (h45UnitIdx 0),
      Subgroup.subset_closure ⟨h45UnitIdx 0, (h45_unit 0).1, rfl⟩, ?_, ?_⟩
    · rw [show h45UnitIdx 0 = ((![0, 21, 18, 59] : Fin 4 → Fin 60) 1) from by decide]
      show (h45Tab.refl (evalAl hα) f ((![0, 21, 18, 59] : Fin 4 → Fin 60) 1)) (f 1) = -f 1
      simpa using (h45_refl_apply_diag hp f hα 1 1)
    · intro j hj
      rw [show h45UnitIdx 0 = ((![0, 21, 18, 59] : Fin 4 → Fin 60) 1) from by decide]
      rw [h45_refl_apply_diag hp f hα 1 j]
      split_ifs with h
      · exact absurd h hj
      · rw [one_smul]
  · refine ⟨h45Tab.refl (evalAl hα) f (h45UnitIdx 1),
      Subgroup.subset_closure ⟨h45UnitIdx 1, (h45_unit 1).1, rfl⟩, ?_, ?_⟩
    · rw [show h45UnitIdx 1 = ((![0, 21, 18, 59] : Fin 4 → Fin 60) 2) from by decide]
      show (h45Tab.refl (evalAl hα) f ((![0, 21, 18, 59] : Fin 4 → Fin 60) 2)) (f 2) = -f 2
      simpa using (h45_refl_apply_diag hp f hα 2 2)
    · intro j hj
      rw [show h45UnitIdx 1 = ((![0, 21, 18, 59] : Fin 4 → Fin 60) 2) from by decide]
      rw [h45_refl_apply_diag hp f hα 2 j]
      split_ifs with h
      · exact absurd h hj
      · rw [one_smul]
  · refine ⟨h45Tab.refl (evalAl hα) f (h45UnitIdx 2),
      Subgroup.subset_closure ⟨h45UnitIdx 2, (h45_unit 2).1, rfl⟩, ?_, ?_⟩
    · rw [show h45UnitIdx 2 = ((![0, 21, 18, 59] : Fin 4 → Fin 60) 3) from by decide]
      show (h45Tab.refl (evalAl hα) f ((![0, 21, 18, 59] : Fin 4 → Fin 60) 3)) (f 3) = -f 3
      simpa using (h45_refl_apply_diag hp f hα 3 3)
    · intro j hj
      rw [show h45UnitIdx 2 = ((![0, 21, 18, 59] : Fin 4 → Fin 60) 3) from by decide]
      rw [h45_refl_apply_diag hp f hα 3 j]
      split_ifs with h
      · exact absurd h hj
      · rw [one_smul]

theorem irredOnSection_reflSubgroupIn_h45 (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) :
    IrredOnSection (reflSubgroupIn p (basisClosure f (h4Mats α)) (LinearMap.ker (f.coord 0))) ⊥
      (Submodule.span (ZMod p) (f '' ↑({1, 2, 3} : Finset (Fin 5)))) := by
  rw [reflSubgroupIn_h45_eq hp f hα]
  refine irredOnSection_span_of_hub (t := h45Tab.refl (evalAl hα) f 30)
    (r := h45Tab.vecU (evalAl hα) f 30) (c := h45Tab.covecU (evalAl hα) f 30)
    hp f ({1, 2, 3} : Finset (Fin 5)) ?_ ?_ ?_ ?_ ?_
  · exact h45_signChange_mem hp f hα
  · exact Subgroup.subset_closure ⟨30, h45_hub.1, rfl⟩
  · intro v; exact ReflTable.refl_apply h45Tab_valid hp 30 v
  · intro i hi
    rw [show h45Tab.vecU (evalAl hα) f 30 = vecR (evalAl hα) f (h45Tab.root 30) from rfl,
      coord_vecR]
    fin_cases i <;> simp at hi
    · exact evalAl_ne_zero hp hα (h45_hub.2 0).1
    · exact evalAl_ne_zero hp hα (h45_hub.2 1).1
    · exact evalAl_ne_zero hp hα (h45_hub.2 2).1
  · intro i hi
    rw [show h45Tab.covecU (evalAl hα) f 30 = covecR (evalAl hα) f (h45Tab.coroot 30)
        from rfl, covecR_basis]
    fin_cases i <;> simp at hi
    · exact mul_ne_zero (inv_ne_zero (ZMod.prime_ne_zero p 2 hp))
        (evalAl_ne_zero hp hα (h45_hub.2 0).2)
    · exact mul_ne_zero (inv_ne_zero (ZMod.prime_ne_zero p 2 hp))
        (evalAl_ne_zero hp hα (h45_hub.2 1).2)
    · exact mul_ne_zero (inv_ne_zero (ZMod.prime_ne_zero p 2 hp))
        (evalAl_ne_zero hp hα (h45_hub.2 2).2)

private theorem h4b_neg_toMatrix (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) :
    LinearMap.toMatrix f f (↑(h4bTab.refl (evalAl hα) f (h4bTab.gen 0) *
      (h4bTab.refl (evalAl hα) f (h4bTab.gen 1) * h4bTab.refl (evalAl hα) f (h4bTab.gen 2) *
        h4bTab.refl (evalAl hα) f (h4bTab.gen 4)) ^ 5) : U →ₗ[ZMod p] U) = -1 := by
  have h0 : LinearMap.toMatrix f f (↑(h4bTab.refl (evalAl hα) f (h4bTab.gen 0)) :
      U →ₗ[ZMod p] U) = evMat (evalAl hα) 1 (h4bG 0) := by
    rw [ReflTable.toMatrix_refl h4bTab_valid hp, h4bTab_gen 0]
  have h1 : LinearMap.toMatrix f f (↑(h4bTab.refl (evalAl hα) f (h4bTab.gen 1)) :
      U →ₗ[ZMod p] U) = evMat (evalAl hα) 1 (h4bG 1) := by
    rw [ReflTable.toMatrix_refl h4bTab_valid hp, h4bTab_gen 1]
  have h2 : LinearMap.toMatrix f f (↑(h4bTab.refl (evalAl hα) f (h4bTab.gen 2)) :
      U →ₗ[ZMod p] U) = evMat (evalAl hα) 1 (h4bG 2) := by
    rw [ReflTable.toMatrix_refl h4bTab_valid hp, h4bTab_gen 2]
  have h4 : LinearMap.toMatrix f f (↑(h4bTab.refl (evalAl hα) f (h4bTab.gen 4)) :
      U →ₗ[ZMod p] U) = evMat (evalAl hα) 1 (h4bG 4) := by
    rw [ReflTable.toMatrix_refl h4bTab_valid hp, h4bTab_gen 4]
  have hprod : LinearMap.toMatrix f f (↑(h4bTab.refl (evalAl hα) f (h4bTab.gen 1) *
      h4bTab.refl (evalAl hα) f (h4bTab.gen 2) * h4bTab.refl (evalAl hα) f (h4bTab.gen 4)) :
      U →ₗ[ZMod p] U) = evMat (evalAl hα) 3 (h4bG 1 * h4bG 2 * h4bG 4) := by
    rw [toMatrix_mul_three, h1, h2, h4, ← evMat_mul, ← evMat_mul]
  rw [show (↑(h4bTab.refl (evalAl hα) f (h4bTab.gen 0) *
      (h4bTab.refl (evalAl hα) f (h4bTab.gen 1) * h4bTab.refl (evalAl hα) f (h4bTab.gen 2) *
        h4bTab.refl (evalAl hα) f (h4bTab.gen 4)) ^ 5) : U →ₗ[ZMod p] U) =
      (↑(h4bTab.refl (evalAl hα) f (h4bTab.gen 0)) : U →ₗ[ZMod p] U) *
        (↑(h4bTab.refl (evalAl hα) f (h4bTab.gen 1) * h4bTab.refl (evalAl hα) f (h4bTab.gen 2) *
          h4bTab.refl (evalAl hα) f (h4bTab.gen 4)) : U →ₗ[ZMod p] U) ^ 5 from by
    rw [LinearEquiv.coe_toLinearMap_mul, coe_toLinearMap_pow]]
  rw [LinearMap.toMatrix_mul, ← LinearMap.toMatrix_pow, h0, hprod, ← evMat_pow, ← evMat_mul,
    h4b_neg]
  rw [show (2 : ZAl) ^ 16 • (-1 : Matrix (Fin 4) (Fin 4) ZAl) =
      -((2 : ZAl) ^ 16 • (1 : Matrix (Fin 4) (Fin 4) ZAl)) from by
    rw [show (-1 : Matrix (Fin 4) (Fin 4) ZAl) = -(1 : Matrix (Fin 4) (Fin 4) ZAl) by simp,
      smul_neg]]
  rw [evMat_neg, evMat_two_pow_smul_one hp (evalAl hα) 16]

theorem neg_mem_basisClosure_h4BlockMats (hp : p ≠ 2) (_hp5 : p ≠ 5)
    (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ basisClosure f (h4BlockMats α) := by
  let g : Fin 5 → U ≃ₗ[ZMod p] U := fun k => h4bTab.refl (evalAl hα) f (h4bTab.gen k)
  have hg : ∀ k, g k ∈ h4bTab.group (evalAl hα) f :=
    fun k => ReflTable.refl_mem_group h4bTab_valid hp (h4bTab.gen k)
  have hmem : g 0 * (g 1 * g 2 * g 4) ^ 5 ∈ h4bTab.group (evalAl hα) f :=
    mul_mem (hg 0) (pow_mem (mul_mem (mul_mem (hg 1) (hg 2)) (hg 4)) 5)
  have heq : h4bTab.refl (evalAl hα) f (h4bTab.gen 0) *
      (h4bTab.refl (evalAl hα) f (h4bTab.gen 1) * h4bTab.refl (evalAl hα) f (h4bTab.gen 2) *
        h4bTab.refl (evalAl hα) f (h4bTab.gen 4)) ^ 5 =
      (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) :=
    eq_neg_of_toMatrix_eq_neg_one f (h4b_neg_toMatrix hp f hα)
  rw [h4b_basisClosure_eq hp f hα, ← heq]
  exact hmem

private def h4Pt (i : Fin 120) : Fin 4 → ZAl :=
  if (i : ℕ) < 60 then h4bTab.root ⟨i % 60, Nat.mod_lt _ (by decide)⟩
  else -h4bTab.root ⟨i % 60, Nat.mod_lt _ (by decide)⟩

private def h4Pi (k : Fin 5) (i : Fin 120) : Fin 120 :=
  let j : Fin 60 := ⟨i % 60, Nat.mod_lt _ (by decide)⟩
  ⟨((h4bTab.conj k j : ℕ) + if decide ((i : ℕ) < 60) = h4bTab.sign k j then 0 else 60) % 120,
    Nat.mod_lt _ (by decide)⟩

private def h4BfsL : List (Fin 120) :=
  [0, 60, 1, 61, 2, 3, 4, 62, 63, 64, 5, 6, 7, 8, 65, 66, 67, 68, 9, 10, 11, 12, 13, 14, 15, 16, 17,
    69, 70, 71, 72, 73, 74, 75, 76, 77, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 78, 79, 80,
    81, 82, 83, 84, 85, 86, 87, 88, 89, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 98, 95, 94, 41,
    42, 90, 91, 92, 93, 96, 97, 99, 100, 101, 102, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 107, 53,
    110, 111, 105, 54, 103, 104, 106, 108, 109, 112, 113, 114, 55, 56, 116, 57, 115, 117, 58, 118,
    59, 119]

private def h4PredL : List (Fin 120) :=
  [0, 0, 0, 1, 2, 2, 2, 3, 3, 3, 4, 5, 5, 6, 7, 8, 8, 9, 10, 10, 10, 11, 11, 11, 11, 12, 13, 14, 14,
    14, 15, 15, 15, 15, 16, 17, 19, 19, 20, 21, 21, 22, 23, 24, 24, 25, 26, 26, 28, 28, 29, 30, 30,
    31, 32, 33, 33, 34, 35, 35, 36, 37, 38, 39, 40, 40, 41, 42, 43, 43, 45, 46, 46, 46, 46, 47, 48,
    49, 50, 51, 53, 54, 55, 57, 58, 59, 60, 60, 61, 62, 62, 63, 63, 68, 68, 69, 69, 70, 71, 71, 72,
    74, 76, 76, 78, 79, 79, 82, 83, 84, 86, 93, 98, 101, 102, 109, 111, 112, 116, 117]

private def h4PkL : List (Fin 5) :=
  [0, 0, 3, 3, 0, 1, 2, 0, 1, 2, 3, 3, 4, 4, 3, 3, 4, 4, 0, 1, 2, 0, 1, 2, 4, 1, 1, 0, 1, 2, 0, 1,
    2, 4, 1, 1, 3, 4, 4, 3, 4, 4, 4, 1, 2, 4, 3, 4, 3, 4, 4, 3, 4, 4, 4, 1, 2, 4, 3, 4, 4, 1, 1, 4,
    1, 2, 2, 2, 2, 3, 2, 0, 1, 2, 4, 2, 4, 1, 1, 4, 2, 2, 3, 2, 4, 2, 1, 2, 4, 3, 4, 1, 2, 3, 4, 0,
    2, 3, 3, 4, 3, 1, 1, 2, 3, 1, 2, 0, 3, 1, 4, 4, 4, 3, 4, 3, 1, 1, 4, 4]

private def h4Bfs (i : Fin 120) : Fin 120 := h4BfsL.getD i 0

private def h4Pred (i : Fin 120) : Fin 120 := h4PredL.getD i 0

private def h4Pk (i : Fin 120) : Fin 5 := h4PkL.getD i 0

private def h4Ch : Fin 4 → Fin 60 := ![0, 1, 43, 19]

private def h4ChPt : Fin 4 → Fin 120 := ![0, 1, 43, 19]

private def h4Lev (j : Fin 60) (i : Fin 120) : ZAl := dotProduct (h4bTab.coroot j) (h4Pt i)

private def h4LevL : List ZAl :=
  [qa (-4) 0, qa (-2) 0, qa (-2) 2, qa 0 (-2), qa 0 0, qa 0 2, qa 2 (-2), qa 2 0, qa 4 0]

private def h4Sig (i : Fin 120) : ℕ :=
  ∑ m : Fin 4, 9 ^ (m : ℕ) * h4LevL.idxOf (h4Lev (h4Ch m) i)

private def GoodAl235 (x : ZAl) : Prop := QuadraticAlgebra.norm x ∣ 2 ^ 32 * 3 ^ 2 * 5

private instance (x : ZAl) : Decidable (GoodAl235 x) :=
  inferInstanceAs (Decidable (QuadraticAlgebra.norm x ∣ (2 ^ 32 * 3 ^ 2 * 5 : ℤ)))

private def h4L2 : List (Fin 120) := [1, 3, 4, 7, 8, 16, 17, 27, 29, 40, 42, 62]

private def h4L3 : List (Fin 120) := [43, 44, 55, 58, 59, 103, 104, 115, 118, 119]

private def h4SpanL : List (List ZAl) := [
    [qa 1 0, qa 0 0, qa 0 0, qa 0 0],
    [qa (-1) (-1), qa 1 1, qa 0 1, qa 0 (-1)],
    [qa 1 0, qa 1 (-1), qa 0 (-1), qa 0 1],
    [qa (-2) 0, qa 0 1, qa 1 0, qa 1 (-2)]]

private def h4Span (i m : Fin 4) : ZAl := (h4SpanL.getD i []).getD m 0

private theorem h4_pt_act : ∀ (k : Fin 5) (i : Fin 120),
    (2 : ZAl) • h4Pt i - dotProduct (h4bTab.coroot (h4bTab.gen k)) (h4Pt i) •
      h4bTab.root (h4bTab.gen k) = (2 : ZAl) • h4Pt (h4Pi k i) := by
  decide +kernel

private theorem h4_pred : ∀ i : Fin 120,
    i = 0 ∨ (h4Pred i < i ∧ h4Pi (h4Pk i) (h4Bfs (h4Pred i)) = h4Bfs i) := by
  decide +kernel

private theorem h4_bfs_zero : h4Bfs 0 = 0 := by
  decide +kernel

private theorem h4_bfs_idx : ∀ j : Fin 120,
    h4Bfs ⟨h4BfsL.idxOf j % 120, Nat.mod_lt _ (by decide)⟩ = j := by
  decide +kernel

private theorem h4_ch_root : ∀ m, h4Pt (h4ChPt m) = h4bTab.root (h4Ch m) := by
  decide +kernel

private theorem h4_lev_mem : ∀ m i, h4Lev (h4Ch m) i ∈ h4LevL := by
  decide +kernel

private theorem h4_lev_sep : ∀ u ∈ h4LevL, ∀ v ∈ h4LevL, u = v ∨ GoodAl235 (u - v) := by
  decide +kernel

private theorem h4_sig : CFSG.Decide.bitsetNodup (List.ofFn h4Sig) = true := by
  decide +kernel

private theorem h4_L2 : ∀ i, h4Lev (h4Ch 0) i = h4Lev (h4Ch 0) (h4ChPt 1) → i ∈ h4L2 := by
  decide +kernel

private theorem h4_L3 : ∀ i, h4Lev (h4Ch 0) i = h4Lev (h4Ch 0) (h4ChPt 2) →
    h4Lev (h4Ch 1) i = h4Lev (h4Ch 1) (h4ChPt 2) → i ∈ h4L3 := by
  decide +kernel

private theorem h4_L4 : ∀ i, h4Lev (h4Ch 0) i = h4Lev (h4Ch 0) (h4ChPt 3) →
    h4Lev (h4Ch 1) i = h4Lev (h4Ch 1) (h4ChPt 3) →
    h4Lev (h4Ch 2) i = h4Lev (h4Ch 2) (h4ChPt 3) → i = h4ChPt 3 := by
  decide +kernel

private theorem h4_span : ∀ i : Fin 4,
    ∑ m, h4Span i m • h4Pt (h4ChPt m) = (2 : ZAl) ^ 1 • Pi.single i 1 := by
  decide +kernel

private theorem evalAl_ne_zero_of_goodAl235 (hp : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    {α : ZMod p} (hα : α ^ 2 = α + 1) {x : ZAl} (hx : GoodAl235 x) : evalAl hα x ≠ 0 := by
  intro h
  have hpp : p.Prime := Fact.out
  have h1 := congrArg (evalAl hα) (QuadraticAlgebra.algebraMap_norm_eq_mul_star x)
  rw [map_mul, h, zero_mul] at h1
  have h2 : evalAl hα ((QuadraticAlgebra.norm x : ℤ) : ZAl) = 0 := h1
  rw [map_intCast] at h2
  have h3 : (p : ℤ) ∣ 2 ^ 32 * 3 ^ 2 * 5 :=
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h2).trans hx
  have h4 : p ∣ 2 ^ 32 * 3 ^ 2 * 5 := by exact_mod_cast h3
  rcases (Nat.Prime.dvd_mul hpp).mp h4 with h5 | h5
  · rcases (Nat.Prime.dvd_mul hpp).mp h5 with h6 | h6
    · exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h6))
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp (hpp.dvd_of_dvd_pow h6))
  · exact hp5 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_five).mp h5)

private theorem zmod_three_sq_ne : ∀ a : ZMod 3, a ^ 2 ≠ a + 1 := by
  decide

private theorem ne_three_of_sq_eq {α : ZMod p} (hα : α ^ 2 = α + 1) : p ≠ 3 := by
  rintro rfl
  exact zmod_three_sq_ne α hα

private theorem covecU_apply_of_apply_eq {R : Type} [CommRing R] {n m N : ℕ}
    {T : ReflTable R n m N} {good : R → Prop} (hv : T.Valid good) (hp : p ≠ 2)
    {φ : R →+* ZMod p} {f : Module.Basis (Fin n) (ZMod p) U}
    (htv : QTwoLin.TransvectionFree (T.group φ f)) {g : U ≃ₗ[ZMod p] U} (hg : g ∈ T.group φ f)
    {j : Fin N} (hfix : g (T.vecU φ f j) = T.vecU φ f j) (v : U) :
    T.covecU φ f j (g v) = T.covecU φ f j v := by
  have hc := ReflTable.covecU_vecU (φ := φ) (f := f) hv hp j
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hr : T.vecU φ f j ≠ 0 := fun h0 => h2 (by rw [← hc, h0, map_zero])
  have hgr : g.symm (T.vecU φ f j) = T.vecU φ f j := by
    conv_lhs => rw [← hfix]
    exact g.symm_apply_apply _
  let ψ := T.covecU φ f j ∘ₗ ((g : U →ₗ[ZMod p] U) - LinearMap.id)
  have hψ : ∀ w, ψ w = T.covecU φ f j (g w) - T.covecU φ f j w := fun w =>
    map_sub (T.covecU φ f j) (g w) w
  have hh : ∀ w, (T.refl φ f j * (g⁻¹ * T.refl φ f j * g)) w = w + ψ w • T.vecU φ f j := by
    intro w
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, ReflTable.refl_apply hv hp, map_sub,
      map_smul, LinearEquiv.symm_apply_apply, hgr, hc, hψ, smul_eq_mul]
    module
  by_contra hne
  refine htv _ (mul_mem (ReflTable.refl_mem_group hv hp j) (mul_mem (mul_mem (inv_mem hg)
    (ReflTable.refl_mem_group hv hp j)) hg)) ⟨_, ψ, hr, fun h0 => hne ?_,
      (hψ _).trans (sub_eq_zero.mpr (by rw [hfix])), hh⟩
  have h1 := LinearMap.congr_fun h0 v
  rwa [hψ, LinearMap.zero_apply, sub_eq_zero] at h1

private noncomputable def h4X (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) (i : Fin 120) : U :=
  vecR (evalAl hα) f (h4Pt i)

private theorem h4_exists_apply_eq (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) {g : U ≃ₗ[ZMod p] U}
    (hg : g ∈ h4bTab.group (evalAl hα) f) (i : Fin 120) : ∃ i', g (h4X f hα i) = h4X f hα i' := by
  obtain ⟨i', hi'⟩ := exists_orbit_index_of_mem_closure
    (g := fun k => h4bTab.refl (evalAl hα) f (h4bTab.gen k)) (x := h4X f hα) (π := h4Pi)
    (O := fun i (_ : Fin 1) => i) (nxt := h4Pi)
    (fun _ => ReflTable.refl_mul_self h4bTab_valid hp _)
    (fun k i => ReflTable.refl_apply_vecR h4bTab_valid hp (h4_pt_act k i)) (fun _ _ => rfl) hg i
  exact ⟨i', hi' 0⟩

private theorem h4_exists_mem_apply_eq (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) (i : Fin 120) :
    ∃ g ∈ h4bTab.group (evalAl hα) f, g (h4X f hα 0) = h4X f hα i := by
  obtain ⟨g, hg, hgi⟩ := exists_mem_closure_of_orbit
    (g := fun k => h4bTab.refl (evalAl hα) f (h4bTab.gen k)) (x := h4X f hα) (π := h4Pi)
    (O := fun i (_ : Fin 1) => h4Bfs i) (pred := h4Pred) (pk := h4Pk)
    (fun k i => ReflTable.refl_apply_vecR h4bTab_valid hp (h4_pt_act k i)) 0
    (fun i => (h4_pred i).imp_right fun h => ⟨h.1, funext fun _ => h.2.symm⟩)
    ⟨h4BfsL.idxOf i % 120, Nat.mod_lt _ (by decide)⟩
  have h := hgi 0
  rw [h4_bfs_zero, h4_bfs_idx] at h
  exact ⟨g, hg, h⟩

private theorem h4_lev_eq (hp : p ≠ 2) (hp5 : p ≠ 5) (f : Module.Basis (Fin 4) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) (m : Fin 4) {a b : Fin 120}
    (h : h4bTab.covecU (evalAl hα) f (h4Ch m) (h4X f hα a) =
      h4bTab.covecU (evalAl hα) f (h4Ch m) (h4X f hα b)) :
    h4Lev (h4Ch m) a = h4Lev (h4Ch m) b := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h' : evalAl hα (h4Lev (h4Ch m) a) = evalAl hα (h4Lev (h4Ch m) b) :=
    mul_left_cancel₀ (inv_ne_zero h2) ((covecR_vecR _ f _ _).symm.trans
      (h.trans (covecR_vecR _ f _ _)))
  rcases h4_lev_sep _ (h4_lev_mem m a) _ (h4_lev_mem m b) with hab | hg
  · exact hab
  · exact absurd ((map_sub _ _ _).trans (sub_eq_zero.mpr h'))
      (evalAl_ne_zero_of_goodAl235 hp (ne_three_of_sq_eq hα) hp5 hα hg)

private theorem h4X_injective (hp : p ≠ 2) (hp5 : p ≠ 5) (f : Module.Basis (Fin 4) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) : Function.Injective (h4X f hα) := by
  intro a b hab
  refine List.nodup_ofFn.mp (CFSG.Decide.nodup_of_bitsetNodup_nat h4_sig) ?_
  exact Finset.sum_congr rfl fun m _ => by rw [h4_lev_eq hp hp5 f hα m (congrArg _ hab)]

private theorem h4_apply_lev (hp : p ≠ 2) (hp5 : p ≠ 5) (f : Module.Basis (Fin 4) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) {g : U ≃ₗ[ZMod p] U}
    (hg : g ∈ h4bTab.group (evalAl hα) f) (i : Fin 120) :
    ∃ i', g (h4X f hα i) = h4X f hα i' ∧ ∀ m, g (h4X f hα (h4ChPt m)) = h4X f hα (h4ChPt m) →
      h4Lev (h4Ch m) i' = h4Lev (h4Ch m) i := by
  obtain ⟨i', hi'⟩ := h4_exists_apply_eq hp f hα hg i
  refine ⟨i', hi', fun m hm => h4_lev_eq hp hp5 f hα m ?_⟩
  have hfix : g (h4bTab.vecU (evalAl hα) f (h4Ch m)) = h4bTab.vecU (evalAl hα) f (h4Ch m) := by
    rw [ReflTable.vecU, ← h4_ch_root m]
    exact hm
  rw [← hi', covecU_apply_of_apply_eq h4bTab_valid hp (h4b_transvectionFree hp f hα) hg hfix]

private theorem h4_eq_one (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) {g : U ≃ₗ[ZMod p] U}
    (hg : ∀ m, g (h4X f hα (h4ChPt m)) = h4X f hα (h4ChPt m)) : g = 1 := by
  have hspan : Submodule.span (ZMod p) (Set.range fun m => h4X f hα (h4ChPt m)) = ⊤ := by
    rw [eq_top_iff, ← f.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact mem_span_of_sum_smul_eq hp (evalAl hα) f (h4Span i) i (h4_span i)
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on_range hspan
  exact hg

private theorem card_eq_ncard_orbit_mul (K : Subgroup (U ≃ₗ[ZMod p] U)) (v : U) :
    Nat.card K = (MulAction.orbit K v).ncard *
      Nat.card (MulAction.stabilizer (U ≃ₗ[ZMod p] U) v ⊓ K :) := by
  rw [← Subgroup.relIndex_mul_card (MulAction.stabilizer (U ≃ₗ[ZMod p] U) v) K,
    Subgroup.relIndex, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer]

private theorem ncard_orbit_le_length {ι : Type} {K : Subgroup (U ≃ₗ[ZMod p] U)} {v : U}
    {x : ι → U} {L : List ι} (h : ∀ g ∈ K, ∃ i ∈ L, g v = x i) :
    (MulAction.orbit K v).ncard ≤ L.length := by
  classical
  calc (MulAction.orbit K v).ncard ≤ (↑(L.map x).toFinset : Set U).ncard := by
        refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
        rintro _ ⟨⟨g, hg⟩, rfl⟩
        obtain ⟨i, hi, hgi⟩ := h g hg
        simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
        exact ⟨i, hi, hgi.symm⟩
    _ = (L.map x).toFinset.card := Set.ncard_coe_finset _
    _ ≤ (L.map x).length := List.toFinset_card_le _
    _ = L.length := List.length_map _

private theorem h4_card_stab_le (hp : p ≠ 2) (hp5 : p ≠ 5) (f : Module.Basis (Fin 4) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) :
    Nat.card (MulAction.stabilizer (U ≃ₗ[ZMod p] U) (h4X f hα 0) ⊓
      h4bTab.group (evalAl hα) f :) ≤ 120 := by
  set G₁ := MulAction.stabilizer (U ≃ₗ[ZMod p] U) (h4X f hα 0) ⊓ h4bTab.group (evalAl hα) f
  set G₂ := MulAction.stabilizer (U ≃ₗ[ZMod p] U) (h4X f hα 1) ⊓ G₁
  have h3 : MulAction.stabilizer (U ≃ₗ[ZMod p] U) (h4X f hα 43) ⊓ G₂ = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
    simp only [G₂, G₁, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      LinearEquiv.smul_def] at hg
    obtain ⟨h43, h1, h0, hG⟩ := hg
    obtain ⟨i, hi, hlev⟩ := h4_apply_lev hp hp5 f hα hG 19
    have h19 := h4_L4 i (hlev 0 h0) (hlev 1 h1) (hlev 2 h43)
    refine h4_eq_one hp f hα fun m => ?_
    fin_cases m
    exacts [h0, h1, h43, hi.trans (by rw [h19]; rfl)]
  have hb2 : (MulAction.orbit G₁ (h4X f hα 1)).ncard ≤ 12 := by
    refine ncard_orbit_le_length (x := h4X f hα) (L := h4L2) fun g hg => ?_
    simp only [G₁, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, LinearEquiv.smul_def] at hg
    obtain ⟨i, hi, hlev⟩ := h4_apply_lev hp hp5 f hα hg.2 1
    exact ⟨i, h4_L2 i (hlev 0 hg.1), hi⟩
  have hb3 : (MulAction.orbit G₂ (h4X f hα 43)).ncard ≤ 10 := by
    refine ncard_orbit_le_length (x := h4X f hα) (L := h4L3) fun g hg => ?_
    simp only [G₂, G₁, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      LinearEquiv.smul_def] at hg
    obtain ⟨h1, h0, hG⟩ := hg
    obtain ⟨i, hi, hlev⟩ := h4_apply_lev hp hp5 f hα hG 43
    exact ⟨i, h4_L3 i (hlev 0 h0) (hlev 1 h1), hi⟩
  rw [card_eq_ncard_orbit_mul G₁ (h4X f hα 1), card_eq_ncard_orbit_mul G₂ (h4X f hα 43), h3,
    Subgroup.card_bot]
  exact (Nat.mul_le_mul hb2 (Nat.mul_le_mul hb3 le_rfl)).trans (by norm_num)

private theorem h4_card_stab_ge (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) :
    120 ≤ Nat.card (MulAction.stabilizer (U ≃ₗ[ZMod p] U) (h4X f hα 0) ⊓
      h4bTab.group (evalAl hα) f :) := by
  have : Module.Finite (ZMod p) U := Module.Finite.of_basis f
  have : Finite U := Module.finite_of_finite (ZMod p)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) DFunLike.coe_injective
  have hx0 : h4X f hα 0 = evalAl hα (h4Pt 0 0) • f 0 := by
    rw [h4X, vecR, Fin.sum_univ_four, show h4Pt 0 1 = 0 by decide, show h4Pt 0 2 = 0 by decide,
      show h4Pt 0 3 = 0 by decide]
    simp
  have hle : fixReflSubgroup p (basisClosure f (h4BlockMats α)) (f 0) ≤
      MulAction.stabilizer (U ≃ₗ[ZMod p] U) (h4X f hα 0) ⊓ h4bTab.group (evalAl hα) f := by
    rw [fixReflSubgroup, Subgroup.closure_le]
    rintro t ⟨htG, -, ht0⟩
    refine Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr ?_, ?_⟩
    · rw [LinearEquiv.smul_def, hx0, map_smul, ht0]
    · rwa [h4b_basisClosure_eq hp f hα] at htG
  calc 120 = Nat.card (fixReflSubgroup p (basisClosure f (h4BlockMats α)) (f 0)) := by
        rw [fixReflSubgroup_h4b_eq hp f hα, card_basisClosure_h3Mats hp _ hα]
    _ ≤ _ := Subgroup.card_le_of_le hle

theorem card_basisClosure_h4BlockMats (hp : p ≠ 2) (hp5 : p ≠ 5)
    (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    Nat.card (basisClosure f (h4BlockMats α)) = 14400 := by
  have horb : MulAction.orbit (h4bTab.group (evalAl hα) f) (h4X f hα 0) =
      Set.range (h4X f hα) := by
    ext v
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨i, hi⟩ := h4_exists_apply_eq hp f hα hg 0
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨g, hg, hgi⟩ := h4_exists_mem_apply_eq hp f hα i
      exact ⟨⟨g, hg⟩, hgi⟩
  rw [h4b_basisClosure_eq hp f hα, card_eq_ncard_orbit_mul _ (h4X f hα 0), horb,
    Set.ncard_range_of_injective (h4X_injective hp hp5 f hα), Nat.card_fin,
    le_antisymm (h4_card_stab_le hp hp5 f hα) (h4_card_stab_ge hp f hα)]

end CFSG.StandardType.ZS.PrimModel

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime]

theorem tfH4Model5_holds : TFH4Model5 p := by
  intro W _ _ f α hp _ hα h₁ z τ hh₁ hz hτ
  have hker : LinearMap.ker ((h₁ : W →ₗ[ZMod p] W) - 1) = LinearMap.ker (f.coord 0) :=
    PrimModel.ker_sub_one_of_toMatrix_eq_diagSignMat hp f hh₁
  refine ⟨PrimModel.h45_primFrameData hp f hα hh₁ hz hτ, ?_, ?_⟩
  · rw [hker, PrimModel.commutatorSpace_reflSubgroupIn_h45 hp f hα,
      PrimModel.finrank_span_basis_image]
    decide
  · rw [hker, PrimModel.commutatorSpace_reflSubgroupIn_h45 hp f hα]
    exact PrimModel.irredOnSection_reflSubgroupIn_h45 hp f hα

theorem tfH4Model_holds : TFH4Model p := by
  intro W _ _ f α hp _ hα
  rw [PrimModel.fixReflSubgroup_h4b_eq hp f hα]
  refine ⟨PrimModel.oneClass_basisClosure_h4BlockMats hp f hα,
    PrimModel.irredOnSection_basisClosure_h4BlockMats hp f hα,
    PrimModel.splitSupport_basisClosure_h3Mats hp (f.reindex PrimModel.h4Perm) hα, ?_, ?_,
    PrimModel.card_basisClosure_h3Mats hp (f.reindex PrimModel.h4Perm) hα,
    PrimModel.dMax_basisClosure_h3Mats hp (f.reindex PrimModel.h4Perm) hα⟩
  · rw [PrimModel.commutatorSpace_basisClosure_h3Mats hp (f.reindex PrimModel.h4Perm) hα]
    congr 1
  · rw [PrimModel.centralizerSpace_basisClosure_h3Mats hp (f.reindex PrimModel.h4Perm) hα]
    congr 1
    simp [Module.Basis.reindex_apply, PrimModel.h4Perm]

end CFSG.StandardType.ZS

end
