module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelH3Data

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.PrimModel

@[expose] def h3MatFun {K : Type} [Field K] (α : K) : Fin 4 → Matrix (Fin 4) (Fin 4) K :=
  ![Matrix.blockSucc (diagSignMat 0), Matrix.blockSucc (diagSignMat 1),
    Matrix.blockSucc (diagSignMat 2), Matrix.blockSucc (h3BlockMat α)]

theorem range_h3MatFun {K : Type} [Field K] (α : K) : Set.range (h3MatFun α) = h3Mats α := by
  ext M
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k <;> simp [h3MatFun, h3Mats, h3BlockMats]
  · intro hM
    simp only [h3Mats, h3BlockMats, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      at hM
    obtain ⟨x, hx, rfl⟩ := hM
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem diagSignMat_apply {K : Type} [Field K] {n : ℕ} (i a b : Fin n) :
    (diagSignMat i : Matrix (Fin n) (Fin n) K) a b =
      if a = b then (if a = i then -1 else 1) else 0 := by
  simp only [diagSignMat, Matrix.diagonal_apply]

private theorem evMat_h3G_zero (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    evMat (evalAl hα) 1 (h3G 0) = h3MatFun α 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rw [evMat, inv_smul_eq_iff₀ (pow_ne_zero 1 h2)]
  change (h3G 0).map (evalAl hα) =
    (2 : ZMod p) ^ 1 • Matrix.blockSucc (diagSignMat (0 : Fin 3))
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, pow_one, smul_eq_mul]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [Matrix.blockSucc_last_last]; simp [h3G, evalAl_qa]
    | cast j =>
      rw [Matrix.blockSucc_last_castSucc]; fin_cases j <;> simp [h3G, evalAl_qa]
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      rw [Matrix.blockSucc_castSucc_last]; fin_cases i <;> simp [h3G, evalAl_qa]
    | cast j =>
      rw [Matrix.blockSucc_castSucc_castSucc]
      fin_cases i <;> fin_cases j <;> simp [h3G, evalAl_qa, diagSignMat_apply]

private theorem evMat_h3G_one (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    evMat (evalAl hα) 1 (h3G 1) = h3MatFun α 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rw [evMat, inv_smul_eq_iff₀ (pow_ne_zero 1 h2)]
  change (h3G 1).map (evalAl hα) =
    (2 : ZMod p) ^ 1 • Matrix.blockSucc (diagSignMat (1 : Fin 3))
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, pow_one, smul_eq_mul]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [Matrix.blockSucc_last_last]; simp [h3G, evalAl_qa]
    | cast j =>
      rw [Matrix.blockSucc_last_castSucc]; fin_cases j <;> simp [h3G, evalAl_qa]
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      rw [Matrix.blockSucc_castSucc_last]; fin_cases i <;> simp [h3G, evalAl_qa]
    | cast j =>
      rw [Matrix.blockSucc_castSucc_castSucc]
      fin_cases i <;> fin_cases j <;> simp [h3G, evalAl_qa, diagSignMat_apply]

private theorem evMat_h3G_two (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    evMat (evalAl hα) 1 (h3G 2) = h3MatFun α 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rw [evMat, inv_smul_eq_iff₀ (pow_ne_zero 1 h2)]
  change (h3G 2).map (evalAl hα) =
    (2 : ZMod p) ^ 1 • Matrix.blockSucc (diagSignMat (2 : Fin 3))
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, pow_one, smul_eq_mul]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [Matrix.blockSucc_last_last]; simp [h3G, evalAl_qa]
    | cast j =>
      rw [Matrix.blockSucc_last_castSucc]; fin_cases j <;> simp [h3G, evalAl_qa]
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      rw [Matrix.blockSucc_castSucc_last]; fin_cases i <;> simp [h3G, evalAl_qa]
    | cast j =>
      rw [Matrix.blockSucc_castSucc_castSucc]
      fin_cases i <;> fin_cases j <;> simp [h3G, evalAl_qa, diagSignMat_apply]

private theorem evMat_h3G_three (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    evMat (evalAl hα) 1 (h3G 3) = h3MatFun α 3 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rw [evMat, inv_smul_eq_iff₀ (pow_ne_zero 1 h2)]
  change (h3G 3).map (evalAl hα) = (2 : ZMod p) ^ 1 • Matrix.blockSucc (h3BlockMat α)
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, pow_one, smul_eq_mul]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [Matrix.blockSucc_last_last]; simp [h3G, evalAl_qa]
    | cast j => rw [Matrix.blockSucc_last_castSucc]; fin_cases j <;> simp [h3G, evalAl_qa]
  | cast i =>
    induction j using Fin.lastCases with
    | last => rw [Matrix.blockSucc_castSucc_last]; fin_cases i <;> simp [h3G, evalAl_qa]
    | cast j =>
      rw [Matrix.blockSucc_castSucc_castSucc]
      fin_cases i <;> fin_cases j <;>
        simp [h3G, h3BlockMat, Matrix.smul_apply, evalAl_qa] <;>
        field_simp [h2] <;> ring

theorem evMat_h3G (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) (k : Fin 4) :
    evMat (evalAl hα) 1 (h3G k) = h3MatFun α k := by
  fin_cases k
  · exact evMat_h3G_zero hp hα
  · exact evMat_h3G_one hp hα
  · exact evMat_h3G_two hp hα
  · exact evMat_h3G_three hp hα

theorem h3_basisClosure_eq (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) : basisClosure f (h3Mats α) = h3Tab.group (evalAl hα) f := by
  rw [← range_h3MatFun]
  exact ReflTable.basisClosure_eq_group h3Tab_valid hp (fun k => by
    rw [h3Tab_gen k]; exact evMat_h3G hp hα k)

theorem h3_transvectionFree (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) : QTwoLin.TransvectionFree (h3Tab.group (evalAl hα) f) := by
  exact ReflTable.transvectionFree_group h3Tab_valid (fun x hx => evalAl_ne_zero hp hα hx) hp h3D
    h3D_good h3Tab_form

theorem h3_forall_conj (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) {x : U ≃ₗ[ZMod p] U} (hx : x ∈ h3Tab.group (evalAl hα) f)
    (hxr : IsRefl p x) : ∃ j, x = h3Tab.refl (evalAl hα) f j ∧
      ∃ g ∈ h3Tab.group (evalAl hα) f, x = g * h3Tab.refl (evalAl hα) f 0 * g⁻¹ := by
  obtain ⟨j, rfl⟩ := ReflTable.exists_eq_refl h3Tab_valid hp (h3_transvectionFree hp f hα) hx hxr
  have hcls : ∀ j : Fin 15, h3Tab.cls 0 = h3Tab.cls j := by decide
  refine ⟨j, rfl, ?_⟩
  exact ReflTable.exists_conj_of_cls_eq h3Tab_valid hp (j := 0) (j' := j) (hcls j)

theorem h3_toMatrix_diag (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) (i : Fin 3) :
    LinearMap.toMatrix f f (h3Tab.refl (evalAl hα) f (h3UnitIdx i) : U →ₗ[ZMod p] U) =
      diagSignMat i.castSucc := by
  fin_cases i
  · change LinearMap.toMatrix f f (h3Tab.refl (evalAl hα) f (0 : Fin 15) : U →ₗ[ZMod p] U) =
      diagSignMat (0 : Fin 4)
    rw [ReflTable.toMatrix_refl h3Tab_valid hp, h3Tab_diag.1, evMat_diagZ hp (evalAl hα)]
  · change LinearMap.toMatrix f f (h3Tab.refl (evalAl hα) f (14 : Fin 15) : U →ₗ[ZMod p] U) =
      diagSignMat (1 : Fin 4)
    rw [ReflTable.toMatrix_refl h3Tab_valid hp, h3Tab_diag.2.1, evMat_diagZ hp (evalAl hα)]
  · change LinearMap.toMatrix f f (h3Tab.refl (evalAl hα) f (13 : Fin 15) : U →ₗ[ZMod p] U) =
      diagSignMat (2 : Fin 4)
    rw [ReflTable.toMatrix_refl h3Tab_valid hp, h3Tab_diag.2.2, evMat_diagZ hp (evalAl hα)]

theorem h3_primFrameData (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) {h₁ z τ : U ≃ₗ[ZMod p] U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    (hz : LinearMap.toMatrix f f (z : U →ₗ[ZMod p] U) = diagSignMat 0 * diagSignMat 1)
    (hτ : LinearMap.toMatrix f f (τ : U →ₗ[ZMod p] U) = diagSignMat 2) :
    PrimFrameData p (basisClosure f (h3Mats α)) h₁ z τ := by
  rw [h3_basisClosure_eq hp f hα]
  have h0 : LinearMap.toMatrix f f (h3Tab.refl (evalAl hα) f 0 : U →ₗ[ZMod p] U) =
      diagSignMat 0 := by
    rw [ReflTable.toMatrix_refl h3Tab_valid hp, h3Tab_diag.1, evMat_diagZ hp (evalAl hα)]
  have h14 : LinearMap.toMatrix f f (h3Tab.refl (evalAl hα) f 14 : U →ₗ[ZMod p] U) =
      diagSignMat 1 := by
    rw [ReflTable.toMatrix_refl h3Tab_valid hp, h3Tab_diag.2.1, evMat_diagZ hp (evalAl hα)]
  have h13 : LinearMap.toMatrix f f (h3Tab.refl (evalAl hα) f 13 : U →ₗ[ZMod p] U) =
      diagSignMat 2 := by
    rw [ReflTable.toMatrix_refl h3Tab_valid hp, h3Tab_diag.2.2, evMat_diagZ hp (evalAl hα)]
  have hh₁r : h₁ = h3Tab.refl (evalAl hα) f 0 :=
    ReflTable.eq_refl_of_toMatrix (T := h3Tab) (φ := evalAl hα) h3Tab_valid hp (j := 0)
      (M := diagSignMat 0) hh₁ (by rw [h3Tab_diag.1, evMat_diagZ hp (evalAl hα)])
  have hzr : z = h3Tab.refl (evalAl hα) f 0 * h3Tab.refl (evalAl hα) f 14 :=
    eq_mul_of_toMatrix_eq_mul f (by rw [hz, h0, h14])
  have hτr : τ = h3Tab.refl (evalAl hα) f 13 :=
    ReflTable.eq_refl_of_toMatrix (T := h3Tab) (φ := evalAl hα) h3Tab_valid hp (j := 13)
      (M := diagSignMat 2) hτ (by rw [h3Tab_diag.2.2, evMat_diagZ hp (evalAl hα)])
  rw [hh₁r, hzr, hτr]
  refine primFrameData_of_diagonal hp f (I := {0, 1}) (i₁ := 0) (iτ := 2) (by decide) (by decide)
    (by decide) ?_ h0 h13 ?_ ?_ ?_ ?_
  · rw [← hzr, hz]
    exact diagSignMat_mul_diagSignMat (by decide)
  · exact Subgroup.mul_mem _ (ReflTable.refl_mem_group h3Tab_valid hp _)
      (ReflTable.refl_mem_group h3Tab_valid hp _)
  · exact ReflTable.refl_mem_group h3Tab_valid hp _
  · exact ReflTable.exists_conj_of_cls_eq h3Tab_valid hp (j := 0) (j' := 13) (by decide)
  · exact ReflTable.exists_conj_le_inf_ker h3Tab_valid (fun x hx => evalAl_ne_zero hp hα hx) hp
      (h3_transvectionFree hp f hα) {0, 1} 0 h3Wit h3Tab_wit

theorem h3_exists_conj_commute (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) :
    ∀ a ∈ basisClosure f (h3Mats α), ∀ b ∈ basisClosure f (h3Mats α),
      ∀ c ∈ basisClosure f (h3Mats α), IsRefl p a → IsRefl p b → IsRefl p c →
      orderOf (a * b) = 5 →
      ∃ g ∈ Subgroup.closure {a, b}, g * c * g⁻¹ * a = a * (g * c * g⁻¹) := by
  rw [h3_basisClosure_eq hp f hα]
  refine exists_conj_commute_of_forall_conj (a₀ := h3Tab.refl (evalAl hα) f 0) ?_ ?_
  · intro x hx hxr
    obtain ⟨j, -, hconj⟩ := h3_forall_conj hp f hα hx hxr
    exact hconj
  · intro b hb c hc hbr hcr hord
    obtain ⟨j, hbj, -⟩ := h3_forall_conj hp f hα hb hbr
    obtain ⟨k, hck, -⟩ := h3_forall_conj hp f hα hc hcr
    subst hbj
    subst hck
    have hj : h3Ord j = 5 := by
      by_contra h
      rcases (h3_ord_cases j).resolve_left h with ⟨hpos, hle3⟩
      have hpow := ReflTable.pow_mul_refl_eq_one (T := h3Tab) (φ := evalAl hα) (f := f)
        h3Tab_valid hp (h3_ord j)
      have hle := orderOf_le_of_pow_eq_one hpos hpow
      omega
    refine ⟨h3Tab.pairProd (evalAl hα) f 0 j (h3A5 j k), ?_, ?_⟩
    · exact ReflTable.pairProd_mem_closure (T := h3Tab) (φ := evalAl hα) (f := f) 0 j (h3A5 j k)
    · have hg := ReflTable.refl_foldr_rc (T := h3Tab) (φ := evalAl hα) (f := f)
        h3Tab_valid hp h3_rc 0 j (h3A5 j k) k
      rcases h3_a5 j k hj with h0 | ⟨h1, h2⟩
      · rw [← hg]
        change h3Tab.refl (evalAl hα) f (h3A5Img j k) * h3Tab.refl (evalAl hα) f 0 =
          h3Tab.refl (evalAl hα) f 0 * h3Tab.refl (evalAl hα) f (h3A5Img j k)
        rw [h0]
      · rw [← hg]
        change h3Tab.refl (evalAl hα) f (h3A5Img j k) * h3Tab.refl (evalAl hα) f 0 =
          h3Tab.refl (evalAl hα) f 0 * h3Tab.refl (evalAl hα) f (h3A5Img j k)
        exact (ReflTable.refl_mul_comm (T := h3Tab) (φ := evalAl hα) (f := f)
          h3Tab_valid hp h1 h2).symm

theorem card_basisClosure_h3Mats (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) : Nat.card (basisClosure f (h3Mats α)) = 120 := by
  rw [h3_basisClosure_eq hp f hα]
  let g : Fin 4 → U ≃ₗ[ZMod p] U := fun k => h3Tab.refl (evalAl hα) f (h3Tab.gen k)
  let x : Fin 31 → U := fun i => vecR (evalAl hα) f (h3Pt i)
  have hgood : ∀ y, GoodAl y → evalAl hα y ≠ 0 := fun y hy => evalAl_ne_zero hp hα hy
  have hspan : Submodule.span (ZMod p) (Set.range fun l : Fin 4 => x (h3Orb 0 l)) = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = Submodule.span (ZMod p) (Set.range f) := f.span_eq.symm
      _ ≤ Submodule.span (ZMod p) (Set.range fun l : Fin 4 => x (h3Orb 0 l)) := by
          apply Submodule.span_le.mpr
          rintro _ ⟨i, rfl⟩
          exact mem_span_of_sum_smul_eq hp (evalAl hα) f (h3Span i) i (h3_span i)
  refine card_closure_eq_of_orbit (g := g) (x := x) (π := h3Pi) (O := h3Orb) (i₀ := 0)
    (nxt := h3Nxt) (pred := h3Pred) (pk := h3Pk) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k
    exact ReflTable.refl_mul_self (T := h3Tab) (φ := evalAl hα) (f := f) h3Tab_valid hp _
  · intro a b h
    by_contra hab
    exact vecR_ne_of_good hgood f (h3_pt_ne a b hab) h
  · intro k i
    exact ReflTable.refl_apply_vecR (T := h3Tab) (φ := evalAl hα) (f := f) h3Tab_valid hp
      (h3_pt_act k i)
  · exact List.nodup_ofFn.mp (CFSG.Decide.nodup_of_bitsetNodup _ h3_orb_key)
  · intro h hh
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on_range hspan
    intro l
    simpa using hh l
  · exact h3_orb_nxt
  · exact h3_orb_pred

theorem commutatorSpace_basisClosure_h3Mats (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) :
    HardMathSupport.Kantor79.commutatorSpace (basisClosure f (h3Mats α)) =
      LinearMap.ker (f.coord 3) := by
  have hgroup : h3Tab.group (evalAl hα) f =
      Subgroup.closure ((fun j => h3Tab.refl (evalAl hα) f j) '' Set.range h3Tab.gen) := by
    rw [ReflTable.group]
    congr 1
    exact Set.range_comp' (fun j => h3Tab.refl (evalAl hα) f j) h3Tab.gen
  have hgen : ∀ i' : Fin 3, h3UnitIdx i' ∈ Set.range h3Tab.gen := by
    intro i'
    fin_cases i'
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  rw [h3_basisClosure_eq hp f hα, hgroup,
    ReflTable.commutatorSpace_closure_image_refl (T := h3Tab) (φ := evalAl hα) (f := f)
      h3Tab_valid hp (Set.range h3Tab.gen)]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, -, rfl⟩
    change (f.coord 3) (h3Tab.vecU (evalAl hα) f j) = 0
    rw [ReflTable.vecU, coord_vecR, (h3_last j).1, map_zero]
  · rw [← span_image_erase_eq_ker_coord f 3, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hne : i ≠ (3 : Fin 4) := (Finset.mem_erase.mp hi).1
    obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hne
    have hmem := mem_span_of_sum_smul_eq hp (evalAl hα) f
      (a := fun _ : Fin 1 => h3UnitCoef i')
      (v := fun _ : Fin 1 => h3Tab.root (h3UnitIdx i')) (s := 1) i'.castSucc
      (by simpa using h3_unit i')
    refine Submodule.span_mono ?_ hmem
    intro y hy
    obtain ⟨l, rfl⟩ := hy
    exact ⟨h3UnitIdx i', hgen i', rfl⟩

private theorem h3_coroot_unit_val (i' : Fin 3) (k : Fin 4) :
    h3Tab.coroot (h3UnitIdx i') k =
      if k ≠ i'.castSucc then 0
      else if i' = 0 then qa 2 0 else if i' = 1 then qa (-2) 0 else qa 2 (-2) := by
  fin_cases i' <;> fin_cases k <;> decide

private theorem h3_group_eq (_hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) : h3Tab.group (evalAl hα) f =
      Subgroup.closure ((fun j => h3Tab.refl (evalAl hα) f j) '' Set.range h3Tab.gen) := by
  rw [ReflTable.group]
  congr 1
  exact Set.range_comp' (fun j => h3Tab.refl (evalAl hα) f j) h3Tab.gen

private theorem h3_unitIdx_mem_gen (i' : Fin 3) : h3UnitIdx i' ∈ Set.range h3Tab.gen := by
  fin_cases i'
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

private theorem h3_covecU_ker (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {α : ZMod p}
    (hα : α ^ 2 = α + 1) (i' : Fin 3) :
    LinearMap.ker (h3Tab.covecU (evalAl hα) f (h3UnitIdx i')) =
      LinearMap.ker (f.coord i'.castSucc) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h1α : (1 : ZMod p) ≠ α := by
    intro h
    have h21 : (2 : ZMod p) = 1 := by
      rw [← h] at hα
      simpa using hα.symm
    have h10 : (1 : ZMod p) = 0 := by
      have hsub : (2 : ZMod p) - 1 = 0 := by rw [h21, sub_self]
      rw [show (2 : ZMod p) - 1 = 1 by ring] at hsub
      exact hsub
    exact one_ne_zero h10
  have hc : ((2 : ZMod p)⁻¹ * evalAl hα (h3Tab.coroot (h3UnitIdx i') i'.castSucc)) ≠ 0 := by
    rw [h3_coroot_unit_val i' i'.castSucc]
    fin_cases i'
    · simpa [evalAl_qa] using h2
    · simpa [evalAl_qa] using h2
    · simp [evalAl_qa]
      refine ⟨h2, fun hzero => h1α ?_⟩
      have h2eq : (2 : ZMod p) * α = 2 * 1 := by
        rw [mul_one]
        exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hzero)).symm
      exact (mul_left_cancel₀ h2 h2eq).symm
  have hform : h3Tab.covecU (evalAl hα) f (h3UnitIdx i') =
      ((2 : ZMod p)⁻¹ * evalAl hα (h3Tab.coroot (h3UnitIdx i') i'.castSucc)) •
        f.coord i'.castSucc := by
    apply LinearMap.ext_on_range f.span_eq
    intro k
    rw [ReflTable.covecU, covecR_basis, h3_coroot_unit_val i' k,
      h3_coroot_unit_val i' i'.castSucc]
    fin_cases i' <;> fin_cases k <;>
      simp [evalAl_qa, Module.Basis.coord_apply]
  rw [hform]
  exact LinearMap.ker_smul (f.coord i'.castSucc) _ hc

theorem centralizerSpace_basisClosure_h3Mats (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) :
    centralizerSpace (basisClosure f (h3Mats α)) = Submodule.span (ZMod p) {f 3} := by
  rw [h3_basisClosure_eq hp f hα, h3_group_eq hp f hα,
    ReflTable.centralizerSpace_closure_image_refl (T := h3Tab) (φ := evalAl hα) (f := f)
      h3Tab_valid hp (Set.range h3Tab.gen)]
  apply le_antisymm
  · calc ⨅ j ∈ Set.range h3Tab.gen, LinearMap.ker (h3Tab.covecU (evalAl hα) f j)
        ≤ ⨅ i ∈ ({0,1,2} : Finset (Fin 4)), LinearMap.ker (f.coord i) := by
          refine le_iInf fun i => le_iInf fun hi => ?_
          have hne : i ≠ (3 : Fin 4) := by
            intro h
            rw [h] at hi
            simp at hi
          obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hne
          rw [← h3_covecU_ker hp f hα i']
          exact le_trans (iInf_le _ (h3UnitIdx i')) (iInf_le _ (h3_unitIdx_mem_gen i'))
      _ = Submodule.span (ZMod p) {f 3} := by
          rw [iInf_ker_coord_eq_span_image f ({0,1,2} : Finset (Fin 4))]
          have hset : (↑(({0,1,2} : Finset (Fin 4))ᶜ) : Set (Fin 4)) = {3} := by
            ext x
            fin_cases x <;> simp
          rw [hset, Set.image_singleton]
  · rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, Submodule.mem_iInf]
    intro j
    rw [Submodule.mem_iInf]
    intro hj
    rw [LinearMap.mem_ker, ReflTable.covecU, covecR_basis, (h3_last j).2, map_zero, mul_zero]

theorem splitSupport_basisClosure_h3Mats (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) : SplitSupport (basisClosure f (h3Mats α)) 3 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  unfold SplitSupport
  rw [commutatorSpace_basisClosure_h3Mats hp f hα,
    centralizerSpace_basisClosure_h3Mats hp f hα]
  refine ⟨?_, ?_, ?_⟩
  · rw [← span_image_erase_eq_ker_coord f 3, ← Set.image_singleton]
    refine f.linearIndependent.isCompl_span_image f.span_eq ?_
    rw [show (↑((Finset.univ : Finset (Fin 4)).erase 3) : Set (Fin 4)) =
      ({3} : Set (Fin 4))ᶜ by
      ext x; simp]
    exact (isCompl_compl (x := ({3} : Set (Fin 4)))).symm
  · rw [← span_image_erase_eq_ker_coord f 3]
    rw [finrank_span_basis_image]
    decide
  · rw [← span_image_erase_eq_ker_coord f 3]
    refine irredOnSection_span_of_hub hp f (Finset.univ.erase 3)
      (t := h3Tab.refl (evalAl hα) f 7) (r := h3Tab.vecU (evalAl hα) f 7)
      (c := h3Tab.covecU (evalAl hα) f 7) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      have hne : i ≠ (3 : Fin 4) := (Finset.mem_erase.mp hi).1
      obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hne
      refine ⟨h3Tab.refl (evalAl hα) f (h3UnitIdx i'), ?_, ?_, ?_⟩
      · rw [h3_basisClosure_eq hp f hα]
        exact ReflTable.refl_mem_group (T := h3Tab) (φ := evalAl hα) (f := f) h3Tab_valid hp _
      · have hmat := apply_basis_of_toMatrix_eq_diagonal f
          (by simpa [diagSignMat] using h3_toMatrix_diag hp f hα i') i'.castSucc
        simpa using hmat
      · intro j hj
        have hmat := apply_basis_of_toMatrix_eq_diagonal f
          (by simpa [diagSignMat] using h3_toMatrix_diag hp f hα i') j
        simpa [hj] using hmat
    · rw [h3_basisClosure_eq hp f hα]
      exact ReflTable.refl_mem_group (T := h3Tab) (φ := evalAl hα) (f := f) h3Tab_valid hp _
    · intro v
      exact ReflTable.refl_apply (T := h3Tab) (φ := evalAl hα) (f := f) h3Tab_valid hp 7 v
    · intro i hi
      have hne : i ≠ (3 : Fin 4) := (Finset.mem_erase.mp hi).1
      obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hne
      rw [ReflTable.vecU, coord_vecR]
      exact evalAl_ne_zero hp hα (h3_hub i').1
    · intro i hi
      have hne : i ≠ (3 : Fin 4) := (Finset.mem_erase.mp hi).1
      obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hne
      rw [ReflTable.covecU, covecR_basis]
      exact mul_ne_zero (inv_ne_zero h2) (evalAl_ne_zero hp hα (h3_hub i').2)

theorem dMax_basisClosure_h3Mats (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {α : ZMod p} (hα : α ^ 2 = α + 1) : DMax p (basisClosure f (h3Mats α)) 5 := by
  rw [h3_basisClosure_eq hp f hα]
  refine dMax_of_forall_conj (a₀ := h3Tab.refl (evalAl hα) f 0) ?_ ?_ ?_ ?_ ?_
  · exact ReflTable.refl_mem_group (T := h3Tab) (φ := evalAl hα) (f := f) h3Tab_valid hp 0
  · exact ReflTable.isRefl_refl (T := h3Tab) (φ := evalAl hα) (f := f) h3Tab_valid hp 0
  · intro x hx hxr
    obtain ⟨j, -, hconj⟩ := h3_forall_conj hp f hα hx hxr
    exact hconj
  · intro y hy hyr
    obtain ⟨j, rfl⟩ := ReflTable.exists_eq_refl (T := h3Tab) (φ := evalAl hα) (f := f)
      h3Tab_valid hp (h3_transvectionFree hp f hα) hy hyr
    have hpow := ReflTable.pow_mul_refl_eq_one (T := h3Tab) (φ := evalAl hα) (f := f)
      h3Tab_valid hp (h3_ord j)
    have hpos : 0 < h3Ord j := by
      rcases h3_ord_cases j with h | h
      · rw [h]; norm_num
      · exact h.1
    have hle := orderOf_le_of_pow_eq_one hpos hpow
    have hle5 : h3Ord j ≤ 5 := by
      rcases h3_ord_cases j with h | h
      · rw [h]
      · omega
    exact le_trans hle hle5
  · refine ⟨h3Tab.refl (evalAl hα) f 1, ?_, ?_, ?_⟩
    · exact ReflTable.refl_mem_group (T := h3Tab) (φ := evalAl hα) (f := f) h3Tab_valid hp 1
    · exact ReflTable.isRefl_refl (T := h3Tab) (φ := evalAl hα) (f := f) h3Tab_valid hp 1
    · have hpow := ReflTable.pow_mul_refl_eq_one (T := h3Tab) (φ := evalAl hα) (f := f)
        h3Tab_valid hp (h3_ord 1)
      have hpow5 : (h3Tab.refl (evalAl hα) f 0 * h3Tab.refl (evalAl hα) f 1) ^ 5 = 1 := by
        rw [show h3Ord 1 = 5 from rfl] at hpow
        exact hpow
      have hne : h3Tab.refl (evalAl hα) f 0 * h3Tab.refl (evalAl hα) f 1 ≠ 1 :=
        ReflTable.mul_refl_ne_one (T := h3Tab) (φ := evalAl hα) (f := f) h3Tab_valid
          (fun x hx => evalAl_ne_zero hp hα hx) hp (i := 0) (j := 1) (a := 1) (b := 1)
          h3_ne_one
      exact @orderOf_eq_prime (U ≃ₗ[ZMod p] U) _
        (PrimModel.h3Tab.refl (PrimModel.evalAl hα) f 0 *
          PrimModel.h3Tab.refl (PrimModel.evalAl hα) f 1)
        5 ⟨by norm_num⟩ hpow5 hne

end CFSG.StandardType.ZS.PrimModel

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime]

theorem tfH3Model_holds : TFH3Model p := by
  intro W _ _ f α hp _ hα
  exact ⟨PrimModel.card_basisClosure_h3Mats hp f hα,
    fun h₁ z τ hh₁ hz hτ => PrimModel.h3_primFrameData hp f hα hh₁ hz hτ,
    fun a ha b hb c hc har hbr hcr hab _ =>
      PrimModel.h3_exists_conj_commute hp f hα a ha b hb c hc har hbr hcr hab⟩

theorem tfH3Pair_holds : TFH3Pair p := by
  intro W _ _ f α hp _ hα h₁ a hh₁ ha g hg hgr hle
  have h0 : LinearMap.toMatrix f f (PrimModel.h3Tab.refl (PrimModel.evalAl hα) f 0 :
      W →ₗ[ZMod p] W) = diagSignMat 0 := by
    rw [PrimModel.ReflTable.toMatrix_refl PrimModel.h3Tab_valid hp, PrimModel.h3Tab_diag.1,
      PrimModel.evMat_diagZ hp (PrimModel.evalAl hα)]
  have h7 : PrimModel.evMat (PrimModel.evalAl hα) 1
      (PrimModel.reflZ (PrimModel.h3Tab.root 7) (PrimModel.h3Tab.coroot 7)) =
      Matrix.blockSucc (h3BlockMat α) := by
    rw [show (7 : Fin 15) = PrimModel.h3Tab.gen 3 from rfl, PrimModel.h3Tab_gen 3,
      PrimModel.evMat_h3G hp hα 3]
    rfl
  have hh₁r : h₁ = PrimModel.h3Tab.refl (PrimModel.evalAl hα) f 0 :=
    PrimModel.ReflTable.eq_refl_of_toMatrix (T := PrimModel.h3Tab) (φ := PrimModel.evalAl hα)
      PrimModel.h3Tab_valid hp (j := 0) (M := diagSignMat 0) hh₁ (by
        rw [PrimModel.h3Tab_diag.1, PrimModel.evMat_diagZ hp (PrimModel.evalAl hα)])
  have har : a = PrimModel.h3Tab.refl (PrimModel.evalAl hα) f 7 :=
    PrimModel.ReflTable.eq_refl_of_toMatrix (T := PrimModel.h3Tab) (φ := PrimModel.evalAl hα)
      PrimModel.h3Tab_valid hp (j := 7) (M := Matrix.blockSucc (h3BlockMat α)) ha h7
  rw [hh₁r, har] at hle ⊢
  rw [PrimModel.h3_basisClosure_eq hp f hα] at hg
  obtain ⟨j, hgj, -⟩ := PrimModel.h3_forall_conj hp f hα hg hgr
  subst hgj
  simp only [PrimModel.ReflTable.movedSpace_refl (T := PrimModel.h3Tab) (φ := PrimModel.evalAl hα)
    (f := f) PrimModel.h3Tab_valid hp] at hle
  have hmem : PrimModel.h3Tab.vecU (PrimModel.evalAl hα) f j ∈ Submodule.span (ZMod p)
      {PrimModel.h3Tab.vecU (PrimModel.evalAl hα) f 0,
        PrimModel.h3Tab.vecU (PrimModel.evalAl hα) f 7} := by
    have h := hle (Submodule.subset_span
      (Set.mem_singleton (PrimModel.h3Tab.vecU (PrimModel.evalAl hα) f j)))
    rwa [← Submodule.span_insert] at h
  rcases PrimModel.h3_ell.2.2 j with h0j | hgoodj
  · have hpair := PrimModel.h3_pair j h0j
    have hmem2 := PrimModel.ReflTable.refl_foldr_rc_mem_closure (T := PrimModel.h3Tab)
      (φ := PrimModel.evalAl hα) (f := f) PrimModel.h3Tab_valid hp PrimModel.h3_rc 0 7
      (PrimModel.h3PairW j) (PrimModel.h3PairB j)
    change PrimModel.h3Tab.refl (PrimModel.evalAl hα) f (PrimModel.h3PairImg j) ∈
      Subgroup.closure {PrimModel.h3Tab.refl (PrimModel.evalAl hα) f 0,
        PrimModel.h3Tab.refl (PrimModel.evalAl hα) f 7} at hmem2
    rwa [hpair] at hmem2
  · exact absurd hmem (PrimModel.ReflTable.vecU_not_mem_span_pair (T := PrimModel.h3Tab)
      (φ := PrimModel.evalAl hα) (f := f) (fun x hx => PrimModel.evalAl_ne_zero hp hα hx) hp
      PrimModel.h3Ell PrimModel.h3_ell.1 PrimModel.h3_ell.2.1 hgoodj)

end CFSG.StandardType.ZS

end
