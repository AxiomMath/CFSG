module

public import CFSG.Monster.B.E6.StdF4HeckeCount
public import CFSG.Monster.B.Generic.OrbitalAlgebra

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.Classical
open Matrix MulAction CFSG.Monster.B.Generic

theorem form_sub_smul_right (x v w : Fin 6 → ℤ) (c : ℤ) :
    E6Folded.form x (v - c • w) = E6Folded.form x v - c * E6Folded.form x w := by
  rw [E6Folded.form_symm, E6Folded.form_sub_smul_left, E6Folded.form_symm v, E6Folded.form_symm w]

theorem form_s (i : Fin 6) (u v : Fin 6 → ℤ) :
    E6Folded.form (E6Folded.s i u) (E6Folded.s i v) = E6Folded.form u v := by
  simp only [E6Folded.s]
  rw [E6Folded.form_sub_smul_left, form_sub_smul_right, form_sub_smul_right, E6Folded.form_e_e,
    E6Folded.form_symm (E6Folded.e i) v]
  ring

theorem form_r (k : Fin 4) (u v : Fin 6 → ℤ) :
    E6Folded.form (E6Folded.r k u) (E6Folded.r k v) = E6Folded.form u v := by
  match k with
  | 0 => exact form_s 1 u v
  | 1 => exact form_s 3 u v
  | 2 =>
    change E6Folded.form (E6Folded.s 2 (E6Folded.s 4 u)) (E6Folded.s 2 (E6Folded.s 4 v)) = _
    rw [form_s, form_s]
  | 3 =>
    change E6Folded.form (E6Folded.s 0 (E6Folded.s 5 u)) (E6Folded.s 0 (E6Folded.s 5 v)) = _
    rw [form_s, form_s]

theorem form_wsmul
    (w : NW) (u v : Fin 6 → ℤ) :
    E6Folded.form (wsmul w u) (wsmul w v) = E6Folded.form u v := by
  obtain ⟨ω, rfl⟩ := ncs.wordProd_surjective w
  rw [wsmul_wordProd, wsmul_wordProd]
  induction ω with
  | nil => rfl
  | cons k ω ih => rw [List.foldr_cons, List.foldr_cons, form_r, ih]

theorem levList_ptIdx
    (w : NW) :
    E6Folded.levList.getD (ptIdx w) 0 = E6Folded.form E6Folded.θ (wsmul w E6Folded.θ) := by
  rw [← E6Folded.form_θ_ι, ι_ptIdx, coe_weylPerm_apply]
  rfl

theorem lidx_ptIdx_inv
    (w : NW) : lidx (ptIdx w⁻¹) = lidx (ptIdx w) := by
  have h : E6Folded.form E6Folded.θ (wsmul w⁻¹ E6Folded.θ) =
      E6Folded.form E6Folded.θ (wsmul w E6Folded.θ) := by
    rw [← form_wsmul w, ← wsmul_mul, mul_inv_cancel, wsmul_one, E6Folded.form_symm]
  rw [lidx, lidx, levList_ptIdx, levList_ptIdx, h]

theorem relPt_comm
    {y z : stdGroup} (hy : y ∈ rootClass) (hz : z ∈ rootClass) :
    relPt y z = relPt z y := by
  rw [relPt_eq hy hz (chamberRoot_ptChamber hy) (chamberRoot_ptChamber hz),
    relPt_eq hz hy (chamberRoot_ptChamber hz) (chamberRoot_ptChamber hy), rho, rho,
    dist_inv hδ (ptChamber y) (ptChamber z), lidx_ptIdx_inv]

theorem relPt_lt
    (y z : stdGroup) : relPt y z < 5 := lidx_lt _ (rhoPt _ z).2

theorem relPt_rootMap
    (g h : stdGroup) :
    relPt (rootMap g) (rootMap h) = lidx (ptIdx (wOf (g⁻¹ * h))) := by
  rw [relPt_eq ((mem_rootClass_iff _).2 ⟨g, rfl⟩) ((mem_rootClass_iff _).2 ⟨h, rfl⟩)
    (chamberRoot_mk g) (chamberRoot_mk h), rho, stdDistance_mk_mk]

theorem lidx_eq_zero_iff : ∀ γ < 24, lidx γ = 0 ↔ γ = 23 := by decide +kernel

theorem relPt_eq_zero_iff
    {y z : stdGroup} (hy : y ∈ rootClass) (hz : z ∈ rootClass) :
    relPt y z = 0 ↔ y = z := by
  rw [relPt, lidx_eq_zero_iff _ (rhoPt _ z).2, rhoPt_eq_23_iff _ hz, chamberRoot_ptChamber hy,
    eq_comm]

abbrev Pts :
    Type := ↥rootClass

instance :
    Fintype Pts := Fintype.ofFinite _

@[expose] def starConj
    (γ : GStar) (x : stdGroup) : stdGroup :=
  γ.left * (γ.right : MulAut stdGroup) x * γ.left⁻¹

theorem inl_starConj
    (γ : GStar) (x : stdGroup) :
    SemidirectProduct.inl (starConj γ x) = γ * SemidirectProduct.inl x * γ⁻¹ :=
  (conj_inl γ x).symm

theorem starConj_rootMap
    (γ : GStar) (g : stdGroup) :
    starConj γ (rootMap g) = rootMap (γ.left * (γ.right : MulAut stdGroup) g) := by
  rw [starConj, apply_rootMap_of_mem_betaGroup, rootMap_mul]

theorem starConj_mem
    (γ : GStar) {x : stdGroup} (hx : x ∈ rootClass) :
    starConj γ x ∈ rootClass := by
  obtain ⟨g, rfl⟩ := (mem_rootClass_iff x).1 hx
  rw [starConj_rootMap]
  exact (mem_rootClass_iff _).2 ⟨_, rfl⟩

theorem starConj_one
    (x : stdGroup) : starConj 1 x = x :=
  SemidirectProduct.inl_injective (by rw [inl_starConj, one_mul, inv_one, mul_one])

theorem starConj_mul
    (γ γ' : GStar) (x : stdGroup) :
    starConj (γ * γ') x = starConj γ (starConj γ' x) :=
  SemidirectProduct.inl_injective (by
    rw [inl_starConj, inl_starConj, inl_starConj]
    group)

instance :
    MulAction GStar Pts where
  smul γ x := ⟨starConj γ x, starConj_mem γ x.2⟩
  one_smul x := Subtype.ext (starConj_one x.1)
  mul_smul γ γ' x := Subtype.ext (starConj_mul γ γ' x.1)

theorem coe_smul
    (γ : GStar) (x : Pts) : ((γ • x : Pts) : stdGroup) = starConj γ x := rfl

@[expose] def relIdx
    (x y : Pts) : Fin 5 := ⟨relPt x y, relPt_lt _ _⟩

theorem val_relIdx
    (x y : Pts) : (relIdx x y : ℕ) = relPt x y := rfl

theorem relIdx_comm
    (x y : Pts) : relIdx x y = relIdx y x :=
  Fin.ext (relPt_comm x.2 y.2)

theorem relIdx_eq_zero_iff
    (x y : Pts) : relIdx x y = 0 ↔ x = y := by
  rw [Fin.ext_iff, val_relIdx, Fin.val_zero, relPt_eq_zero_iff x.2 y.2]
  exact (Subtype.ext_iff (a1 := x) (a2 := y)).symm

theorem wOf_apply_of_mem_betaGroup
    (b : betaGroup) (g : stdGroup) :
    wOf ((b : MulAut stdGroup) g) = wOf g := by
  rcases mem_betaGroup_iff.mp b.2 with h | h <;> rw [h]
  · rfl
  · exact wOf_betaG g

theorem relIdx_smul
    (γ : GStar) (x y : Pts) : relIdx (γ • x) (γ • y) = relIdx x y := by
  obtain ⟨g, hg⟩ := (mem_rootClass_iff x.1).1 x.2
  obtain ⟨h, hh⟩ := (mem_rootClass_iff y.1).1 y.2
  apply Fin.ext
  rw [val_relIdx, val_relIdx, coe_smul, coe_smul, ← hg, ← hh, starConj_rootMap,
    starConj_rootMap, relPt_rootMap, relPt_rootMap]
  have e : (γ.left * (γ.right : MulAut stdGroup) g)⁻¹ * (γ.left * (γ.right : MulAut stdGroup) h) =
      (γ.right : MulAut stdGroup) (g⁻¹ * h) := by
    rw [map_mul, map_inv]
    group
  rw [e, wOf_apply_of_mem_betaGroup]

theorem lidx_injOn : ∀ β < 24, ∀ γ < 24, lidx β = lidx γ →
    E6Folded.levList.getD β 0 = E6Folded.levList.getD γ 0 := by
  decide +kernel

theorem exists_smul_pair
    {x y x' y' : Pts} (h : relIdx x y = relIdx x' y') :
    ∃ γ : GStar, γ • x = x' ∧ γ • y = y' := by
  obtain ⟨g, hg⟩ := (mem_rootClass_iff x.1).1 x.2
  obtain ⟨h₀, hh⟩ := (mem_rootClass_iff y.1).1 y.2
  obtain ⟨g', hg'⟩ := (mem_rootClass_iff x'.1).1 x'.2
  obtain ⟨h', hh'⟩ := (mem_rootClass_iff y'.1).1 y'.2
  have hrel : relPt (rootMap g) (rootMap h₀) = relPt (rootMap g') (rootMap h') := by
    rw [hg, hh, hg', hh']
    exact congrArg Fin.val h
  rw [relPt_rootMap, relPt_rootMap] at hrel
  have hlev : lev (g⁻¹ * h₀) = lev (g'⁻¹ * h') := by
    have e := lidx_injOn _ (ptIdx (wOf (g⁻¹ * h₀))).2 _ (ptIdx (wOf (g'⁻¹ * h'))).2 hrel
    rw [levList_ptIdx, levList_ptIdx] at e
    exact e
  have hmem : rootMap (g'⁻¹ * h') ∈ conjOrbit PJ (rootMap (g⁻¹ * h₀)) := by
    rw [conjOrbit_PJ_rootMap, hlev]
    exact rootMap_mem_levPoints _
  obtain ⟨p, hp, hpe⟩ := hmem
  have hpt : p * rootInv * p⁻¹ = rootInv := (mem_centralizer_rootInv_iff p).2 hp
  refine ⟨SemidirectProduct.inl (g' * p * g⁻¹), Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [coe_smul, starConj]
    simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, OneMemClass.coe_one,
      MulAut.one_apply]
    rw [← hg, ← hg', rootMap, rootMap]
    calc g' * p * g⁻¹ * (g * rootInv * g⁻¹) * (g' * p * g⁻¹)⁻¹ =
        g' * (p * rootInv * p⁻¹) * g'⁻¹ := by group
      _ = g' * rootInv * g'⁻¹ := by rw [hpt]
  · rw [coe_smul, starConj]
    simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, OneMemClass.coe_one,
      MulAut.one_apply]
    rw [← hh, ← hh']
    rw [rootMap_mul] at hpe
    calc g' * p * g⁻¹ * rootMap h₀ * (g' * p * g⁻¹)⁻¹ =
        g' * (p * rootMap (g⁻¹ * h₀) * p⁻¹) * g'⁻¹ := by rw [rootMap_mul]; group
      _ = g' * rootMap (g'⁻¹ * h') * g'⁻¹ := by
          rw [← hpe, rootMap_mul]
      _ = rootMap h' := by rw [← rootMap_mul, mul_inv_cancel_left]

theorem mk_eq_mk_iff
    (x y x' y' : Pts) :
    (Quotient.mk _ (x, y) : orbitRel.Quotient GStar (Pts × Pts)) = Quotient.mk _ (x', y') ↔
      relIdx x y = relIdx x' y' := by
  constructor
  · intro h
    obtain ⟨γ, hγ⟩ := Quotient.exact h
    have hx : γ • x' = x := congrArg Prod.fst hγ
    have hy : γ • y' = y := congrArg Prod.snd hγ
    rw [← hx, ← hy, relIdx_smul]
  · intro h
    obtain ⟨γ, hx, hy⟩ := exists_smul_pair h.symm
    exact Quotient.sound ⟨γ, show γ • (x', y') = (x, y) by rw [Prod.smul_mk, hx, hy]⟩

instance :
    IsPretransitive GStar Pts := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨γ, hγ, -⟩ := exists_smul_pair (x := x) (y := x) (x' := y) (y' := y)
    (by rw [(relIdx_eq_zero_iff x x).2 rfl, (relIdx_eq_zero_iff y y).2 rfl])
  exact ⟨γ, hγ⟩

@[expose] def orbA
    (i : Fin 5) : Matrix Pts Pts ℝ :=
  Matrix.of fun x y => if relIdx x y = i then 1 else 0

theorem orbA_apply
    (i : Fin 5) (x y : Pts) : orbA i x y = if relIdx x y = i then 1 else 0 :=
  rfl

theorem orbitalMatrix_eq_orbA
    {x₀ y₀ : Pts} :
    orbitalMatrix (Quotient.mk _ (x₀, y₀) : orbitRel.Quotient GStar (Pts × Pts)) =
      orbA (relIdx x₀ y₀) := by
  classical
  ext x y
  simp only [orbitalMatrix_apply, orbA_apply, mk_eq_mk_iff]

@[expose] def basePt :
    Pts := ⟨rootInv, (mem_rootClass_iff _).2 ⟨1, rootMap_one⟩⟩

@[expose] def orbM (k i j : Fin 5) : ℕ := ((hMat.getD k []).getD i []).getD j 0

theorem card_filter_relIdx
    (x y : Pts) (k j : Fin 5) :
    (Finset.univ.filter fun z : Pts => relIdx x z = k ∧ relIdx z y = j).card =
      orbM k (relIdx x y) j := by
  rw [orbM, val_relIdx, ← ncard_relPt_relPt x.2 y.2 k.2 j.2, ← Set.ncard_coe_finset]
  refine Set.ncard_congr (fun z _ => z.1) (fun z hz => ?_) (fun a b _ _ h => Subtype.ext h)
    (fun z hz => ⟨⟨z, hz.1⟩, ?_, rfl⟩)
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz
    exact ⟨z.2, congrArg Fin.val hz.1, congrArg Fin.val hz.2⟩
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact ⟨Fin.ext hz.2.1, Fin.ext hz.2.2⟩

theorem orbA_mul
    (k j : Fin 5) : orbA k * orbA j = ∑ i, (orbM k i j : ℝ) • orbA i := by
  classical
  ext x y
  have lhs : (orbA k * orbA j) x y =
      ((Finset.univ.filter fun z : Pts => relIdx x z = k ∧ relIdx z y = j).card : ℝ) := by
    rw [mul_apply, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [orbA_apply]
    split_ifs <;> simp_all
  have rhs : (∑ i, (orbM k i j : ℝ) • orbA i) x y = orbM k (relIdx x y) j := by
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, orbA_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  rw [lhs, rhs, card_filter_relIdx]

open _root_.Classical in
theorem orbA_zero :
    orbA 0 = 1 := by
  ext x y
  rw [orbA_apply, Matrix.one_apply]
  by_cases h : x = y
  · rw [ite_eq_left ((relIdx_eq_zero_iff x y).2 h), ite_eq_left h]
  · rw [ite_eq_right (mt (relIdx_eq_zero_iff x y).1 h), ite_eq_right h]

@[expose] def orbK : Fin 5 → ℕ := ![1, 1782, 44352, 1824768, 2097152]

theorem orbM_zero_diag : ∀ i : Fin 5, orbM i 0 i = orbK i := by decide +kernel

theorem card_relIdx
    (i : Fin 5) (x : Pts) :
    (Finset.univ.filter fun y : Pts => relIdx x y = i).card = orbK i := by
  rw [← orbM_zero_diag i, ← (relIdx_eq_zero_iff x x).2 rfl, ← card_filter_relIdx x x i i]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ⟨h, by rw [relIdx_comm]; exact h⟩
  · exact fun h => h.1

@[expose] def orbP : Fin 5 → Fin 5 → ℤ :=
  ![![1, -297, 5544, -38016, 32768], ![1, -37, 84, 464, -512], ![1, 27, -108, -432, 512],
    ![1, 243, 1260, 2592, -4096], ![1, 1782, 44352, 1824768, 2097152]]

theorem sph_check : ∀ r k l : Fin 5,
    (∑ i : Fin 5, (orbM k l i : ℚ) * orbP r i / orbK i) = orbP r k * orbP r l / orbK l := by
  decide +kernel

@[expose] def sphVec
    (r : Fin 5) (y : Pts) : ℝ :=
  (orbP r (relIdx basePt y) : ℝ) / orbK (relIdx basePt y)

theorem sphVec_eq
    (r : Fin 5) (y : Pts) :
    sphVec r y = ∑ i, ((orbP r i : ℝ) / orbK i) * orbA i y basePt := by
  simp only [orbA_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _), sphVec, relIdx_comm]

theorem sum_orbA_mul_orbA
    (k i : Fin 5) (x : Pts) :
    ∑ y, orbA k x y * orbA i y basePt = (orbM k (relIdx x basePt) i : ℝ) := by
  have h := congrFun (congrFun (orbA_mul k i) x) basePt
  rw [mul_apply] at h
  rw [h, Matrix.sum_apply]
  simp only [Matrix.smul_apply, orbA_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]

theorem orbA_mulVec_sphVec
    (r k : Fin 5) : orbA k *ᵥ sphVec r = (orbP r k : ℝ) • sphVec r := by
  ext x
  have hL : (orbA k *ᵥ sphVec r) x =
      ∑ i : Fin 5, (orbP r i : ℝ) / orbK i * (orbM k (relIdx x basePt) i : ℝ) := by
    rw [mulVec, dotProduct]
    simp_rw [sphVec_eq r, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_orbA_mul_orbA k i x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have hc := sph_check r k (relIdx x basePt)
  have hR : (∑ i : Fin 5, (orbP r i : ℝ) / orbK i * (orbM k (relIdx x basePt) i : ℝ)) =
      (orbP r k : ℝ) * orbP r (relIdx x basePt) / orbK (relIdx x basePt) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hc
    push_cast at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hL, hR, Pi.smul_apply, smul_eq_mul, sphVec, relIdx_comm basePt x]
  ring

theorem sphVec_basePt
    (r : Fin 5) : sphVec r basePt = 1 := by
  rw [sphVec, (relIdx_eq_zero_iff _ _).2 rfl]
  fin_cases r <;> norm_num [orbP, orbK]

theorem sphVec_ne_zero
    (r : Fin 5) : sphVec r ≠ 0 := fun h => by
  have := congrFun h basePt
  rw [sphVec_basePt, Pi.zero_apply] at this
  exact one_ne_zero this

@[expose] def orbMat : Fin 5 → Fin 5 → ℕ :=
  ![![0, 1782, 0, 0, 0], ![1, 85, 672, 1024, 0], ![0, 27, 27, 1728, 0], ![0, 1, 42, 715, 1024],
    ![0, 0, 0, 891, 891]]

theorem orbM_one : ∀ i j : Fin 5, orbM 1 i j = orbMat i j := by decide +kernel

theorem scalar_eq_of_smul
    {v : Pts → ℝ} (hv : v ≠ 0) {a b : ℝ} (h : a • v = b • v) : a = b := by
  have h' : (a - b) • v = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.1 h' with h0 | h0
  · exact sub_eq_zero.1 h0
  · exact absurd h0 hv

theorem eigen_relations
    {p : Fin 5 → ℝ} {v : Pts → ℝ} (hv : v ≠ 0)
    (h : ∀ i, orbA i *ᵥ v = p i • v) :
    p 0 = 1 ∧ ∀ j, p 1 * p j = ∑ i, (orbMat i j : ℝ) * p i := by
  classical
  refine ⟨?_, fun j => ?_⟩
  · have h0 := h 0
    rw [orbA_zero, one_mulVec] at h0
    exact (scalar_eq_of_smul hv (by rw [one_smul]; exact h0)).symm
  · have e1 : (orbA 1 * orbA j) *ᵥ v = (p 1 * p j) • v := by
      rw [← mulVec_mulVec, h j, mulVec_smul, h 1, smul_smul, mul_comm]
    have e2 : (orbA 1 * orbA j) *ᵥ v = (∑ i, (orbMat i j : ℝ) * p i) • v := by
      rw [orbA_mul, sum_mulVec, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mulVec, h i, smul_smul, orbM_one]
    exact scalar_eq_of_smul hv (e1.symm.trans e2)

theorem eq_orbP_of_eigen
    {p : Fin 5 → ℝ} {v : Pts → ℝ} (hv : v ≠ 0)
    (h : ∀ i, orbA i *ᵥ v = p i • v) : ∃ r : Fin 5, ∀ i, p i = orbP r i := by
  obtain ⟨h0, hj⟩ := eigen_relations hv h
  have e1 : p 1 * p 1 = 1782 + 85 * p 1 + 27 * p 2 + p 3 := by
    have := hj 1
    simp [Fin.sum_univ_five, orbMat, h0] at this
    linear_combination this
  have e2 : p 1 * p 2 = 672 * p 1 + 27 * p 2 + 42 * p 3 := by
    have := hj 2
    simp [Fin.sum_univ_five, orbMat, h0] at this
    linear_combination this
  have e3 : p 1 * p 3 = 1024 * p 1 + 1728 * p 2 + 715 * p 3 + 891 * p 4 := by
    have := hj 3
    simp [Fin.sum_univ_five, orbMat, h0] at this
    linear_combination this
  have e4 : p 1 * p 4 = 1024 * p 3 + 891 * p 4 := by
    have := hj 4
    simp [Fin.sum_univ_five, orbMat, h0] at this
    linear_combination this
  have hχ : (p 1 + 297) * (p 1 + 37) * (p 1 - 27) * (p 1 - 243) * (p 1 - 1782) = 0 := by
    linear_combination (p 1 ^ 3 - 1633 * p 1 ^ 2 - 304533 * p 1 + 72098829) * e1 -
      (-27 * p 1 ^ 2 + 41634 * p 1 + 8973261) * e2 - (-p 1 ^ 2 - 216 * p 1 + 986337) * e3 -
      (-891 * p 1 - 986337) * e4
  have hrow : ∀ r : Fin 5, p 1 = orbP r 1 → p 2 = orbP r 2 → p 3 = orbP r 3 →
      p 4 = orbP r 4 → ∀ i, p i = orbP r i := by
    intro r h1 h2 h3 h4 i
    have hr0 : (orbP r 0 : ℝ) = 1 := by fin_cases r <;> norm_num [orbP]
    fin_cases i
    · show p 0 = (orbP r 0 : ℝ)
      rw [hr0]
      exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  rcases mul_eq_zero.1 hχ with hA | hA
  · rcases mul_eq_zero.1 hA with hB | hB
    · rcases mul_eq_zero.1 hB with hC | hC
      · rcases mul_eq_zero.1 hC with hD | hD
        · have hx : p 1 = -297 := by linarith
          rw [hx] at e1 e2 e4
          have h2 : p 2 = 5544 := by linarith
          have h3 : p 3 = -38016 := by linarith
          have h4 : p 4 = 32768 := by linarith
          exact ⟨0, hrow 0 (by rw [hx]; norm_num [orbP]) (by rw [h2]; norm_num [orbP])
            (by rw [h3]; norm_num [orbP]) (by rw [h4]; norm_num [orbP])⟩
        · have hx : p 1 = -37 := by linarith
          rw [hx] at e1 e2 e4
          have h2 : p 2 = 84 := by linarith
          have h3 : p 3 = 464 := by linarith
          have h4 : p 4 = -512 := by linarith
          exact ⟨1, hrow 1 (by rw [hx]; norm_num [orbP]) (by rw [h2]; norm_num [orbP])
            (by rw [h3]; norm_num [orbP]) (by rw [h4]; norm_num [orbP])⟩
      · have hx : p 1 = 27 := by linarith
        rw [hx] at e1 e2 e4
        have h2 : p 2 = -108 := by linarith
        have h3 : p 3 = -432 := by linarith
        have h4 : p 4 = 512 := by linarith
        exact ⟨2, hrow 2 (by rw [hx]; norm_num [orbP]) (by rw [h2]; norm_num [orbP])
          (by rw [h3]; norm_num [orbP]) (by rw [h4]; norm_num [orbP])⟩
    · have hx : p 1 = 243 := by linarith
      rw [hx] at e1 e2 e4
      have h2 : p 2 = 1260 := by linarith
      have h3 : p 3 = 2592 := by linarith
      have h4 : p 4 = -4096 := by linarith
      exact ⟨3, hrow 3 (by rw [hx]; norm_num [orbP]) (by rw [h2]; norm_num [orbP])
        (by rw [h3]; norm_num [orbP]) (by rw [h4]; norm_num [orbP])⟩
  · have hx : p 1 = 1782 := by linarith
    rw [hx] at e1 e2 e4
    have h2 : p 2 = 44352 := by linarith
    have h3 : p 3 = 1824768 := by linarith
    have h4 : p 4 = 2097152 := by linarith
    exact ⟨4, hrow 4 (by rw [hx]; norm_num [orbP]) (by rw [h2]; norm_num [orbP])
      (by rw [h3]; norm_num [orbP]) (by rw [h4]; norm_num [orbP])⟩

instance :

    Fintype (orbitRel.Quotient GStar (Pts × Pts)) := Fintype.ofFinite _

theorem mk_symm
    (x y : Pts) :
    (Quotient.mk _ (x, y) : orbitRel.Quotient GStar (Pts × Pts)) = Quotient.mk _ (y, x) :=
  (mk_eq_mk_iff x y y x).2 (relIdx_comm x y)

@[expose] def orbIdx :
    orbitRel.Quotient GStar (Pts × Pts) → Fin 5 :=
  Quotient.lift (fun q : Pts × Pts => relIdx q.1 q.2) fun a b h =>
    ((mk_eq_mk_iff a.1 a.2 b.1 b.2).1 (Quotient.sound h))

theorem orbIdx_mk
    (x y : Pts) :
    orbIdx (Quotient.mk _ (x, y) : orbitRel.Quotient GStar (Pts × Pts)) = relIdx x y := rfl

theorem exists_relIdx_eq
    (i : Fin 5) : ∃ y : Pts, relIdx basePt y = i := by
  have h := card_relIdx i basePt
  have hpos : 0 < (Finset.univ.filter fun y : Pts => relIdx basePt y = i).card := by
    rw [h]
    fin_cases i <;> decide
  obtain ⟨y, hy⟩ := Finset.card_pos.1 hpos
  exact ⟨y, (Finset.mem_filter.1 hy).2⟩

theorem orbIdx_bijective :
    Function.Bijective orbIdx := by
  refine ⟨fun O O' h => ?_, fun i => ?_⟩
  · induction O using Quotient.inductionOn with | h a => ?_
    induction O' using Quotient.inductionOn with | h b => ?_
    exact (mk_eq_mk_iff a.1 a.2 b.1 b.2).2 h
  · obtain ⟨y, hy⟩ := exists_relIdx_eq i
    exact ⟨Quotient.mk _ (basePt, y), hy⟩

theorem orbitalMatrix_eq
    (O : orbitRel.Quotient GStar (Pts × Pts)) :
    orbitalMatrix O = orbA (orbIdx O) := by
  induction O using Quotient.inductionOn with
  | h a => exact orbitalMatrix_eq_orbA

theorem orbitalValency_eq_orbK
    (O : orbitRel.Quotient GStar (Pts × Pts)) (x : Pts) :
    orbitalValency O x = orbK (orbIdx O) := by
  classical
  have h := sum_orbitalMatrix_row O x
  rw [orbitalMatrix_eq] at h
  simp only [orbA_apply] at h
  rw [Finset.sum_boole] at h
  rw [← card_relIdx (orbIdx O) x]
  exact_mod_cast h.symm

instance :
    Nonempty Pts := ⟨basePt⟩

theorem posSemidef_orbP
    (r : Fin 5) : (∑ i, ((orbP r i : ℝ) / orbK i) • orbA i).PosSemidef := by
  have key := (symmetric_orbital_positive_spectral_combinations (K := GStar) (Ω := Pts)
    mk_symm).2.2.2 (fun O => (orbP r (orbIdx O) : ℝ)) basePt
    ⟨sphVec r, sphVec_ne_zero r, fun O => by
      rw [orbitalMatrix_eq]
      exact orbA_mulVec_sphVec r (orbIdx O)⟩
  have hsum : (∑ O, ((orbP r (orbIdx O) : ℝ) / orbitalValency O basePt) • orbitalMatrix O) =
      ∑ i, ((orbP r i : ℝ) / orbK i) • orbA i := by
    refine Fintype.sum_bijective orbIdx orbIdx_bijective _ _ fun O => ?_
    rw [orbitalMatrix_eq, orbitalValency_eq_orbK]
  rw [← hsum]
  exact key.1

theorem standard_F4_point_orbital_algebra_spectrum :
    (∀ x y x' y' : Pts,
      (Quotient.mk _ (x, y) : orbitRel.Quotient GStar (Pts × Pts)) = Quotient.mk _ (x', y') ↔
        relIdx x y = relIdx x' y') ∧
    (∀ i : Fin 5, ∃ x y : Pts, relIdx x y = i) ∧
    Nat.card (orbitRel.Quotient GStar (Pts × Pts)) = 5 ∧
    (∀ x y : Pts, relIdx x y = 0 ↔ x = y) ∧
    orbK = ![1, 1782, 44352, 1824768, 2097152] ∧
    (∀ (i : Fin 5) (x : Pts), (Finset.univ.filter fun y : Pts => relIdx x y = i).card = orbK i) ∧
    (∀ x y : Pts,
      (Quotient.mk _ (x, y) : orbitRel.Quotient GStar (Pts × Pts)) = Quotient.mk _ (y, x)) ∧
    (∀ x y : Pts, orbitalMatrix (Quotient.mk _ (x, y) : orbitRel.Quotient GStar (Pts × Pts)) =
      orbA (relIdx x y)) ∧
    orbA 0 = (by classical exact 1) ∧
    (∀ j : Fin 5, orbA 1 * orbA j = ∑ i, (orbMat i j : ℝ) • orbA i) ∧
    (∀ k j : Fin 5, orbA k * orbA j = ∑ i, (orbM k i j : ℝ) • orbA i) ∧
    (∀ r : Fin 5, ∃ v : Pts → ℝ, v ≠ 0 ∧ ∀ i, orbA i *ᵥ v = (orbP r i : ℝ) • v) ∧
    (∀ (p : Fin 5 → ℝ) (v : Pts → ℝ), v ≠ 0 → (∀ i, orbA i *ᵥ v = p i • v) →
      ∃ r : Fin 5, ∀ i, p i = orbP r i) ∧
    ∀ r : Fin 5, (∑ i, ((orbP r i : ℝ) / orbK i) • orbA i).PosSemidef := by
  refine ⟨mk_eq_mk_iff, fun i => ?_, ?_, relIdx_eq_zero_iff, rfl, card_relIdx, mk_symm,
    fun x y => orbitalMatrix_eq_orbA, orbA_zero, fun j => ?_, orbA_mul,
    fun r => ⟨sphVec r, sphVec_ne_zero r, fun i => orbA_mulVec_sphVec r i⟩,
    fun p v hv h => eq_orbP_of_eigen hv h, posSemidef_orbP⟩
  · obtain ⟨y, hy⟩ := exists_relIdx_eq i
    exact ⟨basePt, y, hy⟩
  · rw [Nat.card_congr (Equiv.ofBijective orbIdx orbIdx_bijective), Nat.card_eq_fintype_card,
      Fintype.card_fin]
  · rw [orbA_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [orbM_one]

end CFSG.Monster.B.E6.StdF4
