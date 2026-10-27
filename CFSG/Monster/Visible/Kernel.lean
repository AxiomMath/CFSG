module

public import CFSG.Monster.Visible.Action
import CFSG.Monster.Spin.OperatorBasis

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel Matrix

@[expose] def commForm : (C × Cocode) →ₗ[ZMod 2] Module.Dual (ZMod 2) (C × Cocode) :=
  LinearMap.mk₂ (ZMod 2) (fun w v => pair v.1 w.2 + pair w.1 v.2)
    (fun w w' v => by
      simp only [Prod.fst_add, Prod.snd_add, map_add, pair_add_left]
      ring)
    (fun c w v => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, pair_smul_left, smul_eq_mul]
      ring)
    (fun w v v' => by
      simp only [Prod.fst_add, Prod.snd_add, map_add, pair_add_left]
      ring)
    (fun c w v => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, pair_smul_left, smul_eq_mul]
      ring)

theorem commForm_apply (w v : C × Cocode) : commForm w v = pair v.1 w.2 + pair w.1 v.2 := rfl

theorem commForm_injective : Function.Injective commForm := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have h1 : ∀ v : C × Cocode, pair v.1 w.2 + pair w.1 v.2 = 0 := fun v =>
    LinearMap.congr_fun hw v
  have h2 : w.2 = 0 := eq_zero_of_forall_pair fun a => by simpa using h1 (a, 0)
  have h3 : w.1 = 0 := eq_zero_of_forall_pair_left fun δ => by simpa using h1 (0, δ)
  exact Prod.ext h3 h2

theorem commForm_surjective : Function.Surjective commForm :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).1 commForm_injective

private theorem two_eq_zero_zmod2 : (2 : ZMod 2) = 0 := rfl

theorem spinCoord_eq_mul (x : SpinCoord) : x = ⟨x.s, 0, 0⟩ * ⟨0, x.a, x.δ⟩ := by
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [SpinCoord.mul_s, pair_zero_right, add_zero]
  · simp only [SpinCoord.mul_a, zero_add]
  · simp only [SpinCoord.mul_δ, zero_add]

theorem conj_spinCoord (b : C) (ε : Cocode) (x : SpinCoord) :
    (⟨0, b, ε⟩ : SpinCoord)⁻¹ * x * ⟨0, b, ε⟩ = ⟨x.s + pair x.a ε + pair b x.δ, x.a, x.δ⟩ := by
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [SpinCoord.mul_s, SpinCoord.inv_s, SpinCoord.mul_δ, SpinCoord.inv_δ,
      pair_add_right]
    linear_combination (pair b ε) * two_eq_zero_zmod2
  · simp only [SpinCoord.mul_a, SpinCoord.inv_a]
    rw [add_right_comm, add_self_C', zero_add]
  · simp only [SpinCoord.mul_δ, SpinCoord.inv_δ]
    rw [add_right_comm, add_self_cocode, zero_add]

theorem exists_conj_of_fix (F : SpinCoord → SpinCoord) (hmul : ∀ x y, F (x * y) = F x * F y)
    (hfix : ∀ x, (F x).a = x.a ∧ (F x).δ = x.δ) (hz : F SpinCoord.z = SpinCoord.z) :
    ∃ y : SpinCoord, ∀ x, F x = y⁻¹ * x * y := by
  have hf : ∀ x y, (F (x * y)).s + (x * y).s = ((F x).s + x.s) + ((F y).s + y.s) := by
    intro x y
    rw [hmul, SpinCoord.mul_s, SpinCoord.mul_s, (hfix y).1, (hfix x).2]
    linear_combination (pair y.a x.δ) * two_eq_zero_zmod2
  have h1 : F 1 = 1 := by
    have h := hmul 1 1
    rw [one_mul] at h
    exact mul_eq_left.1 h.symm
  have hc : ∀ k : ZMod 2, (F ⟨k, 0, 0⟩).s + k = 0 := by
    intro k
    have hk : ∀ k : ZMod 2, k = 0 ∨ k = 1 := by decide
    rcases hk k with rfl | rfl
    · have e : (⟨0, 0, 0⟩ : SpinCoord) = 1 := rfl
      rw [e, h1]
      rfl
    · have e : (⟨1, 0, 0⟩ : SpinCoord) = SpinCoord.z := rfl
      rw [e, hz]
      rfl
  have hsplit : ∀ x, (F x).s + x.s = (F ⟨0, x.a, x.δ⟩).s + 0 := by
    intro x
    have h := hf ⟨x.s, 0, 0⟩ ⟨0, x.a, x.δ⟩
    rw [← spinCoord_eq_mul x] at h
    rw [h]
    have h' := hc x.s
    linear_combination h'
  let L : C × Cocode → ZMod 2 := fun v => (F ⟨0, v.1, v.2⟩).s + 0
  have hLadd : ∀ v w, L (v + w) = L v + L w := by
    intro v w
    have e : (⟨0, v.1, v.2⟩ : SpinCoord) * ⟨0, w.1, w.2⟩ =
        ⟨pair w.1 v.2, (v + w).1, (v + w).2⟩ := by
      refine SpinCoord.ext ?_ rfl rfl
      simp only [SpinCoord.mul_s, zero_add]
    have h := hf ⟨0, v.1, v.2⟩ ⟨0, w.1, w.2⟩
    rw [e, hsplit] at h
    exact h
  let Lin : C × Cocode →ₗ[ZMod 2] ZMod 2 :=
    AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' L hLadd)
  obtain ⟨w, hw⟩ := commForm_surjective Lin
  refine ⟨⟨0, w.1, w.2⟩, fun x => ?_⟩
  rw [conj_spinCoord]
  have hs : (F x).s + x.s = pair x.a w.2 + pair w.1 x.δ :=
    (hsplit x).trans (LinearMap.congr_fun hw (x.a, x.δ)).symm
  refine SpinCoord.ext ?_ (hfix x).1 (hfix x).2
  show (F x).s = x.s + pair x.a w.2 + pair w.1 x.δ
  linear_combination hs - x.s * two_eq_zero_zmod2

theorem mem_Q_of_conj_eq {s : GL SpinIdx ℚ} (hs : IsDyadicSpinNormalizer s) (q : Q)
    (h : ∀ r : Q, s⁻¹ * (r : GL SpinIdx ℚ) * s = (q : GL SpinIdx ℚ)⁻¹ * r * q) : s ∈ Q := by
  have hcomm : ∀ g ∈ Q, (g : Matrix SpinIdx SpinIdx ℚ) *
      ((s * (q : GL SpinIdx ℚ)⁻¹ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      ((s * (q : GL SpinIdx ℚ)⁻¹ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) * g := by
    intro g hg
    have h1 : s⁻¹ * g * s = (q : GL SpinIdx ℚ)⁻¹ * g * q := h ⟨g, hg⟩
    have h2 : g * (s * (q : GL SpinIdx ℚ)⁻¹) = s * (q : GL SpinIdx ℚ)⁻¹ * g :=
      calc g * (s * (q : GL SpinIdx ℚ)⁻¹) = s * (s⁻¹ * g * s) * (q : GL SpinIdx ℚ)⁻¹ := by group
        _ = s * ((q : GL SpinIdx ℚ)⁻¹ * g * q) * (q : GL SpinIdx ℚ)⁻¹ := by rw [h1]
        _ = s * (q : GL SpinIdx ℚ)⁻¹ * g := by group
    exact (Units.val_mul g _).symm.trans ((congrArg Units.val h2).trans (Units.val_mul _ g))
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_Q hcomm
  have ho := (hs.mul (isDyadicSpinNormalizer_of_mem_Q q.2).inv).mul_transpose
  rw [hc, Matrix.scalar_apply, diagonal_transpose, diagonal_mul_diagonal] at ho
  have hcc : c * c = 1 := by
    have h1 := congrFun (congrFun ho 0) 0
    rw [diagonal_apply_eq, one_apply_eq] at h1
    exact h1
  rcases mul_self_eq_one_iff.1 hcc with h1 | h1
  · have hM : s * (q : GL SpinIdx ℚ)⁻¹ = 1 :=
      Units.ext (hc.trans (by rw [h1, map_one]; exact Units.val_one.symm))
    rw [mul_inv_eq_one.1 hM]
    exact q.2
  · have hM : s * (q : GL SpinIdx ℚ)⁻¹ = zU :=
      Units.ext (hc.trans (by rw [h1, map_neg, map_one]; exact coe_zU.symm))
    rw [mul_inv_eq_iff_eq_mul.1 hM]
    exact Q.mul_mem zU_mem_Q q.2

theorem coordOf_spinEquiv (x : SpinCoord) : coordOf (spinEquiv x) = (x.a, x.δ) := by
  rw [coordOf, MulEquiv.symm_apply_apply]

theorem conjQ_eq_conj (p : Pvis) (y : SpinCoord)
    (hy : ∀ x, spinEquiv.symm (conjQ p (spinEquiv x)) = y⁻¹ * x * y) (r : Q) :
    conjQ p r = (spinEquiv y)⁻¹ * r * spinEquiv y := by
  have e1 : spinEquiv (spinEquiv.symm r) = r := spinEquiv.apply_symm_apply r
  have e4 : spinEquiv.symm (conjQ p r) = y⁻¹ * spinEquiv.symm r * y :=
    (congrArg (fun t => spinEquiv.symm (conjQ p t)) e1).symm.trans (hy (spinEquiv.symm r))
  calc conjQ p r = spinEquiv (spinEquiv.symm (conjQ p r)) :=
        (spinEquiv.apply_symm_apply _).symm
    _ = spinEquiv (y⁻¹ * spinEquiv.symm r * y) := congrArg spinEquiv e4
    _ = spinEquiv y⁻¹ * spinEquiv (spinEquiv.symm r) * spinEquiv y :=
        (map_mul spinEquiv (y⁻¹ * spinEquiv.symm r) y).trans
          (congrArg (· * spinEquiv y) (map_mul spinEquiv y⁻¹ (spinEquiv.symm r)))
    _ = (spinEquiv y)⁻¹ * r * spinEquiv y :=
        congrArg₂ (fun a b => a * b * spinEquiv y) (map_inv spinEquiv y) e1

theorem mem_Q_of_snd_eq_one (p : Pvis) (hp : p.1.2 = 1) : p.1.1 ∈ Q := by
  have hcoord : ∀ r : Q, coordOf (conjQ p r) = coordOf r := fun r => by
    have h : Multiplicative.toAdd (phi (QuotientGroup.mk (conjQ p r))) =
        Multiplicative.toAdd (phi (QuotientGroup.mk r)) :=
      (phi_conjQ p r).trans ((LinearMap.congr_fun (congrArg modTwoEnd hp) _).trans
        (LinearMap.congr_fun modTwoEnd_one _))
    exact phi0_injective ((toAdd_phi_mk _).symm.trans (h.trans (toAdd_phi_mk r)))
  have hmul : ∀ x y : SpinCoord, spinEquiv.symm (conjQ p (spinEquiv (x * y))) =
      spinEquiv.symm (conjQ p (spinEquiv x)) * spinEquiv.symm (conjQ p (spinEquiv y)) :=
    fun x y => (congrArg (fun t => spinEquiv.symm (conjQ p t)) (map_mul spinEquiv x y)).trans
      ((congrArg spinEquiv.symm (map_mul (conjQ p) (spinEquiv x) (spinEquiv y))).trans
        (map_mul spinEquiv.symm _ _))
  have hfix : ∀ x : SpinCoord, (spinEquiv.symm (conjQ p (spinEquiv x))).a = x.a ∧
      (spinEquiv.symm (conjQ p (spinEquiv x))).δ = x.δ := fun x => by
    have h := (hcoord (spinEquiv x)).trans (coordOf_spinEquiv x)
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hz : spinEquiv.symm (conjQ p (spinEquiv SpinCoord.z)) = SpinCoord.z :=
    (congrArg spinEquiv.symm (conjQ_zQ p)).trans (spinEquiv.symm_apply_apply SpinCoord.z)
  obtain ⟨y, hy⟩ := exists_conj_of_fix (fun x => spinEquiv.symm (conjQ p (spinEquiv x)))
    hmul hfix hz
  exact mem_Q_of_conj_eq (isDyadicSpinNormalizer p) (spinEquiv y) fun r =>
    congrArg Subtype.val (conjQ_eq_conj p y hy r)

@[expose] def piPair : Pvis →* latticeO ⧸ Subgroup.zpowers negOneO :=
  (QuotientGroup.mk' _).comp ((MonoidHom.snd _ _).comp Pvis.subtype)

theorem piPair_apply (p : Pvis) : piPair p = QuotientGroup.mk p.1.2 := rfl

theorem ker_thetaGvis_le_ker_piPair : thetaGvis.ker ≤ piPair.ker := by
  rw [ker_thetaGvis, Subgroup.zpowers_le, MonoidHom.mem_ker, piPair_apply]
  exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers negOneO)

@[expose] def piOp : (Gvis)ᵐᵒᵖ →* latticeO ⧸ Subgroup.zpowers negOneO :=
  thetaGvis.liftOfSurjective thetaGvis_surjective ⟨piPair, ker_thetaGvis_le_ker_piPair⟩

theorem piOp_thetaGvis (p : Pvis) : piOp (thetaGvis p) = QuotientGroup.mk p.1.2 :=
  thetaGvis.liftOfRightInverse_comp_apply _ _ _ p

@[expose] def piVis : Gvis →* (latticeO ⧸ Subgroup.zpowers negOneO)ᵐᵒᵖ where
  toFun f := MulOpposite.op (piOp (MulOpposite.op f))
  map_one' := congrArg MulOpposite.op (map_one piOp)
  map_mul' f f' :=
    congrArg MulOpposite.op (map_mul piOp (MulOpposite.op f') (MulOpposite.op f))

theorem piVis_thetaEquiv (p : Pvis) :
    piVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ = MulOpposite.op (QuotientGroup.mk p.1.2) :=
  congrArg MulOpposite.op (piOp_thetaGvis p)

theorem mk_eq_of_thetaEquiv_eq {p q : Pvis} (h : thetaEquiv p = thetaEquiv q) :
    (QuotientGroup.mk p.1.2 : latticeO ⧸ Subgroup.zpowers negOneO) = QuotientGroup.mk q.1.2 := by
  have h1 : piVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ =
      piVis ⟨thetaEquiv q, thetaEquiv_mem_Gvis q⟩ := congrArg piVis (Subtype.ext h)
  exact MulOpposite.op_injective ((piVis_thetaEquiv p).symm.trans (h1.trans (piVis_thetaEquiv q)))

theorem mem_rhoQ_of_piVis_eq_one {f : Gvis} (hf : piVis f = 1) :
    (f : SpaceB ≃ₗ[ℚ] SpaceB) ∈ rhoQ := by
  obtain ⟨p, hp⟩ := mem_Gvis.1 f.2
  have hfp : f = ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ := Subtype.ext hp.symm
  have hmk : (QuotientGroup.mk p.1.2 : latticeO ⧸ Subgroup.zpowers negOneO) = 1 :=
    MulOpposite.op_injective ((piVis_thetaEquiv p).symm.trans ((congrArg piVis hfp).symm.trans hf))
  have hmem : p.1.2 ∈ Subgroup.zpowers negOneO := (QuotientGroup.eq_one_iff _).1 hmk
  rw [zpowers_negOneO_eq_ker, mem_ker_modTwoHom_iff] at hmem
  obtain ⟨p', hp'1, hp'θ⟩ : ∃ p' : Pvis, p'.1.2 = 1 ∧ thetaEquiv p' = thetaEquiv p := by
    rcases hmem with h | h
    · exact ⟨p, mat_injective (h.trans mat_one.symm), rfl⟩
    · refine ⟨p * negPair, mat_injective ?_, thetaEquiv_mul_negPair p⟩
      show mat (p.1.2 * negOneO) = mat 1
      rw [mat_mul, h, mat_negOneO, mat_one, neg_one_mul, neg_neg]
  have hs := mem_Q_of_snd_eq_one p' hp'1
  refine mem_rhoQ.2 ⟨⟨p'.1.1, hs⟩, ?_⟩
  have hpair : rhoPair ⟨p'.1.1, hs⟩ = p' := Subtype.ext (Prod.ext rfl hp'1.symm)
  exact (congrArg thetaEquiv hpair).trans (hp'θ.trans hp)

theorem ker_piVis : piVis.ker = rhoQ.subgroupOf Gvis := by
  ext f
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  refine ⟨mem_rhoQ_of_piVis_eq_one, fun hf => ?_⟩
  obtain ⟨r, hr⟩ := mem_rhoQ.1 hf
  have hfr : f = ⟨thetaEquiv (rhoPair r), thetaEquiv_mem_Gvis _⟩ := Subtype.ext hr.symm
  rw [hfr, piVis_thetaEquiv]
  show MulOpposite.op (QuotientGroup.mk (1 : latticeO)) = 1
  rw [QuotientGroup.mk_one, MulOpposite.op_one]

instance normal_rhoQ_subgroupOf : (rhoQ.subgroupOf Gvis).Normal :=
  ker_piVis ▸ piVis.normal_ker

@[expose] def quotEquivRange : Gvis ⧸ rhoQ.subgroupOf Gvis ≃* piVis.range :=
  (QuotientGroup.quotientMulEquivOfEq ker_piVis.symm).trans
    (QuotientGroup.quotientKerEquivRange piVis)

theorem quotEquivRange_mk (f : Gvis) :
    (quotEquivRange (QuotientGroup.mk f) : (latticeO ⧸ Subgroup.zpowers negOneO)ᵐᵒᵖ) =
      piVis f := rfl

theorem mem_unop_range_piVis {x : latticeO ⧸ Subgroup.zpowers negOneO} :
    x ∈ piVis.range.unop ↔ ∃ p : Pvis, QuotientGroup.mk p.1.2 = x := by
  rw [Subgroup.mem_unop, MonoidHom.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨p, hp⟩ := mem_Gvis.1 f.2
    refine ⟨p, MulOpposite.op_injective ?_⟩
    exact (piVis_thetaEquiv p).symm.trans
      ((congrArg piVis (Subtype.ext hp : (⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ : Gvis) = f)).trans
        hf)
  · rintro ⟨p, rfl⟩
    exact ⟨⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩, piVis_thetaEquiv p⟩

theorem piVis_eq_one_iff (f : Gvis) : piVis f = 1 ↔ ∃ r : Q, rhoEquiv r = f := by
  rw [← MonoidHom.mem_ker, ker_piVis, Subgroup.mem_subgroupOf, mem_rhoQ]

theorem piOp_op (f : Gvis) : piOp (MulOpposite.op f) = (piVis f).unop := rfl

theorem ker_piOp : piOp.ker = (rhoQ.subgroupOf Gvis).op := by
  ext f
  rw [MonoidHom.mem_ker, Subgroup.mem_op, ← ker_piVis, MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg MulOpposite.op h
  · intro h
    exact congrArg MulOpposite.unop h

instance normal_rhoQ_subgroupOf_op : (rhoQ.subgroupOf Gvis).op.Normal :=
  ker_piOp ▸ piOp.normal_ker

theorem range_piOp : piOp.range = piVis.range.unop := by
  ext x
  rw [MonoidHom.mem_range, Subgroup.mem_unop, MonoidHom.mem_range]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.unop, rfl⟩
  · rintro ⟨f, hf⟩
    exact ⟨MulOpposite.op f, congrArg MulOpposite.unop hf⟩

@[expose] def quotEquivRangeOp : (Gvis)ᵐᵒᵖ ⧸ (rhoQ.subgroupOf Gvis).op ≃* piOp.range :=
  (QuotientGroup.quotientMulEquivOfEq ker_piOp.symm).trans
    (QuotientGroup.quotientKerEquivRange piOp)

theorem quotEquivRangeOp_mk (p : Pvis) :
    (quotEquivRangeOp (QuotientGroup.mk (thetaGvis p)) : latticeO ⧸ Subgroup.zpowers negOneO) =
      QuotientGroup.mk p.1.2 :=
  piOp_thetaGvis p

theorem visible_lattice_quotient_kernel :
    (∀ g : GL (Fin 24) ℚ, g ∈ latticeO ↔
      (g : Matrix (Fin 24) (Fin 24) ℚ) ∈ orthogonalGroup (Fin 24) ℚ ∧
        (fun x => x ᵥ* (g : Matrix (Fin 24) (Fin 24) ℚ)) '' latticeQ = latticeQ) ∧
    mat negOneO = -1 ∧
    (∀ p q : Pvis, thetaEquiv p = thetaEquiv q →
      (QuotientGroup.mk p.1.2 : latticeO ⧸ Subgroup.zpowers negOneO) = QuotientGroup.mk q.1.2) ∧
    (∀ p : Pvis, piVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ =
      MulOpposite.op (QuotientGroup.mk p.1.2)) ∧
    (∀ p : Pvis, piOp (thetaGvis p) = QuotientGroup.mk p.1.2) ∧
    piVis.ker = rhoQ.subgroupOf Gvis ∧
    (∀ f : Gvis, piVis f = 1 ↔ ∃ r : Q, rhoEquiv r = f) ∧
    piOp.ker = (rhoQ.subgroupOf Gvis).op ∧
    (rhoQ.subgroupOf Gvis).Normal ∧
    (∀ f : Gvis, (quotEquivRange (QuotientGroup.mk f) :
      (latticeO ⧸ Subgroup.zpowers negOneO)ᵐᵒᵖ) = piVis f) ∧
    (∀ p : Pvis, (quotEquivRangeOp (QuotientGroup.mk (thetaGvis p)) :
      latticeO ⧸ Subgroup.zpowers negOneO) = QuotientGroup.mk p.1.2) ∧
    piOp.range = piVis.range.unop ∧
    (∀ x : latticeO ⧸ Subgroup.zpowers negOneO, x ∈ piVis.range.unop ↔
      ∃ p : Pvis, QuotientGroup.mk p.1.2 = x) :=
  ⟨fun _ => Iff.rfl, mat_negOneO, fun _ _ h => mk_eq_of_thetaEquiv_eq h, piVis_thetaEquiv,
    piOp_thetaGvis, ker_piVis, piVis_eq_one_iff, ker_piOp, normal_rhoQ_subgroupOf,
    quotEquivRange_mk, quotEquivRangeOp_mk, range_piOp, fun _ => mem_unop_range_piVis⟩

end CFSG.Monster.Visible
