module

public import CFSG.Quasithin.Background.SimsF5Ai
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Extension
public import CFSG.Quasithin.Background.SimsF5Main

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix

local notation:max "mat(" g ")" => ((g : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3))

local instance inv_two : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)

theorem inv_mem_commSp_iff (g : GL6) (w : V6) :
    w ∈ commSp g ↔ ∃ v : V6, mat(g) *ᵥ v - v = w := by
  simp only [commSp, LinearMap.mem_range, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec]

theorem inv_mulVec_mulVec {g : GL6} (hgg : g * g = 1) (v : V6) :
    mat(g) *ᵥ (mat(g) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, hgg, Units.val_one, Matrix.one_mulVec]

theorem inv_neg_of_mem_commSp {w : GL6} (hww : w * w = 1) {a : V6} (ha : a ∈ commSp w) :
    mat(w) *ᵥ a = -a := by
  obtain ⟨v, rfl⟩ := (inv_mem_commSp_iff w a).1 ha
  rw [Matrix.mulVec_sub, inv_mulVec_mulVec hww]
  exact (neg_sub _ _).symm

theorem inv_bil_sub_left (u v c : V6) : bil (u - v) c = bil u c - bil v c := by
  rw [bil_comm, bil_sub_right, bil_comm c u, bil_comm c v]

theorem inv_bil_neg_right (u v : V6) : bil u (-v) = -bil u v := by
  have h := bil_smul_right (-1 : ZMod 3) u v
  rwa [neg_one_smul, neg_one_mul] at h

theorem inv_bil_commSp_fix {w : GL6} (hw : w ∈ OVq) {a c : V6} (ha : a ∈ commSp w)
    (hc : mat(w) *ᵥ c = c) : bil a c = 0 := by
  obtain ⟨v, rfl⟩ := (inv_mem_commSp_iff w a).1 ha
  have h := bil_mulVec_of_mem_OVq hw v c
  rw [hc] at h
  rw [inv_bil_sub_left, h, sub_self]

theorem inv_decomp {w : GL6} (hww : w * w = 1) (v : V6) :
    v = (mat(w) *ᵥ v - v) + (-(v + mat(w) *ᵥ v)) ∧
      mat(w) *ᵥ (-(v + mat(w) *ᵥ v)) = -(v + mat(w) *ᵥ v) := by
  refine ⟨?_, ?_⟩
  · funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
    exact (by decide : ∀ a b : ZMod 3, a = (b - a) + -(a + b)) _ _
  · rw [Matrix.mulVec_neg, Matrix.mulVec_add, inv_mulVec_mulVec hww, add_comm]

theorem inv_bil_nondeg {a : V6} (h : ∀ v, bil a v = 0) : a = 0 :=
  QV_nondeg.1 a fun y => by rw [QuadraticMap.polarBilin_apply_apply, polar_QV]; exact h y

theorem inv_isNondegSub {w : GL6} (hw : w ∈ OVq) (hww : w * w = 1) : IsNondegSub (commSp w) := by
  intro a ha hperp
  apply inv_bil_nondeg
  intro v
  obtain ⟨hv, hc⟩ := inv_decomp hww v
  have h1 : mat(w) *ᵥ v - v ∈ commSp w := (inv_mem_commSp_iff w _).2 ⟨v, rfl⟩
  have h2 := inv_bil_commSp_fix hw ha hc
  have h3 := hperp _ h1
  have : bil a v = bil a ((mat(w) *ᵥ v - v) + (-(v + mat(w) *ᵥ v))) := congrArg (bil a) hv
  rw [this, bil_add_right, h3, h2, add_zero]

theorem inv_eq_of_commSp_eq {w w' : GL6} (hw : w ∈ OVq) (hw' : w' ∈ OVq) (hww : w * w = 1)
    (hww' : w' * w' = 1) (h : commSp w = commSp w') : w = w' := by
  have hnd := inv_isNondegSub hw hww
  apply Units.ext
  apply mat_eq_of_mulVec_eq
  intro v
  obtain ⟨hv, hc⟩ := inv_decomp hww v
  set a := mat(w) *ᵥ v - v with ha_def
  set c := -(v + mat(w) *ᵥ v) with hc_def
  have ha : a ∈ commSp w := (inv_mem_commSp_iff w _).2 ⟨v, rfl⟩
  have ha' : a ∈ commSp w' := h ▸ ha
  have hc' : mat(w') *ᵥ c = c := by
    have hd : mat(w') *ᵥ c - c ∈ commSp w := h ▸ (inv_mem_commSp_iff w' _).2 ⟨c, rfl⟩
    have h0 : mat(w') *ᵥ c - c = 0 := by
      apply hnd _ hd
      intro a'' ha''
      have ha''' : a'' ∈ commSp w' := h ▸ ha''
      rw [inv_bil_sub_left]
      have e1 := inv_bil_commSp_fix hw ha'' hc
      have e2 := bil_mulVec_of_mem_OVq hw' (mat(w') *ᵥ c) a''
      rw [inv_mulVec_mulVec hww', inv_neg_of_mem_commSp hww' ha''', inv_bil_neg_right] at e2
      rw [bil_comm] at e1
      have e3 : bil (mat(w') *ᵥ c) a'' = 0 := by rw [← e2, e1, neg_zero]
      rw [e3, e1, sub_zero]
    exact sub_eq_zero.1 h0
  rw [hv]
  rw [Matrix.mulVec_add, Matrix.mulVec_add, inv_neg_of_mem_commSp hww ha,
    inv_neg_of_mem_commSp hww' ha', hc, hc']

theorem inv_mem_commSp_conj (g w : GL6) (u : V6) :
    u ∈ commSp (g * w * g⁻¹) ↔ mat(g⁻¹) *ᵥ u ∈ commSp w := by
  have hgi : mat(g⁻¹) * mat(g) = 1 := Units.inv_mul g
  have hig : mat(g) * mat(g⁻¹) = 1 := Units.mul_inv g
  rw [inv_mem_commSp_iff, inv_mem_commSp_iff]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨mat(g⁻¹) *ᵥ v, ?_⟩
    rw [Matrix.mulVec_sub, Units.val_mul, Units.val_mul]
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hgi, Matrix.one_mul]
  · rintro ⟨v, hv⟩
    refine ⟨mat(g) *ᵥ v, ?_⟩
    have h2 : mat(g) *ᵥ (mat(g⁻¹) *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, hig, Matrix.one_mulVec]
    rw [← h2, ← hv, Matrix.mulVec_sub, Units.val_mul, Units.val_mul]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hgi, Matrix.mul_one]

theorem inv_bil_equiv (φ : V6 ≃ₗ[ZMod 3] V6) (hφ : ∀ v, qV (φ v) = qV v) (x y : V6) :
    bil (φ x) (φ y) = bil x y := by
  unfold bil
  rw [← map_add, hφ, hφ, hφ]

theorem inv_isNondegSub_map (φ : V6 ≃ₗ[ZMod 3] V6) (hφ : ∀ v, qV (φ v) = qV v) {W : Sub6}
    (h : IsNondegSub W) : IsNondegSub (W.map φ.toLinearMap) := by
  rintro _ ⟨a, ha, rfl⟩ hperp
  have : a = 0 := h a ha fun b hb => by
    rw [← inv_bil_equiv φ hφ]
    exact hperp _ ⟨b, hb, rfl⟩
  simp [this]

theorem inv_hasTS_map (φ : V6 ≃ₗ[ZMod 3] V6) (hφ : ∀ v, qV (φ v) = qV v) {W : Sub6}
    (h : ∃ U : Sub6, U ≤ W ∧ (∀ u ∈ U, qV u = 0) ∧
      2 * Module.finrank (ZMod 3) U = Module.finrank (ZMod 3) W) :
    ∃ U : Sub6, U ≤ W.map φ.toLinearMap ∧ (∀ u ∈ U, qV u = 0) ∧
      2 * Module.finrank (ZMod 3) U = Module.finrank (ZMod 3) (W.map φ.toLinearMap) := by
  obtain ⟨U, hUW, hU0, hdim⟩ := h
  refine ⟨U.map φ.toLinearMap, Submodule.map_mono hUW, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact (hφ u).trans (hU0 u hu)
  · rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]
    exact hdim

theorem inv_map_symm_map (φ : V6 ≃ₗ[ZMod 3] V6) (W : Sub6) :
    (W.map φ.toLinearMap).map φ.symm.toLinearMap = W := by
  ext x
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, exists_exists_and_eq_and,
    LinearEquiv.symm_apply_apply, exists_eq_right]

theorem inv_hasTS_map_iff (φ : V6 ≃ₗ[ZMod 3] V6) (hφ : ∀ v, qV (φ v) = qV v) {W : Sub6} :
    (∃ U : Sub6, U ≤ W.map φ.toLinearMap ∧ (∀ u ∈ U, qV u = 0) ∧
      2 * Module.finrank (ZMod 3) U = Module.finrank (ZMod 3) (W.map φ.toLinearMap)) ↔
    (∃ U : Sub6, U ≤ W ∧ (∀ u ∈ U, qV u = 0) ∧
      2 * Module.finrank (ZMod 3) U = Module.finrank (ZMod 3) W) := by
  refine ⟨fun h => ?_, inv_hasTS_map φ hφ⟩
  have hφ' : ∀ v, qV (φ.symm v) = qV v := fun v => by
    have := hφ (φ.symm v)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have := inv_hasTS_map φ.symm hφ' h
  rwa [inv_map_symm_map] at this

theorem inv_signPlus_map (φ : V6 ≃ₗ[ZMod 3] V6) (hφ : ∀ v, qV (φ v) = qV v) {W : Sub6}
    (h : SignPlus W) : SignPlus (W.map φ.toLinearMap) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨inv_isNondegSub_map φ hφ h1, ?_, inv_hasTS_map φ hφ h3⟩
  rwa [LinearEquiv.finrank_map_eq]

theorem inv_signMinus_map (φ : V6 ≃ₗ[ZMod 3] V6) (hφ : ∀ v, qV (φ v) = qV v) {W : Sub6}
    (h : SignMinus W) : SignMinus (W.map φ.toLinearMap) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨inv_isNondegSub_map φ hφ h1, ?_, fun h4 => h3 ((inv_hasTS_map_iff φ hφ).1 h4)⟩
  rwa [LinearEquiv.finrank_map_eq]

theorem inv_commSp_conj_eq (g w : GL6) :
    commSp (g * w * g⁻¹) = (commSp w).map
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 6) (ZMod 3) g).toLinearMap := by
  ext u
  rw [inv_mem_commSp_conj, Submodule.mem_map_equiv]
  have hig : mat(g) * mat(g⁻¹) = 1 := Units.mul_inv g
  have : (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 6) (ZMod 3) g).symm u =
      mat(g⁻¹) *ᵥ u := by
    rw [LinearEquiv.symm_apply_eq, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
      Matrix.mulVec_mulVec, hig, Matrix.one_mulVec]
  rw [this]

theorem inv_toLinEquiv_isometry {g : GL6} (hg : g ∈ OVq) (v : V6) :
    qV (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 6) (ZMod 3) g v) = qV v := by
  rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
  exact qV_mulVec_of_mem_OVq hg v

theorem inv_prod_refl_fix (l : List ReflVec) {c : V6} (hc : ∀ r ∈ l, bil c r.1 = 0) :
    mat((l.map reflOf).prod) *ᵥ c = c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, ← Matrix.mulVec_mulVec,
      ih fun r hr => hc r (List.mem_cons_of_mem _ hr)]
    exact refl6_mulVec_of_bil_eq_zero a.1 a.2 (hc a List.mem_cons_self)

theorem inv_prod_refl_neg (l : List ReflVec) (hl : l.Pairwise fun r s => bil r.1 s.1 = 0)
    {r : ReflVec} (hr : r ∈ l) : mat((l.map reflOf).prod) *ᵥ r.1 = -r.1 := by
  induction l with
  | nil => exact absurd hr (by simp)
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    rw [List.map_cons, List.prod_cons, Units.val_mul, ← Matrix.mulVec_mulVec]
    rcases List.mem_cons.1 hr with rfl | hrl
    · rw [inv_prod_refl_fix l fun s hs => hl.1 s hs]
      exact refl6_mulVec_self _ _
    · rw [ih hl.2 hrl, Matrix.mulVec_neg]
      have : bil r.1 a.1 = 0 := by rw [bil_comm]; exact hl.1 r hrl
      have h2 := refl6_mulVec_of_bil_eq_zero a.1 a.2 this
      simp only [reflOf]
      rw [h2]

theorem inv_prod_eq {w : GL6} (hw : w ∈ OVq) (hww : w * w = 1) {n : ℕ} (u : Fin n → V6)
    (hu : ∀ i, qV (u i) ≠ 0) (horth : ∀ i j, i ≠ j → bil (u i) (u j) = 0)
    (hmem : ∀ i, u i ∈ commSp w)
    (hspan : ∀ a ∈ commSp w, ∃ c : Fin n → ZMod 3, a = ∑ i, c i • u i) :
    ((List.ofFn fun i => (⟨u i, hu i⟩ : ReflVec)).map reflOf).prod = w := by
  set l : List ReflVec := List.ofFn fun i => (⟨u i, hu i⟩ : ReflVec) with hl
  have hpair : l.Pairwise fun r s => bil r.1 s.1 = 0 := by
    rw [hl, List.pairwise_ofFn]
    intro i j hij
    exact horth i j hij.ne
  have hneg : ∀ a ∈ commSp w, mat((l.map reflOf).prod) *ᵥ a = -a := by
    intro a ha
    obtain ⟨c, rfl⟩ := hspan a ha
    rw [Matrix.mulVec_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, inv_prod_refl_neg l hpair (r := ⟨u i, hu i⟩)
      (List.mem_ofFn.2 ⟨i, rfl⟩), smul_neg]
  have hfix : ∀ c, mat(w) *ᵥ c = c → mat((l.map reflOf).prod) *ᵥ c = c := by
    intro c hc
    refine inv_prod_refl_fix l fun r hr => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hr
    rw [bil_comm]
    exact inv_bil_commSp_fix hw (hmem i) hc
  apply Units.ext
  apply mat_eq_of_mulVec_eq
  intro v
  obtain ⟨hv, hc⟩ := inv_decomp hww v
  set a := mat(w) *ᵥ v - v with ha_def
  set c := -(v + mat(w) *ᵥ v) with hc_def
  have ha : a ∈ commSp w := (inv_mem_commSp_iff w _).2 ⟨v, rfl⟩
  rw [hv, Matrix.mulVec_add, Matrix.mulVec_add, hneg a ha, inv_neg_of_mem_commSp hww ha, hfix c hc,
    hc]

theorem inv_binary_equiv :
    (QuadraticMap.weightedSumSquares (ZMod 3) ![(-1 : ZMod 3), -1]).Equivalent
      (QuadraticMap.weightedSumSquares (ZMod 3) ![(1 : ZMod 3), 1]) := by
  refine ⟨{
    toFun := fun x => ![x 0 + x 1, x 0 - x 1]
    invFun := fun y => ![-(y 0 + y 1), -(y 0 - y 1)]
    map_add' := ?_
    map_smul' := ?_
    left_inv := ?_
    right_inv := ?_
    map_app' := ?_ }⟩
  · intro x y
    funext i
    fin_cases i <;> simp <;> ring
  · intro c x
    funext i
    fin_cases i <;> simp <;> ring
  · intro x
    revert x
    decide
  · intro y
    revert y
    decide
  · intro x
    simp only [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two]
    simp
    exact (by decide : ∀ a b : ZMod 3,
      (a + b) * (a + b) + (a - b) * (a - b) = -(a * a) + -(b * b)) _ _

theorem inv_equiv_one (n : ℕ) : ∀ (k : ℕ) (S : Finset (Fin n)), S.card = 2 * k →
    (QuadraticMap.weightedSumSquares (ZMod 3)
      (fun j => if j ∈ S then (-1 : ZMod 3) else 1)).Equivalent
      (QuadraticMap.weightedSumSquares (ZMod 3) (fun _ : Fin n => (1 : ZMod 3))) := by
  intro k
  induction k with
  | zero =>
    intro S hS
    have : S = ∅ := Finset.card_eq_zero.1 (by simpa using hS)
    subst this
    simp only [Finset.notMem_empty, if_false]
    exact QuadraticMap.Equivalent.refl _
  | succ k ih =>
    intro S hS
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < S.card)
    have hS1 : (S.erase i).card = 2 * k + 1 := by rw [Finset.card_erase_of_mem hi]; omega
    obtain ⟨j, hj⟩ := Finset.card_pos.1 (by omega : 0 < (S.erase i).card)
    have hij : j ≠ i := (Finset.mem_erase.1 hj).1
    have hjS : j ∈ S := (Finset.mem_erase.1 hj).2
    have hS2 : ((S.erase i).erase j).card = 2 * k := by
      rw [Finset.card_erase_of_mem hj]; omega
    refine QuadraticMap.Equivalent.trans ?_ (ih _ hS2)
    refine TauCeti.equivalent_weightedSumSquares_of_pair (i := i) (j := j) hij.symm ?_ ?_
    · have hi' : i ∉ (S.erase i).erase j := by simp
      have hj' : j ∉ (S.erase i).erase j := by simp
      simpa [hi, hjS, hi', hj'] using inv_binary_equiv
    · intro k hki hkj
      simp [Finset.mem_erase, hki, hkj]

theorem inv_assoc_two_mul (W : Sub6) (x y : W) :
    2 * QuadraticMap.associated (R := ZMod 3) (QV.restrict W) x y = bil (x : V6) (y : V6) := by
  rw [QuadraticMap.associated_apply]
  change 2 * (⅟(2 : ZMod 3) * ((QV.restrict W) (x + y) - (QV.restrict W) x - (QV.restrict W) y)) = _
  rw [← mul_assoc, mul_invOf_self, one_mul]
  simp only [QuadraticMap.restrict_apply, Submodule.coe_add, QV_apply, bil]

theorem inv_exists_orth_basis (W : Sub6) (hnd : IsNondegSub W) :
    ∃ b : Module.Basis (Fin (Module.finrank (ZMod 3) W)) (ZMod 3) W,
      (∀ i j, i ≠ j → bil (b i : V6) (b j : V6) = 0) ∧ (∀ i, qV (b i : V6) ≠ 0) ∧
      Nonempty ((QV.restrict W).IsometryEquiv
        (QuadraticMap.weightedSumSquares (ZMod 3) fun i => qV (b i : V6))) := by
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (QuadraticForm.associated_isSymm (ZMod 3) (QV.restrict W))
  refine ⟨b, ?_, ?_, ?_⟩
  · intro i j hij
    have := (LinearMap.isOrthoᵢ_def.1 hb) i j hij
    have h2 := inv_assoc_two_mul W (b i) (b j)
    rw [this, mul_zero] at h2
    exact h2.symm
  · have hsep : (QuadraticMap.associated (R := ZMod 3) (QV.restrict W)).SeparatingLeft := by
      intro x hx
      have : (x : V6) = 0 := hnd x x.2 fun y hy => by
        have h2 := inv_assoc_two_mul W x ⟨y, hy⟩
        rw [hx ⟨y, hy⟩, mul_zero] at h2
        exact h2.symm
      exact Subtype.ext this
    intro i h0
    refine hb.not_isOrtho_basis_self_of_separatingLeft hsep i ?_
    have h2 := inv_assoc_two_mul W (b i) (b i)
    rw [bil_self, h0, mul_zero] at h2
    exact (mul_eq_zero.1 h2).resolve_left (by decide)
  · have hw : (fun i => (QV.restrict W) (b i)) = fun i => qV (b i : V6) :=
      funext fun i => by rw [QuadraticMap.restrict_apply, QV_apply]
    exact ⟨(QuadraticForm.isometryEquivWeightedSumSquares (QV.restrict W) b hb).trans
      (QuadraticForm.weightedSumSquaresCongr hw)⟩

theorem inv_countP_ofFn : ∀ {n : ℕ} (u : Fin n → V6) (hu : ∀ i, qV (u i) ≠ 0),
    (List.ofFn fun i => (⟨u i, hu i⟩ : ReflVec)).countP (fun v => qV v.1 = -1) =
      (Finset.univ.filter fun i => qV (u i) = -1).card := by
  intro n
  induction n with
  | zero => intro u hu; simp
  | succ n ih =>
    intro u hu
    rw [List.ofFn_succ, List.countP_cons, ih (fun i => u i.succ) (fun i => hu i.succ),
      Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
    simp only [decide_eq_true_eq]
    omega

theorem inv_type {w : GL6} (hw : w ∈ MDot) (hww : w * w = 1) :
    Even (Module.finrank (ZMod 3) (commSp w)) ∧
      (QV.restrict (commSp w)).Equivalent
        (QuadraticMap.weightedSumSquares (ZMod 3)
          (fun _ : Fin (Module.finrank (ZMod 3) (commSp w)) => (1 : ZMod 3))) := by
  have hO : w ∈ OVq := MDot_le_OVq hw
  obtain ⟨b, horth, hne, ⟨iso⟩⟩ := inv_exists_orth_basis (commSp w) (inv_isNondegSub hO hww)
  have hspan : ∀ a ∈ commSp w, ∃ c : Fin (Module.finrank (ZMod 3) (commSp w)) → ZMod 3,
      a = ∑ i, c i • (b i : V6) := by
    intro a ha
    refine ⟨b.repr ⟨a, ha⟩, ?_⟩
    have := congrArg Subtype.val (b.sum_repr ⟨a, ha⟩)
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this.symm
  have hprod := inv_prod_eq hO hww (fun i => (b i : V6)) hne horth (fun i => (b i).2) hspan
  have hmem := (prod_refl_mem_MDot_iff
    (List.ofFn fun i => (⟨(b i : V6), hne i⟩ : ReflVec))).1 (by rw [hprod]; exact hw)
  rw [List.length_ofFn, inv_countP_ofFn (fun i => (b i : V6)) hne] at hmem
  refine ⟨hmem.1, ?_⟩
  obtain ⟨k, hk⟩ := hmem.2
  set S : Finset (Fin (Module.finrank (ZMod 3) (commSp w))) :=
    Finset.univ.filter fun i => qV (b i : V6) = -1 with hS_def
  have hS : S.card = 2 * k := by omega
  have hweights : (fun i => qV (b i : V6)) = fun j => if j ∈ S then (-1 : ZMod 3) else 1 := by
    funext j
    by_cases h : qV (b j : V6) = -1
    · simp [hS_def, h]
    · have h3 : ∀ a : ZMod 3, a ≠ 0 → a ≠ -1 → a = 1 := by decide
      have : qV (b j : V6) = 1 := h3 _ (hne j) h
      simp [hS_def, h, this]
  have e1 : (QV.restrict (commSp w)).Equivalent
      (QuadraticMap.weightedSumSquares (ZMod 3) fun j => if j ∈ S then (-1 : ZMod 3) else 1) := by
    rw [← hweights]
    exact ⟨iso⟩
  exact e1.trans (inv_equiv_one _ k S hS)

theorem inv_dim {w : GL6} (hw : w ∈ MDot) (hw1 : w ≠ 1) (hww : w * w = 1) :
    Module.finrank (ZMod 3) (commSp w) = 2 ∨ Module.finrank (ZMod 3) (commSp w) = 4 := by
  obtain ⟨hev, -⟩ := inv_type hw hww
  have hle : Module.finrank (ZMod 3) (commSp w) ≤ 6 := by
    have := Submodule.finrank_le (commSp w)
    rwa [Module.finrank_fin_fun] at this
  have h0 : Module.finrank (ZMod 3) (commSp w) ≠ 0 := by
    intro h
    rw [Submodule.finrank_eq_zero] at h
    apply hw1
    apply Units.ext
    apply mat_eq_of_mulVec_eq
    intro v
    have : mat(w) *ᵥ v - v ∈ commSp w := (inv_mem_commSp_iff w _).2 ⟨v, rfl⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at this
    rw [this, Units.val_one, Matrix.one_mulVec]
  have h6 : Module.finrank (ZMod 3) (commSp w) ≠ 6 := by
    intro h
    have htop : commSp w = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h, Module.finrank_fin_fun])
    have hm1 : w = -1 := by
      apply Units.ext
      apply mat_eq_of_mulVec_eq
      intro v
      rw [inv_neg_of_mem_commSp hww (htop ▸ Submodule.mem_top), Units.val_neg, Units.val_one,
        Matrix.neg_mulVec, Matrix.one_mulVec]
    exact neg_one_not_mem_MDot (hm1 ▸ hw)
  obtain ⟨r, hr⟩ := hev
  omega

theorem inv_equiv_of_dim_eq {w₁ w₂ : GL6} (h₁ : w₁ ∈ MDot) (h₂ : w₂ ∈ MDot) (hw₁ : w₁ * w₁ = 1)
    (hw₂ : w₂ * w₂ = 1)
    (hd : Module.finrank (ZMod 3) (commSp w₁) = Module.finrank (ZMod 3) (commSp w₂)) :
    (QV.restrict (commSp w₁)).Equivalent (QV.restrict (commSp w₂)) := by
  obtain ⟨-, e₁⟩ := inv_type h₁ hw₁
  obtain ⟨-, e₂⟩ := inv_type h₂ hw₂
  have key : ∀ {n m : ℕ}, n = m →
      (QuadraticMap.weightedSumSquares (ZMod 3) (fun _ : Fin n => (1 : ZMod 3))).Equivalent
        (QuadraticMap.weightedSumSquares (ZMod 3) (fun _ : Fin m => (1 : ZMod 3))) := by
    rintro n m rfl
    exact QuadraticMap.Equivalent.refl _
  exact e₁.trans ((key hd).trans e₂.symm)

theorem inv_conj_of_equiv {w₁ w₂ : GL6} (hO₁ : w₁ ∈ OVq) (hO₂ : w₂ ∈ OVq) (hw₁ : w₁ * w₁ = 1)
    (hw₂ : w₂ * w₂ = 1) (hnd : (QV.restrict (commSp w₁)).Nondegenerate)
    (f : (QV.restrict (commSp w₁)).IsometryEquiv (QV.restrict (commSp w₂))) :
    ∃ g ∈ OVq, g * w₁ * g⁻¹ = w₂ := by
  obtain ⟨e, he⟩ := QuadraticMap.IsometryEquiv.exists_extension f hnd
  set g : GL6 := (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 6) (ZMod 3)).symm
    e.toLinearEquiv with hg_def
  have hgv : ∀ v, mat(g) *ᵥ v = e v := fun v => by
    have h := MulEquiv.apply_symm_apply (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 6)
      (ZMod 3)) e.toLinearEquiv
    have h2 := congrArg (fun φ : V6 ≃ₗ[ZMod 3] V6 => φ v) h
    simpa [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, ← hg_def] using h2
  have hgO : g ∈ OVq := mem_OVq_iff_forall.2 fun v => by
    rw [hgv, ← QV_apply, ← QV_apply]
    exact e.map_app v
  have hgi : mat(g⁻¹) * mat(g) = 1 := Units.inv_mul g
  have hig : mat(g) * mat(g⁻¹) = 1 := Units.mul_inv g
  have hcs : commSp (g * w₁ * g⁻¹) = commSp w₂ := by
    ext u
    rw [inv_mem_commSp_conj]
    constructor
    · intro hu
      have h1 : u = e (mat(g⁻¹) *ᵥ u) := by
        rw [← hgv, Matrix.mulVec_mulVec, hig, Matrix.one_mulVec]
      rw [h1, he ⟨_, hu⟩]
      exact (f ⟨_, hu⟩).2
    · intro hu
      set x : commSp w₁ := f.symm ⟨u, hu⟩ with hxdef
      have hx : ((f x : commSp w₂) : V6) = u := by rw [hxdef, f.apply_symm_apply]
      have h2 : e (x : V6) = u := by rw [he, hx]
      have h3 : mat(g⁻¹) *ᵥ u = (x : V6) := by
        calc mat(g⁻¹) *ᵥ u = mat(g⁻¹) *ᵥ (mat(g) *ᵥ (x : V6)) := by rw [hgv, h2]
          _ = x := by rw [Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]
      rw [h3]
      exact x.2
  have hconjO : g * w₁ * g⁻¹ ∈ OVq := OVq.mul_mem (OVq.mul_mem hgO hO₁) (OVq.inv_mem hgO)
  have hconj2 : (g * w₁ * g⁻¹) * (g * w₁ * g⁻¹) = 1 := by
    calc (g * w₁ * g⁻¹) * (g * w₁ * g⁻¹) = g * (w₁ * w₁) * g⁻¹ := by group
      _ = 1 := by rw [hw₁]; group
  exact ⟨g, hgO, inv_eq_of_commSp_eq hconjO hO₂ hconj2 hw₂ hcs⟩

theorem inv_conj_of_dim_eq {w₁ w₂ : GL6} (h₁ : w₁ ∈ MDot) (h₂ : w₂ ∈ MDot) (hw₁ : w₁ * w₁ = 1)
    (hw₂ : w₂ * w₂ = 1)
    (hd : Module.finrank (ZMod 3) (commSp w₁) = Module.finrank (ZMod 3) (commSp w₂))
    (hP : ∀ g ∈ OVq, ∃ p ∈ OVq, p * w₁ = w₁ * p ∧ g * p ∈ MDot) :
    ∃ g ∈ MDot, g * w₁ * g⁻¹ = w₂ := by
  obtain ⟨f⟩ := inv_equiv_of_dim_eq h₁ h₂ hw₁ hw₂ hd
  have hnd : (QV.restrict (commSp w₁)).Nondegenerate := by
    obtain ⟨-, ⟨e₁⟩⟩ := inv_type h₁ hw₁
    exact e₁.nondegenerate_iff.2 (QuadraticMap.nondegenerate_weightedSumSquares
      fun _ => isRegular_one)
  obtain ⟨g, hgO, hg⟩ := inv_conj_of_equiv (MDot_le_OVq h₁) (MDot_le_OVq h₂) hw₁ hw₂ hnd f
  obtain ⟨p, hpO, hpc, hgp⟩ := hP g hgO
  refine ⟨g * p, hgp, ?_⟩
  rw [← hg]
  have hp : p * w₁ * p⁻¹ = w₁ := by rw [hpc, mul_assoc, mul_inv_cancel, mul_one]
  calc g * p * w₁ * (g * p)⁻¹ = g * (p * w₁ * p⁻¹) * g⁻¹ := by group
    _ = g * w₁ * g⁻¹ := by rw [hp]

theorem inv_exists_adjust (p : Fin 4 → GL6) (hpO : ∀ i, p i ∈ OVq) (hsq : ∀ i, p i * p i = 1)
    (hinj : ∀ i j, p i * p j ∈ MDot → i = j) : ∀ g ∈ OVq, ∃ i, g * p i ∈ MDot := by
  have hinv : ∀ i, (p i)⁻¹ = p i := fun i => inv_eq_of_mul_eq_one_right (hsq i)
  let F : ↥MDot × Fin 4 → ↥OVq := fun x =>
    ⟨(x.1 : GL6) * p x.2, OVq.mul_mem (MDot_le_OVq x.1.2) (hpO x.2)⟩
  have hFinj : Function.Injective F := by
    rintro ⟨m, i⟩ ⟨m', j⟩ h
    have h1 : (m : GL6) * p i = m' * p j := congrArg Subtype.val h
    have h2 : (m' : GL6)⁻¹ * m = p j * p i := by
      rw [inv_mul_eq_iff_eq_mul]
      calc (m : GL6) = m * (p i * p i) := by rw [hsq, mul_one]
        _ = (m * p i) * p i := by rw [mul_assoc]
        _ = (m' * p j) * p i := by rw [h1]
        _ = m' * (p j * p i) := by rw [mul_assoc]
    have h3 : p j * p i ∈ MDot := h2 ▸ MDot.mul_mem (MDot.inv_mem m'.2) m.2
    have hij : j = i := hinj j i h3
    subst hij
    have : (m : GL6) = m' := mul_right_cancel h1
    simp [Subtype.ext this]
  have hbij : Function.Bijective F := hFinj.bijective_of_nat_card_le (by
    rw [card_OVq_eq, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]
    omega)
  intro g hg
  obtain ⟨⟨m, i⟩, hmi⟩ := hbij.2 ⟨g, hg⟩
  refine ⟨i, ?_⟩
  have : (m : GL6) * p i = g := congrArg Subtype.val hmi
  rw [← this, mul_assoc, hsq, mul_one]
  exact m.2

@[expose] def invT : Fin 4 → GL6 := ![1, eJ {2}, eJ {5}, eJ {2, 5}]

theorem invT_mem (i : Fin 4) : invT i ∈ OVq := by
  fin_cases i
  · exact OVq.one_mem
  · exact eJ_mem_OVq _
  · exact eJ_mem_OVq _
  · exact eJ_mem_OVq _

theorem invT_sq : ∀ i, invT i * invT i = 1 := by decide

theorem invT_comm_zDot : ∀ i, invT i * zDot = zDot * invT i := by
  unfold zDot
  decide +kernel

theorem invT_comm_fDot : ∀ i, invT i * fDot = fDot * invT i := by decide +kernel

theorem inv_eJ_det (J : Finset (Fin 6)) :
    (eJ J : Matrix (Fin 6) (Fin 6) (ZMod 3)).det = ∏ i, eJd J i :=
  Matrix.det_diagonal

theorem inv_eJ_two_not_mem : eJ {2} ∉ MDot := by
  intro h
  have := det_of_mem_MDot h
  rw [inv_eJ_det] at this
  revert this
  decide

theorem inv_eJ_five_not_mem : eJ {5} ∉ MDot := by
  intro h
  have := det_of_mem_MDot h
  rw [inv_eJ_det] at this
  revert this
  decide

theorem inv_eJ_two_five_not_mem : eJ {2, 5} ∉ MDot := by
  intro h
  have hprod : (([⟨xvec 2, qV_xvec_ne_zero 2⟩, ⟨xvec 5, qV_xvec_ne_zero 5⟩] :
      List ReflVec).map reflOf).prod = eJ {2, 5} := by decide +kernel
  rw [← hprod, prod_refl_mem_MDot_iff] at h
  have hc : ([⟨xvec 2, qV_xvec_ne_zero 2⟩, ⟨xvec 5, qV_xvec_ne_zero 5⟩] :
      List ReflVec).countP (fun v => qV v.1 = -1) = 1 := by decide
  rw [hc] at h
  exact absurd h.2 (by decide)

theorem invT_inj : ∀ i j, invT i * invT j ∈ MDot → i = j := by
  have key : ∀ i j : Fin 4, i ≠ j → invT i * invT j = eJ {2} ∨ invT i * invT j = eJ {5} ∨
      invT i * invT j = eJ {2, 5} := by decide +kernel
  intro i j hij
  by_contra hne
  rcases key i j hne with h | h | h <;> rw [h] at hij
  · exact inv_eJ_two_not_mem hij
  · exact inv_eJ_five_not_mem hij
  · exact inv_eJ_two_five_not_mem hij

theorem inv_adjust_of_comm (w : GL6) (hc : ∀ i, invT i * w = w * invT i) :
    ∀ g ∈ OVq, ∃ p ∈ OVq, p * w = w * p ∧ g * p ∈ MDot := by
  intro g hg
  obtain ⟨i, hi⟩ := inv_exists_adjust invT invT_mem invT_sq invT_inj g hg
  exact ⟨invT i, invT_mem i, hc i, hi⟩

theorem inv_zDot_mem_MDot : zDot ∈ MDot := zDot_mem_GDot.1

theorem inv_z_conj {g : GL6} (hg : g ∈ MDot) :
    Module.finrank (ZMod 3) (commSp (g * zDot * g⁻¹)) = 4 ∧
      SignPlus (commSp (g * zDot * g⁻¹)) := by
  rw [inv_commSp_conj_eq, commSp_zDot, LinearEquiv.finrank_map_eq]
  exact ⟨finrank_V4plus, inv_signPlus_map _ (inv_toLinEquiv_isometry (MDot_le_OVq hg))
    signPlus_V4plus⟩

theorem inv_f_conj {g : GL6} (hg : g ∈ MDot) :
    Module.finrank (ZMod 3) (commSp (g * fDot * g⁻¹)) = 2 ∧
      SignMinus (commSp (g * fDot * g⁻¹)) := by
  rw [inv_commSp_conj_eq, commSp_fDot, LinearEquiv.finrank_map_eq]
  exact ⟨finrank_V2minus, inv_signMinus_map _ (inv_toLinEquiv_isometry (MDot_le_OVq hg))
    signMinus_V2minus⟩

theorem inv_exists_z {w : GL6} (hw : w ∈ MDot) (hww : w * w = 1)
    (hd : Module.finrank (ZMod 3) (commSp w) = 4) : ∃ g ∈ MDot, g * zDot * g⁻¹ = w :=
  inv_conj_of_dim_eq inv_zDot_mem_MDot hw zDot_mul_self hww
    (by rw [commSp_zDot, finrank_V4plus, hd]) (inv_adjust_of_comm zDot invT_comm_zDot)

theorem inv_exists_f {w : GL6} (hw : w ∈ MDot) (hww : w * w = 1)
    (hd : Module.finrank (ZMod 3) (commSp w) = 2) : ∃ g ∈ MDot, g * fDot * g⁻¹ = w :=
  inv_conj_of_dim_eq fDot_mem_MDot hw fDot_mul_self hww
    (by rw [commSp_fDot, finrank_V2minus, hd]) (inv_adjust_of_comm fDot invT_comm_fDot)

theorem inv_classes :
    (∀ w : GL6, w ∈ MDot → w ≠ 1 → w * w = 1 →
        ((∃ g ∈ MDot, g * zDot * g⁻¹ = w) ↔
          (Module.finrank (ZMod 3) (commSp w) = 4 ∧ SignPlus (commSp w))) ∧
        ((∃ g ∈ MDot, g * fDot * g⁻¹ = w) ↔
          (Module.finrank (ZMod 3) (commSp w) = 2 ∧ SignMinus (commSp w))) ∧
        ((∃ g ∈ MDot, g * zDot * g⁻¹ = w) ∨ (∃ g ∈ MDot, g * fDot * g⁻¹ = w))) ∧
      ¬ ∃ g ∈ MDot, g * zDot * g⁻¹ = fDot := by
  refine ⟨fun w hw hw1 hww => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro ⟨g, hg, rfl⟩
    exact inv_z_conj hg
  · exact fun h => inv_exists_z hw hww h.1
  · rintro ⟨g, hg, rfl⟩
    exact inv_f_conj hg
  · exact fun h => inv_exists_f hw hww h.1
  · rcases inv_dim hw hw1 hww with h2 | h4
    · exact Or.inr (inv_exists_f hw hww h2)
    · exact Or.inl (inv_exists_z hw hww h4)
  · rintro ⟨g, hg, h⟩
    have h4 := (inv_z_conj hg).1
    rw [h, commSp_fDot, finrank_V2minus] at h4
    omega

theorem f53Model : F53Model := f53Model_of_inv inv_classes

end

end CFSG.Quasithin.SimsF5
