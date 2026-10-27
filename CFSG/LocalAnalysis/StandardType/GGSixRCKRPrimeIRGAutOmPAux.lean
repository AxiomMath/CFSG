module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalGraphPlus
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.Universal.Spin.Roots.TypeD

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1
  CFSG.StandardType.ClassicalPosition
open CFSG.LieType.Universal.Spin CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
open CFSG.StandardType.AutOm CFSG.StandardType.OrdPGraphOmega

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

private def irgOP_flip (k : Fin n) (r : Bool) : Bool :=
  if k.val = 0 then !r else r

private theorem irgOP_flip_eq {k : Fin n} (hk : k.val = 0) (r : Bool) :
    irgOP_flip k r = !r := by
  simp [irgOP_flip, hk]

private theorem irgOP_flip_eq_of_ne {k : Fin n} (hk : k.val ≠ 0) (r : Bool) :
    irgOP_flip k r = r := by
  simp [irgOP_flip, hk]

private theorem irgOP_reflMat_pvec (hn : 1 ≤ n) (k : Fin n) (r : Bool) :
    Matrix.mulVec ((reflMat (coordinateQuadPlus n K) (vPlus hn)
        (plusUnitVector_form_ne_zero hn) : GL (Fin (2 * n)) K) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) K) (pvec k r) =
      pvec k (irgOP_flip k r) := by
  by_cases hk : k.val = 0
  · have hk0 : k = (⟨0, by omega⟩ : Fin n) := Fin.ext hk
    rw [hk0, irgOP_flip_eq (by simp)]
    exact reflMat_vPlus_pvec_zero hn r
  · rw [irgOP_flip_eq_of_ne hk]
    exact reflMat_vPlus_pvec hn (by simpa [Fin.ext_iff] using hk) r

private theorem irgOP_gRefl_eichler (hn : 1 ≤ n) (u w y : Fin (2 * n) → K) :
    coordinateSemilinearMap (gRefl (K := K) hn).val
        (eichlerC (coordinateQuadPlus n K) u w y) =
      eichlerC (coordinateQuadPlus n K)
        (coordinateSemilinearMap (gRefl (K := K) hn).val u)
        (coordinateSemilinearMap (gRefl (K := K) hn).val w)
        (coordinateSemilinearMap (gRefl (K := K) hn).val y) :=
  semilinear_eichlerC (coordinateQuadPlus n K) (gRefl (K := K) hn).val (gRefl_form hn) u w y

private theorem irgOP_plusRefl_longRoot (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (c : K) :
    plusRefl (K := K) (by omega : 1 ≤ n)
        (spinModelPlus hn ((plusFrame n K hn).longRoot hij s t (.ofAdd c))) =
      spinModelPlus hn ((plusFrame n K hn).longRoot hij
        (irgOP_flip i s) (irgOP_flip j t) (.ofAdd c)) := by
  rw [plusRefl_eq]
  refine conjAct_apply_eq_of (gRefl (K := K) (by omega : 1 ≤ n)) _ _ fun y => ?_
  conv_lhs => rw [spinModelPlus_longRoot_eichler hn hij s t c]
  conv_rhs => rw [spinModelPlus_longRoot_eichler hn hij (irgOP_flip i s) (irgOP_flip j t) c]
  rw [irgOP_gRefl_eichler (by omega : 1 ≤ n) (pvec j t) (c • pvec i s) y]
  simp only [coordinateSemilinearMap_inclusion, Matrix.mulVec_smul,
    irgOP_reflMat_pvec (by omega : 1 ≤ n) j t, irgOP_reflMat_pvec (by omega : 1 ≤ n) i s]

private theorem irgOP_fieldAutP_rootGroup (hn : 3 ≤ n) (σ : K ≃+* K)
    {γ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (hstd : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    (((plusDatum n K hn).rootGroup γ).map (spinModelPlus hn)).map (fieldAutP n σ) =
      ((plusDatum n K hn).rootGroup γ).map (spinModelPlus hn) := by
  have hX' : (plusDatum n K hn).rootGroup γ = ((plusFrame n K hn).longRoot hij s t).range :=
    plusRootGroup_eq (K := K) hn hij s t hstd
  rw [hX']
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := hw
    refine ⟨(plusFrame n K hn).longRoot hij s t
      (Multiplicative.ofAdd (σ (Multiplicative.toAdd c))), ⟨_, rfl⟩, ?_⟩
    exact (fieldAutP_spinModelPlus_longRoot (K := K) hn σ hij s t
      (Multiplicative.toAdd c)).symm
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := hy
    refine ⟨spinModelPlus hn ((plusFrame n K hn).longRoot hij s t
      (Multiplicative.ofAdd (σ.symm (Multiplicative.toAdd c)))),
      ⟨(plusFrame n K hn).longRoot hij s t
        (Multiplicative.ofAdd (σ.symm (Multiplicative.toAdd c))), ⟨_, rfl⟩, rfl⟩, ?_⟩
    simpa using fieldAutP_spinModelPlus_longRoot (K := K) hn σ hij s t
      (σ.symm (Multiplicative.toAdd c))

private theorem irgOP_boolSign_eq (r : Bool) : boolSign r = 1 ∨ boolSign r = -1 := by
  cases r <;> simp [boolSign]

private theorem irgOP_flip_not (k : Fin n) (r : Bool) :
    irgOP_flip k (!r) = !(irgOP_flip k r) := by
  by_cases hk : k.val = 0 <;> simp [irgOP_flip, hk]

private theorem irgOP_reflField_rootGroup (hn : 3 ≤ n) (σ : K ≃+* K)
    {γ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (hstd : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    ∃ γ', γ' ∈ (plusDatum n K hn).roots ∧
      (((plusDatum n K hn).rootGroup γ).map (spinModelPlus hn)).map
          (plusRefl (K := K) (by omega : 1 ≤ n) * fieldAutP n σ) =
        ((plusDatum n K hn).rootGroup γ').map (spinModelPlus hn) ∧
      (((plusDatum n K hn).rootGroup (-γ)).map (spinModelPlus hn)).map
          (plusRefl (K := K) (by omega : 1 ≤ n) * fieldAutP n σ) =
        ((plusDatum n K hn).rootGroup (-γ')).map (spinModelPlus hn) := by
  set s' : Bool := irgOP_flip i s with hs'
  set t' : Bool := irgOP_flip j t with ht'
  obtain ⟨γ', hγ'root, hγ'std⟩ :=
    exists_mem_rootsD_toStdD_eq (n := n) (i := i) (j := j) hij
      (irgOP_boolSign_eq s') (irgOP_boolSign_eq t')
  have hXγ : (plusDatum n K hn).rootGroup γ = ((plusFrame n K hn).longRoot hij s t).range :=
    plusRootGroup_eq (K := K) hn hij s t hstd
  have hY : (plusDatum n K hn).rootGroup γ' = ((plusFrame n K hn).longRoot hij s' t').range :=
    plusRootGroup_eq (K := K) hn hij s' t' hγ'std
  have hneg : toStdD n (-γ') = Pi.single i (boolSign (!s')) + Pi.single j (boolSign (!t')) := by
    rw [toStdD_neg, hγ'std, neg_add, ← Pi.single_neg, ← Pi.single_neg,
      ← boolSign_not s', ← boolSign_not t']
  have hYneg : (plusDatum n K hn).rootGroup (-γ') =
      ((plusFrame n K hn).longRoot hij (!s') (!t')).range :=
    plusRootGroup_eq (K := K) hn hij (!s') (!t') hneg
  have hnegγ : toStdD n (-γ) = Pi.single i (boolSign (!s)) + Pi.single j (boolSign (!t)) := by
    rw [toStdD_neg, hstd, neg_add, ← Pi.single_neg, ← Pi.single_neg,
      ← boolSign_not s, ← boolSign_not t]
  have hXneg : (plusDatum n K hn).rootGroup (-γ) =
      ((plusFrame n K hn).longRoot hij (!s) (!t)).range :=
    plusRootGroup_eq (K := K) hn hij (!s) (!t) hnegγ
  have hcc : ∀ c : K, (plusRefl (K := K) (by omega : 1 ≤ n) * fieldAutP n σ :
        MulAut (matrixDerived (coordinateQuadPlus n K)))
        (spinModelPlus hn ((plusFrame n K hn).longRoot hij s t (.ofAdd c))) =
      spinModelPlus hn ((plusFrame n K hn).longRoot hij s' t' (.ofAdd (σ c))) := by
    intro c
    rw [MulAut.mul_apply, fieldAutP_spinModelPlus_longRoot (K := K) hn σ hij s t c,
      irgOP_plusRefl_longRoot hn hij s t (σ c), hs', ht']
  have hccneg : ∀ c : K, (plusRefl (K := K) (by omega : 1 ≤ n) * fieldAutP n σ :
        MulAut (matrixDerived (coordinateQuadPlus n K)))
        (spinModelPlus hn ((plusFrame n K hn).longRoot hij (!s) (!t) (.ofAdd c))) =
      spinModelPlus hn ((plusFrame n K hn).longRoot hij (!s') (!t') (.ofAdd (σ c))) := by
    intro c
    rw [MulAut.mul_apply, fieldAutP_spinModelPlus_longRoot (K := K) hn σ hij (!s) (!t) c,
      irgOP_plusRefl_longRoot hn hij (!s) (!t) (σ c), irgOP_flip_not i s, irgOP_flip_not j t,
      ← hs', ← ht']
  refine ⟨γ', hγ'root, ?_, ?_⟩
  · apply le_antisymm
    · rintro z ⟨y, hy, rfl⟩
      rcases hy with ⟨w, hw, rfl⟩
      have hw' : w ∈ ((plusFrame n K hn).longRoot hij s t).range := hXγ ▸ hw
      rcases hw' with ⟨c, rfl⟩
      exact ⟨(plusFrame n K hn).longRoot hij s' t' (.ofAdd (σ c)),
        hY.symm ▸ ⟨Multiplicative.ofAdd (σ c), rfl⟩, (hcc c).symm⟩
    · rintro z ⟨y, hy, rfl⟩
      have hy' : y ∈ ((plusFrame n K hn).longRoot hij s' t').range := hY ▸ hy
      rcases hy' with ⟨c, rfl⟩
      refine ⟨spinModelPlus hn ((plusFrame n K hn).longRoot hij s t
          (.ofAdd (σ.symm (Multiplicative.toAdd c)))), ?_, ?_⟩
      · exact ⟨(plusFrame n K hn).longRoot hij s t
            (.ofAdd (σ.symm (Multiplicative.toAdd c))),
          hXγ.symm ▸ ⟨Multiplicative.ofAdd (σ.symm (Multiplicative.toAdd c)), rfl⟩, rfl⟩
      · have h := hcc (σ.symm (Multiplicative.toAdd c))
        simpa [RingEquiv.apply_symm_apply] using h
  · apply le_antisymm
    · rintro z ⟨y, hy, rfl⟩
      rcases hy with ⟨w, hw, rfl⟩
      have hw' : w ∈ ((plusFrame n K hn).longRoot hij (!s) (!t)).range := hXneg ▸ hw
      rcases hw' with ⟨c, rfl⟩
      exact ⟨(plusFrame n K hn).longRoot hij (!s') (!t') (.ofAdd (σ c)),
        hYneg.symm ▸ ⟨Multiplicative.ofAdd (σ c), rfl⟩, (hccneg c).symm⟩
    · rintro z ⟨y, hy, rfl⟩
      have hy' : y ∈ ((plusFrame n K hn).longRoot hij (!s') (!t')).range := hYneg ▸ hy
      rcases hy' with ⟨c, rfl⟩
      refine ⟨spinModelPlus hn ((plusFrame n K hn).longRoot hij (!s) (!t)
          (.ofAdd (σ.symm (Multiplicative.toAdd c)))), ?_, ?_⟩
      · exact ⟨(plusFrame n K hn).longRoot hij (!s) (!t)
            (.ofAdd (σ.symm (Multiplicative.toAdd c))),
          hXneg.symm ▸ ⟨Multiplicative.ofAdd (σ.symm (Multiplicative.toAdd c)), rfl⟩, rfl⟩
      · have h := hccneg (σ.symm (Multiplicative.toAdd c))
        simpa [RingEquiv.apply_symm_apply] using h

private theorem irgOP_toStdD_neg_eq {γ : Fin n → ℤ} {i j : Fin n} (s t : Bool)
    (hstd : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    toStdD n (-γ) = Pi.single i (boolSign (!s)) + Pi.single j (boolSign (!t)) := by
  rw [toStdD_neg, hstd, neg_add, ← Pi.single_neg, ← Pi.single_neg,
    ← boolSign_not s, ← boolSign_not t]

private theorem irgOP_conj_map_eq {G : Type*} [Group G] {A B : Subgroup G} {cc : MulAut G}
    {w : G} (h : A.map cc.toMonoidHom = B) :
    (A.map (MulAut.conj w).toMonoidHom).map cc.toMonoidHom =
      B.map (MulAut.conj (cc w)).toMonoidHom := by
  rw [Subgroup.map_map]
  have hfun : cc.toMonoidHom.comp (MulAut.conj w).toMonoidHom =
      (MulAut.conj (cc w)).toMonoidHom.comp cc.toMonoidHom := by
    ext a
    change cc (w * a * w⁻¹) = cc w * cc a * (cc w)⁻¹
    rw [map_mul, map_mul, map_inv]
  rw [hfun, ← Subgroup.map_map, h]

private theorem irgOP_plusCompl_conj (hn : 3 ≤ n)
    {cc : MulAut (matrixDerived (coordinateQuadPlus n K))}
    (hcc : cc ∈ plusCompl (K := K) (n := n) (by omega : 1 ≤ n))
    {γ : Fin n → ℤ} (hγ : γ ∈ (plusDatum n K hn).roots)
    {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (hstd : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (w : matrixDerived (coordinateQuadPlus n K)) :
    ∃ γ', γ' ∈ (plusDatum n K hn).roots ∧
      ((((plusDatum n K hn).rootGroup γ).map (spinModelPlus hn)).map
          (MulAut.conj w).toMonoidHom).map cc.toMonoidHom =
        (((plusDatum n K hn).rootGroup γ').map (spinModelPlus hn)).map
          (MulAut.conj (cc w)).toMonoidHom ∧
      ((((plusDatum n K hn).rootGroup (-γ)).map (spinModelPlus hn)).map
          (MulAut.conj w).toMonoidHom).map cc.toMonoidHom =
        (((plusDatum n K hn).rootGroup (-γ')).map (spinModelPlus hn)).map
          (MulAut.conj (cc w)).toMonoidHom := by
  rw [mem_plusCompl] at hcc
  obtain ⟨σ, rfl | rfl⟩ := hcc
  · refine ⟨γ, hγ, ?_, ?_⟩
    · exact irgOP_conj_map_eq (irgOP_fieldAutP_rootGroup hn σ hij s t hstd)
    · exact irgOP_conj_map_eq (irgOP_fieldAutP_rootGroup hn σ hij (!s) (!t)
        (irgOP_toStdD_neg_eq s t hstd))
  · obtain ⟨γ', hγ', hpos, hneg⟩ := irgOP_reflField_rootGroup hn σ hij s t hstd
    exact ⟨γ', hγ', irgOP_conj_map_eq hpos, irgOP_conj_map_eq hneg⟩

private theorem irgOP_map_conj_map_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (A : Subgroup G) (u : G) :
    (A.map (MulAut.conj u).toMonoidHom).map e.toMonoidHom =
      (A.map e.toMonoidHom).map (MulAut.conj (e u)).toMonoidHom := by
  rw [Subgroup.map_map]
  have hfun : e.toMonoidHom.comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj (e u)).toMonoidHom.comp e.toMonoidHom := by
    ext a
    change e (u * a * u⁻¹) = e u * e a * (e u)⁻¹
    rw [map_mul, map_mul, map_inv]
  rw [hfun, ← Subgroup.map_map]

private theorem irgOP_conj_map_conj {G : Type*} [Group G] (Y : Subgroup G) (v g : G) :
    (Y.map (MulAut.conj v).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      Y.map (MulAut.conj (g * v)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext a
  change g * (v * a * v⁻¹) * g⁻¹ = (g * v) * a * (g * v)⁻¹
  group

private theorem irgOP_map_map_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (f : MulAut G) (A : Subgroup G) :
    (A.map f.toMonoidHom).map e.toMonoidHom =
      (A.map e.toMonoidHom).map (MulAut.congr e f).toMonoidHom := by
  rw [Subgroup.map_map]
  have hfun : e.toMonoidHom.comp f.toMonoidHom =
      (MulAut.congr e f).toMonoidHom.comp e.toMonoidHom := by
    ext a
    rw [MulAut.congr_apply]
    simp
  rw [hfun, ← Subgroup.map_map]

theorem irgOP_spin_plus_rootPair (hn : 5 ≤ n) (hn3 : 3 ≤ n) :
    ∀ (θ : MulAut (spinGroup (quadPlus n K) ⧸ Subgroup.center (spinGroup (quadPlus n K))))
      (β' : Fin n → ℤ), β' ∈ (plusDatum n K hn3).roots →
      GGLongRoot (plusDatum n K hn3) β' →
      ∀ u' : spinGroup (quadPlus n K),
      ∃ β, β ∈ (plusDatum n K hn3).roots ∧
        GGLongRoot (plusDatum n K hn3) β ∧
        ∃ u : spinGroup (quadPlus n K),
          (ggRootSub (plusDatum n K hn3)
              (QuotientGroup.mk' (Subgroup.center (spinGroup (quadPlus n K)))) β' u').map
              θ.toMonoidHom =
            ggRootSub (plusDatum n K hn3)
              (QuotientGroup.mk' (Subgroup.center (spinGroup (quadPlus n K)))) β u ∧
          (ggRootSub (plusDatum n K hn3)
              (QuotientGroup.mk' (Subgroup.center (spinGroup (quadPlus n K)))) (-β') u').map
              θ.toMonoidHom =
            ggRootSub (plusDatum n K hn3)
              (QuotientGroup.mk' (Subgroup.center (spinGroup (quadPlus n K)))) (-β) u := by
  intro θ β' hβ' _ u'
  have hZ : Subgroup.center (spinGroup (quadPlus n K)) = ⊥ :=
    RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := K) hn3
  let qiso : spinGroup (quadPlus n K) ⧸ Subgroup.center (spinGroup (quadPlus n K)) ≃*
      spinGroup (quadPlus n K) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hqiso_mk : ∀ x : spinGroup (quadPlus n K),
      qiso (QuotientGroup.mk' (Subgroup.center (spinGroup (quadPlus n K))) x) = x := by
    intro x
    change (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
        (QuotientGroup.mk' (Subgroup.center (spinGroup (quadPlus n K))) x) = x
    rw [MulEquiv.trans_apply, QuotientGroup.mk'_apply, QuotientGroup.quotientMulEquivOfEq_mk,
      ← QuotientGroup.quotientBot_symm_apply x, MulEquiv.apply_symm_apply]
  let α : MulAut (spinGroup (quadPlus n K)) := MulAut.congr qiso θ
  let sm : spinGroup (quadPlus n K) ≃* matrixDerived (coordinateQuadPlus n K) :=
    MulEquiv.ofBijective (spinModelPlus hn3)
      ⟨spinModelPlus_injective hn3, spinModelPlus_surjective hn3⟩
  have hsm : (sm.toMonoidHom : spinGroup (quadPlus n K) →* matrixDerived (coordinateQuadPlus n K)) =
      spinModelPlus hn3 := by ext x; rfl
  let βΓ : MulAut (matrixDerived (coordinateQuadPlus n K)) := MulAut.congr sm α
  obtain ⟨ι, hι, cc, hcc, hβΓ⟩ := exists_inner_mul_plusCompl hn βΓ
  obtain ⟨g0, rfl⟩ := hι
  obtain ⟨i, j, hij, s, t, hstd, hX⟩ := exists_plusRootGroup_eq (K := K) hn3 hβ'
  set w : matrixDerived (coordinateQuadPlus n K) := sm u' with hw
  obtain ⟨γ', hγ'root, hpos, hneg⟩ := irgOP_plusCompl_conj hn3 hcc hβ' hij s t hstd w
  rw [← hsm] at hpos hneg
  have hlong : GGLongRoot (plusDatum n K hn3) γ' :=
    ggLongRoot_of_symmetric
      (by simpa [plusDatum] using ClassicalInvolution.ModelFacts.isIrreducible_cartanD hn3)
      (by intro a b; simpa [plusDatum] using ClassicalInvolution.RouteD.cartanD_symm a b)
      rfl hγ'root
  set uNew : spinGroup (quadPlus n K) := sm.symm (g0 * cc w) with huNew
  have hsm_uNew : sm uNew = g0 * cc w := by rw [huNew, MulEquiv.apply_symm_apply]
  have hYplus : (((plusDatum n K hn3).rootGroup β').map (MulAut.conj u').toMonoidHom).map
        α.toMonoidHom =
      ((plusDatum n K hn3).rootGroup γ').map (MulAut.conj uNew).toMonoidHom := by
    apply Subgroup.map_injective (f := sm.toMonoidHom) sm.injective
    rw [irgOP_map_map_congr (A := ((plusDatum n K hn3).rootGroup β').map
      (MulAut.conj u').toMonoidHom) sm α]
    rw [irgOP_map_conj_map_equiv (A := (plusDatum n K hn3).rootGroup β') sm u', ← hw]
    rw [show (MulAut.congr sm) α = MulAut.conj g0 * cc from hβΓ]
    rw [show (MulAut.conj g0 * cc).toMonoidHom =
        (MulAut.conj g0).toMonoidHom.comp cc.toMonoidHom from rfl, ← Subgroup.map_map, hpos]
    rw [irgOP_conj_map_conj]
    rw [irgOP_map_conj_map_equiv (A := (plusDatum n K hn3).rootGroup γ') sm uNew, hsm_uNew]
  have hYminus : (((plusDatum n K hn3).rootGroup (-β')).map (MulAut.conj u').toMonoidHom).map
        α.toMonoidHom =
      ((plusDatum n K hn3).rootGroup (-γ')).map (MulAut.conj uNew).toMonoidHom := by
    apply Subgroup.map_injective (f := sm.toMonoidHom) sm.injective
    rw [irgOP_map_map_congr (A := ((plusDatum n K hn3).rootGroup (-β')).map
      (MulAut.conj u').toMonoidHom) sm α]
    rw [irgOP_map_conj_map_equiv (A := (plusDatum n K hn3).rootGroup (-β')) sm u', ← hw]
    rw [show (MulAut.congr sm) α = MulAut.conj g0 * cc from hβΓ]
    rw [show (MulAut.conj g0 * cc).toMonoidHom =
        (MulAut.conj g0).toMonoidHom.comp cc.toMonoidHom from rfl, ← Subgroup.map_map, hneg]
    rw [irgOP_conj_map_conj]
    rw [irgOP_map_conj_map_equiv (A := (plusDatum n K hn3).rootGroup (-γ')) sm uNew, hsm_uNew]
  have hcomp_apply : ∀ x : spinGroup (quadPlus n K),
      qiso (θ (QuotientGroup.mk' (Subgroup.center (spinGroup (quadPlus n K))) x)) = α x := by
    intro x
    have hmk : QuotientGroup.mk' (Subgroup.center (spinGroup (quadPlus n K))) x = qiso.symm x :=
      qiso.injective (by rw [hqiso_mk x, MulEquiv.apply_symm_apply])
    rw [hmk]
    rfl
  have htransport : ∀ (γ : Fin n → ℤ) (u : spinGroup (quadPlus n K)),
      ((ggRootSub (plusDatum n K hn3)
          (QuotientGroup.mk' (Subgroup.center (spinGroup (quadPlus n K)))) γ u).map
          θ.toMonoidHom).map qiso.toMonoidHom =
        (((plusDatum n K hn3).rootGroup γ).map (MulAut.conj u).toMonoidHom).map
          α.toMonoidHom := by
    intro γ u
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨v, hv, rfl⟩
      rcases hv with ⟨a, ha, rfl⟩
      rcases ha with ⟨b, hb, rfl⟩
      exact ⟨u * b * u⁻¹, ⟨b, hb, rfl⟩, (hcomp_apply (u * b * u⁻¹)).symm⟩
    · rintro ⟨v, hv, rfl⟩
      rcases hv with ⟨b, hb, rfl⟩
      exact ⟨θ (QuotientGroup.mk' _ (u * b * u⁻¹)),
        ⟨QuotientGroup.mk' _ (u * b * u⁻¹),
          ⟨u * b * u⁻¹, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩,
        hcomp_apply (u * b * u⁻¹)⟩
  have htransport' : ∀ (γ : Fin n → ℤ) (u : spinGroup (quadPlus n K)),
      ((ggRootSub (plusDatum n K hn3)
          (QuotientGroup.mk' (Subgroup.center (spinGroup (quadPlus n K)))) γ u).map
          qiso.toMonoidHom) =
        ((plusDatum n K hn3).rootGroup γ).map (MulAut.conj u).toMonoidHom := by
    intro γ u
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨a, ha, rfl⟩
      rcases ha with ⟨b, hb, rfl⟩
      exact ⟨b, hb, (hqiso_mk (u * b * u⁻¹)).symm⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨QuotientGroup.mk' _ (u * v * u⁻¹),
        ⟨u * v * u⁻¹, ⟨v, hv, rfl⟩, rfl⟩, hqiso_mk (u * v * u⁻¹)⟩
  refine ⟨γ', hγ'root, hlong, uNew, ?_, ?_⟩
  · apply Subgroup.map_injective (f := qiso.toMonoidHom) qiso.injective
    rw [htransport, hYplus, htransport' γ' uNew]
  · apply Subgroup.map_injective (f := qiso.toMonoidHom) qiso.injective
    rw [htransport, hYminus, htransport' (-γ') uNew]


theorem irgOP_pairAut_of_eq (M : LieUniversal) (hn : 5 ≤ n) (hn3 : 3 ≤ n)
    (hM : M = ⟨spinGroup (quadPlus n K), plusDatum n K hn3⟩) :
    ∀ (θ : MulAut (M.K ⧸ Subgroup.center M.K))
      (β' : Fin M.D.rank → ℤ), β' ∈ M.D.roots → GGLongRoot M.D β' →
      ∀ u' : M.K,
      ∃ β, (β ∈ M.D.roots ∧ (GGLongRoot M.D β ∨
          ((CFSG.Open.StatedLieTag.POmegaPlus = CFSG.Open.StatedLieTag.PSp ∧ n = 2) ∨
            CFSG.Open.StatedLieTag.POmegaPlus = CFSG.Open.StatedLieTag.F4) ∧ 2 • β ∉ M.D.roots)) ∧
        ∃ u : M.K,
          (ggRootSub M.D (QuotientGroup.mk' (Subgroup.center M.K)) β' u').map θ.toMonoidHom =
            ggRootSub M.D (QuotientGroup.mk' (Subgroup.center M.K)) β u ∧
          (ggRootSub M.D (QuotientGroup.mk' (Subgroup.center M.K)) (-β') u').map
              θ.toMonoidHom =
            ggRootSub M.D (QuotientGroup.mk' (Subgroup.center M.K)) (-β) u := by
  subst hM
  intro θ β' hβ' hlong u'
  obtain ⟨β, hβroot, hβlong, u, hpos, hneg⟩ :=
    irgOP_spin_plus_rootPair hn hn3 θ β' hβ' hlong u'
  exact ⟨β, ⟨hβroot, Or.inl hβlong⟩, u, hpos, hneg⟩

end CFSG.StandardType.RCKRP
