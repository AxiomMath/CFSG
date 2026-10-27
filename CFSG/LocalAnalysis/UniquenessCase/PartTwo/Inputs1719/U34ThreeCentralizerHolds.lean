module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3Modules
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xc
public import CFSG.RankThree.PartTwo.KFacts.KS21U34

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartTwo.KFacts.KS21.U34
open CFSG.GH74.KGroups
open Matrix

section U34Concrete

private theorem u34frob4_eq_pow (x : GF16) : frob4 x = x ^ 4 := by
  unfold frob4
  ring

private theorem u34zpow_neg_four (x : GF16) : x ^ (-4 : ℤ) = (x ^ 4)⁻¹ :=
  zpow_neg x 4

private theorem u34eq_diagonal_of_commute_t0 (S : Mat3) (h : S * t0Mat = t0Mat * S) :
    S = Matrix.diagonal ![S 0 0, S 1 1, S 2 2] := by
  rw [t0Mat_eq_diagonal] at h
  have key : ∀ i j, S i j * ![om, 1, om * om] j = ![om, 1, om * om] i * S i j := by
    intro i j
    have := congrFun (congrFun h i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact eq_zero_of_mul_eq (key 0 1) (by decide)
  · exact eq_zero_of_mul_eq (key 0 2) (by decide)
  · exact eq_zero_of_mul_eq (key 1 0) (by decide)
  · rfl
  · exact eq_zero_of_mul_eq (key 1 2) (by decide)
  · exact eq_zero_of_mul_eq (key 2 0) (by decide)
  · exact eq_zero_of_mul_eq (key 2 1) (by decide)
  · rfl

private theorem u34gu3_diagonal_entries {a b c : GF16}
    (h : IsGU3 (Matrix.diagonal ![a, b, c])) :
    a ^ 4 * c = 1 ∧ b ^ 4 * b = 1 ∧ c ^ 4 * a = 1 := by
  unfold IsGU3 at h
  have h02 := congrFun (congrFun h 0) 2
  have h11 := congrFun (congrFun h 1) 1
  have h20 := congrFun (congrFun h 2) 0
  simp [ct3, u34frob4_eq_pow, J3, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.diagonal_apply] at h02 h11 h20
  exact ⟨h02, h11, h20⟩

private theorem u34det3_diagonal {a b c : GF16} :
    det3 (Matrix.diagonal ![a, b, c]) = a * b * c := by
  rw [← det_eq_det3]
  simp [Matrix.det_diagonal, Fin.prod_univ_three]

private noncomputable def u34TorusMat (a : GF16ˣ) : Mat3 :=
  Matrix.diagonal ![((a : GF16)), ((a : GF16)) ^ 3, ((a : GF16)) ^ (-4 : ℤ)]

private theorem u34IsGU3TorusMat : ∀ a : GF16ˣ, IsGU3 (u34TorusMat a) := by
  decide

private theorem u34Det3TorusMat : ∀ a : GF16ˣ, det3 (u34TorusMat a) = 1 := by
  decide

private theorem u34TorusMatDet (a : GF16ˣ) : (u34TorusMat a).det = 1 := by
  rw [det_eq_det3, u34Det3TorusMat]

private noncomputable def u34TorusGL (a : GF16ˣ) : GL (Fin 3) GF16 :=
  GeneralLinearGroup.mkOfDetNeZero (u34TorusMat a)
    (by rw [u34TorusMatDet]; exact one_ne_zero)

private theorem u34CoeTorusGL (a : GF16ˣ) :
    ((u34TorusGL a : GL (Fin 3) GF16) : Mat3) = u34TorusMat a := rfl

private noncomputable def u34TorusElem (a : GF16ˣ) : Y :=
  ⟨u34TorusGL a, by
    rw [mem_Y_iff]
    exact ⟨by rw [u34CoeTorusGL, u34Det3TorusMat],
      by rw [u34CoeTorusGL]; exact u34IsGU3TorusMat a⟩⟩

private theorem u34CoeTorusElem (a : GF16ˣ) : mat (u34TorusElem a) = u34TorusMat a := rfl

private noncomputable def u34TorusHom : GF16ˣ →* Y where
  toFun := u34TorusElem
  map_one' := by
    apply mat_injective
    rw [mat_one, u34CoeTorusElem]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u34TorusMat]
  map_mul' := by
    intro a b
    apply mat_injective
    rw [mat_mul, u34CoeTorusElem, u34CoeTorusElem, u34CoeTorusElem]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u34TorusMat, Matrix.diagonal_mul_diagonal, mul_pow, mul_zpow, mul_comm,
        mul_left_comm, mul_assoc]

private theorem u34TorusHomInjective : Function.Injective u34TorusHom := by
  intro a b h
  have h' := congrArg mat h
  rw [show mat (u34TorusHom a) = u34TorusMat a from rfl,
    show mat (u34TorusHom b) = u34TorusMat b from rfl] at h'
  have h00 := congrFun (congrFun h' 0) 0
  simp [u34TorusMat] at h00
  exact Units.ext h00


private theorem u34TorusElemMemCentralizer (a : GF16ˣ) :
    u34TorusElem a ∈ Subgroup.centralizer ({t0} : Set Y) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply mat_injective
  rw [mat_mul, mat_mul, mat_t0, u34CoeTorusElem]
  rw [u34TorusMat, t0Mat_eq_diagonal]
  simp [Matrix.diagonal_mul_diagonal, mul_comm]

private theorem u34DiagEntriesOfMemCentralizer {g : Y}
    (hg : g ∈ Subgroup.centralizer ({t0} : Set Y)) :
    ∃ (a : GF16) (ha : a ≠ 0), mat g = Matrix.diagonal ![a, a ^ 3, a ^ (-4 : ℤ)] := by
  have hcomm : g * t0 = t0 * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hm : mat g * t0Mat = t0Mat * mat g := by
    rw [← mat_t0]
    rw [← mat_mul, ← mat_mul, hcomm]
  have hdiag := u34eq_diagonal_of_commute_t0 (mat g) hm
  set a : GF16 := mat g 0 0 with ha0
  set b : GF16 := mat g 1 1 with hb0
  set c : GF16 := mat g 2 2 with hc0
  have hdiag' : mat g = Matrix.diagonal ![a, b, c] := by
    simpa only [ha0, hb0, hc0] using hdiag
  have hgu : IsGU3 (Matrix.diagonal ![a, b, c]) := by
    rw [← hdiag']
    exact isGU3_mat g
  obtain ⟨hac, -, -⟩ := u34gu3_diagonal_entries hgu
  have hdet : det3 (Matrix.diagonal ![a, b, c]) = 1 := by
    rw [← hdiag']
    exact ((mem_Y_iff (g : GL (Fin 3) GF16)).mp g.2).1
  have habc : a * b * c = 1 := by
    rw [← u34det3_diagonal]
    exact hdet
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at habc
    exact zero_ne_one habc
  have hc : c = (a ^ 4)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hac)
  have hb : b = a ^ 3 := by
    rw [hc] at habc
    field_simp at habc
    linear_combination habc
  refine ⟨a, ha, ?_⟩
  rw [hdiag', hb, hc, u34zpow_neg_four]

private theorem u34CentralizerT0EqRange :
    Subgroup.centralizer ({t0} : Set Y) = u34TorusHom.range := by
  apply le_antisymm
  · intro g hg
    obtain ⟨a, ha, hgmat⟩ := u34DiagEntriesOfMemCentralizer hg
    refine ⟨Units.mk0 a ha, ?_⟩
    apply mat_injective
    change mat (u34TorusElem (Units.mk0 a ha)) = mat g
    rw [u34CoeTorusElem, hgmat]
    simp [u34TorusMat, Units.val_mk0]
  · rintro g ⟨a, rfl⟩
    exact u34TorusElemMemCentralizer a

private theorem u34IsCyclicCentralizerT0 :
    IsCyclic (Subgroup.centralizer ({t0} : Set Y)) := by
  rw [u34CentralizerT0EqRange]
  exact isCyclic_of_surjective (MonoidHom.ofInjective u34TorusHomInjective).toMonoidHom
    (MonoidHom.ofInjective u34TorusHomInjective).surjective

private theorem u34CardCentralizerT0 :
    Nat.card (Subgroup.centralizer ({t0} : Set Y)) = 15 := by
  rw [u34CentralizerT0EqRange]
  let e := MonoidHom.ofInjective u34TorusHomInjective
  rw [Nat.card_congr e.symm.toEquiv, Nat.card_units, card_GF16]
  norm_num

private theorem u34CentralizerOrderThree (y : Y) (hy : orderOf y = 3) :
    IsCyclic (Subgroup.centralizer ({y} : Set Y)) ∧
      Nat.card (Subgroup.centralizer ({y} : Set Y)) = 15 := by
  have hcardT : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers, hy]
  obtain ⟨g, hg⟩ := exists_eq_map_conj (Subgroup.zpowers y) hcardT
  have hyT : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
  rw [hg] at hyT
  obtain ⟨y0, hy0, hy0eq⟩ := Subgroup.mem_map.mp hyT
  have hy0mem : y0 ∈ Subgroup.zpowers t0 := hy0
  have hy0ord : orderOf y0 = 3 := by
    have hord := (MulEquiv.orderOf_eq (MulAut.conj g) y0).symm
    rw [show (MulAut.conj g) y0 = y from hy0eq, hy] at hord
    exact hord
  have hsub : Subgroup.zpowers y0 = Subgroup.zpowers t0 := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr hy0mem
    · rw [Nat.card_zpowers, orderOf_t0, Nat.card_zpowers, hy0ord]
  have hC : Subgroup.centralizer ({y0} : Set Y) = Subgroup.centralizer ({t0} : Set Y) := by
    ext z
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hz
      have ht0 : t0 ∈ Subgroup.zpowers y0 := by
        rw [hsub]
        exact Subgroup.mem_zpowers t0
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht0
      rw [← hk]
      exact (Commute.zpow_right hz k).eq
    · intro hz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy0mem
      rw [← hk]
      exact (Commute.zpow_right hz k).eq
  have hy0eq' : g * y0 * g⁻¹ = y := by
    simpa [MulAut.conj_apply] using hy0eq
  have hconj : Subgroup.centralizer ({y} : Set Y) =
      (Subgroup.centralizer ({y0} : Set Y)).map (MulAut.conj g).toMonoidHom := by
    rw [← hy0eq']
    ext z
    constructor
    · intro hz
      have hz' := Subgroup.mem_centralizer_singleton_iff.mp hz
      refine ⟨g⁻¹ * z * g, ?_, ?_⟩
      · apply Subgroup.mem_centralizer_singleton_iff.mpr
        calc (g⁻¹ * z * g) * y0 = g⁻¹ * (z * (g * y0 * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * y0 * g⁻¹) * z) * g := by rw [hz']
          _ = y0 * (g⁻¹ * z * g) := by group
      · change g * (g⁻¹ * z * g) * g⁻¹ = z
        group
    · rintro ⟨w, hw, rfl⟩
      have hw' := Subgroup.mem_centralizer_singleton_iff.mp hw
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      calc (g * w * g⁻¹) * (g * y0 * g⁻¹) = g * (w * y0) * g⁻¹ := by group
        _ = g * (y0 * w) * g⁻¹ := by rw [hw']
        _ = (g * y0 * g⁻¹) * (g * w * g⁻¹) := by group
  constructor
  · rw [hconj, hC]
    let e := (Subgroup.centralizer ({t0} : Set Y)).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    exact (MulEquiv.isCyclic e).mp u34IsCyclicCentralizerT0
  · rw [hconj, hC]
    let e := (Subgroup.centralizer ({t0} : Set Y)).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    rw [Nat.card_congr e.symm.toEquiv, u34CardCentralizerT0]

private theorem u34TransferCentralizer {X : Type} [Group X] (e : X ≃* Y) (x : X)
    (hcyc : IsCyclic (Subgroup.centralizer ({e x} : Set Y)))
    (hcard : Nat.card (Subgroup.centralizer ({e x} : Set Y)) = 15) :
    IsCyclic (Subgroup.centralizer ({x} : Set X)) ∧
      Nat.card (Subgroup.centralizer ({x} : Set X)) = 15 := by
  have hmap : (Subgroup.centralizer ({x} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set Y) := by
    apply le_antisymm
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      have hw' := Subgroup.mem_centralizer_singleton_iff.mp hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      change e w * e x = e x * e w
      simpa only [map_mul] using congrArg e hw'
    · intro z hz
      refine Subgroup.mem_map.mpr ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hz' := Subgroup.mem_centralizer_singleton_iff.mp hz
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using hz'
  let eC : Subgroup.centralizer ({x} : Set X) ≃*
      Subgroup.centralizer ({e x} : Set Y) :=
    (Subgroup.equivMapOfInjective (Subgroup.centralizer ({x} : Set X)) e.toMonoidHom
      e.injective).trans (MulEquiv.subgroupCongr hmap)
  refine ⟨?_, ?_⟩
  · exact (MulEquiv.isCyclic eC).mpr hcyc
  · rw [Nat.card_congr eC.toEquiv, hcard]

end U34Concrete

theorem k_U34ThreeCentralizer_holds :
    K_U34ThreeCentralizer := by
  intro X _ _ hX x hx
  have hU3 : IsU3 X 2 :=
    uc22s13xc_isU3_of_isSU3 (by norm_num : Even 2) hX
  have hSC : CFSG.Open.StatedClassicalModel X .PSU 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hU3
  obtain ⟨e⟩ := nonempty_equiv_Y hSC
  have hy : orderOf (e x) = 3 := by rw [MulEquiv.orderOf_eq, hx]
  obtain ⟨hcyc, hcard⟩ := u34CentralizerOrderThree (e x) hy
  exact u34TransferCentralizer e x hcyc hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
