module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenCyclicThreeIrreducible
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenCyclicThreeSigma
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNormalExtraspecialRechoice
public import CFSG.LinearAlgebra.CoordinateMatrixSubgroupTransport
public import CFSG.LinearAlgebra.MatrixPlanes
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLOrderThreeHermitian

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LinearAlgebra CFSG.RepresentationTheory
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open scoped Pointwise

private theorem map_comap_raw_eq_of_cyclic
    {W : Type*} [CommGroup W]
    (A : Subgroup (MulAut W))
    (ρ : A →* coordinateSemilinearGroup 3 OmegaField)
    (Lb : Subgroup (MulAut W))
    (hker : (SemidirectProduct.rightHom.comp ρ).ker =
      (Subgroup.centralizer (Lb : Set (MulAut W))).subgroupOf A)
    (hLbA : Lb ≤ A)
    (hcyc : IsCyclic ↥Lb) :
    (Lb.comap (A.subtype.comp (SemidirectProduct.rightHom.comp ρ).ker.subtype)).map
      (A.subtype.comp (SemidirectProduct.rightHom.comp ρ).ker.subtype) = Lb := by
  classical
  let J : Subgroup A := (SemidirectProduct.rightHom.comp ρ).ker
  let raw : J →* MulAut W := A.subtype.comp J.subtype
  apply le_antisymm
  · rintro g ⟨j, hj, rfl⟩
    exact hj
  · intro l hl
    have hlA : l ∈ A := hLbA hl
    have hlc : l ∈ Subgroup.centralizer (Lb : Set (MulAut W)) :=
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        (@IsCyclic.isMulCommutative ↥Lb _ hcyc)) hl
    have hcC : (⟨l, hlA⟩ : A) ∈
        (Subgroup.centralizer (Lb : Set (MulAut W))).subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]
      exact hlc
    have hcJ : (⟨l, hlA⟩ : A) ∈ J := by
      rw [show J = (Subgroup.centralizer (Lb : Set (MulAut W))).subgroupOf A from hker]
      exact hcC
    refine Subgroup.mem_map.mpr ⟨⟨⟨l, hlA⟩, hcJ⟩, ?_, rfl⟩
    change raw ⟨⟨l, hlA⟩, hcJ⟩ ∈ Lb
    simpa [raw] using hl

theorem exists_cyclic_three_rank_six_s1_action_data
    {G : Type} [Group G] [Finite G]
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    (hm : mBar D.M V₀ V hV = 3)
    (hs : s15 D.M V₀ V hV L = 1)
    (hcyc : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hrk : rk ↥(wTil V₀ V hV L) = 6) :
    ∃ (z : MulAut (Vtil V₀ V hV))
      (e : Vtil V₀ V hV ≃* Multiplicative (Fin 3 → OmegaField))
      (ρ : Mbar D.M V₀ V hV →* coordinateSemilinearGroup 3 OmegaField)
      (τ : (SemidirectProduct.rightHom.comp ρ).ker →*
        Matrix.GeneralLinearGroup (Fin 3) OmegaField),
      let A := Mbar D.M V₀ V hV
      let J := (SemidirectProduct.rightHom.comp ρ).ker
      let raw : J →* MulAut (Vtil V₀ V hV) := A.subtype.comp J.subtype
      let Lb := lBar V₀ V hV L
      let Z : Subgroup J := Lb.comap raw
      let Zmat := Z.map τ
      z ∈ Lb ∧ orderOf z = 3 ∧ Lb = Subgroup.zpowers z ∧
      (∀ w, Multiplicative.toAdd (e (z w)) =
        CFSG.LinearAlgebra.omega • Multiplicative.toAdd (e w)) ∧
      Function.Injective ρ ∧
      (∀ (a : A) (w : Vtil V₀ V hV),
        Multiplicative.toAdd (e ((a : MulAut (Vtil V₀ V hV)) w)) =
          coordinateSemilinearMap (ρ a) (Multiplicative.toAdd (e w))) ∧
      J = (Subgroup.centralizer (Lb : Set (MulAut (Vtil V₀ V hV)))).subgroupOf A ∧
      J.Normal ∧ Odd (Nat.card J) ∧ J.index = 2 ∧
      Function.Injective τ ∧
      (∀ j : J, ρ (j : A) = SemidirectProduct.inl (τ j)) ∧
      (∀ (j : J) (w : Vtil V₀ V hV),
        Multiplicative.toAdd (e ((raw j) w)) =
          (τ j : Matrix (Fin 3) (Fin 3) OmegaField).mulVec
            (Multiplicative.toAdd (e w))) ∧
      IsIrreducibleMatrixRep τ.range.subtype ∧
      (∀ a : A, τ.range.map
        (coordinateSemilinearGLAct 3 OmegaField (ρ a)).toMonoidHom = τ.range) ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup J) ∧
      (∀ N : Subgroup A, N.Normal → N.index ≠ 3) ∧
      D.sig = {3} ∧
      wTil V₀ V hV L = ⊤ ∧
      rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6 ∧
      Lb ≤ A ∧ Z.map raw = Lb ∧
      Z ≤ Subgroup.center J ∧ Nat.card Z = 3 ∧
      Zmat ≤ τ.range ∧ Nat.card Zmat = 3 ∧
      Zmat = (Matrix.GeneralLinearGroup.scalar (Fin 3) :
        OmegaFieldˣ →* Matrix.GeneralLinearGroup (Fin 3) OmegaField).range ∧
      (∀ j ∈ Z, j ^ 3 = 1) ∧
      (∀ M ∈ Zmat, M ^ 3 = 1) ∧
      (∀ j ∈ Z, ∃ c : OmegaFieldˣ,
        τ j = Matrix.GeneralLinearGroup.scalar (Fin 3) c) ∧
      (∃ zJ : J, raw zJ = z ∧ orderOf zJ = 3 ∧
        Z = Subgroup.zpowers zJ ∧
        (τ zJ : Matrix (Fin 3) (Fin 3) OmegaField) =
          Matrix.scalar (Fin 3) CFSG.LinearAlgebra.omega) := by
  classical
  obtain ⟨z, e, ρ, τ, hzmem, hzord, hgen, he, hρinj, hact, hker,
    hτinj, hτ, hτact, hirr⟩ :=
    exists_cyclic_three_rank_six_s1_irreducible D hx h61 h127 h1214 hS hc hm hs hcyc hrk
  let A : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let J : Subgroup A := (SemidirectProduct.rightHom.comp ρ).ker
  let raw : J →* MulAut (Vtil V₀ V hV) := A.subtype.comp J.subtype
  let Lb : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let Z : Subgroup J := Lb.comap raw
  let Zmat : Subgroup (Matrix.GeneralLinearGroup (Fin 3) OmegaField) := Z.map τ
  obtain ⟨hCnormal, hCodd, hCindex⟩ :=
    cyclic_three_rank_six_s1_centralizer D hc hm hs hcyc hrk
  have hJn : J.Normal := by
    rw [show J = (Subgroup.centralizer (Lb : Set (MulAut (Vtil V₀ V hV)))).subgroupOf A
      from hker]
    exact hCnormal
  have hJodd : Odd (Nat.card J) := by
    rw [show J = (Subgroup.centralizer (Lb : Set (MulAut (Vtil V₀ V hV)))).subgroupOf A
      from hker]
    exact hCodd
  have hJidx : J.index = 2 := by
    rw [show J = (Subgroup.centralizer (Lb : Set (MulAut (Vtil V₀ V hV)))).subgroupOf A
      from hker]
    exact hCindex
  obtain ⟨hsigma, hrankA, hrankJ⟩ :=
    cyclic_three_rank_six_s1_sigma_and_pRank D hx h61 h127 hS.hyp16 hc hs hcyc hrk
  have hJrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup J) := by
    haveI : J.Normal := hJn
    exact hrankJ J hJidx
  have hnoindex : ∀ N : Subgroup A, N.Normal → N.index ≠ 3 := by
    intro N hN
    haveI : N.Normal := hN
    exact cyclic_three_rank_six_s1_no_index_three
      D hx h61 h127 h638 hS.hyp16 hc hs hcyc hrk N
  have htop : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 hc hs
  have hrk_top : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6 := by
    rw [← htop]
    exact hrk
  have hLbA : Lb ≤ A := by
    change lBar V₀ V hV L ≤ Mbar D.M V₀ V hV
    simpa [lBar] using barSub_mono V₀ V hV hS.hyp151.le
  have hZraw : Z.map raw = Lb := by
    change (Lb.comap raw).map raw = Lb
    exact map_comap_raw_eq_of_cyclic A ρ Lb hker hLbA hcyc.1
  have hzA : z ∈ A := hLbA hzmem
  have hzC : (⟨z, hzA⟩ : A) ∈
      (Subgroup.centralizer (Lb : Set (MulAut (Vtil V₀ V hV)))).subgroupOf A := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_centralizer_iff.mpr fun l hl =>
      ((Subgroup.mem_centralizer_iff.1
        ((Subgroup.le_centralizer_iff_isMulCommutative.mpr
          (@IsCyclic.isMulCommutative ↥Lb _ hcyc.1)) hl)) z hzmem).symm
  have hzJmem : (⟨z, hzA⟩ : A) ∈ J := by
    rw [show J = (Subgroup.centralizer (Lb : Set (MulAut (Vtil V₀ V hV)))).subgroupOf A
      from hker]
    exact hzC
  let zJ : J := ⟨⟨z, hzA⟩, hzJmem⟩
  have hzJraw : raw zJ = z := rfl
  have hzJZ : zJ ∈ Z := by
    change raw zJ ∈ Lb
    rw [hzJraw]
    exact hzmem
  have hcardZ : Nat.card Z = 3 := by
    have hinj : Function.Injective raw := by
      intro x y hxy
      exact J.subtype_injective (A.subtype_injective hxy)
    have h := Subgroup.card_map_of_injective (f := raw) (K := Z) hinj
    rw [hZraw, hcyc.2] at h
    exact h.symm
  have hzJord : orderOf zJ = 3 := by
    calc orderOf zJ = orderOf (zJ : A) := (Subgroup.orderOf_coe zJ).symm
      _ = orderOf ((zJ : A) : MulAut (Vtil V₀ V hV)) :=
          (Subgroup.orderOf_coe (zJ : A)).symm
      _ = orderOf z := rfl
      _ = 3 := hzord
  have hZzp : Z = Subgroup.zpowers zJ := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzJZ) ?_).symm
    rw [Nat.card_zpowers, hzJord, hcardZ]
  have hJcent : ∀ j : J, j * zJ = zJ * j := by
    intro j
    apply Subtype.ext
    apply Subtype.ext
    change ((j : A) : MulAut (Vtil V₀ V hV)) * z =
      z * ((j : A) : MulAut (Vtil V₀ V hV))
    have hjC : (j : A) ∈
        (Subgroup.centralizer (Lb : Set (MulAut (Vtil V₀ V hV)))).subgroupOf A := by
      have hJle : J ≤ (Subgroup.centralizer
          (Lb : Set (MulAut (Vtil V₀ V hV)))).subgroupOf A := by
        rw [show J = (Subgroup.centralizer
          (Lb : Set (MulAut (Vtil V₀ V hV)))).subgroupOf A from hker]
      exact hJle j.property
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hjC) z hzmem).symm
  have hzJcenter : zJ ∈ Subgroup.center J :=
    Subgroup.mem_center_iff.mpr hJcent
  have hZcent : Z ≤ Subgroup.center J := by
    rw [hZzp]
    exact Subgroup.zpowers_le.mpr hzJcenter
  have hZmat_le_range : Zmat ≤ τ.range := by
    change Z.map τ ≤ τ.range
    exact Subgroup.map_le_range τ Z
  have hcardZmat : Nat.card Zmat = 3 := by
    change Nat.card ↥(Z.map τ) = 3
    rw [Subgroup.card_map_of_injective (f := τ) (K := Z) hτinj, hcardZ]
  have hAllVec : ∀ x : Fin 3 → OmegaField,
      (τ zJ : Matrix (Fin 3) (Fin 3) OmegaField).mulVec x =
        CFSG.LinearAlgebra.omega • x := by
    intro x
    let w : Vtil V₀ V hV := e.symm (Multiplicative.ofAdd x)
    have hx : Multiplicative.toAdd (e w) = x := by simp [w]
    have h1 := hτact zJ w
    rw [hx] at h1
    have h2 := he w
    rw [hx] at h2
    rw [show ((zJ : A) : MulAut (Vtil V₀ V hV)) = z from rfl] at h1
    rw [← h1, h2]
  have hzJscalar : (τ zJ : Matrix (Fin 3) (Fin 3) OmegaField) =
      Matrix.scalar (Fin 3) CFSG.LinearAlgebra.omega := by
    ext i j
    have h := congrFun (hAllVec (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
    rw [h, Matrix.scalar_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  let omegaUnit : OmegaFieldˣ :=
    Units.mk0 CFSG.LinearAlgebra.omega
      CFSG.LocalAnalysis.GorensteinLyons.OrderThreeHermitian.omega_ne_zero
  have hzJscalarGL : τ zJ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) omegaUnit := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    exact hzJscalar
  have hZscalar : ∀ j ∈ Z, ∃ c : OmegaFieldˣ,
      τ j = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    intro j hj
    rw [hZzp] at hj
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hj
    refine ⟨omegaUnit ^ k, ?_⟩
    rw [← hk]
    calc τ (zJ ^ k) = τ zJ ^ k := map_zpow τ zJ k
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 3) omegaUnit) ^ k := by rw [hzJscalarGL]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) (omegaUnit ^ k) :=
          (map_zpow (Matrix.GeneralLinearGroup.scalar (Fin 3)) omegaUnit k).symm
  have hZmat_le_scalar : Zmat ≤
      (Matrix.GeneralLinearGroup.scalar (Fin 3) :
        OmegaFieldˣ →* Matrix.GeneralLinearGroup (Fin 3) OmegaField).range := by
    rintro M ⟨j, hj, rfl⟩
    obtain ⟨c, hc⟩ := hZscalar j hj
    exact ⟨c, hc.symm⟩
  have hcardScalarRange :
      Nat.card ↥((Matrix.GeneralLinearGroup.scalar (Fin 3) :
        OmegaFieldˣ →* Matrix.GeneralLinearGroup (Fin 3) OmegaField).range) = 3 := by
    have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 3) :
        OmegaFieldˣ →* Matrix.GeneralLinearGroup (Fin 3) OmegaField) :=
      generalLinearGroup_scalar_injective
    have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [Nat.card_units,
      CFSG.LocalAnalysis.GorensteinLyons.OrderThreeHermitian.natCard_omegaField] at h
    norm_num at h
    exact h.symm
  have hZmatEq : Zmat =
      (Matrix.GeneralLinearGroup.scalar (Fin 3) :
        OmegaFieldˣ →* Matrix.GeneralLinearGroup (Fin 3) OmegaField).range := by
    exact Subgroup.eq_of_le_of_card_ge hZmat_le_scalar (by rw [hcardScalarRange, hcardZmat])
  have hZcube : ∀ j ∈ Z, j ^ 3 = 1 := by
    intro j hj
    let jZ : Z := ⟨j, hj⟩
    have h := pow_card_eq_one' (x := jZ)
    rw [hcardZ] at h
    exact congrArg Subtype.val h
  have hZmat_cube : ∀ M ∈ Zmat, M ^ 3 = 1 := by
    intro M hM
    let M' : Zmat := ⟨M, hM⟩
    have h := pow_card_eq_one' (x := M')
    rw [hcardZmat] at h
    exact congrArg Subtype.val h
  exact ⟨z, e, ρ, τ, hzmem, hzord, hgen, he, hρinj, hact, hker,
    hJn, hJodd, hJidx, hτinj, hτ, hτact, hirr,
    (fun a => CFSG.LinearAlgebra.tau_range_map_coordinateSemilinearGLAct_eq
      3 OmegaField ρ τ hτ a),
    hJrank, hnoindex, hsigma, htop, hrk_top, hLbA, hZraw, hZcent, hcardZ,
    hZmat_le_range, hcardZmat, hZmatEq, hZcube, hZmat_cube, hZscalar,
    ⟨zJ, hzJraw, hzJord, hZzp, hzJscalar⟩⟩

theorem exists_rechoice_case162_4_case168_3_of_invariant_matrix_isPOnePlusTwo
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    (hcyc : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hFullRank : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6)
    (hSigma : D.sig = {3})
    (ρ : Mbar D.M V₀ V hV →* coordinateSemilinearGroup 3 OmegaField)
    (τ : (SemidirectProduct.rightHom.comp ρ).ker →*
      Matrix.GeneralLinearGroup (Fin 3) OmegaField)
    (hτinj : Function.Injective τ)
    (hτ : ∀ j : (SemidirectProduct.rightHom.comp ρ).ker,
      ρ (j : Mbar D.M V₀ V hV) = SemidirectProduct.inl (τ j))
    (hker : (SemidirectProduct.rightHom.comp ρ).ker =
      (Subgroup.centralizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))).subgroupOf
          (Mbar D.M V₀ V hV))
    (Hmat : Subgroup (Matrix.GeneralLinearGroup (Fin 3) OmegaField))
    (hHrange : Hmat ≤ τ.range)
    (hHinv : ∀ a : Mbar D.M V₀ V hV,
      Hmat.map (coordinateSemilinearGLAct 3 OmegaField (ρ a)).toMonoidHom = Hmat)
    (hZH : ((lBar V₀ V hV L).comap
      ((Mbar D.M V₀ V hV).subtype.comp
        (SemidirectProduct.rightHom.comp ρ).ker.subtype)).map τ ≤ Hmat)
    (hHshape : CFSG.Quasithin.IsPOnePlusTwo 3 ↥Hmat) :
    ∃ L' : Subgroup G, Setting16 D V₀ V L' ∧
      barSub V₀ V hV L' ≠ ⊥ ∧ Conc4_136 D V₀ V hV L' ∧
      lBar V₀ V hV L' = CFSG.LinearAlgebra.CyclicThreeActionData.rawH
        (Mbar D.M V₀ V hV) ρ τ Hmat ∧
      Case162_4 D V₀ V hV L' ∧ Case168_3 D V₀ V hV L' := by
  classical
  let A : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let J : Subgroup A := (SemidirectProduct.rightHom.comp ρ).ker
  let raw : J →* MulAut (Vtil V₀ V hV) := A.subtype.comp J.subtype
  let Lb : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  have hLbA : Lb ≤ A := by
    change lBar V₀ V hV L ≤ Mbar D.M V₀ V hV
    simpa [lBar] using barSub_mono V₀ V hV hS.hyp151.le
  have hZraw : (Lb.comap raw).map raw = Lb :=
    map_comap_raw_eq_of_cyclic A ρ Lb hker hLbA hcyc.1
  have hHA : CFSG.LinearAlgebra.CyclicThreeActionData.rawH A ρ τ Hmat ≤ A :=
    CFSG.LinearAlgebra.CyclicThreeActionData.rawH_le A ρ τ Hmat
  have hHnormal : ((CFSG.LinearAlgebra.CyclicThreeActionData.rawH A ρ τ Hmat).subgroupOf
      A).Normal :=
    CFSG.LinearAlgebra.CyclicThreeActionData.normal_subgroupOf_rawH A ρ τ hτ Hmat hHinv
  have hLH : Lb ≤ CFSG.LinearAlgebra.CyclicThreeActionData.rawH A ρ τ Hmat := by
    exact CFSG.LinearAlgebra.CyclicThreeActionData.le_rawH_of_map_comap_eq
      A ρ τ Lb hZraw Hmat hZH
  have hshape : CFSG.Quasithin.IsPOnePlusTwo 3
      ↥(CFSG.LinearAlgebra.CyclicThreeActionData.rawH A ρ τ Hmat) :=
    CFSG.LinearAlgebra.CyclicThreeActionData.isPOnePlusTwo_of_mulEquiv_rawHEquiv
      A ρ τ hτinj Hmat hHrange hHshape
  obtain ⟨L', hS', hne, hconc', hbar, hcase2, hcase3⟩ :=
    exists_rechoice_case162_4_case168_3_of_normal_isPOnePlusTwo
      hS.hyp16 hc hcyc.2 hFullRank hSigma hHA hHnormal hLH hshape
  refine ⟨L', hS', hne, hconc', ?_, hcase2, hcase3⟩
  simpa [A] using hbar

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
