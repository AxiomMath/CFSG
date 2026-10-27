module

public import CFSG.LocalAnalysis.StandardType.GGHalfCentralizer
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.RankThree.PartOne.KFCL.BlockSL

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.GGHalf CFSG.StandardType.CoordSL
  CFSG.RankThree.CALinearPlane CFSG.RankThree.PartOne.KFCL.BlockSL
  CFSG.LocalAnalysis.ComponentInitial Matrix

private noncomputable def sl6b_coordBlockSL_equiv {n : ℕ} {K : Type*} [Field K]
    (J : Finset (Fin n)) :
    coordBlockSL K J ≃* SpecialLinearGroup (Fin J.card) K :=
  ((MonoidHom.ofInjective (blockSLOn_injective (k := K) J)).trans
    (MulEquiv.subgroupCongr (range_blockSLOn (k := K) J))).symm

private noncomputable def sl6b_SL_ringEquiv {K K' : Type*} [Field K] [Field K']
    (m : ℕ) (e : K ≃+* K') :
    SpecialLinearGroup (Fin m) K ≃* SpecialLinearGroup (Fin m) K' where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    apply Subtype.ext
    ext i j
    exact e.symm_apply_apply (A i j)
  right_inv A := by
    apply Subtype.ext
    ext i j
    exact e.apply_symm_apply (A i j)
  map_mul' := map_mul _

private noncomputable def sl6b_SL_fieldEquiv {m : ℕ} {K K' : Type*} [Field K] [Field K']
    [Finite K] [Finite K'] (h : Nat.card K = Nat.card K') :
    SpecialLinearGroup (Fin m) K ≃* SpecialLinearGroup (Fin m) K' := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype K' := Fintype.ofFinite K'
  have h' : Fintype.card K = Fintype.card K' := by
    rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact sl6b_SL_ringEquiv m (FiniteField.ringEquivOfCardEq h')

private theorem sl6b_disjoint_map_conj {G : Type*} [Group G] {X Y : Subgroup G}
    (hXY : Disjoint X Y) (g : G) :
    Disjoint (X.map (MulAut.conj g).toMonoidHom) (Y.map (MulAut.conj g).toMonoidHom) := by
  rw [Subgroup.disjoint_def]
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  have hba : b = a := (MulAut.conj g).injective hab
  subst hba
  rw [Subgroup.disjoint_def.mp hXY ha hb, map_one]

private theorem sl6b_map_conj_inv {G : Type*} [Group G] (g : G) (X : Subgroup G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = X := by
  rw [Subgroup.map_map]
  have h : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
    ext x
    change (MulAut.conj g⁻¹) ((MulAut.conj g) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  rw [h, Subgroup.map_id]

private theorem sl6b_map_inv_conj {G : Type*} [Group G] (g : G) (X : Subgroup G) :
    (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X := by
  rw [Subgroup.map_map]
  have h : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G := by
    ext x
    change (MulAut.conj g) ((MulAut.conj g⁻¹) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  rw [h, Subgroup.map_id]

theorem sl6b_centralizer_blocks_equiv {n : ℕ}
    {t : SpecialLinearGroup (Fin (n + 1)) F2} (ht3 : t ^ 3 = 1) :
    ∃ Z Λ : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2),
      Nonempty (Z ≃* SpecialLinearGroup (Fin (n + 1 - supp t)) F2) ∧
      Nonempty (Λ ≃* SpecialLinearGroup (Fin (supp t / 2)) (GaloisField 2 2)) ∧
      Disjoint Z Λ ∧
      (3 ≤ n + 1 - supp t →
        IsComponentOf Z (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2)))) ∧
      (2 ≤ supp t / 2 →
        IsComponentOf Λ (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2)))) ∧
      (∀ J : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2),
        IsComponentOf J (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2))) →
          J = Z ∨ J = Λ) := by
  obtain ⟨s, r, ε, A₀, k, htk⟩ := exists_frame_of_pow_three t ht3
  obtain ⟨M, k', hMk, hk'⟩ := exists_conj_nsSL_binary ε k
  have hbin : ∀ i, k' i = 0 ∨ k' i = 1 := fun i => (hk' i).1
  set Y' := SLNS.nsSL ε det_rootMat_phi3 k' with hY'
  set A : SpecialLinearGroup (Fin (n + 1)) F2 := A₀ * M with hA
  have hY : SLNS.nsSL ε det_rootMat_phi3 k = M * Y' * M⁻¹ := by
    rw [← hMk]
    group
  have htA : t = A * Y' * A⁻¹ := by
    rw [htk, hY, hA]
    group
  have hsupp : supp t = 2 * ones k' := by
    rw [htA, supp_conj, supp_nsSL, ones]
    congr 2
    refine Finset.filter_congr fun i _ => ?_
    rcases hbin i with h | h <;> simp [h]
  have hsupp2 : supp t / 2 = ones k' := by
    rw [hsupp]
    omega
  have hcent : Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2)) =
      (Subgroup.centralizer ({Y'} : Set (SpecialLinearGroup (Fin (n + 1)) F2))).map
        (MulAut.conj A).toMonoidHom := by
    rw [htA]
    exact (map_conj_centralizer_singleton A Y').symm
  have hZcard : (zeroCoords ε fun i => (k' i : ZMod 3)).card = n + 1 - supp t := by
    rw [card_zeroCoords ε k' hbin, ← hsupp]
  have hΛcard : (classSet (fun i => (k' i : ZMod 3)) 1).card = supp t / 2 := by
    rw [card_classSet k' hbin, hsupp2]
  haveI : Finite (AdjoinRoot phi3) := finite_adjoinRoot
  refine ⟨(zeroBlk ε k').map (MulAut.conj A).toMonoidHom,
    (classBlk ε k').map (MulAut.conj A).toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨((Subgroup.equivMapOfInjective (zeroBlk ε k') (MulAut.conj A).toMonoidHom
      (MulAut.conj A).injective).symm).trans ?_⟩
    exact (sl6b_coordBlockSL_equiv (K := F2) (zeroCoords ε fun i => (k' i : ZMod 3))).trans
      (reindexSL (K := F2) (finCongr hZcard))
  ·
    refine ⟨((Subgroup.equivMapOfInjective (classBlk ε k') (MulAut.conj A).toMonoidHom
      (MulAut.conj A).injective).symm).trans ?_⟩
    exact ((Subgroup.equivMapOfInjective
        (coordBlockSL (AdjoinRoot phi3) (classSet (fun i => (k' i : ZMod 3)) 1))
        (theta phi3 ε) (theta_injective (g := phi3) (ε := ε))).symm).trans
      ((sl6b_coordBlockSL_equiv (K := AdjoinRoot phi3)
          (classSet (fun i => (k' i : ZMod 3)) 1)).trans
        ((sl6b_SL_fieldEquiv (m := (classSet (fun i => (k' i : ZMod 3)) 1).card)
          (K := AdjoinRoot phi3) (K' := GaloisField 2 2) (by
            rw [natCard_adjoinRoot_phi3, GaloisField.card 2 2 (by norm_num)]; norm_num)).trans
          (reindexSL (K := GaloisField 2 2) (finCongr hΛcard))))
  · exact sl6b_disjoint_map_conj (disjoint_zeroBlk_classBlk ε k') A
  · intro h3
    have h3' : 3 ≤ n + 1 - 2 * ones k' := by simpa [hsupp] using h3
    rw [hcent]
    exact isComponentOf_map_conj (isComponentOf_zeroBlk ε k' hbin h3') A
  · intro h2
    have h2' : 2 ≤ ones k' := by simpa [hsupp2] using h2
    rw [hcent]
    exact isComponentOf_map_conj (isComponentOf_classBlk ε k' hbin h2') A
  · intro J hJ
    have hJ' : IsComponentOf (J.map (MulAut.conj A⁻¹).toMonoidHom)
        (Subgroup.centralizer ({Y'} : Set (SpecialLinearGroup (Fin (n + 1)) F2))) := by
      have h := isComponentOf_map_conj hJ A⁻¹
      rw [hcent] at h
      rwa [sl6b_map_conj_inv A (Subgroup.centralizer ({Y'} : Set _))] at h
    have hJJ : J = (J.map (MulAut.conj A⁻¹).toMonoidHom).map (MulAut.conj A).toMonoidHom := by
      rw [sl6b_map_inv_conj A J]
    rcases comp_eq_zeroBlk_or_classBlk ε k' hbin hJ' with h | h
    · left
      rw [hJJ, h]
    · right
      rw [hJJ, h]


private noncomputable def sl6b_quotCenter_equiv_projSL {G : Type} [Group G] {K : Type} [Field K]
    [Finite K] {a : ℕ} (e : G ≃* SpecialLinearGroup (Fin a) K) :
    G ⧸ Subgroup.center G ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL a K) :=
  (QuotientGroup.congr (Subgroup.center G)
      (Subgroup.center (SpecialLinearGroup (Fin a) K)) e (Subgroup.map_center_eq e)).trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj a K)

private theorem sl6b_card_quotCenter_of_iso_sl {G : Type} [Group G] {K : Type} [Field K]
    [Finite K] {a : ℕ} (e : G ≃* SpecialLinearGroup (Fin a) K) :
    Nat.card (G ⧸ Subgroup.center G) = Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL a K)) :=
  Nat.card_congr (sl6b_quotCenter_equiv_projSL e).toEquiv

private theorem sl6b_card_projSL_zero :
    Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 0 F2)) = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

private theorem sl6b_card_psl_two_eq {a : ℕ} (ha : a ≤ 6)
    (h : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL a F2)) = 20160) : a = 4 := by
  interval_cases a
  · rw [sl6b_card_projSL_zero] at h; norm_num at h
  · rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F2) (n := 1) (by norm_num),
      GaloisField.card 2 1 (by norm_num)] at h
    norm_num at h
  · rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F2) (n := 2) (by norm_num),
      GaloisField.card 2 1 (by norm_num)] at h
    norm_num at h
  · rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F2) (n := 3) (by norm_num),
      GaloisField.card 2 1 (by norm_num)] at h
    exact absurd h (by decide)
  · rfl
  · rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F2) (n := 5) (by norm_num),
      GaloisField.card 2 1 (by norm_num)] at h
    exact absurd h (by decide)
  · rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F2) (n := 6) (by norm_num),
      GaloisField.card 2 1 (by norm_num)] at h
    exact absurd h (by decide)

private theorem sl6b_card_psl_four_eq {b : ℕ} (hb : b ≤ 3)
    (h : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL b (GaloisField 2 2))) = 20160) :
    b = 3 := by
  interval_cases b
  · have h1 : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 0 (GaloisField 2 2))) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    rw [h1] at h; norm_num at h
  · rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL
        (K := GaloisField 2 2) (n := 1) (by norm_num),
      GaloisField.card 2 2 (by norm_num)] at h
    norm_num at h
  · rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL
        (K := GaloisField 2 2) (n := 2) (by norm_num),
      GaloisField.card 2 2 (by norm_num)] at h
    norm_num at h
  · rfl

private theorem sl6b_eq_A22_of_ggLabelIso {lab : LargeEvenLabel}
    (hiso : GGLabelIso lab ⟨.A, 2, 2⟩) : lab = ⟨.A, 2, 2⟩ := by
  rcases hiso with h | h | h | h | h | h | h | h
  · exact h
  · exact absurd h.2.1 (by decide)
  · exact absurd (congrArg LargeEvenLabel.rank h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.rank h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.1) (by decide)

theorem sl6b_supp_six
    {t : SpecialLinearGroup (Fin 6) F2} (ht3 : t ^ 3 = 1)
    {J : Subgroup (SpecialLinearGroup (Fin 6) F2)}
    (hcomp : IsComponentOf J
      (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 6) F2))))
    (hJ : GGHasLabel ⟨.A, 2, 2⟩ (J ⧸ Subgroup.center J)) :
    supp t = 6 := by
  have hsupp_le : supp t ≤ 6 := by
    rw [supp]
    exact Matrix.rank_le_height _
  have hcardJ : Nat.card (J ⧸ Subgroup.center J) = 20160 := by
    obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hJ
    letI : Field K := hKfield
    letI : Finite K := hKfin
    have hK4 : Nat.card K = 4 := by simpa using hKcard
    have h1 : Nat.card (J ⧸ Subgroup.center J) =
        Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)) := by
      rw [Nat.card_congr e.toEquiv, CFSG.Assembly.largeEvenSLGroup_eq_statedSL 3]
    rw [h1, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 3)
      (by norm_num), hK4]
    decide
  obtain ⟨Z, Λ, ⟨eZ⟩, ⟨eΛ⟩, _hdisj, _hZc, _hΛc, hdich⟩ :=
    sl6b_centralizer_blocks_equiv (n := 5) ht3
  rcases hdich J hcomp with hJZ | hJΛ
  ·
    subst hJZ
    exfalso
    have hcard : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL (6 - supp t) F2)) = 20160 := by
      rw [← hcardJ]
      exact (sl6b_card_quotCenter_of_iso_sl eZ).symm
    have ha : 6 - supp t ≤ 6 := by omega
    have ha4 : 6 - supp t = 4 := sl6b_card_psl_two_eq ha hcard
    have eL : J ⧸ Subgroup.center J ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 4 F2) := by
      rw [← ha4]
      exact sl6b_quotCenter_equiv_projSL eZ
    have hmod : CFSG.Open.StatedClassicalModel (J ⧸ Subgroup.center J) .PSL 4 2 1 :=
      ⟨by
        unfold CFSG.Open.StatedLieAdmissible
        refine ⟨Nat.prime_two, by norm_num, by norm_num, ?_, ?_⟩
        · intro hcon; exact absurd (congrArg Prod.fst hcon) (by norm_num)
        · intro hcon; exact absurd (congrArg Prod.fst hcon) (by norm_num),
       F2, inferInstance, inferInstance, by rw [GaloisField.card 2 1 (by norm_num)], ⟨eL⟩⟩
    have hlab31 : GGHasLabel ⟨.A, 3, 1⟩ (J ⧸ Subgroup.center J) := ggHasLabel_typeA hmod
    have hΛ31 : LargeEvenInLambda2 (⟨.A, 3, 1⟩ : LargeEvenLabel) := by
      simp [LargeEvenInLambda2]
    have hΛ22 : LargeEvenInLambda2 (⟨.A, 2, 2⟩ : LargeEvenLabel) := by
      simp [LargeEvenInLambda2]
    have hiso := ggLabelRigidInput_holds ⟨.A, 3, 1⟩ ⟨.A, 2, 2⟩ _
      hΛ31 hΛ22 hlab31 hJ
    exact absurd (sl6b_eq_A22_of_ggLabelIso hiso) (by simp)
  ·
    rw [hJΛ] at hcardJ
    have hcard : Nat.card
        (CFSG.Open.StatedProj (CFSG.Open.StatedSL (supp t / 2) (GaloisField 2 2))) = 20160 := by
      rw [← hcardJ]
      exact (sl6b_card_quotCenter_of_iso_sl eΛ).symm
    have hb : supp t / 2 ≤ 3 := by
      have h := Nat.div_le_div_right (c := 2) hsupp_le
      norm_num at h
      exact h
    have hb3 : supp t / 2 = 3 := sl6b_card_psl_four_eq hb hcard
    have hge6 : 6 ≤ supp t := by
      have h := Nat.div_mul_le_self (supp t) 2
      rw [hb3] at h
      simpa using h
    omega

private theorem sl6b_aligned_one :
    CoordSL.Aligned (g := phi3) (p := 3) root_phi3_pow_three
      (fun _ : Fin 3 => (1 : ZMod 3)) := by
  intro i j _ u _ _
  rfl

private theorem sl6b_nsSL_one_mem_classBlk
    (ε : Fin (5 + 1) ≃ (Fin (rootPB phi3).dim × Fin 3) ⊕ Fin 0) :
    SLNS.nsSL ε (C := rootMat phi3) det_rootMat_phi3 (fun _ : Fin 3 => 1) ∈
      classBlk (n := 5) (s := 3) (r := 0) ε (fun _ : Fin 3 => 1) := by
  haveI : NeZero (3 : ℕ) := ⟨by decide⟩
  obtain ⟨D, hDmem, hDeq⟩ := CoordSL.diag_mem_classBlock (g := phi3) (hζ := root_phi3_pow_three)
    (ε := ε) (hC := det_rootMat_phi3) (β := fun _ : Fin 3 => (1 : ZMod 3))
    (c := 1) (t := fun _ : Fin 3 => (1 : ZMod 3))
    (fun i hi => absurd rfl hi) (by decide)
  refine Subgroup.mem_map.mpr ⟨D, hDmem, ?_⟩
  rw [hDeq]
  exact SLNS.nsSL_congr ε det_rootMat_phi3 rootMat_phi3_pow_three (fun i => by decide)

private theorem sl6b_classBlk_commutant
    (ε : Fin (5 + 1) ≃ (Fin (rootPB phi3).dim × Fin 3) ⊕ Fin 0)
    {N : SpecialLinearGroup (Fin (5 + 1)) F2}
    (hN : ∀ x ∈ classBlk (n := 5) (s := 3) (r := 0) ε (fun _ : Fin 3 => 1), N * x = x * N) :
    N ∈ Subgroup.zpowers (SLNS.nsSL ε (C := rootMat phi3) det_rootMat_phi3
      (fun _ : Fin 3 => 1)) := by
  haveI : NeZero (3 : ℕ) := ⟨by decide⟩
  have hprim : IsPrimitiveRoot (AdjoinRoot.root phi3) 3 :=
    CoordSL.root_isPrimitiveRoot (g := phi3) Nat.prime_three natCast_three_ne_zero
      phi3_dvd_cyclotomic
  let β : Fin 3 → ZMod 3 := fun _ => 1
  have hal : CoordSL.Aligned (g := phi3) (p := 3) root_phi3_pow_three β := sl6b_aligned_one
  let Y : SpecialLinearGroup (Fin (5 + 1)) F2 :=
    SLNS.nsSL ε (C := rootMat phi3) det_rootMat_phi3 (fun i : Fin 3 => (β i).val)
  have hYsame : Y = SLNS.nsSL ε (C := rootMat phi3) det_rootMat_phi3 (fun _ : Fin 3 => 1) :=
    SLNS.nsSL_congr ε det_rootMat_phi3 rootMat_phi3_pow_three (fun i => by decide)
  have hYmem : Y ∈ classBlk (n := 5) (s := 3) (r := 0) ε (fun _ : Fin 3 => 1) := by
    rw [hYsame]
    exact sl6b_nsSL_one_mem_classBlk ε
  have hu : N * Y = Y * N := hN Y hYmem
  have hcls : ∀ i j (hij : i ≠ j), β i = β j → β i ≠ 0 → ∀ c : AdjoinRoot phi3,
      N * CoordSL.theta phi3 ε (Matrix.SpecialLinearGroup.transvection hij c) =
        CoordSL.theta phi3 ε (Matrix.SpecialLinearGroup.transvection hij c) * N := by
    intro i j hij _ _ c
    apply hN
    exact Subgroup.mem_map.mpr ⟨_, SLRep.transvection_mem_coordBlockSL
      (mem_classSet.mpr (by simp [β])) (mem_classSet.mpr (by simp [β])) hij c, rfl⟩
  let U : ((Fin 3 → AdjoinRoot phi3) × (Fin 0 → F2)) →ₗ[F2]
      ((Fin 3 → AdjoinRoot phi3) × (Fin 0 → F2)) :=
    CoordSL.frameForm phi3 ε (N : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F2)
  let μ : Fin 3 → AdjoinRoot phi3 := fun i => (U (Pi.single i (1 : AdjoinRoot phi3), 0)).1 i
  have hscal : ∀ i (hi : β i ≠ 0) (ξ : AdjoinRoot phi3),
      U (Pi.single i ξ, 0) = (Pi.single i (ξ * μ i), 0) := by
    intro i hi ξ
    exact CoordSL.apply_single_eq_of_comm_theta hprim hal hu hcls hi ξ
  have hμeq : ∀ i j : Fin 3, μ i = μ j := by
    intro i j
    by_cases hij : i = j
    · subst hij; rfl
    · have hTmem : CoordSL.theta phi3 ε
          (Matrix.SpecialLinearGroup.transvection hij (1 : AdjoinRoot phi3)) ∈
          classBlk (n := 5) (s := 3) (r := 0) ε (fun _ : Fin 3 => 1) :=
        Subgroup.mem_map.mpr ⟨_, SLRep.transvection_mem_coordBlockSL
          (mem_classSet.mpr (by simp [β])) (mem_classSet.mpr (by simp [β])) hij 1, rfl⟩
      have hNT := hN _ hTmem
      have hcomm : U.comp (CoordSL.blockAct phi3
            (Matrix.SpecialLinearGroup.transvection hij (1 : AdjoinRoot phi3))) =
          (CoordSL.blockAct phi3
            (Matrix.SpecialLinearGroup.transvection hij (1 : AdjoinRoot phi3))).comp U := by
        have h := congrArg (fun z : SpecialLinearGroup (Fin (5 + 1)) F2 =>
            CoordSL.frameForm phi3 ε (z : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F2)) hNT
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
          CoordSL.frameForm_mul, CoordSL.frameForm_mul, CoordSL.coe_theta,
          CoordSL.frameForm_thetaMat] at h
        exact h
      have happ := congrArg (fun φ => φ (Pi.single j (1 : AdjoinRoot phi3),
        (0 : Fin 0 → F2))) hcomm
      have hL : U ((Pi.single j (1 : AdjoinRoot phi3), (0 : Fin 0 → F2)) +
            (Pi.single i (1 : AdjoinRoot phi3), (0 : Fin 0 → F2))) =
          (Pi.single j (μ j) + Pi.single i (μ i), (0 : Fin 0 → F2)) := by
        rw [map_add, hscal j (by simp [β]) 1, hscal i (by simp [β]) 1]
        simp
      have hR : CoordSL.blockAct phi3
            (Matrix.SpecialLinearGroup.transvection hij (1 : AdjoinRoot phi3))
            (U (Pi.single j (1 : AdjoinRoot phi3), (0 : Fin 0 → F2))) =
          (Pi.single j (μ j) + Pi.single i (μ j), (0 : Fin 0 → F2)) := by
        rw [hscal j (by simp [β]) 1, CoordSL.blockAct_apply, CoordSL.transvection_mulVec]
        simp
      have h1 : U (CoordSL.blockAct phi3
            (Matrix.SpecialLinearGroup.transvection hij (1 : AdjoinRoot phi3))
            (Pi.single j (1 : AdjoinRoot phi3), (0 : Fin 0 → F2))) =
          (Pi.single j (μ j) + Pi.single i (μ i), (0 : Fin 0 → F2)) := by
        have hx : CoordSL.blockAct phi3
              (Matrix.SpecialLinearGroup.transvection hij (1 : AdjoinRoot phi3))
              (Pi.single j (1 : AdjoinRoot phi3), (0 : Fin 0 → F2)) =
            (Pi.single j (1 : AdjoinRoot phi3), (0 : Fin 0 → F2)) +
              (Pi.single i (1 : AdjoinRoot phi3), (0 : Fin 0 → F2)) := by
          rw [CoordSL.blockAct_apply, CoordSL.transvection_mulVec]
          simp
        rw [hx]; exact hL
      have h2 := happ
      simp only [LinearMap.comp_apply] at h2
      rw [h1, hR] at h2
      have h3 := congrFun (congrArg Prod.fst h2) i
      simp [Pi.single_eq_same, hij, Ne.symm hij] at h3
      exact h3
  let U' : ((Fin 3 → AdjoinRoot phi3) × (Fin 0 → F2)) →ₗ[F2]
      ((Fin 3 → AdjoinRoot phi3) × (Fin 0 → F2)) :=
    CoordSL.frameForm phi3 ε (((N⁻¹ : SpecialLinearGroup (Fin (5 + 1)) F2) :
      Matrix (Fin (5 + 1)) (Fin (5 + 1)) F2))
  have hU'U : U'.comp U = LinearMap.id := by
    dsimp only [U', U]
    rw [← CoordSL.frameForm_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, CoordSL.frameForm_one]
  have hUinj : Function.Injective U := by
    intro a b hab
    have h := congrArg (fun φ => φ (a - b)) hU'U
    simp only [LinearMap.comp_apply, LinearMap.id_apply, map_sub, hab, sub_self, map_zero] at h
    exact sub_eq_zero.mp h.symm
  have hμ0 : μ 0 ≠ 0 := by
    intro h0
    have hkill : U (Pi.single (0 : Fin 3) (1 : AdjoinRoot phi3), (0 : Fin 0 → F2)) = 0 := by
      rw [hscal 0 (by simp [β]) 1, h0]; simp
    have hzero : (Pi.single (0 : Fin 3) (1 : AdjoinRoot phi3), (0 : Fin 0 → F2)) = 0 :=
      hUinj (by rw [hkill, map_zero])
    have h1 : (Pi.single (0 : Fin 3) (1 : AdjoinRoot phi3) : Fin 3 → AdjoinRoot phi3) 0 =
        (0 : AdjoinRoot phi3) := by
      simpa using congrFun (congrArg Prod.fst hzero) 0
    exact one_ne_zero h1
  have hm_exists : ∃ m : ℕ, μ 0 = AdjoinRoot.root phi3 ^ m := by
    have hμpow : μ 0 ^ 3 = 1 := by
      haveI : Finite (AdjoinRoot phi3) := CoordSL.finite_adjoinRoot
      letI : Fintype (AdjoinRoot phi3) := Fintype.ofFinite _
      have hcard : Fintype.card (AdjoinRoot phi3) = 4 := by
        rw [← Nat.card_eq_fintype_card, natCard_adjoinRoot_phi3]
      have h := FiniteField.pow_card_sub_one_eq_one (μ 0) hμ0
      rwa [hcard] at h
    obtain ⟨m, -, hm⟩ := hprim.eq_pow_of_pow_eq_one hμpow
    exact ⟨m, hm.symm⟩
  obtain ⟨m, hm⟩ := hm_exists
  have hμall : ∀ i : Fin 3, μ i = AdjoinRoot.root phi3 ^ m := fun i => (hμeq i 0).trans hm
  have hUeq : U = CoordSL.torusAct' phi3 (fun _ : Fin 3 => m) := by
    refine CoordSL.frame_ext (fun j ξ => ?_) (fun w => ?_)
    · rw [hscal j (by simp [β]) ξ, hμall j, CoordSL.torusAct'_apply]
      refine Prod.ext ?_ rfl
      funext i
      by_cases hi : i = j
      · subst hi; simp [CoordSL.torusAct, mul_comm]
      · simp [CoordSL.torusAct, Pi.single_eq_of_ne hi]
    · have hw : ((0 : Fin 3 → AdjoinRoot phi3), w) = 0 := by
        refine Prod.ext rfl ?_
        exact Subsingleton.elim w 0
      rw [hw, map_zero, map_zero]
  have hNns : N = SLNS.nsSL ε (C := rootMat phi3) det_rootMat_phi3 (fun _ : Fin 3 => m) := by
    apply Subtype.ext
    apply CoordSL.frameForm_injective phi3 ε
    change CoordSL.frameForm phi3 ε (N : Matrix (Fin (5 + 1)) (Fin (5 + 1)) F2) =
      CoordSL.frameForm phi3 ε (SLNS.nsMat ε (rootMat phi3) (fun _ : Fin 3 => m))
    rw [CoordSL.frameForm_nsMat']
    exact hUeq
  have hYpow : Y ^ m = SLNS.nsSL ε (C := rootMat phi3) det_rootMat_phi3 (fun _ : Fin 3 => m) := by
    rw [SLNS.nsSL_pow]
    exact SLNS.nsSL_congr ε det_rootMat_phi3 rootMat_phi3_pow_three
      (fun i => by simp [β, ZMod.val_one])
  rw [hYsame.symm, hNns, ← hYpow]
  exact Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), zpow_natCast Y m⟩

theorem sl6b_component_commutant
    {t : SpecialLinearGroup (Fin 6) F2} (ht3 : t ^ 3 = 1)
    {J : Subgroup (SpecialLinearGroup (Fin 6) F2)}
    (hcomp : IsComponentOf J
      (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 6) F2))))
    (hJ : GGHasLabel ⟨.A, 2, 2⟩ (J ⧸ Subgroup.center J)) :
    ∀ M : SpecialLinearGroup (Fin 6) F2,
      (∀ j ∈ J, M * j = j * M) → M ∈ Subgroup.zpowers t := by
  intro M hMJ
  have hsupp : supp t = 6 := sl6b_supp_six ht3 hcomp hJ
  have hcardJ : Nat.card (J ⧸ Subgroup.center J) = 20160 := by
    obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hJ
    letI : Field K := hKfield
    letI : Finite K := hKfin
    have hK4 : Nat.card K = 4 := by simpa using hKcard
    have h1 : Nat.card (J ⧸ Subgroup.center J) =
        Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)) := by
      rw [Nat.card_congr e.toEquiv, CFSG.Assembly.largeEvenSLGroup_eq_statedSL 3]
    rw [h1, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 3)
      (by norm_num), hK4]
    decide
  obtain ⟨s, r, ε, A₀, k, htk⟩ := exists_frame_of_pow_three t ht3
  obtain ⟨M₀, k', hM₀, hk'⟩ := exists_conj_nsSL_binary ε k
  have hk'b : ∀ i, k' i = 0 ∨ k' i = 1 := fun i => (hk' i).1
  set A : SpecialLinearGroup (Fin 6) F2 := A₀ * M₀ with hA
  have htk' : t = A * SLNS.nsSL ε (C := rootMat phi3) det_rootMat_phi3 k' * A⁻¹ := by
    rw [htk]
    have hM₀' : SLNS.nsSL ε (C := rootMat phi3) det_rootMat_phi3 k =
        M₀ * SLNS.nsSL ε (C := rootMat phi3) det_rootMat_phi3 k' * M₀⁻¹ := by
      rw [← hM₀]; group
    rw [hM₀', hA]; group
  have hsupp2 : supp t = 2 * ones k' := by
    rw [htk', supp_conj, supp_nsSL, ones]
    congr 2
    refine Finset.filter_congr fun i _ => ?_
    rcases hk'b i with h | h <;> simp [h]
  have hones : ones k' = 3 := by omega
  have hcard_zero : (zeroCoords ε fun i => (k' i : ZMod 3)).card = 0 := by
    rw [card_zeroCoords ε k' hk'b]; omega
  have hzeroEmpty : (zeroCoords ε fun i => (k' i : ZMod 3)) = ∅ :=
    Finset.card_eq_zero.mp hcard_zero
  have hr : r = 0 := by
    by_contra hr
    let j : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    have hmem : (ε.symm (Sum.inr j) : Fin (5 + 1)) ∈
        zeroCoords ε (fun i => (k' i : ZMod 3)) :=
      mem_zeroCoords_inr (by rw [Equiv.apply_symm_apply])
    rw [hzeroEmpty] at hmem
    exact Finset.notMem_empty _ hmem
  have hs : s = 3 := by
    have h := frame_card ε
    omega
  have hk'one : ∀ i, k' i = 1 := by
    intro i
    have hmem : (ε.symm (Sum.inl ((⟨0, by rw [rootPB_phi3_dim]; norm_num⟩ :
        Fin (rootPB phi3).dim), i)) :
        Fin (5 + 1)) ∉ zeroCoords ε (fun i => (k' i : ZMod 3)) := by
      rw [hzeroEmpty]; exact Finset.notMem_empty _
    have hne : ((k' i : ZMod 3)) ≠ 0 := by
      intro h0
      exact hmem ((mem_zeroCoords_inl (by rw [Equiv.apply_symm_apply])).mpr h0)
    rcases hk'b i with h0 | h1
    · exact absurd (by rw [h0]; rfl : ((k' i : ZMod 3)) = 0) hne
    · exact h1
  subst hs
  subst hr
  have hYsame : SLNS.nsSL ε (C := rootMat phi3) det_rootMat_phi3 k' =
      SLNS.nsSL ε (C := rootMat phi3) det_rootMat_phi3 (fun _ : Fin 3 => 1) :=
    SLNS.nsSL_congr ε det_rootMat_phi3 rootMat_phi3_pow_three (fun i => by rw [hk'one i])
  have hcent : Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 6) F2)) =
      (Subgroup.centralizer ({SLNS.nsSL ε (C := rootMat phi3) det_rootMat_phi3 k'} :
        Set (SpecialLinearGroup (Fin 6) F2))).map (MulAut.conj A).toMonoidHom := by
    rw [htk']
    exact (map_conj_centralizer_singleton A _).symm
  have hJ'comp : IsComponentOf (J.map (MulAut.conj A⁻¹).toMonoidHom)
      (Subgroup.centralizer ({SLNS.nsSL ε (C := rootMat phi3) det_rootMat_phi3 k'} :
        Set (SpecialLinearGroup (Fin 6) F2))) := by
    have h := isComponentOf_map_conj hcomp A⁻¹
    rw [hcent] at h
    rwa [sl6b_map_conj_inv A (Subgroup.centralizer
      ({SLNS.nsSL ε (C := rootMat phi3) det_rootMat_phi3 k'} : Set _))] at h
  have hJ'class : J.map (MulAut.conj A⁻¹).toMonoidHom =
      classBlk (n := 5) (s := 3) (r := 0) ε (fun _ : Fin 3 => 1) := by
    rcases comp_eq_zeroBlk_or_classBlk ε k' hk'b hJ'comp with h | h
    · exfalso
      have hzero1 : Nat.card (zeroBlk ε k') = 1 := by
        rw [natCard_zeroBlk ε k' hk'b]
        have h6 : 5 + 1 - 2 * ones k' = 0 := by omega
        rw [h6]
        exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
      have hJ'card : Nat.card (J.map (MulAut.conj A⁻¹).toMonoidHom) = Nat.card J :=
        Subgroup.card_map_of_injective (MulAut.conj A⁻¹).injective
      have hJge : 20160 ≤ Nat.card J := by
        rw [← hcardJ]
        exact Nat.card_le_card_of_surjective (QuotientGroup.mk' (Subgroup.center J))
          (QuotientGroup.mk'_surjective (Subgroup.center J))
      rw [h, hzero1] at hJ'card
      omega
    · rw [h]
      have hk'fun : k' = fun _ : Fin 3 => 1 := funext hk'one
      rw [hk'fun]
  let N : SpecialLinearGroup (Fin 6) F2 := A⁻¹ * M * A
  have hNJ' : ∀ j ∈ J.map (MulAut.conj A⁻¹).toMonoidHom, N * j = j * N := by
    intro j hj
    obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.mp hj
    have h0 : M * j₀ = j₀ * M := hMJ j₀ hj₀
    have hconj : (MulAut.conj A⁻¹).toMonoidHom j₀ = A⁻¹ * j₀ * A := by
      change (MulAut.conj A⁻¹) j₀ = A⁻¹ * j₀ * A
      rw [MulAut.conj_apply, inv_inv]
    rw [hconj]
    dsimp only [N]
    calc (A⁻¹ * M * A) * (A⁻¹ * j₀ * A)
        = A⁻¹ * (M * j₀) * A := by group
      _ = A⁻¹ * (j₀ * M) * A := by rw [h0]
      _ = (A⁻¹ * j₀ * A) * (A⁻¹ * M * A) := by group
  have hclass_center : ∀ x ∈ classBlk (n := 5) (s := 3) (r := 0) ε (fun _ : Fin 3 => 1),
      N * x = x * N := by
    intro x hx
    rw [← hJ'class] at hx
    exact hNJ' x hx
  have hNmem : N ∈ Subgroup.zpowers (SLNS.nsSL ε (C := rootMat phi3) det_rootMat_phi3 k') := by
    have h := sl6b_classBlk_commutant ε hclass_center
    rwa [← hYsame] at h
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hNmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
  have hMN : (MulAut.conj A) N = M := by
    rw [show N = A⁻¹ * M * A from rfl, MulAut.conj_apply]; group
  rw [← hMN, ← hm, map_zpow (MulAut.conj A)]
  rw [htk']
  refine congrArg (fun z => z ^ m) ?_
  rw [MulAut.conj_apply]

end CFSG.StandardType

end
