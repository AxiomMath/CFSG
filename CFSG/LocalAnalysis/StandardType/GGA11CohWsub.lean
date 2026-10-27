module

public import CFSG.LocalAnalysis.StandardType.GGA11CohDefs
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRestNonsplit
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRepCases

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear CFSG.RankThree.CALinearPlane

namespace CFSG.StandardType.A11

private lemma a11ws_F2_card : Nat.card F2 = 2 := GaloisField.card 2 1 (by norm_num)

private lemma a11ws_F2_eq_zero_or_one (c : F2) : c = 0 ∨ c = 1 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    letI : Fintype F2 := Fintype.ofFinite F2
    have hcard : Fintype.card F2 = 2 := by
      rw [← Nat.card_eq_fintype_card]; exact a11ws_F2_card
    have h := FiniteField.pow_card_sub_one_eq_one c hc
    rw [hcard] at h
    simpa using h

private lemma a11ws_Om_det : Om.det = 1 := by
  rw [Matrix.det_fin_three]; simp [Om]

private lemma a11ws_Om_sub_one_unit : IsUnit (Om - 1) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h : (Om - 1).det = 1 := by rw [Matrix.det_fin_three]; simp [Om]
  rw [h]; exact isUnit_one

private def a11ws_pos9 (b a : Fin 3) : Fin 9 := ![![3,7,8],![0,1,2],![4,5,6]] b a

private def a11ws_idx9 (x : Fin 9) : Fin 3 := idxIn (Fin.castLE (by omega : 9 ≤ 12) x)

private def a11ws_blk9 (x : Fin 9) : Fin 3 :=
  ⟨(blk (Fin.castLE (by omega : 9 ≤ 12) x)).val, by fin_cases x <;> decide⟩

private noncomputable def a11ws_eps : Fin 9 ≃ (Fin 3 × Fin 3) ⊕ Fin 0 where
  toFun x := Sum.inl (a11ws_idx9 x, a11ws_blk9 x)
  invFun y := match y with
    | Sum.inl (a, b) => a11ws_pos9 b a
    | Sum.inr e => Fin.elim0 e
  left_inv x := by fin_cases x <;> decide
  right_inv y := by
    rcases y with ⟨⟨a,b⟩⟩ | e
    · fin_cases a <;> fin_cases b <;> decide
    · exact Fin.elim0 e

private def a11ws_J (s : Fin 3) : Finset (Fin 9) :=
  Finset.univ.filter (fun i => blk (Fin.castLE (by omega : 9 ≤ 12) i) ≠ s.castSucc)

private lemma a11ws_J_card (s : Fin 3) : (a11ws_J s).card = 6 := by
  fin_cases s <;> decide

private lemma a11ws_T9_eq_nsSL (s : Fin 3) :
    T9 s = SLNS.nsSL a11ws_eps a11ws_Om_det (SLNS.kT ({s} : Finset (Fin 3))) := by
  apply Subtype.ext
  ext a b
  fin_cases s <;> fin_cases a <;> fin_cases b <;>
    simp [T9, T9mat, SLNS.nsSL, SLNS.nsMat, SLNS.nsCore, SLNS.kT, a11ws_eps, a11ws_idx9,
      a11ws_blk9, blk, idxIn, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply]

private lemma a11ws_fixS_eq_J (s : Fin 3) :
    SLNS.fixS a11ws_eps ({s} : Finset (Fin 3)) = a11ws_J s := by
  ext x
  simp only [SLNS.fixS, Finset.mem_filter, Finset.mem_univ, true_and, a11ws_J]
  simp [SLNS.inT, a11ws_eps, a11ws_blk9, Finset.mem_singleton, Fin.ext_iff]

private lemma a11ws_blockOn_apply (J : Finset (Fin 9))
    (X : Matrix (Fin J.card) (Fin J.card) F2) (p q : Fin 9) :
    blockOn F2 J X p q =
      if hp : p ∈ J then
        (if hq : q ∈ J then X (J.equivFin ⟨p, hp⟩) (J.equivFin ⟨q, hq⟩)
         else if p = q then 1 else 0)
      else if p = q then 1 else 0 := by
  by_cases hp : p ∈ J
  · by_cases hq : q ∈ J
    · rw [dif_pos hp, dif_pos hq]; exact blockOn_apply_mem J X hp hq
    · rw [dif_pos hp, dif_neg hq]; exact blockOn_apply_not_mem J X (Or.inr hq)
  · rw [dif_neg hp]; exact blockOn_apply_not_mem J X (Or.inl hp)

private lemma a11ws_blockSLOn_transvection (J : Finset (Fin 9)) {i j : Fin J.card}
    (hij : i ≠ j) (a : F2) :
    blockSLOn F2 J (Matrix.SpecialLinearGroup.transvection hij a) =
      Matrix.SpecialLinearGroup.transvection (i := (J.equivFin.symm i).1)
        (j := (J.equivFin.symm j).1)
        (fun h => hij (J.equivFin.symm.injective (Subtype.ext h))) a := by
  apply Subtype.ext
  ext p q
  rw [coe_blockSLOn, a11ws_blockOn_apply]
  simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply,
    Matrix.one_apply]
  by_cases hp : p ∈ J
  · by_cases hq : q ∈ J
    · rw [dif_pos hp, dif_pos hq]
      have hpq : (J.equivFin ⟨p, hp⟩ = J.equivFin ⟨q, hq⟩) ↔ p = q := by
        constructor
        · intro h; exact congrArg Subtype.val (J.equivFin.injective h)
        · intro h; subst h; congr 1
      have hpi : (i = J.equivFin ⟨p, hp⟩) ↔ ((J.equivFin.symm i).1 = p) := by
        constructor
        · intro h; rw [h, Equiv.symm_apply_apply]
        · intro h
          have : J.equivFin.symm i = (⟨p, hp⟩ : ↥J) := Subtype.ext h
          calc i = J.equivFin (J.equivFin.symm i) := (J.equivFin.apply_symm_apply i).symm
            _ = J.equivFin ⟨p, hp⟩ := by rw [this]
      have hqj : (j = J.equivFin ⟨q, hq⟩) ↔ ((J.equivFin.symm j).1 = q) := by
        constructor
        · intro h; rw [h, Equiv.symm_apply_apply]
        · intro h
          have : J.equivFin.symm j = (⟨q, hq⟩ : ↥J) := Subtype.ext h
          calc j = J.equivFin (J.equivFin.symm j) := (J.equivFin.apply_symm_apply j).symm
            _ = J.equivFin ⟨q, hq⟩ := by rw [this]
      simp only [hpq, hpi, hqj]
    · rw [dif_pos hp, dif_neg hq]
      have hpi : ¬ ((J.equivFin.symm i).1 = p ∧ (J.equivFin.symm j).1 = q) := by
        rintro ⟨-, hqj⟩
        exact hq (hqj ▸ (J.equivFin.symm j).2)
      rw [if_neg hpi, add_zero]
  · rw [dif_neg hp]
    have hpi : ¬ ((J.equivFin.symm i).1 = p ∧ (J.equivFin.symm j).1 = q) := by
      rintro ⟨hpi, -⟩
      exact hp (hpi ▸ (J.equivFin.symm i).2)
    rw [if_neg hpi, add_zero]

private lemma a11ws_transvection_mem_Wsub (s : Fin 3) {i j : Fin 9}
    (hi : i ∈ a11ws_J s) (hj : j ∈ a11ws_J s) (hij : i ≠ j) (a : F2) :
    Matrix.SpecialLinearGroup.transvection hij a ∈ Wsub s := by
  rcases a11ws_F2_eq_zero_or_one a with ha | ha
  · subst ha
    rw [Matrix.SpecialLinearGroup.transvection_coeff_zero]
    exact Subgroup.one_mem _
  · subst ha
    apply Subgroup.subset_closure
    refine ⟨Fin.castLE (by omega : 9 ≤ 12) i, Fin.castLE (by omega : 9 ≤ 12) j,
      ?_, i.isLt, j.isLt, ?_, ?_, ?_⟩
    · intro h
      exact hij (Fin.castLE_injective (by omega : 9 ≤ 12) h)
    · simpa only [a11ws_J, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    · simpa only [a11ws_J, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    · rw [tv9, dif_pos ⟨i.isLt, j.isLt, fun h => hij (Fin.castLE_injective (by omega) h)⟩]

private lemma a11ws_Wsub_eq_coordBlockSL (s : Fin 3) :
    Wsub s = coordBlockSL F2 (a11ws_J s) := by
  apply le_antisymm
  · rw [Wsub]
    rw [Subgroup.closure_le]
    rintro g ⟨a, b, hab, ha, hb, hba, hbb, rfl⟩
    have hiJ : (⟨a.val, ha⟩ : Fin 9) ∈ a11ws_J s := by
      simp only [a11ws_J, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show Fin.castLE (by omega : 9 ≤ 12) (⟨a.val, ha⟩ : Fin 9) = a from Fin.ext rfl]
      exact hba
    have hjJ : (⟨b.val, hb⟩ : Fin 9) ∈ a11ws_J s := by
      simp only [a11ws_J, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show Fin.castLE (by omega : 9 ≤ 12) (⟨b.val, hb⟩ : Fin 9) = b from Fin.ext rfl]
      exact hbb
    have hij : (⟨a.val, ha⟩ : Fin 9) ≠ ⟨b.val, hb⟩ := by
      intro h
      have hval : a.val = b.val := congrArg (fun x : Fin 9 => x.val) h
      exact hab (Fin.ext hval)
    rw [tv9, dif_pos ⟨ha, hb, hab⟩]
    exact SLRep.transvection_mem_coordBlockSL hiJ hjJ hij 1
  · rw [← range_blockSLOn (k := F2) (J := a11ws_J s)]
    rintro g ⟨X, rfl⟩
    haveI : Nontrivial (Fin (a11ws_J s).card) := by
      rw [a11ws_J_card]; infer_instance
    refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun X : Matrix.SpecialLinearGroup (Fin (a11ws_J s).card) F2 => blockSLOn F2 (a11ws_J s) X ∈ Wsub s)
      X ?_ ?_ ?_
    · intro i j hij c hc
      have hc1 : c = 1 := by
        rcases a11ws_F2_eq_zero_or_one c with h | h
        · exact absurd h hc
        · exact h
      subst hc1
      have hdiag : Matrix.SpecialLinearGroup.diag2n hij (1 : F2) hc = 1 := by
        apply Subtype.ext
        ext k l
        rw [Matrix.SpecialLinearGroup.diag2n_coe, Matrix.SpecialLinearGroup.coe_one]
        simp
      rw [hdiag, map_one]
      exact Subgroup.one_mem _
    · intro i j hij a
      rw [a11ws_blockSLOn_transvection]
      exact a11ws_transvection_mem_Wsub s
        ((a11ws_J s).equivFin.symm i).2 ((a11ws_J s).equivFin.symm j).2
        (fun h => hij ((a11ws_J s).equivFin.symm.injective (Subtype.ext h))) a
    · intro A B hA hB
      rw [map_mul]
      exact (Wsub s).mul_mem hA hB

private lemma a11ws_center_SL_eq_bot (m : ℕ) (hm : 0 < m) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin m) F2) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    rcases a11ws_F2_eq_zero_or_one r with h | h
    · subst h
      rw [zero_pow (Nat.pos_iff_ne_zero.mp hm)] at hr
      exact absurd hr zero_ne_one
    · exact h
  apply Subtype.ext
  rw [← hrx, hr1]
  simp

private noncomputable def a11ws_blockEquiv (J : Finset (Fin 9)) :
    Matrix.SpecialLinearGroup (Fin J.card) F2 ≃* ↥(coordBlockSL F2 J) :=
  (MonoidHom.ofInjective (blockSLOn_injective (k := F2) J)).trans
    (MulEquiv.subgroupCongr (range_blockSLOn (k := F2) J))

private lemma a11ws_center_coordBlockSL_eq_bot (J : Finset (Fin 9)) (hJ : 0 < J.card) :
    Subgroup.center ↥(coordBlockSL F2 J) = ⊥ := by
  have hcSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin J.card) F2) = ⊥ :=
    a11ws_center_SL_eq_bot J.card hJ
  have hmap := CFSG.LieType.Universal.Unitary.map_center_mulEquiv (a11ws_blockEquiv J)
  rw [hcSL, Subgroup.map_bot] at hmap
  exact hmap.symm

private lemma a11ws_T9_mem_Wsub (s : Fin 3) {i : Fin 3} (hi : i ≠ s) :
    T9 i ∈ Wsub s := by
  rw [a11ws_Wsub_eq_coordBlockSL]
  rw [mem_coordBlockSL_iff]
  intro a b hab
  have hne : ¬ (blk (Fin.castLE (by omega : 9 ≤ 12) a) = i.castSucc ∧
      blk (Fin.castLE (by omega : 9 ≤ 12) b) = i.castSucc) := by
    rintro ⟨h1, h2⟩
    rcases hab with h | h
    · have ha : blk (Fin.castLE (by omega : 9 ≤ 12) a) = s.castSucc := by
        by_contra hc
        exact h (by simp only [a11ws_J, Finset.mem_filter, Finset.mem_univ, true_and]; exact hc)
      exact hi (Fin.castSucc_injective 3 (h1.symm.trans ha))
    · have hb : blk (Fin.castLE (by omega : 9 ≤ 12) b) = s.castSucc := by
        by_contra hc
        exact h (by simp only [a11ws_J, Finset.mem_filter, Finset.mem_univ, true_and]; exact hc)
      exact hi (Fin.castSucc_injective 3 (h2.symm.trans hb))
  change (if blk (Fin.castLE (by omega : 9 ≤ 12) a) = i.castSucc ∧
      blk (Fin.castLE (by omega : 9 ≤ 12) b) = i.castSucc
      then Om (idxIn (Fin.castLE (by omega : 9 ≤ 12) a)) (idxIn (Fin.castLE (by omega : 9 ≤ 12) b))
      else if a = b then 1 else 0) = if a = b then 1 else 0
  rw [if_neg hne]

theorem a11WsubInput_holds : A11WsubInput := by
  intro s
  have hW := a11ws_Wsub_eq_coordBlockSL s
  have hJpos : 0 < (a11ws_J s).card := by rw [a11ws_J_card]; norm_num
  have hle : Wsub s ≤ Subgroup.centralizer ({T9 s} : Set (SL 9)) := by
    obtain ⟨o, ho, hCo⟩ := SLNS.exists_pow_sub_one_eq_one (C := Om) a11ws_Om_sub_one_unit
    rw [hW, a11ws_T9_eq_nsSL, ← a11ws_fixS_eq_J]
    exact SLNS.coordBlockSL_le_centralizer a11ws_eps a11ws_Om_det ({s} : Finset (Fin 3)) ho hCo
  have hnorm : ((Wsub s).subgroupOf (Subgroup.centralizer ({T9 s} : Set (SL 9)))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    rintro c g hc hg
    rw [hW] at hc ⊢
    refine conj_mem_coordBlockSL ?_ hc
    have hcomm : T9 s * g = g * T9 s :=
      (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
    obtain ⟨o, ho, hCo⟩ := SLNS.exists_pow_sub_one_eq_one (C := Om) a11ws_Om_sub_one_unit
    have hP : compIndicator F2 (SLNS.fixS a11ws_eps ({s} : Finset (Fin 3))) * g =
        g * compIndicator F2 (SLNS.fixS a11ws_eps ({s} : Finset (Fin 3))) :=
      SLNS.compIndicator_comm_of_comm a11ws_eps a11ws_Om_det ({s} : Finset (Fin 3)) ho hCo
        (by rw [a11ws_T9_eq_nsSL] at hcomm; exact hcomm)
    rwa [a11ws_fixS_eq_J] at hP
  have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin (a11ws_J s).card) F2) :=
    CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (n := (a11ws_J s).card)
      (by rw [a11ws_J_card]; norm_num)
  have hqCoord : CFSG.IsQuasisimple ↥(coordBlockSL F2 (a11ws_J s)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (a11ws_blockEquiv (a11ws_J s)) hqSL
  have hq : Assembly.IsQuasisimple ↥(Wsub s) := by
    rw [hW]
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hqCoord
  have hcenter : Subgroup.center ↥(Wsub s) = ⊥ := by
    rw [hW]
    exact a11ws_center_coordBlockSL_eq_bot (a11ws_J s) hJpos
  exact ⟨⟨hle, IsSubnormal.step hle hnorm (IsSubnormal.refl _), hq⟩, hcenter,
    fun i hi => a11ws_T9_mem_Wsub s hi⟩

end CFSG.StandardType.A11

end
