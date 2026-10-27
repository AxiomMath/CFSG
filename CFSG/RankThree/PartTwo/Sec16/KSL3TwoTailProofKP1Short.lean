module

public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoTailProofKP1Model

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace ProofKS1624KP1

open CFSG CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR.BlockPar
open ProofKS1623Parab
open Matrix
open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] def parB (F : Type) [Field F] : Subgroup (projectiveSL 3 F) :=
  (parK F).map (proj 3 F)

@[expose] def radV (F : Type) [Field F] : Subgroup (projectiveSL 3 F) :=
  (radU F (flagSpace 3 F 2)).map (proj 3 F)

theorem radV_le_parB : radV F ≤ parB F :=
  Subgroup.map_mono radU_le_parK

theorem parB_le_normalizer_radV [Finite F] [CharP F 2] :
    parB F ≤ Subgroup.normalizer (radV F : Set (projectiveSL 3 F)) := by
  rw [radV, normalizer_radU]
  exact Subgroup.map_mono parK_le_stabilizer

@[expose] noncomputable def parKEquiv (F : Type) [Field F] : parK F ≃* parB F :=
  (MonoidHom.ofInjective (f := (proj 3 F).comp (parK F).subtype) (fun x y hxy =>
    Subtype.ext (injOn_proj_parK x.2 y.2 hxy))).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]; rfl))

theorem coe_parKEquiv (g : parK F) : (parKEquiv F g : projectiveSL 3 F) = proj 3 F g :=
  rfl

theorem exists_parK_of_mem_parB {x : projectiveSL 3 F} (hx : x ∈ parB F) :
    ∃ M ∈ parK F, proj 3 F M = x := hx

theorem exists_radU_of_mem_radV {x : projectiveSL 3 F} (hx : x ∈ radV F) :
    ∃ u ∈ radU F (flagSpace 3 F 2), proj 3 F u = x := hx

theorem parB_structure [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F) :
    CFSG.pCore 2 (parB F) = (radV F).subgroupOf (parB F) ∧
      CFSG.solvableRadical (parB F) = (radV F).subgroupOf (parB F) ∧
      Nonempty (parB F ⧸ CFSG.solvableRadical (parB F) ≃* projectiveSL 2 F) ∧
      Nat.card (radV F) = Nat.card F ^ 2 := by
  have hFe : Even (Nat.card F) := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card, Nat.even_iff, ← FiniteField.even_card_iff_char_two]
    exact ringChar.eq F 2
  have hB : parB F = inSubgroup perfectResidual ((stabilizer (flagSpace 3 F 2)).map (proj 3 F)) :=
    (perfectResidual_stabilizer_eq hF4).symm
  obtain ⟨-, -, -, hO2, hRad, ⟨hq⟩, -, hcard, -⟩ :=
    CFSG.LieType.linear_small_parabolic_perfect_residual_structure hFe (n := 3) (d := 2)
      (by norm_num) (by norm_num) (Or.inl ⟨rfl, hF4⟩) (flagSpace 3 F 2)
      (finrank_flagSpace (by norm_num)) (P := (stabilizer (flagSpace 3 F 2)).map (proj 3 F))
      (B := parB F) rfl hB
  exact ⟨hO2.trans hRad, hRad, ⟨hq⟩, hcard⟩

theorem pCoreOf_parB [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F) :
    CFSG.Open.pCoreOf 2 (parB F) = radV F := by
  rw [CFSG.Open.pCoreOf, (parB_structure hF4).1,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left radV_le_parB]

theorem eq_of_proj_eq {g h : SpecialLinearGroup (Fin 3) F} (hg : g ∈ parK F) (hh : h ∈ parK F)
    (hgh : proj 3 F g = proj 3 F h) : g = h :=
  injOn_proj_parK hg hh hgh

theorem parB_inf_centralizer_le :
    parB F ⊓ Subgroup.centralizer (radV F : Set (projectiveSL 3 F)) ≤ radV F := by
  rintro x ⟨hxB, hxC⟩
  obtain ⟨M, hM, rfl⟩ := exists_parK_of_mem_parB hxB
  have hfix : ∀ w : Fin 2 → F, blockAMat M *ᵥ w = w := by
    intro w
    have h1 := Subgroup.mem_centralizer_iff.mp hxC (proj 3 F (uVec w)) ⟨_, uVec_mem_radU w, rfl⟩
    have h2 : proj 3 F (M * uVec w * M⁻¹) = proj 3 F (uVec w) := by
      rw [map_mul, map_mul, map_inv, ← h1, mul_inv_cancel_right]
    have h3 := eq_of_proj_eq (mul_mem (mul_mem hM (radU_le_parK (uVec_mem_radU w)))
      (inv_mem hM)) (radU_le_parK (uVec_mem_radU w)) h2
    have h4 := radCoord_conj hM (uVec_mem_radU w)
    rw [h3, radCoord_uVec] at h4
    exact h4.symm
  have hA : blockA F ⟨M, hM⟩ = 1 := by
    apply Subtype.ext
    show blockAMat M = 1
    have c0 := hfix ![1, 0]
    have c1 := hfix ![0, 1]
    ext i j
    fin_cases i <;> fin_cases j
    · have := congrFun c0 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    · have := congrFun c1 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    · have := congrFun c0 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    · have := congrFun c1 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  exact ⟨M, (blockA_eq_one_iff _).mp hA, rfl⟩

theorem diagT_mulVec {t : F} (ht : t ≠ 0) (w : Fin 2 → F) :
    (diagT t ht).val *ᵥ w = ![t * w 0, t⁻¹ * w 1] := by
  ext i
  fin_cases i <;> simp [diagT, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

theorem radV_inf_centralizer_parB {t : F} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    radV F ⊓ Subgroup.centralizer (parB F : Set (projectiveSL 3 F)) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxV, hxC⟩
  obtain ⟨u, hu, rfl⟩ := exists_radU_of_mem_radV hxV
  set D := lev F (diagT t ht0) with hD
  have h1 := Subgroup.mem_centralizer_iff.mp hxC (proj 3 F D) ⟨D, lev_mem_parK _, rfl⟩
  have h2 : proj 3 F (D * u * D⁻¹) = proj 3 F u := by
    rw [map_mul, map_mul, map_inv, h1, mul_inv_cancel_right]
  have h3 := eq_of_proj_eq (mul_mem (mul_mem (lev_mem_parK _) (radU_le_parK hu))
    (inv_mem (lev_mem_parK _))) (radU_le_parK hu) h2
  have h4 := radCoord_conj (lev_mem_parK (diagT t ht0)) hu
  rw [← hD, h3, blockAMat_lev, diagT_mulVec] at h4
  have e0 := congrFun h4 0
  have e1 := congrFun h4 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
  have hw0 : radCoord u 0 = 0 := by
    have : (t - 1) * radCoord u 0 = 0 := by linear_combination -e0
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht1)
  have hw1 : radCoord u 1 = 0 := by
    have ht' : t⁻¹ - 1 ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      exact ht1 (inv_eq_one.mp h)
    have : (t⁻¹ - 1) * radCoord u 1 = 0 := by linear_combination -e1
    exact (mul_eq_zero.mp this).resolve_left ht'
  have hw : radCoord u = 0 := by
    ext i
    fin_cases i
    · exact hw0
    · exact hw1
  rw [Subgroup.mem_bot, ← uVec_radCoord hu, hw, uVec_zero, map_one]

theorem exists_ne_zero_ne_one [Finite F] (hF : 3 ≤ Nat.card F) : ∃ t : F, t ≠ 0 ∧ t ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have := Fintype.ofFinite F
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · simp [hcon x hx]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
  have h2 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
  omega

theorem exists_diagT_sub_one_mulVec_eq {t : F} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (w : Fin 2 → F) :
    ∃ w' : Fin 2 → F, ((diagT t ht0).val - 1) *ᵥ w' = w := by
  have hs1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hs2 : t⁻¹ - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact ht1 (inv_eq_one.mp h)
  refine ⟨![(t - 1)⁻¹ * w 0, (t⁻¹ - 1)⁻¹ * w 1], ?_⟩
  ext i
  fin_cases i
  · simp [diagT, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.diagonal_apply]
    field_simp
  · simp [diagT, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.diagonal_apply]
    field_simp

theorem commutator_radV_parB [Finite F] [CharP F 2] {t : F} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ⁅radV F, parB F⁆ = radV F := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv b hb
    have hbN := parB_le_normalizer_radV hb
    have h1 : b * v⁻¹ * b⁻¹ ∈ radV F := (Subgroup.mem_normalizer_iff.mp hbN _).mp (inv_mem hv)
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc b]
    exact mul_mem hv h1
  · rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.commutator_comm]
    obtain ⟨w', hw'⟩ := exists_diagT_sub_one_mulVec_eq ht0 ht1 (radCoord u)
    rw [← uVec_radCoord hu, ← hw', ← commutator_lev_uVec, map_mul, map_mul, map_inv, map_inv]
    exact Subgroup.commutator_mem_commutator ⟨_, lev_mem_parK _, rfl⟩
      ⟨_, uVec_mem_radU w', rfl⟩

theorem exists_sl2_first_column {w : Fin 2 → F} (hw : w ≠ 0) :
    ∃ M : SpecialLinearGroup (Fin 2) F, M.val *ᵥ Pi.single 0 1 = w := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1
      apply hw
      ext i
      fin_cases i
      · exact h0
      · exact h1
    refine ⟨⟨!![0, -(w 1)⁻¹; w 1, 0], by simp [Matrix.det_fin_two, h1]⟩, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![w 0, 0; w 1, (w 0)⁻¹], by simp [Matrix.det_fin_two, h0]⟩, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl2_mulVec_eq {w w' : Fin 2 → F} (hw : w ≠ 0) (hw' : w' ≠ 0) :
    ∃ A : SpecialLinearGroup (Fin 2) F, A.val *ᵥ w = w' := by
  obtain ⟨M, hM⟩ := exists_sl2_first_column hw
  obtain ⟨M', hM'⟩ := exists_sl2_first_column hw'
  refine ⟨M' * M⁻¹, ?_⟩
  have hinv : (M⁻¹).val * M.val = 1 := congrArg Subtype.val (inv_mul_cancel M)
  calc (M' * M⁻¹).val *ᵥ w = M'.val *ᵥ ((M⁻¹).val *ᵥ (M.val *ᵥ Pi.single 0 1)) := by
        rw [hM, show (M' * M⁻¹).val = M'.val * (M⁻¹).val from rfl, ← Matrix.mulVec_mulVec]
    _ = M'.val *ᵥ Pi.single 0 1 := by
        congr 1
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    _ = w' := hM'

theorem lev_conj_uVec (A : SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F) :
    lev F A * uVec w * (lev F A)⁻¹ = uVec (A.val *ᵥ w) := by
  have hc := conj_mem_radU (parK_le_stabilizer (lev_mem_parK A)) (uVec_mem_radU w)
  rw [← uVec_radCoord hc, radCoord_conj (lev_mem_parK A) (uVec_mem_radU w), radCoord_uVec,
    blockAMat_lev]

theorem eq_bot_or_eq_of_normalized {W' : Subgroup (projectiveSL 3 F)} (hWV : W' ≤ radV F)
    (hN : parB F ≤ Subgroup.normalizer (W' : Set (projectiveSL 3 F))) :
    W' = ⊥ ∨ W' = radV F := by
  by_cases hbot : W' = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨x, hxW⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨u, hu, hux⟩ := exists_radU_of_mem_radV (hWV hxW)
  have hw : radCoord u ≠ 0 := by
    intro h
    apply hx1'
    rw [← hux, ← uVec_radCoord hu, h, uVec_zero, map_one]
  apply le_antisymm hWV
  rintro _ ⟨u', hu', rfl⟩
  by_cases hw' : radCoord u' = 0
  · rw [← uVec_radCoord hu', hw', uVec_zero, map_one]
    exact one_mem _
  obtain ⟨A, hA⟩ := exists_sl2_mulVec_eq hw hw'
  have h1 : proj 3 F (lev F A) * (x : projectiveSL 3 F) * (proj 3 F (lev F A))⁻¹ ∈ W' :=
    (Subgroup.mem_normalizer_iff.mp (hN ⟨_, lev_mem_parK A, rfl⟩) _).mp hxW
  rw [← hux, ← map_inv, ← map_mul, ← map_mul, ← uVec_radCoord hu, lev_conj_uVec, hA,
    uVec_radCoord hu'] at h1
  exact h1

theorem isPerfect_parB [Finite F] (hF4 : 4 ≤ Nat.card F) : Group.IsPerfect (parB F) := by
  have := isPerfect_parK hF4
  exact Group.IsPerfect.ofSurjective (f := (parKEquiv F).toMonoidHom) (parKEquiv F).surjective

theorem isSimpleGroup_projectiveSL_two [Finite F] (hF4 : 4 ≤ Nat.card F) :
    IsSimpleGroup (projectiveSL 2 F) := by
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨s, hs⟩
  have := (CFSG.LinearGroups.linear_projective_simple (n := 2) le_rfl (Or.inr h4)).2.1
  exact (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 2 F)).isSimpleGroup

theorem isQuasisimple_parB [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple (parB F ⧸ CFSG.pCore 2 (parB F)) := by
  obtain ⟨hO2, hRad, ⟨hq⟩, -⟩ := parB_structure hF4
  set Q := parB F ⧸ CFSG.pCore 2 (parB F) with hQ
  have e : Q ≃* projectiveSL 2 F :=
    (QuotientGroup.quotientMulEquivOfEq (hO2.trans hRad.symm)).trans hq
  have hs := isSimpleGroup_projectiveSL_two hF4
  have hsQ : IsSimpleGroup Q := e.isSimpleGroup
  have hperf : Group.IsPerfect Q := by
    have := isPerfect_parB hF4
    exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 (parB F)))
      (QuotientGroup.mk'_surjective _)
  have hsQ' : IsSimpleGroup (Q ⧸ (⊥ : Subgroup Q)) :=
    (QuotientGroup.quotientBot (G := Q)).isSimpleGroup
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient (⊥ : Subgroup Q) bot_le
    hperf hsQ' ?_
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ a b : Q, a * b = b * a := by
    intro a b
    have := hcon (a : Q ⧸ (⊥ : Subgroup Q)) b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_bot,
      inv_mul_eq_one] at this
    exact this
  have htop : commutator Q = ⊤ := hperf.commutator_eq_top
  have hbot : commutator Q = ⊥ := by
    rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm, hcomm]
  obtain ⟨a, b, hab⟩ := exists_pair_ne Q
  apply hab
  have ha : a ∈ commutator Q := htop ▸ Subgroup.mem_top a
  have hb : b ∈ commutator Q := htop ▸ Subgroup.mem_top b
  rw [hbot, Subgroup.mem_bot] at ha hb
  rw [ha, hb]

theorem radV_ne_bot : radV F ≠ ⊥ := by
  intro h
  have h1 : proj 3 F (uVec ![1, 0]) ∈ radV F := ⟨_, uVec_mem_radU _, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  have h2 := eq_of_proj_eq (radU_le_parK (uVec_mem_radU ![1, 0])) (one_mem _)
    (h1.trans (map_one _).symm)
  have := congrArg radCoord h2
  rw [radCoord_uVec, ← uVec_zero, radCoord_uVec] at this
  have := congrFun this 0
  simp at this

theorem isShort2_parB [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F) :
    CFSG.QuasithinUnique.IsShort2 (parB F) := by
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one (F := F) (by omega)
  have hQ : CFSG.QuasithinUnique.blockQ (parB F) = radV F := pCoreOf_parB hF4
  have hU : CFSG.QuasithinUnique.blockU (parB F) = radV F := by
    rw [CFSG.QuasithinUnique.blockU, hQ]
    exact commutator_radV_parB ht0 ht1
  have hZ : CFSG.QuasithinUnique.blockZ (parB F) = ⊥ := by
    rw [CFSG.QuasithinUnique.blockZ, hU]
    exact radV_inf_centralizer_parB ht0 ht1
  have hel := isElemAbelian_radU (F := F) (flagSpace 3 F 2)
  refine ⟨?_, ?_, ⟨?_, ?_⟩, Or.inl (isQuasisimple_parB hF4), ?_, ?_⟩
  · intro N _ hN
    have hperf := isPerfect_parB hF4
    by_contra hne
    have : Nontrivial (parB F ⧸ N) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      apply hne
      rw [eq_top_iff]
      intro x _
      have : (x : parB F ⧸ N) = 1 := Subsingleton.elim _ _
      rwa [QuotientGroup.eq_one_iff] at this
    have hperfQ : Group.IsPerfect (parB F ⧸ N) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent (parB F ⧸ N) := hN.isNilpotent
    exact Group.IsPerfect.not_isSolvable (parB F ⧸ N) inferInstance
  · show parB F ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 (parB F) : Set _) ≤
      CFSG.Open.pCoreOf 2 (parB F)
    rw [pCoreOf_parB hF4]
    exact parB_inf_centralizer_le
  · rw [hU, hQ]
    refine le_inf le_rfl fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    exact congrArg Subtype.val (hel.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  · intro x hx
    rw [hU] at hx
    exact hel.2 x hx
  · rw [hZ, hU]
    exact bot_lt_iff_ne_bot.mpr radV_ne_bot
  · intro W' hZW hWU hN
    rw [hZ]
    rw [hU] at hWU ⊢
    exact eq_bot_or_eq_of_normalized hWU hN

@[expose] def radCoordHom (F : Type) [Field F] :
    radU F (flagSpace 3 F 2) →* Multiplicative (Fin 2 → F) where
  toFun u := Multiplicative.ofAdd (radCoord u.1)
  map_one' := by
    show Multiplicative.ofAdd (radCoord (1 : SpecialLinearGroup (Fin 3) F)) = 1
    rw [← uVec_zero, radCoord_uVec]
    rfl
  map_mul' u v := by
    show Multiplicative.ofAdd (radCoord (u.1 * v.1)) = _
    rw [radCoord_mul u.2 v.2]
    rfl

@[expose] noncomputable def radUEquiv (F : Type) [Field F] : radU F (flagSpace 3 F 2) ≃* radV F :=
  (MonoidHom.ofInjective (f := (proj 3 F).comp (radU F (flagSpace 3 F 2)).subtype)
    (fun x y hxy => Subtype.ext (injOn_proj_parK (radU_le_parK x.2) (radU_le_parK y.2) hxy))).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]; rfl))

theorem coe_radUEquiv (u : radU F (flagSpace 3 F 2)) :
    (radUEquiv F u : projectiveSL 3 F) = proj 3 F u :=
  rfl

theorem proj_parKEquiv_symm (x : parB F) : proj 3 F ((parKEquiv F).symm x).1 = x := by
  rw [← coe_parKEquiv, MulEquiv.apply_symm_apply]

theorem proj_radUEquiv_symm (x : radV F) : proj 3 F ((radUEquiv F).symm x).1 = x := by
  rw [← coe_radUEquiv, MulEquiv.apply_symm_apply]

theorem isLin2Type_parB [Finite F] [CharP F 2] {m : ℕ} (hFc : Nat.card F = 2 ^ m)
    (hF4 : 4 ≤ Nat.card F) : CFSG.QuasithinUnique.IsLin2Type (parB F) m := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one (F := F) (by omega)
  have hQ : CFSG.QuasithinUnique.blockQ (parB F) = radV F := pCoreOf_parB hF4
  have hU : CFSG.QuasithinUnique.blockU (parB F) = radV F := by
    rw [CFSG.QuasithinUnique.blockU, hQ]
    exact commutator_radV_parB ht0 ht1
  have hZ : CFSG.QuasithinUnique.blockZ (parB F) = ⊥ := by
    rw [CFSG.QuasithinUnique.blockZ, hU]
    exact radV_inf_centralizer_parB ht0 ht1
  refine ⟨F, inferInstance, inferInstance, by rw [← Nat.card_eq_fintype_card, hFc], ?_⟩
  set α : parB F →* SpecialLinearGroup (Fin 2) F :=
    (blockA F).comp (parKEquiv F).symm.toMonoidHom with hα
  refine ⟨α, ?_, ?_, ?_⟩
  · intro A
    obtain ⟨g, hg⟩ := blockA_surjective A
    exact ⟨parKEquiv F g, by rw [hα, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, hg]⟩
  · rw [(parB_structure hF4).1]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hα, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, blockA_eq_one_iff]
    constructor
    · intro hx
      rw [← proj_parKEquiv_symm x]
      exact ⟨_, hx, rfl⟩
    · intro hx
      obtain ⟨u, hu, hux⟩ := exists_radU_of_mem_radV hx
      have := eq_of_proj_eq ((parKEquiv F).symm x).2 (radU_le_parK hu)
        ((proj_parKEquiv_symm x).trans hux.symm)
      rw [this]
      exact hu
  set β : CFSG.QuasithinUnique.blockU (parB F) →* Multiplicative (Fin 2 → F) :=
    (radCoordHom F).comp ((radUEquiv F).symm.toMonoidHom.comp
      (MulEquiv.subgroupCongr hU).toMonoidHom) with hβ
  refine ⟨β, ?_, ?_, ?_⟩
  · intro w
    refine ⟨(MulEquiv.subgroupCongr hU).symm (radUEquiv F ⟨uVec (Multiplicative.toAdd w),
      uVec_mem_radU _⟩), ?_⟩
    rw [hβ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
    show Multiplicative.ofAdd (radCoord (uVec (Multiplicative.toAdd w))) = w
    rw [radCoord_uVec]
    rfl
  · rw [hZ, Subgroup.bot_subgroupOf]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      have h1 : radCoord ((radUEquiv F).symm ((MulEquiv.subgroupCongr hU) x)).1 = 0 :=
        congrArg Multiplicative.toAdd hx
      have h2 := uVec_radCoord ((radUEquiv F).symm ((MulEquiv.subgroupCongr hU) x)).2
      rw [h1, uVec_zero] at h2
      apply Subtype.ext
      have h3 := proj_radUEquiv_symm ((MulEquiv.subgroupCongr hU) x)
      rw [← h2, map_one] at h3
      exact h3.symm
    · rintro rfl
      exact map_one β
  · intro ℓ u v huv
    set M := ((parKEquiv F).symm ℓ).1 with hM
    set u' := ((radUEquiv F).symm ((MulEquiv.subgroupCongr hU) u)).1 with hu'
    set v' := ((radUEquiv F).symm ((MulEquiv.subgroupCongr hU) v)).1 with hv'
    have hMK : M ∈ parK F := ((parKEquiv F).symm ℓ).2
    have hu'U : u' ∈ radU F (flagSpace 3 F 2) := ((radUEquiv F).symm _).2
    have hv'U : v' ∈ radU F (flagSpace 3 F 2) := ((radUEquiv F).symm _).2
    have hpM : proj 3 F M = ℓ := proj_parKEquiv_symm ℓ
    have hpu : proj 3 F u' = u := proj_radUEquiv_symm ((MulEquiv.subgroupCongr hU) u)
    have hpv : proj 3 F v' = v := proj_radUEquiv_symm ((MulEquiv.subgroupCongr hU) v)
    have hv'eq : v' = M * u' * M⁻¹ := by
      refine eq_of_proj_eq (radU_le_parK hv'U)
        (mul_mem (mul_mem hMK (radU_le_parK hu'U)) (inv_mem hMK)) ?_
      rw [hpv, map_mul, map_mul, map_inv, hpM, hpu]
      exact huv
    show radCoord v' = (blockAMat M) *ᵥ radCoord u'
    rw [hv'eq]
    exact radCoord_conj hMK hu'U

end ProofKS1624KP1

end CFSG.RankThree.PartTwo.Sec16
