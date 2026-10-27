module

public import CFSG.Quasithin.Background.SimsF5Defs
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

section Reflections

open Matrix CFSG.Fischer.Classification CFSG.Fischer.Classification.F3

theorem isGenLie_of_mulEquiv_U2 {H : Type} [Group H]
    (e : H ≃* CFSG.Fischer.Classification.Unitary.U2 4) :
    CFSG.ASVolI.ChF.IsGenLie H CFSG.ASVolI.ChF.GLKind.U4 2 1 :=
  ⟨Nat.prime_two, le_rfl, CFSG.Blueprint.Fischer.K, inferInstance, inferInstance,
    by simpa using CFSG.Fischer.Classification.Unitary.card_K,
    ⟨e.trans CFSG.GH74.Exceptional.u2FourEquiv⟩⟩

theorem nonempty_mulEquiv_PSp43_of_isGenLie {G : Type} [Group G]
    (h : CFSG.ASVolI.ChF.IsGenLie G CFSG.ASVolI.ChF.GLKind.U4 2 1) :
    Nonempty (G ≃* CFSG.GH74.Exceptional.PSp43) := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : Fintype CFSG.Blueprint.Fischer.K := Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card CFSG.Blueprint.Fischer.K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      CFSG.Fischer.Classification.Unitary.card_K]
  exact ⟨(e.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 4 (2 ^ 1))).trans
      (CFSG.GH74.Exceptional.u2FourEquiv.symm.trans CFSG.GH74.Exceptional.psp43EquivU2.symm)⟩

theorem I5Form_eq_dotProduct (x y : Fin 5 → ZMod 3) : I5Form x y = x ⬝ᵥ y :=
  I5Form_apply x y

theorem I5Form_self_eq_qV5 (v : Fin 5 → ZMod 3) : I5Form v v = qV5 v := by
  rw [I5Form_apply, qV5]
  exact Finset.sum_congr rfl fun i _ => (sq (v i)).symm

theorem refl_I5_mulVec {v : Fin 5 → ZMod 3} (hv : qV5 v = 1) (x : Fin 5 → ZMod 3) :
    ((refl I5Form v : GL (Fin 5) (ZMod 3)) : Matrix (Fin 5) (Fin 5) (ZMod 3)) *ᵥ x =
      x - (2 * (x ⬝ᵥ v)) • v := by
  have h := act_refl (f := I5Form) (by rw [I5Form_self_eq_qV5]; exact hv) x
  rw [act_def, I5Form_eq_dotProduct] at h
  rw [h, show (2 : ZMod 3) = -1 by decide, neg_one_mul, neg_smul, sub_neg_eq_add]

theorem I5Form_single (i : Fin 5) : I5Form (Pi.single i 1) (Pi.single i 1) = 1 := by
  rw [I5Form_apply]
  simp [Pi.single_apply]

theorem I5Form_apply_single (i : Fin 5) (x : Fin 5 → ZMod 3) :
    I5Form x (Pi.single i 1) = x i := by
  rw [I5Form_apply]
  simp [Pi.single_apply]

theorem act_refl_single (i : Fin 5) (x : Fin 5 → ZMod 3) (j : Fin 5) :
    act (refl I5Form (Pi.single i 1)) x j = if j = i then -x j else x j := by
  rw [act_refl (I5Form_single i), I5Form_apply_single]
  by_cases hji : j = i
  · subst hji
    simp
    generalize x j = a
    revert a
    decide
  · simp [Pi.single_apply, hji]

theorem neg_one_eq_prod_refl :
    (-1 : GL (Fin 5) (ZMod 3)) =
      refl I5Form (Pi.single 0 1) * refl I5Form (Pi.single 1 1) * refl I5Form (Pi.single 2 1) *
        refl I5Form (Pi.single 3 1) * refl I5Form (Pi.single 4 1) := by
  refine (gl_ext fun x => ?_).symm
  funext j
  simp only [act_mul, act_neg_one, act_refl_single]
  fin_cases j <;> simp

theorem neg_one_mem_reflGroup_I5 : (-1 : GL (Fin 5) (ZMod 3)) ∈ reflGroup I5Form := by
  rw [neg_one_eq_prod_refl]
  exact mul_mem (mul_mem (mul_mem (mul_mem (refl_mem_reflGroup _) (refl_mem_reflGroup _))
    (refl_mem_reflGroup _)) (refl_mem_reflGroup _)) (refl_mem_reflGroup _)

@[expose] def negOneR : reflGroup I5Form :=
  ⟨-1, neg_one_mem_reflGroup_I5⟩

@[simp]
theorem coe_negOneR : ((negOneR : reflGroup I5Form) : GL (Fin 5) (ZMod 3)) = -1 :=
  rfl

theorem center_reflGroup_I5 :
    Subgroup.center (reflGroup I5Form) = Subgroup.zpowers negOneR := by
  refine le_antisymm (fun g hg => ?_) ?_
  · rcases coe_eq_of_mem_center isF3Form_I5Form (by norm_num) hg with h | h
    · rw [show g = 1 from Subtype.ext (by simpa using h)]
      exact one_mem _
    · rw [show g = negOneR from Subtype.ext h]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (by simp)

@[expose] def rPlus : Subgroup (GL (Fin 5) (ZMod 3)) :=
  reflGroup I5Form ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin 5) (ZMod 3) →* (ZMod 3)ˣ).ker

theorem mem_rPlus {g : GL (Fin 5) (ZMod 3)} :
    g ∈ rPlus ↔ g ∈ reflGroup I5Form ∧ (g : Matrix (Fin 5) (Fin 5) (ZMod 3)).det = 1 := by
  rw [rPlus, Subgroup.mem_inf, MonoidHom.mem_ker]
  refine and_congr_right fun _ => ?_
  rw [← Units.val_inj, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]

theorem rPlus_le_reflGroup : rPlus ≤ reflGroup I5Form :=
  inf_le_left

theorem det_neg_one_GL5 :
    ((-1 : GL (Fin 5) (ZMod 3)) : Matrix (Fin 5) (Fin 5) (ZMod 3)).det = -1 := by
  rw [Units.val_neg, Units.val_one, Matrix.det_neg, Fintype.card_fin, Matrix.det_one]
  decide

theorem negOneR_mem_center : negOneR ∈ Subgroup.center (reflGroup I5Form) := by
  rw [center_reflGroup_I5]
  exact Subgroup.mem_zpowers _

@[expose] def rPlusToR3 : ↥rPlus →* R3 I5Form :=
  (QuotientGroup.mk' (Subgroup.center (reflGroup I5Form))).comp
    (Subgroup.inclusion rPlus_le_reflGroup)

theorem rPlusToR3_injective : Function.Injective rPlusToR3 := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hc : Subgroup.inclusion rPlus_le_reflGroup a ∈ Subgroup.center (reflGroup I5Form) :=
    (QuotientGroup.eq_one_iff _).1 ha
  have hdet := (mem_rPlus.1 a.2).2
  rcases coe_eq_of_mem_center isF3Form_I5Form (by norm_num) hc with h | h
  · exact Subtype.ext h
  · exfalso
    have h1 : (a : GL (Fin 5) (ZMod 3)) = -1 := h
    rw [h1, det_neg_one_GL5] at hdet
    exact absurd hdet (by decide)

theorem rPlusToR3_surjective : Function.Surjective rPlusToR3 := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hd : ((g : GL (Fin 5) (ZMod 3)) : Matrix (Fin 5) (Fin 5) (ZMod 3)).det = 1 ∨
      ((g : GL (Fin 5) (ZMod 3)) : Matrix (Fin 5) (Fin 5) (ZMod 3)).det = -1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    generalize Matrix.GeneralLinearGroup.det (g : GL (Fin 5) (ZMod 3)) = u
    revert u
    decide
  rcases hd with hd | hd
  · exact ⟨⟨(g : GL (Fin 5) (ZMod 3)), mem_rPlus.2 ⟨g.2, hd⟩⟩, rfl⟩
  · refine ⟨⟨((negOneR * g : reflGroup I5Form) : GL (Fin 5) (ZMod 3)),
      mem_rPlus.2 ⟨(negOneR * g).2, ?_⟩⟩, ?_⟩
    · rw [Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, coe_negOneR, det_neg_one_GL5, hd]
      decide
    · show (QuotientGroup.mk (negOneR * g) : R3 I5Form) = QuotientGroup.mk g
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff negOneR).2 negOneR_mem_center, one_mul]

@[expose] def rPlusEquivR3 : ↥rPlus ≃* R3 I5Form :=
  MulEquiv.ofBijective rPlusToR3 ⟨rPlusToR3_injective, rPlusToR3_surjective⟩

noncomputable def rPlusEquiv : ↥rPlus ≃* CFSG.Fischer.Classification.Unitary.U2 4 :=
  rPlusEquivR3.trans (exists_mulEquiv_U2_four_R3_I5.choose).symm

theorem card_rPlus : Nat.card ↥rPlus = 25920 := by
  rw [Nat.card_congr rPlusEquiv.toEquiv]
  exact CFSG.GH74.Exceptional.card_U2_four

theorem isGenLie_rPlus : CFSG.ASVolI.ChF.IsGenLie ↥rPlus CFSG.ASVolI.ChF.GLKind.U4 2 1 :=
  isGenLie_of_mulEquiv_U2 rPlusEquiv

theorem isSimpleGroup_U2_four : IsSimpleGroup (CFSG.Fischer.Classification.Unitary.U2 4) := by
  have : IsSimpleGroup CFSG.GH74.Exceptional.PSp43 :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 3) 2 (by norm_num)
      (Or.inr (Or.inl ⟨by rw [Nat.card_eq_fintype_card, ZMod.card], le_rfl⟩))
  exact CFSG.GH74.Exceptional.psp43EquivU2.symm.isSimpleGroup

theorem isSimpleGroup_rPlus : IsSimpleGroup ↥rPlus := by
  have := isSimpleGroup_U2_four
  exact rPlusEquiv.isSimpleGroup

theorem commutator_rPlus : commutator ↥rPlus = ⊤ := by
  have := isSimpleGroup_rPlus
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥rPlus)).resolve_left fun hb => ?_
  have hc : IsMulCommutative ↥rPlus := (commutator_eq_bot_iff _).1 hb
  have hp := (Group.is_simple_iff_prime_card (α := ↥rPlus)).1 this
  rw [card_rPlus] at hp
  norm_num at hp

theorem qV5_mulVec_of_mem_reflGroup {g : GL (Fin 5) (ZMod 3)} (hg : g ∈ reflGroup I5Form)
    (v : Fin 5 → ZMod 3) : qV5 ((g : Matrix (Fin 5) (Fin 5) (ZMod 3)) *ᵥ v) = qV5 v := by
  have h := isIsom_of_mem isF3Form_I5Form hg v v
  rwa [I5Form_self_eq_qV5, I5Form_self_eq_qV5] at h

theorem reflGroup_I5_le_isometryCore : reflGroup I5Form ≤ CFSG.MatrixModel.isometryCore qV5 :=
  fun _ hg => Subgroup.subset_closure (qV5_mulVec_of_mem_reflGroup hg)

theorem rPlus_le_isometryCore : rPlus ≤ CFSG.MatrixModel.isometryCore qV5 :=
  fun _ hg => reflGroup_I5_le_isometryCore (rPlus_le_reflGroup hg)

theorem rPlus_le_statedOmega : rPlus ≤ CFSG.Open.StatedOmega qV5 := by
  have h : ⁅rPlus, rPlus⁆ = rPlus :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 commutator_rPlus)
  calc rPlus = ⁅rPlus, rPlus⁆ := h.symm
    _ ≤ ⁅CFSG.MatrixModel.isometryCore qV5, CFSG.MatrixModel.isometryCore qV5⁆ :=
        Subgroup.commutator_mono rPlus_le_isometryCore rPlus_le_isometryCore
    _ = CFSG.Open.StatedOmega qV5 := rfl

end Reflections

section AutPSp43

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher hiding conjAut
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher renaming conjAut → spConjAut

theorem spConjAut_eq_one_of_mem_center {r : ℕ} {K : Type} [Field K] (A : gsp r K)
    (hA : (A : GL (Fin r ⊕ Fin r) K) ∈ Subgroup.center (GL (Fin r ⊕ Fin r) K)) :
    spConjAut r K A = 1 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MulAut.one_apply]
  have hg : conjSp r K A g = g := Subtype.ext <| by
    rw [coe_conjSp, ← Subgroup.mem_center_iff.1 hA (g : GL (Fin r ⊕ Fin r) K),
      mul_inv_cancel_right]
  have h := conjAut_proj A g
  rw [hg] at h
  exact h

theorem spConjAut_surjective_zmod_three : Function.Surjective (spConjAut 2 (ZMod 3)) := by
  intro α
  obtain ⟨A, σ, hα⟩ := CFSG.RankThree.PartTwo.KFacts.psp4_odd_automorphism_normal_form
    (K := ZMod 3) (by rw [ZMod.ringChar_zmod_n]; norm_num) α
  refine ⟨A, ?_⟩
  rw [hα, Subsingleton.elim σ 1, map_one, mul_one]

theorem card_gsp_two_zmod_three_le : Nat.card (gsp 2 (ZMod 3)) ≤ 2 * 51840 := by
  have h := Subgroup.card_ker_mul_card_range (multiplier 2 (ZMod 3))
  rw [ker_multiplier,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (statedSp_le_gsp (r := 2) (K := ZMod 3))).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two_zmod_three] at h
  have hr : Nat.card (multiplier 2 (ZMod 3)).range ≤ 2 := by
    have := Subgroup.card_le_card_group (multiplier 2 (ZMod 3)).range
    have h2 : Nat.card (ZMod 3)ˣ = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
    omega
  rw [← h]
  exact Nat.mul_le_mul_left _ hr

@[expose] def negOneGsp : gsp 2 (ZMod 3) :=
  ⟨-1, statedSp_le_gsp CFSG.GH74.Exceptional.neg_one_mem_statedSp⟩

theorem negOneGsp_ne_one : negOneGsp ≠ 1 := by
  intro h
  have h0 := congrArg (fun g : gsp 2 (ZMod 3) =>
    ((g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3))
      (.inl 0) (.inl 0)) h
  simp [negOneGsp] at h0
  exact absurd h0 (by decide)

theorem negOneGsp_mem_ker : negOneGsp ∈ (spConjAut 2 (ZMod 3)).ker := by
  rw [MonoidHom.mem_ker]
  refine spConjAut_eq_one_of_mem_center _ ?_
  rw [Subgroup.mem_center_iff]
  intro g
  change g * -1 = -1 * g
  rw [mul_neg_one, neg_one_mul]

theorem card_mulAut_PSp43_le : Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) ≤ 51840 := by
  have h1 : Nat.card (spConjAut 2 (ZMod 3)).ker *
      Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) = Nat.card (gsp 2 (ZMod 3)) :=
    Subgroup.card_ker_mul_card_of_surjective spConjAut_surjective_zmod_three
  have h2 : 2 ≤ Nat.card (spConjAut 2 (ZMod 3)).ker := by
    refine (Subgroup.one_lt_card_iff_ne_bot _).2 fun hbot => ?_
    have := negOneGsp_mem_ker
    rw [hbot, Subgroup.mem_bot] at this
    exact negOneGsp_ne_one this
  have h3 := card_gsp_two_zmod_three_le
  have h4 := Nat.mul_le_mul_right (Nat.card (MulAut CFSG.GH74.Exceptional.PSp43)) h2
  omega

theorem card_mulAut_of_mulEquiv_PSp43 {G : Type} [Group G]
    (e : G ≃* CFSG.GH74.Exceptional.PSp43) : Nat.card (MulAut G) ≤ 51840 := by
  rw [Nat.card_congr (MulAut.congr e).toEquiv]
  exact card_mulAut_PSp43_le

theorem card_mulAut_le_of_isGenLie {G : Type} [Group G]
    (h : CFSG.ASVolI.ChF.IsGenLie G CFSG.ASVolI.ChF.GLKind.U4 2 1) :
    Nat.card (MulAut G) ≤ 51840 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_PSp43_of_isGenLie h
  exact card_mulAut_of_mulEquiv_PSp43 e

end AutPSp43

end

end CFSG.Quasithin.SimsF5
