module

public import CFSG.Milestones.ASVolI.F431.AInv
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieB
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieC

public section

namespace CFSG.ASVolI

section U5Cls

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5

variable {f : ℕ} {K : Type} [Field K]

theorem burnsideF4m_invConjV (h : UnitaryFieldData 2 f K) (z : hypPSU h 2 1) (hz : z * z = 1) :
    ∃ w : hypPSU h 2 1, w⁻¹ * z * w ∈ (Vsub h).map (hypProj h 2 1) := by
  obtain ⟨s, hss, rfl⟩ := exists_lift_sq_eq_one h hz
  by_cases hs1 : s = 1
  · refine ⟨1, 1, one_mem _, ?_⟩
    rw [hs1, map_one]
    group
  set W : Submodule K (HypIndex 2 1 → K) :=
    LinearMap.range (mulVecLin ((s : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K)
      - LinearMap.id) with hW
  have hmemW : ∀ u : HypIndex 2 1 → K, s • u - u ∈ W := fun u => ⟨u, rfl⟩
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 1 x y = 0 := by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    exact hypForm_sub_sub_eq_zero h hss u v
  have hW0 : W ≠ ⊥ := by
    intro hbot
    apply hs1
    apply Subtype.ext
    apply Units.ext
    ext a b
    have h1 : ((s : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ
        (Pi.single b 1 : HypIndex 2 1 → K) = Pi.single b 1 := by
      have := hmemW (Pi.single b 1)
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at this
      exact this
    have h2 := congrFun h1 a
    rw [mulVec_single_one, Matrix.col_apply] at h2
    change ((s : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b =
      (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b
    rw [h2, Matrix.one_apply, Pi.single_apply]
  obtain ⟨-, hd2, g, hg⟩ := UnitaryHigher.exists_smul_hypFlag_eq h le_rfl hW0 hWiso
  set d := Module.finrank K W
  have hF : hypFlag h 2 1 d = posFlag 2 1 K d := hypFlag_eq_posFlag h le_rfl (by omega)
  set s' := g⁻¹ * s * g with hs'
  have hrow : ∀ (a b : HypIndex 2 1), 2 ≤ fullPos a →
      ((s' : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b =
        (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b := by
    intro a b ha
    set u : HypIndex 2 1 → K := Pi.single b 1
    have hsu : s • (g • u) - g • u ∈ W := hmemW _
    rw [← hg] at hsu
    obtain ⟨w, hw, hwu⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hsu
    have hw' : g⁻¹ • (s • (g • u) - g • u) = w := by rw [← hwu, inv_smul_smul]
    have hs'u : s' • u - u = w := by
      rw [← hw', smul_sub, inv_smul_smul, hs', mul_smul, mul_smul]
    rw [hF] at hw
    have h1 := congrFun hs'u a
    rw [Pi.sub_apply, hw a (le_trans (by omega) ha), sub_eq_zero] at h1
    change (((s' : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ
      (Pi.single b (1 : K) : HypIndex 2 1 → K)) a = (Pi.single b (1 : K) : HypIndex 2 1 → K) a
      at h1
    rw [mulVec_single_one, Matrix.col_apply] at h1
    rw [h1, Matrix.one_apply, Pi.single_apply]
  set M := ((s' : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) with hM
  have hblk : M = blk3 (blkA M) (blkX M) (blkY M) 1 0 1 := by
    ext a b
    rcases a with i | k | j
    · rcases b with i' | k' | j' <;> rfl
    · have ha : 2 ≤ fullPos (.inr (.inl k) : HypIndex 2 1) := by simp
      rw [hrow _ b ha]
      rcases b with i' | k' | j' <;> simp [Matrix.one_apply]
    · have ha : 2 ≤ fullPos (.inr (.inr j) : HypIndex 2 1) := by simp; omega
      rw [hrow _ b ha]
      rcases b with i' | k' | j' <;> simp [Matrix.one_apply]
  have hgram : (M.map h.bar)ᵀ * hypGram 2 1 K * M = hypGram 2 1 K := (mem_hypSU.1 s'.2).1
  rw [hblk, blk3_gram_iff] at hgram
  obtain ⟨hA, -, hX, -⟩ := hgram
  have hA1 : blkA M = 1 := by
    rw [Matrix.mul_one] at hA
    have := congrArg (fun N => (N.map h.bar)ᵀ) hA
    simpa [conjTranspose_conjTranspose', Matrix.map_one _ (map_zero _) (map_one _)] using this
  have hX0 : blkX M = 0 := by
    rw [Matrix.mul_one, Matrix.mul_zero, add_zero] at hX
    have := congrArg (fun N => (N.map h.bar)ᵀ) hX
    simpa [conjTranspose_conjTranspose'] using this
  have hMN : M = oddUni h 0 (blkY M) := by
    have e : M = blk3 1 0 (blkY M) 1 0 1 := by
      conv_lhs => rw [hblk]
      rw [hA1, hX0]
    have hc : (replicateCol (Fin 1) (0 : Fin 2 → K)) = 0 := by ext; simp
    have hr : (replicateRow (Fin 1) fun j : Fin 2 => -h.bar ((0 : Fin 2 → K) j)) = 0 := by
      ext; simp
    rw [oddUni, hc, hr]
    exact e
  refine ⟨hypProj h 2 1 g, s', mem_Vsub_of_mat hMN, ?_⟩
  rw [hs', map_mul, map_mul, map_inv]

end U5Cls

section U5Std

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit
  CFSG.Quasithin.H13.F431.Un

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem burnsideF4m_cls_Y {x : hypPSU h 2 1} (hx : orderOf x = 2) :
    IsConj (z5Y h) x ∨ IsConj (t5Y h) x := by
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, sq] at this
  obtain ⟨d, v, hv, hvx⟩ := burnsideF4m_invConjV h x hxx
  have hv1 : v ≠ 1 := by
    rintro rfl
    have h1 : x = 1 := by
      have := congrArg (fun y => d * y * d⁻¹) hvx
      simp only [map_one, mul_assoc, mul_inv_cancel, mul_one] at this
      simpa [mul_assoc] using this.symm
    rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hY0 : Yof v ≠ 0 := fun h0 => hv1 ((eq_one_iff_Yof_eq_zero h hv).2 h0)
  have hz1 : z₁SU h ∈ Vsub h := vSU_mem_Vsub (isHerm_e₁₁ h)
  have hz2 : z₂SU h ∈ Vsub h := vSU_mem_Vsub (isHerm_swap h)
  by_cases hd : (Yof v).det = 0
  · left
    have hz10 : Yof (z₁SU h) ≠ 0 := by
      rw [Yof_z₁SU]
      intro e
      have := congrFun (congrFun e 0) 0
      simp at this
    obtain ⟨A, hA, hAv⟩ := exists_lev_conj_of_det_eq_zero hv hz1 hY0 hd hz10
      (by rw [Yof_z₁SU]; simp)
    exact isConj_proj_of_conj hvx hAv
  · right
    obtain ⟨A, hA, hAv⟩ := exists_lev_conj_of_det_ne_zero hv hz2 hd
      (by
        rw [Yof_z₂SU, Matrix.det_fin_two_of]
        simp)
    exact isConj_proj_of_conj hvx hAv

theorem burnsideF4m_stdTwo_Y :
    CFSG.Quasithin.H13.F431.Lift.StdTwo (hypPSU h 2 1) (hypProjUnitriangular h 2 1) (u5PtP h)
      (u5LnP h) (z5Y h) (t5Y h) where
  z_mem := z5Y_mem_U
  t_mem := t5Y_mem_U
  z_two := orderOf_z5Y
  t_two := orderOf_t5Y
  cls _ hx := burnsideF4m_cls_Y hx
  noconj φ := noconj_Y φ
  center _ hw hc hw1 := center_Y hw hc hw1
  aut_z _ h1 h2 := aut_z_Y h1 h2
  aut_t _ h1 h2 := aut_t_Y h1 h2
  cent_z := Or.inl cent_z_Y
  cent_t := Or.inr cent_t_Y

end U5Std

section U5Lie

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431 CFSG.ASVolI.ChF
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.Sec53F.Unit

theorem burnsideF4m_invCent_U5 {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {D : Type} [Group D] [Finite D] (e₀ : D ≃* hypPSU h 2 1) (A : LieAmalgamExt D)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) (hcen : Subgroup.center D = ⊥)
    (hodd : ¬ 2 ∣ (Lift.iK A hgen).range.index) : burnsideF4m_InvCent A := by
  haveI := finite_hypPSU_five h
  obtain ⟨c, hT, hP⟩ := (u5_yamStd (h := h)).pair e₀ A.yam
  let ε : D ≃* hypPSU h 2 1 := e₀.trans (MulAut.conj c⁻¹)
  have hε : ∀ S : Subgroup D, S.map ε.toMonoidHom = (S.map e₀.toMonoidHom).map
      (MulAut.conj c⁻¹).toMonoidHom := fun S => by
    rw [Subgroup.map_map]
    rfl
  have hU : A.TD.map ε.toMonoidHom = hypProjUnitriangular h 2 1 := by
    rw [hε, hT, burnsideF4m_map_conj_inv_map]
  have S1 := burnsideF4m_stdTwo_Y (h := h)
  rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact burnsideF4m_invCent_of_twoClassD A hgen hcen hodd
      (Lift.twoClassD_of_std A ε S1 (Or.inl ⟨rfl, rfl⟩)
        (by rw [hε, h1, burnsideF4m_map_conj_inv_map])
        (by rw [hε, h2, burnsideF4m_map_conj_inv_map]) hU)
  · exact burnsideF4m_invCent_of_twoClassD A hgen hcen hodd
      (Lift.twoClassD_of_std A ε S1 (Or.inr ⟨rfl, rfl⟩)
        (by rw [hε, h2, burnsideF4m_map_conj_inv_map])
        (by rw [hε, h1, burnsideF4m_map_conj_inv_map]) hU)

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_hyp_U5 (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K), Nonempty (↥Gp ≃* hypPSU h 2 1) := by
  obtain ⟨-, hf1, K, fK, finK, hcard, ⟨e⟩⟩ := hyp.model
  letI := fK
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf1, by rw [hcard, ← pow_mul, mul_comm]⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
  exact ⟨K, fK, h, ⟨e.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm⟩⟩

theorem burnsideF4m_centInput_U5 (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) (hodd : Odd Gp.index)
    {x : E} (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    ∃ w : E, IsConj x w ∧
      (Subgroup.centralizer ({w} : Set E) ≤ M₁ ∨ Subgroup.centralizer ({w} : Set E) ≤ M₂) := by
  haveI := hyp.finite
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U5) hyp.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamU5 marking
  rw [← h1, ← h2] at hTD
  obtain ⟨K, fK, h, ⟨e₀⟩⟩ := burnsideF4m_hyp_U5 hyp
  exact burnsideF4m_centInput_of hyp.toHypF_4_4g hTD hodd
    (fun hgen hcen hodd' => burnsideF4m_invCent_U5 h e₀ _ hgen hcen hodd') hx1 hx2

end U5Lie

end CFSG.ASVolI
