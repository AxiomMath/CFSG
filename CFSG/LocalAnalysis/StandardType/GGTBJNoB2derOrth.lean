module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derLinUni
public import CFSG.LocalAnalysis.StandardType.GGTCJDivOrth
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.StandardType.S2MathAs4B2der1822

open CFSG CFSG.Assembly CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem a1o_classical_label_not_b2der {Q : Type} [Group Q] {labC : LargeEvenLabel}
    (hRig : GGLabelRigidInput) (hLC : LargeEvenInLambda2 labC)
    (htag : labC.tag = .A ∨ labC.tag = .twA ∨ labC.tag = .B ∨ labC.tag = .D ∨
      labC.tag = .twD)
    (hC : GGHasLabel labC Q) (hB : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) Q) : False :=
  (not_ggLabelIso_b2der htag)
    (hRig labC ⟨.B2der, 0, 1⟩ Q hLC ⟨le_refl 1, rfl, rfl⟩ hC hB)

private theorem a1o_exists_noncomm_of_component {R : Type} [Group R] {J : Subgroup R}
    (hJ : CFSG.Assembly.IsQuasisimple J) : ∃ x y : R, x * y ≠ y * x := by
  have hJnab : ∃ x y : J, x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact commutator_ne_bot_of_isQuasisimple hJ
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (fun x hx => by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (Subtype.ext_iff.mp (h ⟨x, hx⟩ ⟨y, hy⟩)).symm))
  obtain ⟨x, y, hxy⟩ := hJnab
  exact ⟨x, y, fun heq => hxy (Subtype.ext heq)⟩

private theorem a1o_pow_three_eq_one {R : Type} [Group R] (hcenter : Subgroup.center R = ⊥)
    {a : R} (hφ3 : (MulAut.conj a) ^ 3 = 1) : a ^ 3 = 1 := by
  have hc : a ^ 3 ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := DFunLike.congr_fun (show MulAut.conj (a ^ 3) = 1 by rw [map_pow, hφ3]) z
    rw [MulAut.conj_apply, MulAut.one_apply] at hz
    exact (mul_inv_eq_iff_eq_mul.mp hz).symm
  rw [hcenter] at hc
  exact Subgroup.mem_bot.mp hc

private theorem a1o_cases_contra {R : Type} [Group R] [Finite R]
    {t : StatedLieTag} {m f : ℕ} (hRig : GGLabelRigidInput)
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (hG : StatedClassicalModel R t m 2 f)
    {a : R} (ha3 : a ^ 3 = 1)
    {J : Subgroup R} (hJopen : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj a)))
    (hlab : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel)
      (↥J ⧸ Subgroup.center ↥J)) : False := by
  have hf1 : 1 ≤ f := hG.1.2.1
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJopen.2.2.2
  rcases TCJ.tcjOrth_quotCenter_cases_of_component_conj_omega ht hG Nat.prime_three
      (by norm_num) a ha3 hJopen with
    ⟨b, k, E, hEf, hEfin, hb, hEcard, hfk, hφiso⟩ |
    ⟨b, k, E, hEf, hEfin, τ, hτ, hb, hτk, hEcard, hfk, hψiso⟩ |
    ⟨s, K', hK'f, hK'fin, hs, hK'card, hne, hφSp⟩ |
    ⟨s, hM | hM⟩
  ·
    letI : Field E := hEf
    letI : Finite E := hEfin
    obtain ⟨e⟩ := hφiso
    obtain ⟨hLC, hC⟩ :=
      S2MathAs51600RALabels.admissible_typeA_of_psl (Q := ↥J ⧸ Subgroup.center ↥J) hb hEcard e
    exact a1o_classical_label_not_b2der hRig hLC (Or.inl rfl) hC hlab
  ·
    letI : Field E := hEf
    letI : Finite E := hEfin
    obtain ⟨e⟩ := hψiso
    obtain ⟨labC, htagC, hLC, hC⟩ :=
      S2MathAs51600RALabels.admissible_label_of_heldSU_quot (Q := ↥J ⧸ Subgroup.center ↥J)
        τ hτ hb hτk hEcard e
    have htagC' : labC.tag = .A ∨ labC.tag = .twA ∨ labC.tag = .B ∨ labC.tag = .D ∨
        labC.tag = .twD := by
      rcases htagC with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    exact a1o_classical_label_not_b2der hRig hLC htagC' hC hlab
  ·
    letI : Field K' := hK'f
    letI : Finite K' := hK'fin
    obtain ⟨e⟩ := hφSp
    have h22 : (s, 2 ^ f) ≠ (2, 2) := by
      intro hpair
      exact hne ⟨(Prod.mk.inj hpair).1, by rw [hK'card, (Prod.mk.inj hpair).2]⟩
    have hM : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSp s 2 f :=
      ⟨⟨Nat.prime_two, hf1, hs, h22⟩, K', hK'f, hK'fin, hK'card, ⟨e⟩⟩
    have hLC : LargeEvenInLambda2 (⟨.B, s, f⟩ : LargeEvenLabel) := by
      refine ⟨hf1, hs, fun hs2 => ?_⟩
      have hcardne : Nat.card K' ≠ 2 := fun h => hne ⟨hs2, h⟩
      have hfne : f ≠ 1 := fun hf1' => hcardne (by rw [hK'card, hf1']; norm_num)
      show 2 ≤ f
      exact Nat.succ_le_of_lt (lt_of_le_of_ne hf1 (Ne.symm hfne))
    have hC : GGHasLabel (⟨.B, s, f⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
      simp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum]
      exact recipeSymplectic_of_statedClassicalModel hM
    exact a1o_classical_label_not_b2der hRig hLC (Or.inr (Or.inr (Or.inl rfl))) hC hlab
  ·
    have hs4 : 4 ≤ s := hM.1.2.2
    have hLC : LargeEvenInLambda2 (⟨.D, s, f⟩ : LargeEvenLabel) := by
      refine ⟨hf1, ?_⟩
      show 3 ≤ s
      omega
    have hC : GGHasLabel (⟨.D, s, f⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
      simp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum]
      split_ifs with h3
      · omega
      · exact recipeOmegaPlus_of_statedClassicalModel hM
    exact a1o_classical_label_not_b2der hRig hLC (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hC hlab
  ·
    have hs4 : 4 ≤ s := hM.1.2.2
    have hLC : LargeEvenInLambda2 (⟨.twD, s, f⟩ : LargeEvenLabel) := by
      refine ⟨hf1, ?_⟩
      show 2 ≤ s
      omega
    have hC : GGHasLabel (⟨.twD, s, f⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
      simp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum]
      split_ifs with h2 h3
      · omega
      · omega
      · exact recipeOmegaMinus_of_statedClassicalModel hM
    exact a1o_classical_label_not_b2der hRig hLC
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hC hlab

theorem omegaPlusNoB2der_recipe
    {m n : ℕ} (hm : 4 ≤ m) (hn : 1 ≤ n) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeOmegaPlus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus m (2 ^ n) fun R _ I F => Q R I F ∧ NoB2derProp R I F := by
  unfold LargeEvenRecipeOmegaPlus at hQ
  obtain ⟨K, hKf, hKfin, hcard, hQK⟩ := hQ
  letI : Field K := hKf
  letI : Finite K := hKfin
  refine ⟨K, hKf, hKfin, hcard, hQK, ?_⟩
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  intro φ hφ1 hφ3 hφI J hJ hlab
  simp only [LargeEvenInnSet, Set.mem_range] at hφI
  obtain ⟨a, rfl⟩ := hφI
  haveI : Finite (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) :=
    TCJ.tcjDatum_finite_proj (LargeEvenOmega (LargeEvenQPlus K m))
  have hG : CFSG.Open.StatedClassicalModel
      (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) .POmegaPlus m 2 n :=
    statedClassicalModel_omegaPlus m n hcard ⟨Nat.prime_two, hn, hm⟩
  haveI : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) :=
    (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus _ m 2 n hG).2
  have hna : ∃ x y : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)), x * y ≠ y * x :=
    a1o_exists_noncomm_of_component hJ.2.2
  have hcenter : Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) = ⊥ :=
    center_eq_bot_of_simple_nonabelian hna
  have ha3 : a ^ 3 = 1 := a1o_pow_three_eq_one hcenter hφ3
  have hJopen : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj a)) :=
    (CFSG.Assembly.isComponentOf_iff_open).mp (by
      rw [TCJ.tcj_ggFixSub_eq_fixSubgroup] at hJ
      exact hJ)
  exact a1o_cases_contra hRig (Or.inl rfl) hG ha3 hJopen hlab

theorem omegaMinusNoB2der_recipe
    {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F => Q R I F ∧ NoB2derProp R I F := by
  unfold LargeEvenRecipeOmegaMinus at hQ
  obtain ⟨K, hKf, hKfin, hcard, b, c, hbc, hQK⟩ := hQ
  letI : Field K := hKf
  letI : Finite K := hKfin
  refine ⟨K, hKf, hKfin, hcard, b, c, hbc, hQK, ?_⟩
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  intro φ hφ1 hφ3 hφI J hJ hlab
  simp only [LargeEvenInnSet, Set.mem_range] at hφI
  obtain ⟨a, rfl⟩ := hφI
  haveI : Finite (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) :=
    TCJ.tcjDatum_finite_proj (LargeEvenOmega (LargeEvenQMinus m b c))
  have hG : CFSG.Open.StatedClassicalModel
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) .POmegaMinus (m + 1) 2 n :=
    statedClassicalModel_omegaMinus (m + 1) n hcard b c hbc ⟨Nat.prime_two, hn, by omega⟩
  haveI : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) :=
    (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus _
      (m + 1) 2 n hG).2
  have hna : ∃ x y : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)), x * y ≠ y * x :=
    a1o_exists_noncomm_of_component hJ.2.2
  have hcenter : Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) = ⊥ :=
    center_eq_bot_of_simple_nonabelian hna
  have ha3 : a ^ 3 = 1 := a1o_pow_three_eq_one hcenter hφ3
  have hJopen : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj a)) :=
    (CFSG.Assembly.isComponentOf_iff_open).mp (by
      rw [TCJ.tcj_ggFixSub_eq_fixSubgroup] at hJ
      exact hJ)
  exact a1o_cases_contra hRig (Or.inr rfl) hG ha3 hJopen hlab

theorem orthNoB2derInput_holds :
    OrthNoB2derInput := by
  intro lab hΛ hfam Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  have h := hΛ
  rcases hfam with htag | htag
  ·
    have htag' : tag = .D := htag
    subst htag'
    simp only [LargeEvenInLambda2] at h
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    by_cases h3 : rank = 3
    · simp only [h3, ↓reduceIte] at hQ ⊢
      exact linNoB2der_recipe (d := 4) (n := n) (by omega) h.1 (fun h4 => by omega) hQ
    · simp only [h3, ↓reduceIte] at hQ ⊢
      exact omegaPlusNoB2der_recipe (m := rank) (n := n) (by omega) h.1 hQ
  ·
    have htag' : tag = .twD := htag
    subst htag'
    simp only [LargeEvenInLambda2] at h
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    by_cases h2 : rank = 2
    · simp only [h2, ↓reduceIte] at hQ ⊢
      have hq : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
      rw [hq] at hQ ⊢
      exact linNoB2der_recipe (d := 2) (n := 2 * n) (by omega) (by omega) (fun _ => by omega) hQ
    · by_cases h3 : rank = 3
      · simp only [h2, h3, ↓reduceIte] at hQ ⊢
        exact uniNoB2der_recipe (d := 4) (n := n) (by omega) h.1 (fun h4 => by omega) hQ
      · simp only [h2, h3, ↓reduceIte] at hQ ⊢
        exact omegaMinusNoB2der_recipe (m := rank - 1) (n := n) (by omega) h.1 hQ

end CFSG.StandardType.S2MathAs4B2der1822

end
