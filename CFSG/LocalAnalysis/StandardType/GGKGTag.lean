module

public import CFSG.LocalAnalysis.StandardType.GGKGDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

theorem kg_labelIso_C {k f : ℕ} {lab' : LargeEvenLabel} (h : GGLabelIso ⟨.C, k, f⟩ lab') :
    (lab'.tag = .B ∨ lab'.tag = .C) ∧ lab'.rank = k ∧ lab'.n = f := by
  rcases h with h | ⟨-, hB, hr, hn⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · subst h
    exact ⟨Or.inr rfl, rfl, rfl⟩
  · exact ⟨hB, hr.symm, hn.symm⟩
  all_goals simp [LargeEvenLabel.mk.injEq] at h

theorem kg_inLambda2_C {X : Type} [Group X] {k f : ℕ} (hk : 3 ≤ k)
    (h : GGHasLabel ⟨.C, k, f⟩ X) : LargeEvenInLambda2 ⟨.C, k, f⟩ := by
  have hf : 1 ≤ f := by
    dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeSymplectic] at h
    obtain ⟨K, _, _, hK, -⟩ := h
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  refine ⟨hf, ?_⟩
  change 2 ≤ k ∧ (k = 2 → 2 ≤ f)
  exact ⟨by omega, fun h2 => by omega⟩

theorem kg_rigid_C
    {X : Type} [Group X] {k f : ℕ} (hk : 3 ≤ k) (hC : GGHasLabel ⟨.C, k, f⟩ X)
    {lab' : LargeEvenLabel} (hl' : LargeEvenInLambda2 lab') (h' : GGHasLabel lab' X) :
    (lab'.tag = .B ∨ lab'.tag = .C) ∧ lab'.rank = k ∧ lab'.n = f :=
  kg_labelIso_C (ggLabelRigidInput_holds _ _ X (kg_inLambda2_C hk hC) hl' hC h')

theorem kg_false_of_psl
    {X : Type} [Group X] {k f a m : ℕ} (hk : 3 ≤ k) (hC : GGHasLabel ⟨.C, k, f⟩ X)
    (hM : StatedClassicalModel X .PSL a 2 m) : False := by
  have ha : 1 ≤ a := le_trans (by norm_num) hM.1.2.2.1
  have hM' : StatedClassicalModel X .PSL (a - 1 + 1) 2 m := by
    rw [Nat.sub_add_cancel ha]
    exact hM
  have hl' : LargeEvenInLambda2 (⟨.A, a - 1, m⟩ : LargeEvenLabel) :=
    largeEvenInLambda2_typeA hM'
  have h' : GGHasLabel (⟨.A, a - 1, m⟩ : LargeEvenLabel) X := ggHasLabel_typeA hM'
  rcases (kg_rigid_C hk hC hl' h').1 with htag | htag
  · simp at htag
  · simp at htag

private theorem kgt_largeEvenInLambda2_twA (r f : ℕ) (hr : 2 ≤ r) (hf1 : 1 ≤ f)
    (hf2 : r = 2 → 2 ≤ f) :
    LargeEvenInLambda2 (⟨.twA, r, f⟩ : LargeEvenLabel) :=
  ⟨hf1, hr, hf2⟩

private theorem kgt_ggHasLabel_twA {X : Type} [Group X] (r f : ℕ)
    (h : StatedClassicalModel X .PSU (r + 1) 2 f) :
    GGHasLabel (⟨.twA, r, f⟩ : LargeEvenLabel) X := by
  show LargeEvenRecipeUnitary (r + 1) (2 ^ f) (fun R _ _ _ => Nonempty (X ≃* R))
  exact recipeUnitary_of_statedClassicalModel h

theorem kg_false_of_psu
    {X : Type} [Group X] {k f a m : ℕ} (hk : 3 ≤ k) (hC : GGHasLabel ⟨.C, k, f⟩ X)
    (hM : StatedClassicalModel X .PSU a 2 m) : False := by
  have ha : 1 ≤ a := le_trans (by norm_num) hM.1.2.2.1
  have ha3 : 3 ≤ a := hM.1.2.2.1
  have hm1 : 1 ≤ m := hM.1.2.1
  have hne32 : (a, 2 ^ m) ≠ (3, 2) := hM.1.2.2.2
  have hM' : StatedClassicalModel X .PSU (a - 1 + 1) 2 m := by
    rw [Nat.sub_add_cancel ha]
    exact hM
  have hl' : LargeEvenInLambda2 (⟨.twA, a - 1, m⟩ : LargeEvenLabel) :=
    kgt_largeEvenInLambda2_twA (a - 1) m (by omega) hm1 (by
      intro h2
      have ha_eq : a = 3 := by omega
      by_contra hm2
      have hm_eq : m = 1 := by omega
      exact hne32 (by simp [ha_eq, hm_eq]))
  have h' : GGHasLabel (⟨.twA, a - 1, m⟩ : LargeEvenLabel) X :=
    kgt_ggHasLabel_twA (a - 1) m hM'
  rcases (kg_rigid_C hk hC hl' h').1 with htag | htag
  · simp at htag
  · simp at htag

theorem kg_sp_params
    {X : Type} [Group X] {lab : LargeEvenLabel} {s e : ℕ} (hl : LargeEvenInLambda2 lab)
    (ht : lab.tag = .B ∨ lab.tag = .C) (hX : GGHasLabel lab X)
    (hM : StatedClassicalModel X .PSp s 2 e) : s = lab.rank ∧ e = lab.n := by
  have he : 1 ≤ e := hM.1.2.1
  have hs : 2 ≤ s := hM.1.2.2.1
  have hne : (s, 2 ^ e) ≠ (2, 2) := hM.1.2.2.2
  have hC' : GGHasLabel (⟨.C, s, e⟩ : LargeEvenLabel) X :=
    recipeSymplectic_of_statedClassicalModel hM
  have hl' : LargeEvenInLambda2 (⟨.C, s, e⟩ : LargeEvenLabel) := by
    refine ⟨he, hs, ?_⟩
    change s = 2 → 2 ≤ e
    intro h2
    by_contra he2
    have he1 : e = 1 := by omega
    exact hne (by simp [h2, he1])
  have hiso : GGLabelIso lab (⟨.C, s, e⟩ : LargeEvenLabel) :=
    ggLabelRigidInput_holds lab (⟨.C, s, e⟩ : LargeEvenLabel) X hl hl' hX hC'
  rcases hiso with h | ⟨-, -, hr, hn⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · subst h
    exact ⟨rfl, rfl⟩
  · exact ⟨hr.symm, hn.symm⟩
  all_goals
    (exfalso
     rw [h] at ht
     simp at ht)

theorem kg_false_of_quot_sl
    {X : Type} [Group X] [Finite X] {a k k' f : ℕ} {E : Type} [Field E] [Finite E]
    (hJ : CFSG.Open.IsQuasisimple X) (ha : 2 ≤ a) (hE : Nat.card E = 2 ^ k)
    (hφ : Nonempty (X ⧸ Subgroup.center X ≃* StatedProj (StatedSL a E))) (hk' : 3 ≤ k')
    (hC : GGHasLabel ⟨.C, k', f⟩ (X ⧸ Subgroup.center X)) : False := by
  by_cases h22 : a = 2 ∧ k = 1
  · obtain ⟨rfl, rfl⟩ := h22
    have hE2 : Nat.card E = 2 := by simpa using hE
    obtain ⟨φ⟩ := hφ
    have hcard : Nat.card (X ⧸ Subgroup.center X) < 60 := by
      rw [Nat.card_congr φ.toEquiv]
      have hdvd : Nat.card (StatedProj (StatedSL 2 E)) ∣ Nat.card ↥(StatedSL 2 E) :=
        Subgroup.index_dvd_card _
      rw [CFSG.Open.StatedAPI.card_statedSL_two E, hE2] at hdvd
      norm_num at hdvd
      exact lt_of_le_of_lt (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
    haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hJ.2
    haveI : Group.IsSolvable (X ⧸ Subgroup.center X) :=
      CFSG.GroupTheory.groups_order_below_sixty_solvable hcard
    exact (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.not_isSolvable_quot_center
      (J := X) inferInstance).elim
  · have hk : 1 ≤ k := by
      have h2 : 1 < Nat.card E := Finite.one_lt_card
      rw [hE] at h2
      by_contra hk0
      rw [show k = 0 by omega, pow_zero] at h2
      omega
    have hadm : StatedLieAdmissible .PSL a 2 k := by
      refine ⟨Nat.prime_two, hk, ha, ?_, ?_⟩
      · intro h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact h22 ⟨h1, Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)⟩
      · intro h
        obtain ⟨-, h3⟩ := Prod.mk.inj h
        have hdvd : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
        rw [h3] at hdvd
        norm_num at hdvd
    have hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL a 2 k :=
      ⟨hadm, E, inferInstance, inferInstance, hE, hφ⟩
    exact kg_false_of_psl hk' hC hmodel

theorem kg_false_of_quot_su
    {X : Type} [Group X] [Finite X] {a k k' f : ℕ} {E : Type} [Field E] [Finite E]
    (hJ : CFSG.Open.IsQuasisimple X) (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x) (ha : 2 ≤ a)
    (hτ'k : ∀ x, τ' x = x ^ (2 ^ k)) (hE : Nat.card E = (2 ^ k) ^ 2)
    (hφ : Nonempty (X ⧸ Subgroup.center X ≃*
      ↥(heldSU a E τ' hτ') ⧸ Subgroup.center ↥(heldSU a E τ' hτ')))
    (hk' : 3 ≤ k') (hC : GGHasLabel ⟨.C, k', f⟩ (X ⧸ Subgroup.center X)) : False := by
  obtain ⟨φ⟩ := hφ
  have hk : 1 ≤ k := by
    by_contra hk0
    have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
    rw [hE, show k = 0 by omega] at h2
    norm_num at h2
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  · obtain rfl : a = 2 := by omega
    obtain ⟨K, _, _, hKcard, ⟨ψ⟩⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_quot_heldSU_two_equiv_psl
        τ' hτ' hτ'k hE
    exact kg_false_of_quot_sl hJ le_rfl hKcard ⟨φ.trans ψ⟩ hk' hC
  · by_cases h31 : a = 3 ∧ k = 1
    · obtain ⟨rfl, rfl⟩ := h31
      haveI := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.isSolvable_quot_heldSU_three_two
        τ' hτ' (fun x => by simpa using hτ'k x) (by simpa using hE)
      haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hJ.2
      exact (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.not_isSolvable_quot_center
        (J := X) (solvable_of_surjective (f := φ.symm.toMonoidHom)
          φ.symm.surjective)).elim
    · have hak : (a, 2 ^ k) ≠ (3, 2) := by
        intro h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact h31 ⟨h1, Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)⟩
      obtain ⟨ψ⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj
          CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds τ' hτ' hτ'k hE ha3 hak
      have hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU a 2 k :=
        ⟨⟨Nat.prime_two, hk, ha3, hak⟩, E, inferInstance, inferInstance, hE, ⟨φ.trans ψ⟩⟩
      exact kg_false_of_psu hk' hC hmodel

theorem kg_sp_of_quot_sp
    {X : Type} [Group X] {s k k' f : ℕ} {E : Type} [Field E] [Finite E] (hs : 2 ≤ s)
    (hE : Nat.card E = 2 ^ k) (hne : ¬(s = 2 ∧ Nat.card E = 2))
    (φ : X ⧸ Subgroup.center X ≃* StatedProj (StatedSp s E)) (hk' : 3 ≤ k')
    (hC : GGHasLabel ⟨.C, k', f⟩ (X ⧸ Subgroup.center X)) : s = k' ∧ k = f := by
  have hk : 1 ≤ k := by
    by_contra hk0
    have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
    rw [hE, show k = 0 by omega] at h2
    norm_num at h2
  have hne' : (s, 2 ^ k) ≠ (2, 2) := by
    intro h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact hne ⟨h1, by rw [hE, h2]⟩
  have hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSp s 2 k :=
    ⟨⟨Nat.prime_two, hk, hs, hne'⟩, E, inferInstance, inferInstance, hE, ⟨φ⟩⟩
  exact kg_sp_params (kg_inLambda2_C hk' hC) (Or.inr rfl) hC hmodel

end CFSG.StandardType.KG
