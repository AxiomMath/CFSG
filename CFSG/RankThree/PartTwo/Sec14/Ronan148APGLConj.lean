module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148APGLConjLeaves
public import CFSG.RankThree.PartTwo.Sec14.Ronan148APass
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec14.Ronan148ATwoLocal
import CFSG.RankThree.PartTwo.Sec14.Ronan148JGen
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTenTools
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem commutator_eq_bot_of_omega (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (h142c : Concl142S14) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A) [(ker148 A Y).Normal]
    {B Q : Subgroup G} {e : G} {K Le : Subgroup G} (hP : IsPoint148 A (lB A) Y B Q e K Le)
    (hkt : KType148 A Y e K Le) (he : e ∈ A) {J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hEq : Lift148Eq A Y K J) {p f : ℕ}
    (hf : 1 ≤ f) (hpgl : IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f)
    (heΩ : Subgroup.zpowers e ∈ omegaA A) (hLeA : Le ∈ lA A e)
    (hX1 : img148 A Y (deltaZero A (lB A) (Ronan148M.centPre148 A Y J)) = ⊥)
    {D : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hDY : D ≤ img148 A Y Y)
    (hDC : D ≤ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hAD : img148 A Y A ≤ Subgroup.normalizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {a₀ : G} (ha₀ : a₀ ∈ A) (ha₀Ω : Subgroup.zpowers a₀ ∈ omegaA A)
    {V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hVD : V ≤ D)
    (hVa : V ≤ Subgroup.centralizer {alpha148 A Y a₀ ha₀}) (hV3 : ¬ 3 ∣ Nat.card V)
    (hAV : img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    ⁅V, img148 A Y A⁆ = ⊥ := by
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hJeq : img148 A Y K = img148 A Y J := hEq
  have hJs : IsSimpleGroup ↥(img148 A Y J) := by
    have h1 := isSimpleGroup_img148_of_kType148 h hkt
    rw [hJeq] at h1
    exact h1
  obtain ⟨-, hJZ⟩ := Item148Res5.isComponent_img148 hY.2 hJ hJs
  have hVb : V ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({a₀} : Set G)) := by
    intro v hv
    refine Item148Rank.mem_img148_centralizer_of_commute148 hY.2 ha₀ (hA3 a₀ ha₀) le_rfl
      (hDY (hVD hv)) ?_
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hVa hv)).symm
  have hVX := Ronan148J.commutator_le_img148_deltaZero_of_point h142c h hY ha₀Ω V hVb hV3 hAV
  have hpass :=
    img148_deltaZero_le_sup_pgl h134 h48 h415 h hY hP hkt he hJ hAJ hEq hf hpgl heΩ hLeA
  rw [hX1, sup_bot_eq] at hpass
  have hVAD : ⁅V, img148 A Y A⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro v hv a ha
    have hvD := hVD hv
    have hav : a * v⁻¹ * a⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hAD ha) v⁻¹).mp (D.inv_mem hvD)
    show v * a * v⁻¹ * a⁻¹ ∈ D
    have hc : v * a * v⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) := by group
    rw [hc]
    exact D.mul_mem hvD hav
  rw [eq_bot_iff]
  intro x hx
  have hxD := hVAD hx
  have hxJ := hpass (hVX hx)
  have hxZ : (⟨x, hxJ⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hDC hxD) g g.2)
  rw [hJZ, Subgroup.mem_bot] at hxZ
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hxZ

theorem false_of_conj_pgl_twoLocal148 (hKF2 : KF148L3TwoLocal) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A) [(ker148 A Y).Normal]
    {e : G} {K Le : Subgroup G} (hkt : KType148 A Y e K Le) {J : Subgroup G}
    (hJ : J ∈ thetaComponentsIn Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hEq : Lift148Eq A Y K J) {p f : ℕ} (hf : 1 ≤ f)
    (hpgl : IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f) (hq : p ≠ 2 ∨ 9 ∣ p ^ f - 1)
    (x : ↥(Y ⊔ A) ⧸ ker148 A Y)
    (hDC : (img148 A Y J).map (MulAut.conj x).toMonoidHom ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) : False := by
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hJeq : img148 A Y K = img148 A Y J := hEq
  have hJs : IsSimpleGroup ↥(img148 A Y J) := by
    have h1 := isSimpleGroup_img148_of_kType148 h hkt
    rw [hJeq] at h1
    exact h1
  obtain ⟨-, hJZ⟩ := Item148Res5.isComponent_img148 hY.2 hJ hJs
  have hZJ : img148 A Y J ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzZ : (⟨z, hz.1⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 g g.2)
    rw [hJZ, Subgroup.mem_bot] at hzZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hzZ
  have hAN : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hpgl' := hpgl
  rw [img148_sup hJM le_sup_right] at hpgl'
  have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJnt : Nontrivial ↥(img148 A Y J) := hJs.toNontrivial
  obtain ⟨hp, hJpi⟩ := Ronan148N.isoLThreePi_of_isZ3PGLThreeAt148 hpgl' hJp hJnt hAN
  haveI := hp
  have hDpi : Sec4.IsoLThreePi ↥((img148 A Y J).map (MulAut.conj x).toMonoidHom) p f :=
    isoLThreePi_of_mulEquiv148
      ((img148 A Y J).equivMapOfInjective _ (MulAut.conj x).injective).symm hJpi
  obtain ⟨T, E₁, hTJ, hT1, hT2, hE₁J, hE₁T, hE₁, hE₁9⟩ := hKF2 _ _ p f hf hJpi hq
  obtain ⟨-, E₂, -, -, -, hE₂D, -, hE₂, hE₂9⟩ := hKF2 _ _ p f hf hDpi hq
  exact false_of_commuting_rank_two148 h hDC
    (le_bot_iff.mp ((inf_le_inf_left _ hDC).trans hZJ.le)) hT1 hT2 hTJ hE₁J hE₁T hE₁ hE₁9
    hE₂D hE₂ hE₂9

theorem step148PGLConjOmega_of_two (hKF2 : KF148L3TwoLocal) (hΩ2 : Step148PGLConjOmega2) :
    Step148PGLConjOmega := by
  intro G _ _ A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq hpq heΩ hLeA hX1 y hy
    D hDne hDC hAD heD hHe hV a₀ ha₀ ha₀1 ha₀J
  letI := ker148_normal hY.2
  obtain ⟨p, f, hf, hpgl⟩ := hpq
  by_cases hq : p = 2 ∧ ¬ 9 ∣ p ^ f - 1
  · obtain ⟨rfl, hq9⟩ := hq
    exact hΩ2 G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hEq f hf hq9 hpgl heΩ
      hLeA hX1 y hy hDne hDC hAD heD hHe hV a₀ ha₀ ha₀1 ha₀J
  · have hq' : p ≠ 2 ∨ 9 ∣ p ^ f - 1 := by
      by_contra hcon
      push Not at hcon
      exact hq hcon
    exact (false_of_conj_pgl_twoLocal148 hKF2 h hY hkt hJ hAJ hEq hf hpgl hq' _ hDC).elim

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
