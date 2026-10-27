module

public import CFSG.LocalAnalysis.StandardType.GGB36StepThreeInputs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGB36LemmaRT
public import CFSG.LocalAnalysis.StandardType.GGB36SelfCentU5
public import CFSG.LocalAnalysis.StandardType.GGB36SelfCentOm8
public import CFSG.LocalAnalysis.GLTheoremB.AutL34Bound
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz3
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
public import CFSG.LieType.Steinberg.CentralExt.GriessOmegaEightTwo
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCenter
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsSU
public import CFSG.LocalAnalysis.ComponentClassification.ExactGenAut
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
public import CFSG.CGT.Timmesfeld75.OddCenter
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Sec5Nine
public import CFSG.CGT.Timmesfeld75.Sec5Ten
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.AltCentre
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenGivenNatural
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenSplit
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.TwoGroupExtension
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.L44CoverTrivial
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma136
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec10Closed4
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Norm
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Quot
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Lift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Multiplier

private noncomputable def ltqS3_largeEvenProj_statedProj (K : Type) [Field K] :
    LargeEvenProj (LargeEvenSLGroup (Fin 3) K) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K) :=
  QuotientGroup.congr ((LargeEvenScalars (Fin 3) K).subgroupOf (LargeEvenSLGroup (Fin 3) K))
    ((CFSG.Open.StatedScalars (Fin 3) K).subgroupOf (CFSG.Open.StatedSL 3 K))
    (MulEquiv.subgroupCongr (largeEvenSLGroup_eq_statedSL 3)) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ((MulEquiv.subgroupCongr (largeEvenSLGroup_eq_statedSL 3)) y : GL (Fin 3) K) ∈
        CFSG.Open.StatedScalars (Fin 3) K
      rw [MulEquiv.subgroupCongr_apply]
      change (y : GL (Fin 3) K) ∈ LargeEvenScalars (Fin 3) K at hy
      exact hy
    · intro hx
      change (x : GL (Fin 3) K) ∈ CFSG.Open.StatedScalars (Fin 3) K at hx
      refine ⟨⟨(x : GL (Fin 3) K), ?_⟩, ?_, ?_⟩
      · rw [largeEvenSLGroup_eq_statedSL 3]; exact x.2
      · change (x : GL (Fin 3) K) ∈ LargeEvenScalars (Fin 3) K
        exact hx
      · ext; simp [MulEquiv.subgroupCongr_apply])

private theorem ltqS3_isLThreeFour_of_hasLabel {X : Type} [Group X]
    (h : GGHasLabel ⟨.A, 2, 2⟩ X) : CFSG.LocalAnalysis.GLTheoremB.IsLThreeFour X := by
  unfold GGHasLabel at h
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at h
  unfold LargeEvenRecipeLinear at h
  obtain ⟨K, hK, hKfin, hKcard, ⟨e⟩⟩ := h
  refine ⟨K, hK, hKfin, hKcard, ⟨e.trans (ltqS3_largeEvenProj_statedProj K)⟩⟩

private theorem ltqS3_card_le_nine_of_pRank {J : Type} [Group J] [Finite J]
    (h : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut J)) ≤ 2) :
    ∀ E : Subgroup (MulAut J), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2 := by
  intro E hE
  have hE3 : IsPGroup 3 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 (x : MulAut J) x.2⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE3
  have hn2 : n ≤ 2 :=
    (CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_top hE hn).trans h
  rw [hn]
  exact Nat.pow_le_pow_right (by norm_num) hn2

private theorem ltqS3_A22_contra {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hd : GGTPNBasicB 3 (3 ^ 6) (fun _ _ => True) A Ab σ J)
    (hhJ : GGHasLabel ⟨.A, 2, 2⟩ (↥J ⧸ Subgroup.center ↥J)) : False := by
  obtain ⟨hlocCore, hflat, -, -, hnum, -, -, -⟩ := hd
  obtain ⟨hAbA, hσAb, -, hker⟩ := hflat
  have hnormA : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J := hlocCore.2.2.2.2
  have hperfJ : commutator ↥J = ⊤ := hlocCore.2.2.2.1.2.2.1
  have hAbab : IsElemAbelian 3 Ab := by
    obtain ⟨hc, hp⟩ := hlocCore.1
    haveI : IsMulCommutative A := hc
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun z hz => ?_⟩
    · apply Subtype.ext
      exact Subgroup.mul_comm_of_mem_isMulCommutative A (hAbA u.2) (hAbA v.2)
    · exact hp z (hAbA hz)
  have hnorm : ∀ a ∈ Ab, ∀ j ∈ J, a j ∈ J := fun a ha j hj => hnormA a (hAbA ha) j hj
  have hAut : ∀ E : Subgroup (MulAut ↥J), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2 :=
    ltqS3_card_le_nine_of_pRank
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.pRank_mulAut_le_two_of_l34
        hperfJ (ltqS3_isLThreeFour_of_hasLabel hhJ))
  have hbound : Nat.card Ab ≤ 3 ^ 3 := by
    have h := B36.card_le_of_kernel_le_zpowers (p := 3) (by norm_num) hAbab hσAb hnorm hker
      (k := 2) hAut
    simpa using h
  have hb4 : 3 ^ 4 ≤ Nat.card Ab := by
    have h := hnum.2
    norm_num at h ⊢
    omega
  have hnot : ¬ (3 ^ 4 ≤ 3 ^ 3) := by norm_num
  exact hnot (hb4.trans hbound)

private theorem ltqS3_numbers {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hA : IsElemAbelian 3 A) (hflat : GGTPNFlat 3 A Ab σ J)
    (hnum : GGTPNNum 3 (3 ^ 6) A Ab) :
    Ab = A ∨ (Nat.card A = 3 ^ 5 ∧ Nat.card Ab = 3 ^ 4) := by
  obtain ⟨hAbA, -, hcardA, -⟩ := hflat
  obtain ⟨hnumA, hnumAb⟩ := hnum
  have hP : IsPGroup 3 A := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hA.2 (x : MulAut X) x.2⟩
  have hPab : IsPGroup 3 Ab := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hA.2 (x : MulAut X) (hAbA x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  obtain ⟨l, hl⟩ := IsPGroup.iff_card.1 hPab
  have hlk : l ≤ k := by
    have hdvd : Nat.card Ab ∣ Nat.card A := Subgroup.card_dvd_of_le hAbA
    rw [hl, hk] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 hdvd
  have e1 : 3 * 3 ^ k = 3 ^ (k + 1) := by rw [pow_succ]; ring
  have e2 : 9 * 3 ^ l = 3 ^ (l + 2) := by rw [pow_add]; ring
  have hk5 : k + 1 ≤ 6 := by
    have h : 3 ^ (k + 1) ≤ 3 ^ 6 := by rw [← e1, ← hk]; exact hnumA
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h
  have hl2 : 6 ≤ l + 2 := by
    have h : 3 ^ 6 ≤ 3 ^ (l + 2) := by rw [← e2, ← hl]; exact hnumAb
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h
  have el : 3 * 3 ^ l = 3 ^ (l + 1) := by rw [pow_succ]; ring
  have hkl : k ≤ l + 1 := by
    have h : 3 ^ k ≤ 3 ^ (l + 1) := by
      have h' : 3 ^ k ≤ 3 * 3 ^ l := by rw [← hk, ← hl]; exact hcardA
      rw [el] at h'
      exact h'
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h
  by_cases hkeq : k = l
  · left
    exact Subgroup.eq_of_le_of_card_ge hAbA (by rw [hk, hl, hkeq])
  · right
    have hkl' : k = l + 1 := by omega
    have hl4 : l = 4 := by omega
    exact ⟨by rw [hk, hkl', hl4], by rw [hl, hl4]⟩

private theorem ltqS3_map_eq {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {J : Subgroup X} (hnorm : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J) {a : MulAut X} (ha : a ∈ A) :
    J.map a.toMonoidHom = J := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hnorm a ha y hy
  · rw [Subgroup.card_map_of_injective a.injective]

private theorem ltqS3_ab_le_stab {X : Type} [Group X] [Finite X] {Ab : Subgroup (MulAut X)}
    {J : Subgroup X} (hnorm : ∀ a ∈ Ab, ∀ j ∈ J, a j ∈ J) :
    Ab ≤ CFSG.GroupActions.subgroupStabAut J := by
  intro a ha
  show J.map a.toMonoidHom = J
  exact ltqS3_map_eq hnorm ha

private noncomputable def ltqS3_restrict {X : Type} [Group X] [Finite X]
    (Ab : Subgroup (MulAut X)) (J : Subgroup X) (hnorm : ∀ a ∈ Ab, ∀ j ∈ J, a j ∈ J) :
    Ab →* MulAut ↥J where
  toFun a := CFSG.GroupActions.subgroupStabRestrict J
    ⟨(a : MulAut X), ltqS3_ab_le_stab hnorm a.2⟩
  map_one' := by ext j; rfl
  map_mul' a b := by ext j; rfl

private theorem ltqS3_restrict_apply {X : Type} [Group X] [Finite X]
    {Ab : Subgroup (MulAut X)} {J : Subgroup X}
    {hnorm : ∀ a ∈ Ab, ∀ j ∈ J, a j ∈ J} (a : Ab) (j : ↥J) :
    ((ltqS3_restrict Ab J hnorm a j : ↥J) : X) = (a : MulAut X) j.1 := rfl

private theorem ltqS3_hasLabel_subgroupOf {G : Type} [Group G] {lab : LargeEvenLabel}
    {J X : Subgroup G} (hJX : J ≤ X)
    (h : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J)) :
    GGHasLabel lab (↥(J.subgroupOf X) ⧸ Subgroup.center ↥(J.subgroupOf X)) := by
  let e : ↥(J.subgroupOf X) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJX
  have hmap : Subgroup.map e (Subgroup.center ↥(J.subgroupOf X)) = Subgroup.center ↥J :=
    Subgroup.map_center_eq e
  let iso : (↥(J.subgroupOf X) ⧸ Subgroup.center ↥(J.subgroupOf X)) ≃*
      (↥J ⧸ Subgroup.center ↥J) := QuotientGroup.congr _ _ e hmap
  refine largeEvenRawDatum_mono (fun R _ _ _ hq => ?_) h
  obtain ⟨g⟩ := hq
  exact ⟨iso.trans g⟩

private theorem ltqS3_statedClassicalModel_twA41 {R : Type} [Group R]
    (h : GGHasLabel ⟨.twA, 4, 1⟩ R) : CFSG.Open.StatedClassicalModel R .PSU 5 2 1 := by
  unfold GGHasLabel at h
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at h
  unfold LargeEvenRecipeUnitary at h
  obtain ⟨K, hK, hKfin, hKcard, ⟨e⟩⟩ := h
  have hmod : CFSG.Open.StatedClassicalModel (LargeEvenProj (LargeEvenSUGroup (Fin 5) K 2))
      .PSU 5 2 1 :=
    statedClassicalModel_unitary (K := K) 5 1 hKcard
      ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hmod

private theorem ltqS3_statedClassicalModel_D4 {R : Type} [Group R] {n : ℕ} (hn : 1 ≤ n)
    (h : GGHasLabel ⟨.D, 4, n⟩ R) : CFSG.Open.StatedClassicalModel R .POmegaPlus 4 2 n := by
  unfold GGHasLabel at h
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at h
  unfold LargeEvenRecipeOmegaPlus at h
  obtain ⟨K, hK, hKfin, hKcard, ⟨e⟩⟩ := h
  exact ⟨⟨Nat.prime_two, hn, le_rfl⟩, K, hK, hKfin, hKcard, ⟨e⟩⟩

private theorem ltqS3_center_twA41 {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Assembly.IsQuasisimple Y)
    (h : GGHasLabel ⟨.twA, 4, 1⟩ (Y ⧸ Subgroup.center Y)) :
    ¬ 3 ∣ Nat.card (Subgroup.center Y) := by
  haveI : Group.IsPerfect Y := ⟨hY.1⟩
  have hmod : CFSG.Open.StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU 5 2 1 :=
    ltqS3_statedClassicalModel_twA41 h
  obtain ⟨-, hrow⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row hmod (by decide)
  have hbot := CFSG.OddStandard.SmallF3.HypA2Leaves.a2l_center_eq_bot_of_row hrow
    (by decide) (by decide)
  rw [hbot, Subgroup.card_bot]
  norm_num

private theorem ltqS3_center_D4 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 1 ≤ n)
    (hY : CFSG.Assembly.IsQuasisimple Y)
    (h : GGHasLabel ⟨.D, 4, n⟩ (Y ⧸ Subgroup.center Y)) :
    ¬ 3 ∣ Nat.card (Subgroup.center Y) := by
  haveI : Group.IsPerfect Y := ⟨hY.1⟩
  have hSC : CFSG.Open.StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 n :=
    ltqS3_statedClassicalModel_D4 hn h
  have hdvd : Nat.card (Subgroup.center Y) ∣
      Nat.card (Open.griessHopfMultiplier (Y ⧸ Subgroup.center Y)) :=
    CFSG.ComponentClassification.CatFactsL4U4.Cover82.Mult.card_center_dvd_hopfMultiplier
      (Q := Y) (S := Y ⧸ Subgroup.center Y) (MulEquiv.refl _)
  rcases eq_or_lt_of_le hn with rfl | hn2
  · intro h3
    obtain ⟨-, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaPlus_four_two_row
        (X := Y ⧸ Subgroup.center Y) ⟨hSC.1, Or.inl hSC⟩
    have hcard : Nat.card (generic .POmegaPlus 4 2 1 × exceptional .POmegaPlus 4 2 1) = 4 := by
      simp only [generic, exceptional, genericOrders, exceptionalOrders, ↓reduceIte,
        Nat.card_prod, Nat.card_congr (Multiplicative.ofAdd (α := ZMod 1)),
        Nat.card_congr (Multiplicative.ofAdd (α := ZMod 2))]
      norm_num
    have h4 : 3 ∣ 4 := by
      have h := h3.trans hdvd
      rwa [Nat.card_congr e.toEquiv, hcard] at h
    norm_num at h4
  · have hq : 3 ≤ 2 ^ n :=
      (by norm_num : 3 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by norm_num) hn2)
    obtain ⟨-, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaPlus_row
        (X := Y ⧸ Subgroup.center Y) (n := 4) (p := 2) (f := n) hSC (Or.inl hq)
    have hEven : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have hg : genericOrders .POmegaPlus 4 2 n = (1, 1) := by
      simp only [genericOrders, hEven, ↓reduceIte]
    have he : exceptionalOrders .POmegaPlus 4 2 n = (1, 1) := by
      unfold exceptionalOrders
      split <;> simp_all <;> omega
    have hbot := CFSG.OddStandard.SmallF3.HypA2Leaves.a2l_center_eq_bot_of_row ⟨e⟩ hg he
    rw [hbot, Subgroup.card_bot]
    norm_num

private theorem ltqS3_eq_of_mul_inv_mem_center {X : Type} [Group X]
    (hperf : commutator X = ⊤) {α β : MulAut X}
    (h : ∀ l : X, α l * (β l)⁻¹ ∈ Subgroup.center X) : α = β := by
  let δ : X →* X :=
    { toFun := fun l => α l * (β l)⁻¹
      map_one' := by simp
      map_mul' := fun l m => by
        have hzm : (α m * (β m)⁻¹) * (β l)⁻¹ = (β l)⁻¹ * (α m * (β m)⁻¹) :=
          (Subgroup.mem_center_iff.mp (h m) ((β l)⁻¹)).symm
        show α (l * m) * (β (l * m))⁻¹ = (α l * (β l)⁻¹) * (α m * (β m)⁻¹)
        rw [map_mul, map_mul, mul_inv_rev]
        calc α l * α m * ((β m)⁻¹ * (β l)⁻¹)
            = α l * ((α m * (β m)⁻¹) * (β l)⁻¹) := by group
          _ = α l * ((β l)⁻¹ * (α m * (β m)⁻¹)) := by rw [hzm]
          _ = (α l * (β l)⁻¹) * (α m * (β m)⁻¹) := by group }
  have hδcenter : ∀ l, δ l ∈ Subgroup.center X := h
  have hker : commutator X ≤ δ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hδcenter b)) (δ a)
  have htop : δ.ker = ⊤ := by rw [eq_top_iff, ← hperf]; exact hker
  ext l
  have hl : l ∈ δ.ker := by rw [htop]; exact Subgroup.mem_top l
  exact mul_inv_eq_one.mp (by simpa [δ] using hl)

private theorem ltqS3_inner_twA41 {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hd : GGTPNBasicB 3 (3 ^ 6) (fun _ _ => True) A Ab σ J)
    (hhJ : GGHasLabel ⟨.twA, 4, 1⟩ (↥J ⧸ Subgroup.center ↥J))
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥J)) :
    ∀ a ∈ A, ∃ u ∈ J, ∀ v ∈ J, a v = u * v * u⁻¹ := by
  classical
  obtain ⟨hlocCore, hflat, -, -, hnum, hselfC, honly, hmarked⟩ := hd
  have hnorm : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J := hlocCore.2.2.2.2
  have hSC : CFSG.Open.StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSU 5 2 1 :=
    ltqS3_statedClassicalModel_twA41 hhJ
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥J ⧸ Subgroup.center ↥J)) = 2 :=
    CFSG.StandardType.PRankBounds.card_outer_psu5 hSC
  let Φ : MulAut ↥J →* MulAut (↥J ⧸ Subgroup.center ↥J) :=
    CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (Subgroup.center ↥J)
  have hperf : commutator ↥J = ⊤ := hlocCore.2.2.2.1.2.2.1
  have hkerΦ : Φ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro α hα
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel] at hα
    refine ltqS3_eq_of_mul_inv_mem_center hperf (β := 1) fun l => ?_
    rw [MulAut.one_apply, ← QuotientGroup.eq_one_iff]
    have h1 : QuotientGroup.mk' (Subgroup.center ↥J) (α l) *
        (QuotientGroup.mk' (Subgroup.center ↥J) l)⁻¹ = 1 := by
      rw [hα l, mul_inv_cancel]
    have h2 : QuotientGroup.mk' (Subgroup.center ↥J) (α l * l⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact h1
    exact h2
  intro a ha
  have ha3 : (⟨a, ha⟩ : ↥A) ^ 3 = 1 := Subtype.ext (hlocCore.1.2 a ha)
  have hρ3 : (ltqS3_restrict A J hnorm ⟨a, ha⟩) ^ 3 = 1 := by
    have h := congrArg (ltqS3_restrict A J hnorm) ha3
    rw [map_pow, map_one] at h
    exact h
  have hΦ3 : (Φ (ltqS3_restrict A J hnorm ⟨a, ha⟩)) ^ 3 = 1 := by
    rw [← map_pow, hρ3, map_one]
  set q : CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥J ⧸ Subgroup.center ↥J) :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner _)
      (Φ (ltqS3_restrict A J hnorm ⟨a, ha⟩)) with hq
  have hq3 : q ^ 3 = 1 := by rw [hq, ← map_pow, hΦ3, map_one]
  have hq2 : q ^ 2 = 1 := by
    have := pow_card_eq_one' (G := CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥J ⧸ Subgroup.center ↥J)) (x := q)
    rwa [hout] at this
  have hq1 : q = 1 := by
    calc q = q ^ 3 * (q ^ 2)⁻¹ := by group
      _ = 1 := by rw [hq3, hq2]; group
  rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq1
  obtain ⟨gb, hgb⟩ := hq1
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) gb
  refine ⟨u, u.2, ?_⟩
  intro v hv
  have hconj : MulAut.conj u = ltqS3_restrict A J hnorm ⟨a, ha⟩ := by
    apply (MonoidHom.ker_eq_bot_iff Φ).mp hkerΦ
    rw [← hgb]
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) y
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply,
      MulAut.conj_apply, MulAut.conj_apply, ← hu, map_mul, map_mul, map_inv]
  have hvu : (ltqS3_restrict A J hnorm ⟨a, ha⟩) ⟨v, hv⟩ = MulAut.conj u ⟨v, hv⟩ := by
    rw [← hconj]
  have := congrArg Subtype.val hvu
  simpa [MulAut.conj_apply, ltqS3_restrict_apply] using this


private theorem ltqS3_inner_D4 {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hd : GGTPNBasicB 3 (3 ^ 6) (fun _ _ => True) A Ab σ J)
    (hInn : GGInnerOnD4)
    {labL labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hhasJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hlabJ : labJ = ⟨.D, 4, labL.n⟩) :
    (∃ labK : LargeEvenLabel, (labK.tag = .E6 ∨ labK.tag = .twE6) ∧
        GGHasLabel labK (X ⧸ Subgroup.center X)) ∨
      (∀ a ∈ A, ∃ u ∈ J, ∀ v ∈ J, a v = u * v * u⁻¹) := by
  obtain ⟨hlocCore, hflat, -, -, -, -, -, hmarked⟩ := hd
  unfold GGTPNMarked at hmarked
  obtain ⟨hcomm, lab, hΛlab, hraw⟩ := hmarked
  by_cases htag : lab.tag = .E6 ∨ lab.tag = .twE6
  · left
    refine ⟨lab, htag, ?_⟩
    exact largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hraw
  · right
    intro a ha
    have hmark' : LargeEvenMarking X fun lab R _ I F θ =>
        ¬ (lab.tag = .E6 ∨ lab.tag = .twE6) ∧ GGInducedInn A θ I := by
      refine ⟨hcomm, lab, hΛlab, ?_⟩
      refine largeEvenRawDatum_mono (fun R _ I F hQ => ?_) hraw
      obtain ⟨hsimple, hnonab, θ, -, hhalf, hind⟩ := hQ
      exact ⟨hsimple, hnonab, θ, htag, hind⟩
    subst hlabJ
    exact hInn X A σ J hlocCore.1 hlocCore.2.1 hlocCore.2.2.2.1 hlocCore.2.2.2.2 hmark'
      _ hΛJ rfl rfl hhasJ a ha

private theorem ltqS3_card_image {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X} {labJ : LargeEvenLabel}
    (hnorm : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J)
    (hd : GGTPNBasicB 3 (3 ^ 6) (fun _ _ => True) A Ab σ J)
    (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥J))
    (hinner : ∀ a ∈ A, ∃ u ∈ J, ∀ v ∈ J, a v = u * v * u⁻¹)
    (hself : LargeEvenLabelAll labJ fun R _ _ _ =>
      ∀ E : Subgroup R, IsElemAbelian 3 E →
        (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) → Nat.card E = 3 ^ 4) :
    Nat.card (ltqS3_restrict A J hnorm).range = 3 ^ 4 := by
  classical
  obtain ⟨hlocCore, hflat, -, -, hnum, hselfC, honly, hmarked⟩ := hd
  have hraw := hself (fun R _ _ _ => Nonempty (↥J ⧸ Subgroup.center ↥J ≃* R)) hhJ
  obtain ⟨R, hR, I, F, ⟨⟨e⟩, hselfR⟩⟩ := largeEvenRawDatum_exists hraw
  letI := hR
  let Inn : Subgroup (MulAut ↥J) := (MulAut.conj : ↥J →* MulAut ↥J).range
  have hker_conj : (MulAut.conj : ↥J →* MulAut ↥J).ker = Subgroup.center ↥J := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h y
      have h1 := congrArg (fun φ : MulAut ↥J => φ y) h
      simp only [MulAut.one_apply, MulAut.conj_apply] at h1
      calc y * x = (x * y * x⁻¹) * x := by rw [h1]
        _ = x * y := by group
    · intro h
      ext y
      rw [MulAut.one_apply, MulAut.conj_apply, show x * y = y * x from (h y).symm]
      group
  let innIso : (↥J ⧸ Subgroup.center ↥J) ≃* Inn :=
    (QuotientGroup.quotientMulEquivOfEq hker_conj.symm).trans
      (QuotientGroup.quotientKerEquivRange (MulAut.conj : ↥J →* MulAut ↥J))
  let E : Subgroup (MulAut ↥J) := (ltqS3_restrict A J hnorm).range
  have hEinn : E ≤ Inn := by
    rintro x ⟨a, rfl⟩
    obtain ⟨u, hu, hconj⟩ := hinner a a.2
    refine ⟨⟨u, hu⟩, ?_⟩
    ext v
    simpa [MulAut.conj_apply, ltqS3_restrict_apply] using (hconj v v.2).symm
  have hEelem : IsElemAbelian 3 E := by
    have hAtop : IsElemAbelian 3 (⊤ : Subgroup ↥A) := by
      obtain ⟨hc, hp⟩ := hlocCore.1
      haveI : IsMulCommutative A := hc
      refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x _ => ?_⟩
      · apply Subtype.ext
        apply Subtype.ext
        set xa : ↥A := Subtype.val x
        set ya : ↥A := Subtype.val y
        exact Subgroup.mul_comm_of_mem_isMulCommutative A
          (Subtype.property xa) (Subtype.property ya)
      · apply Subtype.ext
        exact hp (x : MulAut X) (Subtype.property x)
    have := CFSG.SectionRank.isElemAbelian_map hAtop
      (ltqS3_restrict A J hnorm)
    rw [← MonoidHom.range_eq_map] at this
    simpa [E] using this
  have hEinnElem : IsElemAbelian 3 (E.subgroupOf Inn) := hEelem.subgroupOf Inn
  let φ : Inn ≃* R := innIso.symm.trans e
  let E'' : Subgroup R := (E.subgroupOf Inn).map φ.toMonoidHom
  have hE''elem : IsElemAbelian 3 E'' := by
    have := CFSG.SectionRank.isElemAbelian_map hEinnElem φ.toMonoidHom
    simpa [E''] using this
  have hE''self : ∀ g : R, (∀ x ∈ E'', g * x = x * g) → g ^ 3 = 1 → g ∈ E'' := by
    intro g hg hg3
    have hg3' : (e.symm g) ^ 3 = 1 := by
      rw [← map_pow, hg3, map_one]
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (innIso (e.symm g)).2
    have hw' : MulAut.conj w = (innIso (e.symm g) : MulAut ↥J) := hw
    have hw3ker : w ^ 3 ∈ (MulAut.conj : ↥J →* MulAut ↥J).ker := by
      rw [MonoidHom.mem_ker]
      have hconjw3 : MulAut.conj (w ^ 3) = (innIso (e.symm g) : MulAut ↥J) ^ 3 := by
        rw [map_pow, hw']
      have hpow : (innIso (e.symm g) : MulAut ↥J) ^ 3 = 1 := by
        have h1 : ((innIso (e.symm g)) ^ 3 : Inn) = innIso ((e.symm g) ^ 3) :=
          (map_pow innIso (e.symm g) 3).symm
        have h2 : innIso ((e.symm g) ^ 3) = 1 := by rw [hg3', map_one]
        have := congrArg (fun z : Inn => (z : MulAut ↥J)) (h1.trans h2)
        simpa using this
      rw [hconjw3, hpow]
    have hw3c : w ^ 3 ∈ Subgroup.center ↥J := by
      rw [hker_conj] at hw3ker
      exact hw3ker
    have hcop : Nat.Coprime (Nat.card (Subgroup.center ↥J)) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ).symm
    obtain ⟨z, hz⟩ := (Nat.Coprime.pow_left_bijective (n := 3)
      (G := Subgroup.center ↥J) hcop).2 ((⟨w ^ 3, hw3c⟩ : Subgroup.center ↥J)⁻¹)
    have hz3 : (z : ↥J) ^ 3 = (w ^ 3)⁻¹ := by
      have := congrArg Subtype.val hz
      simpa using this
    let u : ↥J := w * (z : ↥J)
    have hwz : Commute w (z : ↥J) := Subgroup.mem_center_iff.mp z.2 w
    have hu3 : u ^ 3 = 1 := by
      change (w * (z : ↥J)) ^ 3 = 1
      rw [hwz.mul_pow, hz3, mul_inv_cancel]
    have hconjz : MulAut.conj (z : ↥J) = 1 := by
      rw [← MonoidHom.mem_ker, hker_conj]
      exact z.2
    have hconju : MulAut.conj u = MulAut.conj w := by
      change MulAut.conj (w * (z : ↥J)) = MulAut.conj w
      rw [map_mul, hconjz, mul_one]
    have hinnw : innIso (e.symm g) = (⟨MulAut.conj w, ⟨w, rfl⟩⟩ : Inn) := by
      apply Subtype.ext
      exact hw'.symm
    have hinnu : innIso (e.symm g) = (⟨MulAut.conj u, ⟨u, rfl⟩⟩ : Inn) := by
      rw [hinnw]
      apply Subtype.ext
      exact hconju.symm
    have hφu : φ (⟨MulAut.conj u, ⟨u, rfl⟩⟩ : Inn) = g := by
      change e (innIso.symm (⟨MulAut.conj u, ⟨u, rfl⟩⟩ : Inn)) = g
      have h1 : innIso.symm (⟨MulAut.conj u, ⟨u, rfl⟩⟩ : Inn) = e.symm g := by
        rw [← hinnu, MulEquiv.symm_apply_apply]
      rw [h1, MulEquiv.apply_symm_apply]
    have hcomm_proof : ∀ a ∈ A, ∀ v ∈ J,
        a ((u : X) * v * (u : X)⁻¹) = (u : X) * a v * (u : X)⁻¹ := by
      intro a ha v hv
      have hmem_a : φ (⟨⟨ltqS3_restrict A J hnorm ⟨a, ha⟩, hEinn ⟨⟨a, ha⟩, rfl⟩⟩,
          ⟨⟨a, ha⟩, rfl⟩⟩ : E.subgroupOf Inn) ∈ E'' :=
        Subgroup.mem_map.mpr ⟨_, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
      have hc := hg _ hmem_a
      have hc' := congrArg φ.symm hc
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at hc'
      have hc'' : (⟨MulAut.conj u, ⟨u, rfl⟩⟩ : Inn) *
          (⟨⟨ltqS3_restrict A J hnorm ⟨a, ha⟩, hEinn ⟨⟨a, ha⟩, rfl⟩⟩,
            ⟨⟨a, ha⟩, rfl⟩⟩ : E.subgroupOf Inn) =
          (⟨⟨ltqS3_restrict A J hnorm ⟨a, ha⟩, hEinn ⟨⟨a, ha⟩, rfl⟩⟩,
            ⟨⟨a, ha⟩, rfl⟩⟩ : E.subgroupOf Inn) *
          (⟨MulAut.conj u, ⟨u, rfl⟩⟩ : Inn) := by
        have hsymmg : φ.symm g = (⟨MulAut.conj u, ⟨u, rfl⟩⟩ : Inn) := by
          rw [← hφu, MulEquiv.symm_apply_apply]
        rw [hsymmg] at hc'
        exact hc'
      have h3 : MulAut.conj u * ltqS3_restrict A J hnorm ⟨a, ha⟩ =
          ltqS3_restrict A J hnorm ⟨a, ha⟩ * MulAut.conj u := by
        have := congrArg (fun z : Inn => (z : MulAut ↥J)) hc''
        simpa using this
      have h4 := congrArg (fun ψ : MulAut ↥J => ψ (⟨v, hv⟩ : ↥J)) h3
      have h5 : (ltqS3_restrict A J hnorm ⟨a, ha⟩) (u * (⟨v, hv⟩ : ↥J) * u⁻¹) =
          u * ((ltqS3_restrict A J hnorm ⟨a, ha⟩) (⟨v, hv⟩ : ↥J)) * u⁻¹ := by
        simpa [MulAut.mul_apply, MulAut.conj_apply] using h4.symm
      have hres := congrArg Subtype.val h5
      simpa [ltqS3_restrict_apply] using hres
    have hup_proof : ∀ v ∈ J, (u : X) ^ 3 * v = v * (u : X) ^ 3 := by
      intro v hv
      have hu3' : (u : X) ^ 3 = 1 := by
        have := congrArg Subtype.val hu3
        simpa using this
      rw [hu3', one_mul, mul_one]
    obtain ⟨a0, ha0, hconja0⟩ :=
      B36.mem_of_commute_inner (p := 3) (by norm_num) hselfC hnorm hZ u.2
        hcomm_proof hup_proof
    have hρeq : ltqS3_restrict A J hnorm ⟨a0, ha0⟩ = MulAut.conj u := by
      ext v
      simpa [MulAut.conj_apply, ltqS3_restrict_apply] using hconja0 v v.2
    have hmem_u : φ (⟨MulAut.conj u, ⟨u, rfl⟩⟩ : Inn) ∈ E'' := by
      refine Subgroup.mem_map.mpr ⟨(⟨MulAut.conj u, ⟨u, rfl⟩⟩ : Inn), ?_, rfl⟩
      show MulAut.conj u ∈ E
      rw [← hρeq]
      exact ⟨⟨a0, ha0⟩, rfl⟩
    rwa [hφu] at hmem_u
  have hE''card : Nat.card E'' = 3 ^ 4 := hselfR E'' hE''elem hE''self
  have hcardE' : Nat.card E'' = Nat.card E := by
    change Nat.card ((E.subgroupOf Inn).map φ.toMonoidHom) = Nat.card E
    exact (Subgroup.card_map_of_injective φ.injective).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEinn).toEquiv)
  rw [← hcardE', hE''card]

private theorem ltqS3_kernel {X : Type} [Group X] [Finite X]
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hnorm : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J)
    (hd : GGTPNBasicB 3 (3 ^ 6) (fun _ _ => True) A Ab σ J)
    (hA5 : Nat.card A = 3 ^ 5)
    (himg : Nat.card (ltqS3_restrict A J hnorm).range = 3 ^ 4) :
    GGTPNKernel A σ J := by
  obtain ⟨hlocCore, hflat, -, -, hnum, hselfC, honly, hmarked⟩ := hd
  have hσmemA : σ ∈ A := hlocCore.2.1
  have hσ3 : σ ^ 3 = 1 := hlocCore.1.2 σ hσmemA
  have hσne : σ ≠ 1 := hlocCore.2.2.1
  have hfix : ∀ j ∈ J, σ j = j := fun j hj =>
    (mem_ggAutFixedSubgroup σ j).mp (hlocCore.2.2.2.1.1 hj)
  have hker_card : Nat.card (ltqS3_restrict A J hnorm).ker = 3 := by
    have h := Subgroup.card_ker_mul_card_range (ltqS3_restrict A J hnorm)
    rw [hA5, himg] at h
    have h3 : (3 : ℕ) ^ 5 = 3 * 3 ^ 4 := by norm_num
    rw [h3] at h
    exact Nat.mul_right_cancel (by norm_num : 0 < 3 ^ 4) h
  have hσker : (⟨σ, hσmemA⟩ : A) ∈ (ltqS3_restrict A J hnorm).ker := by
    rw [MonoidHom.mem_ker]
    ext j
    rw [ltqS3_restrict_apply]
    exact hfix j j.2
  have hzle : Subgroup.zpowers (⟨σ, hσmemA⟩ : A) ≤ (ltqS3_restrict A J hnorm).ker :=
    Subgroup.zpowers_le.mpr hσker
  have hσ3' : (⟨σ, hσmemA⟩ : A) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hσ3
  have hσne' : (⟨σ, hσmemA⟩ : A) ≠ 1 := by
    intro h
    exact hσne (Subtype.ext_iff.mp h)
  have hzpcard : Nat.card (Subgroup.zpowers (⟨σ, hσmemA⟩ : A)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hσ3' hσne'
  have hker_eq : Subgroup.zpowers (⟨σ, hσmemA⟩ : A) = (ltqS3_restrict A J hnorm).ker :=
    Subgroup.eq_of_le_of_card_ge hzle (by rw [hker_card, hzpcard])
  intro a ha hafix
  have hamem : (⟨a, ha⟩ : A) ∈ (ltqS3_restrict A J hnorm).ker := by
    rw [MonoidHom.mem_ker]
    ext j
    rw [ltqS3_restrict_apply]
    exact hafix j j.2
  rw [← hker_eq] at hamem
  rw [Subgroup.mem_zpowers_iff] at hamem
  rw [Subgroup.mem_zpowers_iff]
  obtain ⟨n, hn⟩ := hamem
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem ggB36KernelFail_of_transfer
    (hT : GGTPNTransferBNoCorners) (hInn : GGInnerOnD4) :
    GGB36KernelFail := by
  intro G _ _ p B Bs x L D J y K hc hL hK hn hp hcardBs labL labJ hΛL hΛJ htagL hhasL hhasJ
    hlabJ hJK hN hx
  subst hp
  obtain ⟨hJK', hN', hx', hd⟩ := hT G 3 B Bs x L D J y K hc hL hK hn
  rw [hcardBs] at hd
  have hAeq : ggAutsOf K Bs hN' = ggAutsOf K Bs hN := by
    ext a
    simp only [mem_ggAutsOf]
  have hAbeq : ggAutsOf K B (hc.2.1.1.trans hN') = ggAutsOf K B (hc.2.1.1.trans hN) := by
    ext a
    simp only [mem_ggAutsOf]
  have hσeq : K.normalizerMonoidHom ⟨x, hx'⟩ = K.normalizerMonoidHom ⟨x, hx⟩ := by
    ext k; rfl
  have hdB : GGTPNBasicB 3 (3 ^ 6) (fun _ _ => True) (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩)
      (J.subgroupOf K) := by
    have h := hd
    rw [hAeq, hAbeq, hσeq] at h
    exact h
  have hdB' := hdB
  obtain ⟨hlocCore, hflat, hcardAb, hrank, hnum, hselfC, honly, hmarked⟩ := hdB'
  have hnorm : ∀ a ∈ ggAutsOf K Bs hN,
      ∀ j ∈ J.subgroupOf K, a j ∈ J.subgroupOf K := hlocCore.2.2.2.2
  have hquasi : CFSG.Assembly.IsQuasisimple ↥(J.subgroupOf K) := hlocCore.2.2.2.1.2.2
  rcases ltqS3_numbers hlocCore.1 hflat hnum with hAbA | ⟨hA5, hAb4⟩
  · left
    rw [hAbA] at hflat
    exact hflat.2.2.2
  · rcases hlabJ with hA22 | htwA41 | hD4
    · rw [hA22] at hhasJ
      exact (ltqS3_A22_contra hdB (ltqS3_hasLabel_subgroupOf hJK hhasJ)).elim
    · left
      rw [htwA41] at hhasJ
      have hhasJ' : GGHasLabel ⟨.twA, 4, 1⟩
          (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
        ltqS3_hasLabel_subgroupOf hJK hhasJ
      have hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(J.subgroupOf K)) :=
        ltqS3_center_twA41 hquasi hhasJ'
      have hinner := ltqS3_inner_twA41 hdB hhasJ' hZ
      have himg := ltqS3_card_image hnorm hdB hhasJ' hZ hinner
        B36.twA41_selfCent_elemAbelian_three
      exact ltqS3_kernel hnorm hdB hA5 himg
    · have hlab : labJ = ⟨.D, 4, labL.n⟩ := hD4
      subst hlab
      have hhasJ' : GGHasLabel ⟨.D, 4, labL.n⟩
          (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
        ltqS3_hasLabel_subgroupOf hJK hhasJ
      have hΛJ' : LargeEvenInLambda2 ⟨.D, 4, labL.n⟩ := hΛJ
      have hnD : 1 ≤ labL.n := hΛJ'.1
      rcases ltqS3_inner_D4 hdB hInn hΛJ' hhasJ' rfl with hesc | hinner
      · right
        exact ⟨rfl, hesc⟩
      · left
        have hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(J.subgroupOf K)) :=
          ltqS3_center_D4 hnD hquasi hhasJ'
        have himg := ltqS3_card_image hnorm hdB hhasJ' hZ hinner
          (B36.d4_selfCent_elemAbelian_three hnD)
        exact ltqS3_kernel hnorm hdB hA5 himg

end CFSG.StandardType

end
