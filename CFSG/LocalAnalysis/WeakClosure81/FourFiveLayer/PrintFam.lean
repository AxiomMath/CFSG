module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5EF
import CFSG.Quasithin.Vol2.Ch11SecBRootLiftAux
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.CharacterTheory.CyclicBlocks.Family
import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
import CFSG.ClassicalGroups
import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.GH74.GLS.IVK.L2.F1
import CFSG.GH74.KGroups.L3EpsNoNormalThree
import CFSG.GH74.KGroups.L3EpsOutExp
import CFSG.GH74.KGroups.L3EpsOuterLin
import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
import CFSG.LieType.SeitzGeneration.UnitaryBlocks
import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
import CFSG.LocalAnalysis.SectionRank.QTK.Exc
import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bridge
import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
import CFSG.Permutation.UnitaryThreeRecognition.Model
import CFSG.Quasithin.Background.RonanE111Defs
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.OddKernel.CompleteRankComparison
import CFSG.RankThree.PartOne.KF.ClsPSL
import CFSG.RankThree.PartOne.KF.SU5Model
import CFSG.RankThree.PartOne.KF.SymCtxMatrix
import CFSG.RankThree.PartOne.KF.ToralQuot
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartOne.S11c.Sec66PSL
import CFSG.RankThree.PartOne.S11c.Sec66Sp
import CFSG.RankThree.PartOne.S11c.SuFiveD
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E1

variable {G : Type} [Group G]

@[expose] def IsEG (i : ℕ) (H T A Γ K : Subgroup G) : Prop :=
  K ≤ H ∧ tauOf H T A ≤ T ⊓ K ∧ IsSylowIn 2 (T ⊓ K) K ∧
    ((EOne ↥K (A.subgroupOf K) ∧ Nat.card (barO2 ↥K (A.subgroupOf K)) ≤ 2 ^ i) ∨
     (UniquenessCase.UC22.F12.ETwoPrint ↥K (Γ.subgroupOf K) (A.subgroupOf K) ∧
       Nat.card (barRad ↥K (A.subgroupOf K)) ≤ 2 ^ i))

theorem isEP_iff_isEG {i : ℕ} {H T A K : Subgroup G} :
    UniquenessCase.UC22.F12.IsEP i H T A K ↔ IsEG i H T A (tauOf H T A) K := Iff.rfl

theorem isEG_of_isE_of_isSolvable {i : ℕ} {H T A Γ K : Subgroup G} (h : IsE i H T A K)
    (hK : Group.IsSolvable ↥K) : IsEG i H T A Γ K :=
  ⟨h.1, h.2.1, h.2.2.1, Or.inl (isE_eOne_of_isSolvable h hK)⟩

private theorem eight_one_isEG [Finite G] {H₁ H₂ T A Γ K : Subgroup G} {i : ℕ}
    (hT : IsSylowIn 2 T H₁) (hA : A ≤ T) (hAab : IsElemAbelian 2 A) (hH : H₂ ≤ H₁)
    (hτ : tauOf H₁ T A ≤ T ⊓ H₂) (hS : IsSylowIn 2 (T ⊓ H₂) H₂)
    (hK : IsEG i H₂ (T ⊓ H₂) A Γ K) :
    A ⊔ pCoreOf 2 H₁ ≤ tauOf H₁ T A ∧ tauOf H₁ T A ≤ tauOf H₂ (T ⊓ H₂) A ∧
      tauOf H₂ (T ⊓ H₂) A ≤ tauOf K (T ⊓ K) A ∧ tauOf K (T ⊓ K) A ≤ K := by
  have h1 : A ⊔ pCoreOf 2 H₁ ≤ tauOf H₁ T A := le_tauOf hT hA hAab
  obtain ⟨hKH₂, hτK, -, -⟩ := hK
  have hAH₂ : A ≤ T ⊓ H₂ := fun a ha => hτ (h1 (Subgroup.mem_sup_left ha))
  have hO₁ : pCoreOf 2 H₁ ≤ H₂ := fun o ho => (hτ (h1 (Subgroup.mem_sup_right ho))).2
  have hO₁₂ : pCoreOf 2 H₁ ≤ pCoreOf 2 H₂ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hO₁
      (hH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₁))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₁)
  have h2 : tauOf H₁ T A ≤ tauOf H₂ (T ⊓ H₂) A := by
    intro t ht
    obtain ⟨-, -, ht3⟩ := mem_tauOf.mp ht
    exact (mem_tauOf_of_le inf_le_right).mpr ⟨hτ ht, fun a ha => hO₁₂ (ht3 a ha)⟩
  have h2' : A ⊔ pCoreOf 2 H₂ ≤ tauOf H₂ (T ⊓ H₂) A := le_tauOf hS hAH₂ hAab
  have hO₂K : pCoreOf 2 H₂ ≤ K := fun o ho => (hτK (h2' (Subgroup.mem_sup_right ho))).2
  have hO₂K' : pCoreOf 2 H₂ ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hO₂K
      (hKH₂.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₂))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₂)
  have hTK : (T ⊓ H₂) ⊓ K = T ⊓ K := by rw [inf_assoc, inf_eq_right.mpr hKH₂]
  have h3 : tauOf H₂ (T ⊓ H₂) A ≤ tauOf K (T ⊓ K) A := by
    intro t ht
    obtain ⟨-, -, ht3⟩ := mem_tauOf.mp ht
    have htK : t ∈ T ⊓ K := hTK ▸ hτK ht
    exact (mem_tauOf_of_le inf_le_right).mpr ⟨htK, fun a ha => hO₂K' (ht3 a ha)⟩
  exact ⟨h1, h2, h3, fun t ht => (tauOf_le _ _ _ ht).2⟩

theorem isEG_eight_two [Finite G] {H₁ H₂ T A Γ K : Subgroup G} {i : ℕ} (hT : IsSylowIn 2 T H₁)
    (hA : A ≤ T) (hAab : IsElemAbelian 2 A) (hH : H₂ ≤ H₁) (hτ : tauOf H₁ T A ≤ T ⊓ H₂)
    (hS : IsSylowIn 2 (T ⊓ H₂) H₂) (hK : IsEG i H₂ (T ⊓ H₂) A Γ K) : IsEG i H₁ T A Γ K := by
  obtain ⟨-, h2, h3, -⟩ := eight_one_isEG hT hA hAab hH hτ hS hK
  obtain ⟨hKH₂, -, hSK, hrest⟩ := hK
  have hTK : (T ⊓ H₂) ⊓ K = T ⊓ K := by rw [inf_assoc, inf_eq_right.mpr hKH₂]
  rw [hTK] at hSK
  exact ⟨hKH₂.trans hH, (h2.trans h3).trans (tauOf_le K (T ⊓ K) A), hSK, hrest⟩

private theorem subgroupOf_le_subgroupOf_iff_print {X Y H : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    X.subgroupOf H ≤ Y.subgroupOf H ↔ X ≤ Y := by
  rw [← Subgroup.map_le_map_iff_of_injective H.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hY]

private theorem map_subgroupOf_subgroupOfEquivOfLe_print {K H : Subgroup G} (hK : K ≤ H)
    (B : Subgroup G) :
    ((B.subgroupOf H).subgroupOf (K.subgroupOf H)).map
        (Subgroup.subgroupOfEquivOfLe hK).toMonoidHom = B.subgroupOf K := by
  ext ⟨x, hx⟩
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf]
  exact Iff.rfl

private theorem subgroupOf_map_subtype_eq_print (H : Subgroup G) (X' : Subgroup ↥H) :
    (X'.map H.subtype).subgroupOf H = X' :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective X'

theorem isEG_subgroupOf [Finite G] {i : ℕ} {H T A Γ K : Subgroup G} (hT : T ≤ H) (hA : A ≤ H)
    (hK : K ≤ H) :
    IsEG i H T A Γ K ↔ IsEG i (⊤ : Subgroup ↥H) (T.subgroupOf H) (A.subgroupOf H)
      (Γ.subgroupOf H) (K.subgroupOf H) := by
  have hTK : (T ⊓ K).subgroupOf H = T.subgroupOf H ⊓ K.subgroupOf H := rfl
  have hTKH : T ⊓ K ≤ H := inf_le_left.trans hT
  have htau := tauOf_top_subgroupOf hT hA
  unfold IsEG
  rw [← hTK, htau, subgroupOf_le_subgroupOf_iff_print ((tauOf_le H T A).trans hT) hTKH,
    isSylowIn_subgroupOf_iff hTKH hK,
    ← map_subgroupOf_subgroupOfEquivOfLe_print hK A,
    ← map_subgroupOf_subgroupOfEquivOfLe_print hK Γ,
    ← eOne_map, ← eTwoPrint_map_mulEquiv (Subgroup.subgroupOfEquivOfLe hK),
    card_barO2_map (Subgroup.subgroupOfEquivOfLe hK),
    card_barRad_map (Subgroup.subgroupOfEquivOfLe hK)]
  exact and_congr ⟨fun _ => le_top, fun _ => hK⟩ Iff.rfl

theorem isEG_map_subtype [Finite G] {i : ℕ} (H : Subgroup G) {T' A' Γ' K' : Subgroup ↥H} :
    IsEG i H (T'.map H.subtype) (A'.map H.subtype) (Γ'.map H.subtype) (K'.map H.subtype) ↔
      IsEG i ⊤ T' A' Γ' K' := by
  rw [isEG_subgroupOf (Subgroup.map_subtype_le T') (Subgroup.map_subtype_le A')
    (Subgroup.map_subtype_le K'), subgroupOf_map_subtype_eq_print,
    subgroupOf_map_subtype_eq_print, subgroupOf_map_subtype_eq_print,
    subgroupOf_map_subtype_eq_print]

theorem eTwoPrint_of_surjective {Q Q' : Type} [Group Q] [Group Q'] [Finite Q] [Finite Q']
    (φ : Q →* Q') (hφ : Function.Surjective φ)
    (hZ : IsTwoClosed ((CFSG.Open.pCore 2 Q').comap φ)) {Ta B : Subgroup Q}
    (hres : twoResidual (⊤ : Subgroup Q) = perfectCore (⊤ : Subgroup Q))
    (h : UniquenessCase.UC22.F12.ETwoPrint Q' (Ta.map φ) (B.map φ)) :
    UniquenessCase.UC22.F12.ETwoPrint Q Ta B := by
  have hker := isSolvable_ker_of_isTwoClosed φ hZ
  obtain ⟨hR', h2, -, h4⟩ := h
  refine ⟨isTwoClosed_solvableRadical φ hφ hZ hR', ?_, hres, ?_⟩
  · rw [pCore_two_quotient_eq_top_iff] at h2 ⊢
    intro x
    obtain ⟨k, hk⟩ := h2 (φ x)
    refine ⟨k, ?_⟩
    rw [oInftyE_eq_comap φ hφ hker, Subgroup.mem_comap, map_pow]
    exact hk
  · obtain ⟨ψ, hψ⟩ := exists_quotRadEquiv φ hφ hker
    have hτ : (Ta.map (QuotientGroup.mk' (CFSG.solvableRadical Q))).map ψ.toMonoidHom =
        (Ta.map φ).map (QuotientGroup.mk' (CFSG.solvableRadical Q')) := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      exact hψ x
    have hbar : (barRad Q B).map ψ.toMonoidHom = barRad Q' (B.map φ) := by
      unfold barRad
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      exact hψ x
    refine (exists_subgroup_congr ψ fun L => ?_).mpr h4
    refine and_congr ((CFSG.LocalCores.component_isomorphism ψ).1 L) (and_congr ?_ ?_)
    · have hb := map_biSup_conjSub ψ (Ta.map (QuotientGroup.mk' (CFSG.solvableRadical Q))) L
      unfold conjSub at hb
      rw [← map_inj_mulEquiv ψ, layer_map_mulEquiv, hb, hτ]
    · rw [card_barRad_eq_of_surjective φ hφ hker, ← hbar, ← Subgroup.map_commutator,
        map_inj_mulEquiv, ← Subgroup.map_equiv_normalizer_eq, map_le_map_iff_mulEquiv]

private theorem ten_seven_eTwo_sylow [Finite G] {T A Y : Subgroup G} [Y.Normal]
    (hT : IsSylowIn 2 T ⊤) (hA : A ≤ T) (hAab : IsElemAbelian 2 A) {I : Subgroup (G ⧸ Y)}
    (hIτ : tauOf ⊤ (T.map (QuotientGroup.mk' Y)) (A.map (QuotientGroup.mk' Y)) ≤
      T.map (QuotientGroup.mk' Y) ⊓ I)
    (hIS : IsSylowIn 2 (T.map (QuotientGroup.mk' Y) ⊓ I) I) :
    ∃ H1 T1 : Subgroup G, Y ≤ H1 ∧ H1.map (QuotientGroup.mk' Y) = I ∧ T ⊓ H1 = T1 ∧
      IsSylowIn 2 T1 H1 ∧ tauOf ⊤ T A ≤ T1 ∧ A ≤ T1 := by
  set π := QuotientGroup.mk' Y with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y
  set Tb : Subgroup (G ⧸ Y) := T.map π with hTb
  set Ab : Subgroup (G ⧸ Y) := A.map π with hAb
  have hTb' : IsSylowIn 2 Tb ⊤ := isSylowIn_two_map_top hπs hT
  set H1 : Subgroup G := I.comap π with hH1
  have hYH1 : Y ≤ H1 := fun y hy => by
    have h1 : π y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    show π y ∈ I
    rw [h1]
    exact Subgroup.one_mem _
  have hmapH1 : H1.map π = I := Subgroup.map_comap_eq_self_of_surjective hπs _
  have hSyl1 : IsSylowIn 2 (T ⊓ H1) H1 := by
    have hidx : ¬ 2 ∣ T.index := by
      have := hT.not_dvd_relIndex
      rwa [Subgroup.relIndex_top_right] at this
    let C : Sylow 2 G := hT.isPGroup.toSylow hidx
    have hC : (C : Subgroup G) = T := rfl
    have := isSylowIn_inf_of_quotient Y hYH1 C (by rw [hC, hmapH1]; exact hIS)
    rwa [hC] at this
  have hτT1 : tauOf ⊤ T A ≤ T ⊓ H1 := by
    intro t ht
    refine ⟨tauOf_le _ _ _ ht, ?_⟩
    have h1 : (tauOf ⊤ T A).map π ≤ tauOf ⊤ Tb Ab := by
      have := tauOf_map_le π (A := A) (le_top : T ≤ ⊤)
      rwa [Subgroup.map_top_of_surjective π hπs] at this
    exact (hIτ (h1 (Subgroup.mem_map_of_mem π ht))).2
  exact ⟨H1, T ⊓ H1, hYH1, hmapH1, rfl, hSyl1, hτT1,
    fun a ha => hτT1 (le_tauOf hT hA hAab (Subgroup.mem_sup_left ha))⟩

private theorem ten_seven_eTwo_minimal [Finite G] {T1 H1 Y : Subgroup G} [Y.Normal]
    {I : Subgroup (G ⧸ Y)} (hT1H1 : T1 ≤ H1) (hYH1 : Y ≤ H1)
    (hmapH1 : H1.map (QuotientGroup.mk' Y) = I) :
    ∃ J : Subgroup G, J ≤ H1 ∧ T1 ≤ J ∧ J ∈ sFamily T1 H1 Y ∧
      J.map (QuotientGroup.mk' Y) = I := by
  set π := QuotientGroup.mk' Y with hπ
  obtain ⟨J, hJmin⟩ := (Set.toFinite {K' : Subgroup G | K' ≤ H1 ⊔ T1 ∧ T1 ≤ K' ∧
      H1 ⊔ T1 = K' ⊔ Y}).exists_minimal ⟨H1 ⊔ T1, le_rfl, le_sup_right,
      (sup_eq_left.mpr (hYH1.trans le_sup_left)).symm⟩
  obtain ⟨hJle, hT1J, hEq, hmin⟩ : J ∈ sFamily T1 H1 Y :=
    ⟨hJmin.prop.1, hJmin.prop.2.1, hJmin.prop.2.2,
      fun K' h1 h2 h3 h4 => hJmin.eq_of_le ⟨h1, h2, h3⟩ h4⟩
  have hJH1 : J ≤ H1 := (sup_eq_left.mpr hT1H1) ▸ hJle
  have hYbot : Y.map π = ⊥ := (Subgroup.map_eq_bot_iff Y).mpr (QuotientGroup.ker_mk' Y).ge
  have hπJ : J.map π = I := by
    have h2 : (J ⊔ Y).map π = J.map π := by rw [Subgroup.map_sup, hYbot, sup_bot_eq]
    calc J.map π = (J ⊔ Y).map π := h2.symm
      _ = (H1 ⊔ T1).map π := by rw [hEq]
      _ = I := by rw [sup_eq_left.mpr hT1H1, hmapH1]
  exact ⟨J, hJH1, hT1J, ⟨hJle, hT1J, hEq, hmin⟩, hπJ⟩

private theorem ten_seven_eTwo_phi [Finite G] {Y H1 J T1 : Subgroup G} [Y.Normal]
    {I : Subgroup (G ⧸ Y)}
    (hπJ : J.map (QuotientGroup.mk' Y) = I) (hT1J : T1 ≤ J)
    (hSyl1 : IsSylowIn 2 T1 H1) (hJ : J ∈ sFamily T1 H1 Y) :
    ∃ φ : ↥J →* ↥I, Function.Surjective φ ∧
      IsTwoClosed ((CFSG.Open.pCore 2 ↥I).comap φ) ∧
      (∀ j : ↥J, ((φ j : ↥I) : G ⧸ Y) = QuotientGroup.mk' Y (j : G)) ∧
      ∀ j : ↥J, φ j = 1 → (j : G) ∈ Y := by
  set π := QuotientGroup.mk' Y with hπ
  have hmem : ∀ j : ↥J, π (j : G) ∈ I := by
    intro j
    rw [← hπJ]
    exact Subgroup.mem_map_of_mem π j.2
  let φ : ↥J →* ↥I := (π.comp J.subtype).codRestrict I hmem
  have hφval : ∀ j : ↥J, ((φ j : ↥I) : G ⧸ Y) = π j := fun _ => rfl
  have hφ : Function.Surjective φ := by
    intro y
    have hy : (y : G ⧸ Y) ∈ J.map π := by rw [hπJ]; exact y.2
    obtain ⟨j, hj, hjy⟩ := hy
    exact ⟨⟨j, hj⟩, Subtype.ext hjy⟩
  have hkerY : ∀ j : ↥J, φ j = 1 → (j : G) ∈ Y := fun j hj =>
    (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hj)
  have hZeq : (CFSG.Open.pCore 2 ↥I).comap φ = (preO2 J Y).subgroupOf J := by
    ext j
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    unfold preO2
    rw [Subgroup.mem_inf, Subgroup.mem_comap, hπJ]
    simp only [j.2, true_and]
    unfold pCoreOf
    exact (Subgroup.mem_map_iff_mem I.subtype_injective).symm
  have hZ : IsTwoClosed ((CFSG.Open.pCore 2 ↥I).comap φ) := by
    rw [hZeq]
    exact isTwoClosed_subgroupOf inf_le_left (ten_two hSyl1 le_rfl hJ)
  exact ⟨φ, hφ, hZ, hφval, hkerY⟩

private theorem ten_seven_eTwo_minimality {T Y H1 J T1 : Subgroup G} [Y.Normal]
    {I : Subgroup (G ⧸ Y)}
    (hJH1 : J ≤ H1) (hπJ : J.map (QuotientGroup.mk' Y) = I) (hJ : J ∈ sFamily T1 H1 Y)
    (hYH1 : Y ≤ H1) (hT1T : T1 ≤ T) (hT1J : T1 ≤ J) (φ : ↥J →* ↥I)
    (hkerY : ∀ j : ↥J, φ j = 1 → (j : G) ∈ Y) {M : Subgroup ↥J}
    (hSM : (T ⊓ J).subgroupOf J ≤ M) (hMk : M ⊔ φ.ker = ⊤) : M = ⊤ := by
  obtain ⟨hJle, -, hEq, hmin⟩ := hJ
  set M' : Subgroup G := M.map J.subtype with hM'
  have hM'J : M' ≤ J := Subgroup.map_subtype_le M
  have hT1M' : T1 ≤ M' := fun t ht =>
    ⟨⟨t, hT1J ht⟩, hSM (show t ∈ T ⊓ J from ⟨hT1T ht, hT1J ht⟩), rfl⟩
  have hJM : J ≤ M' ⊔ Y := by
    intro j hj
    have hjt : (⟨j, hj⟩ : ↥J) ∈ (↑(M ⊔ φ.ker) : Set ↥J) := by
      rw [hMk]
      exact Subgroup.mem_top _
    rw [Subgroup.coe_mul_of_left_le_normalizer_right M φ.ker (fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact Subgroup.mem_top x)] at hjt
    obtain ⟨m, hm, k, hk, hmk⟩ := hjt
    rw [show j = (m : G) * (k : G) from congrArg Subtype.val hmk.symm]
    exact Subgroup.mul_mem_sup ⟨m, hm, rfl⟩ (hkerY k hk)
  have hEqM : H1 ⊔ T1 = M' ⊔ Y := by
    refine le_antisymm ?_ ?_
    · rw [hEq]
      exact sup_le hJM le_sup_right
    · exact sup_le (hM'J.trans hJle) (hYH1.trans le_sup_left)
  have hMJ : M' = J := hmin M' (hM'J.trans hJle) hT1M' hEqM hM'J
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : (x : G) ∈ M' := by
    rw [hMJ]
    exact x.2
  obtain ⟨m, hm, hmx⟩ := hx
  have hxm : m = x := Subtype.ext hmx
  exact hxm ▸ hm

private theorem isSolvable_twoResidual_of_map [Finite G] {J Y : Subgroup G} [Y.Normal]
    {I : Subgroup (G ⧸ Y)} (hY : Group.IsSolvable ↥Y) (hI : Group.IsSolvable ↥I)
    (hres : twoResidual I = (twoResidual J).map (QuotientGroup.mk' Y)) :
    Group.IsSolvable ↥(twoResidual J) := by
  set π := QuotientGroup.mk' Y with hπ
  have hIres : Group.IsSolvable ↥(twoResidual I) := by
    have h1 : Group.IsSolvable ↥((twoResidual I).subgroupOf I) := inferInstance
    haveI := h1
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (twoResidual_le I)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe _).symm.injective
  have hJY : Group.IsSolvable ↥(twoResidual J ⊓ Y) := by
    have h1 : Group.IsSolvable ↥((twoResidual J ⊓ Y).subgroupOf Y) := inferInstance
    haveI := h1
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_right : twoResidual J ⊓ Y ≤ Y)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe _).symm.injective
  have hmap : ∀ x : ↥(twoResidual J), π (x : G) ∈ twoResidual I := by
    intro x
    rw [hres]
    exact Subgroup.mem_map_of_mem π x.2
  let f : ↥(twoResidual J) →* ↥(twoResidual I) :=
    (π.comp (twoResidual J).subtype).codRestrict _ hmap
  have hker : f.ker = (twoResidual J ⊓ Y).subgroupOf (twoResidual J) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hx => ⟨x.2, (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)⟩,
      fun hx => Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hx.2)⟩
  have hle : f.ker ≤
      (Subgroup.inclusion (inf_le_left : twoResidual J ⊓ Y ≤ twoResidual J)).range := by
    rw [hker, Subgroup.inclusion_range]
  haveI := hJY
  haveI := hIres
  exact Group.isSolvable_of_ker_le_range _ f hle

private theorem isSolvable_of_twoResidual_eq_map [Finite G] {J Y : Subgroup G} [Y.Normal]
    {I : Subgroup (G ⧸ Y)} (hY : Group.IsSolvable ↥Y) (hI : Group.IsSolvable ↥I)
    (hres : twoResidual I = (twoResidual J).map (QuotientGroup.mk' Y)) :
    Group.IsSolvable ↥J := by
  have hJres : Group.IsSolvable ↥(twoResidual J) := isSolvable_twoResidual_of_map hY hI hres
  have hNnorm : (twoResidual (⊤ : Subgroup ↥J)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  haveI := hNnorm
  have hQ2 : IsPGroup 2 (↥J ⧸ twoResidual (⊤ : Subgroup ↥J)) := by
    intro x
    obtain ⟨xH, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup ↥J) xH (Subgroup.mem_top _)
    exact ⟨k, by rw [← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).mpr hk]⟩
  have hQsolv : Group.IsSolvable (↥J ⧸ twoResidual (⊤ : Subgroup ↥J)) := by
    have := hQ2.isNilpotent
    infer_instance
  have hNsolv : Group.IsSolvable ↥(twoResidual (⊤ : Subgroup ↥J)) := by
    rw [B6.twoResidual_top_eq_subgroupOf J]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (twoResidual_le J)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe _).injective
  haveI := hNsolv
  haveI := hQsolv
  exact Group.isSolvable_of_subgroup_quotient (twoResidual (⊤ : Subgroup ↥J))

private theorem map_subgroupOf_map_print {X J Y : Subgroup G} [Y.Normal] {I : Subgroup (G ⧸ Y)}
    (φ : ↥J →* ↥I) (hφval : ∀ j : ↥J, ((φ j : ↥I) : G ⧸ Y) = QuotientGroup.mk' Y (j : G))
    (hXJ : X ≤ J) :
    (X.subgroupOf J).map φ = (X.map (QuotientGroup.mk' Y)).subgroupOf I := by
  set π := QuotientGroup.mk' Y with hπ
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [← hxy]
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [hφval x]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mp hx)
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_subgroupOf.mp hy
    refine ⟨⟨x, hXJ hx⟩, Subgroup.mem_subgroupOf.mpr hx, ?_⟩
    refine Subtype.ext ?_
    rw [hφval ⟨x, hXJ hx⟩]
    exact hxy

private theorem ten_seven_eTwo_finish [Finite G] {T A Γ Y : Subgroup G} [Y.Normal]
    {i : ℕ} {I : Subgroup (G ⧸ Y)} {J T1 H1 : Subgroup G} (hJH1 : J ≤ H1)
    (hπJ : J.map (QuotientGroup.mk' Y) = I) (hT1J : T1 ≤ J) (hTJ : T ⊓ J = T1)
    (hSyl1 : IsSylowIn 2 T1 H1) (hJ : J ∈ sFamily T1 H1 Y) (hYH1 : Y ≤ H1)
    (hτJ : tauOf ⊤ T A ≤ T ⊓ J) (hAJ : A ≤ J) (hΓT1 : Γ ≤ T1)
    (hE : UniquenessCase.UC22.F12.ETwoPrint ↥I ((Γ.map (QuotientGroup.mk' Y)).subgroupOf I)
      ((A.map (QuotientGroup.mk' Y)).subgroupOf I))
    (hcard : Nat.card (barRad ↥I ((A.map (QuotientGroup.mk' Y)).subgroupOf I)) ≤ 2 ^ i) :
    IsEG i ⊤ T A Γ J ∧ twoResidual I = (twoResidual J).map (QuotientGroup.mk' Y) := by
  set π := QuotientGroup.mk' Y with hπ
  obtain ⟨φ, hφ, hZ, hφval, hkerY⟩ := ten_seven_eTwo_phi hπJ hT1J hSyl1 hJ
  have hSylJ : IsSylowIn 2 T1 J := B6.isSylowTwoOf_mono hSyl1 hT1J hJH1
  have hSylS : IsSylowIn 2 ((T ⊓ J).subgroupOf J) ⊤ := by
    have h1 := (isSylowIn_subgroupOf_iff (P := T1) (K := J) (H := J) hT1J le_rfl).mpr hSylJ
    rwa [Subgroup.subgroupOf_self, ← hTJ] at h1
  have hBmap : (A.subgroupOf J).map φ = (A.map π).subgroupOf I :=
    map_subgroupOf_map_print φ hφval hAJ
  have hΓmap : (Γ.subgroupOf J).map φ = (Γ.map π).subgroupOf I :=
    map_subgroupOf_map_print φ hφval (hΓT1.trans hT1J)
  have hmin' : ∀ M : Subgroup ↥J, (T ⊓ J).subgroupOf J ≤ M → M ⊔ φ.ker = ⊤ → M = ⊤ :=
    fun M hSM hMk =>
      ten_seven_eTwo_minimality hJH1 hπJ hJ hYH1 (hTJ ▸ inf_le_left) hT1J φ hkerY hSM hMk
  have hres : twoResidual (⊤ : Subgroup ↥J) = perfectCore (⊤ : Subgroup ↥J) :=
    twoResidual_eq_perfectCore_of_surjective φ hφ hSylS hmin' hE.2.2.1
  have hETwo : UniquenessCase.UC22.F12.ETwoPrint ↥J (Γ.subgroupOf J) (A.subgroupOf J) :=
    eTwoPrint_of_surjective φ hφ hZ hres (by rw [hΓmap, hBmap]; exact hE)
  have hcard' : Nat.card (barRad ↥J (A.subgroupOf J)) ≤ 2 ^ i := by
    have h := card_barRad_eq_of_surjective φ hφ (isSolvable_ker_of_isTwoClosed φ hZ)
      (A.subgroupOf J)
    rw [← h, hBmap]
    exact hcard
  refine ⟨⟨le_top, hτJ, ?_, Or.inr ⟨hETwo, hcard'⟩⟩, ?_⟩
  · rw [hTJ]
    exact hSylJ
  · rw [map_twoResidual π J, hπJ]

theorem isEG_ten_seven [Finite G] {T A Γ Y : Subgroup G} [Y.Normal] (hT : IsSylowIn 2 T ⊤)
    (hA : A ≤ T) (hAab : IsElemAbelian 2 A) (hΓ : Γ ≤ tauOf ⊤ T A)
    (hY : Group.IsSolvable ↥Y) {i : ℕ} {I : Subgroup (G ⧸ Y)}
    (hI : IsEG i ⊤ (T.map (QuotientGroup.mk' Y)) (A.map (QuotientGroup.mk' Y))
      (Γ.map (QuotientGroup.mk' Y)) I) :
    ∃ J : Subgroup G, IsEG i ⊤ T A Γ J ∧
      twoResidual I = (twoResidual J).map (QuotientGroup.mk' Y) := by
  rcases hI.2.2.2 with ⟨hIE, hIcard⟩ | ⟨hIE, hIcard⟩
  · obtain ⟨J, hJ, hJres⟩ :=
      ten_seven_eOne hT hA hAab ⟨hI.1, hI.2.1, hI.2.2.1, Or.inl ⟨hIE, hIcard⟩⟩ ⟨hIE, hIcard⟩
    exact ⟨J, isEG_of_isE_of_isSolvable hJ
      (isSolvable_of_twoResidual_eq_map hY (RootLift.isSolvable_of_eOne hIE) hJres), hJres⟩
  · obtain ⟨H1, T1, hYH1, hmapH1, hT1eq, hSyl1, hτT1, hAT1⟩ :=
      ten_seven_eTwo_sylow hT hA hAab hI.2.1 hI.2.2.1
    obtain ⟨J, hJH1, hT1J, hJ, hπJ⟩ := ten_seven_eTwo_minimal hSyl1.le hYH1 hmapH1
    have hTJ : T ⊓ J = T1 := by
      refine le_antisymm ?_ (le_inf (hT1eq ▸ inf_le_left) hT1J)
      exact hT1eq ▸ le_inf inf_le_left (inf_le_right.trans hJH1)
    exact ⟨J, ten_seven_eTwo_finish hJH1 hπJ hT1J hTJ hSyl1 hJ hYH1
      (le_inf (tauOf_le _ _ _) (hτT1.trans hT1J)) (hAT1.trans hT1J) (hΓ.trans hτT1) hIE hIcard⟩

end CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer
