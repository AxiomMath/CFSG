module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestBasic
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoJProps
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveF4
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyNormalizer
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoJEq
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviBaseChange
public import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Excl
public import CFSG.RankThree.PartOne.KE6.Phi6Frame
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M24
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem e6a3_normal_eq_top_or_le_center {Q : Type*} [Group Q]
    (hQ : CFSG.Assembly.IsQuasisimple Q) {N : Subgroup Q} (hN : N.Normal) :
    N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅Subgroup.center Q, Subgroup.center Q⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup Q).map (QuotientGroup.mk' N) =
        (Subgroup.center Q).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator Q ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    rw [hp] at hcomm
    exact eq_top_iff.mpr hcomm

theorem eq_of_isComponentOf_of_le_normalizer {G : Type*} [Group G] {H J K' : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (J : Set G)) (hJ : CFSG.Assembly.IsQuasisimple ↥J)
    (hJK : J ≤ K') (hK : CFSG.Assembly.IsComponentOf K' H) : K' = J := by
  have hKN : K' ≤ Subgroup.normalizer (J : Set G) := hK.1.trans hH
  have hnorm : (J.subgroupOf K').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).2 hKN
  rcases e6a3_normal_eq_top_or_le_center hK.2.2 hnorm with h | h
  · exact le_antisymm (fun x hx => by
      have : (⟨x, hx⟩ : K') ∈ J.subgroupOf K' := h ▸ Subgroup.mem_top _
      exact this) hJK
  ·
    exfalso
    have hcomm : ∀ a b : ↥J, a * b = b * a := by
      intro a b
      have ha : (⟨a, hJK a.2⟩ : K') ∈ Subgroup.center K' := h a.2
      have hab := (Subgroup.mem_center_iff.mp ha) ⟨b, hJK b.2⟩
      exact Subtype.ext (congrArg Subtype.val hab).symm
    have hbot : commutator ↥J = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact hcomm y x
    have htop := hJ.1
    rw [hbot] at htop
    haveI := hJ.2.toNontrivial
    have hsub : Subsingleton ↥J := by
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Subgroup ↥J) := htop ▸ Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup ↥J) := htop ▸ Subgroup.mem_top b
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    obtain ⟨u, v, huv⟩ := exists_pair_ne (↥J ⧸ Subgroup.center ↥J)
    induction u using QuotientGroup.induction_on
    induction v using QuotientGroup.induction_on
    exact huv (congrArg _ (Subsingleton.elim _ _))

section Data

private noncomputable def e6a3_omega : F4ˣ := Units.mk0 f4Omega f4Omega_ne_zero

private def e6a3_alpha (i : Fin (Tag.rank .E6)) : Fin (Tag.rank .E6) → ℤ :=
  Pi.single i 1

private def e6a3_i0 : Fin (Tag.rank .E6) := ⟨0, by decide⟩

private def e6a3_i3 : Fin (Tag.rank .E6) := ⟨3, by decide⟩

private def e6a3_i5 : Fin (Tag.rank .E6) := ⟨5, by decide⟩

private def e6a3_Apos : List (Fin (Tag.rank .E6) → ℤ) :=
  [![0, 0, 1, 1, 0, 0], ![0, 0, 0, 0, 1, 1], ![0, 0, 1, 1, 1, 1]]

private def e6a3_Bpos : List (Fin (Tag.rank .E6) → ℤ) :=
  [![0, 1, 1, 1, 1, 0], ![1, 1, 1, 2, 1, 1], highRoot .E6]

private def e6a3_Cpos : List (Fin (Tag.rank .E6) → ℤ) :=
  [![1, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 0], ![1, 0, 1, 1, 1, 0]]

private def e6a3_component (l : List (Fin (Tag.rank .E6) → ℤ)) :
    Set (Fin (Tag.rank .E6) → ℤ) :=
  {γ | γ ∈ l ∨ -γ ∈ l}

private def e6a3_A : Set (Fin (Tag.rank .E6) → ℤ) := e6a3_component e6a3_Apos

private def e6a3_B : Set (Fin (Tag.rank .E6) → ℤ) := e6a3_component e6a3_Bpos

private def e6a3_C : Set (Fin (Tag.rank .E6) → ℤ) := e6a3_component e6a3_Cpos

private def e6a3_PhiD : Set (Fin (Tag.rank .E6) → ℤ) := e6a3_A ∪ e6a3_B ∪ e6a3_C

private def e6a3_S : Set (Fin (Tag.rank .E6) → ℤ) := e6a3_A ∪ e6a3_C

private noncomputable def e6a3_dChar : Fin (Tag.rank .E6) → F4ˣ :=
  fun l => e6a3_omega ^ (Tag.cartan .E6 e6a3_i0 l + Tag.cartan .E6 e6a3_i3 l +
    Tag.cartan .E6 e6a3_i5 l)

private noncomputable def e6a3_d :
    ModGL .E6 F4 :=
  torusElt .E6 F4 e6a3_i0 e6a3_omega * torusElt .E6 F4 e6a3_i3 e6a3_omega *
    torusElt .E6 F4 e6a3_i5 e6a3_omega

private noncomputable def e6a3_P0
    (i : Fin (Tag.rank .E6)) : ModGL .E6 F4 :=
  pinnedX .E6 F4 (-(e6a3_alpha i)) (e6a3_omega : F4) * pinnedX .E6 F4 (e6a3_alpha i) 1

private noncomputable def e6a3_P :
    ModGL .E6 F4 :=
  e6a3_P0 e6a3_i0 * e6a3_P0 e6a3_i3 * e6a3_P0 e6a3_i5

private noncomputable def e6a3_iota : F2 →+* F4 :=
  letI : Fintype F2 := Fintype.ofFinite F2
  let e : ZMod 2 ≃+* F2 := ZMod.ringEquiv (R := F2) (n := 2) (by
    rw [← Nat.card_eq_fintype_card]
    simpa using GaloisField.card 2 1 (by omega))
  (ZMod.castHom (show 2 ∣ 2 by decide) F4).comp e.symm.toRingHom

private noncomputable def e6a3_wF :
    ModGL .E6 F4 :=
  baseChangeGL e6a3_iota (wOmegaE : ModGL .E6 F2)

private noncomputable def e6a3_nu :
    ModGL .E6 F4 :=
  weylElt .E6 F4 e6a3_i0 1 * weylElt .E6 F4 e6a3_i3 1 * weylElt .E6 F4 e6a3_i5 1

private noncomputable def e6a3_F :
    ModGL .E6 F4 →* ModGL .E6 F4 :=
  baseChangeGL (frobenius F4 2)

private noncomputable def e6a3_baseChange :
    EC →* ModGL .E6 F4 :=
  (baseChangeGL e6a3_iota).comp (adjointGroup .E6 F2).subtype

private noncomputable def e6a3_GS :
    Subgroup (ModGL .E6 F4) :=
  rootSpan .E6 F4 e6a3_S

private noncomputable def e6a3_H :
    Subgroup EC :=
  (e6a3_GS.map (MulAut.conj e6a3_P).toMonoidHom).comap e6a3_baseChange

end Data

private theorem e6a3_d_eq_rootDiagUnit
    :
    e6a3_d = rootDiagUnit .E6 e6a3_dChar := by
  rw [e6a3_d, CFSG.LieType.Chevalley.torusElt_eq_rootDiagUnit,
    CFSG.LieType.Chevalley.torusElt_eq_rootDiagUnit,
    CFSG.LieType.Chevalley.torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  funext l
  rw [e6a3_dChar]
  simp only [Pi.mul_apply, zpow_add]

private theorem e6a3_omega_add_sq
    :
    (e6a3_omega : F4) + (e6a3_omega : F4) ^ 2 = 1 := by
  have h := f4Omega_sq
  have h' : (f4Omega : F4) ^ 2 + f4Omega = -1 := by linear_combination h
  rw [CharTwo.neg_eq] at h'
  rw [add_comm]
  exact h'

private theorem e6a3_weylElt_eq (i : Fin (Tag.rank .E6)) :
    weylElt .E6 F4 i 1 =
      pinnedX .E6 F4 (e6a3_alpha i) 1 * pinnedX .E6 F4 (-(e6a3_alpha i)) (-1) *
        pinnedX .E6 F4 (e6a3_alpha i) 1 := by
  rw [CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul, e6a3_alpha, ← pinnedX_single,
    ← pinnedX_neg_single]
  simp

private theorem e6a3_P0_frob_factor (i : Fin (Tag.rank .E6)) :
    (e6a3_P0 i)⁻¹ * e6a3_F (e6a3_P0 i) = weylElt .E6 F4 i 1 := by
  have hF : e6a3_F (e6a3_P0 i) =
      pinnedX .E6 F4 (-(e6a3_alpha i)) ((e6a3_omega : F4) ^ 2) *
        pinnedX .E6 F4 (e6a3_alpha i) 1 := by
    simp only [e6a3_F, e6a3_P0, map_mul, baseChangeGL_pinnedX, frobenius_def, one_pow]
  rw [hF, e6a3_P0, mul_inv_rev, pinnedX_neg, pinnedX_neg]
  rw [e6a3_weylElt_eq]
  rw [← mul_assoc (pinnedX .E6 F4 (e6a3_alpha i) (-1) *
      pinnedX .E6 F4 (-(e6a3_alpha i)) (-(e6a3_omega : F4)))
      (pinnedX .E6 F4 (-(e6a3_alpha i)) ((e6a3_omega : F4) ^ 2))
      (pinnedX .E6 F4 (e6a3_alpha i) 1)]
  rw [mul_assoc (pinnedX .E6 F4 (e6a3_alpha i) (-1))
      (pinnedX .E6 F4 (-(e6a3_alpha i)) (-(e6a3_omega : F4)))
      (pinnedX .E6 F4 (-(e6a3_alpha i)) ((e6a3_omega : F4) ^ 2))]
  rw [← pinnedX_add]
  have hpar : (-(e6a3_omega : F4)) + ((e6a3_omega : F4)) ^ 2 = 1 := by
    rw [CharTwo.neg_eq]
    exact e6a3_omega_add_sq
  rw [hpar]
  rw [CharTwo.neg_eq]

private theorem e6a3xa_prod_inv_mul {G : Type*} [Group G] (a0 a1 a2 n0 n1 n2 : G)
    (h01 : Commute n0 a1) (h02 : Commute n0 a2) (h12 : Commute n1 a2) :
    (a0 * a1 * a2)⁻¹ * ((a0 * n0) * (a1 * n1) * (a2 * n2)) = n0 * n1 * n2 := by
  have e1 : a1⁻¹ * n0 * a1 = n0 := by
    rw [mul_assoc, h01.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have e2 : a2⁻¹ * n0 * a2 = n0 := by
    rw [mul_assoc, h02.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have e3 : a2⁻¹ * n1 * a2 = n1 := by
    rw [mul_assoc, h12.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  calc (a0 * a1 * a2)⁻¹ * ((a0 * n0) * (a1 * n1) * (a2 * n2))
      = a2⁻¹ * a1⁻¹ * (n0 * a1) * n1 * a2 * n2 := by group
    _ = a2⁻¹ * (a1⁻¹ * n0 * a1) * n1 * a2 * n2 := by group
    _ = a2⁻¹ * n0 * n1 * a2 * n2 := by rw [e1]
    _ = a2⁻¹ * n0 * (n1 * a2) * n2 := by group
    _ = a2⁻¹ * n0 * (a2 * n1) * n2 := by rw [h12.eq]
    _ = (a2⁻¹ * n0 * a2) * n1 * n2 := by group
    _ = n0 * n1 * n2 := by rw [e2]

private theorem e6a3xa_iform_self_root
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) : iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  rw [show Tag.symmetrizer .E6 j j = 1 by simp [Tag.symmetrizer], mul_one] at hj
  exact hj

private theorem e6a3xa_not_isRoot_add_of_orthogonal
    {α β : Fin (Tag.rank .E6) → ℤ}
    (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β) (h0 : iform α β = 0) :
    ¬ IsRoot .E6 (α + β) := by
  intro h
  have h2 := e6a3xa_iform_self_root h
  have hα2 := e6a3xa_iform_self_root hα
  have hβ2 := e6a3xa_iform_self_root hβ
  have h0' : iform β α = 0 := by rw [iform_comm]; exact h0
  rw [iform_add_left, iform_add_right, iform_add_right, h0, h0', hα2, hβ2] at h2
  norm_num at h2

private theorem e6a3xa_pinnedX_commute
    {α β : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β)
    (h0 : iform α β = 0) (hp : ¬ IsRoot .E6 (α + β)) (c d : F4) :
    Commute (pinnedX .E6 F4 α c) (pinnedX .E6 F4 β d) :=
  pinnedX_commute_of_iform_eq_zero F4 hα hβ h0 hp c d

private theorem e6a3xa_commute_pp
    {i j : Fin (Tag.rank .E6)} (hij : i ≠ j)
    (h0 : iform (Pi.single i 1) (Pi.single j 1) = 0) (c d : F4) :
    Commute (pinnedX .E6 F4 (Pi.single i 1) c) (pinnedX .E6 F4 (Pi.single j 1) d) :=
  e6a3xa_pinnedX_commute (isRoot_single .E6 i) (isRoot_single .E6 j) h0
    (e6a3xa_not_isRoot_add_of_orthogonal (isRoot_single .E6 i) (isRoot_single .E6 j) h0) c d

private theorem e6a3xa_commute_pn
    {i j : Fin (Tag.rank .E6)} (hij : i ≠ j)
    (h0 : iform (Pi.single i 1) (Pi.single j 1) = 0) (c d : F4) :
    Commute (pinnedX .E6 F4 (Pi.single i 1) c) (pinnedX .E6 F4 (-Pi.single j 1) d) := by
  have h0' : iform (Pi.single i 1) (-Pi.single j 1) = 0 := by rw [iform_neg_right, h0, neg_zero]
  exact e6a3xa_pinnedX_commute (isRoot_single .E6 i) (isRoot_neg_single .E6 j) h0'
    (e6a3xa_not_isRoot_add_of_orthogonal (isRoot_single .E6 i) (isRoot_neg_single .E6 j) h0') c d

private theorem e6a3xa_commute_np
    {i j : Fin (Tag.rank .E6)} (hij : i ≠ j)
    (h0 : iform (Pi.single i 1) (Pi.single j 1) = 0) (c d : F4) :
    Commute (pinnedX .E6 F4 (-Pi.single i 1) c) (pinnedX .E6 F4 (Pi.single j 1) d) := by
  have h0' : iform (-Pi.single i 1) (Pi.single j 1) = 0 := by rw [iform_neg_left, h0, neg_zero]
  exact e6a3xa_pinnedX_commute (isRoot_neg_single .E6 i) (isRoot_single .E6 j) h0'
    (e6a3xa_not_isRoot_add_of_orthogonal (isRoot_neg_single .E6 i) (isRoot_single .E6 j) h0') c d

private theorem e6a3xa_commute_nn
    {i j : Fin (Tag.rank .E6)} (hij : i ≠ j)
    (h0 : iform (Pi.single i 1) (Pi.single j 1) = 0) (c d : F4) :
    Commute (pinnedX .E6 F4 (-Pi.single i 1) c) (pinnedX .E6 F4 (-Pi.single j 1) d) := by
  have h0' : iform (-Pi.single i 1) (-Pi.single j 1) = 0 := by
    rw [iform_neg_left, iform_neg_right, h0, neg_zero, neg_zero]
  have hp : ¬ IsRoot .E6 (-Pi.single i 1 + -Pi.single j 1) := by
    rw [← neg_add]
    exact fun h => e6a3xa_not_isRoot_add_of_orthogonal (isRoot_single .E6 i)
      (isRoot_single .E6 j) h0 (by simpa using IsRoot.neg h)
  exact e6a3xa_pinnedX_commute (isRoot_neg_single .E6 i) (isRoot_neg_single .E6 j) h0' hp c d

private theorem e6a3xa_commute_weylElt_P0
    {i j : Fin (Tag.rank .E6)} (hij : i ≠ j)
    (h0 : iform (Pi.single i 1) (Pi.single j 1) = 0) :
    Commute (weylElt .E6 F4 i 1) (e6a3_P0 j) := by
  set xi := pinnedX .E6 F4 (Pi.single i 1) 1
  set yi := pinnedX .E6 F4 (-Pi.single i 1) (-1)
  set yj := pinnedX .E6 F4 (-Pi.single j 1) (e6a3_omega : F4)
  set xj := pinnedX .E6 F4 (Pi.single j 1) 1
  have hxy : Commute xi yj := e6a3xa_commute_pn hij h0 1 _
  have hxx : Commute xi xj := e6a3xa_commute_pp hij h0 1 1
  have hyy : Commute yi yj := e6a3xa_commute_nn hij h0 (-1) _
  have hyx : Commute yi xj := e6a3xa_commute_np hij h0 (-1) 1
  have hA : Commute (xi * yi * xi) yj := by
    rw [Commute]
    calc xi * yi * xi * yj = xi * yi * (xi * yj) := by group
      _ = xi * yi * (yj * xi) := by rw [hxy.eq]
      _ = xi * (yi * yj) * xi := by group
      _ = xi * (yj * yi) * xi := by rw [hyy.eq]
      _ = (xi * yj) * yi * xi := by group
      _ = (yj * xi) * yi * xi := by rw [hxy.eq]
      _ = yj * (xi * yi * xi) := by group
  have hB : Commute (xi * yi * xi) xj := by
    rw [Commute]
    calc xi * yi * xi * xj = xi * yi * (xi * xj) := by group
      _ = xi * yi * (xj * xi) := by rw [hxx.eq]
      _ = xi * (yi * xj) * xi := by group
      _ = xi * (xj * yi) * xi := by rw [hyx.eq]
      _ = (xi * xj) * yi * xi := by group
      _ = (xj * xi) * yi * xi := by rw [hxx.eq]
      _ = xj * (xi * yi * xi) := by group
  rw [e6a3_weylElt_eq, e6a3_P0, e6a3_alpha]
  exact hA.mul_right hB

private theorem e6a3xa_conj_prod {G : Type*} [Group G] (a0 a1 a2 z0 z1 z2 d0 d1 d2 : G)
    (h0 : a0⁻¹ * z0 * a0 = d0) (h1 : a1⁻¹ * z1 * a1 = d1) (h2 : a2⁻¹ * z2 * a2 = d2)
    (ha01 : Commute a0 a1) (ha02 : Commute a0 a2) (ha12 : Commute a1 a2)
    (ha0z1 : Commute a0 z1) (ha0z2 : Commute a0 z2)
    (ha1z0 : Commute a1 z0) (ha1z2 : Commute a1 z2)
    (ha2z0 : Commute a2 z0) (ha2z1 : Commute a2 z1) :
    (a0 * a1 * a2)⁻¹ * (z0 * z1 * z2) * (a0 * a1 * a2) = d0 * d1 * d2 := by
  have hX0 : Commute a1 (a0⁻¹ * z0 * a0) :=
    ((ha01.symm.inv_right).mul_right ha1z0).mul_right ha01.symm
  have hX0' : Commute a2 (a0⁻¹ * z0 * a0) :=
    ((ha02.symm.inv_right).mul_right ha2z0).mul_right ha02.symm
  have hX1 : Commute a0 (a1⁻¹ * z1 * a1) :=
    ((ha01.inv_right).mul_right ha0z1).mul_right ha01
  have hX1' : Commute a2 (a1⁻¹ * z1 * a1) :=
    ((ha12.symm.inv_right).mul_right ha2z1).mul_right ha12.symm
  have hX2 : Commute a0 (a2⁻¹ * z2 * a2) :=
    ((ha02.inv_right).mul_right ha0z2).mul_right ha02
  have hX2' : Commute a1 (a2⁻¹ * z2 * a2) :=
    ((ha12.inv_right).mul_right ha1z2).mul_right ha12
  have e0 : a1⁻¹ * (a0⁻¹ * z0 * a0) * a1 = a0⁻¹ * z0 * a0 := by
    calc a1⁻¹ * (a0⁻¹ * z0 * a0) * a1 = a1⁻¹ * ((a0⁻¹ * z0 * a0) * a1) := by group
      _ = a1⁻¹ * (a1 * (a0⁻¹ * z0 * a0)) := by rw [← hX0.eq]
      _ = a0⁻¹ * z0 * a0 := by group
  have e0' : a2⁻¹ * (a0⁻¹ * z0 * a0) * a2 = a0⁻¹ * z0 * a0 := by
    calc a2⁻¹ * (a0⁻¹ * z0 * a0) * a2 = a2⁻¹ * ((a0⁻¹ * z0 * a0) * a2) := by group
      _ = a2⁻¹ * (a2 * (a0⁻¹ * z0 * a0)) := by rw [← hX0'.eq]
      _ = a0⁻¹ * z0 * a0 := by group
  have e1 : a0⁻¹ * (a1⁻¹ * z1 * a1) * a0 = a1⁻¹ * z1 * a1 := by
    calc a0⁻¹ * (a1⁻¹ * z1 * a1) * a0 = a0⁻¹ * ((a1⁻¹ * z1 * a1) * a0) := by group
      _ = a0⁻¹ * (a0 * (a1⁻¹ * z1 * a1)) := by rw [← hX1.eq]
      _ = a1⁻¹ * z1 * a1 := by group
  have e1' : a2⁻¹ * (a1⁻¹ * z1 * a1) * a2 = a1⁻¹ * z1 * a1 := by
    calc a2⁻¹ * (a1⁻¹ * z1 * a1) * a2 = a2⁻¹ * ((a1⁻¹ * z1 * a1) * a2) := by group
      _ = a2⁻¹ * (a2 * (a1⁻¹ * z1 * a1)) := by rw [← hX1'.eq]
      _ = a1⁻¹ * z1 * a1 := by group
  have e2 : a0⁻¹ * (a2⁻¹ * z2 * a2) * a0 = a2⁻¹ * z2 * a2 := by
    calc a0⁻¹ * (a2⁻¹ * z2 * a2) * a0 = a0⁻¹ * ((a2⁻¹ * z2 * a2) * a0) := by group
      _ = a0⁻¹ * (a0 * (a2⁻¹ * z2 * a2)) := by rw [← hX2.eq]
      _ = a2⁻¹ * z2 * a2 := by group
  have e2' : a1⁻¹ * (a2⁻¹ * z2 * a2) * a1 = a2⁻¹ * z2 * a2 := by
    calc a1⁻¹ * (a2⁻¹ * z2 * a2) * a1 = a1⁻¹ * ((a2⁻¹ * z2 * a2) * a1) := by group
      _ = a1⁻¹ * (a1 * (a2⁻¹ * z2 * a2)) := by rw [← hX2'.eq]
      _ = a2⁻¹ * z2 * a2 := by group
  have e0z : a0⁻¹ * z0 * a0 = a0⁻¹ * z0 * a0 := rfl
  have e1z : a0⁻¹ * z1 * a0 = z1 := by
    calc a0⁻¹ * z1 * a0 = a0⁻¹ * (z1 * a0) := by group
      _ = a0⁻¹ * (a0 * z1) := by rw [← ha0z1.eq]
      _ = z1 := by group
  have e2z : a0⁻¹ * z2 * a0 = z2 := by
    calc a0⁻¹ * z2 * a0 = a0⁻¹ * (z2 * a0) := by group
      _ = a0⁻¹ * (a0 * z2) := by rw [← ha0z2.eq]
      _ = z2 := by group
  have e2z' : a1⁻¹ * z2 * a1 = z2 := by
    calc a1⁻¹ * z2 * a1 = a1⁻¹ * (z2 * a1) := by group
      _ = a1⁻¹ * (a1 * z2) := by rw [← ha1z2.eq]
      _ = z2 := by group
  have hZ0 : (a0 * a1 * a2)⁻¹ * z0 * (a0 * a1 * a2) = a0⁻¹ * z0 * a0 := by
    calc (a0 * a1 * a2)⁻¹ * z0 * (a0 * a1 * a2)
        = a2⁻¹ * a1⁻¹ * a0⁻¹ * z0 * (a0 * a1 * a2) := by group
      _ = a2⁻¹ * a1⁻¹ * (a0⁻¹ * z0 * a0) * a1 * a2 := by group
      _ = a2⁻¹ * (a1⁻¹ * (a0⁻¹ * z0 * a0) * a1) * a2 := by group
      _ = a2⁻¹ * (a0⁻¹ * z0 * a0) * a2 := by rw [e0]
      _ = a0⁻¹ * z0 * a0 := by rw [e0']
  have hZ1 : (a0 * a1 * a2)⁻¹ * z1 * (a0 * a1 * a2) = a1⁻¹ * z1 * a1 := by
    calc (a0 * a1 * a2)⁻¹ * z1 * (a0 * a1 * a2)
        = a2⁻¹ * a1⁻¹ * a0⁻¹ * z1 * (a0 * a1 * a2) := by group
      _ = a2⁻¹ * a1⁻¹ * (a0⁻¹ * z1 * a0) * a1 * a2 := by group
      _ = a2⁻¹ * a1⁻¹ * z1 * a1 * a2 := by rw [e1z]
      _ = a2⁻¹ * (a1⁻¹ * z1 * a1) * a2 := by group
      _ = a1⁻¹ * z1 * a1 := by rw [e1']
  have hZ2 : (a0 * a1 * a2)⁻¹ * z2 * (a0 * a1 * a2) = a2⁻¹ * z2 * a2 := by
    calc (a0 * a1 * a2)⁻¹ * z2 * (a0 * a1 * a2)
        = a2⁻¹ * a1⁻¹ * a0⁻¹ * z2 * (a0 * a1 * a2) := by group
      _ = a2⁻¹ * a1⁻¹ * (a0⁻¹ * z2 * a0) * a1 * a2 := by group
      _ = a2⁻¹ * a1⁻¹ * z2 * a1 * a2 := by rw [e2z]
      _ = a2⁻¹ * (a1⁻¹ * z2 * a1) * a2 := by group
      _ = a2⁻¹ * z2 * a2 := by rw [e2z']
  have hZ : (a0 * a1 * a2)⁻¹ * (z0 * z1 * z2) * (a0 * a1 * a2) =
      ((a0 * a1 * a2)⁻¹ * z0 * (a0 * a1 * a2)) * ((a0 * a1 * a2)⁻¹ * z1 * (a0 * a1 * a2)) *
        ((a0 * a1 * a2)⁻¹ * z2 * (a0 * a1 * a2)) := by group
  rw [hZ, hZ0, hZ1, hZ2, h0, h1, h2]

private theorem e6a3xa_sl2 :
    (vSL (f4Omega : F4) * uSL 1)⁻¹ * (uSL 1 * vSL 1) * (vSL (f4Omega : F4) * uSL 1) =
      HSL (Units.mk0 f4Omega f4Omega_ne_zero) := by
  have h2 : (2 : F4) = 0 := CharTwo.two_eq_zero
  have hω : (f4Omega : F4) ^ 2 + f4Omega + 1 = 0 := f4Omega_sq
  have hωinv : (f4Omega : F4)⁻¹ = f4Omega ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [mul_comm, ← pow_succ, f4Omega_pow_three]
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_uSL, coe_vSL, coe_HSL, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.adjugate_fin_two, hωinv]
  all_goals
    first
    | linear_combination hω
    | linear_combination hω + f4Omega * h2
    | linear_combination -hω + h2
    | linear_combination (-(f4Omega ^ 2) - f4Omega + 1) * h2

private theorem e6a3xa_P0_conj_z (i : Fin (Tag.rank .E6)) :
    (e6a3_P0 i)⁻¹ * (pinnedX .E6 F4 (e6a3_alpha i) 1 *
      pinnedX .E6 F4 (-(e6a3_alpha i)) 1) * e6a3_P0 i = torusElt .E6 F4 i e6a3_omega := by
  obtain ⟨ρ, hu, hv, hH, -, -, -, -, -⟩ :=
    exceptional_ordinary_rank_one_central_image (τ := .E6) (K := F4) i
  have hP : e6a3_P0 i = yUnit .E6 F4 i (e6a3_omega : F4) * xUnit .E6 F4 i 1 := by
    rw [e6a3_P0, e6a3_alpha, ← pinnedX_single, ← pinnedX_neg_single]
  have hZ : pinnedX .E6 F4 (e6a3_alpha i) 1 * pinnedX .E6 F4 (-(e6a3_alpha i)) 1 =
      xUnit .E6 F4 i 1 * yUnit .E6 F4 i 1 := by
    rw [e6a3_alpha, ← pinnedX_single, ← pinnedX_neg_single]
  have hsl := e6a3xa_sl2
  have hmap := congrArg ρ hsl
  simp only [map_mul, map_inv, hu, hv, hH] at hmap
  rw [hP, hZ]
  exact hmap

private theorem e6a3xa_a5Root_0 : a5Root (blk 0 0) (blk 0 1) = e6a3_alpha e6a3_i0 := by decide
private theorem e6a3xa_a5Root_0' : a5Root (blk 0 1) (blk 0 0) = -(e6a3_alpha e6a3_i0) := by decide
private theorem e6a3xa_a5Root_1 : a5Root (blk 1 0) (blk 1 1) = e6a3_alpha e6a3_i3 := by decide
private theorem e6a3xa_a5Root_1' : a5Root (blk 1 1) (blk 1 0) = -(e6a3_alpha e6a3_i3) := by decide
private theorem e6a3xa_a5Root_2 : a5Root (blk 2 0) (blk 2 1) = e6a3_alpha e6a3_i5 := by decide
private theorem e6a3xa_a5Root_2' : a5Root (blk 2 1) (blk 2 0) = -(e6a3_alpha e6a3_i5) := by decide

private theorem e6a3xa_wF_eq :
    e6a3_wF = (pinnedX .E6 F4 (e6a3_alpha e6a3_i0) 1 *
        pinnedX .E6 F4 (-(e6a3_alpha e6a3_i0)) 1) *
      ((pinnedX .E6 F4 (e6a3_alpha e6a3_i3) 1 * pinnedX .E6 F4 (-(e6a3_alpha e6a3_i3)) 1) *
      (pinnedX .E6 F4 (e6a3_alpha e6a3_i5) 1 * pinnedX .E6 F4 (-(e6a3_alpha e6a3_i5)) 1)) := by
  rw [e6a3_wF, wOmegaE]
  simp only [cOmegaE, xr, Subgroup.coe_mul, Subgroup.coe_one, map_mul, baseChangeGL_pinnedX,
    map_one, one_mul, mul_one]
  rw [e6a3xa_a5Root_0, e6a3xa_a5Root_0', e6a3xa_a5Root_1, e6a3xa_a5Root_1',
    e6a3xa_a5Root_2, e6a3xa_a5Root_2']
  group

private theorem e6a3xa_closure_commute
    {i j : Fin (Tag.rank .E6)} (hij : i ≠ j)
    (h0 : iform (Pi.single i 1) (Pi.single j 1) = 0) :
    ∀ g ∈ Subgroup.closure (Set.range (pinnedX .E6 F4 (Pi.single i 1)) ∪
        Set.range (pinnedX .E6 F4 (-Pi.single i 1))),
      ∀ h ∈ Subgroup.closure (Set.range (pinnedX .E6 F4 (Pi.single j 1)) ∪
        Set.range (pinnedX .E6 F4 (-Pi.single j 1))), g * h = h * g := by
  refine closure_commute ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
  · exact (e6a3xa_commute_pp hij h0 c d).eq
  · exact (e6a3xa_commute_pn hij h0 c d).eq
  · exact (e6a3xa_commute_np hij h0 c d).eq
  · exact (e6a3xa_commute_nn hij h0 c d).eq

private theorem e6a3xa_mem_closure
    (i : Fin (Tag.rank .E6)) :
    e6a3_P0 i ∈ Subgroup.closure (Set.range (pinnedX .E6 F4 (Pi.single i 1)) ∪
        Set.range (pinnedX .E6 F4 (-Pi.single i 1))) ∧
    (pinnedX .E6 F4 (Pi.single i 1) 1 * pinnedX .E6 F4 (-Pi.single i 1) 1) ∈
        Subgroup.closure (Set.range (pinnedX .E6 F4 (Pi.single i 1)) ∪
          Set.range (pinnedX .E6 F4 (-Pi.single i 1))) := by
  have hx : ∀ c : F4, pinnedX .E6 F4 (Pi.single i 1) c ∈
      Subgroup.closure (Set.range (pinnedX .E6 F4 (Pi.single i 1)) ∪
        Set.range (pinnedX .E6 F4 (-Pi.single i 1))) :=
    fun c => Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
  have hy : ∀ c : F4, pinnedX .E6 F4 (-Pi.single i 1) c ∈
      Subgroup.closure (Set.range (pinnedX .E6 F4 (Pi.single i 1)) ∪
        Set.range (pinnedX .E6 F4 (-Pi.single i 1))) :=
    fun c => Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
  refine ⟨?_, ?_⟩
  · rw [e6a3_P0, e6a3_alpha]
    exact mul_mem (hy _) (hx _)
  · exact mul_mem (hx _) (hy _)

private theorem e6a3_P_conj_w :
    e6a3_P⁻¹ * e6a3_wF * e6a3_P = e6a3_d := by
  have h0 := e6a3xa_P0_conj_z e6a3_i0
  have h1 := e6a3xa_P0_conj_z e6a3_i3
  have h2 := e6a3xa_P0_conj_z e6a3_i5
  have hm0 := e6a3xa_mem_closure e6a3_i0
  have hm1 := e6a3xa_mem_closure e6a3_i3
  have hm2 := e6a3xa_mem_closure e6a3_i5
  have c01 := e6a3xa_closure_commute (i := e6a3_i0) (j := e6a3_i3) (by decide) (by decide)
  have c02 := e6a3xa_closure_commute (i := e6a3_i0) (j := e6a3_i5) (by decide) (by decide)
  have c12 := e6a3xa_closure_commute (i := e6a3_i3) (j := e6a3_i5) (by decide) (by decide)
  have ha01 : Commute (e6a3_P0 e6a3_i0) (e6a3_P0 e6a3_i3) := c01 _ hm0.1 _ hm1.1
  have ha02 : Commute (e6a3_P0 e6a3_i0) (e6a3_P0 e6a3_i5) := c02 _ hm0.1 _ hm2.1
  have ha12 : Commute (e6a3_P0 e6a3_i3) (e6a3_P0 e6a3_i5) := c12 _ hm1.1 _ hm2.1
  have ha0z1 : Commute (e6a3_P0 e6a3_i0)
      (pinnedX .E6 F4 (e6a3_alpha e6a3_i3) 1 * pinnedX .E6 F4 (-(e6a3_alpha e6a3_i3)) 1) :=
    c01 _ hm0.1 _ hm1.2
  have ha0z2 : Commute (e6a3_P0 e6a3_i0)
      (pinnedX .E6 F4 (e6a3_alpha e6a3_i5) 1 * pinnedX .E6 F4 (-(e6a3_alpha e6a3_i5)) 1) :=
    c02 _ hm0.1 _ hm2.2
  have ha1z0 : Commute (e6a3_P0 e6a3_i3)
      (pinnedX .E6 F4 (e6a3_alpha e6a3_i0) 1 * pinnedX .E6 F4 (-(e6a3_alpha e6a3_i0)) 1) :=
    (c01 _ hm0.2 _ hm1.1).symm
  have ha1z2 : Commute (e6a3_P0 e6a3_i3)
      (pinnedX .E6 F4 (e6a3_alpha e6a3_i5) 1 * pinnedX .E6 F4 (-(e6a3_alpha e6a3_i5)) 1) :=
    c12 _ hm1.1 _ hm2.2
  have ha2z0 : Commute (e6a3_P0 e6a3_i5)
      (pinnedX .E6 F4 (e6a3_alpha e6a3_i0) 1 * pinnedX .E6 F4 (-(e6a3_alpha e6a3_i0)) 1) :=
    (c02 _ hm0.2 _ hm2.1).symm
  have ha2z1 : Commute (e6a3_P0 e6a3_i5)
      (pinnedX .E6 F4 (e6a3_alpha e6a3_i3) 1 * pinnedX .E6 F4 (-(e6a3_alpha e6a3_i3)) 1) :=
    (c12 _ hm1.2 _ hm2.1).symm
  have hmain := e6a3xa_conj_prod (e6a3_P0 e6a3_i0) (e6a3_P0 e6a3_i3) (e6a3_P0 e6a3_i5)
    (pinnedX .E6 F4 (e6a3_alpha e6a3_i0) 1 * pinnedX .E6 F4 (-(e6a3_alpha e6a3_i0)) 1)
    (pinnedX .E6 F4 (e6a3_alpha e6a3_i3) 1 * pinnedX .E6 F4 (-(e6a3_alpha e6a3_i3)) 1)
    (pinnedX .E6 F4 (e6a3_alpha e6a3_i5) 1 * pinnedX .E6 F4 (-(e6a3_alpha e6a3_i5)) 1)
    (torusElt .E6 F4 e6a3_i0 e6a3_omega) (torusElt .E6 F4 e6a3_i3 e6a3_omega)
    (torusElt .E6 F4 e6a3_i5 e6a3_omega)
    h0 h1 h2 ha01 ha02 ha12 ha0z1 ha0z2 ha1z0 ha1z2 ha2z0 ha2z1
  rw [e6a3_P, e6a3xa_wF_eq, e6a3_d]
  simpa only [mul_assoc] using hmain

private theorem e6a3_P_frob_conj :
    e6a3_P⁻¹ * e6a3_F e6a3_P = e6a3_nu := by
  have hb0 : e6a3_F (e6a3_P0 e6a3_i0) = e6a3_P0 e6a3_i0 * weylElt .E6 F4 e6a3_i0 1 := by
    rw [← e6a3_P0_frob_factor e6a3_i0]
    group
  have hb1 : e6a3_F (e6a3_P0 e6a3_i3) = e6a3_P0 e6a3_i3 * weylElt .E6 F4 e6a3_i3 1 := by
    rw [← e6a3_P0_frob_factor e6a3_i3]
    group
  have hb2 : e6a3_F (e6a3_P0 e6a3_i5) = e6a3_P0 e6a3_i5 * weylElt .E6 F4 e6a3_i5 1 := by
    rw [← e6a3_P0_frob_factor e6a3_i5]
    group
  have h03 : Commute (weylElt .E6 F4 e6a3_i0 1) (e6a3_P0 e6a3_i3) :=
    e6a3xa_commute_weylElt_P0 (i := e6a3_i0) (j := e6a3_i3) (by decide) (by decide)
  have h05 : Commute (weylElt .E6 F4 e6a3_i0 1) (e6a3_P0 e6a3_i5) :=
    e6a3xa_commute_weylElt_P0 (i := e6a3_i0) (j := e6a3_i5) (by decide) (by decide)
  have h35 : Commute (weylElt .E6 F4 e6a3_i3 1) (e6a3_P0 e6a3_i5) :=
    e6a3xa_commute_weylElt_P0 (i := e6a3_i3) (j := e6a3_i5) (by decide) (by decide)
  rw [e6a3_P, e6a3_nu, map_mul, map_mul, hb0, hb1, hb2]
  exact e6a3xa_prod_inv_mul _ _ _ _ _ _ h03 h05 h35

private noncomputable def e6a3xb_fam

    : Fin 1 → Fin (Tag.rank .E6) → F4ˣ := fun _ => e6a3_dChar

private noncomputable def e6a3xb_u

    : WeylGroup .E6 :=
  simple .E6 e6a3_i0 * simple .E6 e6a3_i3 * simple .E6 e6a3_i5

private theorem e6a3xb_familyKernel_eq_rootCharKernel
    :
    CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel e6a3xb_fam =
      rootCharKernel e6a3_dChar := by
  ext α
  simp only [CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel, rootCharKernel,
    e6a3xb_fam, Fin.forall_fin_one]

private def e6a3xc1_c (l : Fin (Tag.rank .E6)) : ℤ :=
  Tag.cartan .E6 e6a3_i0 l + Tag.cartan .E6 e6a3_i3 l + Tag.cartan .E6 e6a3_i5 l

private theorem e6a3xc1_rootChar_eq (v : Fin (Tag.rank .E6) → ℤ) :
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar e6a3_dChar v =
      e6a3_omega ^ (∑ j, v j * e6a3xc1_c j) := by
  simp only [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar, e6a3_dChar,
    e6a3xc1_c, e6a3_i0, e6a3_i3, e6a3_i5, ← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem e6a3xc1_omega_order : orderOf e6a3_omega = 3 := by
  apply orderOf_eq_prime
  · ext
    simp [e6a3_omega, f4Omega_pow_three]
  · intro h
    apply f4Omega_ne_one
    exact congrArg (fun u : F4ˣ => (u : F4)) h

private theorem e6a3xc1_dvd_iff (v : Fin (Tag.rank .E6) → ℤ) :
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar e6a3_dChar v = 1 ↔
      (3 : ℤ) ∣ ∑ j, v j * e6a3xc1_c j := by
  rw [e6a3xc1_rootChar_eq, ← orderOf_dvd_iff_zpow_eq_one, e6a3xc1_omega_order]
  norm_num

private def e6a3xc1_AF : Finset (Fin (Tag.rank .E6) → ℤ) :=
  e6a3_Apos.toFinset ∪ e6a3_Apos.toFinset.image Neg.neg

private def e6a3xc1_BF : Finset (Fin (Tag.rank .E6) → ℤ) :=
  e6a3_Bpos.toFinset ∪ e6a3_Bpos.toFinset.image Neg.neg

private def e6a3xc1_CF : Finset (Fin (Tag.rank .E6) → ℤ) :=
  e6a3_Cpos.toFinset ∪ e6a3_Cpos.toFinset.image Neg.neg

private def e6a3xc1_PhiDfin : Finset (Fin (Tag.rank .E6) → ℤ) :=
  e6a3xc1_AF ∪ e6a3xc1_BF ∪ e6a3xc1_CF

private theorem e6a3xc1_mem_component_iff (l : List (Fin (Tag.rank .E6) → ℤ))
    (v : Fin (Tag.rank .E6) → ℤ) :
    v ∈ e6a3_component l ↔ v ∈ l.toFinset ∪ (l.toFinset.image Neg.neg) := by
  simp only [e6a3_component, Set.mem_setOf_eq, Finset.mem_union, List.mem_toFinset,
    Finset.mem_image]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ⟨-v, h, ?_⟩
      simp
  · rintro (h | ⟨a, ha, hav⟩)
    · exact Or.inl h
    · right
      rw [← hav]
      simpa using ha

private theorem e6a3xc1_fin_to_PhiD {v : Fin (Tag.rank .E6) → ℤ} :
    v ∈ e6a3xc1_PhiDfin → v ∈ e6a3_PhiD := by
  simp only [e6a3xc1_PhiDfin, e6a3xc1_AF, e6a3xc1_BF, e6a3xc1_CF, e6a3_PhiD, Set.mem_union,
    e6a3_A, e6a3_B, e6a3_C, e6a3xc1_mem_component_iff, Finset.mem_union]
  tauto

private theorem e6a3xc1_subset_fin {v : Fin (Tag.rank .E6) → ℤ} :
    v ∈ e6a3_PhiD → v ∈ e6a3xc1_PhiDfin := by
  simp only [e6a3xc1_PhiDfin, e6a3xc1_AF, e6a3xc1_BF, e6a3xc1_CF, e6a3_PhiD, Set.mem_union,
    e6a3_A, e6a3_B, e6a3_C, e6a3xc1_mem_component_iff, Finset.mem_union]
  tauto

private theorem e6a3xc1_root_check : ∀ v ∈ rootFinset .E6,
    (3 : ℤ) ∣ (∑ j, v j * e6a3xc1_c j) → v ∈ e6a3xc1_PhiDfin := by
  decide +kernel

private theorem e6a3xc1_PhiDfin_check : ∀ v ∈ e6a3xc1_PhiDfin,
    v ∈ rootFinset .E6 ∧ (3 : ℤ) ∣ (∑ j, v j * e6a3xc1_c j) := by
  decide +kernel

private theorem e6a3xb_rootCharKernel_eq :
    rootCharKernel e6a3_dChar = e6a3_PhiD := by
  ext α
  rw [rootCharKernel, Set.mem_setOf_eq, e6a3xc1_dvd_iff]
  constructor
  · rintro ⟨hroot, hdvd⟩
    exact e6a3xc1_fin_to_PhiD (e6a3xc1_root_check α (mem_rootFinset.mpr hroot) hdvd)
  · intro h
    have hfin := e6a3xc1_subset_fin h
    have h2 := e6a3xc1_PhiDfin_check α hfin
    exact ⟨mem_rootFinset.mp h2.1, h2.2⟩

private theorem e6a3xb_familyKernel_eq :
    CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel e6a3xb_fam = e6a3_PhiD := by
  rw [e6a3xb_familyKernel_eq_rootCharKernel, e6a3xb_rootCharKernel_eq]

private theorem e6a3xc1_mem_PhiD_components {v : Fin (Tag.rank .E6) → ℤ} (h : v ∈ e6a3_PhiD) :
    v ∈ e6a3_A ∨ v ∈ e6a3_B ∨ v ∈ e6a3_C := by
  have h' : (v ∈ e6a3_A ∨ v ∈ e6a3_B) ∨ v ∈ e6a3_C := by
    simpa only [e6a3_PhiD, Set.mem_union] using h
  rcases h' with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

private theorem e6a3xc1_orth6 :
    (∀ v ∈ e6a3xc1_AF, ∀ w ∈ e6a3xc1_BF,
        dotProduct v (Matrix.mulVec (Tag.symmetrizedCartan .E6) w) = 0) ∧
    (∀ v ∈ e6a3xc1_BF, ∀ w ∈ e6a3xc1_AF,
        dotProduct v (Matrix.mulVec (Tag.symmetrizedCartan .E6) w) = 0) ∧
    (∀ v ∈ e6a3xc1_AF, ∀ w ∈ e6a3xc1_CF,
        dotProduct v (Matrix.mulVec (Tag.symmetrizedCartan .E6) w) = 0) ∧
    (∀ v ∈ e6a3xc1_CF, ∀ w ∈ e6a3xc1_AF,
        dotProduct v (Matrix.mulVec (Tag.symmetrizedCartan .E6) w) = 0) ∧
    (∀ v ∈ e6a3xc1_BF, ∀ w ∈ e6a3xc1_CF,
        dotProduct v (Matrix.mulVec (Tag.symmetrizedCartan .E6) w) = 0) ∧
    (∀ v ∈ e6a3xc1_CF, ∀ w ∈ e6a3xc1_BF,
        dotProduct v (Matrix.mulVec (Tag.symmetrizedCartan .E6) w) = 0) := by
  decide +kernel

private theorem e6a3xc1_commute_of_orthogonal
    {v w : Fin (Tag.rank .E6) → ℤ} (hv : IsRoot .E6 v) (hw : IsRoot .E6 w)
    (h0 : dotProduct v (Matrix.mulVec (Tag.symmetrizedCartan .E6) w) = 0)
    {x y : ModGL .E6 F4} (hx : x ∈ rootSubgroup .E6 F4 v) (hy : y ∈ rootSubgroup .E6 F4 w) :
    Commute x y :=
  (simply_laced_orthogonal_root_commutation .E6 (Or.inr (Or.inl rfl))).2 F4 v w hv hw h0 x hx y hy

private theorem e6a3xb_familyGroup_le_normalizer_union
    {S : Set (Fin (Tag.rank .E6) → ℤ)}
    (hS : S = e6a3_A ∪ e6a3_C ∨ S = e6a3_A ∪ e6a3_B ∨ S = e6a3_B ∪ e6a3_C) :
    CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup (K := F4) e6a3xb_fam ≤
      Subgroup.normalizer (rootSpan .E6 F4 S : Set (ModGL .E6 F4)) := by
  refine CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup_le_normalizer_rootSpan_of_subset
    (a := e6a3xb_fam) ?_ ?_
  · intro v hv
    rw [e6a3xb_familyKernel_eq]
    rcases hS with rfl | rfl | rfl
    · rcases hv with hv | hv
      · exact Or.inl (Or.inl hv)
      · exact Or.inr hv
    · rcases hv with hv | hv
      · exact Or.inl (Or.inl hv)
      · exact Or.inl (Or.inr hv)
    · rcases hv with hv | hv
      · exact Or.inl (Or.inr hv)
      · exact Or.inr hv
  · intro α hα β hβ x hx y hy
    obtain ⟨hAB, hBA, hAC, hCA, hBC, hCB⟩ := e6a3xc1_orth6
    have hker : α ∈ e6a3_PhiD := by
      rw [← e6a3xb_familyKernel_eq]; exact hα.1
    have hβ_Phi : β ∈ e6a3_PhiD := by
      rcases hS with rfl | rfl | rfl
      · rcases hβ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases hβ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
      · rcases hβ with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    have hα_comp := e6a3xc1_mem_PhiD_components hker
    have hrootα : IsRoot .E6 α :=
      mem_rootFinset.mp (e6a3xc1_PhiDfin_check α (e6a3xc1_subset_fin hker)).1
    have hrootβ : IsRoot .E6 β :=
      mem_rootFinset.mp (e6a3xc1_PhiDfin_check β (e6a3xc1_subset_fin hβ_Phi)).1
    rcases hS with hS | hS | hS
    · rw [hS] at hα hβ
      have hαB : α ∈ e6a3_B := by
        rcases hα_comp with h | h | h
        · exact absurd h (fun hh => hα.2 (Or.inl hh))
        · exact h
        · exact absurd h (fun hh => hα.2 (Or.inr hh))
      have hαBF : α ∈ e6a3xc1_BF := (e6a3xc1_mem_component_iff e6a3_Bpos α).mp hαB
      have hβAC : β ∈ e6a3_A ∨ β ∈ e6a3_C := by simpa only [Set.mem_union] using hβ
      rcases hβAC with hβA | hβC
      · exact e6a3xc1_commute_of_orthogonal hrootα hrootβ
          (hBA α hαBF β ((e6a3xc1_mem_component_iff e6a3_Apos β).mp hβA)) hx hy
      · exact e6a3xc1_commute_of_orthogonal hrootα hrootβ
          (hBC α hαBF β ((e6a3xc1_mem_component_iff e6a3_Cpos β).mp hβC)) hx hy
    · rw [hS] at hα hβ
      have hαC : α ∈ e6a3_C := by
        rcases hα_comp with h | h | h
        · exact absurd h (fun hh => hα.2 (Or.inl hh))
        · exact absurd h (fun hh => hα.2 (Or.inr hh))
        · exact h
      have hαCF : α ∈ e6a3xc1_CF := (e6a3xc1_mem_component_iff e6a3_Cpos α).mp hαC
      have hβAB : β ∈ e6a3_A ∨ β ∈ e6a3_B := by simpa only [Set.mem_union] using hβ
      rcases hβAB with hβA | hβB
      · exact e6a3xc1_commute_of_orthogonal hrootα hrootβ
          (hCA α hαCF β ((e6a3xc1_mem_component_iff e6a3_Apos β).mp hβA)) hx hy
      · exact e6a3xc1_commute_of_orthogonal hrootα hrootβ
          (hCB α hαCF β ((e6a3xc1_mem_component_iff e6a3_Bpos β).mp hβB)) hx hy
    · rw [hS] at hα hβ
      have hαA : α ∈ e6a3_A := by
        rcases hα_comp with h | h | h
        · exact h
        · exact absurd h (fun hh => hα.2 (Or.inl hh))
        · exact absurd h (fun hh => hα.2 (Or.inr hh))
      have hαAF : α ∈ e6a3xc1_AF := (e6a3xc1_mem_component_iff e6a3_Apos α).mp hαA
      have hβBC : β ∈ e6a3_B ∨ β ∈ e6a3_C := by simpa only [Set.mem_union] using hβ
      rcases hβBC with hβB | hβC
      · exact e6a3xc1_commute_of_orthogonal hrootα hrootβ
          (hAB α hαAF β ((e6a3xc1_mem_component_iff e6a3_Bpos β).mp hβB)) hx hy
      · exact e6a3xc1_commute_of_orthogonal hrootα hrootβ
          (hAC α hαAF β ((e6a3xc1_mem_component_iff e6a3_Cpos β).mp hβC)) hx hy

private theorem e6a3xc2_image_PhiD
    (w : WeylGroup .E6)
    (hw : w ∈ CFSG.HardMathSupport.Timmesfeld.Torality.familyStabilizer e6a3xb_fam) :
    (fun α => w • α) '' e6a3_PhiD = e6a3_PhiD := by
  rw [← e6a3xb_familyKernel_eq]
  exact CFSG.HardMathSupport.Timmesfeld.Torality.image_familyKernel hw

private abbrev e6a3xc2_root (k : Fin 72) : Fin (Tag.rank .E6) → ℤ :=
  CFSG.LieType.Chevalley.C2E6Std.e6Root k

private theorem e6a3xc2_image_lt (k : Fin 72)
    (i : Fin (Tag.rank .E6)) : e6Certificate.image k i < 72 := by
  have h := e6Certificate_check
  simp only [CFSG.Blueprint.Chevalley.RootCertificate.check, Bool.and_eq_true] at h
  obtain ⟨⟨-, -⟩, ht⟩ := h
  simp only [CFSG.Blueprint.Chevalley.RootCertificate.checkTable, List.all_eq_true,
    List.mem_range, List.mem_finRange, true_implies, Bool.and_eq_true, decide_eq_true_eq] at ht
  have hk : (k : ℕ) < e6Certificate.roots.length := by
    rw [CFSG.LieType.Chevalley.C2E6Std.length_e6Certificate]; exact k.2
  exact (ht (k : ℕ) hk i).1

private theorem e6a3xc2_root_image (k : Fin 72)
    (i : Fin (Tag.rank .E6)) :
    e6a3xc2_root ⟨e6Certificate.image k i, e6a3xc2_image_lt k i⟩ =
      CFSG.Blueprint.Chevalley.reflect .E6 i (e6a3xc2_root k) := by
  have h := e6Certificate_check
  simp only [CFSG.Blueprint.Chevalley.RootCertificate.check, Bool.and_eq_true] at h
  obtain ⟨⟨-, -⟩, ht⟩ := h
  simp only [CFSG.Blueprint.Chevalley.RootCertificate.checkTable, List.all_eq_true,
    List.mem_range, List.mem_finRange, true_implies, Bool.and_eq_true, decide_eq_true_eq] at ht
  have hk : (k : ℕ) < e6Certificate.roots.length := by
    rw [CFSG.LieType.Chevalley.C2E6Std.length_e6Certificate]; exact k.2
  exact CFSG.Blueprint.Chevalley.RootCertificate.eq_of_ofFn_beq (ht (k : ℕ) hk i).2

private def e6a3xc2_sIdx (k : Fin 72) (i : Fin (Tag.rank .E6)) :
    Fin 72 :=
  ⟨e6Certificate.image k i, e6a3xc2_image_lt k i⟩

private theorem e6a3xc2_simple_e6Root (k : Fin 72)
    (i : Fin (Tag.rank .E6)) :
    simple .E6 i • e6a3xc2_root k = e6a3xc2_root (e6a3xc2_sIdx k i) := by
  rw [simple_smul]
  exact (e6a3xc2_root_image k i).symm

private def e6a3xc2_uIdx (k : Fin 72) : Fin 72 :=
  e6a3xc2_sIdx (e6a3xc2_sIdx (e6a3xc2_sIdx k 5) 3) 0

private theorem e6a3xc2_u_e6Root
    (k : Fin 72) :
    e6a3xb_u • e6a3xc2_root k = e6a3xc2_root (e6a3xc2_uIdx k) := by
  rw [e6a3xb_u, mul_smul, mul_smul, e6a3xc2_simple_e6Root, e6a3xc2_simple_e6Root,
    e6a3xc2_simple_e6Root]
  rfl

private def e6a3xc2_vA0 : Fin (Tag.rank .E6) → ℤ := ![0, 0, 1, 1, 0, 0]
private def e6a3xc2_vA1 : Fin (Tag.rank .E6) → ℤ := ![0, 0, 0, 0, 1, 1]
private def e6a3xc2_vA2 : Fin (Tag.rank .E6) → ℤ := ![0, 0, 1, 1, 1, 1]
private def e6a3xc2_vB0 : Fin (Tag.rank .E6) → ℤ := ![0, 1, 1, 1, 1, 0]
private def e6a3xc2_vB1 : Fin (Tag.rank .E6) → ℤ := ![1, 1, 1, 2, 1, 1]
private def e6a3xc2_vB2 : Fin (Tag.rank .E6) → ℤ := highRoot .E6
private def e6a3xc2_vC0 : Fin (Tag.rank .E6) → ℤ := ![1, 0, 1, 0, 0, 0]
private def e6a3xc2_vC1 : Fin (Tag.rank .E6) → ℤ := ![0, 0, 0, 1, 1, 0]
private def e6a3xc2_vC2 : Fin (Tag.rank .E6) → ℤ := ![1, 0, 1, 1, 1, 0]

private theorem e6a3xc2_root_vA0 : e6a3xc2_root ⟨11, by decide⟩ = e6a3xc2_vA0 := by
  decide +kernel
private theorem e6a3xc2_root_vA1 : e6a3xc2_root ⟨15, by decide⟩ = e6a3xc2_vA1 := by
  decide +kernel
private theorem e6a3xc2_root_vA2 : e6a3xc2_root ⟨35, by decide⟩ = e6a3xc2_vA2 := by
  decide +kernel
private theorem e6a3xc2_root_nA0 : e6a3xc2_root ⟨22, by decide⟩ = -e6a3xc2_vA0 := by
  decide +kernel
private theorem e6a3xc2_root_nA1 : e6a3xc2_root ⟨26, by decide⟩ = -e6a3xc2_vA1 := by
  decide +kernel
private theorem e6a3xc2_root_nA2 : e6a3xc2_root ⟨45, by decide⟩ = -e6a3xc2_vA2 := by
  decide +kernel
private theorem e6a3xc2_root_vB0 : e6a3xc2_root ⟨32, by decide⟩ = e6a3xc2_vB0 := by
  decide +kernel
private theorem e6a3xc2_root_vB1 : e6a3xc2_root ⟨56, by decide⟩ = e6a3xc2_vB1 := by
  decide +kernel
private theorem e6a3xc2_root_vB2 : e6a3xc2_root ⟨70, by decide⟩ = e6a3xc2_vB2 := by
  decide +kernel
private theorem e6a3xc2_root_vC0 : e6a3xc2_root ⟨7, by decide⟩ = e6a3xc2_vC0 := by
  decide +kernel
private theorem e6a3xc2_root_vC1 : e6a3xc2_root ⟨13, by decide⟩ = e6a3xc2_vC1 := by
  decide +kernel
private theorem e6a3xc2_root_vC2 : e6a3xc2_root ⟨29, by decide⟩ = e6a3xc2_vC2 := by
  decide +kernel
private theorem e6a3xc2_root_nC0 : e6a3xc2_root ⟨17, by decide⟩ = -e6a3xc2_vC0 := by
  decide +kernel
private theorem e6a3xc2_root_nC1 : e6a3xc2_root ⟨24, by decide⟩ = -e6a3xc2_vC1 := by
  decide +kernel
private theorem e6a3xc2_root_nC2 : e6a3xc2_root ⟨38, by decide⟩ = -e6a3xc2_vC2 := by
  decide +kernel

private def e6a3xc2_imageNat (k : ℕ) (i : ℕ) : ℕ :=
  e6Certificate.table.getD k 0 / 256 ^ i % 256

private def e6a3xc2_uIdxNat (k : ℕ) : ℕ :=
  e6a3xc2_imageNat (e6a3xc2_imageNat (e6a3xc2_imageNat k 5) 3) 0

private theorem e6a3xc2_uIdx_val (k : Fin 72) :
    (e6a3xc2_uIdx k).val = e6a3xc2_uIdxNat k := rfl

private theorem e6a3xc2_u_vA0
    : e6a3xb_u • e6a3xc2_vA0 = e6a3xc2_vC0 := by
  rw [← e6a3xc2_root_vA0, e6a3xc2_u_e6Root, ← e6a3xc2_root_vC0]
  apply congrArg e6a3xc2_root
  apply Fin.ext
  rw [e6a3xc2_uIdx_val]
  decide +kernel
private theorem e6a3xc2_u_vA1
    : e6a3xb_u • e6a3xc2_vA1 = e6a3xc2_vC1 := by
  rw [← e6a3xc2_root_vA1, e6a3xc2_u_e6Root, ← e6a3xc2_root_vC1]
  apply congrArg e6a3xc2_root
  apply Fin.ext
  rw [e6a3xc2_uIdx_val]
  decide +kernel
private theorem e6a3xc2_u_vA2
    : e6a3xb_u • e6a3xc2_vA2 = e6a3xc2_vC2 := by
  rw [← e6a3xc2_root_vA2, e6a3xc2_u_e6Root, ← e6a3xc2_root_vC2]
  apply congrArg e6a3xc2_root
  apply Fin.ext
  rw [e6a3xc2_uIdx_val]
  decide +kernel
private theorem e6a3xc2_u_vB0
    : e6a3xb_u • e6a3xc2_vB0 = e6a3xc2_vB1 := by
  rw [← e6a3xc2_root_vB0, e6a3xc2_u_e6Root, ← e6a3xc2_root_vB1]
  apply congrArg e6a3xc2_root
  apply Fin.ext
  rw [e6a3xc2_uIdx_val]
  decide +kernel
private theorem e6a3xc2_u_vB1
    : e6a3xb_u • e6a3xc2_vB1 = e6a3xc2_vB0 := by
  rw [← e6a3xc2_root_vB1, e6a3xc2_u_e6Root, ← e6a3xc2_root_vB0]
  apply congrArg e6a3xc2_root
  apply Fin.ext
  rw [e6a3xc2_uIdx_val]
  decide +kernel
private theorem e6a3xc2_u_vB2
    : e6a3xb_u • e6a3xc2_vB2 = e6a3xc2_vB2 := by
  rw [← e6a3xc2_root_vB2, e6a3xc2_u_e6Root]
  apply congrArg e6a3xc2_root
  apply Fin.ext
  rw [e6a3xc2_uIdx_val]
  decide +kernel
private theorem e6a3xc2_u_vC0
    : e6a3xb_u • e6a3xc2_vC0 = e6a3xc2_vA0 := by
  rw [← e6a3xc2_root_vC0, e6a3xc2_u_e6Root, ← e6a3xc2_root_vA0]
  apply congrArg e6a3xc2_root
  apply Fin.ext
  rw [e6a3xc2_uIdx_val]
  decide +kernel
private theorem e6a3xc2_u_vC1
    : e6a3xb_u • e6a3xc2_vC1 = e6a3xc2_vA1 := by
  rw [← e6a3xc2_root_vC1, e6a3xc2_u_e6Root, ← e6a3xc2_root_vA1]
  apply congrArg e6a3xc2_root
  apply Fin.ext
  rw [e6a3xc2_uIdx_val]
  decide +kernel
private theorem e6a3xc2_u_vC2
    : e6a3xb_u • e6a3xc2_vC2 = e6a3xc2_vA2 := by
  rw [← e6a3xc2_root_vC2, e6a3xc2_u_e6Root, ← e6a3xc2_root_vA2]
  apply congrArg e6a3xc2_root
  apply Fin.ext
  rw [e6a3xc2_uIdx_val]
  decide +kernel

private theorem e6a3xc2_mem_A {γ : Fin (Tag.rank .E6) → ℤ} :
    γ ∈ e6a3_A ↔ γ = e6a3xc2_vA0 ∨ γ = e6a3xc2_vA1 ∨ γ = e6a3xc2_vA2 ∨
      -γ = e6a3xc2_vA0 ∨ -γ = e6a3xc2_vA1 ∨ -γ = e6a3xc2_vA2 := by
  have hA : e6a3_Apos = [e6a3xc2_vA0, e6a3xc2_vA1, e6a3xc2_vA2] := rfl
  simp only [e6a3_A, e6a3_component, hA, Set.mem_setOf_eq, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc]

private theorem e6a3xc2_mem_B {γ : Fin (Tag.rank .E6) → ℤ} :
    γ ∈ e6a3_B ↔ γ = e6a3xc2_vB0 ∨ γ = e6a3xc2_vB1 ∨ γ = e6a3xc2_vB2 ∨
      -γ = e6a3xc2_vB0 ∨ -γ = e6a3xc2_vB1 ∨ -γ = e6a3xc2_vB2 := by
  have hB : e6a3_Bpos = [e6a3xc2_vB0, e6a3xc2_vB1, e6a3xc2_vB2] := rfl
  simp only [e6a3_B, e6a3_component, hB, Set.mem_setOf_eq, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc]

private theorem e6a3xc2_mem_C {γ : Fin (Tag.rank .E6) → ℤ} :
    γ ∈ e6a3_C ↔ γ = e6a3xc2_vC0 ∨ γ = e6a3xc2_vC1 ∨ γ = e6a3xc2_vC2 ∨
      -γ = e6a3xc2_vC0 ∨ -γ = e6a3xc2_vC1 ∨ -γ = e6a3xc2_vC2 := by
  have hC : e6a3_Cpos = [e6a3xc2_vC0, e6a3xc2_vC1, e6a3xc2_vC2] := rfl
  simp only [e6a3_C, e6a3_component, hC, Set.mem_setOf_eq, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc]

private def e6a3xc2_Avecs : List (Fin (Tag.rank .E6) → ℤ) :=
  [e6a3xc2_vA0, e6a3xc2_vA1, e6a3xc2_vA2, -e6a3xc2_vA0, -e6a3xc2_vA1, -e6a3xc2_vA2]
private def e6a3xc2_Bvecs : List (Fin (Tag.rank .E6) → ℤ) :=
  [e6a3xc2_vB0, e6a3xc2_vB1, e6a3xc2_vB2, -e6a3xc2_vB0, -e6a3xc2_vB1, -e6a3xc2_vB2]
private def e6a3xc2_Cvecs : List (Fin (Tag.rank .E6) → ℤ) :=
  [e6a3xc2_vC0, e6a3xc2_vC1, e6a3xc2_vC2, -e6a3xc2_vC0, -e6a3xc2_vC1, -e6a3xc2_vC2]
private def e6a3xc2_PhiDvecs : List (Fin (Tag.rank .E6) → ℤ) :=
  e6a3xc2_Avecs ++ e6a3xc2_Bvecs ++ e6a3xc2_Cvecs

private theorem e6a3xc2_Avecs_mem {x : Fin (Tag.rank .E6) → ℤ} :
    x ∈ e6a3xc2_Avecs ↔ x ∈ e6a3_A := by
  have hA : e6a3_Apos = [e6a3xc2_vA0, e6a3xc2_vA1, e6a3xc2_vA2] := rfl
  simp only [e6a3xc2_Avecs, e6a3_A, e6a3_component, hA, Set.mem_setOf_eq, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc, neg_eq_iff_eq_neg]
private theorem e6a3xc2_Bvecs_mem {x : Fin (Tag.rank .E6) → ℤ} :
    x ∈ e6a3xc2_Bvecs ↔ x ∈ e6a3_B := by
  have hB : e6a3_Bpos = [e6a3xc2_vB0, e6a3xc2_vB1, e6a3xc2_vB2] := rfl
  simp only [e6a3xc2_Bvecs, e6a3_B, e6a3_component, hB, Set.mem_setOf_eq, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc, neg_eq_iff_eq_neg]
private theorem e6a3xc2_Cvecs_mem {x : Fin (Tag.rank .E6) → ℤ} :
    x ∈ e6a3xc2_Cvecs ↔ x ∈ e6a3_C := by
  have hC : e6a3_Cpos = [e6a3xc2_vC0, e6a3xc2_vC1, e6a3xc2_vC2] := rfl
  simp only [e6a3xc2_Cvecs, e6a3_C, e6a3_component, hC, Set.mem_setOf_eq, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc, neg_eq_iff_eq_neg]

private theorem e6a3xc2_PhiDvecs_mem {x : Fin (Tag.rank .E6) → ℤ} :
    x ∈ e6a3xc2_PhiDvecs ↔ x ∈ e6a3_PhiD := by
  simp only [e6a3xc2_PhiDvecs, e6a3_PhiD, e6a3xc2_Avecs_mem, e6a3xc2_Bvecs_mem,
    e6a3xc2_Cvecs_mem, List.mem_append, Set.mem_union, or_assoc]

private theorem e6a3xc2_test_nonorth_A :
    (e6a3xc2_Avecs.all (fun x => e6a3xc2_PhiDvecs.all (fun γ =>
      decide (iform x γ ≠ 0 ↔ γ ∈ e6a3xc2_Avecs)))) = true := by
  decide +kernel
private theorem e6a3xc2_test_nonorth_B :
    (e6a3xc2_Bvecs.all (fun x => e6a3xc2_PhiDvecs.all (fun γ =>
      decide (iform x γ ≠ 0 ↔ γ ∈ e6a3xc2_Bvecs)))) = true := by
  decide +kernel
private theorem e6a3xc2_test_nonorth_C :
    (e6a3xc2_Cvecs.all (fun x => e6a3xc2_PhiDvecs.all (fun γ =>
      decide (iform x γ ≠ 0 ↔ γ ∈ e6a3xc2_Cvecs)))) = true := by
  decide +kernel

private theorem e6a3xc2_nonorth_A {x : Fin (Tag.rank .E6) → ℤ} (hx : x ∈ e6a3_A) :
    ∀ γ ∈ e6a3_PhiD, (iform x γ ≠ 0 ↔ γ ∈ e6a3_A) := by
  intro γ hγ
  have hxL : x ∈ e6a3xc2_Avecs := (e6a3xc2_Avecs_mem).2 hx
  have hγL : γ ∈ e6a3xc2_PhiDvecs := (e6a3xc2_PhiDvecs_mem).2 hγ
  have h1 := List.all_eq_true.1 e6a3xc2_test_nonorth_A x hxL
  have h2 := List.all_eq_true.1 h1 γ hγL
  rw [decide_eq_true_eq] at h2
  rwa [e6a3xc2_Avecs_mem] at h2

private theorem e6a3xc2_nonorth_B {x : Fin (Tag.rank .E6) → ℤ} (hx : x ∈ e6a3_B) :
    ∀ γ ∈ e6a3_PhiD, (iform x γ ≠ 0 ↔ γ ∈ e6a3_B) := by
  intro γ hγ
  have hxL : x ∈ e6a3xc2_Bvecs := (e6a3xc2_Bvecs_mem).2 hx
  have hγL : γ ∈ e6a3xc2_PhiDvecs := (e6a3xc2_PhiDvecs_mem).2 hγ
  have h1 := List.all_eq_true.1 e6a3xc2_test_nonorth_B x hxL
  have h2 := List.all_eq_true.1 h1 γ hγL
  rw [decide_eq_true_eq] at h2
  rwa [e6a3xc2_Bvecs_mem] at h2

private theorem e6a3xc2_nonorth_C {x : Fin (Tag.rank .E6) → ℤ} (hx : x ∈ e6a3_C) :
    ∀ γ ∈ e6a3_PhiD, (iform x γ ≠ 0 ↔ γ ∈ e6a3_C) := by
  intro γ hγ
  have hxL : x ∈ e6a3xc2_Cvecs := (e6a3xc2_Cvecs_mem).2 hx
  have hγL : γ ∈ e6a3xc2_PhiDvecs := (e6a3xc2_PhiDvecs_mem).2 hγ
  have h1 := List.all_eq_true.1 e6a3xc2_test_nonorth_C x hxL
  have h2 := List.all_eq_true.1 h1 γ hγL
  rw [decide_eq_true_eq] at h2
  rwa [e6a3xc2_Cvecs_mem] at h2

private theorem e6a3xc2_mem_PhiD {γ : Fin (Tag.rank .E6) → ℤ} :
    γ ∈ e6a3_PhiD ↔ γ ∈ e6a3_A ∨ γ ∈ e6a3_B ∨ γ ∈ e6a3_C := by
  rw [e6a3_PhiD]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

private theorem e6a3xc2_subset_PhiD_A : e6a3_A ⊆ e6a3_PhiD :=
  fun _ h => (e6a3xc2_mem_PhiD).2 (Or.inl h)
private theorem e6a3xc2_subset_PhiD_B : e6a3_B ⊆ e6a3_PhiD :=
  fun _ h => (e6a3xc2_mem_PhiD).2 (Or.inr (Or.inl h))
private theorem e6a3xc2_subset_PhiD_C : e6a3_C ⊆ e6a3_PhiD :=
  fun _ h => (e6a3xc2_mem_PhiD).2 (Or.inr (Or.inr h))

private theorem e6a3xb_image_smul_A
    (w : WeylGroup .E6)
    (hw : w ∈ CFSG.HardMathSupport.Timmesfeld.Torality.familyStabilizer e6a3xb_fam) :
    (fun α => w • α) '' e6a3_A = e6a3_A ∨ (fun α => w • α) '' e6a3_A = e6a3_B ∨
      (fun α => w • α) '' e6a3_A = e6a3_C := by
  have hPhi : ∀ α ∈ e6a3_PhiD, (w • α) ∈ e6a3_PhiD := by
    intro α hα
    have h := e6a3xc2_image_PhiD w hw
    rw [← h]; exact ⟨α, hα, rfl⟩
  have hPhipre : ∀ α ∈ e6a3_PhiD, (w⁻¹ • α) ∈ e6a3_PhiD := by
    intro α hα
    have h := e6a3xc2_image_PhiD w⁻¹
      (CFSG.HardMathSupport.Timmesfeld.Torality.familyStabilizer_inv hw)
    rw [← h]; exact ⟨α, hα, rfl⟩
  have hset : (fun α => w • α) '' e6a3_A =
      {γ | γ ∈ e6a3_PhiD ∧ iform (w • e6a3xc2_vA0) γ ≠ 0} := by
    ext γ; constructor
    · rintro ⟨α, hα, rfl⟩
      refine ⟨hPhi α (e6a3xc2_subset_PhiD_A hα), ?_⟩
      rw [iform_smul]
      exact (e6a3xc2_nonorth_A (x := e6a3xc2_vA0) ((e6a3xc2_mem_A).2 (Or.inl rfl)) α
        (e6a3xc2_subset_PhiD_A hα)).2 hα
    · rintro ⟨hγ, hif⟩
      refine ⟨w⁻¹ • γ, ?_, by simp [smul_inv_smul]⟩
      have hif' : iform e6a3xc2_vA0 (w⁻¹ • γ) ≠ 0 := by
        rw [show iform e6a3xc2_vA0 (w⁻¹ • γ) = iform (w • e6a3xc2_vA0) γ from
          (iform_smul w e6a3xc2_vA0 (w⁻¹ • γ)).symm.trans (by rw [smul_inv_smul])]
        exact hif
      exact (e6a3xc2_nonorth_A (x := e6a3xc2_vA0) ((e6a3xc2_mem_A).2 (Or.inl rfl))
        (w⁻¹ • γ) (hPhipre γ hγ)).1 hif'
  have hmem : w • e6a3xc2_vA0 ∈ e6a3_PhiD :=
    hPhi _ (e6a3xc2_subset_PhiD_A ((e6a3xc2_mem_A).2 (Or.inl rfl)))
  rcases (e6a3xc2_mem_PhiD).1 hmem with h | h | h
  · left
    rw [hset]
    ext γ; constructor
    · rintro ⟨hγ, hif⟩; exact (e6a3xc2_nonorth_A h γ hγ).1 hif
    · intro hγ
      exact ⟨e6a3xc2_subset_PhiD_A hγ,
        (e6a3xc2_nonorth_A h γ (e6a3xc2_subset_PhiD_A hγ)).2 hγ⟩
  · right; left
    rw [hset]
    ext γ; constructor
    · rintro ⟨hγ, hif⟩; exact (e6a3xc2_nonorth_B h γ hγ).1 hif
    · intro hγ
      exact ⟨e6a3xc2_subset_PhiD_B hγ,
        (e6a3xc2_nonorth_B h γ (e6a3xc2_subset_PhiD_B hγ)).2 hγ⟩
  · right; right
    rw [hset]
    ext γ; constructor
    · rintro ⟨hγ, hif⟩; exact (e6a3xc2_nonorth_C h γ hγ).1 hif
    · intro hγ
      exact ⟨e6a3xc2_subset_PhiD_C hγ,
        (e6a3xc2_nonorth_C h γ (e6a3xc2_subset_PhiD_C hγ)).2 hγ⟩

private theorem e6a3xb_image_smul_C
    (w : WeylGroup .E6)
    (hw : w ∈ CFSG.HardMathSupport.Timmesfeld.Torality.familyStabilizer e6a3xb_fam) :
    (fun α => w • α) '' e6a3_C = e6a3_A ∨ (fun α => w • α) '' e6a3_C = e6a3_B ∨
      (fun α => w • α) '' e6a3_C = e6a3_C := by
  have hPhi : ∀ α ∈ e6a3_PhiD, (w • α) ∈ e6a3_PhiD := by
    intro α hα
    have h := e6a3xc2_image_PhiD w hw
    rw [← h]; exact ⟨α, hα, rfl⟩
  have hPhipre : ∀ α ∈ e6a3_PhiD, (w⁻¹ • α) ∈ e6a3_PhiD := by
    intro α hα
    have h := e6a3xc2_image_PhiD w⁻¹
      (CFSG.HardMathSupport.Timmesfeld.Torality.familyStabilizer_inv hw)
    rw [← h]; exact ⟨α, hα, rfl⟩
  have hset : (fun α => w • α) '' e6a3_C =
      {γ | γ ∈ e6a3_PhiD ∧ iform (w • e6a3xc2_vC0) γ ≠ 0} := by
    ext γ; constructor
    · rintro ⟨α, hα, rfl⟩
      refine ⟨hPhi α (e6a3xc2_subset_PhiD_C hα), ?_⟩
      rw [iform_smul]
      exact (e6a3xc2_nonorth_C (x := e6a3xc2_vC0) ((e6a3xc2_mem_C).2 (Or.inl rfl)) α
        (e6a3xc2_subset_PhiD_C hα)).2 hα
    · rintro ⟨hγ, hif⟩
      refine ⟨w⁻¹ • γ, ?_, by simp [smul_inv_smul]⟩
      have hif' : iform e6a3xc2_vC0 (w⁻¹ • γ) ≠ 0 := by
        rw [show iform e6a3xc2_vC0 (w⁻¹ • γ) = iform (w • e6a3xc2_vC0) γ from
          (iform_smul w e6a3xc2_vC0 (w⁻¹ • γ)).symm.trans (by rw [smul_inv_smul])]
        exact hif
      exact (e6a3xc2_nonorth_C (x := e6a3xc2_vC0) ((e6a3xc2_mem_C).2 (Or.inl rfl))
        (w⁻¹ • γ) (hPhipre γ hγ)).1 hif'
  have hmem : w • e6a3xc2_vC0 ∈ e6a3_PhiD :=
    hPhi _ (e6a3xc2_subset_PhiD_C ((e6a3xc2_mem_C).2 (Or.inl rfl)))
  rcases (e6a3xc2_mem_PhiD).1 hmem with h | h | h
  · left
    rw [hset]
    ext γ; constructor
    · rintro ⟨hγ, hif⟩; exact (e6a3xc2_nonorth_A h γ hγ).1 hif
    · intro hγ
      exact ⟨e6a3xc2_subset_PhiD_A hγ,
        (e6a3xc2_nonorth_A h γ (e6a3xc2_subset_PhiD_A hγ)).2 hγ⟩
  · right; left
    rw [hset]
    ext γ; constructor
    · rintro ⟨hγ, hif⟩; exact (e6a3xc2_nonorth_B h γ hγ).1 hif
    · intro hγ
      exact ⟨e6a3xc2_subset_PhiD_B hγ,
        (e6a3xc2_nonorth_B h γ (e6a3xc2_subset_PhiD_B hγ)).2 hγ⟩
  · right; right
    rw [hset]
    ext γ; constructor
    · rintro ⟨hγ, hif⟩; exact (e6a3xc2_nonorth_C h γ hγ).1 hif
    · intro hγ
      exact ⟨e6a3xc2_subset_PhiD_C hγ,
        (e6a3xc2_nonorth_C h γ (e6a3xc2_subset_PhiD_C hγ)).2 hγ⟩

private theorem e6a3xc2_isRoot_of_mem_PhiD

    {β : Fin (Tag.rank .E6) → ℤ} (hβ : β ∈ e6a3_PhiD) : IsRoot .E6 β := by
  rw [← e6a3xb_rootCharKernel_eq] at hβ
  exact hβ.1

private theorem e6a3xc2_test_orth_AB :
    (e6a3xc2_Avecs.all (fun x => e6a3xc2_Bvecs.all (fun γ =>
      decide (iform x γ = 0)))) = true := by
  decide +kernel
private theorem e6a3xc2_test_orth_AC :
    (e6a3xc2_Avecs.all (fun x => e6a3xc2_Cvecs.all (fun γ =>
      decide (iform x γ = 0)))) = true := by
  decide +kernel
private theorem e6a3xc2_test_orth_BC :
    (e6a3xc2_Bvecs.all (fun x => e6a3xc2_Cvecs.all (fun γ =>
      decide (iform x γ = 0)))) = true := by
  decide +kernel

private theorem e6a3xc2_orth_AB {x γ : Fin (Tag.rank .E6) → ℤ}
    (hx : x ∈ e6a3_A) (hγ : γ ∈ e6a3_B) : iform x γ = 0 := by
  have hxL : x ∈ e6a3xc2_Avecs := (e6a3xc2_Avecs_mem).2 hx
  have hγL : γ ∈ e6a3xc2_Bvecs := (e6a3xc2_Bvecs_mem).2 hγ
  have h1 := List.all_eq_true.1 e6a3xc2_test_orth_AB x hxL
  have h2 := List.all_eq_true.1 h1 γ hγL
  rwa [decide_eq_true_eq] at h2
private theorem e6a3xc2_orth_AC {x γ : Fin (Tag.rank .E6) → ℤ}
    (hx : x ∈ e6a3_A) (hγ : γ ∈ e6a3_C) : iform x γ = 0 := by
  have hxL : x ∈ e6a3xc2_Avecs := (e6a3xc2_Avecs_mem).2 hx
  have hγL : γ ∈ e6a3xc2_Cvecs := (e6a3xc2_Cvecs_mem).2 hγ
  have h1 := List.all_eq_true.1 e6a3xc2_test_orth_AC x hxL
  have h2 := List.all_eq_true.1 h1 γ hγL
  rwa [decide_eq_true_eq] at h2
private theorem e6a3xc2_orth_BC {x γ : Fin (Tag.rank .E6) → ℤ}
    (hx : x ∈ e6a3_B) (hγ : γ ∈ e6a3_C) : iform x γ = 0 := by
  have hxL : x ∈ e6a3xc2_Bvecs := (e6a3xc2_Bvecs_mem).2 hx
  have hγL : γ ∈ e6a3xc2_Cvecs := (e6a3xc2_Cvecs_mem).2 hγ
  have h1 := List.all_eq_true.1 e6a3xc2_test_orth_BC x hxL
  have h2 := List.all_eq_true.1 h1 γ hγL
  rwa [decide_eq_true_eq] at h2

private theorem e6a3xc2_commute_rootSpan

    {S : Set (Fin (Tag.rank .E6) → ℤ)} {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β)
    (horth : ∀ γ ∈ S, iform β γ = 0) (hSroot : ∀ γ ∈ S, IsRoot .E6 γ)
    (c : F4) {y : ModGL .E6 F4} (hy : y ∈ rootSpan .E6 F4 S) :
    pinnedX .E6 F4 β c * y = y * pinnedX .E6 F4 β c := by
  rw [rootSpan_eq_closure] at hy
  have hx : ∀ γ ∈ S, ∀ d : F4,
      pinnedX .E6 F4 β c * pinnedX .E6 F4 γ d =
        pinnedX .E6 F4 γ d * pinnedX .E6 F4 β c := by
    intro γ hγ d
    have h0 : dotProduct β (Matrix.mulVec (Tag.E6).symmetrizedCartan γ) = 0 := by
      rw [dotProduct_mulVec_eq_iform]
      exact horth γ hγ
    exact (simply_laced_orthogonal_root_commutation .E6 (Or.inr (Or.inl rfl))).2 F4 β γ hβ
      (hSroot γ hγ) h0 _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)
  have hle : Subgroup.closure {g | ∃ γ ∈ S, ∃ d : F4, pinnedX .E6 F4 γ d = g} ≤
      Subgroup.centralizer ({pinnedX .E6 F4 β c} : Set (ModGL .E6 F4)) := by
    rw [Subgroup.closure_le]
    rintro g ⟨γ, hγS, d, rfl⟩
    change pinnedX .E6 F4 γ d ∈ Subgroup.centralizer ({pinnedX .E6 F4 β c} : Set (ModGL .E6 F4))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hx γ hγS d).symm
  have h1 := hle hy
  change y ∈ Subgroup.centralizer ({pinnedX .E6 F4 β c} : Set (ModGL .E6 F4)) at h1
  rw [Subgroup.mem_centralizer_singleton_iff] at h1
  exact h1.symm

private theorem e6a3xc2_sup_abelian
    {H K : Subgroup (ModGL .E6 F4)}
    (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (hHK : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    ∀ x ∈ H ⊔ K, ∀ y ∈ H ⊔ K, x * y = y * x := by
  intro x hx y hy
  have hle : (H ⊔ K : Subgroup (ModGL .E6 F4)) ≤
      Subgroup.centralizer ((H ⊔ K : Subgroup (ModGL .E6 F4)) : Set (ModGL .E6 F4)) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (hH a ha b hb).symm
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact hHK b hb a ha
    · rw [Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (hHK a ha b hb).symm
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (hK a ha b hb).symm
  exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) y hy).symm

private theorem e6a3xc2_sup_noncomm
    {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) :
    ∃ x y : (rootSubgroup .E6 F4 β ⊔ rootSubgroup .E6 F4 (-β) : Subgroup (ModGL .E6 F4)),
      x * y ≠ y * x := by
  have hcard : 4 ≤ Nat.card F4 := by
    have h : Nat.card F4 = 4 := by simpa using GaloisField.card 2 2 (by norm_num)
    omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hnc⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .E6 F4 hβ
  exact (hnc inferInstance hcard).2.2

private theorem e6a3xc2_noncomm
    {S T : Set (Fin (Tag.rank .E6) → ℤ)} (h : rootSpan .E6 F4 S = rootSpan .E6 F4 T)
    (hSroot : ∀ γ ∈ S, IsRoot .E6 γ)
    {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β)
    (hβT : β ∈ T) (hnegβT : -β ∈ T) (horth : ∀ γ ∈ S, iform β γ = 0) : False := by
  have hUnbS : rootSubgroup .E6 F4 (-β) ≤ rootSpan .E6 F4 S :=
    h.symm ▸ rootSubgroup_le_rootSpan hnegβT
  have hcross : ∀ x ∈ rootSubgroup .E6 F4 β, ∀ y ∈ rootSubgroup .E6 F4 (-β),
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    exact e6a3xc2_commute_rootSpan hβ horth hSroot c (hUnbS hy)
  have hUbCom : ∀ x ∈ rootSubgroup .E6 F4 β, ∀ y ∈ rootSubgroup .E6 F4 β, x * y = y * x :=
    fun x hx y hy => rootSubgroup_mul_comm F4 hx hy
  have hUnbCom : ∀ x ∈ rootSubgroup .E6 F4 (-β), ∀ y ∈ rootSubgroup .E6 F4 (-β),
      x * y = y * x := fun x hx y hy => rootSubgroup_mul_comm F4 hx hy
  have hJab := e6a3xc2_sup_abelian hUbCom hUnbCom hcross
  obtain ⟨x, y, hxy⟩ := e6a3xc2_sup_noncomm hβ
  exact hxy (Subtype.ext (hJab x x.2 y y.2))

private theorem e6a3xb_rootSpan_inj
    {S T : Set (Fin (Tag.rank .E6) → ℤ)}
    (hS : S = e6a3_A ∪ e6a3_C ∨ S = e6a3_A ∪ e6a3_B ∨ S = e6a3_B ∪ e6a3_C)
    (hT : T = e6a3_A ∪ e6a3_C ∨ T = e6a3_A ∪ e6a3_B ∨ T = e6a3_B ∪ e6a3_C)
    (h : rootSpan .E6 F4 S = rootSpan .E6 F4 T) : S = T := by
  by_contra hne
  have hvA0 : e6a3xc2_vA0 ∈ e6a3_A := (e6a3xc2_mem_A).2 (Or.inl rfl)
  have hvB0 : e6a3xc2_vB0 ∈ e6a3_B := (e6a3xc2_mem_B).2 (Or.inl rfl)
  have hvC0 : e6a3xc2_vC0 ∈ e6a3_C := (e6a3xc2_mem_C).2 (Or.inl rfl)
  have hroot_AC : ∀ γ ∈ e6a3_A ∪ e6a3_C, IsRoot .E6 γ := by
    rintro γ (hγ | hγ)
    · exact e6a3xc2_isRoot_of_mem_PhiD (e6a3xc2_subset_PhiD_A hγ)
    · exact e6a3xc2_isRoot_of_mem_PhiD (e6a3xc2_subset_PhiD_C hγ)
  have hroot_AB : ∀ γ ∈ e6a3_A ∪ e6a3_B, IsRoot .E6 γ := by
    rintro γ (hγ | hγ)
    · exact e6a3xc2_isRoot_of_mem_PhiD (e6a3xc2_subset_PhiD_A hγ)
    · exact e6a3xc2_isRoot_of_mem_PhiD (e6a3xc2_subset_PhiD_B hγ)
  have hroot_BC : ∀ γ ∈ e6a3_B ∪ e6a3_C, IsRoot .E6 γ := by
    rintro γ (hγ | hγ)
    · exact e6a3xc2_isRoot_of_mem_PhiD (e6a3xc2_subset_PhiD_B hγ)
    · exact e6a3xc2_isRoot_of_mem_PhiD (e6a3xc2_subset_PhiD_C hγ)
  have horth_AC_B : ∀ γ ∈ e6a3_A ∪ e6a3_C, iform e6a3xc2_vB0 γ = 0 := by
    rintro γ (hγ | hγ)
    · rw [iform_comm]; exact e6a3xc2_orth_AB hγ hvB0
    · exact e6a3xc2_orth_BC hvB0 hγ
  have horth_AB_C : ∀ γ ∈ e6a3_A ∪ e6a3_B, iform e6a3xc2_vC0 γ = 0 := by
    rintro γ (hγ | hγ)
    · rw [iform_comm]; exact e6a3xc2_orth_AC hγ hvC0
    · rw [iform_comm]; exact e6a3xc2_orth_BC hγ hvC0
  have horth_BC_A : ∀ γ ∈ e6a3_B ∪ e6a3_C, iform e6a3xc2_vA0 γ = 0 := by
    rintro γ (hγ | hγ)
    · exact e6a3xc2_orth_AB hvA0 hγ
    · exact e6a3xc2_orth_AC hvA0 hγ
  rcases hS with hS | hS | hS <;> rcases hT with hT | hT | hT
  · exact (hne (hS.trans hT.symm)).elim
  · exact e6a3xc2_noncomm h (hS.symm ▸ hroot_AC)
      (e6a3xc2_isRoot_of_mem_PhiD (e6a3xc2_subset_PhiD_B hvB0))
      (by rw [hT]; exact Or.inr hvB0)
      (by rw [hT]; exact Or.inr ((e6a3xc2_mem_B).2 (by simp)))
      (hS.symm ▸ horth_AC_B)
  · exact e6a3xc2_noncomm h (hS.symm ▸ hroot_AC)
      (e6a3xc2_isRoot_of_mem_PhiD (e6a3xc2_subset_PhiD_B hvB0))
      (by rw [hT]; exact Or.inl hvB0)
      (by rw [hT]; exact Or.inl ((e6a3xc2_mem_B).2 (by simp)))
      (hS.symm ▸ horth_AC_B)
  · exact e6a3xc2_noncomm h (hS.symm ▸ hroot_AB)
      (e6a3xc2_isRoot_of_mem_PhiD (e6a3xc2_subset_PhiD_C hvC0))
      (by rw [hT]; exact Or.inr hvC0)
      (by rw [hT]; exact Or.inr ((e6a3xc2_mem_C).2 (by simp)))
      (hS.symm ▸ horth_AB_C)
  · exact (hne (hS.trans hT.symm)).elim
  · exact e6a3xc2_noncomm h (hS.symm ▸ hroot_AB)
      (e6a3xc2_isRoot_of_mem_PhiD (e6a3xc2_subset_PhiD_C hvC0))
      (by rw [hT]; exact Or.inr hvC0)
      (by rw [hT]; exact Or.inr ((e6a3xc2_mem_C).2 (by simp)))
      (hS.symm ▸ horth_AB_C)
  · exact e6a3xc2_noncomm h (hS.symm ▸ hroot_BC)
      (e6a3xc2_isRoot_of_mem_PhiD (e6a3xc2_subset_PhiD_A hvA0))
      (by rw [hT]; exact Or.inl hvA0)
      (by rw [hT]; exact Or.inl ((e6a3xc2_mem_A).2 (by simp)))
      (hS.symm ▸ horth_BC_A)
  · exact e6a3xc2_noncomm h (hS.symm ▸ hroot_BC)
      (e6a3xc2_isRoot_of_mem_PhiD (e6a3xc2_subset_PhiD_A hvA0))
      (by rw [hT]; exact Or.inl hvA0)
      (by rw [hT]; exact Or.inl ((e6a3xc2_mem_A).2 (by simp)))
      (hS.symm ▸ horth_BC_A)
  · exact (hne (hS.trans hT.symm)).elim

private theorem e6a3xc2_u_image_A
    :
    (fun α => e6a3xb_u • α) '' e6a3_A = e6a3_C := by
  ext γ
  constructor
  · rintro ⟨α, hα, rfl⟩
    rw [e6a3xc2_mem_A] at hα
    rcases hα with h | h | h | h | h | h
    · rw [h]; beta_reduce; rw [e6a3xc2_u_vA0]; exact (e6a3xc2_mem_C).2 (Or.inl rfl)
    · rw [h]; beta_reduce; rw [e6a3xc2_u_vA1]; exact (e6a3xc2_mem_C).2 (Or.inr (Or.inl rfl))
    · rw [h]; beta_reduce; rw [e6a3xc2_u_vA2]
      exact (e6a3xc2_mem_C).2 (Or.inr (Or.inr (Or.inl rfl)))
    · have h' : α = -e6a3xc2_vA0 := (neg_neg α).symm.trans (congrArg Neg.neg h)
      rw [h']; beta_reduce; rw [smul_neg, e6a3xc2_u_vA0]
      exact (e6a3xc2_mem_C).2 (by simp)
    · have h' : α = -e6a3xc2_vA1 := (neg_neg α).symm.trans (congrArg Neg.neg h)
      rw [h']; beta_reduce; rw [smul_neg, e6a3xc2_u_vA1]
      exact (e6a3xc2_mem_C).2 (by simp)
    · have h' : α = -e6a3xc2_vA2 := (neg_neg α).symm.trans (congrArg Neg.neg h)
      rw [h']; beta_reduce; rw [smul_neg, e6a3xc2_u_vA2]
      exact (e6a3xc2_mem_C).2 (by simp)
  · intro hγ
    rw [e6a3xc2_mem_C] at hγ
    rcases hγ with h | h | h | h | h | h
    · exact ⟨e6a3xc2_vA0, (e6a3xc2_mem_A).2 (Or.inl rfl), by simpa [e6a3xc2_u_vA0] using h.symm⟩
    · exact ⟨e6a3xc2_vA1, (e6a3xc2_mem_A).2 (Or.inr (Or.inl rfl)),
        by simpa [e6a3xc2_u_vA1] using h.symm⟩
    · exact ⟨e6a3xc2_vA2, (e6a3xc2_mem_A).2 (Or.inr (Or.inr (Or.inl rfl))),
        by simpa [e6a3xc2_u_vA2] using h.symm⟩
    · refine ⟨-e6a3xc2_vA0, (e6a3xc2_mem_A).2 (by simp), ?_⟩
      simpa [smul_neg, e6a3xc2_u_vA0] using (congrArg Neg.neg h).symm
    · refine ⟨-e6a3xc2_vA1, (e6a3xc2_mem_A).2 (by simp), ?_⟩
      simpa [smul_neg, e6a3xc2_u_vA1] using (congrArg Neg.neg h).symm
    · refine ⟨-e6a3xc2_vA2, (e6a3xc2_mem_A).2 (by simp), ?_⟩
      simpa [smul_neg, e6a3xc2_u_vA2] using (congrArg Neg.neg h).symm

private theorem e6a3xc2_u_image_C
    :
    (fun α => e6a3xb_u • α) '' e6a3_C = e6a3_A := by
  ext γ
  constructor
  · rintro ⟨α, hα, rfl⟩
    rw [e6a3xc2_mem_C] at hα
    rcases hα with h | h | h | h | h | h
    · rw [h]; beta_reduce; rw [e6a3xc2_u_vC0]; exact (e6a3xc2_mem_A).2 (Or.inl rfl)
    · rw [h]; beta_reduce; rw [e6a3xc2_u_vC1]; exact (e6a3xc2_mem_A).2 (Or.inr (Or.inl rfl))
    · rw [h]; beta_reduce; rw [e6a3xc2_u_vC2]
      exact (e6a3xc2_mem_A).2 (Or.inr (Or.inr (Or.inl rfl)))
    · have h' : α = -e6a3xc2_vC0 := (neg_neg α).symm.trans (congrArg Neg.neg h)
      rw [h']; beta_reduce; rw [smul_neg, e6a3xc2_u_vC0]
      exact (e6a3xc2_mem_A).2 (by simp)
    · have h' : α = -e6a3xc2_vC1 := (neg_neg α).symm.trans (congrArg Neg.neg h)
      rw [h']; beta_reduce; rw [smul_neg, e6a3xc2_u_vC1]
      exact (e6a3xc2_mem_A).2 (by simp)
    · have h' : α = -e6a3xc2_vC2 := (neg_neg α).symm.trans (congrArg Neg.neg h)
      rw [h']; beta_reduce; rw [smul_neg, e6a3xc2_u_vC2]
      exact (e6a3xc2_mem_A).2 (by simp)
  · intro hγ
    rw [e6a3xc2_mem_A] at hγ
    rcases hγ with h | h | h | h | h | h
    · exact ⟨e6a3xc2_vC0, (e6a3xc2_mem_C).2 (Or.inl rfl), by simpa [e6a3xc2_u_vC0] using h.symm⟩
    · exact ⟨e6a3xc2_vC1, (e6a3xc2_mem_C).2 (Or.inr (Or.inl rfl)),
        by simpa [e6a3xc2_u_vC1] using h.symm⟩
    · exact ⟨e6a3xc2_vC2, (e6a3xc2_mem_C).2 (Or.inr (Or.inr (Or.inl rfl))),
        by simpa [e6a3xc2_u_vC2] using h.symm⟩
    · refine ⟨-e6a3xc2_vC0, (e6a3xc2_mem_C).2 (by simp), ?_⟩
      simpa [smul_neg, e6a3xc2_u_vC0] using (congrArg Neg.neg h).symm
    · refine ⟨-e6a3xc2_vC1, (e6a3xc2_mem_C).2 (by simp), ?_⟩
      simpa [smul_neg, e6a3xc2_u_vC1] using (congrArg Neg.neg h).symm
    · refine ⟨-e6a3xc2_vC2, (e6a3xc2_mem_C).2 (by simp), ?_⟩
      simpa [smul_neg, e6a3xc2_u_vC2] using (congrArg Neg.neg h).symm

private theorem e6a3xc2_u_image_B
    :
    (fun α => e6a3xb_u • α) '' e6a3_B = e6a3_B := by
  ext γ
  constructor
  · rintro ⟨α, hα, rfl⟩
    rw [e6a3xc2_mem_B] at hα
    rcases hα with h | h | h | h | h | h
    · rw [h]; beta_reduce; rw [e6a3xc2_u_vB0]; exact (e6a3xc2_mem_B).2 (Or.inr (Or.inl rfl))
    · rw [h]; beta_reduce; rw [e6a3xc2_u_vB1]; exact (e6a3xc2_mem_B).2 (Or.inl rfl)
    · rw [h]; beta_reduce; rw [e6a3xc2_u_vB2]
      exact (e6a3xc2_mem_B).2 (Or.inr (Or.inr (Or.inl rfl)))
    · have h' : α = -e6a3xc2_vB0 := (neg_neg α).symm.trans (congrArg Neg.neg h)
      rw [h']; beta_reduce; rw [smul_neg, e6a3xc2_u_vB0]
      exact (e6a3xc2_mem_B).2 (by simp)
    · have h' : α = -e6a3xc2_vB1 := (neg_neg α).symm.trans (congrArg Neg.neg h)
      rw [h']; beta_reduce; rw [smul_neg, e6a3xc2_u_vB1]
      exact (e6a3xc2_mem_B).2 (by simp)
    · have h' : α = -e6a3xc2_vB2 := (neg_neg α).symm.trans (congrArg Neg.neg h)
      rw [h']; beta_reduce; rw [smul_neg, e6a3xc2_u_vB2]
      exact (e6a3xc2_mem_B).2 (by simp)
  · intro hγ
    rw [e6a3xc2_mem_B] at hγ
    rcases hγ with h | h | h | h | h | h
    · exact ⟨e6a3xc2_vB1, (e6a3xc2_mem_B).2 (Or.inr (Or.inl rfl)),
        by simpa [e6a3xc2_u_vB1] using h.symm⟩
    · exact ⟨e6a3xc2_vB0, (e6a3xc2_mem_B).2 (Or.inl rfl),
        by simpa [e6a3xc2_u_vB0] using h.symm⟩
    · exact ⟨e6a3xc2_vB2, (e6a3xc2_mem_B).2 (Or.inr (Or.inr (Or.inl rfl))),
        by simpa [e6a3xc2_u_vB2] using h.symm⟩
    · refine ⟨-e6a3xc2_vB1, (e6a3xc2_mem_B).2 (by simp), ?_⟩
      simpa [smul_neg, e6a3xc2_u_vB1] using (congrArg Neg.neg h).symm
    · refine ⟨-e6a3xc2_vB0, (e6a3xc2_mem_B).2 (by simp), ?_⟩
      simpa [smul_neg, e6a3xc2_u_vB0] using (congrArg Neg.neg h).symm
    · refine ⟨-e6a3xc2_vB2, (e6a3xc2_mem_B).2 (by simp), ?_⟩
      simpa [smul_neg, e6a3xc2_u_vB2] using (congrArg Neg.neg h).symm

private theorem e6a3xc2_uinv_image_C
    :
    (fun α => e6a3xb_u⁻¹ • α) '' e6a3_C = e6a3_A := by
  rw [← e6a3xc2_u_image_A, Set.image_image]
  simp [smul_inv_smul]

private theorem e6a3xc2_uinv_image_A
    :
    (fun α => e6a3xb_u⁻¹ • α) '' e6a3_A = e6a3_C := by
  rw [← e6a3xc2_u_image_C, Set.image_image]
  simp [smul_inv_smul]

private theorem e6a3xc2_uinv_image_B
    :
    (fun α => e6a3xb_u⁻¹ • α) '' e6a3_B = e6a3_B := by
  rw [← e6a3xc2_u_image_B, Set.image_image]
  simp only [Function.comp_apply, inv_smul_smul]
  rw [e6a3xc2_u_image_B]
  exact Set.image_id e6a3_B

private theorem e6a3xc2_vA0_notin_B : e6a3xc2_vA0 ∉ e6a3_B := by
  rw [e6a3xc2_mem_B]; simp only [not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
private theorem e6a3xc2_vA0_notin_C : e6a3xc2_vA0 ∉ e6a3_C := by
  rw [e6a3xc2_mem_C]; simp only [not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
private theorem e6a3xc2_vC0_notin_A : e6a3xc2_vC0 ∉ e6a3_A := by
  rw [e6a3xc2_mem_A]; simp only [not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
private theorem e6a3xc2_vC0_notin_B : e6a3xc2_vC0 ∉ e6a3_B := by
  rw [e6a3xc2_mem_B]; simp only [not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem e6a3xb_W
    {S : Set (Fin (Tag.rank .E6) → ℤ)}
    (hS : S = e6a3_A ∪ e6a3_C ∨ S = e6a3_A ∪ e6a3_B ∨ S = e6a3_B ∪ e6a3_C)
    (hu : (fun α => e6a3xb_u⁻¹ • α) '' S = S) : S = e6a3_S := by
  rcases hS with h | h | h
  · exact h
  · exfalso
    have h1 : (fun α => e6a3xb_u⁻¹ • α) '' S = e6a3_B ∪ e6a3_C := by
      rw [h, Set.image_union, e6a3xc2_uinv_image_A, e6a3xc2_uinv_image_B, Set.union_comm]
    have hBC : e6a3_B ∪ e6a3_C = S := h1.symm.trans hu
    have hvA0S : e6a3xc2_vA0 ∈ S := by
      rw [h]; exact Or.inl ((e6a3xc2_mem_A).2 (Or.inl rfl))
    have hvA0BC : e6a3xc2_vA0 ∈ e6a3_B ∪ e6a3_C := hBC.symm ▸ hvA0S
    rcases hvA0BC with h2 | h2
    · exact e6a3xc2_vA0_notin_B h2
    · exact e6a3xc2_vA0_notin_C h2
  · exfalso
    have h1 : (fun α => e6a3xb_u⁻¹ • α) '' S = e6a3_A ∪ e6a3_B := by
      rw [h, Set.image_union, e6a3xc2_uinv_image_B, e6a3xc2_uinv_image_C, Set.union_comm]
    have hAB : e6a3_A ∪ e6a3_B = S := h1.symm.trans hu
    have hvC0S : e6a3xc2_vC0 ∈ S := by
      rw [h]; exact Or.inr ((e6a3xc2_mem_C).2 (Or.inl rfl))
    have hvC0AB : e6a3xc2_vC0 ∈ e6a3_A ∪ e6a3_B := hAB.symm ▸ hvC0S
    rcases hvC0AB with h2 | h2
    · exact e6a3xc2_vC0_notin_A h2
    · exact e6a3xc2_vC0_notin_B h2

private theorem e6a3xb_S_isRoot :
    ∀ α ∈ e6a3_S, IsRoot .E6 α := by
  intro α hα
  have hA : e6a3_Apos = [e6a3xc2_vA0, e6a3xc2_vA1, e6a3xc2_vA2] := rfl
  have hC : e6a3_Cpos = [e6a3xc2_vC0, e6a3xc2_vC1, e6a3xc2_vC2] := rfl
  simp only [e6a3_S, e6a3_A, e6a3_C, e6a3_component, hA, hC,
    Set.mem_union, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
    or_assoc] at hα
  rcases hα with h | h | h | h | h | h | h | h | h | h | h | h
  · subst h; rw [← e6a3xc2_root_vA0]; exact CFSG.LieType.Chevalley.C2E6Std.isRoot_e6Root _
  · subst h; rw [← e6a3xc2_root_vA1]; exact CFSG.LieType.Chevalley.C2E6Std.isRoot_e6Root _
  · subst h; rw [← e6a3xc2_root_vA2]; exact CFSG.LieType.Chevalley.C2E6Std.isRoot_e6Root _
  · have h' : α = -e6a3xc2_vA0 := (neg_neg α).symm.trans (congrArg Neg.neg h)
    subst h'; rw [← e6a3xc2_root_nA0]
    exact CFSG.LieType.Chevalley.C2E6Std.isRoot_e6Root _
  · have h' : α = -e6a3xc2_vA1 := (neg_neg α).symm.trans (congrArg Neg.neg h)
    subst h'; rw [← e6a3xc2_root_nA1]
    exact CFSG.LieType.Chevalley.C2E6Std.isRoot_e6Root _
  · have h' : α = -e6a3xc2_vA2 := (neg_neg α).symm.trans (congrArg Neg.neg h)
    subst h'; rw [← e6a3xc2_root_nA2]
    exact CFSG.LieType.Chevalley.C2E6Std.isRoot_e6Root _
  · subst h; rw [← e6a3xc2_root_vC0]; exact CFSG.LieType.Chevalley.C2E6Std.isRoot_e6Root _
  · subst h; rw [← e6a3xc2_root_vC1]; exact CFSG.LieType.Chevalley.C2E6Std.isRoot_e6Root _
  · subst h; rw [← e6a3xc2_root_vC2]; exact CFSG.LieType.Chevalley.C2E6Std.isRoot_e6Root _
  · have h' : α = -e6a3xc2_vC0 := (neg_neg α).symm.trans (congrArg Neg.neg h)
    subst h'; rw [← e6a3xc2_root_nC0]
    exact CFSG.LieType.Chevalley.C2E6Std.isRoot_e6Root _
  · have h' : α = -e6a3xc2_vC1 := (neg_neg α).symm.trans (congrArg Neg.neg h)
    subst h'; rw [← e6a3xc2_root_nC1]
    exact CFSG.LieType.Chevalley.C2E6Std.isRoot_e6Root _
  · have h' : α = -e6a3xc2_vC2 := (neg_neg α).symm.trans (congrArg Neg.neg h)
    subst h'; rw [← e6a3xc2_root_nC2]
    exact CFSG.LieType.Chevalley.C2E6Std.isRoot_e6Root _

private theorem e6a3xb_image_smul_S
    (w : WeylGroup .E6)
    (hw : w ∈ CFSG.HardMathSupport.Timmesfeld.Torality.familyStabilizer e6a3xb_fam) :
    (fun α => w • α) '' e6a3_S = e6a3_A ∪ e6a3_C ∨
      (fun α => w • α) '' e6a3_S = e6a3_A ∪ e6a3_B ∨
      (fun α => w • α) '' e6a3_S = e6a3_B ∪ e6a3_C := by
  have hA := e6a3xb_image_smul_A w hw
  have hC := e6a3xb_image_smul_C w hw
  have hinj : Function.Injective (fun α : Fin (Tag.rank .E6) → ℤ => w • α) := by
    intro a b hab
    have := congrArg (fun v => w⁻¹ • v) hab
    simpa only [inv_smul_smul] using this
  have himg : Function.Injective (Set.image (fun α : Fin (Tag.rank .E6) → ℤ => w • α)) :=
    Set.image_injective.2 hinj
  have hAC : e6a3_A ≠ e6a3_C := by
    intro h
    have : e6a3xc2_vA0 ∈ e6a3_C := h ▸ (e6a3xc2_mem_A).2 (Or.inl rfl)
    exact e6a3xc2_vA0_notin_C this
  rw [e6a3_S, Set.image_union]
  rcases hA with hA | hA | hA <;> rcases hC with hC | hC | hC
  · exact absurd (himg (hA.trans hC.symm)) hAC
  · right; left; rw [hA, hC]
  · left; rw [hA, hC]
  · right; left; rw [hA, hC, Set.union_comm]
  · exact absurd (himg (hA.trans hC.symm)) hAC
  · right; right; rw [hA, hC]
  · left; rw [hA, hC, Set.union_comm]
  · right; right; rw [hA, hC, Set.union_comm]
  · exact absurd (himg (hA.trans hC.symm)) hAC

private theorem e6a3xb_u_image_S
    : (fun α => e6a3xb_u • α) '' e6a3_S = e6a3_S := by
  change (fun α => e6a3xb_u • α) '' (e6a3_A ∪ e6a3_C) = e6a3_A ∪ e6a3_C
  rw [Set.image_union, e6a3xc2_u_image_A, e6a3xc2_u_image_C, Set.union_comm]

private theorem e6a3xb_u_image_union
    {S : Set (Fin (Tag.rank .E6) → ℤ)}
    (hS : S = e6a3_A ∪ e6a3_C ∨ S = e6a3_A ∪ e6a3_B ∨ S = e6a3_B ∪ e6a3_C) :
    (fun α => e6a3xb_u⁻¹ • α) '' S = e6a3_A ∪ e6a3_C ∨
      (fun α => e6a3xb_u⁻¹ • α) '' S = e6a3_A ∪ e6a3_B ∨
      (fun α => e6a3xb_u⁻¹ • α) '' S = e6a3_B ∪ e6a3_C := by
  rcases hS with h | h | h
  · left
    rw [h, Set.image_union, e6a3xc2_uinv_image_A, e6a3xc2_uinv_image_C, Set.union_comm]
  · right; right
    rw [h, Set.image_union, e6a3xc2_uinv_image_A, e6a3xc2_uinv_image_B, Set.union_comm]
  · right; left
    rw [h, Set.image_union, e6a3xc2_uinv_image_B, e6a3xc2_uinv_image_C, Set.union_comm]

private theorem e6a3xc3_word_conj

    (ω : List (Fin (Tag.rank .E6))) (S : Set (Fin (Tag.rank .E6) → ℤ))
    (hS : ∀ α ∈ S, IsRoot .E6 α) :
    (rootSpan .E6 F4 S).map
        (MulAut.conj ((ω.map fun i => weylElt .E6 F4 i 1).prod)).toMonoidHom =
      rootSpan .E6 F4 ((fun α => (coxeterSystem .E6).wordProd ω • α) '' S) := by
  have hroot : ∀ α ∈ S,
      (rootSubgroup .E6 F4 α).map
          (MulAut.conj ((ω.map fun i => weylElt .E6 F4 i 1).prod)).toMonoidHom =
        rootSubgroup .E6 F4 ((coxeterSystem .E6).wordProd ω • α) :=
    fun α hα => map_conj_prod_weylElt_rootSubgroup F4 ω (hS α hα)
  simp only [rootSpan, Subgroup.map_iSup, iSup_image]
  exact iSup_congr fun α => iSup_congr fun hα => hroot α hα

private theorem e6a3xc3_map_conj_one {G : Type*} [Group G] (K : Subgroup G) :
    K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  have hconj : MulAut.conj (1 : G) = 1 := by
    ext x
    simp [MulAut.conj_apply]
  rw [hconj]
  exact Subgroup.map_id K

private theorem e6a3xb_nu_conj

    (S : Set (Fin (Tag.rank .E6) → ℤ)) (hS : ∀ α ∈ S, IsRoot .E6 α) :
    (rootSpan .E6 F4 S).map (MulAut.conj e6a3_nu).toMonoidHom =
      rootSpan .E6 F4 ((fun α => e6a3xb_u • α) '' S) := by
  have h := e6a3xc3_word_conj [e6a3_i0, e6a3_i3, e6a3_i5] S hS
  have hnu : (List.map (fun i => weylElt .E6 F4 i 1) [e6a3_i0, e6a3_i3, e6a3_i5]).prod =
      e6a3_nu := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, e6a3_nu, mul_one]
    rw [mul_assoc]
  have hu : (coxeterSystem .E6).wordProd [e6a3_i0, e6a3_i3, e6a3_i5] = e6a3xb_u := by
    simp only [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, e6a3xb_u, mul_one]
    rw [mul_assoc]
  rw [hnu, hu] at h
  exact h

private theorem e6a3xb_nu_inv_conj

    (S : Set (Fin (Tag.rank .E6) → ℤ)) (hS : ∀ α ∈ S, IsRoot .E6 α) :
    (rootSpan .E6 F4 S).map (MulAut.conj e6a3_nu⁻¹).toMonoidHom =
      rootSpan .E6 F4 ((fun α => e6a3xb_u⁻¹ • α) '' S) := by
  set S' : Set (Fin (Tag.rank .E6) → ℤ) := (fun α => e6a3xb_u⁻¹ • α) '' S
  have hS' : ∀ α ∈ S', IsRoot .E6 α := by
    rintro α ⟨γ, hγ, rfl⟩
    exact IsRoot.smul (hS γ hγ) e6a3xb_u⁻¹
  have h := e6a3xb_nu_conj S' hS'
  have himg : (fun α => e6a3xb_u • α) '' S' = S := by
    rw [Set.image_image]
    have hfun : (fun α : Fin (Tag.rank .E6) → ℤ =>
        e6a3xb_u • (e6a3xb_u⁻¹ • α)) = (fun α => α) := by
      funext α
      rw [← mul_smul, mul_inv_cancel, one_smul]
    rw [hfun]
    ext x
    simp
  rw [himg] at h
  have h3 := congrArg (fun K : Subgroup (ModGL .E6 F4) =>
    K.map (MulAut.conj e6a3_nu⁻¹).toMonoidHom) h
  rw [← map_conj_mul e6a3_nu⁻¹ e6a3_nu, inv_mul_cancel, e6a3xc3_map_conj_one] at h3
  exact h3.symm

private theorem e6a3xb_F_rootSpan
    (S : Set (Fin (Tag.rank .E6) → ℤ)) :
    (rootSpan .E6 F4 S).map e6a3_F = rootSpan .E6 F4 S := by
  apply map_rootSpan_of_forall
  intro α _
  apply map_rootSubgroup_of_eq (g := fun c : F4 => c ^ 2)
  · intro y
    obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.1 (frobenius_inj F4 2) y
    exact ⟨x, by simpa [frobenius_def] using hx⟩
  · intro c
    unfold e6a3_F
    rw [baseChangeGL_pinnedX, frobenius_def]

private theorem e6a3xb_F_canonicalRep
    (w : WeylGroup .E6) :
    e6a3_F (canonicalRep (coxeterSystem .E6) F4 w) =
      canonicalRep (coxeterSystem .E6) F4 w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem .E6).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  unfold e6a3_F
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact baseChangeGL_weylElt_one (frobenius F4 2) i

private theorem e6a3xb_F_torusGroup :
    (torusGroup .E6 F4).map e6a3_F = torusGroup .E6 F4 := by
  apply le_antisymm
  · rw [torusGroup, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ ⟨⟨i, t⟩, rfl⟩
    change e6a3_F (torusElt .E6 F4 i t) ∈
      Subgroup.closure (Set.range fun p : Fin (Tag.rank .E6) × F4ˣ => torusElt .E6 F4 p.1 p.2)
    unfold e6a3_F
    rw [baseChangeGL_torusElt]
    exact Subgroup.subset_closure ⟨⟨i, Units.map (frobenius F4 2).toMonoidHom t⟩, rfl⟩
  · rw [torusGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, t⟩, rfl⟩
    obtain ⟨t', ht'⟩ := Finite.injective_iff_surjective.1 (frobenius_inj F4 2) (t : F4)
    have hne : t' ≠ 0 := fun h => t.ne_zero (by rw [← ht', h, map_zero])
    refine ⟨torusElt .E6 F4 i (Units.mk0 t' hne),
      Subgroup.subset_closure ⟨⟨i, Units.mk0 t' hne⟩, rfl⟩, ?_⟩
    unfold e6a3_F
    rw [baseChangeGL_torusElt]
    exact congrArg (torusElt .E6 F4 i) (Units.ext ht')

private theorem e6a3xb_F_familyGroup :
    (CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup (K := F4) e6a3xb_fam).map
        e6a3_F =
      CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup (K := F4) e6a3xb_fam := by
  rw [CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup, Subgroup.map_sup,
    e6a3xb_F_torusGroup, e6a3xb_F_rootSpan]

private theorem e6a3xb_descent_normalizes
    (g : ModGL .E6 F4)
    (hg : g ∈ CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer .E6 F4 e6a3xb_fam)
    (hF : e6a3_F g = e6a3_nu⁻¹ * g * e6a3_nu) :
    g ∈ Subgroup.normalizer (e6a3_GS : Set (ModGL .E6 F4)) := by
  obtain ⟨w, hw, m, hm, rfl⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer_le_mul .E6 F4 e6a3xb_fam hg
  have hwSd : (fun α => w • α) '' e6a3_S = e6a3_A ∪ e6a3_C ∨
      (fun α => w • α) '' e6a3_S = e6a3_A ∪ e6a3_B ∨
      (fun α => w • α) '' e6a3_S = e6a3_B ∪ e6a3_C := by
    rcases e6a3xb_image_smul_S w hw with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hwSroot : ∀ α ∈ (fun γ => w • γ) '' e6a3_S, IsRoot .E6 α := by
    rintro α ⟨γ, hγ, rfl⟩
    exact IsRoot.smul (e6a3xb_S_isRoot γ hγ) w
  have hmap_conj_n : (e6a3_GS).map
        (MulAut.conj (canonicalRep (coxeterSystem .E6) F4 w)).toMonoidHom =
      rootSpan .E6 F4 ((fun α => w • α) '' e6a3_S) :=
    (canonical_weyl_root_transport .E6 F4).1 w e6a3_S e6a3xb_S_isRoot
  have hmN : m ∈ Subgroup.normalizer
      (rootSpan .E6 F4 ((fun α => w • α) '' e6a3_S) : Set (ModGL .E6 F4)) :=
    e6a3xb_familyGroup_le_normalizer_union hwSd hm
  have hmN' : (rootSpan .E6 F4 ((fun α => w • α) '' e6a3_S)).map
        (MulAut.conj m).toMonoidHom =
      rootSpan .E6 F4 ((fun α => w • α) '' e6a3_S) := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_map]
    exact Subgroup.mem_normalizer_iff_conj_image_eq.1 hmN
  have hKconj : (e6a3_GS).map
        (MulAut.conj (m * canonicalRep (coxeterSystem .E6) F4 w)).toMonoidHom =
      rootSpan .E6 F4 ((fun α => w • α) '' e6a3_S) := by
    rw [map_conj_mul, hmap_conj_n, hmN']
  have hFmM : e6a3_F m ∈
      CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup (K := F4) e6a3xb_fam := by
    rw [← e6a3xb_F_familyGroup]
    exact Subgroup.mem_map_of_mem e6a3_F hm
  have hFmN : e6a3_F m ∈ Subgroup.normalizer
      (rootSpan .E6 F4 ((fun α => w • α) '' e6a3_S) : Set (ModGL .E6 F4)) :=
    e6a3xb_familyGroup_le_normalizer_union hwSd hFmM
  have hFmN' : (rootSpan .E6 F4 ((fun α => w • α) '' e6a3_S)).map
        (MulAut.conj (e6a3_F m)).toMonoidHom =
      rootSpan .E6 F4 ((fun α => w • α) '' e6a3_S) := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_map]
    exact Subgroup.mem_normalizer_iff_conj_image_eq.1 hFmN
  have hFgEq : e6a3_F (m * canonicalRep (coxeterSystem .E6) F4 w) =
      e6a3_F m * canonicalRep (coxeterSystem .E6) F4 w := by
    rw [map_mul, e6a3xb_F_canonicalRep]
  have hFgconj : (e6a3_GS).map
        (MulAut.conj (e6a3_F (m * canonicalRep (coxeterSystem .E6) F4 w))).toMonoidHom =
      rootSpan .E6 F4 ((fun α => w • α) '' e6a3_S) := by
    rw [hFgEq, map_conj_mul, hmap_conj_n, hFmN']
  have hnuK : (e6a3_GS).map (MulAut.conj e6a3_nu).toMonoidHom = e6a3_GS := by
    rw [show e6a3_GS = rootSpan .E6 F4 e6a3_S from rfl,
      e6a3xb_nu_conj e6a3_S e6a3xb_S_isRoot, e6a3xb_u_image_S]
  have hstep1 : (e6a3_GS).map
        (MulAut.conj
          (e6a3_nu⁻¹ * (m * canonicalRep (coxeterSystem .E6) F4 w) * e6a3_nu)).toMonoidHom =
      ((e6a3_GS).map (MulAut.conj e6a3_nu).toMonoidHom).map
        (MulAut.conj (e6a3_nu⁻¹ * (m * canonicalRep (coxeterSystem .E6) F4 w))).toMonoidHom :=
    map_conj_mul (e6a3_nu⁻¹ * (m * canonicalRep (coxeterSystem .E6) F4 w)) e6a3_nu e6a3_GS
  have hstep2 : ((e6a3_GS).map (MulAut.conj e6a3_nu).toMonoidHom).map
        (MulAut.conj (e6a3_nu⁻¹ * (m * canonicalRep (coxeterSystem .E6) F4 w))).toMonoidHom =
      (((e6a3_GS).map (MulAut.conj e6a3_nu).toMonoidHom).map
        (MulAut.conj (m * canonicalRep (coxeterSystem .E6) F4 w)).toMonoidHom).map
        (MulAut.conj e6a3_nu⁻¹).toMonoidHom :=
    map_conj_mul e6a3_nu⁻¹ (m * canonicalRep (coxeterSystem .E6) F4 w)
      ((e6a3_GS).map (MulAut.conj e6a3_nu).toMonoidHom)
  have hFgconj2 : (e6a3_GS).map
        (MulAut.conj (e6a3_F (m * canonicalRep (coxeterSystem .E6) F4 w))).toMonoidHom =
      rootSpan .E6 F4 ((fun α => e6a3xb_u⁻¹ • α) '' ((fun α => w • α) '' e6a3_S)) := by
    rw [hF, hstep1, hstep2, hnuK, hKconj]
    exact e6a3xb_nu_inv_conj _ hwSroot
  have hrootSpaneq : rootSpan .E6 F4 ((fun α => w • α) '' e6a3_S) =
      rootSpan .E6 F4 ((fun α => e6a3xb_u⁻¹ • α) '' ((fun α => w • α) '' e6a3_S)) := by
    rw [← hFgconj, hFgconj2]
  have huwS : (fun α => w • α) '' e6a3_S =
      (fun α => e6a3xb_u⁻¹ • α) '' ((fun α => w • α) '' e6a3_S) :=
    e6a3xb_rootSpan_inj hwSd (e6a3xb_u_image_union hwSd) hrootSpaneq
  have hwSS : (fun α => w • α) '' e6a3_S = e6a3_S := e6a3xb_W hwSd huwS.symm
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have hK : (e6a3_GS).map
        (MulAut.conj (m * canonicalRep (coxeterSystem .E6) F4 w)).toMonoidHom = e6a3_GS := by
    rw [hKconj, hwSS, e6a3_GS]
  have := congrArg SetLike.coe hK
  rwa [Subgroup.coe_map] at this

private theorem e6a3xb_P_mem :
    e6a3_P ∈ adjointGroup .E6 F4 := by
  unfold e6a3_P e6a3_P0
  exact mul_mem (mul_mem
    (mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _))
    (mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)))
    (mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _))

private theorem e6a3xb_conj_normalizer_map {G : Type*} [Group G] {K : Subgroup G} {P X : G}
    (h : P⁻¹ * X * P ∈ Subgroup.normalizer (K : Set G)) :
    X ∈ Subgroup.normalizer ((K.map (MulAut.conj P).toMonoidHom) : Set G) := by
  have hh := Subgroup.mem_normalizer_iff.1 h
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨k, hk, rfl⟩ := hy
    refine ⟨(P⁻¹ * X * P) * k * (P⁻¹ * X * P)⁻¹, (hh k).1 hk, ?_⟩
    show P * ((P⁻¹ * X * P) * k * (P⁻¹ * X * P)⁻¹) * P⁻¹ = X * (P * k * P⁻¹) * X⁻¹
    group
  · intro hy
    obtain ⟨k, hk, hky⟩ := hy
    have hk' : (P⁻¹ * X * P) * ((P⁻¹ * X * P)⁻¹ * k * (P⁻¹ * X * P)) *
        (P⁻¹ * X * P)⁻¹ ∈ K := by
      have h1 : (P⁻¹ * X * P) * ((P⁻¹ * X * P)⁻¹ * k * (P⁻¹ * X * P)) *
          (P⁻¹ * X * P)⁻¹ = k := by group
      rwa [h1]
    refine ⟨(P⁻¹ * X * P)⁻¹ * k * (P⁻¹ * X * P), (hh _).2 hk', ?_⟩
    change P * ((P⁻¹ * X * P)⁻¹ * k * (P⁻¹ * X * P)) * P⁻¹ = y
    have hk'' : P * ((P⁻¹ * X * P)⁻¹ * k * (P⁻¹ * X * P)) * P⁻¹ =
        X⁻¹ * (P * k * P⁻¹) * X := by group
    rw [hk'']
    have h1 : P * k * P⁻¹ = X * y * X⁻¹ := hky
    rw [h1]; group

private theorem e6a3xb_conj_mem_familyCentralizer
    (x : EC)
    (hx : x ∈ Subgroup.centralizer ({wOmegaE} : Set EC)) :
    e6a3_P⁻¹ * e6a3_baseChange x * e6a3_P ∈
      CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer .E6 F4 e6a3xb_fam := by
  have hX : e6a3_baseChange x * e6a3_wF = e6a3_wF * e6a3_baseChange x := by
    have hxw : x * wOmegaE = wOmegaE * x := Subgroup.mem_centralizer_singleton_iff.1 hx
    have h1 : e6a3_baseChange (x * wOmegaE) = e6a3_baseChange (wOmegaE * x) := by rw [hxw]
    rw [map_mul, map_mul] at h1
    rwa [show e6a3_baseChange wOmegaE = e6a3_wF from rfl] at h1
  rw [CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer]
  refine ⟨mul_mem (mul_mem (inv_mem e6a3xb_P_mem)
    (baseChangeGL_mem_adjointGroup (f := e6a3_iota) x.2)) e6a3xb_P_mem, ?_⟩
  intro i
  fin_cases i
  show rootDiagUnit .E6 (e6a3xb_fam 0) * (e6a3_P⁻¹ * e6a3_baseChange x * e6a3_P) *
      (rootDiagUnit .E6 (e6a3xb_fam 0))⁻¹ = e6a3_P⁻¹ * e6a3_baseChange x * e6a3_P
  rw [show e6a3xb_fam 0 = e6a3_dChar from rfl, ← e6a3_d_eq_rootDiagUnit,
    show e6a3_d = e6a3_P⁻¹ * e6a3_wF * e6a3_P from e6a3_P_conj_w.symm]
  have hconj : e6a3_wF * e6a3_baseChange x * e6a3_wF⁻¹ = e6a3_baseChange x := by
    rw [hX.symm]; group
  rw [show (e6a3_P⁻¹ * e6a3_wF * e6a3_P) * (e6a3_P⁻¹ * e6a3_baseChange x * e6a3_P) *
      (e6a3_P⁻¹ * e6a3_wF * e6a3_P)⁻¹ =
        e6a3_P⁻¹ * (e6a3_wF * e6a3_baseChange x * e6a3_wF⁻¹) * e6a3_P from by group,
    hconj]

private theorem e6a3xb_f2_cases (a : F2) : a = 0 ∨ a = 1 := by
  have hcard : Nat.card F2 = 2 := by
    simpa using GaloisField.card 2 1 (by omega)
  by_cases hz : a = 0
  · exact Or.inl hz
  · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
    exact Or.inr ((huniq a hz).trans (huniq 1 one_ne_zero).symm)

private theorem e6a3xb_F_baseChange
    (x : EC) :
    e6a3_F (e6a3_baseChange x) = e6a3_baseChange x := by
  have hiota : (frobenius F4 2).comp e6a3_iota = e6a3_iota := by
    ext a
    rcases e6a3xb_f2_cases a with rfl | rfl <;> simp [frobenius_def]
  have h := baseChangeGL_baseChangeGL (τ := .E6) (f := e6a3_iota) (f' := frobenius F4 2)
    (g := (adjointGroup .E6 F2).subtype x)
  rw [hiota] at h
  simpa [e6a3_F, e6a3_baseChange] using h

private theorem e6a3xb_F_conj
    (x : EC) :
    e6a3_F (e6a3_P⁻¹ * e6a3_baseChange x * e6a3_P) =
      e6a3_nu⁻¹ * (e6a3_P⁻¹ * e6a3_baseChange x * e6a3_P) * e6a3_nu := by
  have hX : e6a3_F (e6a3_baseChange x) = e6a3_baseChange x := e6a3xb_F_baseChange x
  have hP : e6a3_F e6a3_P = e6a3_P * e6a3_nu := by
    calc e6a3_F e6a3_P = e6a3_P * (e6a3_P⁻¹ * e6a3_F e6a3_P) := by group
      _ = e6a3_P * e6a3_nu := by rw [e6a3_P_frob_conj]
  rw [map_mul, map_mul, map_inv, hX, hP]
  group

private theorem e6a3xb_conj_H
    (x : EC)
    (hx : x ∈ Subgroup.centralizer ({wOmegaE} : Set EC)) :
    (e6a3_H).map (MulAut.conj x).toMonoidHom = e6a3_H := by
  have hg := e6a3xb_conj_mem_familyCentralizer x hx
  have hF := e6a3xb_F_conj x
  have hgN := e6a3xb_descent_normalizes _ hg hF
  have hX := e6a3xb_conj_normalizer_map hgN
  apply le_antisymm
  · rintro z ⟨y, hy, rfl⟩
    change e6a3_baseChange y ∈ Subgroup.map (MulAut.conj e6a3_P).toMonoidHom e6a3_GS at hy
    change e6a3_baseChange (x * y * x⁻¹) ∈
      Subgroup.map (MulAut.conj e6a3_P).toMonoidHom e6a3_GS
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hX (e6a3_baseChange y)).1 hy
  · intro z hz
    change e6a3_baseChange z ∈ Subgroup.map (MulAut.conj e6a3_P).toMonoidHom e6a3_GS at hz
    refine ⟨x⁻¹ * z * x, ?_, by show x * (x⁻¹ * z * x) * x⁻¹ = z; group⟩
    change e6a3_baseChange (x⁻¹ * z * x) ∈
      Subgroup.map (MulAut.conj e6a3_P).toMonoidHom e6a3_GS
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (inv_mem hX) (e6a3_baseChange z)).1 hz

private theorem e6a3_step3 :
    Subgroup.centralizer ({wOmegaE} : Set EC) ≤ Subgroup.normalizer (e6a3_H : Set EC) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have hH := congrArg SetLike.coe (e6a3xb_conj_H x hx)
  rwa [Subgroup.coe_map] at hH

private noncomputable def e6a3xc_Phi :
    Matrix.SpecialLinearGroup (Fin 6) F4 →* ModGL .E6 F4 :=
  (adjointGroup .E6 F4).subtype.comp (E6Pilot.slToAdjointE6 F4)

private noncomputable def e6a3xc_M : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F4) :=
  Subgroup.closure {g | (∃ i j : Fin 6, ∃ hij : i ≠ j, (i : ℕ) % 2 = (j : ℕ) % 2 ∧
      ∃ c : F4, Matrix.SpecialLinearGroup.transvection hij c = g) ∨
    g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F4)}

private noncomputable def e6a3xc_P' : Matrix.SpecialLinearGroup (Fin 6) F4 :=
  (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 0 by decide) (e6a3_omega : F4) *
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) (1 : F4)) *
    (Matrix.SpecialLinearGroup.transvection (show (3 : Fin 6) ≠ 2 by decide) (e6a3_omega : F4) *
      Matrix.SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 3 by decide) (1 : F4)) *
    (Matrix.SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 4 by decide) (e6a3_omega : F4) *
      Matrix.SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) (1 : F4))

private noncomputable def e6a3xc_MP : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F4) :=
  e6a3xc_M.map (MulAut.conj e6a3xc_P').toMonoidHom

private lemma e6a3xc_a5Root_10 : a5Root (1 : Fin 6) (0 : Fin 6) = -e6a3_alpha e6a3_i0 := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_01 : a5Root (0 : Fin 6) (1 : Fin 6) = e6a3_alpha e6a3_i0 := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_32 : a5Root (3 : Fin 6) (2 : Fin 6) = -e6a3_alpha e6a3_i3 := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_23 : a5Root (2 : Fin 6) (3 : Fin 6) = e6a3_alpha e6a3_i3 := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_54 : a5Root (5 : Fin 6) (4 : Fin 6) = -e6a3_alpha e6a3_i5 := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_45 : a5Root (4 : Fin 6) (5 : Fin 6) = e6a3_alpha e6a3_i5 := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_13 : a5Root (1 : Fin 6) (3 : Fin 6) = ![0, 0, 1, 1, 0, 0] := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_35 : a5Root (3 : Fin 6) (5 : Fin 6) = ![0, 0, 0, 0, 1, 1] := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_15 : a5Root (1 : Fin 6) (5 : Fin 6) = ![0, 0, 1, 1, 1, 1] := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_02 : a5Root (0 : Fin 6) (2 : Fin 6) = ![1, 0, 1, 0, 0, 0] := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_24 : a5Root (2 : Fin 6) (4 : Fin 6) = ![0, 0, 0, 1, 1, 0] := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_04 : a5Root (0 : Fin 6) (4 : Fin 6) = ![1, 0, 1, 1, 1, 0] := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_31 : a5Root (3 : Fin 6) (1 : Fin 6) = -![0, 0, 1, 1, 0, 0] := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_53 : a5Root (5 : Fin 6) (3 : Fin 6) = -![0, 0, 0, 0, 1, 1] := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_51 : a5Root (5 : Fin 6) (1 : Fin 6) = -![0, 0, 1, 1, 1, 1] := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_20 : a5Root (2 : Fin 6) (0 : Fin 6) = -![1, 0, 1, 0, 0, 0] := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_42 : a5Root (4 : Fin 6) (2 : Fin 6) = -![0, 0, 0, 1, 1, 0] := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_40 : a5Root (4 : Fin 6) (0 : Fin 6) = -![1, 0, 1, 1, 1, 0] := by
  funext m
  fin_cases m <;> decide

private lemma e6a3xc_a5Root_mem_S {i j : Fin 6} (hij : i ≠ j)
    (hpar : (i : ℕ) % 2 = (j : ℕ) % 2) : a5Root i j ∈ e6a3_S := by
  fin_cases i <;> fin_cases j <;>
    (simp only [e6a3_S, e6a3_A, e6a3_C, e6a3_component, Set.mem_union, Set.mem_setOf_eq,
      List.mem_cons, List.not_mem_nil, or_false]) <;>
    first
      | exact absurd rfl hij
      | exact absurd hpar (by decide)
      | decide

private lemma e6a3xc_exists_of_mem_S {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ ∈ e6a3_S) :
    ∃ i j : Fin 6, i ≠ j ∧ (i : ℕ) % 2 = (j : ℕ) % 2 ∧ a5Root i j = γ := by
  simp only [e6a3_S, e6a3_A, e6a3_C, e6a3_component, Set.mem_union, Set.mem_setOf_eq] at hγ
  rcases hγ with (h | h) | (h | h)
  · obtain ⟨n, hn⟩ := List.mem_iff_get.mp h
    fin_cases n
    · exact ⟨1, 3, by decide, by decide, e6a3xc_a5Root_13.trans hn⟩
    · exact ⟨3, 5, by decide, by decide, e6a3xc_a5Root_35.trans hn⟩
    · exact ⟨1, 5, by decide, by decide, e6a3xc_a5Root_15.trans hn⟩
  · obtain ⟨n, hn⟩ := List.mem_iff_get.mp h
    fin_cases n
    · exact ⟨3, 1, by decide, by decide,
        e6a3xc_a5Root_31.trans (neg_eq_iff_eq_neg.mpr hn)⟩
    · exact ⟨5, 3, by decide, by decide,
        e6a3xc_a5Root_53.trans (neg_eq_iff_eq_neg.mpr hn)⟩
    · exact ⟨5, 1, by decide, by decide,
        e6a3xc_a5Root_51.trans (neg_eq_iff_eq_neg.mpr hn)⟩
  · obtain ⟨n, hn⟩ := List.mem_iff_get.mp h
    fin_cases n
    · exact ⟨0, 2, by decide, by decide, e6a3xc_a5Root_02.trans hn⟩
    · exact ⟨2, 4, by decide, by decide, e6a3xc_a5Root_24.trans hn⟩
    · exact ⟨0, 4, by decide, by decide, e6a3xc_a5Root_04.trans hn⟩
  · obtain ⟨n, hn⟩ := List.mem_iff_get.mp h
    fin_cases n
    · exact ⟨2, 0, by decide, by decide,
        e6a3xc_a5Root_20.trans (neg_eq_iff_eq_neg.mpr hn)⟩
    · exact ⟨4, 2, by decide, by decide,
        e6a3xc_a5Root_42.trans (neg_eq_iff_eq_neg.mpr hn)⟩
    · exact ⟨4, 0, by decide, by decide,
        e6a3xc_a5Root_40.trans (neg_eq_iff_eq_neg.mpr hn)⟩

private lemma e6a3xc_Phi_transvection
    {i j : Fin 6} (hij : i ≠ j) (c : F4) :
    e6a3xc_Phi (Matrix.SpecialLinearGroup.transvection hij c) =
      pinnedX .E6 F4 (a5Root i j) c := by
  rw [e6a3xc_Phi, MonoidHom.comp_apply, E6Pilot.slToAdjointE6_transvection]
  rfl

private theorem e6a3xc_P_eq :
    e6a3xc_Phi e6a3xc_P' = e6a3_P := by
  simp only [e6a3xc_P', e6a3_P, e6a3_P0, map_mul]
  rw [e6a3xc_Phi_transvection, e6a3xc_Phi_transvection, e6a3xc_Phi_transvection,
    e6a3xc_Phi_transvection, e6a3xc_Phi_transvection, e6a3xc_Phi_transvection,
    e6a3xc_a5Root_10, e6a3xc_a5Root_01, e6a3xc_a5Root_32, e6a3xc_a5Root_23,
    e6a3xc_a5Root_54, e6a3xc_a5Root_45]

private theorem e6a3xc_GS_eq :
    e6a3xc_M.map e6a3xc_Phi = e6a3_GS := by
  refine le_antisymm ?_ ?_
  · rw [e6a3xc_M, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨i, j, hij, hpar, c, rfl⟩ | hx
    · rw [e6a3xc_Phi_transvection]
      exact pinnedX_mem_rootSpan (S := e6a3_S) (e6a3xc_a5Root_mem_S hij hpar) c
    · have hx1 : x ∈ (E6Pilot.slToAdjointE6 F4).ker := by
        rwa [E6Pilot.ker_slToAdjointE6]
      rw [show e6a3xc_Phi x = 1 by
        rw [e6a3xc_Phi, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx1]
        rfl]
      exact e6a3_GS.one_mem
  · rw [e6a3_GS]
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    obtain ⟨i, j, hij, hpar, rfl⟩ := e6a3xc_exists_of_mem_S hγ
    rw [← e6a3xc_Phi_transvection hij c]
    exact Subgroup.mem_map_of_mem e6a3xc_Phi
      (Subgroup.subset_closure (Or.inl ⟨i, j, hij, hpar, c, rfl⟩))

private theorem e6a3xc_map_MP :
    e6a3xc_MP.map e6a3xc_Phi = e6a3_GS.map (MulAut.conj e6a3_P).toMonoidHom := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨m₀, hm₀, rfl⟩ := hm
    refine ⟨e6a3xc_Phi m₀, ?_, ?_⟩
    · rw [← e6a3xc_GS_eq]
      exact Subgroup.mem_map_of_mem e6a3xc_Phi hm₀
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [map_mul, map_mul, map_inv, e6a3xc_P_eq]
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := hx
    rw [← e6a3xc_GS_eq] at hg
    obtain ⟨m₀, hm₀, rfl⟩ := hg
    refine ⟨e6a3xc_P' * m₀ * e6a3xc_P'⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem (MulAut.conj e6a3xc_P').toMonoidHom hm₀
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [map_mul, map_mul, map_inv, e6a3xc_P_eq]

private theorem e6a3xc_ker_le :
    (E6Pilot.slToAdjointE6 F4).ker ≤ e6a3xc_MP := by
  rw [E6Pilot.ker_slToAdjointE6]
  intro z hz
  refine ⟨z, Subgroup.subset_closure (Or.inr hz), ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_assoc,
    ((Subgroup.mem_center_iff.mp hz) e6a3xc_P'⁻¹).symm, ← mul_assoc, mul_inv_cancel, one_mul]

private theorem e6a3xc_Phi_MP
    (y : Matrix.SpecialLinearGroup (Fin 6) F4) :
    e6a3xc_Phi y ∈ e6a3_GS.map (MulAut.conj e6a3_P).toMonoidHom ↔ y ∈ e6a3xc_MP := by
  rw [← e6a3xc_map_MP]
  constructor
  · rintro ⟨m, hm, hmy⟩
    have hy : m⁻¹ * y ∈ (E6Pilot.slToAdjointE6 F4).ker := by
      rw [MonoidHom.mem_ker]
      apply (adjointGroup .E6 F4).subtype_injective
      change e6a3xc_Phi (m⁻¹ * y) = 1
      rw [map_mul, map_inv, hmy, inv_mul_cancel]
    have hk := e6a3xc_ker_le hy
    rw [← mul_inv_cancel_left m y]
    exact mul_mem hm hk
  · intro hy
    exact ⟨y, hy, rfl⟩

private theorem e6a3xd1_frob_involutive (z : F4) :
    frobenius F4 2 (frobenius F4 2 z) = z := by
  haveI : Fintype F4 := Fintype.ofFinite F4
  have hcard : Fintype.card F4 = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h := FiniteField.pow_card (K := F4) z
  rw [hcard] at h
  have h4 : (2 : ℕ) * 2 = 4 := by norm_num
  rw [frobenius_def, frobenius_def, ← pow_mul, h4]
  exact h

private theorem e6a3xd1_frob_eq_self_iff (z : F4) :
    frobenius F4 2 z = z ↔ z ∈ Set.range e6a3_iota := by
  constructor
  · intro hz
    rcases f4_cases z with rfl | rfl | hω | hω
    · exact ⟨0, map_zero _⟩
    · exact ⟨1, map_one _⟩
    · exfalso
      have h2 : f4Omega ^ 2 = f4Omega := by
        have h := hz
        rw [hω, frobenius_def] at h
        exact h
      have hsq := f4Omega_sq
      rw [h2] at hsq
      rw [CharTwo.add_self_eq_zero] at hsq
      exact (one_ne_zero : (1 : F4) ≠ 0) (by simpa using hsq)
    · exfalso
      have h2 : (f4Omega ^ 2) ^ 2 = f4Omega ^ 2 := by
        have h := hz
        rw [hω, frobenius_def] at h
        exact h
      have hω4 : f4Omega ^ 4 = f4Omega := by
        rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, f4Omega_pow_three, one_mul]
      have hh : (f4Omega ^ 2) ^ 2 = f4Omega := by
        rw [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num, hω4]
      have h3 : f4Omega ^ 2 = f4Omega := h2.symm.trans hh
      have hsq := f4Omega_sq
      rw [h3] at hsq
      rw [CharTwo.add_self_eq_zero] at hsq
      exact (one_ne_zero : (1 : F4) ≠ 0) (by simpa using hsq)
  · rintro ⟨a, rfl⟩
    haveI : Fintype F2 := Fintype.ofFinite F2
    have hcard : Fintype.card F2 = 2 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num)]
      norm_num
    have ha : a ^ 2 = a := by
      have h := FiniteField.pow_card (K := F2) a
      rwa [hcard] at h
    rw [frobenius_def, ← map_pow, ha]

private theorem e6a3xc_descent
    (x : EC) (hx : e6a3_baseChange x ∈ e6a3_GS.map (MulAut.conj e6a3_P).toMonoidHom) :
    x ∈ E6Pilot.a5Levi F2 := by
  rw [← e6a3xc_map_MP] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hcomp : (frobenius F4 2).comp e6a3_iota = e6a3_iota :=
    RingHom.ext fun a => (e6a3xd1_frob_eq_self_iff (e6a3_iota a)).2 ⟨a, rfl⟩
  have hσd : baseChangeGL (frobenius F4 2) (e6a3_baseChange x) = e6a3_baseChange x := by
    rw [e6a3_baseChange, MonoidHom.comp_apply, F4Pilot.baseChangeGL_baseChangeGL, hcomp]
  have hd : e6a3_baseChange x ∈ rootSpan .E6 F4 E6Pilot.a5LeviRoots := by
    rw [← hyx]
    exact E6Pilot.mem_a5Levi_iff.1 (E6Pilot.slToAdjointE6_mem_a5Levi y)
  obtain ⟨d₀, hd₀mem, hd₀eq⟩ :=
    E6Pilot.exists_baseChangeGL_eq_of_mem_rootSpan_a5LeviRoots e6a3_iota (frobenius F4 2)
      e6a3xd1_frob_eq_self_iff e6a3xd1_frob_involutive hd hσd
  have hxd : d₀ = (x : ModGL .E6 F2) := by
    apply baseChangeGL_injective e6a3_iota
    rw [hd₀eq]
    rfl
  rw [E6Pilot.mem_a5Levi_iff, ← hxd]
  exact hd₀mem

private theorem e6a3xd2_omega_sq : (f4Omega : F4) ^ 2 = f4Omega + 1 := by
  have h : f4Omega ^ 2 + (f4Omega + 1) = 0 := by
    rw [← add_assoc]; exact f4Omega_sq
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
  exact h

private theorem e6a3xd2_omega_four : (f4Omega : F4) ^ 4 = f4Omega := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, f4Omega_pow_three, one_mul]

private noncomputable def e6a3xd2_B0 : Matrix (Fin 2) (Fin 2) F4 := !![1, 1; f4Omega, f4Omega ^ 2]

private noncomputable def e6a3xd2_B0inv : Matrix (Fin 2) (Fin 2) F4 :=
  !![f4Omega ^ 2, 1; f4Omega, 1]

private noncomputable def e6a3xd2_eps : F4 →+* Matrix (Fin 2) (Fin 2) F4 :=
  (RingHom.mapMatrix e6a3_iota).comp f4Eps

private theorem e6a3xd2_eps_apply (a : F4) :
    e6a3xd2_eps a = e6a3_iota.mapMatrix (f4Eps a) := rfl

private theorem e6a3xd2_eps_omega : e6a3xd2_eps f4Omega = !![0, 1; 1, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [e6a3xd2_eps, f4Eps_omega, RingHom.mapMatrix_apply, RingHom.comp_apply]

private theorem e6a3xd2_eps_omega_sq : e6a3xd2_eps (f4Omega ^ 2) = !![1, 1; 1, 0] := by
  rw [pow_two, map_mul, e6a3xd2_eps_omega]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, CharTwo.add_self_eq_zero]

private theorem e6a3xd2_B0_mul_B0inv : e6a3xd2_B0 * e6a3xd2_B0inv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [e6a3xd2_B0, e6a3xd2_B0inv, Matrix.mul_fin_two, e6a3xd2_omega_sq,
      CharTwo.add_self_eq_zero] <;>
     (ring_nf; simp [CharTwo.two_eq_zero, CharTwo.add_self_eq_zero]))

private theorem e6a3xd2_conj_eps (a : F4) :
    e6a3xd2_B0inv * e6a3xd2_eps a * e6a3xd2_B0 =
      Matrix.diagonal ![a, a ^ 2] := by
  rcases f4_cases a with rfl | rfl | rfl | rfl
  · rw [map_zero]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [e6a3xd2_B0, e6a3xd2_B0inv, Matrix.mul_fin_two, Matrix.diagonal_apply]
  · rw [map_one, Matrix.mul_one]
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp [e6a3xd2_B0, e6a3xd2_B0inv, Matrix.mul_fin_two, Matrix.diagonal_apply] <;>
       first
         | linear_combination (1 : F4) * f4Omega_sq
         | linear_combination (1 : F4) * CharTwo.add_self_eq_zero f4Omega
         | linear_combination (1 : F4) * CharTwo.add_self_eq_zero (1 : F4)
         | linear_combination (1 : F4) * f4Omega_sq + f4Omega * f4Omega_pow_three
         | linear_combination (1 : F4) * f4Omega_sq + f4Omega * f4Omega_pow_three +
             (1 : F4) * CharTwo.add_self_eq_zero f4Omega
         | linear_combination (1 : F4) * f4Omega_sq + f4Omega * f4Omega_pow_three +
             (1 : F4) * CharTwo.add_self_eq_zero (1 : F4)
         | linear_combination (1 : F4) * f4Omega_sq +
             (1 : F4) * CharTwo.add_self_eq_zero f4Omega +
             (1 : F4) * CharTwo.add_self_eq_zero (1 : F4)
         | (ring_nf; simp [e6a3xd2_omega_sq, f4Omega_pow_three, e6a3xd2_omega_four, pow_succ,
             CharTwo.two_eq_zero, CharTwo.add_self_eq_zero] <;>
            (ring_nf; simp [CharTwo.two_eq_zero, CharTwo.add_self_eq_zero])))
  · rw [e6a3xd2_eps_omega]
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp [e6a3xd2_B0, e6a3xd2_B0inv, Matrix.mul_fin_two, Matrix.diagonal_apply] <;>
       first
         | linear_combination (1 : F4) * f4Omega_sq
         | linear_combination (1 : F4) * CharTwo.add_self_eq_zero f4Omega
         | linear_combination (1 : F4) * CharTwo.add_self_eq_zero (1 : F4)
         | linear_combination (1 : F4) * f4Omega_sq + f4Omega * f4Omega_pow_three
         | linear_combination (1 : F4) * f4Omega_sq + f4Omega * f4Omega_pow_three +
             (1 : F4) * CharTwo.add_self_eq_zero f4Omega
         | linear_combination (1 : F4) * f4Omega_sq + f4Omega * f4Omega_pow_three +
             (1 : F4) * CharTwo.add_self_eq_zero (1 : F4)
         | linear_combination (1 : F4) * f4Omega_sq +
             (1 : F4) * CharTwo.add_self_eq_zero f4Omega +
             (1 : F4) * CharTwo.add_self_eq_zero (1 : F4)
         | (ring_nf; simp [e6a3xd2_omega_sq, f4Omega_pow_three, e6a3xd2_omega_four, pow_succ,
             CharTwo.two_eq_zero, CharTwo.add_self_eq_zero] <;>
            (ring_nf; simp [CharTwo.two_eq_zero, CharTwo.add_self_eq_zero])))
  · rw [e6a3xd2_eps_omega_sq]
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp [e6a3xd2_B0, e6a3xd2_B0inv, Matrix.mul_fin_two, Matrix.diagonal_apply] <;>
       first
         | linear_combination (1 : F4) * f4Omega_sq
         | linear_combination (1 : F4) * CharTwo.add_self_eq_zero f4Omega
         | linear_combination (1 : F4) * CharTwo.add_self_eq_zero (1 : F4)
         | linear_combination (1 : F4) * f4Omega_sq + f4Omega * f4Omega_pow_three
         | linear_combination (1 : F4) * f4Omega_sq + f4Omega * f4Omega_pow_three +
             (1 : F4) * CharTwo.add_self_eq_zero f4Omega
         | linear_combination (1 : F4) * f4Omega_sq + f4Omega * f4Omega_pow_three +
             (1 : F4) * CharTwo.add_self_eq_zero (1 : F4)
         | linear_combination (1 : F4) * f4Omega_sq +
             (1 : F4) * CharTwo.add_self_eq_zero f4Omega +
             (1 : F4) * CharTwo.add_self_eq_zero (1 : F4)
         | (ring_nf; simp [e6a3xd2_omega_sq, f4Omega_pow_three, e6a3xd2_omega_four, pow_succ,
             CharTwo.two_eq_zero, CharTwo.add_self_eq_zero] <;>
            (ring_nf; simp [CharTwo.two_eq_zero, CharTwo.add_self_eq_zero])))

private theorem e6a3xd2_eps_mul_B0 (a : F4) :
    e6a3xd2_eps a * e6a3xd2_B0 = e6a3xd2_B0 * Matrix.diagonal ![a, a ^ 2] := by
  rw [← e6a3xd2_conj_eps a, ← mul_assoc, ← mul_assoc, e6a3xd2_B0_mul_B0inv, one_mul]

private noncomputable def e6a3xd2_P2 : Matrix (Fin 6) (Fin 6) F4 :=
  fun i j => if i.val / 2 = j.val / 2 then
    e6a3xd2_B0 ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ ⟨j.val % 2, Nat.mod_lt _ (by decide)⟩
    else 0

private theorem e6a3xd2_P'_row0 (j : Fin 6) :
    (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) 0 j = e6a3xd2_P2 0 j := by
  fin_cases j <;> simp [e6a3xc_P', e6a3xd2_P2, e6a3xd2_B0,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_six,
    e6a3_omega, e6a3xd2_omega_sq, CharTwo.add_self_eq_zero]
private theorem e6a3xd2_P'_row1 (j : Fin 6) :
    (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) 1 j = e6a3xd2_P2 1 j := by
  fin_cases j <;> simp [e6a3xc_P', e6a3xd2_P2, e6a3xd2_B0,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_six,
    e6a3_omega, e6a3xd2_omega_sq, CharTwo.add_self_eq_zero]
private theorem e6a3xd2_P'_row2 (j : Fin 6) :
    (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) 2 j = e6a3xd2_P2 2 j := by
  fin_cases j <;> simp [e6a3xc_P', e6a3xd2_P2, e6a3xd2_B0,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_six,
    e6a3_omega, e6a3xd2_omega_sq, CharTwo.add_self_eq_zero]
private theorem e6a3xd2_P'_row3 (j : Fin 6) :
    (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) 3 j = e6a3xd2_P2 3 j := by
  fin_cases j <;> simp [e6a3xc_P', e6a3xd2_P2, e6a3xd2_B0,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_six,
    e6a3_omega, e6a3xd2_omega_sq, CharTwo.add_self_eq_zero]
private theorem e6a3xd2_P'_row4 (j : Fin 6) :
    (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) 4 j = e6a3xd2_P2 4 j := by
  fin_cases j <;> simp [e6a3xc_P', e6a3xd2_P2, e6a3xd2_B0,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_six,
    e6a3_omega, e6a3xd2_omega_sq, CharTwo.add_self_eq_zero]
private theorem e6a3xd2_P'_row5 (j : Fin 6) :
    (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) 5 j = e6a3xd2_P2 5 j := by
  fin_cases j <;> simp [e6a3xc_P', e6a3xd2_P2, e6a3xd2_B0,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_six,
    e6a3_omega, e6a3xd2_omega_sq, CharTwo.add_self_eq_zero]

private theorem e6a3xd2_P'_eq_P2 : (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) = e6a3xd2_P2 := by
  ext i j
  fin_cases i
  · exact e6a3xd2_P'_row0 j
  · exact e6a3xd2_P'_row1 j
  · exact e6a3xd2_P'_row2 j
  · exact e6a3xd2_P'_row3 j
  · exact e6a3xd2_P'_row4 j
  · exact e6a3xd2_P'_row5 j

private noncomputable def e6a3xd2_blk (X Y : Matrix (Fin 3) (Fin 3) F4) :
    Matrix (Fin 6) (Fin 6) F4 :=
  fun i j => if i.val % 2 = j.val % 2 then
    (if i.val % 2 = 0 then X ⟨i.val / 2, by omega⟩ ⟨j.val / 2, by omega⟩
     else Y ⟨i.val / 2, by omega⟩ ⟨j.val / 2, by omega⟩) else 0

private noncomputable def e6a3xd2_resF4 (X : Matrix (Fin 3) (Fin 3) F4) :
    Matrix (Fin 6) (Fin 6) F4 :=
  e6a3_iota.mapMatrix (resMat 3 X)

private theorem e6a3xd2_divmod (i : Fin 6) :
    finProdFinEquiv ((⟨i.val / 2, by omega⟩ : Fin 3),
      (⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2)) = i := by
  fin_cases i <;> rfl

private theorem e6a3xd2_resF4_apply (X : Matrix (Fin 3) (Fin 3) F4) (i j : Fin 6) :
    e6a3xd2_resF4 X i j = e6a3xd2_eps (X ⟨i.val / 2, by omega⟩ ⟨j.val / 2, by omega⟩)
      ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ ⟨j.val % 2, Nat.mod_lt _ (by decide)⟩ := by
  have h : resMat 3 X i j = f4Eps (X ⟨i.val / 2, by omega⟩ ⟨j.val / 2, by omega⟩)
      ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ ⟨j.val % 2, Nat.mod_lt _ (by decide)⟩ := by
    have := resMat_apply 3 X (⟨i.val / 2, by omega⟩ : Fin 3) (⟨j.val / 2, by omega⟩ : Fin 3)
      (⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2)
      (⟨j.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2)
    rwa [e6a3xd2_divmod i, e6a3xd2_divmod j] at this
  rw [e6a3xd2_resF4, RingHom.mapMatrix_apply, e6a3xd2_eps_apply, RingHom.mapMatrix_apply]
  exact congrArg e6a3_iota h

private theorem e6a3xd2_B0_diag_apply (a : F4) (r r' : Fin 2) :
    (e6a3xd2_B0 * Matrix.diagonal ![a, a ^ 2]) r r' =
      (e6a3xd2_eps a * e6a3xd2_B0) r r' := by
  rw [← e6a3xd2_eps_mul_B0]

private theorem e6a3xd2_B0_diag_00 (a : F4) :
    e6a3xd2_B0 0 0 * a =
      e6a3xd2_eps a 0 0 * e6a3xd2_B0 0 0 + e6a3xd2_eps a 0 1 * e6a3xd2_B0 1 0 := by
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
    using e6a3xd2_B0_diag_apply a 0 0
private theorem e6a3xd2_B0_diag_01 (a : F4) :
    e6a3xd2_B0 0 1 * a ^ 2 =
      e6a3xd2_eps a 0 0 * e6a3xd2_B0 0 1 + e6a3xd2_eps a 0 1 * e6a3xd2_B0 1 1 := by
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
    using e6a3xd2_B0_diag_apply a 0 1
private theorem e6a3xd2_B0_diag_10 (a : F4) :
    e6a3xd2_B0 1 0 * a =
      e6a3xd2_eps a 1 0 * e6a3xd2_B0 0 0 + e6a3xd2_eps a 1 1 * e6a3xd2_B0 1 0 := by
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
    using e6a3xd2_B0_diag_apply a 1 0
private theorem e6a3xd2_B0_diag_11 (a : F4) :
    e6a3xd2_B0 1 1 * a ^ 2 =
      e6a3xd2_eps a 1 0 * e6a3xd2_B0 0 1 + e6a3xd2_eps a 1 1 * e6a3xd2_B0 1 1 := by
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
    using e6a3xd2_B0_diag_apply a 1 1

private theorem e6a3xd2_conj (X : Matrix (Fin 3) (Fin 3) F4) :
    (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) *
        e6a3xd2_blk X (X.map (fun a => a ^ 2)) =
      e6a3xd2_resF4 X * (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) := by
  rw [e6a3xd2_P'_eq_P2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.mul_apply, Fin.sum_univ_six, e6a3xd2_P2, e6a3xd2_blk,
      e6a3xd2_resF4_apply] <;> norm_num)
  all_goals
    first
      | exact e6a3xd2_B0_diag_00 _
      | exact e6a3xd2_B0_diag_01 _
      | exact e6a3xd2_B0_diag_10 _
      | exact e6a3xd2_B0_diag_11 _

private def e6a3xd2_sig : Fin 3 ⊕ Fin 3 → Fin 6
  | Sum.inl k => ⟨2 * k.val, by omega⟩
  | Sum.inr k => ⟨2 * k.val + 1, by omega⟩

private noncomputable def e6a3xd2_σ : Fin 3 ⊕ Fin 3 ≃ Fin 6 where
  toFun := e6a3xd2_sig
  invFun i := if i.val % 2 = 0 then Sum.inl ⟨i.val / 2, by omega⟩
    else Sum.inr ⟨i.val / 2, by omega⟩
  left_inv := by rintro (k | k) <;> fin_cases k <;> decide
  right_inv := by intro i; fin_cases i <;> decide

private theorem e6a3xd2_σ_inl (k : Fin 3) :
    e6a3xd2_σ (Sum.inl k) = ⟨2 * k.val, by omega⟩ := rfl
private theorem e6a3xd2_σ_inr (k : Fin 3) :
    e6a3xd2_σ (Sum.inr k) = ⟨2 * k.val + 1, by omega⟩ := rfl

private noncomputable def e6a3xd2_re :
    Matrix (Fin 6) (Fin 6) F4 ≃+* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F4 :=
  (Matrix.reindexAlgEquiv F4 F4 e6a3xd2_σ).symm

private theorem e6a3xd2_re_symm (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F4) :
    e6a3xd2_re.symm M = Matrix.reindexAlgEquiv F4 F4 e6a3xd2_σ M := by
  simp [e6a3xd2_re]

private theorem e6a3xd2_re_apply (g : Matrix (Fin 6) (Fin 6) F4) (i j : Fin 3 ⊕ Fin 3) :
    e6a3xd2_re g i j = g (e6a3xd2_σ i) (e6a3xd2_σ j) := by
  simp [e6a3xd2_re, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm]

private noncomputable def e6a3xd2_ev (g : Matrix (Fin 6) (Fin 6) F4) : Matrix (Fin 3) (Fin 3) F4 :=
  (e6a3xd2_re g).toBlocks₁₁

private theorem e6a3xd2_det_bd (A D : Matrix (Fin 3) (Fin 3) F4) (hA : A.det = 1)
    (hD : D.det = 1) : (e6a3xd2_re.symm (Matrix.fromBlocks A 0 0 D)).det = 1 := by
  rw [e6a3xd2_re_symm, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₁₂, hA, hD, mul_one]

private noncomputable def e6a3xd2_BDhom :
    Matrix.SpecialLinearGroup (Fin 3) F4 × Matrix.SpecialLinearGroup (Fin 3) F4 →*
      Matrix.SpecialLinearGroup (Fin 6) F4 where
  toFun p := ⟨e6a3xd2_re.symm (Matrix.fromBlocks (p.1 : Matrix (Fin 3) (Fin 3) F4) 0 0
      (p.2 : Matrix (Fin 3) (Fin 3) F4)), e6a3xd2_det_bd _ _ p.1.2 p.2.2⟩
  map_one' := by
    apply Subtype.ext
    change e6a3xd2_re.symm (Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) F4) 0 0
      (1 : Matrix (Fin 3) (Fin 3) F4)) = (1 : Matrix (Fin 6) (Fin 6) F4)
    rw [Matrix.fromBlocks_one, map_one]
  map_mul' p q := by
    apply Subtype.ext
    change e6a3xd2_re.symm (Matrix.fromBlocks
        (((p.1 * q.1 : Matrix.SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)) 0 0
        (((p.2 * q.2 : Matrix.SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4))) =
      e6a3xd2_re.symm (Matrix.fromBlocks (p.1 : Matrix (Fin 3) (Fin 3) F4) 0 0
          (p.2 : Matrix (Fin 3) (Fin 3) F4)) *
        e6a3xd2_re.symm (Matrix.fromBlocks (q.1 : Matrix (Fin 3) (Fin 3) F4) 0 0
          (q.2 : Matrix (Fin 3) (Fin 3) F4))
    rw [← map_mul, Matrix.fromBlocks_multiply]
    congr 1
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul]

private theorem e6a3xd2_two_ne (k k' : Fin 3) (h : k ≠ k') :
    (⟨2 * k.val, by omega⟩ : Fin 6) ≠ ⟨2 * k'.val, by omega⟩ := by
  intro hh
  exact h (Fin.ext (by have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega))

private theorem e6a3xd2_two_add_one_ne (k k' : Fin 3) (h : k ≠ k') :
    (⟨2 * k.val + 1, by omega⟩ : Fin 6) ≠ ⟨2 * k'.val + 1, by omega⟩ := by
  intro hh
  exact h (Fin.ext (by have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega))

private theorem e6a3xd2_re_transvection_even (k k' : Fin 3) (h : k ≠ k') (c : F4) :
    e6a3xd2_re ((Matrix.SpecialLinearGroup.transvection
        (e6a3xd2_two_ne k k' h) c :
          Matrix.SpecialLinearGroup (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.fromBlocks ((Matrix.SpecialLinearGroup.transvection h c :
        Matrix.SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) 0 0 1 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [e6a3xd2_re_apply, e6a3xd2_σ_inl, e6a3xd2_σ_inr,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply, Matrix.one_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.of_apply, Matrix.add_apply]
  all_goals
    fin_cases a <;> fin_cases b <;>
      (simp only [Fin.ext_iff] <;> split_ifs <;> simp_all <;> omega)

private theorem e6a3xd2_re_transvection_odd (k k' : Fin 3) (h : k ≠ k') (c : F4) :
    e6a3xd2_re ((Matrix.SpecialLinearGroup.transvection
        (e6a3xd2_two_add_one_ne k k' h) c :
          Matrix.SpecialLinearGroup (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.fromBlocks 1 0 0 ((Matrix.SpecialLinearGroup.transvection h c :
        Matrix.SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [e6a3xd2_re_apply, e6a3xd2_σ_inl, e6a3xd2_σ_inr,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply, Matrix.one_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.of_apply, Matrix.add_apply]
  all_goals
    fin_cases a <;> fin_cases b <;>
      (simp only [Fin.ext_iff] <;> split_ifs <;> simp_all <;> omega)

private theorem e6a3xd2_even_mem (k k' : Fin 3) (h : k ≠ k') (c : F4)
    (hij : (⟨2 * k.val, by omega⟩ : Fin 6) ≠ ⟨2 * k'.val, by omega⟩) :
    (Matrix.SpecialLinearGroup.transvection hij c) ∈ e6a3xd2_BDhom.range := by
  refine ⟨(Matrix.SpecialLinearGroup.transvection h c, 1), ?_⟩
  apply Subtype.ext
  change e6a3xd2_re.symm (Matrix.fromBlocks
      (Matrix.SpecialLinearGroup.transvection h c : Matrix (Fin 3) (Fin 3) F4) 0 0 1) =
    (Matrix.SpecialLinearGroup.transvection hij c : Matrix (Fin 6) (Fin 6) F4)
  rw [← e6a3xd2_re_transvection_even k k' h c, RingEquiv.symm_apply_apply]

private theorem e6a3xd2_odd_mem (k k' : Fin 3) (h : k ≠ k') (c : F4)
    (hij : (⟨2 * k.val + 1, by omega⟩ : Fin 6) ≠ ⟨2 * k'.val + 1, by omega⟩) :
    (Matrix.SpecialLinearGroup.transvection hij c) ∈ e6a3xd2_BDhom.range := by
  refine ⟨(1, Matrix.SpecialLinearGroup.transvection h c), ?_⟩
  apply Subtype.ext
  change e6a3xd2_re.symm (Matrix.fromBlocks 1 0 0
      (Matrix.SpecialLinearGroup.transvection h c : Matrix (Fin 3) (Fin 3) F4)) =
    (Matrix.SpecialLinearGroup.transvection hij c : Matrix (Fin 6) (Fin 6) F4)
  rw [← e6a3xd2_re_transvection_odd k k' h c, RingEquiv.symm_apply_apply]

private theorem e6a3xe1_re_scalar (r : F4) :
    e6a3xd2_re (Matrix.scalar (Fin 6) r) =
      Matrix.fromBlocks (Matrix.scalar (Fin 3) r) 0 0 (Matrix.scalar (Fin 3) r) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [e6a3xd2_re_apply, e6a3xd2_σ_inl, e6a3xd2_σ_inr, Matrix.scalar_apply,
      Matrix.diagonal_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Pi.zero_apply]
  all_goals
    fin_cases a <;> fin_cases b <;>
      (simp only [Fin.ext_iff] <;> split_ifs <;> simp_all <;> omega)

private theorem e6a3xe1_decomp :
    ∀ i j : Fin 6, i ≠ j → (i : ℕ) % 2 = (j : ℕ) % 2 →
      (∃ k k' : Fin 3, k ≠ k' ∧ (⟨2 * k.val, by omega⟩ : Fin 6) = i ∧
          (⟨2 * k'.val, by omega⟩ : Fin 6) = j) ∨
        (∃ k k' : Fin 3, k ≠ k' ∧ (⟨2 * k.val + 1, by omega⟩ : Fin 6) = i ∧
          (⟨2 * k'.val + 1, by omega⟩ : Fin 6) = j) := by
  decide

private theorem e6a3xe1_transvection_mem (i j : Fin 6) (hij : i ≠ j) (c : F4)
    (hpar : (i : ℕ) % 2 = (j : ℕ) % 2) :
    (Matrix.SpecialLinearGroup.transvection hij c) ∈ e6a3xd2_BDhom.range := by
  rcases e6a3xe1_decomp i j hij hpar with ⟨k, k', h, hi, hj⟩ | ⟨k, k', h, hi, hj⟩
  · subst i; subst j
    exact e6a3xd2_even_mem k k' h c hij
  · subst i; subst j
    exact e6a3xd2_odd_mem k k' h c hij

private theorem e6a3xd2_M_le_BD : e6a3xc_M ≤ e6a3xd2_BDhom.range := by
  rw [e6a3xc_M, Subgroup.closure_le]
  rintro g (⟨i, j, hij, hpar, c, rfl⟩ | hg)
  · exact e6a3xe1_transvection_mem i j hij c hpar
  · obtain ⟨r, hr, hscal⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
    have hr6 : r ^ 6 = 1 := by simpa using hr
    have hsq : (r ^ 3) ^ 2 = 1 := by rw [← pow_mul, show 3 * 2 = 6 from rfl]; exact hr6
    have hr3 : r ^ 3 = 1 := by
      rcases sq_eq_one_iff.mp hsq with h | h
      · exact h
      · rwa [CharTwo.neg_eq] at h
    have hdet3 : (Matrix.scalar (Fin 3) r).det = 1 := by
      rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      exact hr3
    refine ⟨(⟨Matrix.scalar (Fin 3) r, hdet3⟩, ⟨Matrix.scalar (Fin 3) r, hdet3⟩), ?_⟩
    apply Subtype.ext
    change e6a3xd2_re.symm (Matrix.fromBlocks (Matrix.scalar (Fin 3) r) 0 0
        (Matrix.scalar (Fin 3) r)) = (g : Matrix (Fin 6) (Fin 6) F4)
    apply e6a3xd2_re.injective
    rw [RingEquiv.apply_symm_apply, ← hscal, e6a3xe1_re_scalar]

private theorem e6a3xd2_det_ev {g : Matrix.SpecialLinearGroup (Fin 6) F4}
    (hg : g ∈ e6a3xd2_BDhom.range) :
    (e6a3xd2_ev (g : Matrix (Fin 6) (Fin 6) F4)).det = 1 := by
  obtain ⟨p, rfl⟩ := hg
  have h : e6a3xd2_re ((e6a3xd2_BDhom p : Matrix.SpecialLinearGroup (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4) =
      Matrix.fromBlocks (p.1 : Matrix (Fin 3) (Fin 3) F4) 0 0
        (p.2 : Matrix (Fin 3) (Fin 3) F4) := by
    change e6a3xd2_re (e6a3xd2_re.symm (Matrix.fromBlocks (p.1 : Matrix (Fin 3) (Fin 3) F4) 0 0
      (p.2 : Matrix (Fin 3) (Fin 3) F4))) = _
    rw [RingEquiv.apply_symm_apply]
  rw [e6a3xd2_ev, h, Matrix.toBlocks_fromBlocks₁₁]
  exact p.1.2

private theorem e6a3xd2_ev_blk (X Y : Matrix (Fin 3) (Fin 3) F4) :
    e6a3xd2_ev (e6a3xd2_blk X Y) = X := by
  ext k k'
  rw [e6a3xd2_ev, Matrix.toBlocks₁₁, Matrix.of_apply, e6a3xd2_re_apply]
  simp [e6a3xd2_blk, e6a3xd2_σ_inl, Nat.mul_mod_right, Nat.mul_div_right]

private theorem e6a3xe2_re_blk (X Y : Matrix (Fin 3) (Fin 3) F4) :
    e6a3xd2_re (e6a3xd2_blk X Y) = Matrix.fromBlocks X 0 0 Y := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
      simp [e6a3xd2_re_apply, e6a3xd2_blk, e6a3xd2_σ_inl, e6a3xd2_σ_inr,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂]

private noncomputable def e6a3xe2_Dmat : Matrix (Fin 6) (Fin 6) F4 :=
  e6a3xd2_blk (Matrix.scalar (Fin 3) f4Omega) (Matrix.scalar (Fin 3) (f4Omega ^ 2))

private theorem e6a3xe2_re_D :
    e6a3xd2_re e6a3xe2_Dmat =
      Matrix.fromBlocks (Matrix.scalar (Fin 3) f4Omega) 0 0
        (Matrix.scalar (Fin 3) (f4Omega ^ 2)) := by
  rw [e6a3xe2_Dmat, e6a3xe2_re_blk]

private theorem e6a3xe2_det_blk (X Y : Matrix (Fin 3) (Fin 3) F4) :
    (e6a3xd2_blk X Y).det = X.det * Y.det := by
  have h : e6a3xd2_blk X Y = e6a3xd2_re.symm (Matrix.fromBlocks X 0 0 Y) := by
    rw [← RingEquiv.symm_apply_apply e6a3xd2_re (e6a3xd2_blk X Y), e6a3xe2_re_blk]
  rw [h, e6a3xd2_re_symm, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₁₂]

private theorem e6a3xe2_det_scalar : (Matrix.scalar (Fin 3) f4Omega).det = 1 := by
  rw [Matrix.scalar_apply, Matrix.det_diagonal]
  simp [f4Omega_pow_three]

private theorem e6a3xe2_det_scalar_sq : (Matrix.scalar (Fin 3) (f4Omega ^ 2)).det = 1 := by
  rw [Matrix.scalar_apply, Matrix.det_diagonal]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, show (2 : ℕ) * 3 = 3 * 2 by norm_num, pow_mul, f4Omega_pow_three, one_pow]

private noncomputable def e6a3xe2_D : Matrix.SpecialLinearGroup (Fin 6) F4 :=
  ⟨e6a3xe2_Dmat, by
    rw [e6a3xe2_Dmat, e6a3xe2_det_blk, e6a3xe2_det_scalar, e6a3xe2_det_scalar_sq, one_mul]⟩

private theorem e6a3xe2_D_coe :
    (e6a3xe2_D : Matrix (Fin 6) (Fin 6) F4) = e6a3xe2_Dmat := rfl

private theorem e6a3xe2_scalar_map :
    (Matrix.scalar (Fin 3) f4Omega).map (fun a => a ^ 2) =
      Matrix.scalar (Fin 3) (f4Omega ^ 2) := by
  ext i j
  by_cases h : i = j <;>
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply, h]

private theorem e6a3xe2_P'_conj_D :
    (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) * e6a3xe2_Dmat =
      e6a3xd2_resF4 (Matrix.scalar (Fin 3) f4Omega) *
        (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) := by
  have h := e6a3xd2_conj (Matrix.scalar (Fin 3) f4Omega)
  rw [e6a3xe2_scalar_map] at h
  simpa [e6a3xe2_Dmat] using h

private theorem e6a3xe2_resF4_scalar :
    e6a3xd2_resF4 (Matrix.scalar (Fin 3) f4Omega) =
      ((Matrix.SpecialLinearGroup.map e6a3_iota zeta5 : Matrix.SpecialLinearGroup (Fin 6) F4) :
        Matrix (Fin 6) (Fin 6) F4) := by
  rw [e6a3xd2_resF4, Matrix.SpecialLinearGroup.map_apply_coe]
  congr 1
  rw [zeta5_eq, coe_resGL]
  congr 1

private theorem e6a3xe2_re_BDhom
    (p : Matrix.SpecialLinearGroup (Fin 3) F4 × Matrix.SpecialLinearGroup (Fin 3) F4) :
    e6a3xd2_re ((e6a3xd2_BDhom p : Matrix.SpecialLinearGroup (Fin 6) F4) :
        Matrix (Fin 6) (Fin 6) F4) =
      Matrix.fromBlocks (p.1 : Matrix (Fin 3) (Fin 3) F4) 0 0
        (p.2 : Matrix (Fin 3) (Fin 3) F4) := by
  change e6a3xd2_re (e6a3xd2_re.symm (Matrix.fromBlocks (p.1 : Matrix (Fin 3) (Fin 3) F4) 0 0
      (p.2 : Matrix (Fin 3) (Fin 3) F4))) = Matrix.fromBlocks (p.1 : Matrix (Fin 3) (Fin 3) F4) 0 0
      (p.2 : Matrix (Fin 3) (Fin 3) F4)
  rw [RingEquiv.apply_symm_apply]

private theorem e6a3xe2_BD_comm_D {m : Matrix.SpecialLinearGroup (Fin 6) F4}
    (hm : m ∈ e6a3xd2_BDhom.range) : m * e6a3xe2_D = e6a3xe2_D * m := by
  obtain ⟨p, rfl⟩ := hm
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  apply e6a3xd2_re.injective
  rw [map_mul, map_mul, e6a3xe2_re_BDhom p, e6a3xe2_D_coe, e6a3xe2_re_D]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [Matrix.fromBlocks_inj]
  refine ⟨(Matrix.scalar_comm f4Omega (fun r' => mul_comm f4Omega r')
      (p.1 : Matrix (Fin 3) (Fin 3) F4)).symm, rfl, rfl,
    (Matrix.scalar_comm (f4Omega ^ 2) (fun r' => mul_comm (f4Omega ^ 2) r')
      (p.2 : Matrix (Fin 3) (Fin 3) F4)).symm⟩

private theorem e6a3xe2_map_iota_injective :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 6) e6a3_iota) := by
  intro A B h
  ext i j
  have h1 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 6) F4 =>
    (M : Matrix (Fin 6) (Fin 6) F4) i j) h
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h1
  exact RingHom.injective e6a3_iota h1

private theorem e6a3xe2_exists_M {y : Matrix.SpecialLinearGroup (Fin 6) F4}
    (hy : y ∈ e6a3xc_MP) :
    ∃ m ∈ e6a3xc_M, y = e6a3xc_P' * m * e6a3xc_P'⁻¹ := by
  rw [e6a3xc_MP] at hy
  obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp hy
  exact ⟨m, hm, by rw [← hmy]; simp [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩

private theorem e6a3xd2_fwd (A : Matrix.SpecialLinearGroup (Fin 6) F2)
    (hA : Matrix.SpecialLinearGroup.map e6a3_iota A ∈ e6a3xc_MP) : A ∈ sl3four := by
  obtain ⟨m, hm, hAeq⟩ := e6a3xe2_exists_M hA
  have hmBD : m ∈ e6a3xd2_BDhom.range := e6a3xd2_M_le_BD hm
  have hmD : m * e6a3xe2_D = e6a3xe2_D * m := e6a3xe2_BD_comm_D hmBD
  have hPD : e6a3xc_P' * e6a3xe2_D =
      Matrix.SpecialLinearGroup.map e6a3_iota zeta5 * e6a3xc_P' := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [← e6a3xe2_resF4_scalar]
    exact e6a3xe2_P'_conj_D
  have hZ : Matrix.SpecialLinearGroup.map e6a3_iota zeta5 =
      e6a3xc_P' * e6a3xe2_D * e6a3xc_P'⁻¹ := by
    rw [hPD]
    group
  have h1 : Matrix.SpecialLinearGroup.map e6a3_iota A *
        Matrix.SpecialLinearGroup.map e6a3_iota zeta5 =
      e6a3xc_P' * (m * e6a3xe2_D) * e6a3xc_P'⁻¹ := by
    rw [hAeq, hZ]
    group
  have h2 : Matrix.SpecialLinearGroup.map e6a3_iota zeta5 *
        Matrix.SpecialLinearGroup.map e6a3_iota A =
      e6a3xc_P' * (m * e6a3xe2_D) * e6a3xc_P'⁻¹ := by
    rw [hAeq, hZ, hmD]
    group
  have hcommF : Matrix.SpecialLinearGroup.map e6a3_iota A *
        Matrix.SpecialLinearGroup.map e6a3_iota zeta5 =
      Matrix.SpecialLinearGroup.map e6a3_iota zeta5 *
        Matrix.SpecialLinearGroup.map e6a3_iota A := h1.trans h2.symm
  have hcomm : A * zeta5 = zeta5 * A := by
    apply e6a3xe2_map_iota_injective
    rw [map_mul, map_mul]
    exact hcommF
  have hcent : A ∈ Subgroup.centralizer
      ({zeta5} : Set (Matrix.SpecialLinearGroup (Fin 6) F2)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  rw [centralizer_zeta5] at hcent
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hcent
  have hresF4 : e6a3xd2_resF4 (g : Matrix (Fin 3) (Fin 3) F4) =
      ((Matrix.SpecialLinearGroup.map e6a3_iota A : Matrix.SpecialLinearGroup (Fin 6) F4) :
        Matrix (Fin 6) (Fin 6) F4) := by
    rw [e6a3xd2_resF4, Matrix.SpecialLinearGroup.map_apply_coe, ← hg,
      coe_resGL]
  have hconj' : (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) *
        e6a3xd2_blk (g : Matrix (Fin 3) (Fin 3) F4)
          ((g : Matrix (Fin 3) (Fin 3) F4).map (fun a => a ^ 2)) =
      ((Matrix.SpecialLinearGroup.map e6a3_iota A : Matrix.SpecialLinearGroup (Fin 6) F4) :
        Matrix (Fin 6) (Fin 6) F4) * (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) := by
    rw [← hresF4]
    exact e6a3xd2_conj (g : Matrix (Fin 3) (Fin 3) F4)
  have hcoeeq : ((Matrix.SpecialLinearGroup.map e6a3_iota A :
        Matrix.SpecialLinearGroup (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) * (m : Matrix (Fin 6) (Fin 6) F4) *
        ((e6a3xc_P'⁻¹ : Matrix.SpecialLinearGroup (Fin 6) F4) :
          Matrix (Fin 6) (Fin 6) F4) := by
    rw [hAeq, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hPimPm : ((e6a3xc_P'⁻¹ : Matrix.SpecialLinearGroup (Fin 6) F4) :
        Matrix (Fin 6) (Fin 6) F4) * (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hP'blk : (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) *
        e6a3xd2_blk (g : Matrix (Fin 3) (Fin 3) F4)
          ((g : Matrix (Fin 3) (Fin 3) F4).map (fun a => a ^ 2)) =
      (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) * (m : Matrix (Fin 6) (Fin 6) F4) := by
    calc (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) *
          e6a3xd2_blk (g : Matrix (Fin 3) (Fin 3) F4)
            ((g : Matrix (Fin 3) (Fin 3) F4).map (fun a => a ^ 2))
        = ((Matrix.SpecialLinearGroup.map e6a3_iota A :
            Matrix.SpecialLinearGroup (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
            (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) := hconj'
      _ = ((e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) * (m : Matrix (Fin 6) (Fin 6) F4) *
            ((e6a3xc_P'⁻¹ : Matrix.SpecialLinearGroup (Fin 6) F4) :
              Matrix (Fin 6) (Fin 6) F4)) *
            (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) := by rw [hcoeeq]
      _ = (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) * (m : Matrix (Fin 6) (Fin 6) F4) := by
            rw [Matrix.mul_assoc ((e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) *
                  (m : Matrix (Fin 6) (Fin 6) F4))
                ((e6a3xc_P'⁻¹ : Matrix.SpecialLinearGroup (Fin 6) F4) :
                  Matrix (Fin 6) (Fin 6) F4)
                (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4),
              hPimPm, mul_one]
  have hunit : IsUnit ((e6a3xc_P' : Matrix.SpecialLinearGroup (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4) := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
    rw [show ((e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4)).det = 1 from e6a3xc_P'.property]
    exact isUnit_one
  have hblk_eq : e6a3xd2_blk (g : Matrix (Fin 3) (Fin 3) F4)
        ((g : Matrix (Fin 3) (Fin 3) F4).map (fun a => a ^ 2)) =
      (m : Matrix (Fin 6) (Fin 6) F4) := hunit.mul_left_cancel hP'blk
  have hdetg : (g : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
    have hdet := e6a3xd2_det_ev hmBD
    rwa [← hblk_eq, e6a3xd2_ev_blk] at hdet
  rw [sl3four]
  let hSL : Matrix.SpecialLinearGroup (Fin 3) F4 :=
    ⟨(g : Matrix (Fin 3) (Fin 3) F4), hdetg⟩
  refine ⟨hSL, ?_⟩
  change (resGL 3) (Matrix.SpecialLinearGroup.toGL hSL) = A
  have htoGL : (Matrix.SpecialLinearGroup.toGL hSL : Matrix.GeneralLinearGroup (Fin 3) F4) = g := by
    apply Units.ext
    rfl
  rw [htoGL]
  exact hg

private noncomputable def e6a3xe3_psi :
    Matrix.SpecialLinearGroup (Fin 3) F4 →* Matrix.SpecialLinearGroup (Fin 6) F4 :=
  (Matrix.SpecialLinearGroup.map e6a3_iota).comp (resSL 3)

private theorem e6a3xe3_psi_coe (X : Matrix.SpecialLinearGroup (Fin 3) F4) :
    (e6a3xe3_psi X : Matrix (Fin 6) (Fin 6) F4) =
      e6a3xd2_resF4 (X : Matrix (Fin 3) (Fin 3) F4) := by
  rw [e6a3xe3_psi, MonoidHom.comp_apply, Matrix.SpecialLinearGroup.map_apply_coe, coe_resSL]
  rfl

private theorem e6a3xe3_transvection_sq (i j : Fin 3) (hij : i ≠ j) (c : F4) :
    ((Matrix.SpecialLinearGroup.transvection hij c :
        Matrix.SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).map
        (fun a => a ^ 2) =
      (Matrix.SpecialLinearGroup.transvection hij (c ^ 2) :
        Matrix (Fin 3) (Fin 3) F4) := by
  have hfun : (fun a : F4 => a ^ 2) = (frobenius F4 2) := by
    funext a
    rw [frobenius_def]
  rw [hfun, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  change (frobenius F4 2).mapMatrix ((1 : Matrix (Fin 3) (Fin 3) F4) +
      Matrix.single i j c) = 1 + Matrix.single i j (c ^ 2)
  rw [map_add, map_one, RingHom.mapMatrix_apply, Matrix.map_single, frobenius_def]

private theorem e6a3xe3_re_blk (X Y : Matrix (Fin 3) (Fin 3) F4) :
    e6a3xd2_re (e6a3xd2_blk X Y) = Matrix.fromBlocks X 0 0 Y := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    fin_cases a <;> fin_cases b <;>
      simp [e6a3xd2_re_apply, e6a3xd2_σ_inl, e6a3xd2_σ_inr, e6a3xd2_blk,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

private theorem e6a3xe3_transvection_mem (i j : Fin 3) (hij : i ≠ j) (c : F4) :
    e6a3xe3_psi (Matrix.SpecialLinearGroup.transvection hij c) ∈ e6a3xc_MP := by
  let X : Matrix (Fin 3) (Fin 3) F4 :=
    (Matrix.SpecialLinearGroup.transvection hij c : Matrix (Fin 3) (Fin 3) F4)
  let E : Matrix.SpecialLinearGroup (Fin 6) F4 :=
    Matrix.SpecialLinearGroup.transvection (e6a3xd2_two_ne i j hij) c
  let O : Matrix.SpecialLinearGroup (Fin 6) F4 :=
    Matrix.SpecialLinearGroup.transvection (e6a3xd2_two_add_one_ne i j hij) (c ^ 2)
  have hE : e6a3xd2_re (E : Matrix (Fin 6) (Fin 6) F4) = Matrix.fromBlocks X 0 0 1 := by
    rw [e6a3xd2_re_transvection_even i j hij c]
  have hO : e6a3xd2_re (O : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.fromBlocks 1 0 0 (X.map (fun a => a ^ 2)) := by
    rw [e6a3xd2_re_transvection_odd i j hij (c ^ 2),
      ← e6a3xe3_transvection_sq i j hij c]
  have hblk : e6a3xd2_blk X (X.map (fun a => a ^ 2)) =
      (E : Matrix (Fin 6) (Fin 6) F4) * (O : Matrix (Fin 6) (Fin 6) F4) := by
    apply e6a3xd2_re.injective
    rw [e6a3xe3_re_blk, map_mul, hE, hO, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hE_mem : E ∈ e6a3xc_M := by
    rw [e6a3xc_M]
    refine Subgroup.subset_closure ?_
    left
    exact ⟨⟨2 * i.val, by omega⟩, ⟨2 * j.val, by omega⟩, e6a3xd2_two_ne i j hij,
      by simp [Nat.mul_mod_right], c, rfl⟩
  have hO_mem : O ∈ e6a3xc_M := by
    rw [e6a3xc_M]
    refine Subgroup.subset_closure ?_
    left
    exact ⟨⟨2 * i.val + 1, by omega⟩, ⟨2 * j.val + 1, by omega⟩,
      e6a3xd2_two_add_one_ne i j hij, by simp [Nat.add_mod, Nat.mul_mod_right], c ^ 2, rfl⟩
  rw [e6a3xc_MP]
  refine Subgroup.mem_map.mpr ⟨E * O, e6a3xc_M.mul_mem hE_mem hO_mem, ?_⟩
  have hP : e6a3xc_P' * (E * O) =
      e6a3xe3_psi (Matrix.SpecialLinearGroup.transvection hij c) * e6a3xc_P' := by
    apply Subtype.ext
    change (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4) *
        ((E : Matrix (Fin 6) (Fin 6) F4) * (O : Matrix (Fin 6) (Fin 6) F4)) =
      (e6a3xe3_psi (Matrix.SpecialLinearGroup.transvection hij c) :
          Matrix (Fin 6) (Fin 6) F4) * (e6a3xc_P' : Matrix (Fin 6) (Fin 6) F4)
    rw [← hblk, e6a3xe3_psi_coe]
    exact e6a3xd2_conj X
  change MulAut.conj e6a3xc_P' (E * O) =
    e6a3xe3_psi (Matrix.SpecialLinearGroup.transvection hij c)
  rw [MulAut.conj_apply]
  calc e6a3xc_P' * (E * O) * e6a3xc_P'⁻¹
      = (e6a3xc_P' * (E * O)) * e6a3xc_P'⁻¹ := rfl
    _ = (e6a3xe3_psi (Matrix.SpecialLinearGroup.transvection hij c) * e6a3xc_P') *
          e6a3xc_P'⁻¹ := by rw [hP]
    _ = e6a3xe3_psi (Matrix.SpecialLinearGroup.transvection hij c) *
          (e6a3xc_P' * e6a3xc_P'⁻¹) := by rw [mul_assoc]
    _ = e6a3xe3_psi (Matrix.SpecialLinearGroup.transvection hij c) := by
          rw [mul_inv_cancel, mul_one]

private theorem e6a3xe3_closure_aux :
    Subgroup.closure {g : Matrix.SpecialLinearGroup (Fin 3) F4 |
      ∃ (i j : Fin 3) (hij : i ≠ j) (c : F4),
        g = Matrix.SpecialLinearGroup.transvection hij c} ≤
      Subgroup.comap e6a3xe3_psi e6a3xc_MP := by
  rw [Subgroup.closure_le]
  rintro g ⟨i, j, hij, c, rfl⟩
  exact e6a3xe3_transvection_mem i j hij c

private theorem e6a3xd2_bwd (A : Matrix.SpecialLinearGroup (Fin 6) F2)
    (hA : A ∈ sl3four) : Matrix.SpecialLinearGroup.map e6a3_iota A ∈ e6a3xc_MP := by
  obtain ⟨X, rfl⟩ := hA
  have htop : Subgroup.closure {g : Matrix.SpecialLinearGroup (Fin 3) F4 |
      ∃ (i j : Fin 3) (hij : i ≠ j) (c : F4),
        g = Matrix.SpecialLinearGroup.transvection hij c} = ⊤ :=
    CFSG.ClassicalGroups.SpecialLinear.closure_transvection_eq_top
  have hle : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F4)) ≤
      Subgroup.comap e6a3xe3_psi e6a3xc_MP := by
    rw [← htop]
    exact e6a3xe3_closure_aux
  exact hle (Subgroup.mem_top X)

private theorem e6a3xc_sl3four

    (A : Matrix.SpecialLinearGroup (Fin 6) F2) :
    Matrix.SpecialLinearGroup.map e6a3_iota A ∈ e6a3xc_MP ↔ A ∈ sl3four :=
  ⟨e6a3xd2_fwd A, e6a3xd2_bwd A⟩

private theorem e6a3xc_naturality
    (A : Matrix.SpecialLinearGroup (Fin 6) F2) :
    e6a3_baseChange (E6Pilot.slToAdjointE6 F2 A) =
      e6a3xc_Phi (Matrix.SpecialLinearGroup.map e6a3_iota A) := by
  have hle : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F2)) ≤
      MonoidHom.eqLocus (e6a3_baseChange.comp (E6Pilot.slToAdjointE6 F2))
        (e6a3xc_Phi.comp (Matrix.SpecialLinearGroup.map e6a3_iota)) := by
    rw [← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
      Subgroup.closure_le]
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    change (e6a3_baseChange.comp (E6Pilot.slToAdjointE6 F2))
        (Matrix.TransvectionStruct.toSpecialLinearGroup ⟨i, j, hij, c⟩) =
      (e6a3xc_Phi.comp (Matrix.SpecialLinearGroup.map e6a3_iota))
        (Matrix.TransvectionStruct.toSpecialLinearGroup ⟨i, j, hij, c⟩)
    simp only [MonoidHom.comp_apply, Matrix.TransvectionStruct.toSpecialLinearGroup_mk,
      Matrix.SpecialLinearGroup.map_transvection]
    have h1 : e6a3_baseChange (E6Pilot.slToAdjointE6 F2
        (Matrix.SpecialLinearGroup.transvection hij c)) =
        baseChangeGL e6a3_iota (pinnedX .E6 F2 (a5Root i j) c) := by
      rw [e6a3_baseChange, MonoidHom.comp_apply]
      exact congrArg (baseChangeGL e6a3_iota) (E6Pilot.coe_slToAdjointE6_transvection hij c)
    rw [h1, baseChangeGL_pinnedX, e6a3xc_Phi_transvection]
  exact hle (Subgroup.mem_top A)

private theorem e6a3_step4 :
    e6a3_H = jE := by
  rw [jE_eq]
  refine le_antisymm ?_ ?_
  · intro x hx
    change e6a3_baseChange x ∈ e6a3_GS.map (MulAut.conj e6a3_P).toMonoidHom at hx
    have hxlev : x ∈ E6Pilot.a5Levi F2 := e6a3xc_descent x hx
    rw [← E6Pilot.range_slToAdjointE6 (K := F2)] at hxlev
    obtain ⟨A, rfl⟩ := hxlev
    rw [e6a3xc_naturality A] at hx
    exact ⟨A, (e6a3xc_sl3four A).mp
      ((e6a3xc_Phi_MP (Matrix.SpecialLinearGroup.map e6a3_iota A)).mp hx), rfl⟩
  · rintro x ⟨A, hA, rfl⟩
    change e6a3_baseChange (E6Pilot.slToAdjointE6 F2 A) ∈
      e6a3_GS.map (MulAut.conj e6a3_P).toMonoidHom
    rw [e6a3xc_naturality A]
    exact (e6a3xc_Phi_MP (Matrix.SpecialLinearGroup.map e6a3_iota A)).mpr
      ((e6a3xc_sl3four A).mpr hA)

theorem centralizer_wOmegaE_le_normalizer_jE :
    Subgroup.centralizer ({wOmegaE} : Set EC) ≤ Subgroup.normalizer (jE : Set EC) := by
  have h := e6a3_step3
  rw [e6a3_step4] at h
  exact h

theorem eq_jE_of_isComponentOf_centralizer_wE
    {K' : Subgroup EC} (hJ : jE ≤ K')
    (hK : CFSG.Assembly.IsComponentOf K' (Subgroup.centralizer ({wOmegaE} : Set EC))) :
    K' = jE :=
  eq_of_isComponentOf_of_le_normalizer centralizer_wOmegaE_le_normalizer_jE isQuasisimple_jE hJ hK

end CFSG.StandardType.GGSixE6Two
