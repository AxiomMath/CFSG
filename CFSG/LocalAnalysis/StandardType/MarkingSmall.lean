module

public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionTypeExceptions
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases
public import CFSG.Monster.Existence.Compat.Sp8
public import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.Open.StatedZModTwo
import CFSG.Adapters.StatedPSLTwoNine
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem center_eq_bot_of_isSimpleGroup {H : Type*} [Group H] [IsSimpleGroup H]
    (hR : ∃ a b : H ⧸ Subgroup.center H, a * b ≠ b * a) : Subgroup.center H = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hR
    have h1 : ∀ x : H ⧸ Subgroup.center H, x = 1 := fun x =>
      QuotientGroup.induction_on x fun g => (QuotientGroup.eq_one_iff g).2 (by
        rw [h]; exact Subgroup.mem_top g)
    exact hab (by rw [h1 a, h1 b])

theorem nonempty_centerQuot_equiv_of_isSimpleGroup {H : Type*} [Group H] [IsSimpleGroup H]
    (hR : ∃ a b : H ⧸ Subgroup.center H, a * b ≠ b * a) :
    Nonempty (H ⧸ Subgroup.center H ≃* H) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_isSimpleGroup hR)).trans
    QuotientGroup.quotientBot⟩

theorem nonabelian_of_mulEquiv {R R' : Type*} [Group R] [Group R'] (e : R ≃* R')
    (h : ∃ a b : R, a * b ≠ b * a) : ∃ a b : R', a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e a, e b, fun h' => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h']

theorem suzukiModel_largeEvenSz {a : ℕ} (ha : 1 ≤ a)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hR : ∃ x y : LargeEvenCenterQuot (LargeEvenSzGroup a K), x * y ≠ y * x) :
    SuzukiModel (LargeEvenCenterQuot (LargeEvenSzGroup a K)) 2 (2 * a + 1) := by
  obtain ⟨e₁⟩ := nonempty_centerQuot_congr (largeEvenSzGroup_eq a K)
  have : IsSimpleGroup (suzukiGroup a K) := (CFSG.LieType.Ree.suzuki_simple ha hK).2.2
  obtain ⟨e₂⟩ := nonempty_centerQuot_equiv_of_isSimpleGroup (H := suzukiGroup a K)
    (nonabelian_of_mulEquiv e₁ hR)
  exact ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨e₁.trans e₂⟩⟩

theorem largeEvenScalars_eq_bot {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) : LargeEvenScalars ι K = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK ι

theorem nonempty_largeEvenProj_equiv_of_card_two {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (H : Subgroup (GL ι K)) :
    Nonempty (LargeEvenProj H ≃* H) := by
  have h : (LargeEvenScalars ι K).subgroupOf H = ⊥ := by
    rw [largeEvenScalars_eq_bot hK, Subgroup.bot_subgroupOf]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot⟩

theorem nonempty_commutator_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    Nonempty (↥(commutator G) ≃* ↥(commutator G')) := by
  have hmap : (commutator G).map e.toMonoidHom = commutator G' := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 e.surjective]
  exact ⟨((commutator G).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hmap)⟩

theorem nonempty_commutator_subgroup_equiv {G : Type*} [Group G] (H : Subgroup G) :
    Nonempty (↥⁅H, H⁆ ≃* ↥(commutator H)) :=
  ⟨(((commutator H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr H.map_subtype_commutator)).symm⟩

theorem nonempty_largeEvenSpGroup_equiv_sympFour {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    Nonempty (↥(LargeEvenSpGroup K 2) ≃*
      CFSG.ComponentClassification.PresentationLocal.sympFour) := by
  have := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card]
  exact ⟨((CFSG.Monster.Existence.Compat.statedSpEquiv 2 K).trans
    (CFSG.Monster.Existence.Compat.sympMapEquiv (FiniteField.ringEquivOfCardEq hc))).trans
    (MulEquiv.ofBijective CFSG.ComponentClassification.StandardRecognition.symplecticToSympFour
      CFSG.ComponentClassification.StandardRecognition.symplecticToSympFour_bijective)⟩

theorem nonempty_b2der_equiv_alternatingGroup {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    Nonempty (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ ≃*
      alternatingGroup (Fin 6)) := by
  obtain ⟨e₁⟩ := nonempty_largeEvenProj_equiv_of_card_two hK
    ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆
  obtain ⟨e₂⟩ := nonempty_commutator_subgroup_equiv (LargeEvenSpGroup K 2)
  obtain ⟨e₃⟩ := nonempty_largeEvenSpGroup_equiv_sympFour hK
  obtain ⟨e₄⟩ := nonempty_commutator_equiv e₃
  exact ⟨((e₁.trans e₂).trans e₄).trans
    CFSG.ComponentClassification.PresentationLocal.commutatorEquivAlternating⟩

theorem statedClassicalModel_b2der {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    StatedClassicalModel (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆) .PSL 2 3 2 :=
  CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six _
    (nonempty_b2der_equiv_alternatingGroup hK)

theorem nonempty_alternatingGroup_of_psl_two_nine {S : Type} [Group S]
    (h : StatedClassicalModel S .PSL 2 3 2) : Nonempty (S ≃* alternatingGroup (Fin 6)) :=
  CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine h

theorem nonempty_alternatingGroup_of_markedModel_b2der {lab : LargeEvenLabel}
    (ht : lab.tag = .B2der) {R : Type} [Group R] (h : MarkedModel lab R) :
    Nonempty (R ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at h
  rcases h with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact nonempty_alternatingGroup_of_psl_two_nine h
  · simp [chevalleyExceptionalTags] at ht
  · simp [reeTitsTags] at ht
  · cases ht

theorem lieModel_g2der (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2)
    (hR : ∃ x y : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true), x * y ≠ y * x) :
    LieModel (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) .PSU 3 3 1 := by
  obtain ⟨e₁⟩ := centerQuot_commutator_chevGroup_equiv K .G2
  have hL := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds K hK
  have hC : StatedClassicalModel ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ .PSU 3 3 1 := by
    rcases hL with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact h
    · simp [chevalleyExceptionalTags] at ht
    · simp [reeTitsTags] at ht
    · cases ht
  have : IsSimpleGroup ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hC).2
  obtain ⟨e₂⟩ := nonempty_centerQuot_equiv_of_isSimpleGroup
    (H := ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆) (nonabelian_of_mulEquiv e₁ hR)
  exact lieModel_of_mulEquiv' (e₁.trans e₂).symm hL

end CFSG.StandardType
