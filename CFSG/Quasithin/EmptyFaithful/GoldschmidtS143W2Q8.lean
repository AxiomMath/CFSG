module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Gen
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B3Q
public import CFSG.Quasithin.Background.B3ThreeModel
public import CFSG.Quasithin.Background.B3ThreeStruct
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.G2Omega4PlusModule
public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S143FF
public import CFSG.Quasithin.EmptyFaithful.S143Final
public import CFSG.Quasithin.EmptyFaithful.S143HD
public import CFSG.Quasithin.EmptyFaithful.S143IG
public import CFSG.Quasithin.EmptyFaithful.S143JB
public import CFSG.Quasithin.EmptyFaithful.S143KO
public import CFSG.Quasithin.EmptyFaithful.S143KP
public import CFSG.Quasithin.EmptyFaithful.S143SC
public import CFSG.Quasithin.EmptyFaithful.S143SD
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin

open scoped MatrixGroups commutatorElement
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace S143

namespace InspW2

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

@[expose] def q8 : Finset (SL(2, ZMod 3)) := Finset.univ.filter fun g => g ^ 4 = 1

theorem q8_card : q8.card = 8 := by decide +kernel

theorem q8_commutators : ∀ g ∈ q8, ∃ x y : SL(2, ZMod 3), ⁅x, y⁆ = g := by decide +kernel

theorem q8_shape : ∃ c ∈ q8, c ≠ 1 ∧ ∀ g ∈ q8, ∀ h ∈ q8,
    g = h ∨ g⁻¹ * h = c ∨ (g⁻¹ * h) * (g⁻¹ * h) = c := by decide +kernel

theorem eight_le_of_q8_perm {n : ℕ} {T : Subgroup SL(2, ZMod 3)} (hT : ∀ g ∈ q8, g ∈ T)
    (θ : T →* Equiv.Perm (Fin n)) (hθ : Function.Injective θ) : 8 ≤ n := by
  obtain ⟨c, hcq, hc1, hshape⟩ := q8_shape
  have hcT : c ∈ T := hT c hcq
  have hne : (⟨c, hcT⟩ : T) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hθc : θ ⟨c, hcT⟩ ≠ 1 := fun h => hne (hθ (by rw [h, map_one]))
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hθc
  classical
  let f : SL(2, ZMod 3) → Fin n := fun g => if h : g ∈ T then θ ⟨g, h⟩ x else x
  have hinj : Set.InjOn f (q8 : Set (SL(2, ZMod 3))) := by
    intro g hg h hh hfg
    have hgT := hT g hg
    have hhT := hT h hh
    simp only [f, hgT, hhT, dite_true] at hfg
    have key : θ ((⟨g, hgT⟩ : T)⁻¹ * ⟨h, hhT⟩) x = x := by
      rw [map_mul, map_inv, Equiv.Perm.mul_apply, ← hfg]
      simp
    rcases hshape g hg h hh with hgh | hc' | hc'
    · exact hgh
    · exact absurd (by simpa [show (⟨g, hgT⟩ : T)⁻¹ * ⟨h, hhT⟩ = ⟨c, hcT⟩ from Subtype.ext hc']
        using key) hx
    · refine absurd ?_ hx
      have h2 : (⟨g, hgT⟩ : T)⁻¹ * ⟨h, hhT⟩ * ((⟨g, hgT⟩ : T)⁻¹ * ⟨h, hhT⟩) = ⟨c, hcT⟩ :=
        Subtype.ext hc'
      rw [← h2, map_mul, Equiv.Perm.mul_apply, key, key]
      simp
  have h1 := Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
  simpa [q8_card] using h1

theorem eight_le_of_sl23_in_aut {L Gc : Type} [Group L] [Group Gc] {n : ℕ}
    (hZ : Subgroup.center L = ⊥) (hout : ∀ a b : Outer L, a * b = b * a)
    (ρ : Gc →* MulAut L) (hρ : Function.Injective ρ) (κ : SL(2, ZMod 3) →* Gc)
    (hκ : Function.Injective κ) (π : L →* Equiv.Perm (Fin n)) (hπ : Function.Injective π) :
    8 ≤ n := by
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [← MonoidHom.ker_eq_bot_iff, Insp7.ker_conj_eq_center, hZ]
  let Θ : SL(2, ZMod 3) →* MulAut L := ρ.comp κ
  have hΘ : Function.Injective Θ := hρ.comp hκ
  let T : Subgroup SL(2, ZMod 3) := (Inn L).comap Θ
  have hcomm : ∀ x y : SL(2, ZMod 3), ⁅x, y⁆ ∈ T := by
    intro x y
    have h1 : (QuotientGroup.mk (Θ ⁅x, y⁆) : MulAut L ⧸ Inn L) = 1 := by
      have h2 : (QuotientGroup.mk' (Inn L)) (Θ ⁅x, y⁆) = 1 := by
        rw [map_commutatorElement, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hout _ _)
      exact h2
    exact (QuotientGroup.eq_one_iff (Θ ⁅x, y⁆)).mp h1
  have hq8 : ∀ g ∈ q8, g ∈ T := by
    intro g hg
    obtain ⟨x, y, rfl⟩ := q8_commutators g hg
    exact hcomm x y
  let ι : L ≃* (MulAut.conj : L →* MulAut L).range := MonoidHom.ofInjective hinj
  let Θ₁ : T →* (MulAut.conj : L →* MulAut L).range :=
    (Θ.comp T.subtype).codRestrict _ (fun t => t.2)
  have hΘ₁ : Function.Injective Θ₁ := fun a b h =>
    Subtype.ext (hΘ (congrArg Subtype.val h))
  exact eight_le_of_q8_perm hq8 (π.comp (ι.symm.toMonoidHom.comp Θ₁))
    (hπ.comp (ι.symm.injective.comp hΘ₁))

end InspW2

end S143

end CFSG.Quasithin
