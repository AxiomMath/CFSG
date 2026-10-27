module

public import CFSG.RankThree.PartOne.K1320X.TwoSub
public import CFSG.RankThree.PartOne.S12.Facts13
public import CFSG.RankThree.PartOne.S12.KFTransfer
public import CFSG.RankThree.PartOne.S13K.ThetaFixed
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
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
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KF.R5Layer
public import CFSG.RankThree.PartOne.KF.R6Layer
public import CFSG.RankThree.PartOne.KF.R7Final
public import CFSG.RankThree.PartOne.KFOUT3.KtyD8
public import CFSG.RankThree.PartOne.KFOUT3.KtyRow4
public import CFSG.RankThree.PartOne.KLAY.RootLayerRow4
public import CFSG.RankThree.PartOne.S13K.HasTwoSub
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.Walter.Defs

public section

namespace CFSG.RankThree.PartOne.K1320X

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem hasTwoSub_of_model {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) {s : MulAut E}
    (hs : s ∈ reflectionSet p E) {K : Subgroup G} {g : ℕ}
    (hmod : Assembly.LowTwoRank.StatedClassicalModel ↥K .PSL 2 2 g) (hpg : p ∣ 2 ^ g - 1)
    (hmov : autMovedInG E s ≤ K) (hKc : K ≤ Subgroup.centralizer (autFixedInG E s : Set G)) :
    HasTwoSub E K := by
  classical
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hEsup, -, hcard⟩ := hF13.reflection s hs
  have hMne : autMovedInG E s ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    exact hp.one_lt.ne hcard
  obtain ⟨⟨x, hxM⟩, hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hMne
  have hx1 : x ≠ 1 := fun h1 => hx1' (Subtype.ext h1)
  have hxp : x ^ p = 1 := by
    have h1 : (⟨x, hxM⟩ : ↥(autMovedInG E s)) ^ p = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    exact congrArg Subtype.val h1
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hzM : Subgroup.zpowers x = autMovedInG E s := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxM) ?_
    rw [hcard, Nat.card_zpowers, hord]
  have hME : autMovedInG E s ≤ E := Subgroup.map_subtype_le _
  obtain ⟨S, hSK, hS1, hS2, hxS, hSc⟩ := exists_twoSub_of_psl2 hp hmod hpg (hmov hxM) hx1 hxp
  have hKcent : ∀ k ∈ K, ∀ y ∈ autFixedInG E s, y * k = k * y := fun k hk y hy =>
    Subgroup.mem_centralizer_iff.mp (hKc hk) y hy
  have hfixS : autFixedInG E s ≤ Subgroup.normalizer (S : Set G) := by
    intro y hy
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hKcent z (hSK hz) y hy).symm
  have hE : E ≤ Subgroup.normalizer (S : Set G) := by
    rw [hEsup]
    refine sup_le hfixS ?_
    rw [← hzM]
    exact Subgroup.zpowers_le.2 hxS
  refine ⟨S, hSK, hS1, hS2, hE, le_antisymm ?_ ?_⟩
  · refine hSc.trans (Subgroup.commutator_mono le_rfl ?_)
    rw [hzM]
    exact hME
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    have h3 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.1 (hE hg₂) g₁⁻¹).1 (S.inv_mem hg₁)
    have : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by group
    rw [this]
    exact S.mul_mem hg₁ h3

theorem hasTwoSub_of_kfAt {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) {s : MulAut E}
    (hs : s ∈ reflectionSet p E) {g : ℕ} (hK : KFAt p E g s) (hpg : p ∣ 2 ^ g - 1) :
    HasTwoSub E (kZero p E s) :=
  hasTwoSub_of_model h hF13 hs hK.2.1 hpg hK.2.2.2.1 (kZero_le_centralizer_fixed p E s)

end CFSG.RankThree.PartOne.K1320X
