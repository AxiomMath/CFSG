module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSmallDefs
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestBasic
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.LocalAnalysis.StandardType.GGL45FixA2Arith
import CFSG.LieType.Ree.LargeReeCenterTrivial
import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank
import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
import CFSG.RankThree.PartOne.BRANCH.RankRee
import CFSG.RankThree.PartOne.KE.A2Family
import CFSG.RankThree.PartOne.KE.A2Shape
import CFSG.RankThree.PartOne.KE.StabGeneral
import CFSG.RankThree.PartOne.KLR.Master
import CFSG.RankThree.PartOne.KLR.SectorAssembly
import CFSG.RankThree.PartOne.N143.Weyl613Defs
import CFSG.RankThree.PartOne.N143X.KF64WSimple
import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem card_le_nine_of_mulEquiv {R G : Type*} [Group R] [Group G] (e : R ≃* G)
    (h : ∀ E : Subgroup G, CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 9)
    {A : Subgroup R} (hA : CFSG.Open.IsElemAbelian 3 A) : Nat.card A ≤ 9 := by
  have h1 := h (A.map e.toMonoidHom) (TableB.isElemAbelian_map hA e.toMonoidHom)
  rwa [Subgroup.card_map_of_injective e.injective] at h1

private theorem card_le_nine_of_subset_inn {R : Type*} [Group R] [Finite R]
    (hR : Subgroup.center R = ⊥)
    (h : ∀ A : Subgroup R, CFSG.Open.IsElemAbelian 3 A → Nat.card A ≤ 9)
    {X : Subgroup (MulAut R)}
    (hXI : (X : Set (MulAut R)) ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hX : CFSG.Open.IsElemAbelian 3 X) : Nat.card X ≤ 9 := by
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn hR hXI hX
  rw [← hAc]
  exact h A hA

section SVTwF4

open CFSG.LieType.Ree

private theorem ggInndiagThreeRankTwo_twF4_recipe
    {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.StandardType.SCFourCover.GGInndiagThreeRankTwo
      (LargeEvenCenterQuot (LargeEvenTwF4H a K))
      (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
      (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) := by
  haveI : CharP K ReeTag.F4.prime := charP_two_of_card hK
  intro B hB hBI
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_twF4_equiv ha K hK
  haveI : Finite (LargeEvenCenterQuot (LargeEvenTwF4H a K)) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hZ := TableBExcSmallRest.center_eq_bot_of_mulEquiv e
    (ReeTag.large_Ree_fixed_group_center_trivial a K hK)
  have h3dvd : 3 ∣ 2 ^ (2 * a + 1) + 1 :=
    (gffa2_three_dvd_pow_add_one_iff (2 * a + 1)).mpr ⟨a, rfl⟩
  have hcop : Nat.Coprime 3 (Nat.card Kˣ) := by
    rw [Nat.card_units, hK]
    exact TableBExcSmallRest.coprime_of_dvd_two_pow_add_one Nat.prime_three (by omega) h3dvd
  have hXI : (B : Set (MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K)))) ⊆
      (Subgroup.closure (Set.range (MulAut.conj :
          LargeEvenCenterQuot (LargeEvenTwF4H a K) →*
            MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K))) ∪
        LargeEvenChevDiagImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) :
        Set (MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K)))) := by
    intro χ hχ
    have h : χ ∈ Subgroup.closure
        (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) := hBI hχ
    rw [LargeEvenChevIDImage, LargeEvenInnSet] at h
    rwa [Subgroup.closure_eq] at h
  have hBinn : (B : Set (MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K)))) ⊆
      Set.range (MulAut.conj :
        LargeEvenCenterQuot (LargeEvenTwF4H a K) →*
          MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K))) :=
    TableBExcSmallRest.subset_inn_of_pow_eq_one
      (ggOutCyclic_twF4 ha K hK)
      (D := LargeEvenChevDiagImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
      (fun δ hδ => TableBExcSmallRest.pow_card_units_eq_one_of_mem_diagImage hδ)
      hcop hXI (fun χ hχ => hB.2 χ hχ)
  exact card_le_nine_of_subset_inn hZ
    (fun A hA => card_le_nine_of_mulEquiv e
      (fun E hE =>
        CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof.card_le_nine_of_reeGamma a K hK E hE)
      hA)
    hBinn hB

theorem svRankTwF4_holds :
    SVRank (fun t => t = .twF4) := by
  intro lab hlab ht
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab
  subst ht
  obtain ⟨-, -, ⟨k, hk⟩, hn3⟩ := hlab
  have hk' : n = 2 * k + 1 := hk
  have hn1 : n - 1 = 2 * k := by omega
  have hdiv : (n - 1) / 2 = k := by
    rw [hn1]
    exact Nat.mul_div_cancel_left k (by norm_num)
  have ha : 1 ≤ (n - 1) / 2 := by
    rw [hdiv]
    omega
  intro Q hQ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  intro _ _
  exact ggInndiagThreeRankTwo_twF4_recipe (a := (n - 1) / 2) ha K hK

end SVTwF4

end CFSG.StandardType.TablePThreeKG

end
