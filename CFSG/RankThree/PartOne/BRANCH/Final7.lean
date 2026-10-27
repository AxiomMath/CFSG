module

public import CFSG.RankThree.PartOne.BRANCH.Bridge
public import CFSG.RankThree.PartOne.BRANCH.Lift7
public import CFSG.RankThree.PartOne.BRANCH.Succ7
public import CFSG.RankThree.PartOne.K156.Full
public import CFSG.RankThree.PartOne.S10.FiveCriticalActors

public section

namespace CFSG.RankThree.PartOne.BRANCH

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.MB3 CFSG.RankThree.PartOne.N143
  CFSG.RankThree.PartOne.FiveCritical
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

theorem sevenSmallPrimeCase_of_rank (hZS : ZeroStarSmall) (hRank : EvenLieSevenRank) :
    SevenSmallPrimeCase := by
  intro hS hTwo G _ _ A h L hL hnq hmax q D R hq35 hd
  have hp : (7 : ℕ).Prime := by norm_num
  have : Fact (7 : ℕ).Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hd.q_prime⟩
  obtain ⟨hsimple, hnonab, hKP, -, -, -, hAe, hAcard, -, -⟩ := id h
  have : IsSimpleGroup G := hsimple
  have he3 : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq h).le
  have hAL : A ≤ normalizer (L : Set G) :=
    selected_prime_elements_normalize_theta_components.2 G he3 7 hp (by norm_num) A hAe L hL.1
  have hLD : L ≤ normalizer (D : Set G) :=
    le_normalizer_of_characteristic_subgroupOf Subgroup.le_normalizer hd.D_le hd.D_char
  have hAD : A ≤ normalizer (D : Set G) :=
    le_normalizer_of_characteristic_subgroupOf hAL hd.D_le hd.D_char
  have hRAD : R ⊔ A ≤ normalizer (D : Set G) := sup_le (hd.R_le.trans hLD) hAD
  obtain ⟨hDe, hDcard, hDR, hDC⟩ := seven_lifting_full hTwo h hd hRAD
  have hED := seven_commutator_E_D hd hAe hDe hq35
  obtain ⟨c, hcA, hc1, hLc⟩ := mem_thetaComponentFamily_iff.mp hL.1
  have hEA : thetaQuotientCentralizer 7 A L ≤ A := inf_le_left
  have hEcard : Nat.card (thetaQuotientCentralizer 7 A L) = 7 ^ 2 :=
    card_eq_sq_of_relIndex_eq_prime hp hAcard hEA hd.relIndex
  obtain ⟨e, K, heE, he1, hKe, hKZ, hKq, hAK, hRP, hPK⟩ :=
    exists_seven_successor hS h hcA hc1 ⟨hL, hLc⟩ hmax hEcard hd.R_two hd.R_le hd.R_inv
      hd.R_comm hd.R_ne_bot hd.kernel
  have hDfix : D ≤ L ⊓ centralizer ({e} : Set G) := fun d hdD => by
    refine ⟨hd.D_le hdD, ?_⟩
    have heD : e ∈ centralizer (D : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hED heE
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp heD d hdD)
  have hPnorm : ∀ g ∈ L ⊓ centralizer ({e} : Set G), ∀ x ∈ fiveResidual L e,
      g * x * g⁻¹ ∈ fiveResidual L e := by
    intro g hg x hx
    obtain ⟨x', hx', rfl⟩ := hx
    refine ⟨⟨g, hg⟩ * x' * ⟨g, hg⟩⁻¹,
      (inferInstance : (perfectResidual ↥(L ⊓ centralizer ({e} : Set G))).Normal).conj_mem x' hx'
        ⟨g, hg⟩, ?_⟩
    simp
  have hDP : D ≤ fiveResidual L e := by
    rw [← hDR]
    refine Subgroup.commutator_le.mpr fun d hdD r hr => ?_
    rw [commutatorElement_def]
    exact (fiveResidual L e).mul_mem (hPnorm d (hDfix hdD) r (hRP hr))
      ((fiveResidual L e).inv_mem (hRP hr))
  have hDK : D ≤ K := hDP.trans hPK
  obtain ⟨K', hK', hKK'⟩ := exists_zeroStar_above_of_zero hS h hKZ
  have hKleK' : K ≤ K' := K156.le_of_sectionTenRel_of_quasisimple hp hKq hKK'
  obtain ⟨X, _, _, φ, -, hφk, hXs, hXn, hXsmall⟩ := hZS G A h K' hK'
  have hDK' : D ≤ K' := hDK.trans hKleK'
  have hRK' : R ≤ K' := (hRP.trans hPK).trans hKleK'
  have hdis : Disjoint (D.subgroupOf K') φ.ker := by
    rw [Subgroup.disjoint_def]
    intro x hxD hxk
    have hxc := hφk hxk
    have hxC : (x : G) ∈ centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨r, hRK' hr⟩)
    have h1 : (x : G) ∈ D ⊓ centralizer (R : Set G) := ⟨hxD, hxC⟩
    rw [hDC, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hD₀e : IsElementaryAbelian q ↥(D.subgroupOf K') := by
    have := hDe
    exact IsElementaryAbelian.subgroupOf hDK'
  have hD₀card : Nat.card ↥(D.subgroupOf K') = q ^ 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK').toEquiv]
    exact hDcard
  have hD'e : IsElementaryAbelian q ↥((D.subgroupOf K').map φ) := by
    have := hD₀e
    exact IsElementaryAbelian.map φ
  have hD'card : Nat.card ↥((D.subgroupOf K').map φ) = q ^ 7 := by
    rw [card_map_of_disjoint_ker φ hdis]
    exact hD₀card
  exact hRank X hXs hXn hXsmall q hq35 _ hD'e hD'card

end CFSG.RankThree.PartOne.BRANCH
