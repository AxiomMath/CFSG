module

public import CFSG.Quasithin.H13.U3L14W
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.H13.U3L14Q

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.InternalSec
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_two_mem_of_sup {K T : Subgroup G} (hTK : T ≤ normalizer (K : Set G))
    (hT : IsPGroup 2 T) {y : G} (hy : y ∈ K ⊔ T) : ∃ m : ℕ, y ^ 2 ^ m ∈ K := by
  obtain ⟨k, hk, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTK).1 hy
  have key : ∀ n : ℕ, (k * t) ^ n * (t ^ n)⁻¹ ∈ K := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : t ^ n * k * (t ^ n)⁻¹ ∈ K :=
        (mem_normalizer_iff.mp (hTK (pow_mem ht n)) k).mp hk
      have : (k * t) ^ (n + 1) * (t ^ (n + 1))⁻¹ =
          ((k * t) ^ n * (t ^ n)⁻¹) * (t ^ n * k * (t ^ n)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [this]
      exact mul_mem ih h1
  obtain ⟨m, hm⟩ := hT ⟨t, ht⟩
  refine ⟨m, ?_⟩
  have htm : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  simpa [htm] using key (2 ^ m)

omit [Finite G] in
theorem pow_two_mem_autOn_sup {K T W : Subgroup G} (hTK : T ≤ normalizer (K : Set G))
    (hT : IsPGroup 2 T) (hW : K ⊔ T ≤ normalizer (W : Set G)) :
    ∀ g ∈ autOn (K ⊔ T) W, ∃ m : ℕ, g ^ 2 ^ m ∈ autOn K W := by
  intro g hg
  obtain ⟨⟨y, hyN⟩, hy, rfl⟩ := Setup.mem_autOn_iff.1 hg
  obtain ⟨m, hm⟩ := pow_two_mem_of_sup hTK hT hy
  refine ⟨m, ?_⟩
  rw [← map_pow]
  have := conjAct_mem_autOn (U := W) (le_sup_left.trans hW) hm
  convert this using 2

omit [Finite G] in
theorem map_commV_autOn {K W : Subgroup G} [IsMulCommutative ↥W]
    (hKW : K ≤ normalizer (W : Set G)) : (commV (autOn K W)).map W.subtype = ⁅W, K⁆ :=
  CFSG.Quasithin.AutOn.map_commV_autOn_eq hKW

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem b51Part1_KT (h1332 : Stmt13_3_2) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) :
    ∃ _ : IsMulCommutative ↥(reducedAggregate (K ⊔ T)),
      B51Part1 (ffJ (autOn (K ⊔ T) (reducedAggregate (K ⊔ T))))
        (autOn K (reducedAggregate (K ⊔ T))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := reducedAggregate (K ⊔ T) with hWdef
  have hred : IsTwoReducedIn (K ⊔ T) W := isTwoReducedIn_reducedAggregate (K ⊔ T)
  have hWe : IsElemAbelian 2 W := hred.2.2.1
  have hWc : IsMulCommutative ↥W := hWe.1
  refine ⟨hWc, ?_⟩
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := S.syl le_sup_right
  have hYK : K ⊔ T ≤ normalizer (K : Set G) := sup_le le_normalizer hD.T_K
  have hKW : K ≤ normalizer (W : Set G) := le_sup_left.trans hred.2.1
  have hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥K)).symm
      (A3.isQuasisimple_iff_open.2 hD.quasi)
  have hnt : ¬ K ≤ centralizer (W : Set G) := (S.reduced_K h1332 hD.faithful hD.quasi).1
  have hO2Y : pCoreOf 2 (autOn (K ⊔ T) W) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hO2K : pCoreOf 2 (autOn K W) = ⊥ := by
    have hn : ((autOn K W).subgroupOf (autOn (K ⊔ T) W)).Normal := by
      refine ⟨fun k hk x => ?_⟩
      rw [mem_subgroupOf] at hk ⊢
      exact autOn_normal_of hYK _ x.2 _ hk
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _
      (autOn_le_autOn_of_le le_sup_left) hn
    rw [hO2Y] at this
    exact le_bot_iff.1 this
  have hq : CFSG.IsQuasisimple ↥(autOn K W) := isQuasisimple_autOn hKW hKq hO2K hnt
  have hJ : K = ⁅K, thompsonJ T⁆ := (S.K_eq_comm_J h1332 hC58 h317 hD).symm
  have hSY : SQTKGroup ↥(K ⊔ T) :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hD.faithful.1.2.2.2
  obtain ⟨A₀, -, hA, hKA⟩ := exists_offender_of hTsyl le_sup_left hYK hred hq hnt hJ
  obtain ⟨hKJ, hn, hQ, -, hcases⟩ := b56Cases_ffJ_autOn h56 (fun w hw => hWe.2 w hw) hred.2.1
    le_sup_left hYK hSY hO2Y hA hKA
  have h2 : ∀ g ∈ ffJ (autOn (K ⊔ T) W), ∃ m : ℕ, g ^ 2 ^ m ∈ autOn K W := fun g hg =>
    pow_two_mem_autOn_sup hD.T_K S.isP_T hred.2.1 g (B6.ffJ_le _ hg)
  obtain ⟨h1, hF⟩ := b56Case1_of_pow_two hKJ hn hq hQ h2 hcases
  have hB51 := h1.2.1
  rw [hF] at hB51
  exact hB51.1

end Set14

end CFSG.Quasithin.H13.U3
