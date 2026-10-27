module

public import CFSG.Quasithin.H13.NQS1345B
public import CFSG.Quasithin.H13.U3S1343
public import CFSG.Quasithin.H13.U3S134Defs

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.InternalSec
open CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem cZL_K_eq_bot (S : A6.Setting134 G T L V) {K : Subgroup G}
    (hKM : ¬ K ≤ normalizer (L : Set G)) :
    quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) ⊓ centralizer (K : Set G) = ⊥ := by
  by_contra hD
  set D := quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) ⊓ centralizer (K : Set G)
    with hDdef
  have hDT : D ≤ T := (inf_le_left.trans inf_le_left).trans (U3.s134_Z_le_center T |>.trans
    inf_le_left)
  have hD2 : IsPGroup 2 D := S.h13.sylow.1.to_le hDT
  have hloc : IsTwoLocal (normalizer (D : Set G)) := ⟨D, hD, hD2, rfl⟩
  have hDC : ∀ {X : Subgroup G}, D ≤ centralizer (X : Set G) → X ≤ normalizer (D : Set G) :=
    fun hX => (le_centralizer_iff.mp hX).trans (centralizer_le_normalizer _)
  have hLTD : L ⊔ T ≤ normalizer (D : Set G) := by
    refine sup_le (hDC (inf_le_left.trans inf_le_right)) (hDC ?_)
    exact (inf_le_left.trans inf_le_left).trans ((U3.s134_Z_le_center T).trans inf_le_right)
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hM'M := S.uniqueM.2 M' ⟨hM', hLTD.trans hle⟩
  exact hKM ((hDC inf_le_right).trans (hM'M ▸ hle))

theorem cZ_K_eq (S : A6.Setting134 G T L V) {K : Subgroup G}
    (hKM : ¬ K ≤ normalizer (L : Set G)) {z : G} (hzZ : z ∈ quasithinOmegaOneCenter T)
    (hz1 : z ≠ 1) (hKz : K ≤ centralizer ({z} : Set G))
    (hZL : Nat.card ↥(quasithinOmegaOneCenter T) =
      2 * Nat.card ↥(quasithinOmegaOneCenter T ⊓ centralizer (L : Set G))) :
    U3.cZ T K = zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZdef
  set A := U3.cZ T K with hAdef
  set B := Z ⊓ centralizer (L : Set G) with hBdef
  have hAB : B ⊓ A = ⊥ := by
    rw [eq_bot_iff, ← cZL_K_eq_bot S hKM]
    intro x hx
    obtain ⟨⟨hxZ, hxL⟩, -, hxK⟩ := hx
    exact ⟨⟨hxZ, hxL⟩, hxK⟩
  have hAZ : A ≤ Z := inf_le_left
  have hBZ : B ≤ Z := inf_le_left
  have hBi : B.relIndex Z = 2 := by
    have h1 := relIndex_mul_card B Z
    rw [inf_eq_left.2 hBZ, hZL] at h1
    have hpos : 0 < Nat.card B := Nat.card_pos
    nlinarith
  have hcard : Nat.card A ≤ 2 := by
    have h1 : B.relIndex A = Nat.card A := by
      rw [← inf_relIndex_right, hAB, relIndex_bot_left]
    rw [← h1, ← hBi]
    exact relIndex_le_of_le_right hAZ (by rw [hBi]; norm_num)
  have hzA : z ∈ A := by
    refine ⟨hzZ, mem_centralizer_iff.mpr fun k hk => ?_⟩
    exact (mem_centralizer_singleton_iff.mp (hKz hk))
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.1 hzZ).2.2
  have hzc : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz2 hz1
  exact (eq_of_le_of_card_ge (zpowers_le.mpr hzA) (by rw [hzc]; exact hcard)).symm

theorem b51Part1_K (h56 : AsB56) (S : A6.Setting134 G T L V) {K : Subgroup G}
    (hKf : quasithinIsFaithfulLocal T K) (hTK : T ≤ normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKW : ¬ K ≤ centralizer (reducedAggregate (K ⊔ T) : Set G))
    (hJ : ⁅K, thompsonJ T⁆ = K) :
    ∃ _ : IsMulCommutative ↥(reducedAggregate (K ⊔ T)),
      B51Part1 (ffJ (autOn (K ⊔ T) (reducedAggregate (K ⊔ T))))
        (autOn K (reducedAggregate (K ⊔ T))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := reducedAggregate (K ⊔ T) with hWdef
  have hred : IsTwoReducedIn (K ⊔ T) W := twoReduced_R2 (K ⊔ T)
  have hWe : IsElemAbelian 2 W := hred.2.2.1
  have hWc : IsMulCommutative ↥W := hWe.1
  refine ⟨hWc, ?_⟩
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKf.1.1, hKf.1.2.2.1⟩
  have hYK : K ⊔ T ≤ normalizer (K : Set G) := sup_le le_normalizer hTK
  have hKWn : K ≤ normalizer (W : Set G) := le_sup_left.trans hred.2.1
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
  have hqA : CFSG.IsQuasisimple ↥(autOn K W) := isQuasisimple_autOn hKWn hq hO2K hKW
  have hSY : SQTKGroup ↥(K ⊔ T) :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hKf.1.2.2.2
  obtain ⟨A₀, -, hA, hKA⟩ :=
    U3.exists_offender_of hTsyl le_sup_left hYK hred hqA hKW hJ.symm
  obtain ⟨hKJ, hn, hQ, -, hcases⟩ := b56Cases_ffJ_autOn h56 (fun w hw => hWe.2 w hw) hred.2.1
    le_sup_left hYK hSY hO2Y hA hKA
  have h2 : ∀ g ∈ ffJ (autOn (K ⊔ T) W), ∃ m : ℕ, g ^ 2 ^ m ∈ autOn K W := fun g hg =>
    U3.pow_two_mem_autOn_sup hTK hTsyl.2.1 hred.2.1 g (B6.ffJ_le _ hg)
  obtain ⟨h1, hF⟩ := U3.b56Case1_of_pow_two hKJ hn hqA hQ h2 hcases
  have hB51 := h1.2.1
  rw [hF] at hB51
  exact hB51.1

end CFSG.Quasithin.H13.NQS134
