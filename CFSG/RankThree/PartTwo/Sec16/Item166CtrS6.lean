module

public import CFSG.RankThree.PartTwo.Sec16.Item166CtrKcdA5
public import CFSG.RankThree.PartTwo.Sec16.Item166CtrS6Push
public import CFSG.RankThree.PartTwo.Sec16.Item166CtrS6Red
public import CFSG.RankThree.PartTwo.Sec17.Item1730Chosen
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR

public section

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec11 CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

private theorem le_M_of_eq_bot {T S : Subgroup G}
    (hO : pPrimeCoreOf 2 T ≤ Subgroup.normalizer (Y₀ : Set G))
    (hSidx : ¬ 2 ∣ S.relIndex T) (hSbot : S = ⊥) :
    T ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have hodd : ¬ 2 ∣ Nat.card T := by
    rwa [hSbot, Subgroup.relIndex_bot_left] at hSidx
  have hT : T ≤ pPrimeCoreOf 2 T :=
    le_pPrimeCoreOf le_rfl Subgroup.le_normalizer
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  exact hT.trans hO

private theorem exists_threeCentral_inf
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ∃ d ∈ A ⊓ L, d ≠ 1 ∧ IsThreeCentralIn L d := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨-, h9, -⟩ := Sec14.j2_point_facts h.toSec13Data hJ
  obtain ⟨-, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  exact Sec17.exists_threeCentral_of_card_nine h415 hθ3 hJ inf_le_right
    (fun x hx => h.toSec13Data.isElemAbelian.2 x hx.1) h9

theorem le_M_of_omegaOneZ_le_centralizer
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h155 : Item155R) (h143 : Ronan148Q.Item143QS14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets)
    (hKcd : Step166KcdA5) (hData : Step166A5Data)
    (hKd : Step166KCommD) {J : Subgroup G} (hJY : J ≤ Y₀) (hJperf : Group.IsPerfect ↥J)
    (hJA5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)))
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {M : Subgroup G} (hMY : M ∈ scriptY2 A)
    (hJM : J ≤ M) (hMJ : M ≤ Subgroup.normalizer (J : Set G)) {T S : Subgroup G}
    (hTM : T ≤ M) (hTJ : ⁅T, J⁆ ≤ CFSG.Open.pCoreOf 2 J)
    (hJQ : J ⊓ CFSG.Open.pCoreOf 2 Y₀ = CFSG.Open.pCoreOf 2 J)
    (hTQ : T ∈ scriptQ A (lB A))
    (hsol : Group.IsSolvable ↥T) (hST : S ≤ T) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex T) (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hO : pPrimeCoreOf 2 T ≤ Subgroup.normalizer (Y₀ : Set G))
    (hZ : omegaOneZ S ≤ Subgroup.centralizer (Y₀ : Set G)) :
    T ≤ Subgroup.normalizer (Y₀ : Set G) := by
  classical
  by_cases hSbot : S = ⊥
  · exact le_M_of_eq_bot hO hSidx hSbot
  obtain ⟨d, hdAL, hd1, hdc⟩ := exists_threeCentral_inf h hJ
  obtain ⟨R₂, hR₂S, hZR₂, hAR₂, hKM⟩ :=
    exists_le_M_of_commutator_le h hTQ hsol hST hS2 hSidx hAS hO
  refine hKM fun p hp hp2 hp3 P hPT hPp hAP hPN => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (h.toSec13Data.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩)
  have hAcN : A ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    have h : Subgroup.centralizer ({c} : Set G) =
        Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact (h ▸ hAc).trans (Subgroup.centralizer_le_normalizer _)
  have hKP : ⁅P, Subgroup.zpowers c⁆ ≤ P :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr hcA).trans hAP)
  have hAK : A ≤ Subgroup.normalizer ((⁅P, Subgroup.zpowers c⁆ : Subgroup G) : Set G) :=
    Sec14.le_normalizer_commutator hAP hAcN
  have hPQ : P ∈ scriptQ A (lB A) := mem_scriptQ_of_le hTQ hPT hAP
  have hKQ : ⁅P, Subgroup.zpowers c⁆ ∈ scriptQ A (lB A) := mem_scriptQ_of_le hPQ hKP hAK
  have hKCd : ⁅P, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ({d} : Set G) :=
    commutator_zpowers_le_centralizer_d_of_kcdA5 h hJ h143 h134 h48 h1514 hMeets hKcd hData
      hJY hJperf hJA5 hAJ hdAL.1 hd1 hdc hPp hp2 hp3 hPQ hMY hJM hMJ (hPT.trans hTM)
      ((Subgroup.commutator_mono hPT le_rfl).trans hTJ) hJQ
  have hSQ : S ∈ scriptQ A (lB A) := mem_scriptQ_of_le hTQ hST hAS
  have hR2 : IsPGroup 2 R₂ := hS2.to_le hR₂S
  have hRQ : R₂ ∈ scriptQ A (lB A) := mem_scriptQ_of_le hSQ hR₂S hAR₂
  have hZ1 : omegaOneZ S ≠ ⊥ := Sec7.omegaOneZ_ne_bot hS2 hSbot
  have hAZ : A ≤ Subgroup.normalizer (omegaOneZ S : Set G) :=
    hAS.trans (by simpa only [Sec7.tripleOf_two] using Sec7.normalizer_le_normalizer_tripleOf S 2)
  set L₀ : Subgroup G := lB A (Subgroup.closure {c, d}) with hL₀
  have hLY : L₀ ≤ Y₀ := by
    rw [hL₀]
    exact (lB_closure_le h hJ hdAL.1 hd1 hdc).trans h.le_y0
  have hdL₀ : d ∈ L₀ := by
    rw [hL₀]
    exact mem_lB_closure h hJ hdAL.1 hd1 hdc
  have hL₀d : L₀ ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [hL₀, lB_closure_eq_residual h hJ hdAL.1 hd1 hdc]
    exact Item148HJ.residual_le_centralizer_singleton L d
  have hL₀perf : Group.IsPerfect ↥L₀ := by
    rw [hL₀, lB_closure_eq_residual h hJ hdAL.1 hd1 hdc]
    exact Item148HJ.residual_isPerfect L d
  have hB : IsHyperplane A (Subgroup.closure {c, d}) :=
    isHyperplane_closure_cd h hJ hdAL.1 hd1 hdc
  have hcfg : IsLBConfig A (Subgroup.closure {c, d}) c d L :=
    isLBConfig_closure_cd_of_threeCentral h hJ hdc
  have hL₀Δ : L₀ ≤ delta A (lB A) L₀ := by
    rw [hL₀]
    exact lB_le_delta_lB h.toSec14Std hB hcfg
  have hL₀6 : Sec4.IsTripleCover (↥L₀ ⧸ CFSG.pCore 2 ↥L₀) (alternatingGroup (Fin 6)) := by
    rw [hL₀]
    exact isTripleCover_lB h.toSec14Std hB hcfg
  have hZL₀ : omegaOneZ S ≤ Subgroup.centralizer (L₀ : Set G) :=
    hZ.trans (Subgroup.centralizer_le fun x hx => hLY hx)
  have hZd : omegaOneZ S ≤ Subgroup.centralizer ({d} : Set G) :=
    hZ.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (hLY hdL₀)))
  exact le_M_of_commutator_le_pCoreOf h (h155 G A c L h.toSec15R) hdAL.1 hd1 hL₀d
    hL₀perf (le_normalizer_lB_closure h hJ hdAL.1 hd1 hdc) hL₀Δ hL₀6 hKQ hKCd
    (commutator_lB_le_pCoreOf h hJ hKd hdAL.1 hd1 hdc hPQ hKCd) hR2 hRQ
    (hKP.trans hPN) hZR₂ hZ1 hAZ hZL₀ hZd

end CFSG.RankThree.PartTwo.Sec16.Ctr166
