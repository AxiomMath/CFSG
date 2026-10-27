module

import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofSeven
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
public import CFSG.RankThree.PartTwo.Sec16.Item168StepsProofTwo

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Proof168Res2

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem inf_centralizer_mem_scriptQ_of_normal (h : Sec17Std G A c L Y₀) {V : Subgroup G}
    (hV2 : IsPGroup 2 V)
    (hMV : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    V ⊓ Subgroup.centralizer ({c} : Set G) ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := h.le_normalizer_y0.trans hMV
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hcop : ∀ X : Subgroup G, X ≤ V → Nat.Coprime 3 (Nat.card X) := fun X hX => by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hV2.to_le hX)
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have key : ∀ K : Subgroup G, K ≤ Subgroup.normalizer (Y₀ : Set G) →
      V ⊓ K ≤ pPrimeCoreOf 3 K := fun K hK =>
    le_pPrimeCoreOf inf_le_right (le_normalizer_inf (hK.trans hMV) Subgroup.le_normalizer)
      (hcop _ inf_le_left)
  refine mem_scriptQ_iff.mpr ⟨(isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (hcop _ inf_le_left)),
    le_normalizer_inf hAV (h.toSec13Data.A_le_centralizer.trans Subgroup.le_normalizer),
    fun B hB => ?_⟩
  by_cases hcB : c ∈ B
  ·
    have hCB : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)).trans
        (HeadProof.centralizer_c_le_M h)
    exact ((inf_le_inf_right _ inf_le_left).trans (key _ hCB)).trans
      (le_sup_left.trans le_sup_left)
  ·
    have hAcB := Proof169.le_zpowers_sup_of_not_mem hB hcA hcB
    have hCA : Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer (B : Set G) ≤
        Subgroup.centralizer (A : Set G) := by
      rintro x ⟨hxc, hxB⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hsub : Subgroup.zpowers c ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
        · intro z hz
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hxB z hz)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hsub (hAcB hy))
    have hle : V ⊓ Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer (B : Set G) ≤
        V ⊓ Subgroup.centralizer (A : Set G) := by
      rw [inf_assoc]
      exact inf_le_inf_left V hCA
    exact (hle.trans (key _ (HeadProof.centralizer_le_M h))).trans
      (le_sup_right.trans le_sup_left)

theorem mem_scriptQ_of_commutator_of_centralizer (hA : IsE27 A) (h146 : Item146 A (lB A))
    {V : Subgroup G} (hV3 : ¬ 3 ∣ Nat.card V) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hcA : c ∈ A) (hN : ⁅V, Subgroup.zpowers c⁆ ∈ scriptQ A (lB A))
    (hC : V ⊓ Subgroup.centralizer ({c} : Set G) ∈ scriptQ A (lB A)) :
    V ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : V = ⁅V, Subgroup.zpowers c⁆ ⊔ (V ⊓ Subgroup.centralizer ({c} : Set G)) := by
    have h := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three (Subgroup.zpowers c) V (hA.isPGroup.to_le (Subgroup.zpowers_le.mpr hcA))
      hV3 (Subgroup.zpowers_le.mpr (hAV hcA))
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      ← Subgroup.zpowers_eq_closure] at h
  have hCN : V ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer ((⁅V, Subgroup.zpowers c⁆ : Subgroup G) : Set G) :=
    inf_le_left.trans (Subgroup.normalizer_commutator_ge_left V (Subgroup.zpowers c))
  have hsup := sup_mem_scriptQ_of_item146 hA h146 hC hN hCN
  refine mem_scriptQ_of_le hsup ?_ hAV
  calc V = ⁅V, Subgroup.zpowers c⁆ ⊔ (V ⊓ Subgroup.centralizer ({c} : Set G)) := hfac
    _ ≤ (V ⊓ Subgroup.centralizer ({c} : Set G)) ⊔ ⁅V, Subgroup.zpowers c⁆ :=
        sup_le le_sup_right le_sup_left

theorem pCoreOf_M_mem_scriptQ (h : Sec17Std G A c L Y₀) (h146 : Item146 A (lB A))
    (hQ0 : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A))
    (hcomm : omegaA A = {Subgroup.zpowers c} →
      ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)), Subgroup.zpowers c⁆ ∈
        scriptQ A (lB A)) :
    CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  set V := CFSG.Open.pCoreOf 2 M with hVdef
  have hA : IsE27 A := HeadProof.isE27_of_std h
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMV : M ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := h.le_normalizer_y0.trans hMV
  have hV3 : ¬ 3 ∣ Nat.card V := by
    obtain ⟨k, hk⟩ := hV2.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hN : ⁅V, Subgroup.zpowers c⁆ ∈ scriptQ A (lB A) := by
    rcases h.a10_or_omega with hA10 | hΩ
    ·
      have hcY : c ∈ Y₀ := h.le_y0_of_alternating_ten hA10 hcA
      have hY₀V : Y₀ ≤ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer.trans hMV
      have hVY₀ : V ≤ Subgroup.normalizer (Y₀ : Set G) := CFSG.LieType.BorelTits.pCoreOf_le 2 M
      have hle1 : ⁅V, Subgroup.zpowers c⁆ ≤ ⁅V, Y₀⁆ :=
        Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hcY)
      have hle2 : ⁅V, Y₀⁆ ≤ V ⊓ Y₀ := by
        refine le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hY₀V) ?_
        rw [Subgroup.commutator_comm]
        exact Subgroup.le_normalizer_iff_commutator_le_left.mp hVY₀
      have hle3 : V ⊓ Y₀ ≤ CFSG.Open.pCoreOf 2 Y₀ :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
          (le_normalizer_inf hY₀V Subgroup.le_normalizer) (hV2.to_le inf_le_left)
      have hAc : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
        h.toSec13Data.A_le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)
      exact mem_scriptQ_of_le hQ0 (hle1.trans (hle2.trans hle3))
        (le_normalizer_commutator hAV hAc)
    · exact hcomm hΩ
  exact mem_scriptQ_of_commutator_of_centralizer hA h146 hV3 hAV hcA hN
    (inf_centralizer_mem_scriptQ_of_normal h hV2 hMV)

theorem two168Out_of_pCoreOf_mem (h : Sec17Std G A c L Y₀)
    (hst : StellmacherKP) (h146 : Item146 A (lB A))
    (h167 : Item167 A (lB A) c L)
    (hVM : CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) ∈ scriptQ A (lB A)) :
    Two168Out A Y₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro V hV Y hY hVY N hN hYN S hS Y₁ _ _ _ _ _ hOS
  exfalso
  apply hOS
  have hA : IsE27 A := HeadProof.isE27_of_std h
  obtain ⟨hSG, -, -⟩ := Proof168Steps.facts_at_N h hst h146 h167 hV hY hVY hN hYN hS
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  set U := CFSG.Open.pCoreOf 2 M with hUdef
  have hSM : S ≤ M := h.qStar_le S hSG
  have hSU : S ≤ Subgroup.normalizer (U : Set G) :=
    hSM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hSG.prop
  have hU2 : IsPGroup 2 U := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hUSQ : U ⊔ S ∈ scriptQ A (lB A) := by
    rw [sup_comm]
    exact sup_mem_scriptQ_of_item146 hA h146 hSG.prop.1.1 hVM hSU
  have hmem : U ⊔ S ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨hUSQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      (hU2.to_sup_of_normal_left' hS2 hSU)⟩
  exact le_sup_left.trans (hSG.2 hmem le_sup_right)

end Proof168Res2

end CFSG.RankThree.PartTwo.Sec17
