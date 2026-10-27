module

import CFSG.Quasithin.Background.A312SporAlt5
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22se
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open scoped commutatorElement
open P22s

variable {G : Type} [Group G] [Finite G]

namespace P22s

theorem ne_bot_of_isQuasisimple {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 L)) : L ≠ ⊥ := by
  intro hbot
  obtain ⟨a, b, hab⟩ := CFSG.LocalCores.isQuasisimple_nontrivial (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq)
  apply hab
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) b
  have ha : (a' : G) = 1 := Subgroup.mem_bot.1 (hbot.le a'.2)
  have hb : (b' : G) = 1 := Subgroup.mem_bot.1 (hbot.le b'.2)
  rw [show a' = b' from Subtype.ext (ha.trans hb.symm)]

theorem mem_cComp_of_mem_calC {L X : Subgroup G} (hL : L ∈ calC X) : L ∈ CFSG.Quasithin.cComp X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsub, hperf, hq⟩ := hL
  refine ⟨ne_bot_of_isQuasisimple hq, hperf, hsub, fun K hKL hKne hKperf hKsub => hKne ?_⟩
  have hKL' : CFSG.Open.IsSubnormal K L :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hKsub hKL.le (isSubnormal_le hsub)
  obtain ⟨P, hPL, hPn, hKP⟩ := CFSG.Quasithin.A3.subnormal_exists_normal_of_lt hKL' hKL
  have hLP : L ≤ normalizer (P : Set G) := (Subgroup.normal_subgroupOf_iff_le_normalizer hPL.le).1 hPn
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq)
      (N := (P.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))
      (hPn.map _ (QuotientGroup.mk'_surjective _)) with htop | hcen
  ·
    exfalso
    refine hPL.ne (le_antisymm hPL.le (le_of_commutator_eq_self (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLP) (fun l hl => ?_) hperf))
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨l, hl⟩ ∈
        (P.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      htop ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hnl⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnl
    have e : l = (n : G) * ((n⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup hn ⟨_, hnl, rfl⟩
  ·
    have hPP : ⁅P, P⁆ ≤ pCoreOf 2 L := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have hca : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨a, hPL.le ha⟩ ∈ Subgroup.center (Bar2 L) :=
        hcen ⟨⟨a, hPL.le ha⟩, ha, rfl⟩
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⁅(⟨a, hPL.le ha⟩ : ↥L), ⟨b, hPL.le hb⟩⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact ((Subgroup.mem_center_iff.1 hca) _).symm
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, by simp [commutatorElement_def]⟩
    have hKO : K ≤ pCoreOf 2 L :=
      calc K = ⁅K, K⁆ := hKperf.symm
        _ ≤ ⁅P, P⁆ := Subgroup.commutator_mono hKP hKP
        _ ≤ pCoreOf 2 L := hPP
    have hK2 : IsPGroup 2 ↥K := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hKO
    haveI := hK2.isNilpotent
    exact CFSG.Quasithin.A312S.eq_bot_of_perfect_of_solvable hKperf inferInstance

theorem le_normalizer_of_mem_calC {L₀ L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ calC L₀) (h₂ : L₂ ∈ calC L₀)
    (heq : L₀ = L₁ ⊔ L₂) : L₀ ≤ normalizer (L₁ : Set G) := by
  have hc₁ := mem_cComp_of_mem_calC h₁
  have hc₂ := mem_cComp_of_mem_calC h₂
  have hspan : CFSG.Quasithin.cCompSpan L₀ = L₀ := by
    refine le_antisymm (sSup_le fun K hK => CFSG.Quasithin.le_of_mem_cComp hK) ?_
    calc L₀ = L₁ ⊔ L₂ := heq
      _ ≤ CFSG.Quasithin.cCompSpan L₀ := sup_le (le_sSup hc₁) (le_sSup hc₂)
  obtain ⟨hle, hn⟩ := CFSG.Quasithin.cComp_normal_span_of_le hc₁
  rw [hspan] at hle hn
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 hn

end P22s

end CFSG.LocalAnalysis.UniquenessCase.UC22
