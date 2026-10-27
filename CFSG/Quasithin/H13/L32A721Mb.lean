module

public import CFSG.Quasithin.H13.L32A715j

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (E : Ctx7153 G T L V (hz T V))
include E

theorem hz_le_mK : hz T V ≤ mK T V := E.hz_le_normalizer_K

theorem t_le_mK : T ≤ mK T V := E.t_le_hz.trans E.hz_le_mK

theorem mK_le_normalizer_l1 : mK T V ≤ Subgroup.normalizer (l1 T L V : Set G) := by
  obtain ⟨-, hL1eq, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  rw [hL1eq]
  exact (normalizer_le_normalizer_o2z _).trans (normalizer_le_normalizer_oTwoUpper _)

theorem l1_le_hz : l1 T L V ≤ hz T V := by
  obtain ⟨hL1K, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  exact hL1K.trans (oTwoUpper_le _)

theorem l1_le_kz_ctx : l1 T L V ≤ kz T V :=
  (lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three).1

theorem V_le_pCoreOf_mK : V ≤ pCoreOf 2 (mK T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h := E.S.hyp
  obtain ⟨-, hV8, hLTV, -, -⟩ := hMod G T L V h.hyp h.fsu
  have hVL1 : V ≤ l1 T L V := by
    have := v_le_l1_of h hMod E.h1222 E.h1332 E.h1334
    rwa [l1_eq_L₁Of] at this
  have hL1V : l1 T L V ≤ Subgroup.normalizer (V : Set G) :=
    ((oTwoUpper_le _).trans inf_le_left).trans (le_sup_left.trans hLTV)
  have hV2 : IsPGroup 2 ↥V := IsPGroup.of_card (n := 3) (by rw [hV8]; norm_num)
  have hVO : V ≤ pCoreOf 2 (l1 T L V) := le_pCoreOf_of_le_normalizer 2 hVL1 hL1V hV2
  refine hVO.trans (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans
    (E.l1_le_hz.trans E.hz_le_mK)) (E.mK_le_normalizer_l1.trans
      (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _))

theorem pCoreOf_mK_ne_bot : pCoreOf 2 (mK T V) ≠ ⊥ := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  obtain ⟨-, hV8, -, -, -⟩ := hMod G T L V E.S.hyp.hyp E.S.hyp.fsu
  intro h0
  have hV := E.V_le_pCoreOf_mK
  rw [h0, le_bot_iff] at hV
  rw [hV, Subgroup.card_bot] at hV8
  norm_num at hV8

theorem isSylowTwoOf_mK : IsSylowTwoOf T (mK T V) := isSylowTwoOf_of_le E.S.hyp E.t_le_mK

theorem sqtk_mK : SQTKGroup ↥(mK T V) :=
  sqtkGroup_of_pCoreOf_ne_bot E.S.hyp.fsu.qtke E.S.hyp.fsu.simple E.S.hyp.fsu.nonabelian
    E.pCoreOf_mK_ne_bot

theorem pRank_gamma_le :
    Open.pRank 3 (⊤ : Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Open.pRank 3 (⊤ : Subgroup ↥(mK T V)) ≤ 2 := E.sqtk_mK.1 3 Nat.prime_three (by norm_num)
  have hN : ¬ 3 ∣ Nat.card ↥(CFSG.pCore 2 ↥(mK T V)) := by
    have hP2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥(mK T V)) := CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  rw [CFSG.SectionRank.pRank_quotient_eq _ hN]
  exact h1

theorem isPOnePlusTwo_kbar : IsPOnePlusTwo 3 ↥(modO2Image (mK T V) (kz T V)) :=
  isPOnePlusTwo_of_mulEquiv (quotEquivStar kz_le_mK le_rfl) (isPOnePlusTwo_K E.three)

omit [Finite G] E in
theorem kbar_normal : (modO2Image (mK T V) (kz T V)).Normal := modO2Image_normal le_rfl

theorem l1bar_normal : (modO2Image (mK T V) (l1 T L V)).Normal :=
  modO2Image_normal E.mK_le_normalizer_l1

theorem max_two_local_of_le (hle : mK T V ≤ hz T V) : quasithinIsMaxTwoLocal (hz T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨fsuV1 T V, ?_, IsPGroup.of_card (n := 1) (by rw [E.card_v1, pow_one]),
    (normalizer_eq_centralizer_of_card_eq_two E.card_v1).symm⟩, fun X hX hHX => ?_⟩
  · intro h0
    have h2 := E.card_v1
    rw [h0, Subgroup.card_bot] at h2
    norm_num at h2
  · obtain ⟨P, hP1, hP2, rfl⟩ := hX
    have hO : pCoreOf 2 (Subgroup.normalizer (P : Set G)) ≠ ⊥ := by
      intro h0
      apply hP1
      have hP : P ≤ pCoreOf 2 (Subgroup.normalizer (P : Set G)) :=
        le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hP2
      rw [h0] at hP
      exact le_bot_iff.mp hP
    have hXK := le_normalizer_K E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.h3x E.S E.three hO
      ((oTwoUpper_le _).trans hHX) (E.t_le_hz.trans hHX)
    exact le_antisymm (hXK.trans hle) hHX

end Ctx7153

end CFSG.Quasithin.H13.L32A
