module

import CFSG.RankThree.PartOne.N143.T2CenLie
import CFSG.Quasithin.Background.A318PL3Inst
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankFourLin
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevSigma
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossOmega
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankFourOrth

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup TauCeti
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.GroupTheory.WeirSylow

namespace K1Lin

theorem pRank_three_projSL_le_two {F : Type} [Field F] [Finite F] (hF : ¬ 3 ∣ Nat.card F)
    {n : ℕ} (hn3 : ¬ 3 ∣ n) (hlt : n / orderOf (Nat.card F : ZMod 3) < 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n F))) ≤ 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  have hF' : ¬ 3 ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hmod : Fintype.card F % 3 = 1 ∨ Fintype.card F % 3 = 2 := by
    have hlt3 : Fintype.card F % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have h0 : Fintype.card F % 3 ≠ 0 := fun h => hF' (Nat.dvd_of_mod_eq_zero h)
    omega
  have hepos : 0 < orderOf (Fintype.card F : ZMod 3) := by
    rcases hmod with h | h
    · have he : orderOf (Fintype.card F : ZMod 3) = 1 := by
        rw [orderOf_eq_one_iff, ← ZMod.natCast_mod, h]; rfl
      omega
    · have h2 : (Fintype.card F : ZMod 3) = 2 := by rw [← ZMod.natCast_mod, h]; rfl
      have he : orderOf (Fintype.card F : ZMod 3) = 2 := by
        rw [h2]
        exact orderOf_eq_prime (by decide) (by decide)
      omega
  have hqa : 1 ≤ padicValNat 3 (Fintype.card F ^ orderOf (Fintype.card F : ZMod 3) - 1) := by
    refine one_le_padicValNat_of_dvd ?_ ?_
    · have h1 : 1 < Fintype.card F ^ orderOf (Fintype.card F : ZMod 3) := by
        calc 1 < Fintype.card F := hq
          _ = Fintype.card F ^ 1 := (pow_one _).symm
          _ ≤ Fintype.card F ^ orderOf (Fintype.card F : ZMod 3) :=
            Nat.pow_le_pow_right (by omega) hepos
      omega
    · have h1 : ((Fintype.card F : ZMod 3) ^ orderOf (Fintype.card F : ZMod 3)) = 1 :=
        pow_orderOf_eq_one _
      have h2 : ((Fintype.card F ^ orderOf (Fintype.card F : ZMod 3) - 1 : ℕ) : ZMod 3) = 0 := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, h1, Nat.cast_one, sub_self]
      exact (ZMod.natCast_eq_zero_iff
        (Fintype.card F ^ orderOf (Fintype.card F : ZMod 3) - 1) 3).1 h2
  have hGL : CFSG.Open.pRank 3 (⊤ : Subgroup (GL (Fin n) F)) =
      n / orderOf (Fintype.card F : ZMod 3) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.RankChevProof.pRank_eq_of_sylow_sigmaModel (p := 3)
      (e := orderOf (Fintype.card F : ZMod 3))
      (a := padicValNat 3 (Fintype.card F ^ orderOf (Fintype.card F : ZMod 3) - 1))
      (N := n) (by omega)
      (fun P => CFSG.GroupTheory.WeirSylow.sylow_GL (p := 3) (by decide) F hF' n P)
  have hSL : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSL n F)) ≤
      n / orderOf (Fintype.card F : ZMod 3) :=
    (CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num)
      (StatedSL n F).subtype Subtype.val_injective).trans_eq hGL
  have hker : ¬ 3 ∣ Nat.card ↥(QuotientGroup.mk'
      ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F))).ker :=
    CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.ProjLin.not_three_dvd_card_ker hn3
      (StatedSL n F) fun g hg => CFSG.Open.StatedAPI.det_of_mem_statedSL hg
  have hN : ¬ 3 ∣ Nat.card ↥((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) := by
    rwa [QuotientGroup.ker_mk'] at hker
  have hquot : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n F))) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSL n F)) :=
    CFSG.SectionRank.pRank_quotient_eq ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) hN
  rw [hquot]
  have hlt' : n / orderOf (Fintype.card F : ZMod 3) < 3 := by
    rwa [Nat.card_eq_fintype_card] at hlt
  omega

theorem pRank_three_projSU_le_two {L : Type} [Field L] [Finite L] {ℓ f n : ℕ}
    (hL : Nat.card L = (ℓ ^ f) ^ 2) (hq3 : ¬ 3 ∣ ℓ ^ f) (hn : 1 ≤ n) (hn3 : ¬ 3 ∣ n)
    (hlt : n / orderOf (-((ℓ ^ f : ℕ) : ZMod 3)) < 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n (ℓ ^ f) L))) ≤ 2 := by
  haveI : Fintype L := Fintype.ofFinite L
  have hLc : Fintype.card L = (ℓ ^ f) ^ 2 := by rwa [← Nat.card_eq_fintype_card]
  have hq2 : 2 ≤ ℓ ^ f := by
    have h1 : 2 ≤ (ℓ ^ f) ^ 2 := by rw [← hLc]; exact Fintype.one_lt_card
    nlinarith [Nat.zero_le (ℓ ^ f)]
  have ha : 1 ≤ padicValInt 3 ((-((ℓ ^ f : ℕ) : ℤ)) ^
      orderOf (-(((ℓ ^ f : ℕ)) : ZMod 3)) - 1) := by
    have hc : ¬ ((3 : ℕ) : ℤ) ∣ -((ℓ ^ f : ℕ) : ℤ) := by
      rw [dvd_neg]
      exact_mod_cast hq3
    have hc2 : 2 ≤ |-((ℓ ^ f : ℕ) : ℤ)| := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      exact_mod_cast hq2
    have hpos : 0 < orderOf (-(((ℓ ^ f : ℕ)) : ZMod 3)) := by
      rw [← ordMod_neg_natCast]
      exact ordMod_pos hc
    have hdvd : ((3 : ℕ) : ℤ) ∣ (-((ℓ ^ f : ℕ) : ℤ)) ^
        orderOf (-(((ℓ ^ f : ℕ)) : ZMod 3)) - 1 := by
      rw [dvd_pow_sub_one_iff, ordMod_neg_natCast]
    have hne := pow_sub_one_ne_zero hc2 hpos.ne'
    exact one_le_padicValNat_of_dvd (by simpa using hne) (Int.natCast_dvd.1 hdvd)
  have hGU : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(CFSG.Quasithin.StatedGU n (ℓ ^ f) L)) =
      n / orderOf (-(((ℓ ^ f : ℕ)) : ZMod 3)) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.RankChevProof.pRank_eq_of_sylow_sigmaModel (p := 3)
      (e := orderOf (-(((ℓ ^ f : ℕ)) : ZMod 3)))
      (a := padicValInt 3 ((-((ℓ ^ f : ℕ) : ℤ)) ^
        orderOf (-(((ℓ ^ f : ℕ)) : ZMod 3)) - 1))
      (N := n) ha
      (fun P => CFSG.GroupTheory.WeirSylow.sylow_GU (p := 3) (by decide) L hLc hq3 hn P)
  have hSU : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSU n (ℓ ^ f) L)) ≤
      n / orderOf (-(((ℓ ^ f : ℕ)) : ZMod 3)) :=
    (CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num)
      (Subgroup.inclusion
        CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.statedSU_le_statedGU)
      (Subgroup.inclusion_injective _)).trans_eq hGU
  have hker : ¬ 3 ∣ Nat.card ↥(QuotientGroup.mk'
      ((StatedScalars (Fin n) L).subgroupOf (StatedSU n (ℓ ^ f) L))).ker :=
    CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.ProjLin.not_three_dvd_card_ker hn3
      (StatedSU n (ℓ ^ f) L) fun g hg => CFSG.Open.StatedAPI.det_of_mem_statedSU hg
  have hN : ¬ 3 ∣ Nat.card ↥((StatedScalars (Fin n) L).subgroupOf (StatedSU n (ℓ ^ f) L)) := by
    rwa [QuotientGroup.ker_mk'] at hker
  have hquot : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n (ℓ ^ f) L))) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSU n (ℓ ^ f) L)) :=
    CFSG.SectionRank.pRank_quotient_eq
      ((StatedScalars (Fin n) L).subgroupOf (StatedSU n (ℓ ^ f) L)) hN
  rw [hquot]
  omega

theorem pRank_three_projSp_two_le_two {F : Type} [Field F] [Finite F] (hF : ¬ 3 ∣ Nat.card F) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp 2 F))) ≤ 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  have hF' : ¬ 3 ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hmod : Fintype.card F % 3 = 1 ∨ Fintype.card F % 3 = 2 := by
    have hlt3 : Fintype.card F % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have h0 : Fintype.card F % 3 ≠ 0 := fun h => hF' (Nat.dvd_of_mod_eq_zero h)
    omega
  have hepos : 0 < orderOf (Fintype.card F : ZMod 3) := by
    rcases hmod with h | h
    · have he : orderOf (Fintype.card F : ZMod 3) = 1 := by
        rw [orderOf_eq_one_iff, ← ZMod.natCast_mod, h]; rfl
      omega
    · have h2 : (Fintype.card F : ZMod 3) = 2 := by rw [← ZMod.natCast_mod, h]; rfl
      have he : orderOf (Fintype.card F : ZMod 3) = 2 := by
        rw [h2]
        exact orderOf_eq_prime (by decide) (by decide)
      omega
  have hqa : 1 ≤ padicValNat 3 (Fintype.card F ^ orderOf (Fintype.card F : ZMod 3) - 1) := by
    refine one_le_padicValNat_of_dvd ?_ ?_
    · have h1 : 1 < Fintype.card F ^ orderOf (Fintype.card F : ZMod 3) := by
        calc 1 < Fintype.card F := hq
          _ = Fintype.card F ^ 1 := (pow_one _).symm
          _ ≤ Fintype.card F ^ orderOf (Fintype.card F : ZMod 3) :=
            Nat.pow_le_pow_right (by omega) hepos
      omega
    · have h1 : ((Fintype.card F : ZMod 3) ^ orderOf (Fintype.card F : ZMod 3)) = 1 :=
        pow_orderOf_eq_one _
      have h2 : ((Fintype.card F ^ orderOf (Fintype.card F : ZMod 3) - 1 : ℕ) : ZMod 3) = 0 := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, h1, Nat.cast_one, sub_self]
      exact (ZMod.natCast_eq_zero_iff
        (Fintype.card F ^ orderOf (Fintype.card F : ZMod 3) - 1) 3).1 h2
  have hSp : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSp 2 F)) ≤ 2 := by
    rcases hmod with h | h
    · have he : orderOf (Fintype.card F : ZMod 3) = 1 := by
        rw [orderOf_eq_one_iff, ← ZMod.natCast_mod, h]; rfl
      have hrank := CFSG.LocalAnalysis.RankThreeUC.S15.RankChevProof.pRank_eq_of_sylow_sigmaModel
        (p := 3) (e := orderOf (Fintype.card F : ZMod 3))
        (a := padicValNat 3 (Fintype.card F ^ orderOf (Fintype.card F : ZMod 3) - 1))
        (N := if Even (orderOf (Fintype.card F : ZMod 3)) then 2 * 2 else 2) hqa
        (fun P => CFSG.GroupTheory.WeirSylow.sylow_Sp (p := 3) (by decide) F hF' 2 P)
      rw [hrank, he]
      norm_num
    · have h2 : (Fintype.card F : ZMod 3) = 2 := by rw [← ZMod.natCast_mod, h]; rfl
      have he : orderOf (Fintype.card F : ZMod 3) = 2 := by
        rw [h2]
        exact orderOf_eq_prime (by decide) (by decide)
      have hrank := CFSG.LocalAnalysis.RankThreeUC.S15.RankChevProof.pRank_eq_of_sylow_sigmaModel
        (p := 3) (e := orderOf (Fintype.card F : ZMod 3))
        (a := padicValNat 3 (Fintype.card F ^ orderOf (Fintype.card F : ZMod 3) - 1))
        (N := if Even (orderOf (Fintype.card F : ZMod 3)) then 2 * 2 else 2) hqa
        (fun P => CFSG.GroupTheory.WeirSylow.sylow_Sp (p := 3) (by decide) F hF' 2 P)
      rw [hrank, he]
      norm_num
  have hker : ¬ 3 ∣ Nat.card ↥(QuotientGroup.mk'
      ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F))).ker := by
    refine CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.CrossOmega.not_dvd_card_ker_of_sq
      Nat.prime_three (by norm_num) _ fun x hx => ?_
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hx)
    have hc2 : c ^ 2 = 1 :=
      (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff (n := 2) (by norm_num) c).1
        (by rw [hc]; exact x.2)
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, ← map_pow, hc2, map_one, Subgroup.coe_one]
  have hN : ¬ 3 ∣ Nat.card ↥((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)) := by
    rwa [QuotientGroup.ker_mk'] at hker
  have hquot : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp 2 F))) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSp 2 F)) :=
    CFSG.SectionRank.pRank_quotient_eq
      ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)) hN
  rw [hquot]
  exact hSp

end K1Lin

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
  (four_le_pRank_projSL_of_eight_le four_le_pRank_projSU_of_dvd_add four_le_pRank_three_orth
   four_le_pRank_projSL_of_dvd four_le_pRank_projSU_of_dvd_sub four_le_pRank_projSp_of_four_le)

private abbrev CrossCharConcl (X : Type) [Group X] : Prop :=
  LieModel X .PSp 2 3 1 ∨
    ((∃ p f : ℕ, p ≠ 3 ∧ LieModel X .PSp 3 p f) ∨
      (∃ p f : ℕ, p ≠ 3 ∧ LieModel X .POmegaMinus 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel X .PSL 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ p ^ f ≠ 2 ∧ LieModel X .PSU 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel X .PSL 6 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel X .PSU 6 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel X .PSL 7 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel X .PSU 7 p f) ∨
      (∃ p f : ℕ, p ≠ 3 ∧ LieModel X .POmegaOdd 3 p f))

private theorem pRank_three_statedPSL_le_two_of_le_five {X : Type} [Group X] [Finite X]
    {p f n : ℕ} (hm : StatedClassicalModel X .PSL n p f)
    (hn5 : n ≤ 5) (hn3 : ¬ 3 ∣ n) (hp3 : ¬ 3 ∣ p ^ f) (hmod : p ^ f % 3 = 2) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
  obtain ⟨-, F, hFld, hFin, hF, ⟨φ⟩⟩ := hm
  have hF3 : ¬ 3 ∣ Nat.card F := by rw [hF]; exact hp3
  have hcast : (Nat.card F : ZMod 3) = 2 := by
    rw [hF, ← ZMod.natCast_mod, hmod]; rfl
  have hord : orderOf (Nat.card F : ZMod 3) = 2 := by
    rw [hcast]
    exact orderOf_eq_prime (by decide) (by decide)
  have hlt : n / orderOf (Nat.card F : ZMod 3) < 3 := by rw [hord]; omega
  have hle := K1Lin.pRank_three_projSL_le_two (n := n) hF3 hn3 hlt
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) φ]
  exact hle

private theorem pRank_three_statedPSU_le_two_of_four_five {X : Type} [Group X] [Finite X]
    {p f n : ℕ} (hm : StatedClassicalModel X .PSU n p f) (hn : 4 ≤ n) (hn5 : n ≤ 5)
    (hp3 : ¬ 3 ∣ p ^ f) (hmod : p ^ f % 3 = 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
  obtain ⟨-, F, hFld, hFin, hF, ⟨φ⟩⟩ := hm
  have hq1c : ((p ^ f : ℕ) : ZMod 3) = 1 := by
    rw [← ZMod.natCast_mod, hmod]; rfl
  have hneg : -((p ^ f : ℕ) : ZMod 3) = 2 := by rw [hq1c]; decide
  have hord : orderOf (-((p ^ f : ℕ) : ZMod 3)) = 2 := by
    rw [hneg]
    exact orderOf_eq_prime (by decide) (by decide)
  have hlt : n / orderOf (-((p ^ f : ℕ) : ZMod 3)) < 3 := by rw [hord]; omega
  have hle := K1Lin.pRank_three_projSU_le_two (n := n) hF hp3 (by omega) (by omega) hlt
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) φ]
  exact hle

private theorem not_three_dvd_and_mod_three {q : PrimePower} (hp3 : q.p ≠ 3) :
    ¬ 3 ∣ q.p ^ q.exponent ∧ (q.card % 3 = 1 ∨ q.card % 3 = 2) := by
  have hq3 : ¬ 3 ∣ q.p ^ q.exponent := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  rw [PrimePower.card_def]
  exact ⟨hq3, by omega⟩

private theorem crossChar_A_mod1_ge_four (X : Type) [Group X] [Finite X] (r : ℕ)
    (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.A r q, hv⟩).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3) (hr : 4 ≤ r)
    (hdvd : 3 ∣ q.p ^ q.exponent - 1) : CrossCharConcl X := by
  obtain ⟨-, F, hFld, hFin, hF, ⟨φ⟩⟩ :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  have hdvdF : 3 ∣ Nat.card F - 1 := by rw [hF]; exact hdvd
  exfalso
  have h4 := four_le_pRank_projSL_of_dvd (n := r + 1) (by omega) hdvdF
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) φ] at hrk
  omega

private theorem crossChar_A_mod1 (X : Type) [Group X] [Finite X] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.A r q, hv⟩).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (hr : 2 ≤ r) (hq1 : q.card % 3 = 1) : CrossCharConcl X := by
  have hq1' : q.p ^ q.exponent % 3 = 1 := by rwa [← PrimePower.card_def]
  have hdvd1 : 3 ∣ q.card - 1 := by omega
  have hdvd1' : 3 ∣ q.p ^ q.exponent - 1 := by rwa [PrimePower.card_def] at hdvd1
  rcases Nat.lt_or_ge r 3 with hr2 | hr2
  · have hr2' : r = 2 := by omega
    subst r
    have h2 := CFSG.RankThree.PartOne.N143.T2.pRank_three_le_two_of_lie_cover
      (d := ⟨.A 2 q, hv⟩) (Or.inl ⟨q, rfl, hdvd1⟩) e
    exfalso; omega
  rcases Nat.lt_or_ge r 4 with hr3 | hr3
  · have hr3' : r = 3 := by omega
    subst r
    have hm : StatedClassicalModel X .PSL 4 q.p q.exponent :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    right; right; right; left
    exact ⟨q.p, q.exponent, hq1', Or.inl ⟨by decide, hm⟩⟩
  · exact crossChar_A_mod1_ge_four X r q hv e hrk hr3 hdvd1'

private theorem crossChar_A_mod2 (X : Type) [Group X] [Finite X] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.A r q, hv⟩).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (hr : 2 ≤ r) (hq2 : q.card % 3 = 2) (hq3' : ¬ 3 ∣ q.p ^ q.exponent) :
    CrossCharConcl X := by
  have hq2' : q.p ^ q.exponent % 3 = 2 := by rwa [← PrimePower.card_def]
  rcases Nat.lt_or_ge r 3 with hr2 | hr2
  · have hr2' : r = 2 := by omega
    subst r
    have hm : StatedClassicalModel X .PSL 3 q.p q.exponent :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    have h1 := CFSG.Quasithin.A318P.pRank_three_le_one_linear hm hq2'
    exfalso; omega
  rcases Nat.lt_or_ge r 5 with hr4 | hr4
  · have hle := pRank_three_statedPSL_le_two_of_le_five (n := r + 1)
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e)
      (by omega) (by omega) hq3' hq2'
    exfalso; omega
  rcases Nat.lt_or_ge r 6 with hr5 | hr5
  · have hr5' : r = 5 := by omega
    subst r
    have hm : StatedClassicalModel X .PSL 6 q.p q.exponent :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    right; right; right; right; right; left
    exact ⟨q.p, q.exponent, hq2', Or.inl ⟨by decide, hm⟩⟩
  rcases Nat.lt_or_ge r 7 with hr6 | hr6
  · have hr6' : r = 6 := by omega
    subst r
    have hm : StatedClassicalModel X .PSL 7 q.p q.exponent :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    right; right; right; right; right; right; right; left
    exact ⟨q.p, q.exponent, hq2', Or.inl ⟨by decide, hm⟩⟩
  · obtain ⟨-, F, _, _, _, ⟨φ⟩⟩ :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    exfalso
    have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL (r + 1) F))) :=
      four_le_pRank_projSL_of_eight_le (n := r + 1) (by omega)
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) φ] at hrk
    omega

private theorem crossChar_A (X : Type) [Group X] [Finite X] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.A r q, hv⟩).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (hch : (LieTypeIndex.A r q).characteristic ≠ 3) : CrossCharConcl X := by
  have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_A] using hch
  obtain ⟨hq3', hmod⟩ := not_three_dvd_and_mod_three hp3
  have hr1 : 1 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1 |>.1
  rcases Nat.lt_or_ge r 2 with hr | hr
  · have hr1' : r = 1 := by omega
    subst r
    obtain ⟨-, F, hFld, hFin, hF, ⟨φ⟩⟩ :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    have hF3 : ¬ 3 ∣ Nat.card F := by rw [hF]; exact hq3'
    have hlt : (2 : ℕ) / orderOf (Nat.card F : ZMod 3) < 3 := by
      have hle := Nat.div_le_self 2 (orderOf (Nat.card F : ZMod 3))
      omega
    exfalso
    have hle := K1Lin.pRank_three_projSL_le_two (n := 2) hF3 (by norm_num) hlt
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) φ] at hrk
    omega
  rcases hmod with hq1 | hq2
  · exact crossChar_A_mod1 X r q hv e hrk hr hq1
  · exact crossChar_A_mod2 X r q hv e hrk hr hq2 hq3'

private theorem crossChar_twistedA_mod1_ge_seven (X : Type) [Group X] [Finite X] (r : ℕ)
    (q : PrimePower) (hv : (LieTypeIndex.twistedA r q).Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3) (hr : 7 ≤ r)
    (hq1 : q.p ^ q.exponent % 3 = 1) : CrossCharConcl X := by
  obtain ⟨-, F, hFld, hFin, hF, ⟨φ⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : CharP F q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
      (k := q.exponent * 2) (by have := q.exponent_pos; omega) (by rw [hF, ← pow_mul])
  exfalso
  have h4 := four_le_pRank_projSU_of_dvd_sub hF (n := r + 1) (by omega) hq1
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) φ] at hrk
  omega

private theorem crossChar_twistedA_mod2_ge_four (X : Type) [Group X] [Finite X] (r : ℕ)
    (q : PrimePower) (hv : (LieTypeIndex.twistedA r q).Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3) (hr : 4 ≤ r)
    (hdvd : 3 ∣ q.p ^ q.exponent + 1) : CrossCharConcl X := by
  obtain ⟨-, F, hFld, hFin, hF, ⟨φ⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  exfalso
  have h4 := four_le_pRank_projSU_of_dvd_add hF (n := r + 1) (by omega) hdvd
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) φ] at hrk
  omega

private theorem crossChar_twistedA_mod1 (X : Type) [Group X] [Finite X] (r : ℕ)
    (q : PrimePower) (hv : (LieTypeIndex.twistedA r q).Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3) (hr : 3 ≤ r)
    (hq1 : q.card % 3 = 1) (hq3' : ¬ 3 ∣ q.p ^ q.exponent) : CrossCharConcl X := by
  have hq1' : q.p ^ q.exponent % 3 = 1 := by rwa [← PrimePower.card_def]
  rcases Nat.lt_or_ge r 5 with hr4 | hr4
  · have hle := pRank_three_statedPSU_le_two_of_four_five (n := r + 1)
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)
      (by omega) (by omega) hq3' hq1'
    exfalso; omega
  rcases Nat.lt_or_ge r 6 with hr5 | hr5
  · have hr5' : r = 5 := by omega
    subst r
    have hm : StatedClassicalModel X .PSU 6 q.p q.exponent :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv e
    right; right; right; right; right; right; left
    exact ⟨q.p, q.exponent, hq1', Or.inl ⟨by decide, hm⟩⟩
  rcases Nat.lt_or_ge r 7 with hr6 | hr6
  · have hr6' : r = 6 := by omega
    subst r
    have hm : StatedClassicalModel X .PSU 7 q.p q.exponent :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 6 q hv e
    right; right; right; right; right; right; right; right; left
    exact ⟨q.p, q.exponent, hq1', Or.inl ⟨by decide, hm⟩⟩
  · exact crossChar_twistedA_mod1_ge_seven X r q hv e hrk hr6 hq1'

private theorem crossChar_twistedA_mod2 (X : Type) [Group X] [Finite X] (r : ℕ)
    (q : PrimePower) (hv : (LieTypeIndex.twistedA r q).Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3) (hr : 3 ≤ r)
    (hq2 : q.card % 3 = 2) (hq3' : ¬ 3 ∣ q.p ^ q.exponent) : CrossCharConcl X := by
  have hq2' : q.p ^ q.exponent % 3 = 2 := by rwa [← PrimePower.card_def]
  have hdvd2 : 3 ∣ q.card + 1 := by omega
  have hdvd2' : 3 ∣ q.p ^ q.exponent + 1 := by rwa [PrimePower.card_def] at hdvd2
  rcases Nat.lt_or_ge r 4 with hr3 | hr4
  · have hr3' : r = 3 := by omega
    subst r
    by_cases hqcard : q.card = 2
    · have hcard : q.p ^ q.exponent = 2 := by
        rw [← PrimePower.card_def]; exact hqcard
      obtain ⟨hp2, hexp⟩ := Nat.prime_two.pow_eq_iff.1 hcard
      have hm : StatedClassicalModel X .PSU 4 q.p q.exponent :=
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
      have hm2 : LieModel X .PSU 4 2 1 := by
        have h : LieModel X .PSU 4 q.p q.exponent := Or.inl ⟨by decide, hm⟩
        rwa [hp2, hexp] at h
      exact Or.inl (CFSG.GH74.Exceptional.lieModel_PSp_two_three_of_lieModel_PSU_four_two hm2)
    · have hm : StatedClassicalModel X .PSU 4 q.p q.exponent :=
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
      have hne : q.p ^ q.exponent ≠ 2 := by
        rw [← PrimePower.card_def]; exact hqcard
      right; right; right; right; left
      exact ⟨q.p, q.exponent, hq2', hne, Or.inl ⟨by decide, hm⟩⟩
  · exact crossChar_twistedA_mod2_ge_four X r q hv e hrk hr4 hdvd2'

private theorem crossChar_twistedA (X : Type) [Group X] [Finite X] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (hch : (LieTypeIndex.twistedA r q).characteristic ≠ 3) : CrossCharConcl X := by
  have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_twistedA] using hch
  obtain ⟨hq3', hmod⟩ := not_three_dvd_and_mod_three hp3
  have hr2 : 2 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1 |>.1
  rcases Nat.lt_or_ge r 3 with hr | hr
  · have hr2' : r = 2 := by omega
    subst r
    rcases hmod with hq1 | hq2
    · have hm : StatedClassicalModel X .PSU 3 q.p q.exponent :=
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      have hq1' : q.p ^ q.exponent % 3 = 1 := by rwa [← PrimePower.card_def]
      have h1 := CFSG.Quasithin.A318P.pRank_three_le_one_unitary hm hq1'
      exfalso; omega
    · have hdvd2 : 3 ∣ q.card + 1 := by omega
      have h2 := CFSG.RankThree.PartOne.N143.T2.pRank_three_le_two_of_lie_cover
        (d := ⟨.twistedA 2 q, hv⟩) (Or.inr ⟨q, rfl, hdvd2⟩) e
      exfalso; omega
  rcases hmod with hq1 | hq2
  · exact crossChar_twistedA_mod1 X r q hv e hrk hr hq1 hq3'
  · exact crossChar_twistedA_mod2 X r q hv e hrk hr hq2 hq3'

private theorem crossChar_B (X : Type) [Group X] [Finite X] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.B r q).Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.B r q, hv⟩).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (hch : (LieTypeIndex.B r q).characteristic ≠ 3) : CrossCharConcl X := by
  have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_B] using hch
  have hq3' := (not_three_dvd_and_mod_three hp3).1
  have hr2 : 2 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1 |>.1
  rcases Nat.lt_or_ge r 3 with hr | hr
  · have hr2' : r = 2 := by omega
    subst r
    obtain ⟨-, F, hFld, hFin, hF, ⟨φ⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    have hF3 : ¬ 3 ∣ Nat.card F := by rw [hF]; exact hq3'
    exfalso
    have hle := K1Lin.pRank_three_projSp_two_le_two hF3
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) φ] at hrk
    omega
  by_cases hp2 : q.p = 2
  · obtain ⟨-, F, hFld, hFin, hF, ⟨φ⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp2 (by omega) e
    rcases Nat.lt_or_ge r 4 with hr3 | hr4
    · have hr3' : r = 3 := by omega
      subst r
      have hm : StatedClassicalModel X .PSp 3 q.p q.exponent :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hp2 (by norm_num) e
      right; left
      exact ⟨q.p, q.exponent, by omega, Or.inl ⟨by decide, hm⟩⟩
    · exfalso
      have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp r F))) :=
        four_le_pRank_projSp_of_four_le (n := r) hr4
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) φ] at hrk
      omega
  · have hm : StatedClassicalModel X .POmegaOdd r q.p q.exponent :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 (by omega) e
    rcases Nat.lt_or_ge r 4 with hr3 | hr4
    · have hr3' : r = 3 := by omega
      subst r
      right; right; right; right; right; right; right; right; right
      exact ⟨q.p, q.exponent, hp3, Or.inl ⟨by decide, hm⟩⟩
    · exfalso
      have h4 := four_le_pRank_three_orth (hC := hm) (Or.inl ⟨rfl, hr4⟩) hp3
      omega

private theorem crossChar_C (X : Type) [Group X] [Finite X] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.C r q).Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.C r q, hv⟩).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (hch : (LieTypeIndex.C r q).characteristic ≠ 3) : CrossCharConcl X := by
  have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_C] using hch
  have hr3 : 3 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1 |>.1
  rcases Nat.lt_or_ge r 4 with hr | hr
  · have hr3' : r = 3 := by omega
    subst r
    have hm : StatedClassicalModel X .PSp 3 q.p q.exponent :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC 3 q hv e
    right; left
    exact ⟨q.p, q.exponent, hp3, Or.inl ⟨by decide, hm⟩⟩
  · obtain ⟨-, F, hFld, hFin, hF, ⟨φ⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e
    exfalso
    have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp r F))) :=
      four_le_pRank_projSp_of_four_le (n := r) hr
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) φ] at hrk
    omega

private theorem crossChar_D (X : Type) [Group X] [Finite X] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.D r q).Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.D r q, hv⟩).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (hch : (LieTypeIndex.D r q).characteristic ≠ 3) : CrossCharConcl X := by
  have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_D] using hch
  have hr4 : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm : StatedClassicalModel X .POmegaPlus r q.p q.exponent :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
  exfalso
  have h4 := four_le_pRank_three_orth (hC := hm) (Or.inr (Or.inl ⟨rfl, hr4⟩)) hp3
  omega

private theorem crossChar_twistedD (X : Type) [Group X] [Finite X] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (hch : (LieTypeIndex.twistedD r q).characteristic ≠ 3) : CrossCharConcl X := by
  have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_twistedD] using hch
  have hr4 : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases Nat.lt_or_ge r 5 with hr | hr
  · have hr4' : r = 4 := by omega
    subst r
    have hm : StatedClassicalModel X .POmegaMinus 4 q.p q.exponent :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD 4 q hv e
    right; right; left
    exact ⟨q.p, q.exponent, hp3, Or.inl ⟨by decide, hm⟩⟩
  · have hm : StatedClassicalModel X .POmegaMinus r q.p q.exponent :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
    exfalso
    have h4 := four_le_pRank_three_orth (hC := hm) (Or.inr (Or.inr ⟨rfl, hr⟩)) hp3
    omega

theorem k34odd_lie_classical_crossChar
    (X : Type) [Group X] [Finite X] (d : ValidLieTypeIndex)
    (e : X ≃* (CFSGIndex.lie d).Group) (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (hch : d.1.characteristic ≠ 3)
    (hcl : (∃ r q, d.1 = .A r q) ∨ (∃ r q, d.1 = .twistedA r q) ∨ (∃ r q, d.1 = .B r q) ∨
        (∃ r q, d.1 = .C r q) ∨ (∃ r q, d.1 = .D r q) ∨ (∃ r q, d.1 = .twistedD r q)) :
    LieModel X .PSp 2 3 1 ∨
      ((∃ p f : ℕ, p ≠ 3 ∧ LieModel X .PSp 3 p f) ∨
        (∃ p f : ℕ, p ≠ 3 ∧ LieModel X .POmegaMinus 4 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel X .PSL 4 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 2 ∧ p ^ f ≠ 2 ∧ LieModel X .PSU 4 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel X .PSL 6 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel X .PSU 6 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel X .PSL 7 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel X .PSU 7 p f) ∨
        (∃ p f : ℕ, p ≠ 3 ∧ LieModel X .POmegaOdd 3 p f)) := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A r q => exact crossChar_A X r q hv e hrk hch
  | twistedA r q => exact crossChar_twistedA X r q hv e hrk hch
  | B r q => exact crossChar_B X r q hv e hrk hch
  | C r q => exact crossChar_C X r q hv e hrk hch
  | D r q => exact crossChar_D X r q hv e hrk hch
  | twistedD r q => exact crossChar_twistedD X r q hv e hrk hch
  | E6 q => exfalso; simpa using hcl
  | E7 q => exfalso; simpa using hcl
  | E8 q => exfalso; simpa using hcl
  | F4 q => exfalso; simpa using hcl
  | G2 q => exfalso; simpa using hcl
  | twistedE6 q => exfalso; simpa using hcl
  | trialityD4 q => exfalso; simpa using hcl
  | suzuki k => exfalso; simpa using hcl
  | reeG2 k => exfalso; simpa using hcl
  | reeF4 k => exfalso; simpa using hcl
  | tits => exfalso; simpa using hcl

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
