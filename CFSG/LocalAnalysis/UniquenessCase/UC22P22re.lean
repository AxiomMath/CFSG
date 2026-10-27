module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22r
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ra
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rb
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rd
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p22r_centralizer_mem_hSet (D : Data G) {z : G} (hzZ : z ∈ D.Z) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hC : ¬ centralizer (D.Z : Set G) ≤ D.M) : centralizer ({z} : Set G) ∈ hSet D.T D.M := by
  have hZz : centralizer (D.Z : Set G) ≤ centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzZ)
  refine ⟨?_, fun h => hC (hZz.trans h), D.standing.charTwo _ (uc22p22f_isTwoLocal_centralizer hz1 hz2)⟩
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  rw [hw]
  exact ((CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.1 hzZ).2.1 t ht).symm

theorem uc22p22r_s22_10_of_parts (D : Data G) (Ch : Choice2011 G) (h63 : UC6.R6_3 D)
    (h77 : F07.R77Eq D)
    (hV : S22_V D Ch) (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h8 : S22_8 D Ch) (hne : D.sig.Nonempty) (hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M)
    (hFin : Final2210 D) (hF : Fix108H D) : S22_10 D Ch := by
  have hP := uc22p22r_pgrp2210_holds (D := D) (Ch := Ch)
  have hS := uc22p22r_sym2210_holds (D := D) (Ch := Ch)
  classical
  intro h1930 c q hq hq2 Q hQ hrank
  by_contra hne'
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hPQ, hPq, hPexp, hPcl, hPnc, hPY, hPA⟩ := hP h1930 c q hq hq2 Q hQ hrank hne'
  have hQM : Q ≤ D.M := hQ.le.trans (uc22p21c_barPreimage_le _ _)
  have hPM : P ≤ D.M := hPQ.trans hQM
  have hPcard : q ^ 2 ≤ Nat.card ↥P := by
    obtain ⟨k, hk⟩ := hPq.exists_card_eq
    by_contra hlt
    push Not at hlt
    apply hPnc
    rw [hk] at hlt
    have hk' : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      exact absurd hlt (not_lt.2 (Nat.pow_le_pow_right hq.pos hk2))
    interval_cases k
    · haveI : Subsingleton ↥P := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card (by simpa using hk)
  have hΓP : rankThreeGamma 1 q P ≤ D.M :=
    gam2210_of D Ch h77 hsp h8 hne hrk h1930 c q hq hq2 P hPM hPq hPexp hPcl hPnc hPY
  have hAle : Nat.card ↥(P ⊓ centralizer (c.V : Set G)) ≤ q :=
    uc22p22f_card_cent_le D Ch h63 c hq hq2 hPM hPq hPexp hΓP
  have hAcard : Nat.card ↥(P ⊓ centralizer (c.V : Set G)) = q := by
    obtain ⟨k, hk⟩ := (hPq.to_le (inf_le_left : P ⊓ centralizer (c.V : Set G) ≤ P)).exists_card_eq
    have h1 : 1 < Nat.card ↥(P ⊓ centralizer (c.V : Set G)) :=
      (Subgroup.one_lt_card_iff_ne_bot _).2 hPA
    rw [hk] at h1 hAle ⊢
    have hk1 : 1 ≤ k := by
      by_contra h0
      push Not at h0
      interval_cases k
      simp at h1
    have hk2 : k ≤ 1 := by
      by_contra h2
      push Not at h2
      exact absurd hAle (not_le.2 (lt_of_lt_of_le (by nlinarith [hq.one_lt])
        (Nat.pow_le_pow_right hq.pos h2 : q ^ 2 ≤ q ^ k)))
    have : k = 1 := le_antisymm hk2 hk1
    rw [this, pow_one]
  obtain ⟨z, hzV, hz1, hzZ, hz2⟩ := uc22p22f_exists_z c
  have hH := uc22p22r_centralizer_mem_hSet D hzZ hz1 hz2 c.hC
  have hzA : P ⊓ centralizer (c.V : Set G) ≤ centralizer ({z} : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzV))
  obtain ⟨g₀, hg₀H, hg₀M, hAg₀⟩ := hF h1930 _ hH q hq hq2 _ (le_inf hzA (inf_le_left.trans hPM)) hAcard
    (uc22p22f_permutes_cent D Ch hV h1930 c hPM hPY)
  obtain ⟨g, hgz, hgM, hAgM, hAMg, hneA, hcomm, ⟨k₁, hk₁, hAP₁, hDN⟩, ⟨k₂, hk₂, hAP₂, hAN⟩⟩ :=
    hS h1930 c q hq hq2 P hPM hPq hPY hΓP hAcard z hzV hz1 g₀ hg₀H hg₀M hAg₀
  have hk₁M : k₁ ∈ D.M := Subgroup.map_subtype_le _ hk₁
  have hk₂M : k₂ ∈ D.M := Subgroup.map_subtype_le _ hk₂
  have hPkM : ∀ k ∈ D.M, uniqueFourConj k P ≤ D.M := fun k hk =>
    (uc22p22r_conj_mono hPM k).trans (uc22p22r_conj_self_of_mem D.M hk).le
  have hzA' : ∀ a ∈ P ⊓ centralizer (c.V : Set G), a * z = z * a := fun a ha =>
    (Subgroup.mem_centralizer_iff.1 ha.2 z hzV).symm
  exact hFin q hq hq2 (uniqueFourConj k₁ P) (uniqueFourConj k₂ P) _ g z (hPkM k₁ hk₁M) (hPkM k₂ hk₂M)
    (uc22p22r_isPGroup_conj hPq k₁) (uc22p22r_isPGroup_conj hPq k₂) (uc22p22r_pow_conj hPexp k₁)
    (uc22p22r_pow_conj hPexp k₂) ((uc22p22r_card_conj P k₁).symm ▸ hPcard)
    ((uc22p22r_card_conj P k₂).symm ▸ hPcard) (uc22p22r_gamma_conj hq hk₁M hΓP)
    (uc22p22r_gamma_conj hq hk₂M hΓP) hAcard hAP₁ hAP₂ hz1 (uc22p22f_V_le_pCoreOf c hzV) hzA' hgz hgM
    hneA hcomm hAgM hAMg hDN hAN

theorem uc22p22r_s22_10_of_split (D : Data G) (Ch : Choice2011 G) (h63 : UC6.R6_3 D)
    (h77 : F07.R77Eq D)
    (hV : S22_V D Ch) (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h8 : S22_8 D Ch) (hne : D.sig.Nonempty) (hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M)
    (hF : Fix108H D) : S22_10 D Ch :=
  uc22p22r_s22_10_of_parts D Ch h63 h77 hV hsp h8 hne hrk (uc22p22r_final2210_holds D h63) hF

end CFSG.LocalAnalysis.UniquenessCase.UC22
