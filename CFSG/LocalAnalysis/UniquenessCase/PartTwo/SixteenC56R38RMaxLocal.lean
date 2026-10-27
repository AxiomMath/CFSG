module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.LocalAnalysis.WeakClosure81.SixFifteen
import CFSG.RankThree.PartOne.CTP.StrongPGlue
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

private lemma rankThreeGamma_le_of_isStronglyPEmbedded {M E : Subgroup G}
    (hsp : IsStronglyPEmbedded 3 M) (hEM : E ≤ M) :
    rankThreeGamma 1 3 E ≤ M := by
  unfold rankThreeGamma CFSG.Open.GLBCore
  refine sSup_le ?_
  rintro N ⟨Q, hQE, h1Q, rfl⟩
  intro h hh
  by_contra hhM
  have hQdvd : 3 ∣ Nat.card Q :=
    CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three h1Q
  have hQle : Q ≤ M ⊓ M.map (MulAut.conj h).toMonoidHom := by
    refine le_inf (hQE.trans hEM) ?_
    intro x hx
    refine Subgroup.mem_map.2 ⟨h⁻¹ * x * h, ?_, ?_⟩
    · have hxQ : h⁻¹ * x * h ∈ Q := (Subgroup.mem_normalizer_iff''.1 hh x).1 hx
      exact hEM (hQE hxQ)
    · change (MulAut.conj h) (h⁻¹ * x * h) = x
      rw [MulAut.conj_apply]
      group
  exact (hsp.2.2 h hhM) (hQdvd.trans (Subgroup.card_dvd_of_le hQle))

private lemma isTwoLocal_normalizer_zpowers (v : G) (hv : v ^ 2 = 1) (hv1 : v ≠ 1) :
    IsTwoLocal (normalizer (zpowers v : Set G)) := by
  refine ⟨zpowers v, ?_, ?_, rfl⟩
  · intro hbot
    exact hv1 (Subgroup.zpowers_eq_bot.1 hbot)
  · rw [IsPGroup.iff_card]
    refine ⟨1, ?_⟩
    rw [Nat.card_zpowers, orderOf_eq_prime hv hv1, pow_one]

theorem r38_centralizer_le_of_two_le_pRank (D : Data G) (h63 : UC6.R6_3 D)
    (hsp : IsStronglyPEmbedded 3 D.M) {v : G} (hv : v ^ 2 = 1) (hv1 : v ≠ 1)
    (hrk : 2 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer ({v} : Set G))) :
    centralizer ({v} : Set G) ≤ D.M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E', hE'le, hE'abel, hE'card⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (D.M ⊓ centralizer ({v} : Set G))
  have hE'leM : E' ≤ D.M := fun x hx => (hE'le hx).1
  have hE'leC : E' ≤ centralizer ({v} : Set G) := fun x hx => (hE'le hx).2
  have hdvd : 3 ^ 2 ∣ Nat.card ↥E' := by
    rw [show Nat.card ↥E' = Nat.card E' from rfl, hE'card]
    exact pow_dvd_pow 3 hrk
  obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E') 3 (n := 2) hdvd
  let E : Subgroup G := K.map E'.subtype
  have hEE' : E ≤ E' := by
    dsimp [E]
    exact Subgroup.map_subtype_le K
  have hEcard : Nat.card E = 3 ^ 2 := by
    dsimp [E]
    exact (Subgroup.card_map_of_injective (K := K) (f := E'.subtype)
      E'.subtype_injective).trans hKcard
  have hEabel : CFSG.Open.IsElemAbelian 3 E := hE'abel.mono hEE'
  have hEM : E ≤ D.M := hEE'.trans hE'leM
  have hEC : E ≤ centralizer ({v} : Set G) := hEE'.trans hE'leC
  have hEH : E ≤ normalizer (zpowers v : Set G) :=
    hEC.trans (CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers v)
  have hΓ : rankThreeGamma 1 3 E ≤ D.M :=
    rankThreeGamma_le_of_isStronglyPEmbedded hsp hEM
  have hU : calMOf E = {D.M} := h63 3 Nat.prime_three (by norm_num) E hEM hEabel hEcard hΓ
  obtain ⟨N, hNmax, hHN⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.exists_maxTwoLocal_ge
      (isTwoLocal_normalizer_zpowers v hv hv1)
  have hEN : E ≤ N := hEH.trans hHN
  have hNmem : N ∈ calMOf E := ⟨hNmax, hEN⟩
  rw [hU] at hNmem
  have hN : N = D.M := Set.mem_singleton_iff.1 hNmem
  intro g hg
  have hgH : g ∈ normalizer (zpowers v : Set G) :=
    CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers v hg
  have hgN : g ∈ N := hHN hgH
  rwa [hN] at hgN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
