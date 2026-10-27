module

public import CFSG.StandardComponent.AschbacherSeitz.AltNF

import CFSG.GroupTheory.PRankLeOfSylowLe

public section

namespace CFSG.StandardComponent.AschbacherSeitz

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
open CFSG.ComponentClassification.RankTwoAlt

theorem isKleinFour_of_isSylowOf_centralizer_alt
    {G : Type} [Group G] [Finite G] {A : Subgroup G} (hH : RankTwoHypNF G A)
    (hO : standardComponentOddCore G = ⊥) {n : ℕ} (hn : 5 ≤ n)
    (hQ : Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin n))) {R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) :
    IsKleinFour R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hQ
  obtain ⟨R₀, T, g, hc⟩ :=
    RankTwoAlt.exists_sec3_of RankTwoFoundation.section3Config
      (RankTwoClassical.hyp31_ofNF hH hO hn e)
  have h32 := RankTwoFoundation.lemma32
  have h332 := RankTwoFoundation.lemma33Two
  have h4 := RankTwoFoundation.asc75Theorem4
  have h2 := RankTwoFoundation.asc76Theorem2
  have h34 := AS76b.asc08Lemma34
  have hcardR₀ : Nat.card R₀ = 4 := by
    rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7 ∨ 8 ≤ n) with rfl | rfl | rfl | hn8
    ·
      have hodd := RankTwoClassical.altEvenCenterSmallNF_of h32 h4 h34
        RankTwoFoundation.section3Config G A hH hO 5 le_rfl (by norm_num) ⟨e⟩
      have hZ := RankTwoAlt.center_eq_bot_of_odd_five hH.standard.1.1 e hodd
      exact (RankTwoAltFive.card_sec3V h32 h332 hc.hyp
        (RankTwoAlt.mulEquivOfCenter hZ e) hc.sylowR hc.not_mem hc.sylowT
        hc.le_centralizer).1
    ·
      have hodd := RankTwoClassical.altEvenCenterSmallNF_of h32 h4 h34
        RankTwoFoundation.section3Config G A hH hO 6 (by norm_num) (by norm_num) ⟨e⟩
      have hZ := RankTwoAlt.altThreeCoverNF_of h32 h4 h34 h2
        RankTwoFoundation.section3Config G A hH hO 6 le_rfl (by norm_num) ⟨e⟩ hodd
      obtain ⟨np⟩ := RankTwoAlt.exists_sixPair hc h32 h4 h34 h2
        (RankTwoAlt.mulEquivOfCenter hZ e)
      let f : ↥R₀ → ↥(RankTwoAlt.rootV 6) := fun r =>
        ⟨np.ψB ⟨r, np.le_B r.2⟩, (np.mem_R ⟨r, np.le_B r.2⟩).mp r.2⟩
      have hf : Function.Bijective f := by
        refine ⟨?_, ?_⟩
        · intro r s hrs
          have h1 := congrArg
            (fun x : ↥(RankTwoAlt.rootV 6) => (x : alternatingGroup (Fin 6))) hrs
          have h2 : (⟨r, np.le_B r.2⟩ : ↥(rightConjugate A g)) =
              ⟨s, np.le_B s.2⟩ := np.ψB.injective h1
          exact Subtype.ext (congrArg (fun x : ↥(rightConjugate A g) => (x : G)) h2)
        · intro v
          let b : ↥(rightConjugate A g) := np.ψB.symm (v : alternatingGroup (Fin 6))
          have hb : (b : G) ∈ R₀ := (np.mem_R b).mpr (by simp [b])
          refine ⟨⟨(b : G), hb⟩, ?_⟩
          apply Subtype.ext
          show np.ψB (⟨(b : G), np.le_B hb⟩ : ↥(rightConjugate A g)) =
            (v : alternatingGroup (Fin 6))
          rw [show (⟨(b : G), np.le_B hb⟩ : ↥(rightConjugate A g)) = b from Subtype.ext rfl,
            MulEquiv.apply_symm_apply]
      have hbij : Nat.card R₀ = Nat.card (RankTwoAlt.rootV 6) :=
        Nat.card_congr (Equiv.ofBijective f hf)
      rw [hbij, RankTwoAlt.nat_card_rootV (by norm_num : 4 ≤ 6)]
    ·
      have hodd := RankTwoClassical.altEvenCenterSmallNF_of h32 h4 h34
        RankTwoFoundation.section3Config G A hH hO 7 (by norm_num) le_rfl ⟨e⟩
      have hZ := RankTwoAlt.altThreeCoverNF_of h32 h4 h34 h2
        RankTwoFoundation.section3Config G A hH hO 7 (by norm_num) le_rfl ⟨e⟩ hodd
      have hOut := RankTwoAlt.odd_card_commutator_outer_of_mulEquiv le_rfl
        (RankTwoAlt.mulEquivOfCenter hZ e)
      let eQuot : ↥A ⧸ center ↥A ≃* alternatingGroup (Fin 7) :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans
          (QuotientGroup.quotientBot.trans (RankTwoAlt.mulEquivOfCenter hZ e))
      obtain ⟨np⟩ := RankTwoAlt.exists_normPair hc h32 h4 h34 h2 hOut le_rfl eQuot hZ
      exact np.card_R (by norm_num)
    ·
      have hperf : commutator ↥A = ⊤ := hH.standard.1.1
      have hOut := RankTwoAlt.odd_card_commutator_outer_of_quot hperf (by omega) e
      obtain ⟨ψ, hψ⟩ := RankTwoSporadic.exists_isActionHom
        (RankTwoAlt.autModel_perm (Or.inr (by omega))) hperf e
      have hZ := RankTwoAlt.center_eq_bot hc h32 h4 h34 h2 hOut (by omega) hψ
      obtain ⟨np⟩ := RankTwoAlt.exists_normPair hc h32 h4 h34 h2 hOut (by omega) e hZ
      exact np.card_R (by omega)
  have hExpR₀ : Monoid.exponent ↥R₀ = 2 := by
    have hdvd : Monoid.exponent ↥R₀ ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one (fun r => by
        have h := (hc.elemR h32).2 (r : G) r.2
        exact Subtype.ext (by simpa using h))
    have hne : Monoid.exponent ↥R₀ ≠ 1 := by
      intro h1
      have hsub : Subsingleton ↥R₀ := Monoid.exp_eq_one_iff.mp h1
      have hle : Nat.card ↥R₀ ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
      omega
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  obtain ⟨c, _, hRc⟩ := IsSylowOf.exists_conj hc.sylowR hR
  have hcardR : Nat.card R = 4 := by
    rw [hRc, Subgroup.card_map_of_injective (MulAut.conj c).injective, hcardR₀]
  have hExpR : Monoid.exponent ↥R = 2 := by
    rw [hRc]
    exact (Monoid.exponent_eq_of_mulEquiv
      (Subgroup.equivMapOfInjective R₀ (MulAut.conj c).toMonoidHom
        (MulAut.conj c).injective).symm).trans hExpR₀
  exact IsKleinFour.mk hcardR hExpR

theorem pRank_centralizer_le_two_of_standard_alt
    {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : standardComponentIsStandard A) (hO : standardComponentOddCore G = ⊥)
    (hN : ¬ A.Normal) {n : ℕ} (hn : 5 ≤ n)
    (hQ : Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin n))) :
    CFSG.Open.pRank 2 (centralizer (A : Set G)) ≤ 2 := by
  classical
  by_contra hle
  have hrank : 2 ≤ CFSG.Open.pRank 2 (centralizer (A : Set G)) := by
    have := not_le.mp hle
    omega
  have hH : RankTwoHypNF G A := ⟨hA, hN, hrank⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 (centralizer (A : Set G))
  have hcardR : Nat.card R = 4 :=
    (isKleinFour_of_isSylowOf_centralizer_alt hH hO hn hQ hR).card_four
  have hrankR : CFSG.Open.pRank 2 R ≤ 2 := by
    refine CFSG.SectionRank.pRank_le (p := 2) (k := 2) (by norm_num) ?_
    intro E hER hE
    have hdvd : Nat.card E ∣ 4 := hcardR ▸ Subgroup.card_dvd_of_le hER
    have hle4 : Nat.card E ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    calc Nat.card E ≤ 4 := hle4
      _ = 2 ^ 2 := by norm_num
  have hCR : CFSG.Open.pRank 2 (centralizer (A : Set G)) ≤ CFSG.Open.pRank 2 R :=
    CFSG.pRank_le_of_isSylowOf_le (X := G) (p := 2)
      (Y := centralizer (A : Set G)) (N₁ := R) (S := R)
      Nat.prime_two hR.le hR le_rfl
  exact hle (hCR.trans hrankR)

end CFSG.StandardComponent.AschbacherSeitz
