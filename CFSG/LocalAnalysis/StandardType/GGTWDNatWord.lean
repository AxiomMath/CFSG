module

public import CFSG.LocalAnalysis.StandardType.GGTWDCells
public import CFSG.LocalAnalysis.StandardType.GGDepASmallNat
public import Certificates.Data.TwoDepSmallN

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmallN Certificates.DepASmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTWDValid (p N : ℕ) (q : GGDepANPair) : Prop :=
  q.1.length = N ∧ q.2.length = N ∧ ggDepANDot p q.2 q.1 = 2 % p

abbrev ggTWDRflOf (p N : ℕ) (q : GGDepANPair) : Module.End (ZMod p) (GGDepAE p N) :=
  ggDepARefl (ggDepANToZ p N q.1) (ggDepANToZ p N q.2)

@[expose] def ggTWDGens (p N : ℕ) (news : List GGDepANPair) :
    Set (Module.End (ZMod p) (GGDepAE p N)) :=
  Set.range (fun i : Fin (N - 1) => ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
    {s | ∃ q ∈ news, s = ggTWDRflOf p N q}

theorem ggTWDGen_valid {p N : ℕ} [Fact p.Prime] (hN : 5 ≤ N) {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWDValid p N q) {g : ℕ} (hg : g < N - 1 + news.length) :
    GGTWDValid p N (ggTWDGen p N news g) := by
  by_cases h : g + 1 < N
  · have hg' : g < N - 1 := by omega
    have hHlen : (ggDepANH p N g).length = N := l05nNC_H_length p N g
    have hAlen : (ggDepANA p N g).length = N := l05nNC_A_length p N g
    have hH : ggDepANToZ p N (ggDepANH p N g) = ggDepAh p N ⟨g, hg'⟩ :=
      l05nNC_toZ_H (p := p) (N := N) (i := g) h
    have hA : ggDepANToZ p N (ggDepANA p N g) = ggDepAα p N ⟨g, hg'⟩ :=
      l05nNC_toZ_A (p := p) (N := N) (i := g) h
    refine ⟨?_, ?_, ?_⟩
    · simpa [ggTWDGen, if_pos h] using hHlen
    · simpa [ggTWDGen, if_pos h] using hAlen
    · have hdot : ggDepAdot (ggDepANToZ p N (ggDepANA p N g))
          (ggDepANToZ p N (ggDepANH p N g)) = 2 := by
        rw [hA, hH]
        exact l05nNC_pair_i ⟨g, hg'⟩
      have hcast := ggDepANDot_cast (p := p) (N := N) (ggDepANA p N g) (ggDepANH p N g)
        hAlen hHlen
      rw [hdot] at hcast
      have h2 : ((ggDepANDot p (ggDepANA p N g) (ggDepANH p N g) : ℕ) : ZMod p) =
          ((2 % p : ℕ) : ZMod p) := by
        rw [ZMod.natCast_mod]; exact hcast
      rw [ZMod.natCast_eq_natCast_iff'] at h2
      simpa [ggTWDGen, if_pos h, ggDepANDot, Nat.mod_mod] using h2
  · have hk : g + 1 - N < news.length := by omega
    have hmem : news[g + 1 - N] ∈ news := List.getElem_mem hk
    have hq := hnews (news[g + 1 - N]) hmem
    rw [ggTWDGen, if_neg h,
      List.getD_eq_getElem (l := news) (d := ([], [])) (n := g + 1 - N) hk]
    exact hq

theorem ggTWDGen_mem {p N : ℕ} [Fact p.Prime] (hN : 5 ≤ N) {news : List GGDepANPair} {g : ℕ}
    (hg : g < N - 1 + news.length) :
    ggTWDRflOf p N (ggTWDGen p N news g) ∈ Submonoid.closure (ggTWDGens p N news) := by
  by_cases h : g + 1 < N
  · have hg' : g < N - 1 := by omega
    have hH : ggDepANToZ p N (ggDepANH p N g) = ggDepAh p N ⟨g, hg'⟩ :=
      l05nNC_toZ_H (p := p) (N := N) (i := g) h
    have hA : ggDepANToZ p N (ggDepANA p N g) = ggDepAα p N ⟨g, hg'⟩ :=
      l05nNC_toZ_A (p := p) (N := N) (i := g) h
    simp only [ggTWDRflOf, ggTWDGen, if_pos h, hH, hA]
    exact Submonoid.subset_closure (Or.inl ⟨⟨g, hg'⟩, rfl⟩)
  · have hk : g + 1 - N < news.length := by omega
    rw [ggTWDRflOf, ggTWDGen, if_neg h,
      List.getD_eq_getElem (l := news) (d := ([], [])) (n := g + 1 - N) hk]
    exact Submonoid.subset_closure (Or.inr ⟨news[g + 1 - N], List.getElem_mem hk, rfl⟩)

private lemma l05nD2_dot_of_valid {p N : ℕ} [Fact p.Prime] {q : GGDepANPair}
    (h : GGTWDValid p N q) :
    ggDepAdot (ggDepANToZ p N q.2) (ggDepANToZ p N q.1) = 2 := by
  have hcast := ggDepANDot_cast (p := p) (N := N) q.2 q.1 h.2.1 h.1
  rw [h.2.2, ZMod.natCast_mod] at hcast
  exact hcast.symm

private lemma l05nD2_valid_of_dot {p N : ℕ} [Fact p.Prime] {q : GGDepANPair}
    (hq1 : q.1.length = N) (hq2 : q.2.length = N)
    (h : ggDepAdot (ggDepANToZ p N q.2) (ggDepANToZ p N q.1) = 2) :
    ggDepANDot p q.2 q.1 = 2 % p := by
  have hcast := ggDepANDot_cast (p := p) (N := N) q.2 q.1 hq2 hq1
  rw [h] at hcast
  have h2 : ((ggDepANDot p q.2 q.1 : ℕ) : ZMod p) = ((2 % p : ℕ) : ZMod p) := by
    rw [ZMod.natCast_mod]; exact hcast
  rw [ZMod.natCast_eq_natCast_iff'] at h2
  simpa [ggDepANDot, Nat.mod_mod] using h2

private lemma l05nD2_word_cons (p N : ℕ) (news : List GGDepANPair) (q : GGDepANPair) (g : ℕ)
    (w : List ℕ) :
    ggTWDWord p N news q (g :: w) =
      ggDepANConj p (ggTWDWord p N news q w) (ggTWDGen p N news g) := by
  simp [ggTWDWord]

private lemma l05nD2_word {p N : ℕ} [Fact p.Prime] (hN : 5 ≤ N)
    {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWDValid p N q)
    (S : Submonoid (Module.End (ZMod p) (GGDepAE p N)))
    (hmem : ∀ g : ℕ, g < N - 1 + news.length → ggTWDRflOf p N (ggTWDGen p N news g) ∈ S)
    (w : List ℕ) (hw : ∀ g ∈ w, g < N - 1 + news.length)
    (q : GGDepANPair) (hq : GGTWDValid p N q) (hqm : ggTWDRflOf p N q ∈ S) :
    GGTWDValid p N (ggTWDWord p N news q w) ∧ ggTWDRflOf p N (ggTWDWord p N news q w) ∈ S := by
  revert hw q hq hqm
  induction w with
  | nil => intro hw q hq hqm; simpa [ggTWDWord] using ⟨hq, hqm⟩
  | cons g w ih =>
      intro hw q hq hqm
      rw [l05nD2_word_cons]
      have hg : g < N - 1 + news.length := hw g (by simp)
      have hw' : ∀ g' ∈ w, g' < N - 1 + news.length := fun g' hg' => hw g' (by simp [hg'])
      obtain ⟨ihQ, ihM⟩ := ih hw' q hq hqm
      have hG : GGTWDValid p N (ggTWDGen p N news g) := ggTWDGen_valid hN hnews hg
      have hQ1 : (ggTWDWord p N news q w).1.length = N := ihQ.1
      have hQ2 : (ggTWDWord p N news q w).2.length = N := ihQ.2.1
      have hG1 : (ggTWDGen p N news g).1.length = N := hG.1
      have hG2 : (ggTWDGen p N news g).2.length = N := hG.2.1
      have hconj := l05nNC_conj_length (p := p) hQ1 hQ2 hG1 hG2
      have hdq := l05nD2_dot_of_valid ihQ
      have hdg := l05nD2_dot_of_valid hG
      obtain ⟨hc1, hc2⟩ := l05nNC_toZ_conj (p := p) (N := N)
        (q := ggTWDWord p N news q w) (g := ggTWDGen p N news g) hQ1 hQ2 hG1 hG2
      have hc1' : ggDepANToZ p N (ggDepANConj p (ggTWDWord p N news q w) (ggTWDGen p N news g)).1 =
          ggDepANToZ p N (ggTWDWord p N news q w).1 -
            ggDepAdot (ggDepANToZ p N (ggTWDGen p N news g).2)
              (ggDepANToZ p N (ggTWDWord p N news q w).1) •
              ggDepANToZ p N (ggTWDGen p N news g).1 := hc1
      have hc2' : ggDepANToZ p N (ggDepANConj p (ggTWDWord p N news q w) (ggTWDGen p N news g)).2 =
          ggDepANToZ p N (ggTWDWord p N news q w).2 -
            ggDepAdot (ggDepANToZ p N (ggTWDWord p N news q w).2)
              (ggDepANToZ p N (ggTWDGen p N news g).1) •
              ggDepANToZ p N (ggTWDGen p N news g).2 := hc2
      refine ⟨⟨hconj.1, hconj.2, ?_⟩, ?_⟩
      · apply l05nD2_valid_of_dot hconj.1 hconj.2
        rw [hc1', hc2']
        exact l05nNC_conj_dot (ggDepANToZ p N (ggTWDWord p N news q w).1)
          (ggDepANToZ p N (ggTWDWord p N news q w).2)
          (ggDepANToZ p N (ggTWDGen p N news g).1) (ggDepANToZ p N (ggTWDGen p N news g).2)
          hdq hdg
      · simp only [ggTWDRflOf]
        rw [hc1', hc2']
        rw [← l05nNC_refl_conj (ggDepANToZ p N (ggTWDWord p N news q w).1)
          (ggDepANToZ p N (ggTWDWord p N news q w).2)
          (ggDepANToZ p N (ggTWDGen p N news g).1)
          (ggDepANToZ p N (ggTWDGen p N news g).2) hdg]
        exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hmem g hg) ihM) (hmem g hg)

theorem ggTWDWord_valid_mem {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N)
    {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWDValid p N q) {q : GGDepANPair}
    (hq : GGTWDValid p N q) (hqm : ggTWDRflOf p N q ∈ Submonoid.closure (ggTWDGens p N news))
    {w : List ℕ} (hw : ∀ g ∈ w, g < N - 1 + news.length) :
    GGTWDValid p N (ggTWDWord p N news q w) ∧
      ggTWDRflOf p N (ggTWDWord p N news q w) ∈ Submonoid.closure (ggTWDGens p N news) := by
  exact l05nD2_word hN hnews (Submonoid.closure (ggTWDGens p N news))
    (fun g hg => ggTWDGen_mem hN hg) w hw q hq hqm

theorem ggTWDTv_sound {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N)
    {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWDValid p N q) (w : GGDepANWit)
    (hv : ggTWDWitValid (N - 1 + news.length) w = true)
    (ht : ggTWDWitTest p N news w = true) :
    ∃ g ∈ Submonoid.closure (ggTWDGens p N news), GGDepAIsTv g := by
  have hv' := hv
  simp only [ggTWDWitValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv'
  obtain ⟨⟨⟨hvg1, hvg2⟩, hvw1⟩, hvw2⟩ := hv'
  set q1 : GGDepANPair := ggTWDWord p N news (ggTWDGen p N news w.g1) w.w1 with hq1def
  set q2 : GGDepANPair := ggTWDWord p N news (ggTWDGen p N news w.g2) w.w2 with hq2def
  have ht' : ggDepANTestPair p q1 q2 = true := by
    rw [hq1def, hq2def]
    simpa only [ggTWDWitTest] using ht
  have h1 : GGTWDValid p N q1 ∧
      ggTWDRflOf p N q1 ∈ Submonoid.closure (ggTWDGens p N news) :=
    ggTWDWord_valid_mem hp2 hN hnews (ggTWDGen_valid hN hnews hvg1)
      (ggTWDGen_mem hN hvg1) hvw1
  have h2 : GGTWDValid p N q2 ∧
      ggTWDRflOf p N q2 ∈ Submonoid.closure (ggTWDGens p N news) :=
    ggTWDWord_valid_mem hp2 hN hnews (ggTWDGen_valid hN hnews hvg2)
      (ggTWDGen_mem hN hvg2) hvw2
  obtain ⟨hv1, hm1⟩ := h1
  obtain ⟨hv2, hm2⟩ := h2
  have htv := ggDepANTestPair_sound (p := p) (N := N) hp2 q1 q2
    hv1.1 hv1.2.1 hv2.1 hv2.2.1 hv1.2.2 hv2.2.2 ht'
  refine ⟨ggDepARefl (ggDepANToZ p N q1.1) (ggDepANToZ p N q1.2) *
      ggDepARefl (ggDepANToZ p N q2.1) (ggDepANToZ p N q2.2), ?_, ?_⟩
  · exact Submonoid.mul_mem _ hm1 hm2
  · exact htv.2.2

end CFSG.StandardType

end
