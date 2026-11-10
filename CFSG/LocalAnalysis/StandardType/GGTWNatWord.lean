module

public import CFSG.LocalAnalysis.StandardType.GGTWNatBase

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTWNValid (p N : ℕ) (q : GGDepANPair) : Prop :=
  q.1.length = N - 1 ∧ q.2.length = N - 1 ∧ ggDepANDot p q.2 q.1 = 2 % p

abbrev ggTWNRflOf (p N : ℕ) (q : GGDepANPair) : Module.End (ZMod p) (GGTWE p N) :=
  ggTWRefl (ggTWNToZ p N q.1) (ggTWNToZ p N q.2)

@[expose] def ggTWNNews (p N : ℕ) (news : List GGDepANPair) : Set (GGTWE p N × GGTWE p N) :=
  {t | ∃ q ∈ news, t = (ggTWNToZ p N q.1, ggTWNToZ p N q.2)}

private lemma l05nE3_cast_sub (p : ℕ) [Fact p.Prime] (x y : ℕ) :
    (((x + (p - y % p)) % p : ℕ) : ZMod p) = (x : ZMod p) - (y : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (le_of_lt (Nat.mod_lt y hp)),
    ZMod.natCast_self, ZMod.natCast_mod]
  ring

private lemma l05nE3_smul_length {p N k : ℕ} {a : List ℕ} (ha : a.length = N) :
    (ggDepANSmul p k a).length = N := by
  simp only [ggDepANSmul, List.length_map, ha]

private lemma l05nE3_sub_length {p N : ℕ} {a b : List ℕ} (ha : a.length = N) (hb : b.length = N) :
    (ggDepANSub p a b).length = N := by
  simp only [ggDepANSub, List.length_zipWith, ha, hb, min_self]

private lemma l05nE3_conj_length {p N : ℕ} {q g : GGDepANPair} (hq1 : q.1.length = N)
    (hq2 : q.2.length = N) (hg1 : g.1.length = N) (hg2 : g.2.length = N) :
    (ggDepANConj p q g).1.length = N ∧ (ggDepANConj p q g).2.length = N := by
  constructor
  · simp only [ggDepANConj]
    exact l05nE3_sub_length hq1 (l05nE3_smul_length hg1)
  · simp only [ggDepANConj]
    exact l05nE3_sub_length hq2 (l05nE3_smul_length hg2)

private lemma l05nE3_toZ_sub {p N : ℕ} [Fact p.Prime] {a b : List ℕ} (ha : a.length = N)
    (hb : b.length = N) :
    ggDepANToZ p N (ggDepANSub p a b) = ggDepANToZ p N a - ggDepANToZ p N b := by
  funext j
  have hj : j.val < N := j.isLt
  have hja : j.val < a.length := by rw [ha]; exact hj
  have hjb : j.val < b.length := by rw [hb]; exact hj
  have hjl : j.val < (a.zipWith (fun x y => (x + (p - y % p)) % p) b).length := by
    rw [List.length_zipWith, ha, hb, min_self]; exact hj
  simp only [ggDepANToZ, ggDepANSub, Pi.sub_apply]
  rw [List.getD_eq_getElem (l := a.zipWith _ b) (d := 0) (n := j.val) hjl,
    List.getD_eq_getElem (l := a) (d := 0) (n := j.val) hja,
    List.getD_eq_getElem (l := b) (d := 0) (n := j.val) hjb]
  rw [List.getElem_zipWith]
  exact l05nE3_cast_sub p _ _

private lemma l05nE3_toZ_smul {p N : ℕ} [Fact p.Prime] {a : List ℕ} (ha : a.length = N) (k : ℕ) :
    ggDepANToZ p N (ggDepANSmul p k a) = (k : ZMod p) • ggDepANToZ p N a := by
  funext j
  have hj : j.val < N := j.isLt
  have hja : j.val < a.length := by rw [ha]; exact hj
  have hjl : j.val < (a.map (fun x => k * x % p)).length := by
    rw [List.length_map, ha]; exact hj
  simp only [ggDepANToZ, ggDepANSmul, Pi.smul_apply, smul_eq_mul]
  rw [List.getD_eq_getElem (l := a.map _) (d := 0) (n := j.val) hjl,
    List.getD_eq_getElem (l := a) (d := 0) (n := j.val) hja]
  rw [List.getElem_map, ZMod.natCast_mod, Nat.cast_mul]

private lemma l05nE3_toZ_conj {p N : ℕ} [Fact p.Prime] {q g : GGDepANPair} (hq1 : q.1.length = N)
    (hq2 : q.2.length = N) (hg1 : g.1.length = N) (hg2 : g.2.length = N) :
    ggDepANToZ p N (ggDepANConj p q g).1 =
        ggDepANToZ p N q.1 - ggDepAdot (ggDepANToZ p N g.2) (ggDepANToZ p N q.1) •
          ggDepANToZ p N g.1 ∧
      ggDepANToZ p N (ggDepANConj p q g).2 =
        ggDepANToZ p N q.2 - ggDepAdot (ggDepANToZ p N q.2) (ggDepANToZ p N g.1) •
          ggDepANToZ p N g.2 := by
  constructor
  · simp only [ggDepANConj]
    rw [l05nE3_toZ_sub hq1 (l05nE3_smul_length hg1), l05nE3_toZ_smul hg1,
      ggDepANDot_cast g.2 q.1 hg2 hq1]
  · simp only [ggDepANConj]
    rw [l05nE3_toZ_sub hq2 (l05nE3_smul_length hg2), l05nE3_toZ_smul hg2,
      ggDepANDot_cast q.2 g.1 hq2 hg1]

private lemma l05nE3_form_apply {p N : ℕ} (f v : GGDepAE p N) :
    ggDepAform f v = ggDepAdot f v := by
  simp [ggDepAform, ggDepAdot]

private lemma l05nE3_refl_apply {p N : ℕ} (c f v : GGDepAE p N) :
    ggDepARefl c f v = v - ggDepAdot f v • c := by
  simp [ggDepARefl, l05nE3_form_apply]

private lemma l05nE3_dot_sub {p N : ℕ} (a v w : GGDepAE p N) :
    ggDepAdot a (v - w) = ggDepAdot a v - ggDepAdot a w := by
  rw [← l05nE3_form_apply a (v - w), map_sub, l05nE3_form_apply a v, l05nE3_form_apply a w]

private lemma l05nE3_dot_smul {p N : ℕ} (a : GGDepAE p N) (k : ZMod p) (v : GGDepAE p N) :
    ggDepAdot a (k • v) = k * ggDepAdot a v := by
  rw [← l05nE3_form_apply a (k • v), map_smul, l05nE3_form_apply a v]
  simp

private lemma l05nE3_dot_sub_left {p N : ℕ} (a b v : GGDepAE p N) :
    ggDepAdot (a - b) v = ggDepAdot a v - ggDepAdot b v := by
  simp only [ggDepAdot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma l05nE3_dot_smul_left {p N : ℕ} (k : ZMod p) (a v : GGDepAE p N) :
    ggDepAdot (k • a) v = k * ggDepAdot a v := by
  simp only [ggDepAdot, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum]

private lemma l05nE3_refl_conj {p N : ℕ} (c f gc gf : GGDepAE p N)
    (h : ggDepAdot gf gc = 2) :
    ggDepARefl gc gf * ggDepARefl c f * ggDepARefl gc gf =
      ggDepARefl (c - ggDepAdot gf c • gc) (f - ggDepAdot f gc • gf) := by
  apply LinearMap.ext; intro v
  ext j
  simp only [Module.End.mul_apply, l05nE3_refl_apply, Pi.sub_apply, Pi.smul_apply,
    l05nE3_dot_sub, l05nE3_dot_smul, l05nE3_dot_sub_left, l05nE3_dot_smul_left, h]
  ring

private lemma l05nE3_conj_dot {p N : ℕ} (c f gc gf : GGDepAE p N)
    (h : ggDepAdot f c = 2) (hg : ggDepAdot gf gc = 2) :
    ggDepAdot (f - ggDepAdot f gc • gf) (c - ggDepAdot gf c • gc) = 2 := by
  rw [l05nE3_dot_sub, l05nE3_dot_sub_left, l05nE3_dot_smul_left, l05nE3_dot_smul,
    l05nE3_dot_sub_left, l05nE3_dot_smul_left, h, hg]
  ring

private lemma l05nE3_pair_i {p N : ℕ} (hN : 3 ≤ N) (i : Fin (N - 1)) :
    ggDepAdot (ggTWα p N i) (ggTWh p N i) = 2 := by
  rw [ggDepAdot]
  by_cases hi : i.val = 0
  · rw [Finset.sum_eq_single_of_mem (⟨0, by omega⟩ : Fin (N - 1)) (Finset.mem_univ _)]
    · have hα : ggTWα p N i (⟨0, by omega⟩ : Fin (N - 1)) = -1 := by
        rw [ggTWα, hi]
        rw [if_neg (by omega : ¬ ((0 : ℕ) + 2 = N)),
          if_neg (by omega : ¬ ((0 : ℕ) + 1 = 0)),
          if_pos (by omega : (0 : ℕ) + 2 = 0 ∨ (0 : ℕ) = 0)]
      have hh : ggTWh p N i (⟨0, by omega⟩ : Fin (N - 1)) = -2 := by
        rw [ggTWh]
        rw [if_neg (by omega : ¬ ((0 : ℕ) + 2 = N)), if_pos hi]
        norm_num
      rw [hα, hh]
      ring
    · intro j _ hj
      have hjv : j.val ≠ 0 := by
        intro h; apply hj; apply Fin.ext; simpa using h
      have hα0 : ggTWα p N i j = 0 := by
        by_cases hj2 : j.val + 2 = N
        · rw [ggTWα, if_pos hj2]
        · rw [ggTWα, if_neg hj2, hi]
          rw [if_neg (by omega : ¬ (j.val + 1 = 0)),
            if_neg (by omega : ¬ (j.val + 2 = 0 ∨ j.val = 0))]
      rw [hα0, zero_mul]
  · let j0 : Fin (N - 1) := ⟨i.val - 1, by omega⟩
    have hj0val : j0.val = i.val - 1 := rfl
    rw [Finset.sum_eq_single_of_mem j0 (Finset.mem_univ _)]
    · have hα : ggTWα p N i j0 = 2 := by
        have hj2 : ¬ (j0.val + 2 = N) := by rw [hj0val]; omega
        have h1 : j0.val + 1 = i.val := by rw [hj0val]; omega
        rw [ggTWα, if_neg hj2, if_pos h1]
      have hh : ggTWh p N i j0 = 1 := by
        have hj2 : ¬ (j0.val + 2 = N) := by rw [hj0val]; omega
        have h1 : j0.val + 1 = i.val := by rw [hj0val]; omega
        rw [ggTWh, if_neg hj2, if_neg hi, if_pos h1]
      rw [hα, hh, mul_one]
    · intro j _ hj
      have hji : ¬ (j.val + 1 = i.val) := by
        intro h
        apply hj
        apply Fin.ext
        rw [hj0val]
        omega
      have hh0 : ggTWh p N i j = 0 := by
        by_cases hj2 : j.val + 2 = N
        · rw [ggTWh, if_pos hj2]
        · rw [ggTWh, if_neg hj2, if_neg hi, if_neg hji]
      rw [hh0, mul_zero]

private lemma l05nE3_H_length (p N i : ℕ) : (ggTWNH p N i).length = N - 1 := by
  simp [ggTWNH]

private lemma l05nE3_A_length (p N i : ℕ) : (ggTWNA p N i).length = N - 1 := by
  simp [ggTWNA]

private lemma l05nE3_cast_neg (p : ℕ) [Fact p.Prime] (x : ℕ) :
    (((p - x % p) % p : ℕ) : ZMod p) = -(x : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [ZMod.natCast_mod, Nat.cast_sub (le_of_lt (Nat.mod_lt x hp)), ZMod.natCast_self,
    ZMod.natCast_mod]
  ring

private lemma l05nE3_cast_pred (p : ℕ) [Fact p.Prime] :
    (((p - 1) % p : ℕ) : ZMod p) = -1 := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
  rw [ZMod.natCast_mod, Nat.cast_sub hp, ZMod.natCast_self]
  ring

private lemma l05nE3_toZ_H {p N : ℕ} [Fact p.Prime] (i : Fin (N - 1)) :
    ggTWNToZ p N (ggTWNH p N i.val) = ggTWh p N i := by
  change ggDepANToZ p (N - 1) (ggTWNH p N i.val) = ggTWh p N i
  funext j
  have hj : j.val < N - 1 := j.isLt
  have hjlen : j.val < (ggTWNH p N i.val).length := by rw [l05nE3_H_length]; exact hj
  simp only [ggDepANToZ]
  rw [List.getD_eq_getElem (l := ggTWNH p N i.val) (d := 0) (n := j.val) hjlen]
  simp only [ggTWNH, ggTWh]
  rw [List.getElem_map]
  simp only [List.range_eq_range', List.getElem_range'_1, Nat.zero_add]
  by_cases hj2 : j.val + 2 = N
  · rw [if_pos hj2, if_pos hj2]; simp
  · rw [if_neg hj2, if_neg hj2]
    by_cases hi : i.val = 0
    · rw [if_pos hi, if_pos hi]
      rw [l05nE3_cast_neg p (j.val + 2)]
      push_cast
      ring
    · rw [if_neg hi, if_neg hi]
      by_cases h1 : j.val + 1 = i.val
      · rw [if_pos h1, if_pos h1]; simp
      · rw [if_neg h1, if_neg h1]; simp

private lemma l05nE3_toZ_A {p N : ℕ} [Fact p.Prime] (i : Fin (N - 1)) :
    ggTWNToZ p N (ggTWNA p N i.val) = ggTWα p N i := by
  change ggDepANToZ p (N - 1) (ggTWNA p N i.val) = ggTWα p N i
  funext j
  have hj : j.val < N - 1 := j.isLt
  have hjlen : j.val < (ggTWNA p N i.val).length := by rw [l05nE3_A_length]; exact hj
  simp only [ggDepANToZ]
  rw [List.getD_eq_getElem (l := ggTWNA p N i.val) (d := 0) (n := j.val) hjlen]
  simp only [ggTWNA, ggTWα, Bool.or_eq_true, decide_eq_true_eq]
  rw [List.getElem_map]
  simp only [List.range_eq_range', List.getElem_range'_1, Nat.zero_add]
  by_cases hj2 : j.val + 2 = N
  · rw [if_pos hj2, if_pos hj2]; simp
  · rw [if_neg hj2, if_neg hj2]
    by_cases h1 : j.val + 1 = i.val
    · rw [if_pos h1, if_pos h1]; simp
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : j.val + 2 = i.val ∨ j.val = i.val
      · rw [if_pos h2, if_pos h2]
        rw [l05nE3_cast_pred p]
      · rw [if_neg h2, if_neg h2]; simp

private lemma l05nE3_dot_of_valid {p N : ℕ} [Fact p.Prime] {q : GGDepANPair}
    (h : GGTWNValid p N q) :
    ggDepAdot (ggTWNToZ p N q.2) (ggTWNToZ p N q.1) = 2 := by
  have hcast := ggDepANDot_cast (p := p) (N := N - 1) q.2 q.1 h.2.1 h.1
  rw [h.2.2, ZMod.natCast_mod] at hcast
  exact hcast.symm

private lemma l05nE3_valid_of_dot {p N : ℕ} [Fact p.Prime] {q : GGDepANPair}
    (hq1 : q.1.length = N - 1) (hq2 : q.2.length = N - 1)
    (h : ggDepAdot (ggTWNToZ p N q.2) (ggTWNToZ p N q.1) = 2) :
    ggDepANDot p q.2 q.1 = 2 % p := by
  have hcast := ggDepANDot_cast (p := p) (N := N - 1) q.2 q.1 hq2 hq1
  rw [h] at hcast
  have h2 : ((ggDepANDot p q.2 q.1 : ℕ) : ZMod p) = ((2 % p : ℕ) : ZMod p) := by
    rw [ZMod.natCast_mod]; exact hcast
  rw [ZMod.natCast_eq_natCast_iff'] at h2
  simpa [ggDepANDot, Nat.mod_mod] using h2

theorem ggTWNGen_valid {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid p N q) {g : ℕ} (hg : g < N - 1 + news.length) :
    GGTWNValid p N (ggTWNGen p N news g) := by
  by_cases h : g + 1 < N
  · have hg' : g < N - 1 := by omega
    have hHlen : (ggTWNH p N g).length = N - 1 := l05nE3_H_length p N g
    have hAlen : (ggTWNA p N g).length = N - 1 := l05nE3_A_length p N g
    have hH : ggTWNToZ p N (ggTWNH p N g) = ggTWh p N ⟨g, hg'⟩ :=
      l05nE3_toZ_H (p := p) (N := N) ⟨g, hg'⟩
    have hA : ggTWNToZ p N (ggTWNA p N g) = ggTWα p N ⟨g, hg'⟩ :=
      l05nE3_toZ_A (p := p) (N := N) ⟨g, hg'⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [ggTWNGen, if_pos h] using hHlen
    · simpa [ggTWNGen, if_pos h] using hAlen
    · have hdot : ggDepAdot (ggDepANToZ p (N - 1) (ggTWNA p N g))
          (ggDepANToZ p (N - 1) (ggTWNH p N g)) = 2 := by
        change ggDepAdot (ggTWNToZ p N (ggTWNA p N g)) (ggTWNToZ p N (ggTWNH p N g)) = 2
        rw [hA, hH]
        exact l05nE3_pair_i (by omega) ⟨g, hg'⟩
      have hcast := ggDepANDot_cast (p := p) (N := N - 1) (ggTWNA p N g) (ggTWNH p N g)
        hAlen hHlen
      rw [hdot] at hcast
      have h2 : ((ggDepANDot p (ggTWNA p N g) (ggTWNH p N g) : ℕ) : ZMod p) =
          ((2 % p : ℕ) : ZMod p) := by
        rw [ZMod.natCast_mod]; exact hcast
      rw [ZMod.natCast_eq_natCast_iff'] at h2
      simpa [ggTWNGen, if_pos h, ggDepANDot, Nat.mod_mod] using h2
  · have hk : g + 1 - N < news.length := by omega
    have hmem : news[g + 1 - N] ∈ news := List.getElem_mem hk
    have hq := hnews (news[g + 1 - N]) hmem
    rw [ggTWNGen, if_neg h,
      List.getD_eq_getElem (l := news) (d := ([], [])) (n := g + 1 - N) hk]
    exact hq

theorem ggTWNGen_mem {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    {news : List GGDepANPair}
    {g : ℕ} (hg : g < N - 1 + news.length) :
    ggTWNRflOf p N (ggTWNGen p N news g) ∈
      Submonoid.closure (ggTWGens p N (ggTWNNews p N news)) := by
  by_cases h : g + 1 < N
  · have hg' : g < N - 1 := by omega
    have hH : ggTWNToZ p N (ggTWNH p N g) = ggTWh p N ⟨g, hg'⟩ :=
      l05nE3_toZ_H (p := p) (N := N) ⟨g, hg'⟩
    have hA : ggTWNToZ p N (ggTWNA p N g) = ggTWα p N ⟨g, hg'⟩ :=
      l05nE3_toZ_A (p := p) (N := N) ⟨g, hg'⟩
    simp only [ggTWNRflOf, ggTWNGen, if_pos h, hH, hA]
    exact Submonoid.subset_closure (Or.inl ⟨⟨g, hg'⟩, rfl⟩)
  · have hk : g + 1 - N < news.length := by omega
    rw [ggTWNRflOf, ggTWNGen, if_neg h,
      List.getD_eq_getElem (l := news) (d := ([], [])) (n := g + 1 - N) hk]
    refine Submonoid.subset_closure (Or.inr ?_)
    exact ⟨(ggTWNToZ p N (news[g + 1 - N]).1, ggTWNToZ p N (news[g + 1 - N]).2),
      ⟨news[g + 1 - N], List.getElem_mem hk, rfl⟩, rfl⟩

private lemma l05nE3_word_cons (p N : ℕ) (news : List GGDepANPair) (q : GGDepANPair) (g : ℕ)
    (w : List ℕ) :
    ggTWNWord p N news q (g :: w) =
      ggDepANConj p (ggTWNWord p N news q w) (ggTWNGen p N news g) := by
  simp [ggTWNWord]

private lemma l05nE3_word {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid p N q)
    (S : Submonoid (Module.End (ZMod p) (GGTWE p N)))
    (hmem : ∀ g : ℕ, g < N - 1 + news.length → ggTWNRflOf p N (ggTWNGen p N news g) ∈ S)
    (w : List ℕ) (hw : ∀ g ∈ w, g < N - 1 + news.length)
    (q : GGDepANPair) (hq : GGTWNValid p N q) (hqm : ggTWNRflOf p N q ∈ S) :
    GGTWNValid p N (ggTWNWord p N news q w) ∧ ggTWNRflOf p N (ggTWNWord p N news q w) ∈ S := by
  revert hw q hq hqm
  induction w with
  | nil => intro hw q hq hqm; simpa [ggTWNWord] using ⟨hq, hqm⟩
  | cons g w ih =>
      intro hw q hq hqm
      rw [l05nE3_word_cons]
      have hg : g < N - 1 + news.length := hw g (by simp)
      have hw' : ∀ g' ∈ w, g' < N - 1 + news.length := fun g' hg' => hw g' (by simp [hg'])
      obtain ⟨ihQ, ihM⟩ := ih hw' q hq hqm
      have hG : GGTWNValid p N (ggTWNGen p N news g) := ggTWNGen_valid hp hN hnews hg
      have hQ1 : (ggTWNWord p N news q w).1.length = N - 1 := ihQ.1
      have hQ2 : (ggTWNWord p N news q w).2.length = N - 1 := ihQ.2.1
      have hG1 : (ggTWNGen p N news g).1.length = N - 1 := hG.1
      have hG2 : (ggTWNGen p N news g).2.length = N - 1 := hG.2.1
      have hconj := l05nE3_conj_length (p := p) hQ1 hQ2 hG1 hG2
      have hdq := l05nE3_dot_of_valid ihQ
      have hdg := l05nE3_dot_of_valid hG
      obtain ⟨hc1, hc2⟩ := l05nE3_toZ_conj (p := p) hQ1 hQ2 hG1 hG2
      have hc1' : ggTWNToZ p N (ggDepANConj p (ggTWNWord p N news q w) (ggTWNGen p N news g)).1 =
          ggTWNToZ p N (ggTWNWord p N news q w).1 -
            ggDepAdot (ggTWNToZ p N (ggTWNGen p N news g).2)
              (ggTWNToZ p N (ggTWNWord p N news q w).1) •
              ggTWNToZ p N (ggTWNGen p N news g).1 := hc1
      have hc2' : ggTWNToZ p N (ggDepANConj p (ggTWNWord p N news q w) (ggTWNGen p N news g)).2 =
          ggTWNToZ p N (ggTWNWord p N news q w).2 -
            ggDepAdot (ggTWNToZ p N (ggTWNWord p N news q w).2)
              (ggTWNToZ p N (ggTWNGen p N news g).1) •
              ggTWNToZ p N (ggTWNGen p N news g).2 := hc2
      refine ⟨⟨hconj.1, hconj.2, ?_⟩, ?_⟩
      · apply l05nE3_valid_of_dot hconj.1 hconj.2
        rw [hc1', hc2']
        exact l05nE3_conj_dot (ggTWNToZ p N (ggTWNWord p N news q w).1)
          (ggTWNToZ p N (ggTWNWord p N news q w).2)
          (ggTWNToZ p N (ggTWNGen p N news g).1) (ggTWNToZ p N (ggTWNGen p N news g).2) hdq hdg
      · simp only [ggTWNRflOf, ggTWRefl]
        rw [hc1', hc2']
        rw [← l05nE3_refl_conj (ggTWNToZ p N (ggTWNWord p N news q w).1)
          (ggTWNToZ p N (ggTWNWord p N news q w).2)
          (ggTWNToZ p N (ggTWNGen p N news g).1) (ggTWNToZ p N (ggTWNGen p N news g).2) hdg]
        exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hmem g hg) ihM) (hmem g hg)

theorem ggTWNWord_valid_mem {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid p N q) {q : GGDepANPair} (hq : GGTWNValid p N q)
    (hqm : ggTWNRflOf p N q ∈ Submonoid.closure (ggTWGens p N (ggTWNNews p N news)))
    {w : List ℕ} (hw : ∀ g ∈ w, g < N - 1 + news.length) :
    GGTWNValid p N (ggTWNWord p N news q w) ∧
      ggTWNRflOf p N (ggTWNWord p N news q w) ∈
        Submonoid.closure (ggTWGens p N (ggTWNNews p N news)) := by
  exact l05nE3_word hp hN hnews (Submonoid.closure (ggTWGens p N (ggTWNNews p N news)))
    (fun g hg => ggTWNGen_mem hp hN hg) w hw q hq hqm

theorem ggTWNTv_sound {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid p N q) (R : List (List ℕ)) (w : GGDepANWit)
    (hv : ggTWNKillValid N (N - 1 + news.length) (GGTWNKill.tv w) = true)
    (ht : ggTWNKillTest p N news R (GGTWNKill.tv w) = true) :
    ∃ g ∈ Submonoid.closure (ggTWGens p N (ggTWNNews p N news)), GGTWIsTv g := by
  have hp3 : 3 ≤ p := by omega
  have hv' := hv
  simp only [ggTWNKillValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv'
  obtain ⟨⟨⟨hvg1, hvg2⟩, hvw1⟩, hvw2⟩ := hv'
  set q1 : GGDepANPair := ggTWNWord p N news (ggTWNGen p N news w.g1) w.w1 with hq1def
  set q2 : GGDepANPair := ggTWNWord p N news (ggTWNGen p N news w.g2) w.w2 with hq2def
  have ht' : ggDepANTestPair p q1 q2 = true := by
    rw [hq1def, hq2def]
    simpa only [ggTWNKillTest] using ht
  have h1 : GGTWNValid p N q1 ∧
      ggTWNRflOf p N q1 ∈ Submonoid.closure (ggTWGens p N (ggTWNNews p N news)) :=
    ggTWNWord_valid_mem hp3 hN hnews (ggTWNGen_valid hp3 hN hnews hvg1)
      (ggTWNGen_mem hp3 hN hvg1) hvw1
  have h2 : GGTWNValid p N q2 ∧
      ggTWNRflOf p N q2 ∈ Submonoid.closure (ggTWGens p N (ggTWNNews p N news)) :=
    ggTWNWord_valid_mem hp3 hN hnews (ggTWNGen_valid hp3 hN hnews hvg2)
      (ggTWNGen_mem hp3 hN hvg2) hvw2
  obtain ⟨hv1, hm1⟩ := h1
  obtain ⟨hv2, hm2⟩ := h2
  have hp2 : p ≠ 2 := by omega
  have htv := ggDepANTestPair_sound (p := p) (N := N - 1) hp2 q1 q2
    hv1.1 hv1.2.1 hv2.1 hv2.2.1 hv1.2.2 hv2.2.2 ht'
  refine ⟨ggTWRefl (ggTWNToZ p N q1.1) (ggTWNToZ p N q1.2) *
      ggTWRefl (ggTWNToZ p N q2.1) (ggTWNToZ p N q2.2), ?_, ?_⟩
  · exact Submonoid.mul_mem _ hm1 hm2
  · exact htv.2.2

end CFSG.StandardType
