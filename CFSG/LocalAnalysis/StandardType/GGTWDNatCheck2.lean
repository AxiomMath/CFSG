module

public import CFSG.LocalAnalysis.StandardType.GGTWDNatCheck1
public import CFSG.LocalAnalysis.StandardType.GGTWDRes

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmallN Certificates.DepASmall Certificates.TwoDepSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nD4_nat_eq_of_cast {p : ℕ} {x y : ℕ} (hx : x < p) (hy : y < p)
    (h : (x : ZMod p) = (y : ZMod p)) : x = y := by
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hv

private lemma l05nD4_target_neg_one {p : ℕ} (hp : 1 ≤ p) {N : ℕ} (c' c : Fin (N - 1)) :
    (((if c'.val = c.val then (p - 1) % p else 0 : ℕ)) : ZMod p) =
      (if c' = c then (-1 : ZMod p) else 0) := by
  by_cases h : c' = c
  · subst h
    rw [if_pos rfl, if_pos rfl]
    simpa using l05nND_cast_neg p 1 hp
  · have hne : c'.val ≠ c.val := fun hh => h (Fin.ext hh)
    rw [if_neg h, if_neg hne, Nat.cast_zero]

private lemma l05nD4_X_length (N : ℕ) : (ggDepANX N).length = N := by
  simp [ggDepANX]

private lemma l05nD4_toZ_X (p N : ℕ) : ggDepANToZ p N (ggDepANX N) = ggDepAx p N := by
  funext j
  have hj : j.val < (ggDepANX N).length := by simpa [ggDepANX] using j.isLt
  rw [ggDepANToZ, List.getD_eq_getElem (l := ggDepANX N) (d := 0) (n := j.val) hj]
  simp only [ggDepANX, ggDepAx, List.getElem_map, List.getElem_range]
  split <;> simp

private lemma l05nD4_witValid_mono {G G' : ℕ} (hGG : G ≤ G') (w : GGDepANWit)
    (h : ggTWDWitValid G w = true) : ggTWDWitValid G' w = true := by
  obtain ⟨g1, w1, g2, w2⟩ := w
  simp only [ggTWDWitValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
  exact ⟨⟨⟨Nat.lt_of_lt_of_le h.1.1.1 hGG, Nat.lt_of_lt_of_le h.1.1.2 hGG⟩,
    fun g hg => Nat.lt_of_lt_of_le (h.1.2 g hg) hGG⟩,
    fun g hg => Nat.lt_of_lt_of_le (h.2 g hg) hGG⟩

private lemma l05nD4_res_extract {p N : ℕ} (posn c : ℕ) (swits rwits : List GGDepANWit)
    (h : ggTWDRes p N posn c swits rwits = true)
    {lh1 la1 lh2 la2 : List ℕ}
    (hlh1 : lh1 ∈ ggTWDSolH p N posn (fun c' => if c' = c then (p - 1) % p else 0))
    (hla1 : la1 ∈ ggTWDSolA p N posn (fun c' => if c' = c then (p - 1) % p else 0))
    (hlh2 : lh2 ∈ ggTWDSolH p N posn (fun _ => 0))
    (hla2 : la2 ∈ ggTWDSolA p N posn (fun _ => 0))
    (hd1 : ggDepANDot p la1 lh1 = 2 % p)
    (hz1 : ggDepANDot p la1 (ggDepANX N) = 0)
    (hd2 : ggDepANDot p la1 lh2 = (p - 1) % p)
    (hd3 : ggDepANDot p la2 lh2 = 2 % p)
    (hd4 : ggDepANDot p la2 lh1 = (p - 1) % p)
    (hz2 : ggDepANDot p la2 (ggDepANX N) ≠ 0) :
    ∃ w ∈ swits ++ rwits, ggTWDWitTest p N [(lh1, la1), (lh2, la2)] w = true := by
  simp only [ggTWDRes] at h
  have e1 := List.all_eq_true.mp h lh1 hlh1
  have e2 := List.all_eq_true.mp e1 la1 hla1
  have hc1 : (ggDepANDot p la1 lh1 == 2 % p && ggDepANDot p la1 (ggDepANX N) == 0) = true := by
    rw [Bool.and_eq_true]
    exact ⟨beq_iff_eq.mpr hd1, beq_iff_eq.mpr hz1⟩
  rw [if_pos hc1] at e2
  have e3 := List.all_eq_true.mp e2 lh2 hlh2
  rw [if_pos (beq_iff_eq.mpr hd2)] at e3
  have e4 := List.all_eq_true.mp e3 la2 hla2
  have hc2 : (ggDepANDot p la2 lh2 == 2 % p && ggDepANDot p la2 lh1 == (p - 1) % p &&
      ggDepANDot p la2 (ggDepANX N) != 0) = true := by
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨beq_iff_eq.mpr hd3, beq_iff_eq.mpr hd4⟩, bne_iff_ne.mpr hz2⟩
  rw [if_pos hc2] at e4
  exact List.any_eq_true.mp e4

private lemma l05nD4_pat1_wit {N : ℕ} {pos : GGTWPos} {c0 : ℕ} {m n : ℤ}
    (h : GGTWPat1 N pos c0 m n) :
    ∃ mi ni : ℕ, (mi = 1 ∨ mi = 2) ∧ (ni = 1 ∨ ni = 2) ∧
      m = -(mi : ℤ) ∧ n = -(ni : ℤ) := by
  obtain ⟨hm, hn⟩ := ggTWPat1_mn h
  rcases hm with rfl | rfl <;> rcases hn with rfl | rfl
  · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, rfl, rfl⟩
  · exact ⟨1, 2, Or.inl rfl, Or.inr rfl, rfl, rfl⟩
  · exact ⟨2, 1, Or.inr rfl, Or.inl rfl, rfl, rfl⟩
  · exact ⟨2, 2, Or.inr rfl, Or.inr rfl, rfl, rfl⟩

private lemma l05nD4_check_one {p N : ℕ} (d : GGTWDData) (h : ggTWDCheck p N d = true)
    (posn c0 mi ni : ℕ) (hpat : ggTWNPat1B N posn c0 mi ni = true)
    (hpos : posn ∈ [0, 1]) (hc0 : c0 ∈ List.range (N - 1))
    (hmi : mi = 1 ∨ mi = 2) (hni : ni = 1 ∨ ni = 2) :
    ∃ wits, d.single.lookup (posn, c0, mi, ni) = some wits ∧
      (∀ w ∈ wits, ggTWDWitValid N w = true) ∧
      ggTWDCases1 p N posn c0 mi ni wits = true := by
  have hh := h
  rw [ggTWDCheck] at hh
  have h1 := Bool.and_eq_true_iff.mp hh
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have hone : d.single.all (fun e => e.2.all (ggTWDWitValid N)) = true := h2.1
  have ha := List.all_eq_true.mp h1.2 posn hpos
  have hb := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ha).1 c0 hc0
  have hmi' : mi ∈ [1, 2] := by rcases hmi with rfl | rfl <;> simp
  have hni' : ni ∈ [1, 2] := by rcases hni with rfl | rfl <;> simp
  have hc := List.all_eq_true.mp hb mi hmi'
  have hd := List.all_eq_true.mp hc ni hni'
  rw [if_pos hpat] at hd
  cases hlook : d.single.lookup (posn, c0, mi, ni) with
  | none => rw [hlook] at hd; simp at hd
  | some wits =>
      rw [hlook] at hd
      obtain ⟨l₁, l₂, hdata, -⟩ := List.lookup_eq_some_iff.mp hlook
      have hentry : ((posn, c0, mi, ni), wits) ∈ d.single := by
        rw [hdata]; simp
      have hwv : ∀ w ∈ wits, ggTWDWitValid N w = true := by
        intro w hw
        exact List.all_eq_true.mp
          (List.all_eq_true.mp hone (((posn, c0, mi, ni), wits)) hentry) w hw
      exact ⟨wits, rfl, hwv, hd⟩

private lemma l05nD4_check_res {p N : ℕ} (d : GGTWDData) (h : ggTWDCheck p N d = true)
    (posn c : ℕ) (hpat : ggTWNPat2B N posn c none = true)
    (hpos : posn ∈ [0, 1]) (hc : c ∈ List.range (N - 1)) :
    ∃ swits rwits, d.single.lookup (posn, c, 1, 1) = some swits ∧
      d.res.lookup (posn, c) = some rwits ∧
      (∀ w ∈ swits, ggTWDWitValid N w = true) ∧
      (∀ w ∈ rwits, ggTWDWitValid (N + 1) w = true) ∧
      ggTWDRes p N posn c swits rwits = true := by
  have hh := h
  rw [ggTWDCheck] at hh
  have h1 := Bool.and_eq_true_iff.mp hh
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have hone : d.single.all (fun e => e.2.all (ggTWDWitValid N)) = true := h2.1
  have hres : d.res.all (fun e => e.2.all (ggTWDWitValid (N + 1))) = true := h2.2
  have ha := List.all_eq_true.mp h1.2 posn hpos
  have hb := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ha).2 c hc
  rw [if_pos hpat] at hb
  cases hsl : d.single.lookup (posn, c, 1, 1) with
  | none => rw [hsl] at hb; simp at hb
  | some swits =>
      cases hrl : d.res.lookup (posn, c) with
      | none => rw [hsl, hrl] at hb; simp at hb
      | some rwits =>
          rw [hsl, hrl] at hb
          obtain ⟨l₁, l₂, hdata, -⟩ := List.lookup_eq_some_iff.mp hsl
          have hentry1 : ((posn, c, 1, 1), swits) ∈ d.single := by
            rw [hdata]; simp
          obtain ⟨m₁, m₂, hdata2, -⟩ := List.lookup_eq_some_iff.mp hrl
          have hentry2 : ((posn, c), rwits) ∈ d.res := by
            rw [hdata2]; simp
          have hsv : ∀ w ∈ swits, ggTWDWitValid N w = true := by
            intro w hw
            exact List.all_eq_true.mp
              (List.all_eq_true.mp hone (((posn, c, 1, 1), swits)) hentry1) w hw
          have hrv : ∀ w ∈ rwits, ggTWDWitValid (N + 1) w = true := by
            intro w hw
            exact List.all_eq_true.mp
              (List.all_eq_true.mp hres (((posn, c), rwits)) hentry2) w hw
          exact ⟨swits, rwits, rfl, rfl, hsv, hrv, hb⟩

theorem ggTWDRes_sound {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N) (pos : GGTWPos)
    (c : Fin (N - 1)) (swits rwits : List GGDepANWit)
    (hsv : ∀ w ∈ swits, ggTWDWitValid N w = true)
    (hrv : ∀ w ∈ rwits, ggTWDWitValid (N + 1) w = true)
    (hc : ggTWDRes p N (ggTWPosNat pos) c.val swits rwits = true)
    (ha1 αa1 ha2 αa2 : GGDepAE p N) (hpair : GGTWDPairs2 p N pos c none ha1 αa1 ha2 αa2)
    (hx1 : ggDepAdot αa1 (ggDepAx p N) = 0) (hx2 : ggDepAdot αa2 (ggDepAx p N) ≠ 0) :
    ∃ g ∈ Submonoid.closure (Set.range (fun i : Fin (N - 1) =>
        ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
          {ggDepARefl ha1 αa1, ggDepARefl ha2 αa2}), GGDepAIsTv g := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hvH1 : ∀ c' : Fin (N - 1), ggTWInJ N pos c'.val →
      ggDepAdot (ggDepAα p N c') ha1 =
        (((if c'.val = c.val then (p - 1) % p else 0 : ℕ)) : ZMod p) := by
    intro c' hcJ
    have h := (hpair.1 c' hcJ).2.1
    rw [h]
    exact (l05nD4_target_neg_one hp1 c' c).symm
  have hvA1 : ∀ c' : Fin (N - 1), ggTWInJ N pos c'.val →
      ggDepAdot αa1 (ggDepAh p N c') =
        (((if c'.val = c.val then (p - 1) % p else 0 : ℕ)) : ZMod p) := by
    intro c' hcJ
    have h := (hpair.1 c' hcJ).1
    rw [h]
    exact (l05nD4_target_neg_one hp1 c' c).symm
  have hvH2 : ∀ c' : Fin (N - 1), ggTWInJ N pos c'.val →
      ggDepAdot (ggDepAα p N c') ha2 = (((0 : ℕ)) : ZMod p) := by
    intro c' hcJ
    have h := (hpair.1 c' hcJ).2.2.2
    rw [h]; simp
  have hvA2 : ∀ c' : Fin (N - 1), ggTWInJ N pos c'.val →
      ggDepAdot αa2 (ggDepAh p N c') = (((0 : ℕ)) : ZMod p) := by
    intro c' hcJ
    have h := (hpair.1 c' hcJ).2.2.1
    rw [h]; simp
  obtain ⟨lh1, hlh1_mem, hlh1_eq, hlh1_len⟩ :=
    ggTWDSolH_complete (p := p) (N := N) pos
      (fun x => if x = c.val then (p - 1) % p else 0) ha1 hvH1
  obtain ⟨la1, hla1_mem, hla1_eq, hla1_len⟩ :=
    ggTWDSolA_complete (p := p) (N := N) pos
      (fun x => if x = c.val then (p - 1) % p else 0) αa1 hvA1
  obtain ⟨lh2, hlh2_mem, hlh2_eq, hlh2_len⟩ :=
    ggTWDSolH_complete (p := p) (N := N) pos (fun _ => 0) ha2 hvH2
  obtain ⟨la2, hla2_mem, hla2_eq, hla2_len⟩ :=
    ggTWDSolA_complete (p := p) (N := N) pos (fun _ => 0) αa2 hvA2
  have hd1 : ggDepANDot p la1 lh1 = 2 % p := by
    refine l05nD4_nat_eq_of_cast (p := p) (x := ggDepANDot p la1 lh1) (y := 2 % p) ?_ ?_ ?_
    · simp only [ggDepANDot]; exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · rw [ggDepANDot_cast (p := p) (N := N) la1 lh1 hla1_len hlh1_len, hla1_eq, hlh1_eq,
          ZMod.natCast_mod]
      exact hpair.2.2.2.1
  have hd3 : ggDepANDot p la2 lh2 = 2 % p := by
    refine l05nD4_nat_eq_of_cast (p := p) (x := ggDepANDot p la2 lh2) (y := 2 % p) ?_ ?_ ?_
    · simp only [ggDepANDot]; exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · rw [ggDepANDot_cast (p := p) (N := N) la2 lh2 hla2_len hlh2_len, hla2_eq, hlh2_eq,
          ZMod.natCast_mod]
      exact hpair.2.2.2.2
  have hd2 : ggDepANDot p la1 lh2 = (p - 1) % p := by
    refine l05nD4_nat_eq_of_cast (p := p) (x := ggDepANDot p la1 lh2) (y := (p - 1) % p) ?_ ?_ ?_
    · simp only [ggDepANDot]; exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · have hneg : (((p - 1) % p : ℕ) : ZMod p) = (-1 : ZMod p) := by
        simpa using l05nND_cast_neg p 1 hp1
      rw [ggDepANDot_cast (p := p) (N := N) la1 lh2 hla1_len hlh2_len, hla1_eq, hlh2_eq,
          hneg, hpair.2.1]
      simp
  have hd4 : ggDepANDot p la2 lh1 = (p - 1) % p := by
    refine l05nD4_nat_eq_of_cast (p := p) (x := ggDepANDot p la2 lh1) (y := (p - 1) % p) ?_ ?_ ?_
    · simp only [ggDepANDot]; exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · have hneg : (((p - 1) % p : ℕ) : ZMod p) = (-1 : ZMod p) := by
        simpa using l05nND_cast_neg p 1 hp1
      rw [ggDepANDot_cast (p := p) (N := N) la2 lh1 hla2_len hlh1_len, hla2_eq, hlh1_eq,
          hneg, hpair.2.2.1]
      simp
  have hz1 : ggDepANDot p la1 (ggDepANX N) = 0 := by
    refine l05nD4_nat_eq_of_cast (p := p) (x := ggDepANDot p la1 (ggDepANX N)) (y := 0) ?_ ?_ ?_
    · simp only [ggDepANDot]; exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · exact (Fact.out : p.Prime).pos
    · rw [ggDepANDot_cast (p := p) (N := N) la1 (ggDepANX N) hla1_len (l05nD4_X_length N),
          hla1_eq, l05nD4_toZ_X, hx1, Nat.cast_zero]
  have hz2 : ggDepANDot p la2 (ggDepANX N) ≠ 0 := by
    intro h0
    apply hx2
    have hcast := ggDepANDot_cast (p := p) (N := N) la2 (ggDepANX N) hla2_len (l05nD4_X_length N)
    rw [h0, Nat.cast_zero, hla2_eq, l05nD4_toZ_X] at hcast
    exact hcast.symm
  obtain ⟨w, hwmem, hwtest⟩ :=
    l05nD4_res_extract (p := p) (N := N) (ggTWPosNat pos) c.val swits rwits hc
      hlh1_mem hla1_mem hlh2_mem hla2_mem hd1 hz1 hd2 hd3 hd4 hz2
  have hnews : ∀ q ∈ [(lh1, la1), (lh2, la2)], GGTWDValid p N q := by
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq; exact ⟨hlh1_len, hla1_len, hd1⟩
    · rcases List.mem_cons.mp hq with hq | hq
      · subst hq; exact ⟨hlh2_len, hla2_len, hd3⟩
      · simp at hq
  have hv : ggTWDWitValid (N - 1 + [(lh1, la1), (lh2, la2)].length) w = true := by
    have hlen : N - 1 + [(lh1, la1), (lh2, la2)].length = N + 1 := by
      simp only [List.length_cons, List.length_nil]; omega
    rw [hlen]
    rcases List.mem_append.mp hwmem with hw | hw
    · exact l05nD4_witValid_mono (by omega : N ≤ N + 1) w (hsv w hw)
    · exact hrv w hw
  have hgens : ggTWDGens p N [(lh1, la1), (lh2, la2)] =
      Set.range (fun i : Fin (N - 1) =>
          ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
        {ggDepARefl ha1 αa1, ggDepARefl ha2 αa2} := by
    rw [ggTWDGens]
    congr 1
    ext s
    rw [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases List.mem_cons.mp hq with hq | hq
      · subst hq
        left
        simp only [ggTWDRflOf, hlh1_eq, hla1_eq]
      · rcases List.mem_cons.mp hq with hq | hq
        · subst hq
          right
          simp only [ggTWDRflOf, hlh2_eq, hla2_eq]
        · simp at hq
    · intro hs
      rcases hs with hs | hs
      · exact ⟨(lh1, la1), by simp, by rw [hs]; simp only [ggTWDRflOf, hlh1_eq, hla1_eq]⟩
      · exact ⟨(lh2, la2), by simp, by rw [hs]; simp only [ggTWDRflOf, hlh2_eq, hla2_eq]⟩
  obtain ⟨g, hgclos, hgtv⟩ := ggTWDTv_sound hp2 hN hnews w hv hwtest
  exact ⟨g, by rwa [hgens] at hgclos, hgtv⟩

theorem ggTWDCheck_sound {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N) (d : GGTWDData)
    (h : ggTWDCheck p N d = true) : GGTWDCertCells p N := by
  constructor
  · intro pos c0 m n hpat ha αa hpair hdot hx
    obtain ⟨mi, ni, hmi, hni, hm, hn⟩ := l05nD4_pat1_wit hpat
    have hpatB : ggTWNPat1B N (ggTWPosNat pos) c0.val mi ni = true :=
      (ggTWNPat1B_iff pos c0.val mi ni hmi hni).mpr (by rw [← hm, ← hn]; exact hpat)
    have hpm : ggTWPosNat pos ∈ [0, 1] := by cases pos <;> simp [ggTWPosNat]
    have hc0m : c0.val ∈ List.range (N - 1) := List.mem_range.mpr c0.isLt
    obtain ⟨wits, -, hwv, hcases⟩ :=
      l05nD4_check_one d h (ggTWPosNat pos) c0.val mi ni hpatB hpm hc0m hmi hni
    have hpair' : GGTWDPairs1 p N pos c0 (-(mi : ℤ)) (-(ni : ℤ)) ha αa := by
      rw [← hm, ← hn]; exact hpair
    exact ggTWDCases1_sound hp2 hN pos c0 mi ni hmi hni wits hwv hcases ha αa hpair' hdot hx
  · intro pos c hpat ha1 αa1 ha2 αa2 hpair hx1 hx2
    have hpatB : ggTWNPat2B N (ggTWPosNat pos) c.val none = true :=
      (ggTWNPat2B_iff pos c.val none).mpr hpat
    have hpm : ggTWPosNat pos ∈ [0, 1] := by cases pos <;> simp [ggTWPosNat]
    have hcm : c.val ∈ List.range (N - 1) := List.mem_range.mpr c.isLt
    obtain ⟨swits, rwits, -, -, hsv, hrv, hres⟩ :=
      l05nD4_check_res d h (ggTWPosNat pos) c.val hpatB hpm hcm
    exact ggTWDRes_sound hp2 hN pos c swits rwits hsv hrv hres ha1 αa1 ha2 αa2 hpair hx1 hx2

end CFSG.StandardType

end
