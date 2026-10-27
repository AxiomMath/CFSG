module

public import Certificates.Data.DepASmall
public import CFSG.LocalAnalysis.StandardType.GGDepAThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGDepASmallNat

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


open Certificates.DepASmall

@[expose] def ggDepAThreePatB (N b c0 mi ni : Nat) : Bool :=
  decide (b < N - 1) && decide (c0 < N - 1) && (decide (b = 0) || decide (b + 2 = N)) &&
    decide (c0 ≠ b) &&
    (((decide ((if b = 0 then c0 - 1 else c0) = 0) ||
          decide ((if b = 0 then c0 - 1 else c0) + 1 = N - 2)) &&
        ((mi == 1 && ni == 1) || (mi == 1 && ni == 2) || (mi == 2 && ni == 1))) ||
      (decide (3 ≤ N - 2) &&
        (decide ((if b = 0 then c0 - 1 else c0) = 1) ||
          decide ((if b = 0 then c0 - 1 else c0) + 2 = N - 2)) && mi == 1 && ni == 1) ||
      (decide (N - 2 = 5) && decide ((if b = 0 then c0 - 1 else c0) = 2) && mi == 1 && ni == 1) ||
      (decide (N - 2 = 7) && (decide ((if b = 0 then c0 - 1 else c0) = 2) ||
          decide ((if b = 0 then c0 - 1 else c0) = 4)) && mi == 1 && ni == 1))

structure GGDepAThreeSurv where
  s : List (Nat × List Nat × Nat)
  g : List (Nat × List Nat)
  o : List (Nat × Nat)

abbrev GGDepAThreeSData := List ((Nat × Nat × Nat × Nat) × List GGDepAThreeSurv)

@[expose] def ggDepAThreeE6Edge (i j : Nat) : Bool :=
  (i == 0 && j == 2) || (i == 2 && j == 0) || (i == 1 && j == 3) || (i == 3 && j == 1) ||
  (i == 2 && j == 3) || (i == 3 && j == 2) || (i == 3 && j == 4) || (i == 4 && j == 3) ||
  (i == 4 && j == 5) || (i == 5 && j == 4)

@[expose] def ggDepAThreeE6Res (p i j : Nat) : Nat :=
  if i == j then 2 % p else if ggDepAThreeE6Edge i j then (p - 1) % p else 0

@[expose] def ggDepAThreeSWord (p : Nat) (sp : List GGDepANPair) (j0 : Nat) (w : List Nat) :
    GGDepANPair :=
  w.foldr (fun t acc => ggDepANConj p acc (sp.getD t ([], []))) (sp.getD j0 ([], []))

@[expose] def ggDepAThreeSameRefl (p : Nat) (q r : GGDepANPair) : Bool :=
  (q.1 == r.1 && q.2 == r.2) ||
    (q.1 == ggDepANSmul p (p - 1) r.1 && q.2 == ggDepANSmul p (p - 1) r.2)

@[expose] def ggDepAThreeKey (p : Nat) (v : List Nat) : Nat :=
  v.foldl (fun acc a => acc * p + a % p) 0

@[expose] def ggDepAThreeOrbit (p N : Nat) (gen : Nat → GGDepANPair) (o : List (Nat × Nat)) :
    List (List Nat) :=
  o.foldl (fun acc e =>
    acc ++ [ggDepANSub p (acc.getD e.1 [])
      (ggDepANSmul p (ggDepANDot p (gen e.2).2 (acc.getD e.1 [])) (gen e.2).1)]) [ggDepANX N]

@[expose] def ggDepAThreeSurvTest (p N : Nat) (ha aa : List Nat) (r : GGDepAThreeSurv) : Bool :=
  let gen := ggDepANGen p N ha aa
  let sp : List GGDepANPair := r.s.map fun e =>
    let q := ggDepANWord p N (gen e.1) e.2.1 ha aa
    (ggDepANSmul p e.2.2 q.1, ggDepANSmul p e.2.2 q.2)
  let orbit := ggDepAThreeOrbit p N gen r.o
  decide (r.s.length = 6) && decide (r.g.length = N) && decide (r.o.length = 71) &&
  r.s.all (fun e => decide (e.1 < N) && e.2.1.all (fun t => decide (t < N)) &&
    (e.2.2 == 1 || e.2.2 == p - 1)) &&
  r.g.all (fun e => decide (e.1 < 6) && e.2.all (fun t => decide (t < 6))) &&
  (List.range r.o.length).all (fun k => match r.o[k]? with
    | none => false
    | some e => decide (e.1 < k + 1) && decide (e.2 < N)) &&
  sp.all (fun q => ggDepANDot p q.2 q.1 == 2 % p) &&
  (List.range 6).all (fun i => (List.range 6).all fun j =>
    ggDepANDot p (sp.getD i ([], [])).2 (sp.getD j ([], [])).1 == ggDepAThreeE6Res p i j) &&
  (List.range N).all (fun k => match r.g[k]? with
    | none => false
    | some e => ggDepAThreeSameRefl p (ggDepAThreeSWord p sp e.1 e.2) (gen k)) &&
  decide (orbit.length = 72) && decide ((orbit.map (ggDepAThreeKey p)).Nodup)

@[expose] def ggDepAThreeCases (p N b c0 mi ni : Nat) (wits : List GGDepANWit)
    (survs : List GGDepAThreeSurv) : Bool :=
  (List.range p).all fun s => (List.range p).all fun t => (List.range p).all fun u =>
    (List.range p).all fun v =>
      let ha := ggDepANHaParam p N b c0 ((p - ni) % p) s t
      let aa := ggDepANAaParam p N b c0 ((p - mi) % p) u v
      if ggDepANDot p aa ha == 2 % p && v % p != 0 then
        wits.any (fun w => ggDepANWitTest p N w ha aa) ||
          survs.any (fun r => ggDepAThreeSurvTest p N ha aa r)
      else true

@[expose] def ggDepAThreeCheck (p N : Nat) (data : GGDepANData) (sdata : GGDepAThreeSData) : Bool :=
  data.all (fun e => e.2.all (ggDepANWitValid N)) &&
  (List.range (N - 1)).all fun b => (List.range (N - 1)).all fun c0 =>
    [1, 2].all fun mi => [1, 2].all fun ni =>
      if ggDepAThreePatB N b c0 mi ni then
        match data.lookup (b, c0, mi, ni) with
        | none => false
        | some wits =>
            ggDepAThreeCases p N b c0 mi ni wits ((sdata.lookup (b, c0, mi, ni)).getD [])
      else true

private lemma lr7ck_ANPatB_imp (N b c0 mi ni : ℕ) (h : ggDepANPatB N b c0 mi ni = true) :
    ggDepAThreePatB N b c0 mi ni = true := by
  let P := decide (b < N - 1) && decide (c0 < N - 1) &&
    (decide (b = 0) || decide (b + 2 = N)) && decide (c0 ≠ b)
  let X := ((decide ((if b = 0 then c0 - 1 else c0) = 0) ||
      decide ((if b = 0 then c0 - 1 else c0) + 1 = N - 2)) &&
    ((mi == 1 && ni == 1) || (mi == 1 && ni == 2) || (mi == 2 && ni == 1)))
  let Y := (decide (3 ≤ N - 2) &&
    (decide ((if b = 0 then c0 - 1 else c0) = 1) ||
      decide ((if b = 0 then c0 - 1 else c0) + 2 = N - 2)) && mi == 1 && ni == 1)
  let Z := (decide (N - 2 = 5) && decide ((if b = 0 then c0 - 1 else c0) = 2) &&
    mi == 1 && ni == 1)
  let W := (decide (N - 2 = 7) && (decide ((if b = 0 then c0 - 1 else c0) = 2) ||
      decide ((if b = 0 then c0 - 1 else c0) = 4)) && mi == 1 && ni == 1)
  have h' : (P && (X || Y || Z)) = true := h
  have h2 : (P && (X || Y || Z || W)) = true := by
    rw [Bool.and_eq_true] at h' ⊢
    refine ⟨h'.1, ?_⟩
    rw [Bool.or_eq_true] at h' ⊢
    exact Or.inl (Bool.or_eq_true_iff.mpr h'.2)
  exact h2

private lemma lr7ck_patB_E8 {N : ℕ} (b c0 : Fin (N - 1)) (hN : N = 9)
    (hb : b.val = 0 ∨ b.val + 2 = N) (hbc : c0 ≠ b)
    (hpos : (if b.val = 0 then c0.val - 1 else c0.val) = 2 ∨
      (if b.val = 0 then c0.val - 1 else c0.val) = 4) :
    ggDepAThreePatB N b.val c0.val 1 1 = true := by
  subst hN
  simp only [ggDepAThreePatB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff, beq_iff_eq]
  refine ⟨⟨⟨⟨b.isLt, c0.isLt⟩, hb⟩, fun h => hbc (Fin.ext h)⟩, ?_⟩
  tauto

private lemma lr7ck_pat_wit {N : ℕ} (b c0 : Fin (N - 1)) {m n : ℤ}
    (h : GGDepAPatE N b c0 m n) :
    ∃ mi ni : ℕ, (mi = 1 ∨ mi = 2) ∧ (ni = 1 ∨ ni = 2) ∧
      m = -(mi : ℤ) ∧ n = -(ni : ℤ) ∧ ggDepAThreePatB N b.val c0.val mi ni = true := by
  rcases h with h | ⟨hN, hb, hbc, hm, hn, hpos⟩
  · unfold GGDepAPat at h
    obtain ⟨hb', hbc', h⟩ := h
    rcases h with ⟨hA, (⟨hm, hn⟩ | ⟨hm, hn⟩ | ⟨hm, hn⟩)⟩ | ⟨hB, hC, hm, hn⟩ |
      ⟨hE, hF, hm, hn⟩
    · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, by omega, by omega, lr7ck_ANPatB_imp _ _ _ _ _
        (by rw [ggDepANPatB_iff b c0 1 1 (Or.inl rfl) (Or.inl rfl)]
            exact ⟨hb', hbc', Or.inl ⟨hA, Or.inl ⟨rfl, rfl⟩⟩⟩)⟩
    · exact ⟨1, 2, Or.inl rfl, Or.inr rfl, by omega, by omega, lr7ck_ANPatB_imp _ _ _ _ _
        (by rw [ggDepANPatB_iff b c0 1 2 (Or.inl rfl) (Or.inr rfl)]
            exact ⟨hb', hbc', Or.inl ⟨hA, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩⟩)⟩
    · exact ⟨2, 1, Or.inr rfl, Or.inl rfl, by omega, by omega, lr7ck_ANPatB_imp _ _ _ _ _
        (by rw [ggDepANPatB_iff b c0 2 1 (Or.inr rfl) (Or.inl rfl)]
            exact ⟨hb', hbc', Or.inl ⟨hA, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩⟩)⟩
    · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, by omega, by omega, lr7ck_ANPatB_imp _ _ _ _ _
        (by rw [ggDepANPatB_iff b c0 1 1 (Or.inl rfl) (Or.inl rfl)]
            exact ⟨hb', hbc', Or.inr (Or.inl ⟨hB, hC, rfl, rfl⟩)⟩)⟩
    · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, by omega, by omega, lr7ck_ANPatB_imp _ _ _ _ _
        (by rw [ggDepANPatB_iff b c0 1 1 (Or.inl rfl) (Or.inl rfl)]
            exact ⟨hb', hbc', Or.inr (Or.inr ⟨hE, hF, rfl, rfl⟩)⟩)⟩
  · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, by omega, by omega,
      lr7ck_patB_E8 b c0 hN hb hbc hpos⟩

private lemma lr7ck_dot_eq_two {p : ℕ} (hp : 3 ≤ p) {x : ℕ} (hx : x < p)
    (h : (x : ZMod p) = 2) : x = 2 % p := by
  have h2 : x % p = 2 % p := by
    have h' : (x : ZMod p).val = ((2 : ℕ) : ZMod p).val := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast] at h'
  rw [Nat.mod_eq_of_lt (by omega : 2 < p)]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega : 2 < p)] at h2
  exact h2

private lemma lr7ck_lookup_getD_mem {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × List β)) (k : α) {r : β} (h : r ∈ (l.lookup k).getD []) :
    r ∈ l.flatMap Prod.snd := by
  cases hl : l.lookup k with
  | none => rw [hl] at h; simp at h
  | some v =>
    rw [hl] at h
    simp only [Option.getD_some] at h
    obtain ⟨l₁, l₂, hdata, -⟩ := List.lookup_eq_some_iff.mp hl
    subst hdata
    exact List.mem_flatMap.mpr ⟨(k, v), by simp, h⟩

theorem ggDepAThreeCheck_core {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hpN : p ∣ N) (hN : 5 ≤ N)
    (data : GGDepANData) (sdata : GGDepAThreeSData)
    (h : ggDepAThreeCheck p N data sdata = true) :
    ∀ (b c0 : Fin (N - 1)) (m n : ℤ), GGDepAPatE N b c0 m n → ∀ ha αa : GGDepAE p N,
      (∀ c : Fin (N - 1), c ≠ b →
        ggDepAdot αa (ggDepAh p N c) = (if c = c0 then (m : ZMod p) else 0) ∧
          ggDepAdot (ggDepAα p N c) ha = (if c = c0 then (n : ZMod p) else 0)) →
      ggDepAdot αa ha = 2 → ggDepAdot αa (ggDepAx p N) ≠ 0 →
        (∃ g ∈ Submonoid.closure (Set.range (fun i : Fin (N - 1) =>
            ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪ {ggDepARefl ha αa}), GGDepAIsTv g) ∨
        ∃ (hl al : List ℕ) (r : GGDepAThreeSurv), r ∈ sdata.flatMap Prod.snd ∧ hl.length = N ∧
          al.length = N ∧ ggDepANToZ p N hl = ha ∧ ggDepANToZ p N al = αa ∧
          ggDepAThreeSurvTest p N hl al r = true := by
  intro b c0 m n hpat ha αa hpairs hdot2 hx
  obtain ⟨mi, ni, hmi, hni, hm, hn, hpatB⟩ := lr7ck_pat_wit b c0 hpat
  have hb : b.val = 0 ∨ b.val + 2 = N := by
    have hpat' := hpat
    rcases hpat' with h | ⟨-, hb, -, -, -, -⟩
    · unfold GGDepAPat at h; exact h.1
    · exact hb
  have hbc : c0 ≠ b := by
    have hpat' := hpat
    rcases hpat' with h | ⟨-, -, hbc, -, -, -⟩
    · unfold GGDepAPat at h; exact h.2.1
    · exact hbc
  rw [ggDepAThreeCheck, Bool.and_eq_true] at h
  obtain ⟨hvalid, hcheck⟩ := h
  have hb_mem : b.val ∈ List.range (N - 1) := List.mem_range.mpr b.isLt
  have hc0_mem : c0.val ∈ List.range (N - 1) := List.mem_range.mpr c0.isLt
  have hmi_mem : mi ∈ [1, 2] := by rcases hmi with rfl | rfl <;> simp
  have hni_mem : ni ∈ [1, 2] := by rcases hni with rfl | rfl <;> simp
  have h1 := List.all_eq_true.mp hcheck b.val hb_mem
  have h2 := List.all_eq_true.mp h1 c0.val hc0_mem
  have h3 := List.all_eq_true.mp h2 mi hmi_mem
  have h4 := List.all_eq_true.mp h3 ni hni_mem
  rw [if_pos hpatB] at h4
  cases hlook : data.lookup (b.val, c0.val, mi, ni) with
  | none => rw [hlook] at h4; simp at h4
  | some wits =>
    rw [hlook] at h4
    obtain ⟨l₁, l₂, hdata, -⟩ := List.lookup_eq_some_iff.mp hlook
    subst hdata
    have hentry : (((b.val, c0.val, mi, ni) : ℕ × ℕ × ℕ × ℕ), wits) ∈
        l₁ ++ (((b.val, c0.val, mi, ni) : ℕ × ℕ × ℕ × ℕ), wits) :: l₂ := by simp
    simp only [ggDepAThreeCases] at h4
    have hm_cast : (m : ZMod p) = (((p - mi) % p : ℕ) : ZMod p) := by
      rw [hm, Int.cast_neg, Int.cast_natCast]
      exact (l05nND_cast_neg p mi (by omega)).symm
    have hn_cast : (n : ZMod p) = (((p - ni) % p : ℕ) : ZMod p) := by
      rw [hn, Int.cast_neg, Int.cast_natCast]
      exact (l05nND_cast_neg p ni (by omega)).symm
    have hpairA : ∀ c : Fin (N - 1), c ≠ b →
        ggDepAdot αa (ggDepAh p N c) = if c = c0 then (((p - mi) % p : ℕ) : ZMod p) else 0 := by
      intro c hc
      rw [(hpairs c hc).1, hm_cast]
    obtain ⟨u, v, huv⟩ :=
      ggDepANAa_complete hpN hN b c0 hb hbc ((p - mi) % p) αa hpairA
    have hpairH : ∀ c : Fin (N - 1), c ≠ b →
        ggDepAdot (ggDepAα p N c) ha = if c = c0 then (((p - ni) % p : ℕ) : ZMod p) else 0 := by
      intro c hc
      rw [(hpairs c hc).2, hn_cast]
    obtain ⟨s, t, hst⟩ :=
      ggDepANHa_complete hN b c0 hb hbc ((p - ni) % p) ha hpairH
    have hs : s % p ∈ List.range p := List.mem_range.mpr (Nat.mod_lt s (by omega))
    have ht : t % p ∈ List.range p := List.mem_range.mpr (Nat.mod_lt t (by omega))
    have hu : u % p ∈ List.range p := List.mem_range.mpr (Nat.mod_lt u (by omega))
    have hv : v % p ∈ List.range p := List.mem_range.mpr (Nat.mod_lt v (by omega))
    have hcase := List.all_eq_true.mp h4 (s % p) hs
    have hcase := List.all_eq_true.mp hcase (t % p) ht
    have hcase := List.all_eq_true.mp hcase (u % p) hu
    have hcase := List.all_eq_true.mp hcase (v % p) hv
    have hxval : ggDepAdot (ggDepANToZ p N
        (ggDepANAaParam p N b.val c0.val ((p - mi) % p) u v)) (ggDepAx p N) =
        ((v % p : ℕ) : ZMod p) := by
      rw [l05nND_dot_ax _ (by omega)]
      show ((ggDepANAaParam p N b.val c0.val ((p - mi) % p) u v).getD (N - 1) 0 : ZMod p) =
        ((v % p : ℕ) : ZMod p)
      rw [l05nND_AaParam_getD p N b.val c0.val ((p - mi) % p) u v (by omega)]
    have hv0 : v % p ≠ 0 := by
      intro hvz
      apply hx
      rw [huv, hxval, hvz]
      simp
    have hdotN : ggDepANDot p (ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) (v % p))
        (ggDepANHaParam p N b.val c0.val ((p - ni) % p) (s % p) (t % p)) = 2 % p := by
      rw [l05nND_AaParam_mod, l05nND_HaParam_mod]
      refine lr7ck_dot_eq_two hp (by rw [ggDepANDot]; exact Nat.mod_lt _ (by omega)) ?_
      rw [ggDepANDot_cast _ _ (l05nND_AaParam_length ..) (l05nND_HaParam_length ..),
        ← huv, ← hst]
      exact hdot2
    have hvv : (v % p) % p ≠ 0 := by
      rwa [Nat.mod_eq_of_lt (Nat.mod_lt v (by omega))]
    have hcond : (ggDepANDot p (ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) (v % p))
        (ggDepANHaParam p N b.val c0.val ((p - ni) % p) (s % p) (t % p)) == 2 % p &&
        (v % p) % p != 0) = true := by
      rw [Bool.and_eq_true]
      exact ⟨beq_iff_eq.mpr hdotN, bne_iff_ne.mpr hvv⟩
    rw [if_pos hcond] at hcase
    have hlenH : (ggDepANHaParam p N b.val c0.val ((p - ni) % p) (s % p) (t % p)).length = N :=
      l05nND_HaParam_length ..
    have hlenA : (ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) (v % p)).length = N :=
      l05nND_AaParam_length ..
    have hHa : ggDepANToZ p N
        (ggDepANHaParam p N b.val c0.val ((p - ni) % p) (s % p) (t % p)) = ha := by
      rw [l05nND_HaParam_mod]
      exact hst.symm
    have hAa : ggDepANToZ p N
        (ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) (v % p)) = αa := by
      rw [l05nND_AaParam_mod]
      exact huv.symm
    rw [Bool.or_eq_true] at hcase
    rcases hcase with hwit | hsurv
    · obtain ⟨w, hwmem, hwtest⟩ := List.any_eq_true.mp hwit
      have hwvalid : ggDepANWitValid N w = true :=
        List.all_eq_true.mp
          (List.all_eq_true.mp hvalid (((b.val, c0.val, mi, ni) : ℕ × ℕ × ℕ × ℕ), wits) hentry)
          w hwmem
      obtain ⟨g, hgmem, hgtv⟩ :=
        ggDepANWitTest_sound (by omega : p ≠ 2) hN w hwvalid
          (ggDepANHaParam p N b.val c0.val ((p - ni) % p) (s % p) (t % p))
          (ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) (v % p))
          hlenH hlenA hdotN hwtest
      refine Or.inl ⟨g, ?_, hgtv⟩
      rw [hHa, hAa] at hgmem
      exact hgmem
    · obtain ⟨r, hrmem, hrtest⟩ := List.any_eq_true.mp hsurv
      refine Or.inr ⟨ggDepANHaParam p N b.val c0.val ((p - ni) % p) (s % p) (t % p),
        ggDepANAaParam p N b.val c0.val ((p - mi) % p) (u % p) (v % p), r, ?_, hlenH,
        hlenA, hHa, hAa, hrtest⟩
      exact lr7ck_lookup_getD_mem _ _ hrmem

theorem ggDepAThree_cells9_of_check (data : GGDepANData)
    (h : ggDepAThreeCheck 3 9 data [] = true) : GGDepAThreeCells9 := by
  intro b c0 m n hpat ha αa hpairs hdot2 hx
  rcases ggDepAThreeCheck_core (p := 3) (N := 9) (by omega) (by decide) (by omega) data [] h
      b c0 m n hpat ha αa hpairs hdot2 hx with hwit | hsurv
  · exact hwit
  · obtain ⟨hl, al, r, hrmem, -⟩ := hsurv
    simp at hrmem

end CFSG.StandardType
