module

public import CFSG.LocalAnalysis.StandardType.GGKacTable
public import CFSG.LocalAnalysis.StandardType.GGKacK0V2
public import CFSG.LocalAnalysis.StandardType.GGKacTableShapes
public import CFSG.LocalAnalysis.StandardType.GGKacTablePatternList

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGKacIdentityDatum (lab : LargeEvenLabel) : GGKacDatum := ⟨[⟨lab, true⟩], 0, 1⟩

private abbrev ltrk0t1_smul (p : ℕ) (l : List ℕ) : List ℕ := l.map (fun x => p * x)

private lemma ltrk0t1_smul_set (n i p : ℕ) :
    ltrk0t1_smul p ((List.replicate n 0).set i 1) = (List.replicate n 0).set i p := by
  rw [ltrk0t1_smul, List.map_set, List.map_replicate, Nat.mul_one]
  rfl

private lemma ltrk0t1_mul_cancel {p a b : ℕ} (hp : 0 < p) (h : p * a = p * b) : a = b :=
  Nat.mul_left_cancel hp h

private lemma ltrk0t1_smul_inj {p : ℕ} (hp : 0 < p) :
    Function.Injective (ltrk0t1_smul p) := by
  intro u v h
  have hlen : u.length = v.length := by
    have := congrArg List.length h
    simpa [ltrk0t1_smul] using this
  apply List.ext_getElem hlen
  intro i hi hi'
  rw [List.getElem_eq_getD (h := hi) 0, List.getElem_eq_getD (h := hi') 0]
  have hg : (u.map (fun x => p * x)).getD i 0 = (v.map (fun x => p * x)).getD i 0 := by
    rw [ltrk0t1_smul] at h
    exact congrArg (fun l => l.getD i 0) h
  rw [k0patAct_getD_map (fun x => p * x) (by rfl),
      k0patAct_getD_map (fun x => p * x) (by rfl)] at hg
  exact Nat.mul_left_cancel hp hg

private lemma ltrk0t1_act_eq_smul_iff {p : ℕ} (hp : 0 < p) (a s : List ℕ) :
    k0pAct a (ltrk0t1_smul p s) = ltrk0t1_smul p s ↔ k0pAct a s = s := by
  rw [ltrk0t1_smul, k0patAct_map a s (fun x => p * x) (by rfl)]
  constructor
  · intro h; exact ltrk0t1_smul_inj hp h
  · intro h; rw [h]

private lemma ltrk0t1_filter_smul (D : K0Diag) (s : List ℕ) (p : ℕ) (hp : 0 < p) :
    D.omega.filter (fun a => decide (k0pAct a (ltrk0t1_smul p s) = ltrk0t1_smul p s))
      = D.omega.filter (fun a => decide (k0pAct a s = s)) := by
  apply List.filter_congr
  intro a _
  exact decide_eq_decide.mpr (ltrk0t1_act_eq_smul_iff hp a s)

private lemma ltrk0t1_lex_smul {p : ℕ} (hp : 0 < p) (u w : List ℕ) :
    k0LexLtNat (ltrk0t1_smul p u) (ltrk0t1_smul p w) = k0LexLtNat u w := by
  induction u generalizing w with
  | nil => cases w <;> rfl
  | cons x xs ih =>
      cases w with
      | nil => rfl
      | cons y ys =>
          have h1 : p * x < p * y ↔ x < y := Nat.mul_lt_mul_left hp
          have h2 : p * y < p * x ↔ y < x := Nat.mul_lt_mul_left hp
          show (if p * x < p * y then true
              else if p * y < p * x then false
              else k0LexLtNat (ltrk0t1_smul p xs) (ltrk0t1_smul p ys)) =
            (if x < y then true else if y < x then false else k0LexLtNat xs ys)
          simp only [h1, h2, ih ys]

private lemma ltrk0t1_insertBy_smul {p : ℕ} (hp : 0 < p) (a : List ℕ) (l : List (List ℕ)) :
    k0InsertBy k0LexLtNat (ltrk0t1_smul p a) (l.map (ltrk0t1_smul p))
      = (k0InsertBy k0LexLtNat a l).map (ltrk0t1_smul p) := by
  induction l with
  | nil => simp [k0InsertBy]
  | cons b bs ih =>
      simp only [List.map_cons, k0InsertBy]
      rw [ltrk0t1_lex_smul hp a b]
      by_cases h : k0LexLtNat a b
      · simp [h]
      · simp [h, ih]

private lemma ltrk0t1_sortBy_smul {p : ℕ} (hp : 0 < p) (l : List (List ℕ)) :
    k0SortBy k0LexLtNat (l.map (ltrk0t1_smul p))
      = (k0SortBy k0LexLtNat l).map (ltrk0t1_smul p) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, k0SortBy]
      rw [ih, ltrk0t1_insertBy_smul hp a (k0SortBy k0LexLtNat as)]

private lemma ltrk0t1_orbMin_smul (D : K0Diag) (s : List ℕ) (p : ℕ) (hp : 0 < p) :
    k0OrbMin D (ltrk0t1_smul p s) = ltrk0t1_smul p (k0OrbMin D s) := by
  unfold k0OrbMin
  have hmap : D.omega.map (fun a => k0pAct a (ltrk0t1_smul p s))
      = (D.omega.map (fun a => k0pAct a s)).map (ltrk0t1_smul p) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a _
    exact k0patAct_map a s (fun x => p * x) (by rfl)
  rw [hmap, ltrk0t1_sortBy_smul hp]
  cases h : k0SortBy k0LexLtNat (D.omega.map (fun a => k0pAct a s)) with
  | nil => rfl
  | cons c cs => rfl

private lemma ltrk0t1_vecsAux_zero (ms : List ℕ) :
    List.replicate ms.length 0 ∈ k0VecsAux ms 0 := by
  induction ms with
  | nil => simp [k0VecsAux]
  | cons m ms ih =>
      unfold k0VecsAux
      rw [k0shape_mem_foldr_append]
      refine ⟨0, List.mem_range.mpr (Nat.zero_lt_succ _), ?_⟩
      rw [List.mem_map]
      refine ⟨List.replicate ms.length 0, ?_, ?_⟩
      · rw [show 0 - 0 * m = 0 by omega]
        exact ih
      · rw [List.length_cons, List.replicate_succ]

private lemma ltrk0t1_vecsAux_set (ms : List ℕ) (i p : ℕ) (hi : i < ms.length)
    (hmark : ms.getD i 0 = 1) :
    (List.replicate ms.length 0).set i p ∈ k0VecsAux ms p := by
  induction ms generalizing i with
  | nil => simp at hi
  | cons m ms ih =>
      cases i with
      | zero =>
          simp only [List.getD_cons_zero] at hmark
          rw [hmark, List.length_cons, List.replicate_succ, List.set_cons_zero]
          unfold k0VecsAux
          rw [k0shape_mem_foldr_append]
          refine ⟨p, ?_, ?_⟩
          · rw [Nat.div_one]
            exact List.mem_range.mpr (Nat.lt_succ_self p)
          · rw [List.mem_map]
            refine ⟨List.replicate ms.length 0, ?_, rfl⟩
            rw [show p - p * 1 = 0 by omega]
            exact ltrk0t1_vecsAux_zero ms
      | succ j =>
          rw [List.length_cons, List.replicate_succ, List.set_cons_succ]
          unfold k0VecsAux
          rw [k0shape_mem_foldr_append]
          refine ⟨0, List.mem_range.mpr (Nat.zero_lt_succ _), ?_⟩
          rw [List.mem_map]
          refine ⟨(List.replicate ms.length 0).set j p, ?_, rfl⟩
          have hj : j < ms.length := by simpa using hi
          have hmark' : ms.getD j 0 = 1 := by
            rw [List.getD_cons_succ] at hmark
            exact hmark
          rw [show p - 0 * m = p by rw [Nat.zero_mul, Nat.sub_zero]]
          exact ih j hj hmark'

private lemma ltrk0t1_baseAux_smul (rho0 s : List ℕ) (p : ℕ) (hp : 0 < p)
    (l : List (List ℕ)) :
    k0BaseAux rho0 (ltrk0t1_smul p s) l = k0BaseAux rho0 s l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      simp only [k0BaseAux]
      by_cases h : k0pAct (k0pMul a rho0) s = s
      · rw [if_pos ((ltrk0t1_act_eq_smul_iff hp (k0pMul a rho0) s).mpr h), if_pos h]
      · rw [if_neg (fun hh => h ((ltrk0t1_act_eq_smul_iff hp (k0pMul a rho0) s).mp hh)),
          if_neg h]
        exact ih

private lemma ltrk0t1_kacBase_smul (D : K0Diag) (rho0 s : List ℕ) (p : ℕ) (hp : 0 < p) :
    k0KacBase D rho0 (ltrk0t1_smul p s) = k0KacBase D rho0 s :=
  ltrk0t1_baseAux_smul rho0 s p hp D.omega

private lemma ltrk0t1_datum_zeroSet (D : K0Diag) {s s' : List ℕ} {rho : List ℕ} {d n st : ℕ}
    (h : ∀ i, s'.getD i 0 = 0 ↔ s.getD i 0 = 0) :
    k0Datum D s' rho d n st = k0Datum D s rho d n st := by
  have hpos : ∀ i, s'.getD i 0 > 0 ↔ s.getD i 0 > 0 := by
    intro i
    change 0 < s'.getD i 0 ↔ 0 < s.getD i 0
    rw [Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero]
    exact not_congr (h i)
  have hf : (List.range D.marks.length).filter (fun i => decide (s'.getD i 0 > 0))
      = (List.range D.marks.length).filter (fun i => decide (s.getD i 0 > 0)) := by
    apply List.filter_congr
    intro i _
    exact decide_eq_decide.mpr (hpos i)
  have horb : (k0Datum D s' rho d n st).orbits = (k0Datum D s rho d n st).orbits := by
    rw [ggKacShDatum_orbits_shapes D s' rho d n st,
        ggKacShDatum_orbits_shapes D s rho d n st,
        ggKacShShapes_congr (D := D) (s := s) (s' := s') (rho := rho) (d := d) h]
  have hrz : (k0Datum D s' rho d n st).rZ = (k0Datum D s rho d n st).rZ := by
    dsimp only [k0Datum]
    rw [hf]
  calc
    k0Datum D s' rho d n st
        = ⟨(k0Datum D s' rho d n st).orbits, (k0Datum D s' rho d n st).rZ, st⟩ := rfl
    _ = ⟨(k0Datum D s rho d n st).orbits, (k0Datum D s rho d n st).rZ, st⟩ := by
          rw [horb, hrz]
    _ = k0Datum D s rho d n st := rfl

private lemma ltrk0t1_datum_smul (D : K0Diag) (s rho : List ℕ) (d n st p : ℕ) (hp : 0 < p) :
    k0Datum D (ltrk0t1_smul p s) rho d n st = k0Datum D s rho d n st := by
  apply ltrk0t1_datum_zeroSet
  intro i
  rw [ltrk0t1_smul, k0patAct_getD_map (fun x => p * x) (by rfl)]
  constructor
  · intro h; exact (Nat.mul_eq_zero.mp h).resolve_left hp.ne'
  · intro h; rw [h, Nat.mul_zero]

private lemma ltrk0t1_datumsOf_smul (D : K0Diag) (rho0 s : List ℕ) (d n p : ℕ) (hp : 0 < p) :
    k0DatumsOf D rho0 (ltrk0t1_smul p s) d n = k0DatumsOf D rho0 s d n := by
  have hstab := ltrk0t1_filter_smul D s p hp
  unfold k0DatumsOf
  rw [ltrk0t1_kacBase_smul D rho0 s p hp]
  generalize hb : k0KacBase D rho0 s = bb
  cases bb with
  | none => rfl
  | some base =>
      rw [hstab]
      apply List.map_congr_left
      intro rho _
      exact ltrk0t1_datum_smul D s rho d n _ p hp

private lemma ltrk0t1_mem_rawDatums_of {D : K0Diag} {tw : Bool} {p n d : ℕ}
    {D₀ : GGKacDatum} {s : List ℕ} (hvec : s ∈ k0VecsAux D.marks p) (hmin : k0OrbMin D s = s)
    (hdat : D₀ ∈ k0DatumsOf D (k0Rho0 D tw d) s d n) :
    D₀ ∈ k0RawDatums D tw p n d := by
  rw [k0RawDatums]
  simp only [k0shape_mem_foldr_append]
  refine ⟨s, ?_, hdat⟩
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨hvec, hmin⟩

private lemma ltrk0t1_rawMem_smul (D : K0Diag) (tw : Bool) (d n p : ℕ) (s₁ : List ℕ)
    (D₀ : GGKacDatum)
    (hp : 0 < p) (hvec : ltrk0t1_smul p s₁ ∈ k0VecsAux D.marks p)
    (hmin : k0OrbMin D (ltrk0t1_smul p s₁) = ltrk0t1_smul p s₁)
    (hdat : D₀ ∈ k0DatumsOf D (k0Rho0 D tw d) s₁ d n) :
    D₀ ∈ k0RawDatums D tw p n d := by
  refine ltrk0t1_mem_rawDatums_of hvec hmin ?_
  rw [ltrk0t1_datumsOf_smul D (k0Rho0 D tw d) s₁ d n p hp]
  exact hdat

private lemma ltrk0t1_not_dvd_neg {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) :
    p ∣ 2 ^ n + 1 → ¬ p ∣ 2 ^ n - 1 := by
  intro h2 h1
  have hsub : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h2 h1
  have heq : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
    have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have hpdiv2 : p ∣ 2 := by rwa [heq] at hsub
  have hpeq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdiv2
  exact hp2 hpeq

private abbrev ltrk0t1_sE6 : List ℕ := (List.replicate 7 0).set 6 1
private abbrev ltrk0t1_sE7 : List ℕ := (List.replicate 8 0).set 7 1
private abbrev ltrk0t1_sE8 : List ℕ := (List.replicate 9 0).set 0 1
private abbrev ltrk0t1_sF4 : List ℕ := (List.replicate 5 0).set 0 1

private lemma ltrk0t1_E6f1 (n p : ℕ) (hp : 0 < p) :
    (⟨[⟨⟨.E6, 0, n⟩, true⟩], 0, 1⟩ : GGKacDatum) ∈ k0RawDatums k0E6Diag false p n 1 := by
  refine ltrk0t1_rawMem_smul k0E6Diag false 1 n p ltrk0t1_sE6 _ hp ?_ ?_ ?_
  · rw [ltrk0t1_smul_set 7 6 p]
    exact ltrk0t1_vecsAux_set k0E6Diag.marks 6 p (by decide) (by decide)
  · rw [ltrk0t1_orbMin_smul k0E6Diag ltrk0t1_sE6 p hp,
      show k0OrbMin k0E6Diag ltrk0t1_sE6 = ltrk0t1_sE6 from by decide]
  · rw [show k0DatumsOf k0E6Diag (k0Rho0 k0E6Diag false 1) ltrk0t1_sE6 1 n
        = [⟨[⟨⟨.E6, 0, 1 * n⟩, true⟩], 0, 1⟩] from rfl]
    exact List.mem_singleton.mpr (by rw [Nat.one_mul])

private lemma ltrk0t1_E6f2 (n p : ℕ) (hp : 0 < p) :
    (⟨[⟨⟨.E6, 0, n⟩, true⟩], 0, 1⟩ : GGKacDatum) ∈ k0RawDatums k0E6Diag false p n 2 := by
  refine ltrk0t1_rawMem_smul k0E6Diag false 2 n p ltrk0t1_sE6 _ hp ?_ ?_ ?_
  · rw [ltrk0t1_smul_set 7 6 p]
    exact ltrk0t1_vecsAux_set k0E6Diag.marks 6 p (by decide) (by decide)
  · rw [ltrk0t1_orbMin_smul k0E6Diag ltrk0t1_sE6 p hp,
      show k0OrbMin k0E6Diag ltrk0t1_sE6 = ltrk0t1_sE6 from by decide]
  · rw [show k0DatumsOf k0E6Diag (k0Rho0 k0E6Diag false 2) ltrk0t1_sE6 2 n
        = [⟨[⟨⟨.E6, 0, 1 * n⟩, true⟩], 0, 1⟩] from rfl]
    exact List.mem_singleton.mpr (by rw [Nat.one_mul])

private lemma ltrk0t1_twE6f1 (n p : ℕ) (hp : 0 < p) :
    (⟨[⟨⟨.twE6, 0, n⟩, true⟩], 0, 1⟩ : GGKacDatum) ∈ k0RawDatums k0E6Diag true p n 1 := by
  refine ltrk0t1_rawMem_smul k0E6Diag true 1 n p ltrk0t1_sE6 _ hp ?_ ?_ ?_
  · rw [ltrk0t1_smul_set 7 6 p]
    exact ltrk0t1_vecsAux_set k0E6Diag.marks 6 p (by decide) (by decide)
  · rw [ltrk0t1_orbMin_smul k0E6Diag ltrk0t1_sE6 p hp,
      show k0OrbMin k0E6Diag ltrk0t1_sE6 = ltrk0t1_sE6 from by decide]
  · rw [show k0DatumsOf k0E6Diag (k0Rho0 k0E6Diag true 1) ltrk0t1_sE6 1 n
        = [⟨[⟨⟨.twE6, 0, 1 * n⟩, true⟩], 0, 1⟩] from rfl]
    exact List.mem_singleton.mpr (by rw [Nat.one_mul])

private lemma ltrk0t1_twE6f2 (n p : ℕ) (hp : 0 < p) :
    (⟨[⟨⟨.twE6, 0, n⟩, true⟩], 0, 1⟩ : GGKacDatum) ∈ k0RawDatums k0E6Diag true p n 2 := by
  refine ltrk0t1_rawMem_smul k0E6Diag true 2 n p ltrk0t1_sE6 _ hp ?_ ?_ ?_
  · rw [ltrk0t1_smul_set 7 6 p]
    exact ltrk0t1_vecsAux_set k0E6Diag.marks 6 p (by decide) (by decide)
  · rw [ltrk0t1_orbMin_smul k0E6Diag ltrk0t1_sE6 p hp,
      show k0OrbMin k0E6Diag ltrk0t1_sE6 = ltrk0t1_sE6 from by decide]
  · rw [show k0DatumsOf k0E6Diag (k0Rho0 k0E6Diag true 2) ltrk0t1_sE6 2 n
        = [⟨[⟨⟨.twE6, 0, 1 * n⟩, true⟩], 0, 1⟩] from rfl]
    exact List.mem_singleton.mpr (by rw [Nat.one_mul])

private lemma ltrk0t1_E71 (n p : ℕ) (hp : 0 < p) :
    (⟨[⟨⟨.E7, 0, n⟩, true⟩], 0, 1⟩ : GGKacDatum) ∈ k0RawDatums k0E7Diag false p n 1 := by
  refine ltrk0t1_rawMem_smul k0E7Diag false 1 n p ltrk0t1_sE7 _ hp ?_ ?_ ?_
  · rw [ltrk0t1_smul_set 8 7 p]
    exact ltrk0t1_vecsAux_set k0E7Diag.marks 7 p (by decide) (by decide)
  · rw [ltrk0t1_orbMin_smul k0E7Diag ltrk0t1_sE7 p hp,
      show k0OrbMin k0E7Diag ltrk0t1_sE7 = ltrk0t1_sE7 from by decide]
  · rw [show k0DatumsOf k0E7Diag (k0Rho0 k0E7Diag false 1) ltrk0t1_sE7 1 n
        = [⟨[⟨⟨.E7, 0, 1 * n⟩, true⟩], 0, 1⟩] from rfl]
    exact List.mem_singleton.mpr (by rw [Nat.one_mul])

private lemma ltrk0t1_E72 (n p : ℕ) (hp : 0 < p) :
    (⟨[⟨⟨.E7, 0, n⟩, true⟩], 0, 1⟩ : GGKacDatum) ∈ k0RawDatums k0E7Diag false p n 2 := by
  refine ltrk0t1_rawMem_smul k0E7Diag false 2 n p ltrk0t1_sE7 _ hp ?_ ?_ ?_
  · rw [ltrk0t1_smul_set 8 7 p]
    exact ltrk0t1_vecsAux_set k0E7Diag.marks 7 p (by decide) (by decide)
  · rw [ltrk0t1_orbMin_smul k0E7Diag ltrk0t1_sE7 p hp,
      show k0OrbMin k0E7Diag ltrk0t1_sE7 = ltrk0t1_sE7 from by decide]
  · rw [show k0DatumsOf k0E7Diag (k0Rho0 k0E7Diag false 2) ltrk0t1_sE7 2 n
        = [⟨[⟨⟨.E7, 0, 1 * n⟩, true⟩], 0, 1⟩] from rfl]
    exact List.mem_singleton.mpr (by rw [Nat.one_mul])

private lemma ltrk0t1_E81 (n p : ℕ) (hp : 0 < p) :
    (⟨[⟨⟨.E8, 0, n⟩, true⟩], 0, 1⟩ : GGKacDatum) ∈ k0RawDatums k0E8Diag false p n 1 := by
  refine ltrk0t1_rawMem_smul k0E8Diag false 1 n p ltrk0t1_sE8 _ hp ?_ ?_ ?_
  · rw [ltrk0t1_smul_set 9 0 p]
    exact ltrk0t1_vecsAux_set k0E8Diag.marks 0 p (by decide) (by decide)
  · rw [ltrk0t1_orbMin_smul k0E8Diag ltrk0t1_sE8 p hp,
      show k0OrbMin k0E8Diag ltrk0t1_sE8 = ltrk0t1_sE8 from by decide]
  · rw [show k0DatumsOf k0E8Diag (k0Rho0 k0E8Diag false 1) ltrk0t1_sE8 1 n
        = [⟨[⟨⟨.E8, 0, 1 * n⟩, true⟩], 0, 1⟩] from rfl]
    exact List.mem_singleton.mpr (by rw [Nat.one_mul])

private lemma ltrk0t1_E82 (n p : ℕ) (hp : 0 < p) :
    (⟨[⟨⟨.E8, 0, n⟩, true⟩], 0, 1⟩ : GGKacDatum) ∈ k0RawDatums k0E8Diag false p n 2 := by
  refine ltrk0t1_rawMem_smul k0E8Diag false 2 n p ltrk0t1_sE8 _ hp ?_ ?_ ?_
  · rw [ltrk0t1_smul_set 9 0 p]
    exact ltrk0t1_vecsAux_set k0E8Diag.marks 0 p (by decide) (by decide)
  · rw [ltrk0t1_orbMin_smul k0E8Diag ltrk0t1_sE8 p hp,
      show k0OrbMin k0E8Diag ltrk0t1_sE8 = ltrk0t1_sE8 from by decide]
  · rw [show k0DatumsOf k0E8Diag (k0Rho0 k0E8Diag false 2) ltrk0t1_sE8 2 n
        = [⟨[⟨⟨.E8, 0, 1 * n⟩, true⟩], 0, 1⟩] from rfl]
    exact List.mem_singleton.mpr (by rw [Nat.one_mul])

private lemma ltrk0t1_F41 (n p : ℕ) (hp : 0 < p) :
    (⟨[⟨⟨.F4, 0, n⟩, true⟩], 0, 1⟩ : GGKacDatum) ∈ k0RawDatums k0F4Diag false p n 1 := by
  refine ltrk0t1_rawMem_smul k0F4Diag false 1 n p ltrk0t1_sF4 _ hp ?_ ?_ ?_
  · rw [ltrk0t1_smul_set 5 0 p]
    exact ltrk0t1_vecsAux_set k0F4Diag.marks 0 p (by decide) (by decide)
  · rw [ltrk0t1_orbMin_smul k0F4Diag ltrk0t1_sF4 p hp,
      show k0OrbMin k0F4Diag ltrk0t1_sF4 = ltrk0t1_sF4 from by decide]
  · rw [show k0DatumsOf k0F4Diag (k0Rho0 k0F4Diag false 1) ltrk0t1_sF4 1 n
        = [⟨[⟨⟨.F4, 0, 1 * n⟩, true⟩], 0, 1⟩] from rfl]
    exact List.mem_singleton.mpr (by rw [Nat.one_mul])

private lemma ltrk0t1_F42 (n p : ℕ) (hp : 0 < p) :
    (⟨[⟨⟨.F4, 0, n⟩, true⟩], 0, 1⟩ : GGKacDatum) ∈ k0RawDatums k0F4Diag false p n 2 := by
  refine ltrk0t1_rawMem_smul k0F4Diag false 2 n p ltrk0t1_sF4 _ hp ?_ ?_ ?_
  · rw [ltrk0t1_smul_set 5 0 p]
    exact ltrk0t1_vecsAux_set k0F4Diag.marks 0 p (by decide) (by decide)
  · rw [ltrk0t1_orbMin_smul k0F4Diag ltrk0t1_sF4 p hp,
      show k0OrbMin k0F4Diag ltrk0t1_sF4 = ltrk0t1_sF4 from by decide]
  · rw [show k0DatumsOf k0F4Diag (k0Rho0 k0F4Diag false 2) ltrk0t1_sF4 2 n
        = [⟨[⟨⟨.F4, 0, 1 * n⟩, true⟩], 0, 1⟩] from rfl]
    exact List.mem_singleton.mpr (by rw [Nat.one_mul])

theorem ggKacValid_identityDatum {lab : LargeEvenLabel} {p : ℕ} (hΛ : LargeEvenInLambda2 lab)
    (hpair : GGKacExcPair lab p) : GGKacValid lab p (GGKacIdentityDatum lab) := by
  obtain ⟨tag, rk, n⟩ := lab
  obtain ⟨hpprime, hpne2, hbranch, htag⟩ := hpair
  have hp : 0 < p := hpprime.pos
  rcases htag with hE6 | htwE6 | hE7 | hE8 | hF4
  · subst hE6
    obtain ⟨hn, hrk⟩ : 1 ≤ n ∧ rk = 0 := by simpa only [LargeEvenInLambda2] using hΛ
    subst hrk
    refine ⟨.E6, false, rfl, ?_⟩
    rcases hbranch with h1 | h2
    · rw [k0shape_table_branch1 .E6 false p n h1]
      exact (k0shape_sortDatums_perm _).mem_iff.mpr (ltrk0t1_E6f1 n p hp)
    · have h1' : ¬ p ∣ 2 ^ n - 1 := ltrk0t1_not_dvd_neg hpprime hpne2 hn h2
      rw [k0shape_table_branch2 .E6 false p n h1' h2]
      exact (k0shape_sortDatums_perm _).mem_iff.mpr (ltrk0t1_E6f2 n p hp)
  · subst htwE6
    obtain ⟨hn, hrk⟩ : 1 ≤ n ∧ rk = 0 := by simpa only [LargeEvenInLambda2] using hΛ
    subst hrk
    refine ⟨.E6, true, rfl, ?_⟩
    rcases hbranch with h1 | h2
    · rw [k0shape_table_branch1 .E6 true p n h1]
      exact (k0shape_sortDatums_perm _).mem_iff.mpr (ltrk0t1_twE6f1 n p hp)
    · have h1' : ¬ p ∣ 2 ^ n - 1 := ltrk0t1_not_dvd_neg hpprime hpne2 hn h2
      rw [k0shape_table_branch2 .E6 true p n h1' h2]
      exact (k0shape_sortDatums_perm _).mem_iff.mpr (ltrk0t1_twE6f2 n p hp)
  · subst hE7
    obtain ⟨hn, hrk⟩ : 1 ≤ n ∧ rk = 0 := by simpa only [LargeEvenInLambda2] using hΛ
    subst hrk
    refine ⟨.E7, false, rfl, ?_⟩
    rcases hbranch with h1 | h2
    · rw [k0shape_table_branch1 .E7 false p n h1]
      exact (k0shape_sortDatums_perm _).mem_iff.mpr (ltrk0t1_E71 n p hp)
    · have h1' : ¬ p ∣ 2 ^ n - 1 := ltrk0t1_not_dvd_neg hpprime hpne2 hn h2
      rw [k0shape_table_branch2 .E7 false p n h1' h2]
      exact (k0shape_sortDatums_perm _).mem_iff.mpr (ltrk0t1_E72 n p hp)
  · subst hE8
    obtain ⟨hn, hrk⟩ : 1 ≤ n ∧ rk = 0 := by simpa only [LargeEvenInLambda2] using hΛ
    subst hrk
    refine ⟨.E8, false, rfl, ?_⟩
    rcases hbranch with h1 | h2
    · rw [k0shape_table_branch1 .E8 false p n h1]
      exact (k0shape_sortDatums_perm _).mem_iff.mpr (ltrk0t1_E81 n p hp)
    · have h1' : ¬ p ∣ 2 ^ n - 1 := ltrk0t1_not_dvd_neg hpprime hpne2 hn h2
      rw [k0shape_table_branch2 .E8 false p n h1' h2]
      exact (k0shape_sortDatums_perm _).mem_iff.mpr (ltrk0t1_E82 n p hp)
  · subst hF4
    obtain ⟨hn, hrk⟩ : 1 ≤ n ∧ rk = 0 := by simpa only [LargeEvenInLambda2] using hΛ
    subst hrk
    refine ⟨.F4, false, rfl, ?_⟩
    rcases hbranch with h1 | h2
    · rw [k0shape_table_branch1 .F4 false p n h1]
      exact (k0shape_sortDatums_perm _).mem_iff.mpr (ltrk0t1_F41 n p hp)
    · have h1' : ¬ p ∣ 2 ^ n - 1 := ltrk0t1_not_dvd_neg hpprime hpne2 hn h2
      rw [k0shape_table_branch2 .F4 false p n h1' h2]
      exact (k0shape_sortDatums_perm _).mem_iff.mpr (ltrk0t1_F42 n p hp)

end CFSG.StandardType

end
