module

public import CFSG.LocalAnalysis.StandardType.GGTWNatWord

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nE4_cast_sub (p : ℕ) [Fact p.Prime] (x y : ℕ) :
    (((x + (p - y % p)) % p : ℕ) : ZMod p) = (x : ZMod p) - (y : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (le_of_lt (Nat.mod_lt y hp)),
    ZMod.natCast_self, ZMod.natCast_mod]
  ring

private lemma l05nE4_sub_length {p N : ℕ} {a b : List ℕ} (ha : a.length = N) (hb : b.length = N) :
    (ggDepANSub p a b).length = N := by
  simp only [ggDepANSub, List.length_zipWith, ha, hb, min_self]

private lemma l05nE4_smul_length {p N k : ℕ} {a : List ℕ} (ha : a.length = N) :
    (ggDepANSmul p k a).length = N := by
  simp only [ggDepANSmul, List.length_map, ha]

private lemma l05nE4_toZ_sub {p N : ℕ} [Fact p.Prime] {a b : List ℕ} (ha : a.length = N)
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
  exact l05nE4_cast_sub p _ _

private lemma l05nE4_toZ_smul {p N : ℕ} [Fact p.Prime] {a : List ℕ} (ha : a.length = N) (k : ℕ) :
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

private lemma l05nE4_form_apply {p N : ℕ} (f v : GGDepAE p N) :
    ggDepAform f v = ggDepAdot f v := by
  simp [ggDepAform, ggDepAdot]

private lemma l05nE4_refl_apply {p N : ℕ} (c f v : GGDepAE p N) :
    ggDepARefl c f v = v - ggDepAdot f v • c := by
  simp [ggDepARefl, l05nE4_form_apply]

private lemma l05nE4_toZ_refl {p N : ℕ} [Fact p.Prime] {q : GGDepANPair} {v : List ℕ}
    (hq1 : q.1.length = N - 1) (hq2 : q.2.length = N - 1) (hv : v.length = N - 1) :
    ggTWNToZ p N (ggTWNRefl p q v) =
      ggTWRefl (ggTWNToZ p N q.1) (ggTWNToZ p N q.2) (ggTWNToZ p N v) := by
  unfold ggTWNRefl ggTWNToZ ggTWRefl
  rw [l05nE4_toZ_sub hv (l05nE4_smul_length hq1), l05nE4_toZ_smul hq1,
    ggDepANDot_cast q.2 v hq2 hv]
  rw [l05nE4_refl_apply]

private lemma l05nE4_refl_length {p N : ℕ} {q : GGDepANPair} {v : List ℕ}
    (hq1 : q.1.length = N) (hv : v.length = N) :
    (ggTWNRefl p q v).length = N := by
  rw [ggTWNRefl]
  exact l05nE4_sub_length hv (l05nE4_smul_length hq1)

private lemma l05nE4_apply_length {p N : ℕ} (w : List ℕ) (v : List ℕ) (hv : v.length = N - 1)
    (hw : ∀ g ∈ w, g + 1 < N) :
    (ggTWNApply p N w v).length = N - 1 := by
  induction w generalizing v with
  | nil => simpa [ggTWNApply] using hv
  | cons g w ih =>
      have htaillen : (ggTWNApply p N w v).length = N - 1 :=
        ih v hv (fun g' hg' => hw g' (List.mem_cons_of_mem g hg'))
      change (ggTWNRefl p (ggTWNH p N g, ggTWNA p N g) (ggTWNApply p N w v)).length = N - 1
      exact l05nE4_refl_length (ggTWNH_length p N g) htaillen

private lemma l05nE4_foldl_length {N : ℕ} {l : List ℕ} {f : List ℕ → ℕ → List ℕ}
    (hf : ∀ acc k, acc.length = N - 1 → (f acc k).length = N - 1) (init : List ℕ)
    (hinit : init.length = N - 1) : (l.foldl f init).length = N - 1 := by
  induction l generalizing init with
  | nil => simpa using hinit
  | cons k ks ih => simp only [List.foldl_cons]; exact ih (f init k) (hf init k hinit)

private lemma l05nE4_sum_length (p N i j : ℕ) :
    (((List.range (N - 1)).filter fun k => decide (i ≤ k) && decide (k ≤ j)).foldl
      (fun acc k => ggTWNAdd p acc (ggTWNH p N k)) (List.replicate (N - 1) 0)).length
        = N - 1 :=
  l05nE4_foldl_length
    (l := (List.range (N - 1)).filter fun k => decide (i ≤ k) && decide (k ≤ j))
    (f := fun acc k => ggTWNAdd p acc (ggTWNH p N k))
    (fun acc k hacc => by rw [ggTWNAdd, List.length_zipWith, hacc, ggTWNH_length, min_self])
    (List.replicate (N - 1) 0) (by rw [List.length_replicate])

private lemma l05nE4_roots_length {p N : ℕ} {u : List ℕ} (hu : u ∈ ggTWNRoots p N) :
    u.length = N - 1 := by
  unfold ggTWNRoots at hu
  simp only [List.mem_flatMap, List.mem_range] at hu
  obtain ⟨i, _hi, j, _hj, hu⟩ := hu
  by_cases hij : i ≤ j
  · rw [if_pos hij] at hu
    simp only [List.mem_cons] at hu
    rcases hu with rfl | rfl | hu
    · exact l05nE4_sum_length p N i j
    · rw [ggDepANSmul, List.length_map]
      exact l05nE4_sum_length p N i j
    · cases hu
  · rw [if_neg hij] at hu
    cases hu

private lemma l05nE4_contains_of_OK {p N : ℕ} (hR : ggTWNRootsOK p N (ggTWNRoots p N) = true) :
    ∀ i : Fin (N - 1), ggTWNH p N i.val ∈ ggTWNRoots p N := by
  intro i
  have h1 : ((List.range (N - 1)).all fun i => (ggTWNRoots p N).contains (ggTWNH p N i))
      = true := by
    have h := hR
    simp only [ggTWNRootsOK, Bool.and_eq_true] at h
    exact h.1.1
  exact List.contains_iff_mem.mp ((List.all_eq_true.mp h1) i.val (List.mem_range.mpr i.isLt))

private lemma l05nE4_stable_of_OK {p N : ℕ} (hR : ggTWNRootsOK p N (ggTWNRoots p N) = true) :
    ∀ u ∈ ggTWNRoots p N, ∀ g : Fin (N - 1),
      ggTWNRefl p (ggTWNH p N g.val, ggTWNA p N g.val) u ∈ ggTWNRoots p N := by
  intro u hu g
  have h3 : (ggTWNRoots p N).all (fun u => (List.range (N - 1)).all fun g =>
      (ggTWNRoots p N).contains (ggTWNRefl p (ggTWNH p N g, ggTWNA p N g) u)) = true := by
    have h := hR
    simp only [ggTWNRootsOK, Bool.and_eq_true] at h
    exact h.2
  have hinner := (List.all_eq_true.mp h3) u hu
  exact List.contains_iff_mem.mp ((List.all_eq_true.mp hinner) g.val (List.mem_range.mpr g.isLt))

private lemma l05nE4_firstNZ_spec {p : ℕ} {l : List ℕ} {i : ℕ}
    (h : ggDepANFirstNZ p l = some i) :
    i < l.length ∧ (l.getD i 0 % p != 0) = true := by
  rw [ggDepANFirstNZ] at h
  refine ⟨List.mem_range.mp (List.mem_of_find?_eq_some
    (p := fun j => l.getD j 0 % p != 0) (a := i) h), ?_⟩
  exact List.find?_some (p := fun j => l.getD j 0 % p != 0) (a := i) h

private lemma l05nE4_natCast_mod_ne_zero {p x : ℕ} (hx : x % p ≠ 0) : (x : ZMod p) ≠ 0 := by
  intro h0
  exact hx (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff x p).mp h0))

private lemma l05nE4_natCast_eq_zero_of_mod_eq {p x : ℕ} (hx : x % p = 0) :
    (x : ZMod p) = 0 :=
  (ZMod.natCast_eq_zero_iff x p).mpr (Nat.dvd_of_mod_eq_zero hx)

private lemma l05nE4_mod_eq_of_natCast_eq {p x y : ℕ} (h : (x : ZMod p) = (y : ZMod p)) :
    x % p = y % p := (ZMod.natCast_eq_natCast_iff' x y p).mp h

private lemma l05nE4_par_of_prop {p : ℕ} [Fact p.Prime] {a b : List ℕ} {c : ZMod p}
    (hc : c ≠ 0) (hprop : ∀ j : ℕ, j < a.length →
      (b.getD j 0 : ZMod p) = c * (a.getD j 0 : ZMod p))
    {i : ℕ} (hfirst : ggDepANFirstNZ p a = some i) :
    ggDepANPar p a b = true := by
  obtain ⟨hi_lt, hi_pred⟩ := l05nE4_firstNZ_spec hfirst
  have hai_mod : a.getD i 0 % p ≠ 0 := bne_iff_ne.mp hi_pred
  have hai : (a.getD i 0 : ZMod p) ≠ 0 := l05nE4_natCast_mod_ne_zero hai_mod
  rw [ggDepANPar, hfirst, Bool.and_eq_true]
  constructor
  · rw [bne_iff_ne]
    intro hmod
    have hbi : (b.getD i 0 : ZMod p) = 0 := l05nE4_natCast_eq_zero_of_mod_eq hmod
    rw [hprop i hi_lt] at hbi
    exact mul_ne_zero hc hai hbi
  · rw [List.all_eq_true]
    intro k hk
    rw [List.mem_range] at hk
    rw [beq_iff_eq]
    apply l05nE4_mod_eq_of_natCast_eq
    rw [Nat.cast_mul, Nat.cast_mul, hprop k hk, hprop i hi_lt]
    ring

private lemma l05nE4_getD_take {α : Type*} (l : List α) (k : ℕ) (d : α) {j : ℕ} (hj : j < k) :
    (l.take k).getD j d = l.getD j d := by
  by_cases hlen : j < l.length
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_take]; exact lt_min hj hlen),
      List.getD_eq_getElem _ _ hlen]
    rw [List.getElem_take]
  · rw [List.getD_eq_default _ _ (by rw [List.length_take]; omega),
      List.getD_eq_default _ _ (by omega)]

private lemma l05nE4_x_apply_zero {p N : ℕ} (j : Fin (N - 1)) (hj : j.val < N - 2) :
    ggTWx p N j = 0 := by
  simp only [ggTWx]
  rw [if_neg (by change ¬ (j.val + 2 = N); omega)]

private lemma l05nE4_orbit_aux {p N : ℕ} [Fact p.Prime]
    (hcontains : ∀ i : Fin (N - 1), ggTWNH p N i.val ∈ ggTWNRoots p N)
    (hstable : ∀ u ∈ ggTWNRoots p N, ∀ g : Fin (N - 1),
      ggTWNRefl p (ggTWNH p N g.val, ggTWNA p N g.val) u ∈ ggTWNRoots p N)
    (hlen : ∀ u ∈ ggTWNRoots p N, u.length = N - 1) :
    ∀ W ∈ Submonoid.closure (ggTWFrameGens p N), ∀ u ∈ ggTWNRoots p N,
      ∃ u' ∈ ggTWNRoots p N, ggTWNToZ p N u' = W (ggTWNToZ p N u) := by
  intro W hW
  induction hW using Submonoid.closure_induction with
  | mem x hx =>
      intro u hu
      rcases hx with ⟨i, rfl⟩
      exact ⟨ggTWNRefl p (ggTWNH p N i.val, ggTWNA p N i.val) u, hstable u hu i, by
        rw [l05nE4_toZ_refl (ggTWNH_length p N i.val) (ggTWNA_length p N i.val) (hlen u hu),
          ggTWNH_toZ i, ggTWNA_toZ i]⟩
  | one =>
      intro u hu
      exact ⟨u, hu, rfl⟩
  | mul x y hx hy ihx ihy =>
      intro u hu
      obtain ⟨u1, hu1, hu1eq⟩ := ihy u hu
      obtain ⟨u2, hu2, hu2eq⟩ := ihx u1 hu1
      exact ⟨u2, hu2, by rw [hu2eq, hu1eq]; rfl⟩

theorem ggTWNRoots_orbit {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (hR : ggTWNRootsOK p N (ggTWNRoots p N) = true) :
    ∀ v ∈ ggTWRoots (ggTWFrameGens p N) (Set.range (ggTWh p N)),
      ∃ u ∈ ggTWNRoots p N, ggTWNToZ p N u = v := by
  intro v hv
  rcases hv with ⟨W, hW, c, hc, rfl⟩
  rcases hc with ⟨i, rfl⟩
  obtain ⟨u, hu, hueq⟩ := l05nE4_orbit_aux (l05nE4_contains_of_OK hR) (l05nE4_stable_of_OK hR)
    (fun u hu => l05nE4_roots_length hu) W hW (ggTWNH p N i.val) (l05nE4_contains_of_OK hR i)
  exact ⟨u, hu, by rw [hueq, ggTWNH_toZ i]⟩

private lemma l05nE4_apply_mem_aux {p N : ℕ} [Fact p.Prime] {w : List ℕ}
    (hw : ∀ g ∈ w, g + 1 < N) (v : List ℕ) (hv : v.length = N - 1) :
    ∃ W ∈ Submonoid.closure (ggTWFrameGens p N),
      ggTWNToZ p N (ggTWNApply p N w v) = W (ggTWNToZ p N v) := by
  induction w generalizing v with
  | nil => exact ⟨1, Submonoid.one_mem _, by simp [ggTWNApply]⟩
  | cons g w ih =>
      have hgN : g + 1 < N := hw g (List.mem_cons_self ..)
      let gi : Fin (N - 1) := ⟨g, by omega⟩
      have hwtail : ∀ g' ∈ w, g' + 1 < N := fun g' hg' => hw g' (List.mem_cons_of_mem g hg')
      obtain ⟨W, hWmem, hWv⟩ := ih hwtail v hv
      refine ⟨ggTWRefl (ggTWh p N gi) (ggTWα p N gi) * W,
        Submonoid.mul_mem _ (Submonoid.subset_closure ⟨gi, rfl⟩) hWmem, ?_⟩
      have htail : (ggTWNApply p N w v).length = N - 1 := l05nE4_apply_length w v hv hwtail
      have hHg : ggTWNToZ p N (ggTWNH p N g) = ggTWh p N gi := ggTWNH_toZ gi
      have hAg : ggTWNToZ p N (ggTWNA p N g) = ggTWα p N gi := ggTWNA_toZ gi
      have hstep : ggTWNToZ p N (ggTWNApply p N (g :: w) v) =
          ggTWRefl (ggTWNToZ p N (ggTWNH p N g)) (ggTWNToZ p N (ggTWNA p N g))
            (ggTWNToZ p N (ggTWNApply p N w v)) := by
        change ggTWNToZ p N
          (ggTWNRefl p (ggTWNH p N g, ggTWNA p N g) (ggTWNApply p N w v)) = _
        exact l05nE4_toZ_refl (ggTWNH_length p N g) (ggTWNA_length p N g) htail
      rw [hstep, hHg, hAg, hWv]
      rfl

theorem ggTWNApply_mem {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) {w : List ℕ}
    (hw : ∀ g ∈ w, g + 1 < N) {i : ℕ} (hi : i + 1 < N) :
    ggTWNToZ p N (ggTWNApply p N w (ggTWNH p N i)) ∈
      ggTWRoots (ggTWFrameGens p N) (Set.range (ggTWh p N)) := by
  obtain ⟨W, hWmem, hWv⟩ := l05nE4_apply_mem_aux (p := p) (N := N) hw (ggTWNH p N i)
    (ggTWNH_length p N i)
  have hi' : i < N - 1 := by omega
  refine ⟨W, hWmem, ggTWh p N ⟨i, hi'⟩, Set.mem_range_self _, ?_⟩
  rw [hWv, ggTWNH_toZ (p := p) (N := N) ⟨i, hi'⟩]

theorem ggTWNLine_sound {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid p N q)
    (hR : ggTWNRootsOK p N (ggTWNRoots p N) = true) (w : GGTWNLine)
    (hv : ggTWNKillValid N (N - 1 + news.length) (GGTWNKill.line w) = true)
    (ht : ggTWNKillTest p N news (ggTWNRoots p N) (GGTWNKill.line w) = true) :
    ∃ s ∈ Submonoid.closure (ggTWGens p N (ggTWNNews p N news)), GGTWIsRefl s ∧
      GGTWMovesLine (ggTWRoots (ggTWFrameGens p N) (Set.range (ggTWh p N))) (ggTWx p N) s := by
  classical
  let R := ggTWNRoots p N
  let s : GGDepANPair := ggTWNWord p N news (ggTWNGen p N news w.g) w.w
  let sv : List ℕ := ggTWNRefl p s (ggTWNApply p N w.wv (ggTWNH p N w.i))
  have hv' := hv
  simp only [ggTWNKillValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv'
  obtain ⟨⟨⟨hvg, hvw⟩, hvi⟩, hvwv⟩ := hv'
  have ht' : ((ggDepANDot p s.2 (ggTWNX N) == 0) && R.all
      (fun u => !ggDepANPar p (u.take (N - 2)) (sv.take (N - 2)))) = true := ht
  rw [Bool.and_eq_true] at ht'
  have hdot : ggDepANDot p s.2 (ggTWNX N) = 0 := beq_iff_eq.mp ht'.1
  have hall : ∀ u ∈ R, (!ggDepANPar p (u.take (N - 2)) (sv.take (N - 2))) = true :=
    List.all_eq_true.mp ht'.2
  have hgenv : GGTWNValid p N (ggTWNGen p N news w.g) :=
    ggTWNGen_valid (p := p) (N := N) (by omega) hN hnews hvg
  have hgenm : ggTWNRflOf p N (ggTWNGen p N news w.g) ∈
      Submonoid.closure (ggTWGens p N (ggTWNNews p N news)) :=
    ggTWNGen_mem (p := p) (N := N) (by omega) hN hvg
  have hword := ggTWNWord_valid_mem (p := p) (N := N) (by omega) hN hnews hgenv hgenm hvw
  refine ⟨ggTWNRflOf p N s, hword.2, ?_, ?_⟩
  · refine ⟨ggTWNToZ p N s.1, ggTWNToZ p N s.2, ?_, rfl⟩
    have hd := hword.1.2.2
    show ggDepAdot (ggDepANToZ p (N - 1) s.2) (ggDepANToZ p (N - 1) s.1) = 2
    rw [← ggDepANDot_cast (p := p) s.2 s.1 hword.1.2.1 hword.1.1, hd, ZMod.natCast_mod]
    rfl
  · constructor
    · show ggTWNRflOf p N s (ggTWx p N) = ggTWx p N
      have hx0 : ggDepAdot (ggTWNToZ p N s.2) (ggTWx p N) = 0 := by
        have h := ggDepANDot_cast (p := p) s.2 (ggTWNX N) hword.1.2.1 (ggTWNX_length N)
        rw [hdot] at h
        rw [← ggTWNX_toZ]
        simpa using h.symm
      rw [l05nE4_refl_apply, hx0, zero_smul, sub_zero]
    · refine ⟨ggTWNToZ p N (ggTWNApply p N w.wv (ggTWNH p N w.i)),
        ggTWNApply_mem (p := p) (N := N) hp hvwv hvi, ?_⟩
      intro w' hw' c d hc heq
      obtain ⟨u', hu'R, hu'eq⟩ := ggTWNRoots_orbit (p := p) (N := N) hp hR w' hw'
      have hu'len : u'.length = N - 1 := l05nE4_roots_length hu'R
      have hfirst : (ggDepANFirstNZ p (u'.take (N - 2))).isSome = true := by
        have h := hR
        simp only [ggTWNRootsOK, Bool.and_eq_true] at h
        exact (List.all_eq_true.mp h.1.2) u' hu'R
      obtain ⟨i0, hi0⟩ := Option.isSome_iff_exists.mp hfirst
      have hlenS1 : s.1.length = N - 1 := hword.1.1
      have hlenS2 : s.2.length = N - 1 := hword.1.2.1
      have hlenApply : (ggTWNApply p N w.wv (ggTWNH p N w.i)).length = N - 1 :=
        l05nE4_apply_length w.wv (ggTWNH p N w.i) (ggTWNH_length p N w.i) hvwv
      have htoZ_sv : ggTWNToZ p N sv =
          ggTWRefl (ggTWNToZ p N s.1) (ggTWNToZ p N s.2)
            (ggTWNToZ p N (ggTWNApply p N w.wv (ggTWNH p N w.i))) :=
        l05nE4_toZ_refl hlenS1 hlenS2 hlenApply
      have heq2 : ggTWNToZ p N sv = c • ggTWNToZ p N u' + d • ggTWNToZ p N (ggTWNX N) := by
        rw [htoZ_sv]
        show ggTWNRflOf p N s (ggTWNToZ p N (ggTWNApply p N w.wv (ggTWNH p N w.i))) =
          c • ggTWNToZ p N u' + d • ggTWNToZ p N (ggTWNX N)
        rw [heq, ← hu'eq, ggTWNX_toZ]
      have hprop : ∀ j : ℕ, j < (u'.take (N - 2)).length →
          ((sv.take (N - 2)).getD j 0 : ZMod p) =
            c * ((u'.take (N - 2)).getD j 0 : ZMod p) := by
        intro j hj
        have hj2 : j < N - 2 := by
          rw [List.length_take, hu'len, Nat.min_eq_left (by omega)] at hj
          exact hj
        let jf : Fin (N - 1) := ⟨j, by omega⟩
        have hcoord : (sv.getD j 0 : ZMod p) =
            c * (u'.getD j 0 : ZMod p) + d * (ggTWx p N jf) := by
          have h := congrFun heq2 jf
          rw [ggTWNX_toZ] at h
          change (sv.getD j 0 : ZMod p) =
            c * (u'.getD j 0 : ZMod p) + d * (ggTWx p N jf) at h
          exact h
        rw [l05nE4_x_apply_zero jf (by simpa using hj2), mul_zero, add_zero] at hcoord
        rw [l05nE4_getD_take sv (N - 2) 0 hj2, l05nE4_getD_take u' (N - 2) 0 hj2]
        exact hcoord
      have hpar_true : ggDepANPar p (u'.take (N - 2)) (sv.take (N - 2)) = true :=
        l05nE4_par_of_prop hc hprop hi0
      have hhall := hall u' hu'R
      rw [hpar_true] at hhall
      exact Bool.false_ne_true hhall

theorem ggTWNKillTest_sound {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWNValid p N q)
    (hR : ggTWNRootsOK p N (ggTWNRoots p N) = true) (w : GGTWNKill)
    (hv : ggTWNKillValid N (N - 1 + news.length) w = true)
    (ht : ggTWNKillTest p N news (ggTWNRoots p N) w = true) (pos : GGTWPos)
    (y : GGTWE p N) :
    GGTWKill .frame p N pos (ggTWNNews p N news) y := by
  cases w with
  | tv wt =>
      exact Or.inl (ggTWNTv_sound (p := p) (N := N) hp hN hnews (ggTWNRoots p N) wt hv ht)
  | line wl =>
      exact Or.inr (ggTWNLine_sound (p := p) (N := N) hp hN hnews hR wl hv ht)


end CFSG.StandardType
