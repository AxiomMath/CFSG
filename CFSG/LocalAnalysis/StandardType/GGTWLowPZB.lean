module

public import CFSG.LocalAnalysis.StandardType.GGTWLowEnum
public import CFSG.LocalAnalysis.StandardType.GGTWLowPZA
public import CFSG.LocalAnalysis.StandardType.GGTWNatWord

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nLB_toZ_add {p N : ℕ} [Fact p.Prime] {a b : List ℕ}
    (ha : a.length = N - 1) (hb : b.length = N - 1) :
    ggTWNToZ p N (ggTWNAdd p a b) = ggTWNToZ p N a + ggTWNToZ p N b := by
  funext j
  have hj : j.val < N - 1 := j.isLt
  have hja : j.val < a.length := by rw [ha]; exact hj
  have hjb : j.val < b.length := by rw [hb]; exact hj
  have hjl : j.val < (a.zipWith (fun x y => (x + y) % p) b).length := by
    rw [List.length_zipWith, ha, hb, min_self]; exact hj
  simp only [ggTWNToZ, ggDepANToZ, ggTWNAdd, Pi.add_apply]
  rw [List.getD_eq_getElem (l := a.zipWith (fun x y => (x + y) % p) b) (d := 0) (n := j.val) hjl,
    List.getD_eq_getElem (l := a) (d := 0) (n := j.val) hja,
    List.getD_eq_getElem (l := b) (d := 0) (n := j.val) hjb,
    List.getElem_zipWith, ZMod.natCast_mod, Nat.cast_add]
private lemma l05nLB_add_length {p N : ℕ} {a b : List ℕ} (ha : a.length = N) (hb : b.length = N) :
    (ggTWNAdd p a b).length = N := by
  simp only [ggTWNAdd, List.length_zipWith, ha, hb, min_self]
private lemma l05nLB_form_apply {p N : ℕ} (f v : GGDepAE p N) :
    ggDepAform f v = ggDepAdot f v := by
  simp [ggDepAform, ggDepAdot]
private lemma l05nLB_dot_sub {p N : ℕ} (a v w : GGDepAE p N) :
    ggDepAdot a (v - w) = ggDepAdot a v - ggDepAdot a w := by
  rw [← l05nLB_form_apply a (v - w), map_sub, l05nLB_form_apply a v, l05nLB_form_apply a w]
private lemma l05nLB_dot_smul {p N : ℕ} (a : GGDepAE p N) (k : ZMod p) (v : GGDepAE p N) :
    ggDepAdot a (k • v) = k * ggDepAdot a v := by
  rw [← l05nLB_form_apply a (k • v), map_smul, l05nLB_form_apply a v]
  simp
private lemma l05nLB_depA_refl_mul_self {p N : ℕ} (c f : GGDepAE p N) (h : ggDepAdot f c = 2) :
    ggDepARefl c f * ggDepARefl c f = 1 := by
  apply LinearMap.ext; intro v
  ext j
  have hd : ggDepAdot f (v - ggDepAdot f v • c) =
      ggDepAdot f v - ggDepAdot f v * ggDepAdot f c := by
    rw [l05nLB_dot_sub, l05nLB_dot_smul]
  have hone : (1 : Module.End (ZMod p) (GGDepAE p N)) v = v := rfl
  simp only [Module.End.mul_apply, l05nNC_refl_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hd, h, hone]
  ring
private lemma l05nLB_refl_mul_self {p N : ℕ} (c f : GGTWE p N) (h : ggTWdot f c = 2) :
    ggTWRefl c f * ggTWRefl c f = 1 :=
  l05nLB_depA_refl_mul_self (p := p) (N := N - 1) c f h
private lemma l05nLB_dot_of_valid {p N : ℕ} [Fact p.Prime] {q : GGDepANPair}
    (h : GGTWNValid p N q) :
    ggTWdot (ggTWNToZ p N q.2) (ggTWNToZ p N q.1) = 2 := by
  have hcast := ggDepANDot_cast (p := p) (N := N - 1) q.2 q.1 h.2.1 h.1
  rw [h.2.2, ZMod.natCast_mod] at hcast
  exact hcast.symm
private lemma l05nLB_valid_of_dot {p N : ℕ} [Fact p.Prime] {q : GGDepANPair}
    (hq1 : q.1.length = N - 1) (hq2 : q.2.length = N - 1)
    (h : ggTWdot (ggTWNToZ p N q.2) (ggTWNToZ p N q.1) = 2) :
    GGTWNValid p N q := by
  refine ⟨hq1, hq2, ?_⟩
  have hcast := ggDepANDot_cast (p := p) (N := N - 1) q.2 q.1 hq2 hq1
  have hdot : ggDepAdot (ggDepANToZ p (N - 1) q.2) (ggDepANToZ p (N - 1) q.1) = 2 := h
  rw [hdot] at hcast
  have h2 : ((ggDepANDot p q.2 q.1 : ℕ) : ZMod p) = ((2 % p : ℕ) : ZMod p) := by
    rw [ZMod.natCast_mod]; exact hcast
  rw [ZMod.natCast_eq_natCast_iff'] at h2
  simpa [ggDepANDot, Nat.mod_mod] using h2
private lemma l05nLB_isRefl_of_valid {p N : ℕ} [Fact p.Prime] {q : GGDepANPair}
    (hq : GGTWNValid p N q) : GGTWIsRefl (ggTWNRflOf p N q) :=
  ⟨ggTWNToZ p N q.1, ggTWNToZ p N q.2, l05nLB_dot_of_valid hq, rfl⟩
private lemma l05nLB_refl_mul_self_of_isRefl {p N : ℕ} (r : Module.End (ZMod p) (GGTWE p N))
    (hr : GGTWIsRefl r) : r * r = 1 := by
  rcases hr with ⟨c, f, h, rfl⟩
  exact l05nLB_refl_mul_self c f h
private lemma l05nLB_rfl_conj {p N : ℕ} [Fact p.Prime] {q g : GGDepANPair}
    (hq : GGTWNValid p N q) (hg : GGTWNValid p N g) :
    ggTWNRflOf p N (ggDepANConj p q g) =
      ggTWNRflOf p N g * ggTWNRflOf p N q * ggTWNRflOf p N g := by
  have hc := l05nNC_toZ_conj (p := p) (N := N - 1) (q := q) (g := g) hq.1 hq.2.1 hg.1 hg.2.1
  show ggDepARefl (ggDepANToZ p (N - 1) (ggDepANConj p q g).1)
      (ggDepANToZ p (N - 1) (ggDepANConj p q g).2) = _
  rw [hc.1, hc.2]
  exact (l05nNC_refl_conj (ggDepANToZ p (N - 1) q.1) (ggDepANToZ p (N - 1) q.2)
    (ggDepANToZ p (N - 1) g.1) (ggDepANToZ p (N - 1) g.2) (l05nLB_dot_of_valid hg)).symm
private lemma l05nLB_conj_valid {p N : ℕ} [Fact p.Prime] {q g : GGDepANPair}
    (hq : GGTWNValid p N q) (hg : GGTWNValid p N g) :
    GGTWNValid p N (ggDepANConj p q g) := by
  have hlen := l05nNC_conj_length (p := p) (N := N - 1) hq.1 hq.2.1 hg.1 hg.2.1
  have hc := l05nNC_toZ_conj (p := p) (N := N - 1) (q := q) (g := g) hq.1 hq.2.1 hg.1 hg.2.1
  apply l05nLB_valid_of_dot hlen.1 hlen.2
  change ggDepAdot (ggDepANToZ p (N - 1) (ggDepANConj p q g).2)
    (ggDepANToZ p (N - 1) (ggDepANConj p q g).1) = 2
  rw [hc.1, hc.2]
  exact l05nNC_conj_dot (ggDepANToZ p (N - 1) q.1) (ggDepANToZ p (N - 1) q.2)
    (ggDepANToZ p (N - 1) g.1) (ggDepANToZ p (N - 1) g.2) (l05nLB_dot_of_valid hq)
    (l05nLB_dot_of_valid hg)
private lemma l05nLB_fix_refl {p N : ℕ} [Fact p.Prime] {q : GGDepANPair} {z : List ℕ}
    (hq : GGTWNValid p N q)
    (hz : z.length = N - 1) (h : ggDepANDot p q.2 z % p = 0) :
    ggTWNRflOf p N q (ggTWNToZ p N z) = ggTWNToZ p N z := by
  have hdot : ggDepAdot (ggDepANToZ p (N - 1) q.2) (ggDepANToZ p (N - 1) z) = 0 := by
    have hcast := ggDepANDot_cast (p := p) (N := N - 1) q.2 z hq.2.1 hz
    rw [← hcast]
    exact (ZMod.natCast_eq_zero_iff (ggDepANDot p q.2 z) p).mpr (Nat.dvd_of_mod_eq_zero h)
  show ggDepARefl (ggDepANToZ p (N - 1) q.1) (ggDepANToZ p (N - 1) q.2)
      (ggDepANToZ p (N - 1) z) = ggDepANToZ p (N - 1) z
  rw [l05nNC_refl_apply, hdot, zero_smul, sub_zero]

private lemma l05nLB_conj_fold {p N : ℕ} [Fact p.Prime]
    (C : Submonoid (Module.End (ZMod p) (GGTWE p N))) (q : GGDepANPair) (hq : GGTWNValid p N q) :
    ∀ fixes : List GGDepANPair,
      (∀ g ∈ fixes, GGTWNValid p N g) →
      (∀ g ∈ fixes, ggTWNRflOf p N g ∈ C) →
      ∃ G ∈ C, ∃ G' ∈ C, G * G' = 1 ∧
        GGTWNValid p N (fixes.foldr (fun g acc => ggDepANConj p acc g) q) ∧
        ggTWNRflOf p N (fixes.foldr (fun g acc => ggDepANConj p acc g) q) =
          G * ggTWNRflOf p N q * G' := by
  intro fixes
  induction fixes with
  | nil =>
      intro _ _
      exact ⟨1, C.one_mem, 1, C.one_mem, by simp, by simpa [ggTWNRflOf] using hq, by simp⟩
  | cons g gs ih =>
      intro hfixv hfixmem
      have hgv : GGTWNValid p N g := hfixv g (by simp)
      have hgsv : ∀ g' ∈ gs, GGTWNValid p N g' := fun g' hg' => hfixv g' (by simp [hg'])
      have hgmem : ggTWNRflOf p N g ∈ C := hfixmem g (by simp)
      have hgsmem : ∀ g' ∈ gs, ggTWNRflOf p N g' ∈ C := fun g' hg' => hfixmem g' (by simp [hg'])
      obtain ⟨G, hG, G', hG', hGG', hvrest, hEq⟩ := ih hgsv hgsmem
      refine ⟨ggTWNRflOf p N g * G, Submonoid.mul_mem _ hgmem hG,
        G' * ggTWNRflOf p N g, Submonoid.mul_mem _ hG' hgmem, ?_, ?_, ?_⟩
      · calc (ggTWNRflOf p N g * G) * (G' * ggTWNRflOf p N g)
            = ggTWNRflOf p N g * (G * G') * ggTWNRflOf p N g := by
              simp only [mul_assoc]
          _ = ggTWNRflOf p N g * 1 * ggTWNRflOf p N g := by rw [hGG']
          _ = ggTWNRflOf p N g * ggTWNRflOf p N g := by rw [mul_one]
          _ = 1 := l05nLB_refl_mul_self_of_isRefl _ (l05nLB_isRefl_of_valid hgv)
      · rw [List.foldr_cons]
        exact l05nLB_conj_valid hvrest hgv
      · rw [List.foldr_cons, l05nLB_rfl_conj hvrest hgv, hEq]
        simp only [mul_assoc]

private lemma l05nLB_word_cons (p N : ℕ) (news : List GGDepANPair) (q : GGDepANPair) (g : ℕ)
    (w : List ℕ) :
    ggTWNWord p N news q (g :: w) =
      ggDepANConj p (ggTWNWord p N news q w) (ggTWNGen p N news g) := by
  simp [ggTWNWord]
private lemma l05nLB_word_J {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWNValid p N q)
    (S : Submonoid (Module.End (ZMod p) (GGTWE p N)))
    (w : List ℕ) (hw : ∀ g ∈ w, g < N - 1 + news.length)
    (hmem : ∀ g ∈ w, ggTWNRflOf p N (ggTWNGen p N news g) ∈ S)
    (q : GGDepANPair) (hq : GGTWNValid p N q) (hqm : ggTWNRflOf p N q ∈ S) :
    GGTWNValid p N (ggTWNWord p N news q w) ∧ ggTWNRflOf p N (ggTWNWord p N news q w) ∈ S := by
  induction w generalizing q with
  | nil => simpa [ggTWNWord] using ⟨hq, hqm⟩
  | cons g w ih =>
      rw [l05nLB_word_cons]
      have hg : g < N - 1 + news.length := hw g (by simp)
      have hw' : ∀ g' ∈ w, g' < N - 1 + news.length := fun g' hg' => hw g' (by simp [hg'])
      have hmem' : ∀ g' ∈ w, ggTWNRflOf p N (ggTWNGen p N news g') ∈ S :=
        fun g' hg' => hmem g' (by simp [hg'])
      obtain ⟨ihV, ihM⟩ := ih hw' hmem' q hq hqm
      have hG : GGTWNValid p N (ggTWNGen p N news g) := ggTWNGen_valid hp hN hnews hg
      refine ⟨l05nLB_conj_valid ihV hG, ?_⟩
      rw [l05nLB_rfl_conj ihV hG]
      exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hmem g (by simp)) ihM) (hmem g (by simp))

private lemma l05nLB_isUnit_closure {M : Type*} [Monoid M] {S : Set M}
    (hS : ∀ s ∈ S, s * s = 1) : ∀ g ∈ Submonoid.closure S, IsUnit g := by
  intro g hg
  induction hg using Submonoid.closure_induction with
  | mem x hx => exact ⟨⟨x, x, hS x hx, hS x hx⟩, rfl⟩
  | one => exact isUnit_one
  | mul x y _ _ ihx ihy => exact ihx.mul ihy
private lemma l05nLB_mul_eq_one_comm {M : Type*} [Monoid M] {g g' : M} (hg : IsUnit g)
    (h : g * g' = 1) : g' * g = 1 := by
  obtain ⟨u, rfl⟩ := hg
  have hg' : g' = ↑(u⁻¹) := by
    rw [← one_mul g', ← Units.inv_mul u, mul_assoc, h, mul_one]
  rw [hg', Units.inv_mul]
private lemma l05nLB_orbit_involution {p N : ℕ} (pos : GGTWPos)
    (gens : Set (Module.End (ZMod p) (GGTWE p N))) (z : GGTWE p N)
    (hfix : ∀ s ∈ ggTWPZFixRefl p N gens z, s * s = 1) :
    ∀ t ∈ ggTWPZOrbit p N pos gens z, t * t = 1 := by
  intro t ht
  rcases ht with ⟨r, hrJ, g, hg, g', hg', hgg', rfl⟩
  have hrr : r * r = 1 := l05nLB_refl_mul_self_of_isRefl r hrJ.2
  have hgunit : IsUnit g := l05nLB_isUnit_closure hfix g hg
  have hg'g : g' * g = 1 := l05nLB_mul_eq_one_comm hgunit hgg'
  calc (g * r * g') * (g * r * g') = g * (r * (g' * g) * r) * g' := by
        simp only [mul_assoc]
    _ = g * (r * 1 * r) * g' := by rw [hg'g]
    _ = g * (r * r) * g' := by rw [mul_one]
    _ = g * 1 * g' := by rw [hrr]
    _ = 1 := by rw [mul_one, hgg']

private lemma l05nLB_gen_lt_of_inJ {N : ℕ} {pos : GGTWPos} {g : ℕ} (h : ggTWInJ N pos g) :
    g + 1 < N := by
  cases pos with
  | ends => simp only [ggTWInJ] at h; omega
  | adj => simp only [ggTWInJ] at h; omega


theorem ggTWLPZTest_sound {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N) (pos : GGTWPos)
    {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWNValid p N q) (y : List ℕ)
    (hy : y.length = N - 1) (w : GGTWLPZ)
    (h : ggTWLPZTest p N (ggTWPosNat pos) news y w = true) :
    (w.c0 : ZMod p) ≠ 0 ∧
      GGTWPZBad p N pos (ggTWGens p N (ggTWNNews p N news))
        (ggTWx p N + (w.c0 : ZMod p) • ggTWNToZ p N y) := by
  simp only [ggTWLPZTest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  set fixP : List GGDepANPair :=
    w.fixs.map (fun e => ggTWNWord p N news (ggTWNGen p N news e.1) e.2) with hfixP
  set orbP : List GGDepANPair := w.orbs.map (fun e =>
      e.2.2.foldr (fun k acc => ggDepANConj p acc (fixP.getD k ([], [])))
        (ggTWNWord p N news (ggTWNGen p N news e.1) e.2.1)) with horbP
  set T : List (List (List ℕ)) :=
    (w.hg.map fun j => orbP.getD j ([], [])).map (ggTWLMatOfPair p (N - 1)) with hT
  set par : List (Nat × Nat) := ggTWLBfsTree p (N - 1) T 1000 with hpar
  set Ms : List (List (List ℕ)) := ggTWLReplay p (N - 1) T par with hMs
  set A : Set (Module.End (ZMod p) (GGTWE p N)) := ggTWGens p N (ggTWNNews p N news) with hA
  set zvec : GGTWE p N := ggTWx p N + (w.c0 : ZMod p) • ggTWNToZ p N y with hzvec
  set M : Submonoid (Module.End (ZMod p) (GGTWE p N)) :=
    Submonoid.closure (ggTWPZOrbit p N pos A zvec) with hM
  set Sp : Set (Module.End (ZMod p) (GGTWE p N)) :=
    {g | ∃ t ∈ T, g = ggTWLMatLin p (N - 1) t} with hSp
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hc0, hc0p⟩, hfixs⟩, horbs⟩, hhg⟩, hfixdot⟩, henum⟩, harith⟩
  have hztest : ggTWNToZ p N (ggTWNAdd p (ggTWNX N) (ggDepANSmul p w.c0 y)) = zvec := by
    rw [hzvec, l05nLB_toZ_add (ggTWNX_length N) (l05nNC_smul_length (N := N - 1) hy), ggTWNX_toZ,
      show ggTWNToZ p N (ggDepANSmul p w.c0 y) = (w.c0 : ZMod p) • ggTWNToZ p N y from
        l05nNC_toZ_smul (N := N - 1) (k := w.c0) hy]
  refine ⟨?_, ?_⟩
  · intro hz
    have hdvd : p ∣ w.c0 := (ZMod.natCast_eq_zero_iff w.c0 p).mp hz
    have hle : p ≤ w.c0 := Nat.le_of_dvd hc0 hdvd
    omega
  ·
    haveI : Fintype (Module.End (ZMod p) (GGTWE p N)) :=
      Fintype.ofInjective
        (fun f : Module.End (ZMod p) (GGTWE p N) => (f : GGTWE p N → GGTWE p N))
        (fun f g h => LinearMap.ext (fun x => congrFun h x))
    have hfix_all : ∀ s ∈ fixP, GGTWNValid p N s ∧
        ggTWNRflOf p N s ∈ ggTWPZFixRefl p N A zvec := by
      intro s hs
      have hdotmod : ggDepANDot p s.2 (ggTWNAdd p (ggTWNX N) (ggDepANSmul p w.c0 y)) % p = 0 :=
        beq_iff_eq.mp (hfixdot s hs)
      rw [hfixP] at hs
      rcases List.mem_map.mp hs with ⟨e, he, rfl⟩
      obtain ⟨he1, he2⟩ := hfixs e he
      have hvg : GGTWNValid p N (ggTWNGen p N news e.1) := ggTWNGen_valid hp hN hnews he1
      have hmg : ggTWNRflOf p N (ggTWNGen p N news e.1) ∈ Submonoid.closure A :=
        ggTWNGen_mem hp hN he1
      obtain ⟨hv, hm⟩ := ggTWNWord_valid_mem hp hN hnews hvg hmg he2
      have hzl : (ggTWNAdd p (ggTWNX N) (ggDepANSmul p w.c0 y)).length = N - 1 :=
        l05nLB_add_length (ggTWNX_length N) (l05nNC_smul_length (N := N - 1) hy)
      have hfixz : ggTWNRflOf p N (ggTWNWord p N news (ggTWNGen p N news e.1) e.2) zvec = zvec := by
        rw [← hztest]
        exact l05nLB_fix_refl hv hzl hdotmod
      exact ⟨hv, hm, l05nLB_isRefl_of_valid hv, hfixz⟩
    have horbit : ∀ q ∈ orbP, GGTWNValid p N q ∧
        ggTWNRflOf p N q ∈ ggTWPZOrbit p N pos A zvec := by
      intro q hq
      rw [horbP] at hq
      rcases List.mem_map.mp hq with ⟨e, he, rfl⟩
      obtain ⟨⟨heJ, heJw⟩, hefix⟩ := horbs e he
      have he1lt : e.1 + 1 < N := l05nLB_gen_lt_of_inJ ((ggTWNInJ_iff pos e.1).mp heJ)
      have he1lt' : e.1 < N - 1 := by omega
      let qin : GGDepANPair := ggTWNWord p N news (ggTWNGen p N news e.1) e.2.1
      have hJmem : ggTWNRflOf p N (ggTWNGen p N news e.1) ∈
          Submonoid.closure ((fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} =>
            ggTWRefl (ggTWh p N i.1) (ggTWα p N i.1)) '' Set.univ) := by
        have hgen : ggTWNGen p N news e.1 = (ggTWNH p N e.1, ggTWNA p N e.1) := by
          rw [ggTWNGen, if_pos he1lt]
        rw [hgen]
        refine Submonoid.subset_closure ⟨⟨⟨e.1, he1lt'⟩, (ggTWNInJ_iff pos e.1).mp heJ⟩,
          Set.mem_univ _, ?_⟩
        change ggTWRefl (ggTWh p N ⟨e.1, he1lt'⟩) (ggTWα p N ⟨e.1, he1lt'⟩) =
          ggTWRefl (ggTWNToZ p N (ggTWNH p N e.1)) (ggTWNToZ p N (ggTWNA p N e.1))
        rw [show ggTWNToZ p N (ggTWNH p N e.1) = ggTWh p N ⟨e.1, he1lt'⟩ from
              ggTWNH_toZ ⟨e.1, he1lt'⟩,
            show ggTWNToZ p N (ggTWNA p N e.1) = ggTWα p N ⟨e.1, he1lt'⟩ from
              ggTWNA_toZ ⟨e.1, he1lt'⟩]
      have hwlt : ∀ g ∈ e.2.1, g < N - 1 + news.length := by
        intro g hg
        have hgJ : ggTWInJ N pos g := (ggTWNInJ_iff pos g).mp (heJw g hg)
        have := l05nLB_gen_lt_of_inJ hgJ
        omega
      have hmemJ : ∀ g ∈ e.2.1, ggTWNRflOf p N (ggTWNGen p N news g) ∈
          Submonoid.closure ((fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} =>
            ggTWRefl (ggTWh p N i.1) (ggTWα p N i.1)) '' Set.univ) := by
        intro g hg
        have hgJ : ggTWInJ N pos g := (ggTWNInJ_iff pos g).mp (heJw g hg)
        have hglt : g + 1 < N := l05nLB_gen_lt_of_inJ hgJ
        have hglt' : g < N - 1 := by omega
        have hgen : ggTWNGen p N news g = (ggTWNH p N g, ggTWNA p N g) := by
          rw [ggTWNGen, if_pos hglt]
        rw [hgen]
        refine Submonoid.subset_closure ⟨⟨⟨g, hglt'⟩, hgJ⟩, Set.mem_univ _, ?_⟩
        change ggTWRefl (ggTWh p N ⟨g, hglt'⟩) (ggTWα p N ⟨g, hglt'⟩) =
          ggTWRefl (ggTWNToZ p N (ggTWNH p N g)) (ggTWNToZ p N (ggTWNA p N g))
        rw [show ggTWNToZ p N (ggTWNH p N g) = ggTWh p N ⟨g, hglt'⟩ from ggTWNH_toZ ⟨g, hglt'⟩,
          show ggTWNToZ p N (ggTWNA p N g) = ggTWα p N ⟨g, hglt'⟩ from ggTWNA_toZ ⟨g, hglt'⟩]
      obtain ⟨hqinV, hqinM⟩ := l05nLB_word_J hp hN hnews
        (Submonoid.closure ((fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} =>
          ggTWRefl (ggTWh p N i.1) (ggTWα p N i.1)) '' Set.univ))
        e.2.1 hwlt hmemJ (ggTWNGen p N news e.1) (ggTWNGen_valid hp hN hnews (by omega)) hJmem
      have hqinJ : ggTWNRflOf p N qin ∈ ggTWPZJRefl p N pos := by
        rw [ggTWPZJRefl]
        exact ⟨hqinM, l05nLB_isRefl_of_valid hqinV⟩
      set fixes : List GGDepANPair := e.2.2.map (fun k => fixP.getD k ([], [])) with hfixes
      have hgetmem : ∀ k ∈ e.2.2, fixP.getD k ([], []) ∈ fixP := by
        intro k hk
        have hklt : k < fixP.length := hefix k hk
        rw [List.getD_eq_getElem (l := fixP) (d := ([], [])) (n := k) hklt]
        exact List.getElem_mem hklt
      have hfixe_v : ∀ g ∈ fixes, GGTWNValid p N g := by
        intro g hg
        rw [hfixes] at hg
        rcases List.mem_map.mp hg with ⟨k, hk, rfl⟩
        exact (hfix_all _ (hgetmem k hk)).1
      have hfixe_m : ∀ g ∈ fixes,
          ggTWNRflOf p N g ∈ Submonoid.closure (ggTWPZFixRefl p N A zvec) := by
        intro g hg
        rw [hfixes] at hg
        rcases List.mem_map.mp hg with ⟨k, hk, rfl⟩
        exact Submonoid.subset_closure (hfix_all _ (hgetmem k hk)).2
      obtain ⟨G, hG, G', hG', hGG', hvfold, hfold⟩ :=
        l05nLB_conj_fold (Submonoid.closure (ggTWPZFixRefl p N A zvec)) qin hqinV
          fixes hfixe_v hfixe_m
      have hfoldmap : fixes.foldr (fun g acc => ggDepANConj p acc g) qin =
          e.2.2.foldr (fun k acc => ggDepANConj p acc (fixP.getD k ([], []))) qin :=
        List.foldr_map
      rw [hfoldmap] at hvfold hfold
      exact ⟨hvfold, ⟨ggTWNRflOf p N qin, hqinJ, G, hG, G', hG', hGG', hfold⟩⟩
    have hTWC : ∀ t ∈ T, ∃ q ∈ orbP, t = ggTWLMatOfPair p (N - 1) q := by
      intro t ht
      rw [hT] at ht
      rcases List.mem_map.mp ht with ⟨q, hq, rfl⟩
      rw [horbP] at hq
      rcases List.mem_map.mp hq with ⟨j, hj, rfl⟩
      have hjlt : j < orbP.length := hhg j hj
      refine ⟨orbP.getD j ([], []), ?_, rfl⟩
      rw [List.getD_eq_getElem (l := orbP) (d := ([], [])) (n := j) hjlt]
      exact List.getElem_mem hjlt
    have hT_valid : ∀ t ∈ T, ggTWLMatWF (N - 1) t := by
      intro t ht
      obtain ⟨q, hq, rfl⟩ := hTWC t ht
      exact (ggTWLMatOfPair_lin (horbit q hq).1).1
    have hEnumRes := ggTWLEnum_sound (p := p) (d := N - 1) hT_valid par henum
    have hCardH : Nat.card ↥(Submonoid.closure Sp) = Ms.length := hEnumRes.2.2
    have hS_orbit : ∀ s ∈ ggTWPZOrbit p N pos A zvec, s * s = 1 :=
      l05nLB_orbit_involution pos A zvec
        (fun s hs => l05nLB_refl_mul_self_of_isRefl s hs.2.1)
    have hSp : ∀ s ∈ Sp, s * s = 1 := by
      intro s hs
      rcases hs with ⟨t, ht, rfl⟩
      obtain ⟨q, hq, rfl⟩ := hTWC t ht
      rw [(ggTWLMatOfPair_lin (horbit q hq).1).2]
      exact l05nLB_refl_mul_self_of_isRefl _ (l05nLB_isRefl_of_valid (horbit q hq).1)
    have hsub : Sp ⊆ (M : Set (Module.End (ZMod p) (GGTWE p N))) := by
      intro s hs
      rcases hs with ⟨t, ht, rfl⟩
      obtain ⟨q, hq, rfl⟩ := hTWC t ht
      rw [(ggTWLMatOfPair_lin (horbit q hq).1).2]
      exact Submonoid.subset_closure (horbit q hq).2
    have hKdvd : Ms.length ∣ Nat.card ↥M := by
      rw [← hCardH]
      exact ggTWL_card_dvd (p := p) (N := N) hS_orbit hSp hsub
    intro r n c ht hlo hhi hbad
    rcases hbad with ⟨hdvdn, hcen⟩
    have hKpos : 0 < Ms.length := by
      have ha := harith
      simp only [ggTWLPZArith, Bool.and_eq_true, decide_eq_true_eq] at ha
      exact ha.1
    obtain ⟨hn, hc, hhasCen⟩ :=
      ggTWLPZArith_sound harith ht hlo hhi (dvd_trans hKdvd hdvdn)
    have hMcard : Nat.card ↥M = Ms.length := by
      rw [hn] at hdvdn
      exact Nat.dvd_antisymm hdvdn hKdvd
    have hcentre1 : ggTWCentreCard M = 1 := by
      have hcc := hcen (hMcard.trans hn.symm)
      rw [hc] at hcc
      exact hcc
    rcases List.any_eq_true.mp hhasCen with ⟨a, haMs, haProp⟩
    rw [Bool.and_eq_true] at haProp
    obtain ⟨haNe, haComm⟩ := haProp
    have haWF : ggTWLMatWF (N - 1) a := hEnumRes.1 a haMs
    have honeWF : ggTWLMatWF (N - 1) (ggTWLMatOne (N - 1)) :=
      (ggTWLMatOne_lin (p := p) (d := N - 1)).1
    have hlin_a_ne : ggTWLMatLin p (N - 1) a ≠ 1 := by
      intro heq
      have htrue : ggTWLMatEq p a (ggTWLMatOne (N - 1)) = true :=
        (ggTWLMatEq_iff haWF honeWF).mpr (by rw [heq, (ggTWLMatOne_lin (p := p) (d := N - 1)).2])
      have hfalse : ggTWLMatEq p a (ggTWLMatOne (N - 1)) = false := by simpa using haNe
      rw [htrue] at hfalse
      exact Bool.false_ne_true hfalse.symm
    have hcommT : ∀ t ∈ T, ggTWLMatLin p (N - 1) a * ggTWLMatLin p (N - 1) t =
        ggTWLMatLin p (N - 1) t * ggTWLMatLin p (N - 1) a := by
      intro t ht
      have hcomm := List.all_eq_true.mp haComm t ht
      have htWF : ggTWLMatWF (N - 1) t := hT_valid t ht
      have h1 := (ggTWLMatMul_lin (p := p) (d := N - 1) haWF htWF).2
      have h2 := (ggTWLMatMul_lin (p := p) (d := N - 1) htWF haWF).2
      rw [← h1, ← h2]
      exact (ggTWLMatEq_iff (ggTWLMatMul_lin haWF htWF).1
        (ggTWLMatMul_lin htWF haWF).1).mp hcomm
    have hHM : Submonoid.closure Sp ≤ M := Submonoid.closure_le.mpr hsub
    have hcard_eq : Nat.card ↥(Submonoid.closure Sp) = Nat.card ↥M := by rw [hCardH, hMcard]
    have hHMeq : Submonoid.closure Sp = M := by
      have hset : (↑(Submonoid.closure Sp) : Set (Module.End (ZMod p) (GGTWE p N))) = ↑M :=
        Set.Finite.eq_of_subset_of_card_le
          (Set.finite_univ.subset (Set.subset_univ (M : Set (Module.End (ZMod p) (GGTWE p N)))))
          (fun x hx => hHM hx) (le_of_eq hcard_eq.symm)
      exact SetLike.ext (Set.ext_iff.mp hset)
    have hlin_a_H : ggTWLMatLin p (N - 1) a ∈ Submonoid.closure Sp := by
      have hmem : ggTWLMatLin p (N - 1) a ∈
          ({g | ∃ b ∈ Ms, g = ggTWLMatLin p (N - 1) b} :
            Set (Module.End (ZMod p) (GGTWE p N))) := ⟨a, haMs, rfl⟩
      exact (Set.ext_iff.mp hEnumRes.2.1 _).mpr hmem
    have hlin_a_M : ggTWLMatLin p (N - 1) a ∈ M := by
      rw [← hHMeq]
      exact hlin_a_H
    have hcentH : ∀ y ∈ Submonoid.closure Sp,
        ggTWLMatLin p (N - 1) a * y = y * ggTWLMatLin p (N - 1) a := by
      intro y hy
      induction hy using Submonoid.closure_induction with
      | mem t ht =>
          rcases ht with ⟨t', ht', rfl⟩
          exact hcommT t' ht' 
      | one => simp
      | mul x y hx hy ihx ihy =>
          calc ggTWLMatLin p (N - 1) a * (x * y)
              = (ggTWLMatLin p (N - 1) a * x) * y := by rw [mul_assoc]
            _ = (x * ggTWLMatLin p (N - 1) a) * y := by rw [ihx]
            _ = x * (ggTWLMatLin p (N - 1) a * y) := by rw [mul_assoc]
            _ = x * (y * ggTWLMatLin p (N - 1) a) := by rw [ihy]
            _ = (x * y) * ggTWLMatLin p (N - 1) a := by rw [mul_assoc]
    have hcentM : ∀ y ∈ M, ggTWLMatLin p (N - 1) a * y = y * ggTWLMatLin p (N - 1) a := by
      intro y hy
      exact hcentH y (by rw [hHMeq]; exact hy)
    let z0 : {g : ↥M // ∀ h : ↥M, g * h = h * g} :=
      ⟨⟨ggTWLMatLin p (N - 1) a, hlin_a_M⟩, fun h => Subtype.ext (hcentM h.1 h.2)⟩
    let z1 : {g : ↥M // ∀ h : ↥M, g * h = h * g} := ⟨1, fun h => by simp⟩
    have hz01 : z0 ≠ z1 := by
      intro heq
      have hval : (z0 : ↥M) = (z1 : ↥M) := congrArg Subtype.val heq
      have hcoe : (z0 : Module.End (ZMod p) (GGTWE p N)) =
          (z1 : Module.End (ZMod p) (GGTWE p N)) := congrArg Subtype.val hval
      apply hlin_a_ne
      simpa [z0, z1] using hcoe
    haveI : Nontrivial {g : ↥M // ∀ h : ↥M, g * h = h * g} := ⟨z0, z1, hz01⟩
    have h2 : 1 < ggTWCentreCard M := by
      rw [ggTWCentreCard]
      exact Finite.one_lt_card
    omega



end CFSG.StandardType

end
