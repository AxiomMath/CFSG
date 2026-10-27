module

public import Certificates.Data.TwoDepSmallLow
public import CFSG.LocalAnalysis.StandardType.GGTWNatWord

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nLL_cast_sub (p : ℕ) [Fact p.Prime] (x y : ℕ) :
    (((x + (p - y % p)) % p : ℕ) : ZMod p) = (x : ZMod p) - (y : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (le_of_lt (Nat.mod_lt y hp)),
    ZMod.natCast_self, ZMod.natCast_mod]
  ring

private lemma l05nLL_smul_length {p M k : ℕ} {a : List ℕ} (ha : a.length = M) :
    (ggDepANSmul p k a).length = M := by
  simp only [ggDepANSmul, List.length_map, ha]

private lemma l05nLL_sub_length {p M : ℕ} {a b : List ℕ} (ha : a.length = M) (hb : b.length = M) :
    (ggDepANSub p a b).length = M := by
  simp only [ggDepANSub, List.length_zipWith, ha, hb, min_self]

private lemma l05nLL_toZ_sub {p N : ℕ} [Fact p.Prime] {a b : List ℕ} (ha : a.length = N - 1)
    (hb : b.length = N - 1) :
    ggTWNToZ p N (ggDepANSub p a b) = ggTWNToZ p N a - ggTWNToZ p N b := by
  funext j
  have hj : j.val < N - 1 := j.isLt
  have hja : j.val < a.length := by rw [ha]; exact hj
  have hjb : j.val < b.length := by rw [hb]; exact hj
  have hjl : j.val < (a.zipWith (fun x y => (x + (p - y % p)) % p) b).length := by
    rw [List.length_zipWith, ha, hb, min_self]; exact hj
  simp only [ggDepANToZ, ggDepANSub, Pi.sub_apply]
  rw [List.getD_eq_getElem (l := a.zipWith _ b) (d := 0) (n := j.val) hjl,
    List.getD_eq_getElem (l := a) (d := 0) (n := j.val) hja,
    List.getD_eq_getElem (l := b) (d := 0) (n := j.val) hjb]
  rw [List.getElem_zipWith]
  exact l05nLL_cast_sub p _ _

private lemma l05nLL_toZ_smul {p N : ℕ} [Fact p.Prime] {a : List ℕ} (ha : a.length = N - 1)
    (k : ℕ) :
    ggTWNToZ p N (ggDepANSmul p k a) = (k : ZMod p) • ggTWNToZ p N a := by
  funext j
  have hj : j.val < N - 1 := j.isLt
  have hja : j.val < a.length := by rw [ha]; exact hj
  have hjl : j.val < (a.map (fun x => k * x % p)).length := by
    rw [List.length_map, ha]; exact hj
  simp only [ggDepANToZ, ggDepANSmul, Pi.smul_apply, smul_eq_mul]
  rw [List.getD_eq_getElem (l := a.map _) (d := 0) (n := j.val) hjl,
    List.getD_eq_getElem (l := a) (d := 0) (n := j.val) hja]
  rw [List.getElem_map, ZMod.natCast_mod, Nat.cast_mul]

private lemma l05nLL_form_apply {p N : ℕ} (f v : GGTWE p N) : ggTWform f v = ggTWdot f v := by
  simp [ggTWform, ggTWdot, ggDepAform, ggDepAdot]

private lemma l05nLL_dot_add {p N : ℕ} (a v w : GGTWE p N) :
    ggTWdot a (v + w) = ggTWdot a v + ggTWdot a w := by
  rw [← l05nLL_form_apply a (v + w), map_add, l05nLL_form_apply a v, l05nLL_form_apply a w]

private lemma l05nLL_dot_smul {p N : ℕ} (a : GGTWE p N) (k : ZMod p) (v : GGTWE p N) :
    ggTWdot a (k • v) = k * ggTWdot a v := by
  rw [← l05nLL_form_apply a (k • v), map_smul, l05nLL_form_apply a v]
  simp

private lemma l05nLL_dot_cast {p N : ℕ} [Fact p.Prime] {a b : List ℕ}
    (ha : a.length = N - 1) (hb : b.length = N - 1) :
    ((ggDepANDot p a b : ℕ) : ZMod p) = ggTWdot (ggTWNToZ p N a) (ggTWNToZ p N b) := by
  have h := ggDepANDot_cast (p := p) (N := N - 1) a b ha hb
  simpa only [ggTWNToZ, ggTWdot] using h

private lemma l05nLL_inv_spec {p : ℕ} [Fact p.Prime] {a : ℕ} (ha : (a : ZMod p) ≠ 0) :
    ((ggTWLInv p a : ℕ) : ZMod p) = ((a : ZMod p))⁻¹ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  set b : ZMod p := ((a : ZMod p))⁻¹ with hbdef
  have hb : b * (a : ZMod p) = 1 := by rw [hbdef]; exact inv_mul_cancel₀ ha
  have hbne : b ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hb
    exact one_ne_zero hb.symm
  have hbval : b.val ≠ 0 := by
    intro h0
    apply hbne
    rw [← ZMod.natCast_zmod_val b, h0, Nat.cast_zero]
  have hmod : (b.val * a) % p = 1 := by
    have hcast : (((b.val * a) % p : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_zmod_val, hb, Nat.cast_one]
    have h' := (ZMod.natCast_eq_natCast_iff' ((b.val * a) % p) 1 p).mp hcast
    rwa [Nat.mod_eq_of_lt (Nat.mod_lt _ hp),
      Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt] at h'
  have hex : ∃ k ∈ List.range p, (decide (0 < k) && (k * a) % p == 1) = true := by
    refine ⟨b.val, List.mem_range.mpr (ZMod.val_lt b), ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨Nat.pos_of_ne_zero hbval, hmod⟩
  unfold ggTWLInv
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr hex)
  rw [hk']
  simp only [Option.getD_some]
  have hpred : (decide (0 < k') && (k' * a) % p == 1) = true :=
    List.find?_some (p := fun x => decide (0 < x) && (x * a) % p == 1) hk'
  have hk'mod : (k' * a) % p = 1 := by
    have := hpred
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this.2
  have hk'mul : (a : ZMod p) * (k' : ZMod p) = 1 := by
    rw [mul_comm, ← Nat.cast_mul, ← ZMod.natCast_mod (k' * a) p, hk'mod, Nat.cast_one]
  rw [hbdef]
  exact (ZMod.inv_eq_of_mul_eq_one p (a : ZMod p) (k' : ZMod p) hk'mul).symm

theorem ggTWLY0_line {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N) (pos : GGTWPos)
    {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWNValid p N q) (lam mu : ZMod p)
    (hlm : lam ≠ 0 ∨ mu ≠ 0)
    (hfix : ∀ q ∈ news, ggTWdot (ggTWNToZ p N q.2) (lam • ggTWx p N + mu • ggTWz p N pos) = 0)
    (hx : ∃ q ∈ news, ggTWdot (ggTWNToZ p N q.2) (ggTWx p N) ≠ 0) :
    (ggTWLY0 p N (ggTWPosNat pos) news).length = N - 1 ∧
      ∃ t : ZMod p, t ≠ 0 ∧
        lam • ggTWx p N + mu • ggTWz p N pos =
          t • ggTWNToZ p N (ggTWLY0 p N (ggTWPosNat pos) news) := by
  have hx' : ∃ q ∈ news, ggDepANDot p q.2 (ggTWNX N) % p ≠ 0 := by
    obtain ⟨q, hqmem, hqne⟩ := hx
    refine ⟨q, hqmem, ?_⟩
    intro h0
    apply hqne
    have hv := hnews q hqmem
    have hcast := l05nLL_dot_cast (p := p) (N := N) (a := q.2) (b := ggTWNX N) hv.2.1
      (ggTWNX_length N)
    rw [← ZMod.natCast_mod (ggDepANDot p q.2 (ggTWNX N)) p, h0, Nat.cast_zero, ggTWNX_toZ] at hcast
    exact hcast.symm
  cases hfind : news.find? (fun q => ggDepANDot p q.2 (ggTWNX N) % p != 0) with
  | none =>
      exfalso
      obtain ⟨q, hqmem, hqpred⟩ := hx'
      exact (List.find?_eq_none.mp hfind) q hqmem (by simpa [bne_iff_ne] using hqpred)
  | some q =>
      have hqmem : q ∈ news := List.mem_of_find?_eq_some hfind
      have hqpred : ggDepANDot p q.2 (ggTWNX N) % p ≠ 0 := by
        have := List.find?_some hfind
        simpa [bne_iff_ne] using this
      have hqvalid : GGTWNValid p N q := hnews q hqmem
      have hgoal : ggTWLY0 p N (ggTWPosNat pos) news = ggTWLY0One p N (ggTWPosNat pos) q.2 := by
        simp only [ggTWLY0, hfind]
      rw [hgoal]
      set ax : ZMod p := ggTWdot (ggTWNToZ p N q.2) (ggTWx p N) with hax
      set az : ZMod p := ggTWdot (ggTWNToZ p N q.2) (ggTWz p N pos) with haz
      set c : ℕ := (ggDepANDot p q.2 (ggTWNZ p N (ggTWPosNat pos)) *
        ggTWLInv p (ggDepANDot p q.2 (ggTWNX N))) % p with hc
      have hx_cast : ((ggDepANDot p q.2 (ggTWNX N) : ℕ) : ZMod p) = ax := by
        rw [l05nLL_dot_cast (p := p) (N := N) (a := q.2) (b := ggTWNX N) hqvalid.2.1
          (ggTWNX_length N), ggTWNX_toZ, hax]
      have hz_cast : ((ggDepANDot p q.2 (ggTWNZ p N (ggTWPosNat pos)) : ℕ) : ZMod p) = az := by
        rw [l05nLL_dot_cast (p := p) (N := N) (a := q.2) (b := ggTWNZ p N (ggTWPosNat pos))
          hqvalid.2.1 (ggTWNZ_length p N (ggTWPosNat pos)), ggTWNZ_toZ, haz]
      have hαx : ax ≠ 0 := by
        intro h0
        apply hqpred
        have hzero : ((ggDepANDot p q.2 (ggTWNX N) : ℕ) : ZMod p) = 0 := by rw [hx_cast, h0]
        exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ p).mp hzero)
      have hax_ne : ((ggDepANDot p q.2 (ggTWNX N) : ℕ) : ZMod p) ≠ 0 := by
        rw [hx_cast]; exact hαx
      have hinv : ((ggTWLInv p (ggDepANDot p q.2 (ggTWNX N)) : ℕ) : ZMod p) =
          (((ggDepANDot p q.2 (ggTWNX N) : ℕ) : ZMod p))⁻¹ :=
        l05nLL_inv_spec hax_ne
      have hc_eq : ((c : ℕ) : ZMod p) = az * ax⁻¹ := by
        rw [hc]
        rw [ZMod.natCast_mod (ggDepANDot p q.2 (ggTWNZ p N (ggTWPosNat pos)) *
          ggTWLInv p (ggDepANDot p q.2 (ggTWNX N))) p, Nat.cast_mul, hz_cast, hinv, hx_cast]
      have hsum : lam * ax + mu * az = 0 := by
        have h := hfix q hqmem
        rw [l05nLL_dot_add, l05nLL_dot_smul, l05nLL_dot_smul] at h
        rw [hax, haz]
        exact h
      have hmu : mu ≠ 0 := by
        intro hmu0
        have hlam0 : lam = 0 := by
          have h : lam * ax = 0 := by
            have hh := hsum
            rw [hmu0, zero_mul, add_zero] at hh
            exact hh
          exact (mul_eq_zero.mp h).resolve_right hαx
        rcases hlm with hl | hm
        · exact hl hlam0
        · exact hm hmu0
      have hlam : lam = mu * (-(az * ax⁻¹)) := by
        have h1 : lam * ax = -(mu * az) := add_eq_zero_iff_eq_neg.mp hsum
        calc lam = (lam * ax) * ax⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hαx, mul_one]
          _ = (-(mu * az)) * ax⁻¹ := by rw [h1]
          _ = mu * (-(az * ax⁻¹)) := by ring
      have hY0 : ggTWNToZ p N (ggTWLY0One p N (ggTWPosNat pos) q.2) =
          ggTWz p N pos - (az * ax⁻¹) • ggTWx p N := by
        unfold ggTWLY0One
        rw [l05nLL_toZ_sub (ggTWNZ_length p N (ggTWPosNat pos))
            (l05nLL_smul_length (ggTWNX_length N)),
          l05nLL_toZ_smul (ggTWNX_length N), hc_eq, ggTWNZ_toZ, ggTWNX_toZ]
      refine ⟨?_, mu, hmu, ?_⟩
      · unfold ggTWLY0One
        exact l05nLL_sub_length (ggTWNZ_length p N (ggTWPosNat pos))
          (l05nLL_smul_length (ggTWNX_length N))
      · rw [hY0, hlam, mul_smul, ← smul_add]
        congr 1
        rw [neg_smul, sub_eq_add_neg, add_comm]

private lemma l05nLL_movesLine_smul {p N : ℕ} [Fact p.Prime] (R : Set (GGTWE p N))
    (y : GGTWE p N) (s : Module.End (ZMod p) (GGTWE p N)) (t : ZMod p) (ht : t ≠ 0) :
    GGTWMovesLine R (t • y) s ↔ GGTWMovesLine R y s := by
  constructor
  · rintro ⟨hfix, v, hvR, hv⟩
    refine ⟨?_, v, hvR, ?_⟩
    · have h : t • s y = t • y := by rw [← map_smul, hfix]
      exact smul_right_injective (GGTWE p N) ht h
    · intro w hwR c d hc heq
      apply hv w hwR c (d * t⁻¹) hc
      rw [heq, smul_smul, mul_assoc, inv_mul_cancel₀ ht, mul_one]
  · rintro ⟨hfix, v, hvR, hv⟩
    refine ⟨?_, v, hvR, ?_⟩
    · rw [map_smul, hfix]
    · intro w hwR c d hc heq
      apply hv w hwR c (d * t) hc
      rw [heq, smul_smul]

theorem ggTWKill_other_smul {p N : ℕ} [Fact p.Prime] (pos : GGTWPos)
    (news : Set (GGTWE p N × GGTWE p N)) (y : GGTWE p N) (t : ZMod p) (ht : t ≠ 0) :
    GGTWKill .other p N pos news (t • y) ↔ GGTWKill .other p N pos news y := by
  simp only [GGTWKill]
  constructor
  · rintro (h | ⟨s, hs, hrefl, hmoves⟩)
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, hrefl, (l05nLL_movesLine_smul _ y s t ht).mp hmoves⟩
  · rintro (h | ⟨s, hs, hrefl, hmoves⟩)
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, hrefl, (l05nLL_movesLine_smul _ y s t ht).mpr hmoves⟩

end CFSG.StandardType

end
