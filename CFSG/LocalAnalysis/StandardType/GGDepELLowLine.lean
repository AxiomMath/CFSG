module

public import CFSG.LocalAnalysis.StandardType.GGDepELNatWord
public import CFSG.LocalAnalysis.StandardType.GGTWLowOutE6Aux

public section

namespace CFSG.StandardType

open Certificates.DepED4Low Certificates.TwoDepSmall Certificates.DepASmall
open Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nLY_inv_spec {p : ℕ} [Fact p.Prime] {a : ℕ} (ha : (a : ZMod p) ≠ 0) :
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

private lemma l05nLY_dot_add {p N : ℕ} (a v w : GGDepAE p N) :
    ggDepAdot a (v + w) = ggDepAdot a v + ggDepAdot a w := by
  simp only [ggDepAdot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ggDepELY0_line {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGDepELNValid q)
    (lam mu : ZMod 3) (hlm : lam ≠ 0 ∨ mu ≠ 0)
    (hfix : ∀ q ∈ news, ggDepAdot (ggDepELToZ q.2) (lam • ggDepELx + mu • ggDepELz) = 0)
    (hx : ∃ q ∈ news, ggDepAdot (ggDepELToZ q.2) ggDepELx ≠ 0) :
    (ggDepELY0 news).length = 6 ∧
      ∃ t : ZMod 3, t ≠ 0 ∧
        lam • ggDepELx + mu • ggDepELz = t • ggDepELToZ (ggDepELY0 news) := by
  have hx' : ∃ q ∈ news, ggDepANDot 3 q.2 ggDepELNX % 3 ≠ 0 := by
    obtain ⟨q, hqmem, hqne⟩ := hx
    refine ⟨q, hqmem, ?_⟩
    intro h0
    apply hqne
    have hv := hnews q hqmem
    have hcast := ggDepELDot_cast (a := q.2) (b := ggDepELNX) hv.2.1 ggDepELNX_length
    rw [← ZMod.natCast_mod (ggDepANDot 3 q.2 ggDepELNX) 3, h0, Nat.cast_zero,
      ggDepELNX_toZ] at hcast
    exact hcast.symm
  cases hfind : news.find? (fun q => ggDepANDot 3 q.2 ggDepELNX % 3 != 0) with
  | none =>
      exfalso
      obtain ⟨q, hqmem, hqpred⟩ := hx'
      exact (List.find?_eq_none.mp hfind) q hqmem (by simpa [bne_iff_ne] using hqpred)
  | some q =>
      have hqmem : q ∈ news := List.mem_of_find?_eq_some hfind
      have hqpred : ggDepANDot 3 q.2 ggDepELNX % 3 ≠ 0 := by
        have := List.find?_some hfind
        simpa [bne_iff_ne] using this
      have hqvalid : GGDepELNValid q := hnews q hqmem
      have hgoal : ggDepELY0 news = ggDepELY0One q.2 := by
        simp only [ggDepELY0, hfind]
      rw [hgoal]
      set ax : ZMod 3 := ggDepAdot (ggDepELToZ q.2) ggDepELx with hax
      set az : ZMod 3 := ggDepAdot (ggDepELToZ q.2) ggDepELz with haz
      set c : ℕ := (ggDepANDot 3 q.2 ggDepELNZ *
        ggTWLInv 3 (ggDepANDot 3 q.2 ggDepELNX)) % 3 with hc
      have hx_cast : ((ggDepANDot 3 q.2 ggDepELNX : ℕ) : ZMod 3) = ax := by
        rw [ggDepELDot_cast (a := q.2) (b := ggDepELNX) hqvalid.2.1 ggDepELNX_length,
          ggDepELNX_toZ, hax]
      have hz_cast : ((ggDepANDot 3 q.2 ggDepELNZ : ℕ) : ZMod 3) = az := by
        rw [ggDepELDot_cast (a := q.2) (b := ggDepELNZ) hqvalid.2.1 ggDepELNZ_length,
          ggDepELNZ_toZ, haz]
      have hαx : ax ≠ 0 := by
        intro h0
        apply hqpred
        have hzero : ((ggDepANDot 3 q.2 ggDepELNX : ℕ) : ZMod 3) = 0 := by rw [hx_cast, h0]
        exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ 3).mp hzero)
      have hax_ne : ((ggDepANDot 3 q.2 ggDepELNX : ℕ) : ZMod 3) ≠ 0 := by
        rw [hx_cast]; exact hαx
      have hinv : ((ggTWLInv 3 (ggDepANDot 3 q.2 ggDepELNX) : ℕ) : ZMod 3) =
          (((ggDepANDot 3 q.2 ggDepELNX : ℕ) : ZMod 3))⁻¹ :=
        l05nLY_inv_spec hax_ne
      have hc_eq : ((c : ℕ) : ZMod 3) = az * ax⁻¹ := by
        rw [hc]
        rw [ZMod.natCast_mod (ggDepANDot 3 q.2 ggDepELNZ *
          ggTWLInv 3 (ggDepANDot 3 q.2 ggDepELNX)) 3, Nat.cast_mul, hz_cast, hinv, hx_cast]
      have hsum : lam * ax + mu * az = 0 := by
        have h := hfix q hqmem
        rw [l05nLY_dot_add, l05nL6_dot_smul, l05nL6_dot_smul] at h
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
      have hY0 : ggDepELToZ (ggDepELY0One q.2) =
          ggDepELz - (az * ax⁻¹) • ggDepELx := by
        unfold ggDepELY0One
        rw [ggDepELToZ_sub ggDepELNZ_length (ggDepELSmul_length c ggDepELNX_length),
          ggDepELToZ_smul ggDepELNX_length, hc_eq, ggDepELNZ_toZ, ggDepELNX_toZ]
      refine ⟨?_, mu, hmu, ?_⟩
      · unfold ggDepELY0One
        exact ggDepELSub_length ggDepELNZ_length (ggDepELSmul_length c ggDepELNX_length)
      · rw [hY0, hlam, mul_smul, ← smul_add]
        congr 1
        rw [neg_smul, sub_eq_add_neg, add_comm]

private lemma l05nLY_movesLine_smul (R : Set (GGDepAE 3 6)) (y : GGDepAE 3 6)
    (s : Module.End (ZMod 3) (GGDepAE 3 6)) (t : ZMod 3) (ht : t ≠ 0) :
    GGDepELMovesLine R (t • y) s ↔ GGDepELMovesLine R y s := by
  constructor
  · rintro ⟨hfix, v, hvR, hv⟩
    refine ⟨?_, v, hvR, ?_⟩
    · have h : t • s y = t • y := by rw [← map_smul, hfix]
      exact smul_right_injective (GGDepAE 3 6) ht h
    · intro w hwR c d hc heq
      apply hv w hwR c (d * t⁻¹) hc
      rw [heq, smul_smul, mul_assoc, inv_mul_cancel₀ ht, mul_one]
  · rintro ⟨hfix, v, hvR, hv⟩
    refine ⟨?_, v, hvR, ?_⟩
    · rw [map_smul, hfix]
    · intro w hwR c d hc heq
      apply hv w hwR c (d * t) hc
      rw [heq, smul_smul]

theorem ggDepELKill_other_smul (news : Set (GGDepAE 3 6 × GGDepAE 3 6)) (y : GGDepAE 3 6)
    (t : ZMod 3) (ht : t ≠ 0) :
    GGDepELKill .other news (t • y) ↔ GGDepELKill .other news y := by
  simp only [GGDepELKill]
  constructor
  · rintro (h | ⟨s, hs, hrefl, hmoves⟩)
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, hrefl, (l05nLY_movesLine_smul _ y s t ht).mp hmoves⟩
  · rintro (h | ⟨s, hs, hrefl, hmoves⟩)
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, hrefl, (l05nLY_movesLine_smul _ y s t ht).mpr hmoves⟩

end CFSG.StandardType

end
