module

public import CFSG.Quasithin.H13.L32A755b
public import CFSG.Quasithin.H13.L32A753h

public section

namespace CFSG.Quasithin.H13.L32A.M755

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 Orbit

@[expose] def innerS : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 40, 41,
  42, 43, 44, 45, 46, 47, 56, 57, 58, 59, 60, 61, 62, 63]

theorem innerS_spec : ∀ i < 64,
    (i ∈ innerS ↔ (sWords.getD i []).countP (fun j => j ≠ 0) % 2 = 0) := by
  decide

theorem mem_g2Derived_iff
    {i : ℕ} (hi : i < 64) :
    sEltG i ∈ g2Derived (ZMod 2) ↔ i ∈ innerS := by
  rw [M753.sEltG_eq_foldl, M753.foldl_genS_mem_iff _ (sWords_spec i hi).2, innerS_spec i hi,
    ← Nat.even_iff]
  exact ⟨fun h => h.1 (one_mem _), fun h => ⟨fun _ => h, fun _ => one_mem _⟩⟩

theorem fix_S0 : ∀ c ∈ ptsQ, (∀ i ∈ innerS, nq (mact (sM i) c) = c) → c = 8 := by
  decide +kernel

theorem line_S0 : ∀ d ∈ ptsQ, d ≠ 8 →
    (∀ i ∈ innerS, nq (mact (sM i) d) = d ∨ nq (mact (sM i) d) = d ^^^ 8) → d = 32 ∨ d = 40 := by
  decide +kernel

theorem innerS_lt : ∀ i ∈ innerS, i < 64 := by
  decide

theorem decodeZ_129 : decodeZ 129 = zornOne := by
  decide

theorem nq_mact_mem (g : ↥(quasithinG2 (ZMod 2))) {c : ℕ} (hc : c ∈ ptsQ) :
    nq (mact (matCode g.1) c) ∈ ptsQ := by
  obtain ⟨hc0, -, -⟩ := ptsQ_mem c hc
  have hm := mact_mem_o0Codes g.2 hc0
  have hd := decodeZ_mact' g.1 (mem_o0Codes.1 hc0).1
  refine nq_mem_ptsQ _ hm (fun h0 => ?_) (fun h1 => ?_)
  · rw [h0, decodeZ_zero] at hd
    have h1 : decodeZ c = decodeZ 0 := g.1.injective (by rw [← hd, decodeZ_zero, map_zero])
    have := decodeZ_injective (mem_o0Codes.1 hc0).1 (by norm_num) h1
    subst this
    exact absurd hc (by decide)
  · rw [h1, decodeZ_129] at hd
    have h2 : decodeZ c = decodeZ 129 :=
      g.1.injective (by rw [← hd, decodeZ_129, (mem_quasithinG2_isZornAuto g.2).map_one])
    have := decodeZ_injective (mem_o0Codes.1 hc0).1 (by norm_num) h2
    subst this
    exact absurd hc (by decide)

theorem g2QAct_sEltG {i : ℕ} (hi : i < 64) {c : ℕ} (hc : c ∈ ptsQ) :
    g2QAct (ZMod 2) (sEltG i) (ptQ c) = ptQ (nq (mact (sM i) c)) := by
  have hm := mact_mem_o0Codes (sEltG i).2 (ptsQ_mem c hc).1
  rw [g2QAct_ptQ _ (ptsQ_mem c hc).1, ← ptQ_nq hm]
  congr 2
  rw [show (sEltG i).1 = sElt i from rfl, matCode_sElt hi]

theorem nq_sM_mem {i : ℕ} (hi : i < 64) {c : ℕ} (hc : c ∈ ptsQ) : nq (mact (sM i) c) ∈ ptsQ := by
  have h := nq_mact_mem (sEltG i) hc
  rwa [show (sEltG i).1 = sElt i from rfl, matCode_sElt hi] at h

theorem eq_ptQ_eight {p : ModQ} (hp : p ≠ 1)
    (hfix : ∀ i ∈ innerS, g2QAct (ZMod 2) (sEltG i) p = p) : p = ptQ 8 := by
  obtain ⟨c, hc, rfl⟩ := exists_ptQ hp
  refine congrArg ptQ (fix_S0 c hc fun i hi => ?_)
  have h := hfix i hi
  rw [g2QAct_sEltG (innerS_lt i hi) hc] at h
  exact ptQ_injective (nq_sM_mem (innerS_lt i hi) hc) hc h

theorem xor8_mem : ∀ d ∈ ptsQ, d ≠ 8 → (8 ^^^ d) ∈ ptsQ := by
  decide

theorem eq_of_mem_line0 {q : ModQ} (hq : q ≠ 1) (hq8 : q ≠ ptQ 8)
    (h : ∀ i ∈ innerS, g2QAct (ZMod 2) (sEltG i) q = q ∨
      g2QAct (ZMod 2) (sEltG i) q = ptQ 8 * q) : q = ptQ 32 ∨ q = ptQ 40 := by
  have h8 : (8 : ℕ) ∈ ptsQ := by decide
  obtain ⟨d, hd, rfl⟩ := exists_ptQ hq
  have hd8 : d ≠ 8 := fun e => hq8 (by rw [e])
  have key := line_S0 d hd hd8 fun i hi => by
    have hi64 := innerS_lt i hi
    rcases h i hi with h1 | h1
    · rw [g2QAct_sEltG hi64 hd] at h1
      exact Or.inl (ptQ_injective (nq_sM_mem hi64 hd) hd h1)
    · rw [g2QAct_sEltG hi64 hd, ptQ_mul (ptsQ_mem 8 h8).1 (ptsQ_mem d hd).1] at h1
      have hx : (8 ^^^ d) ∈ ptsQ := xor8_mem d hd hd8
      right
      rw [ptQ_injective (nq_sM_mem hi64 hd) hx h1, Nat.xor_comm]
  rcases key with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

end CFSG.Quasithin.H13.L32A.M755
