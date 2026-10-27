module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2S08SgnLinExt

public section

namespace CFSG.StandardType.TestLin

open Matrix

variable {r : ℕ}

@[expose] def sgnDiffL2 (i j : Fin r) : Vn (r + 2) × Vn (r + 2) :=
  (frameE2 r i - frameE2 r j, frameE2 r i - frameE2 r j)

@[expose] def sgnSumL2 (i j : Fin r) : Vn (r + 2) × Vn (r + 2) :=
  (frameE2 r i + frameE2 r j, frameE2 r i + frameE2 r j)

theorem sgnDiff2_eq_letLin (i j : Fin r) (h : i ≠ j) :
    sgnDiff2 i j h = letLin (sgnDiffL2 i j) := by
  rw [letLin_of]
  rfl

theorem sgnSum2_eq_letLin (i j : Fin r) (h : i ≠ j) : sgnSum2 i j h = letLin (sgnSumL2 i j) := by
  rw [letLin_of]
  rfl

@[expose] def dFrameB2 (r : ℕ) (L : List ((Vn (r + 2) × Vn (r + 2)) × List ℕ × ℕ)) : Bool :=
  decide (∀ i j : Fin r, i ≠ j → sgnDiffL2 i j ∈ L.map Prod.fst ∧ sgnSumL2 i j ∈ L.map Prod.fst)

@[expose] def dCovB2 (r : ℕ) (pats : List ((Vn (r + 2) × Vn (r + 2)) × PatV (r + 2))) : Bool :=
  ((List.range (r + 1)).all fun k => [0, 1, 2].all fun l => [0, 1, 2].all fun e =>
    [0, 1, 2].all fun g => [0, 1, 2].all fun e' => [0, 1, 2].all fun d =>
      !(decide (canonA2 r k l e' d ⬝ᵥ canonC2 r k e g = 2) &&
          movesB (xLast2 r) (canonC2 r k e g) (canonA2 r k l e' d)) ||
        decide ((canonC2 r k e g, canonA2 r k l e' d) ∈ pats.map Prod.fst)) &&
  ([0, 1, 2].all fun l => [0, 1, 2].all fun e => [0, 1, 2].all fun g =>
    [0, 1, 2].all fun e' => [0, 1, 2].all fun d =>
      !(decide (canonAD2 r l e' d ⬝ᵥ canonD2 r e g = 2) &&
          movesB (xLast2 r) (canonD2 r e g) (canonAD2 r l e' d)) ||
        decide ((canonD2 r e g, canonAD2 r l e' d) ∈ pats.map Prod.fst))

variable {W A M : Subgroup (Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2))}

theorem TestHyp.dframe2_cover (hr : 3 ≤ r) (hT : TestHyp W (xLast2 r) A M)
    (hW : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff2 i j h ∈ W)
    (hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum2 i j h ∈ W)
    {pats : List ((Vn (r + 2) × Vn (r + 2)) × PatV (r + 2))} (hcov : dCovB2 r pats = true) :
    ∀ u ∈ A, IsRefl u → ¬ FixesLine (xLast2 r) u → ∃ w ∈ W, ∃ p ∈ pats,
      ∃ h : p.1.2 ⬝ᵥ p.1.1 = 2, w * u * w⁻¹ = refl p.1.1 p.1.2 h := by
  intro u hu huR hux
  unfold dCovB2 at hcov
  rw [Bool.and_eq_true] at hcov
  obtain ⟨hcovC, hcovD⟩ := hcov
  obtain ⟨w, hw, k, hkr, hwx, hcase⟩ := hT.exists_canonical_D2 hr hW hWs hu huR hux
  have key : ∀ (c a : Vn (r + 2)) (h : a ⬝ᵥ c = 2), w * u * w⁻¹ = refl c a h →
      (c, a) ∈ pats.map Prod.fst → ∃ p ∈ pats, ∃ h : p.1.2 ⬝ᵥ p.1.1 = 2,
        w * u * w⁻¹ = refl p.1.1 p.1.2 h := by
    intro c a h hconj hc
    obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hc
    have hp2 : p.1.2 ⬝ᵥ p.1.1 = 2 := by
      rw [hpeq]
      exact h
    refine ⟨p, hp, hp2, ?_⟩
    rw [hconj]
    exact refl_congr (congrArg Prod.fst hpeq).symm (congrArg Prod.snd hpeq).symm h hp2
  refine ⟨w, hw, ?_⟩
  rcases hcase with ⟨l, e, g, e', d, h, hconj⟩ | ⟨-, l, e, g, e', d, h, hconj⟩
  · have hmv := movesB_of_conj hwx hux h hconj
    have hc := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
      (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hcovC k
        (List.mem_range.mpr (by omega))) l (zmod3_mem_list l)) e (zmod3_mem_list e)) g
          (zmod3_mem_list g)) e' (zmod3_mem_list e')) d (zmod3_mem_list d)
    rw [show decide (canonA2 r k l e' d ⬝ᵥ canonC2 r k e g = 2) = true from decide_eq_true h,
      hmv, Bool.and_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc
    exact key _ _ h hconj hc
  · have hmv := movesB_of_conj hwx hux h hconj
    have hc := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
      (List.all_eq_true.mp (List.all_eq_true.mp hcovD l (zmod3_mem_list l)) e
        (zmod3_mem_list e)) g (zmod3_mem_list g)) e' (zmod3_mem_list e')) d (zmod3_mem_list d)
    rw [show decide (canonAD2 r l e' d ⬝ᵥ canonD2 r e g = 2) = true from decide_eq_true h, hmv,
      Bool.and_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc
    exact key _ _ h hconj hc

theorem linTest_dframe2_of_certOK (hr : 3 ≤ r) {ℓ : ℕ}
    (S : Fin ℓ → (Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2)))
    (gens : List (Vn (r + 2) × Vn (r + 2))) (hlen : gens.length = ℓ)
    (hS : ∀ k : Fin ℓ, S k = letLin (letAt gens k))
    {L : List ((Vn (r + 2) × Vn (r + 2)) × List ℕ × ℕ)} (hL : reflCertB gens L = true)
    (hF : dFrameB2 r L = true) {sets : List (List (Vn (r + 2)))}
    {pats : List ((Vn (r + 2) × Vn (r + 2)) × PatV (r + 2))}
    {reps : List (Vn (r + 2) × Vn (r + 2))} {s2 : List (S2V (r + 2))}
    (hOK : certOK gens (xLast2 r) sets pats reps s2 = true) (hcov : dCovB2 r pats = true) :
    ∀ A Mg : Subgroup (Vn (r + 2) ≃ₗ[ZMod 3] Vn (r + 2)),
      TestHyp (Subgroup.closure (Set.range S)) (xLast2 r) A Mg →
      ∀ t₁ ∈ Mg, IsRefl t₁ → ¬ FixesLine (xLast2 r) t₁ →
      ∀ t ∈ A, IsRefl t → ¬ FixesLine (xLast2 r) t → t ∈ Mg := by
  intro A Mg hT r' hr' hrR hrx t ht htR htx
  have hgens : AlphOK gens := by
    unfold certOK at hOK
    simp only [Bool.and_eq_true] at hOK
    exact AlphOK.of_all hOK.1.1.1.1
  have hgW : ∀ l ∈ gens, letLin l ∈ Subgroup.closure (Set.range S) := by
    intro l hl
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
    have hl' : letAt gens k = gens[k] := List.getD_eq_getElem _ _ hk
    rw [← hl', ← hS ⟨k, hlen ▸ hk⟩]
    exact Subgroup.subset_closure (Set.mem_range_self _)
  have hWgen : Subgroup.closure (Set.range S) ≤
      Subgroup.closure {g | ∃ l ∈ gens, g = letLin l} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    refine Subgroup.subset_closure ⟨letAt gens k, ?_, hS k⟩
    have hk : k.val < gens.length := hlen ▸ k.isLt
    rw [show letAt gens k = gens[k.val] from List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  unfold dFrameB2 at hF
  rw [decide_eq_true_eq] at hF
  have hW : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff2 i j h ∈ Subgroup.closure (Set.range S) :=
    fun i j h => sgnDiff2_eq_letLin i j h ▸ mem_of_reflCertB hgens hgW hL (hF i j h).1
  have hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum2 i j h ∈ Subgroup.closure (Set.range S) :=
    fun i j h => sgnSum2_eq_letLin i j h ▸ mem_of_reflCertB hgens hgW hL (hF i j h).2
  exact hT.mem_of_certOK hOK hgW hWgen (hT.dframe2_cover hr hW hWs hcov) hr' hrR hrx ht htR htx

end CFSG.StandardType.TestLin

end
