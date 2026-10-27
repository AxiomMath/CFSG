module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08TestCert
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertPerm

public section

namespace CFSG.StandardType.TestLin

open Matrix

variable {n : ℕ}

@[expose] def certOKGiven (gens : List (Vn n × Vn n)) (x₀ : Vn n) (sets : List (List (Vn n)))
    (pats : List ((Vn n × Vn n) × PatV n)) (reps : List (Vn n × Vn n)) (s2 : List (S2V n))
    (gp : List (ℕ × ℕ)) : Bool :=
  gens.all (fun l => decide (l.2 ⬝ᵥ l.1 = 2)) && reps.all (fun l => decide (l.2 ⬝ᵥ l.1 = 2)) &&
    sets.all (fun S => gens.all fun g => S.all fun v => decide (letApp g v ∈ S)) &&
    pats.all (patB gens sets x₀ reps) &&
    (List.range reps.length).all fun i => (List.range reps.length).all fun j =>
      decide ((i, j) ∈ gp) || s2B gens sets x₀ reps i j (s2.getD (i * reps.length + j) (.sym []))

variable {W A M : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} {x₀ : Vn n}

theorem TestHyp.mem_of_certOKGiven (hT : TestHyp W x₀ A M) {gens : List (Vn n × Vn n)}
    {sets : List (List (Vn n))} {pats : List ((Vn n × Vn n) × PatV n)}
    {reps : List (Vn n × Vn n)} {s2 : List (S2V n)} {gp : List (ℕ × ℕ)}
    (hOK : certOKGiven gens x₀ sets pats reps s2 gp = true) (hgW : ∀ l ∈ gens, letLin l ∈ W)
    (hWgen : W ≤ Subgroup.closure {g | ∃ l ∈ gens, g = letLin l})
    (hred : ∀ u ∈ A, IsRefl u → ¬ FixesLine x₀ u → ∃ w ∈ W, ∃ p ∈ pats,
      ∃ h : p.1.2 ⬝ᵥ p.1.1 = 2, w * u * w⁻¹ = refl p.1.1 p.1.2 h)
    (hgiven : ∀ i j, (i, j) ∈ gp → ∀ (hi : (letAt reps i).2 ⬝ᵥ (letAt reps i).1 = 2)
      (hj : (letAt reps j).2 ⬝ᵥ (letAt reps j).1 = 2),
      refl (letAt reps i).1 (letAt reps i).2 hi ∈ M →
      refl (letAt reps j).1 (letAt reps j).2 hj ∈ A → refl (letAt reps j).1 (letAt reps j).2 hj ∈ M)
    {r t : Vn n ≃ₗ[ZMod 3] Vn n} (hr : r ∈ M) (hrR : IsRefl r) (hrx : ¬ FixesLine x₀ r)
    (ht : t ∈ A) (htR : IsRefl t) (htx : ¬ FixesLine x₀ t) : t ∈ M := by
  unfold certOKGiven at hOK
  simp only [Bool.and_eq_true] at hOK
  obtain ⟨⟨⟨⟨hgOK, hrOK⟩, hsOK⟩, hpOK⟩, hs2OK⟩ := hOK
  have hgens : AlphOK gens := AlphOK.of_all hgOK
  have hreps : AlphOK reps := AlphOK.of_all hrOK
  have hinv := sets_inv_of_gens hgens hWgen hsOK
  have hcls : ∀ u ∈ A, IsRefl u → ¬ FixesLine x₀ u → ∃ w ∈ W, ∃ i < reps.length,
      ∃ h : (letAt reps i).2 ⬝ᵥ (letAt reps i).1 = 2,
        w * u * w⁻¹ = refl (letAt reps i).1 (letAt reps i).2 h := by
    intro u hu huR hux
    obtain ⟨w, hw, p, hp, hpc, hwu⟩ := hred u hu huR hux
    have hpA : refl p.1.1 p.1.2 hpc ∈ A := by
      rw [← hwu]
      exact A.mul_mem (A.mul_mem (hT.le (hT.W_le hw)) hu) (A.inv_mem (hT.le (hT.W_le hw)))
    obtain ⟨w', hw', i, hi, hrep, hw'p⟩ := hT.exists_rep_of_patB hgens hgW hinv hreps
      (List.all_eq_true.mp hpOK p hp) hpc hpA
    refine ⟨w' * w, W.mul_mem hw' hw, i, hi, hrep, ?_⟩
    rw [← hw'p, ← hwu, mul_inv_rev]
    group
  obtain ⟨wr, hwr, i, hi, hri, hwrr⟩ := hcls r (hT.le hr) hrR hrx
  obtain ⟨wt, hwt, j, hj, htj, hwtt⟩ := hcls t ht htR htx
  have hrM : refl (letAt reps i).1 (letAt reps i).2 hri ∈ M := by
    rw [← hwrr]
    exact M.mul_mem (M.mul_mem (hT.W_le hwr) hr) (M.inv_mem (hT.W_le hwr))
  have htA : refl (letAt reps j).1 (letAt reps j).2 htj ∈ A := by
    rw [← hwtt]
    exact A.mul_mem (A.mul_mem (hT.le (hT.W_le hwt)) ht) (A.inv_mem (hT.le (hT.W_le hwt)))
  have hB := List.all_eq_true.mp (List.all_eq_true.mp hs2OK i (List.mem_range.mpr hi)) j
    (List.mem_range.mpr hj)
  have htM : refl (letAt reps j).1 (letAt reps j).2 htj ∈ M := by
    rcases Bool.or_eq_true_iff.mp hB with hg | hB
    · exact hgiven i j (of_decide_eq_true hg) hri htj hrM htA
    · exact hT.mem_of_s2B hgens hgW hinv hri htj hrM htA hB
  have heq : t = wt⁻¹ * refl (letAt reps j).1 (letAt reps j).2 htj * wt := by
    rw [← hwtt]
    group
  rw [heq]
  exact M.mul_mem (M.mul_mem (M.inv_mem (hT.W_le hwt)) htM) (hT.W_le hwt)

theorem linTest_perm_of_certOKGiven [NeZero n] {ℓ : ℕ} (S : Fin ℓ → (Vn n ≃ₗ[ZMod 3] Vn n))
    (gens : List (Vn n × Vn n)) (hlen : gens.length = ℓ)
    (hS : ∀ k : Fin ℓ, S k = letLin (letAt gens k))
    (hperm : permGroup n ≤ Subgroup.closure (Set.range S)) {sets : List (List (Vn n))}
    {pats : List ((Vn n × Vn n) × PatV n)} {reps : List (Vn n × Vn n)} {s2 : List (S2V n)}
    {gp : List (ℕ × ℕ)} (hOK : certOKGiven gens (oneN n) sets pats reps s2 gp = true)
    (hcov : permCovB n pats = true) :
    ∀ A Mg : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n),
      TestHyp (Subgroup.closure (Set.range S)) (oneN n) A Mg →
      (∀ i j, (i, j) ∈ gp → ∀ (hi : (letAt reps i).2 ⬝ᵥ (letAt reps i).1 = 2)
        (hj : (letAt reps j).2 ⬝ᵥ (letAt reps j).1 = 2),
        refl (letAt reps i).1 (letAt reps i).2 hi ∈ Mg →
        refl (letAt reps j).1 (letAt reps j).2 hj ∈ A →
        refl (letAt reps j).1 (letAt reps j).2 hj ∈ Mg) →
      ∀ r ∈ Mg, IsRefl r → ¬ FixesLine (oneN n) r →
      ∀ t ∈ A, IsRefl t → ¬ FixesLine (oneN n) t → t ∈ Mg := by
  intro A Mg hT hgiven r hr hrR hrx t ht htR htx
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
  exact hT.mem_of_certOKGiven hOK hgW hWgen (hT.perm_cover hperm hcov) hgiven hr hrR hrx ht htR
    htx

end CFSG.StandardType.TestLin

end
