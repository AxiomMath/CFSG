module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertA7Full

public section

namespace CFSG.StandardType.TestLin

open Matrix

variable {n : ℕ} {W A M : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} {x₀ : Vn n}

theorem TestHyp.mem_of_certOKGiven_of (hT : TestHyp W x₀ A M) {gens : List (Vn n × Vn n)}
    {sets : List (List (Vn n))} {pats : List ((Vn n × Vn n) × PatV n)}
    {reps : List (Vn n × Vn n)} {s2 : List (S2V n)} {gp : List (ℕ × ℕ)}
    (hOK : certOKGiven gens x₀ sets pats reps s2 gp = true) (hgW : ∀ l ∈ gens, letLin l ∈ W)
    (hWgen : W ≤ Subgroup.closure {g | ∃ l ∈ gens, g = letLin l})
    (hred : ∀ u ∈ A, IsRefl u → ¬ FixesLine x₀ u → ∃ w ∈ W, ∃ p ∈ pats,
      ∃ h : p.1.2 ⬝ᵥ p.1.1 = 2, w * u * w⁻¹ = refl p.1.1 p.1.2 h)
    (P : (Vn n ≃ₗ[ZMod 3] Vn n) → Prop) (hPW : ∀ w ∈ W, ∀ u, P u → P (w * u * w⁻¹))
    (hgiven : ∀ i j, (i, j) ∈ gp → ∀ (hi : (letAt reps i).2 ⬝ᵥ (letAt reps i).1 = 2)
      (hj : (letAt reps j).2 ⬝ᵥ (letAt reps j).1 = 2),
      refl (letAt reps i).1 (letAt reps i).2 hi ∈ M →
      refl (letAt reps j).1 (letAt reps j).2 hj ∈ A →
      P (refl (letAt reps j).1 (letAt reps j).2 hj) →
      refl (letAt reps j).1 (letAt reps j).2 hj ∈ M)
    {r t : Vn n ≃ₗ[ZMod 3] Vn n} (hr : r ∈ M) (hrR : IsRefl r) (hrx : ¬ FixesLine x₀ r)
    (ht : t ∈ A) (htR : IsRefl t) (htx : ¬ FixesLine x₀ t) (hPt : P t) : t ∈ M := by
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
  have hPj : P (refl (letAt reps j).1 (letAt reps j).2 htj) := hwtt ▸ hPW wt hwt t hPt
  have hB := List.all_eq_true.mp (List.all_eq_true.mp hs2OK i (List.mem_range.mpr hi)) j
    (List.mem_range.mpr hj)
  have htM : refl (letAt reps j).1 (letAt reps j).2 htj ∈ M := by
    rcases Bool.or_eq_true_iff.mp hB with hg | hB
    · exact hgiven i j (of_decide_eq_true hg) hri htj hrM htA hPj
    · exact hT.mem_of_s2B hgens hgW hinv hri htj hrM htA hB
  have heq : t = wt⁻¹ * refl (letAt reps j).1 (letAt reps j).2 htj * wt := by
    rw [← hwtt]
    group
  rw [heq]
  exact M.mul_mem (M.mul_mem (M.inv_mem (hT.W_le hwt)) htM) (hT.W_le hwt)

@[expose] def a7fCen (u : Vn 7 ≃ₗ[ZMod 3] Vn 7) : Prop :=
  ∃ S : Finset (Fin 7), 5 ≤ S.card ∧ ∀ v : Vn 7, ∀ a ∈ S, ∀ b ∈ S, (u v - v) a = (u v - v) b

theorem a7fCen_conj (σ : Equiv.Perm (Fin 7)) {u : Vn 7 ≃ₗ[ZMod 3] Vn 7} (hu : a7fCen u) :
    a7fCen (permN σ * u * (permN σ)⁻¹) := by
  obtain ⟨S, hS, hc⟩ := hu
  refine ⟨S.map σ.toEmbedding, by rw [Finset.card_map]; exact hS, fun v a' ha' b' hb' => ?_⟩
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp ha'
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hb'
  have key : ∀ c : Fin 7, ((permN σ * u * (permN σ)⁻¹) v - v) (σ c) =
      (u (permN σ⁻¹ v) - permN σ⁻¹ v) c := by
    intro c
    rw [permN_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, Pi.sub_apply, Pi.sub_apply,
      permN_apply, permN_apply, Equiv.symm_apply_apply, Equiv.Perm.inv_def, Equiv.symm_symm]
  change ((permN σ * u * (permN σ)⁻¹) v - v) (σ a) = ((permN σ * u * (permN σ)⁻¹) v - v) (σ b)
  rw [key, key]
  exact hc _ a ha b hb

theorem not_a7fCen_of {u : Vn 7 ≃ₗ[ZMod 3] Vn 7} (k : Fin 7)
    (h : ∀ S : Finset (Fin 7), 5 ≤ S.card → ∃ a ∈ S, ∃ b ∈ S,
      (u (Pi.single k 1) - (Pi.single k 1 : Vn 7)) a ≠
        (u (Pi.single k 1) - (Pi.single k 1 : Vn 7)) b) :
    ¬ a7fCen u := by
  rintro ⟨S, hS, hc⟩
  obtain ⟨a, ha, b, hb, hab⟩ := h S hS
  exact hab (hc _ a ha b hb)

theorem linTest_perm_of_certOKGiven_of [NeZero n] {ℓ : ℕ} (S : Fin ℓ → (Vn n ≃ₗ[ZMod 3] Vn n))
    (gens : List (Vn n × Vn n)) (hlen : gens.length = ℓ)
    (hS : ∀ k : Fin ℓ, S k = letLin (letAt gens k))
    (hperm : permGroup n ≤ Subgroup.closure (Set.range S)) {sets : List (List (Vn n))}
    {pats : List ((Vn n × Vn n) × PatV n)} {reps : List (Vn n × Vn n)} {s2 : List (S2V n)}
    {gp : List (ℕ × ℕ)} (hOK : certOKGiven gens (oneN n) sets pats reps s2 gp = true)
    (hcov : permCovB n pats = true) (P : (Vn n ≃ₗ[ZMod 3] Vn n) → Prop)
    (hPW : ∀ w ∈ Subgroup.closure (Set.range S), ∀ u, P u → P (w * u * w⁻¹)) :
    ∀ A Mg : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n),
      TestHyp (Subgroup.closure (Set.range S)) (oneN n) A Mg →
      (∀ i j, (i, j) ∈ gp → ∀ (hi : (letAt reps i).2 ⬝ᵥ (letAt reps i).1 = 2)
        (hj : (letAt reps j).2 ⬝ᵥ (letAt reps j).1 = 2),
        refl (letAt reps i).1 (letAt reps i).2 hi ∈ Mg →
        refl (letAt reps j).1 (letAt reps j).2 hj ∈ A →
        P (refl (letAt reps j).1 (letAt reps j).2 hj) →
        refl (letAt reps j).1 (letAt reps j).2 hj ∈ Mg) →
      ∀ r ∈ Mg, IsRefl r → ¬ FixesLine (oneN n) r →
      ∀ t ∈ A, IsRefl t → ¬ FixesLine (oneN n) t → P t → t ∈ Mg := by
  intro A Mg hT hgiven r hr hrR hrx t ht htR htx hPt
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
  exact hT.mem_of_certOKGiven_of hOK hgW hWgen (hT.perm_cover hperm hcov) P hPW hgiven hr hrR
    hrx ht htR htx hPt

theorem closure_a7fS_le_permGroup : Subgroup.closure (Set.range a7fS) ≤ permGroup 7 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  have hne : k.castSucc ≠ k.succ := Fin.castSucc_lt_succ.ne
  refine ⟨Equiv.swap k.castSucc k.succ, ?_⟩
  change permN _ = _
  rw [permN_swap _ _ hne, a7fS, a7f_adj k, letLin_of _ (dot_sub_single_self _ _ hne)]

theorem a7f_given_not_cen : ∀ i j, (i, j) ∈ a7fGiven →
    ∀ (hj : (letAt a7fReps j).2 ⬝ᵥ (letAt a7fReps j).1 = 2),
      ¬ a7fCen (refl (letAt a7fReps j).1 (letAt a7fReps j).2 hj) := by
  intro i j hij hj
  simp only [a7fGiven, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hij
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine not_a7fCen_of 0 ?_
    simp only [refl_apply]
    decide +kernel
  · refine not_a7fCen_of 0 ?_
    simp only [refl_apply]
    decide +kernel

theorem a7f_test_cen : ∀ A Mg : Subgroup (Vn 7 ≃ₗ[ZMod 3] Vn 7),
    TestHyp (Subgroup.closure (Set.range a7fS)) (oneN 7) A Mg →
    ∀ r ∈ Mg, IsRefl r → ¬ FixesLine (oneN 7) r →
    ∀ t ∈ A, IsRefl t → ¬ FixesLine (oneN 7) t → a7fCen t → t ∈ Mg := by
  intro A Mg hT
  refine linTest_perm_of_certOKGiven_of a7fS a7fGens rfl (fun _ => rfl)
    (permGroup_le_of_gens a7fS a7fGens (fun _ => rfl) (by norm_num) a7f_adj)
    a7f_certOK a7f_cov a7fCen (fun w hw u hu => ?_) A Mg hT
    (fun i j hij hi hj _ _ hP => absurd hP (a7f_given_not_cen i j hij hj))
  obtain ⟨σ, rfl⟩ := closure_a7fS_le_permGroup hw
  exact a7fCen_conj σ hu

end CFSG.StandardType.TestLin

end
