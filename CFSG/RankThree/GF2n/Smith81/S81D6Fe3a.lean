module

public import CFSG.RankThree.GF2n.Smith81.S81E7Fe3
public import CFSG.RankThree.GF2n.Smith81.S81D6Basic
public import CFSG.RankThree.GF2n.Smith81.S81E7Lam

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


variable {K : Type} [Field K]

@[expose] def wordTable4 : List (List ℕ) :=
  [[], [3, 4, 5, 6, 2, 3, 4, 5], [3, 4, 5, 6, 1, 3, 4, 5], [4, 5, 6, 2, 1, 3, 4, 5],
   [5, 6, 3, 2, 1, 3, 4, 5], [6, 4, 3, 2, 1, 3, 4, 5], [5, 4, 3, 2, 1, 3, 4, 5], [], [],
   [1, 3, 4, 5, 6, 2, 3, 4, 5], [4, 5, 6, 2, 3, 4, 5], [2, 3, 4, 5, 6, 1, 3, 4, 5],
   [4, 5, 6, 1, 3, 4, 5], [3, 4, 5, 6, 2, 1, 3, 4, 5], [5, 6, 2, 1, 3, 4, 5],
   [4, 5, 6, 3, 2, 1, 3, 4, 5], [6, 3, 2, 1, 3, 4, 5], [5, 6, 4, 3, 2, 1, 3, 4, 5],
   [4, 3, 2, 1, 3, 4, 5], [6, 5, 4, 3, 2, 1, 3, 4, 5], [], [], [1, 3, 4, 5, 6, 2, 1, 3, 4, 5],
   [4, 5, 6, 3, 4, 5], [5, 6, 2, 3, 4, 5], [2, 3, 4, 5, 6, 2, 1, 3, 4, 5], [5, 6, 1, 3, 4, 5],
   [3, 4, 5, 6, 3, 2, 1, 3, 4, 5], [6, 2, 1, 3, 4, 5], [4, 5, 6, 4, 3, 2, 1, 3, 4, 5],
   [3, 2, 1, 3, 4, 5], [5, 6, 5, 4, 3, 2, 1, 3, 4, 5], [], [], [],
   [2, 1, 3, 4, 5, 6, 2, 1, 3, 4, 5], [1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5], [5, 6, 3, 4, 5],
   [6, 2, 3, 4, 5], [2, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5], [6, 1, 3, 4, 5],
   [3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5], [2, 1, 3, 4, 5], [4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5], [], [],
   [], [], [2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5], [1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5], [5, 6, 4, 5],
   [6, 3, 4, 5], [2, 3, 4, 5], [2, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5], [1, 3, 4, 5],
   [3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5], [], [], [], [], [],
   [3, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5], [2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5],
   [1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5], [6, 4, 5], [3, 4, 5],
   [2, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5], [], [], [], [], [], [],
   [3, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5], [2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5], [6, 5],
   [4, 5], [], [], [], [], [], [], [4, 3, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5],
   [3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5], [5], [], [], [], [], [], [],
   [4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5], [], [], [], [], [], [], [],
   [5, 4, 3, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5], [], [], [], [], [], [], [], [], [], [], [],
   [], [], [], [], [], [], [], [], [], [], [], [], [], []]

set_option maxRecDepth 20000 in
theorem wordTable4_correct : ∀ k : Fin 126, ((Tag.rootCertificate .E7).root k) node1 = 0 →
    (∀ i ∈ wordTable4.getD k [], i % 7 ≠ 0) ∧
      applyWord (wordTable4.getD k []) ((Tag.rootCertificate .E7).root k) = theta4 := by
  unfold applyWord wordTable4 letter
  decide +kernel

theorem exists_word_perp_to_theta4 {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) :
    ∃ ω : List ℕ, (∀ i ∈ ω, i % 7 ≠ 0) ∧ applyWord ω β = theta4 := by
  obtain ⟨hR, h0⟩ := perp_iff.1 hβ
  obtain ⟨k, hk, hkβ⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hR
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  have hk126 : k < 126 := by omega
  subst hkβ
  exact ⟨wordTable4.getD k [], (wordTable4_correct ⟨k, hk126⟩ h0).1,
    (wordTable4_correct ⟨k, hk126⟩ h0).2⟩

private theorem reflect_neg_E7 (j : Fin (Tag.rank .E7)) (v : Fin (Tag.rank .E7) → ℤ) :
    reflect .E7 j (-v) = -reflect .E7 j v := by
  have hs : ∑ l, Tag.cartan .E7 j l * (-v) l = -∑ l, Tag.cartan .E7 j l * v l := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => mul_neg _ _
  unfold reflect
  rw [hs, neg_smul]
  abel

theorem applyWord_neg (ω : List ℕ) (v : Fin (Tag.rank .E7) → ℤ) :
    applyWord ω (-v) = -applyWord ω v := by
  induction ω generalizing v with
  | nil => rfl
  | cons i ω ih =>
    show applyWord ω (reflect .E7 (letter i) (-v)) = -applyWord ω (reflect .E7 (letter i) v)
    rw [reflect_neg_E7, ih]

@[expose] def nWord (K : Type) [Field K] : List ℕ → ↥(e7Data_valid.minGroup K)
  | [] => 1
  | i :: ω => nWord K ω * e7Data_valid.nm K (letter i)

theorem nWord_conj_xm [CharP K 2] (ω : List ℕ) : ∀ v : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 v →
    ∀ c : K, nWord K ω * e7Data_valid.xm K v c * (nWord K ω)⁻¹ =
      e7Data_valid.xm K (applyWord ω v) c := by
  induction ω with
  | nil =>
    intro v _ c
    simp [nWord, applyWord]
  | cons i ω ih =>
    intro v hv c
    have hv' : IsRoot .E7 (reflect .E7 (letter i) v) := IsRoot.reflect (letter i) hv
    obtain ⟨σ, hσ, hconj⟩ := e7Data_valid.nm_conj_xm K hv (letter i)
    have hσ1 : σ = 1 := by
      rcases hσ with h | h
      · exact h
      · rw [h]
        exact CharTwo.neg_eq (1 : K)
    have hcj : e7Data_valid.nm K (letter i) * e7Data_valid.xm K v c *
        (e7Data_valid.nm K (letter i))⁻¹ =
        e7Data_valid.xm K (reflect .E7 (letter i) v) c := by
      rw [hconj c, hσ1, one_mul]
    have ih' := ih (reflect .E7 (letter i) v) hv' c
    show (nWord K ω * e7Data_valid.nm K (letter i)) * e7Data_valid.xm K v c *
        (nWord K ω * e7Data_valid.nm K (letter i))⁻¹ =
        e7Data_valid.xm K (applyWord ω (reflect .E7 (letter i) v)) c
    rw [← ih', ← hcj]
    simp only [mul_inv_rev, mul_assoc]

theorem nm_mem_Lam [CharP K 2] {i : Fin (Tag.rank .E7)} (hi : i ≠ ⟨0, by decide⟩) :
    ((e7Data_valid.nm K i : ↥(e7Data_valid.minGroup K)) : (Module.End K (V K))ˣ) ∈ Lam K := by
  have hsP : Pi.single i (1 : ℤ) ∈ Perp :=
    perp_iff.2 ⟨isRoot_single .E7 i, by rw [Pi.single_apply, if_neg (fun h => hi h.symm)]⟩
  have hsN : -Pi.single i (1 : ℤ) ∈ Perp := neg_mem_Perp hsP
  show ((e7Data_valid.xm K (Pi.single i 1) 1 * e7Data_valid.xm K (-Pi.single i 1)
      (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) * e7Data_valid.xm K (Pi.single i 1) 1 :
      ↥(e7Data_valid.minGroup K)) : (Module.End K (V K))ˣ) ∈ Lam K
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact mul_mem (mul_mem (xu_mem_Lam hsP 1) (xu_mem_Lam hsN _)) (xu_mem_Lam hsP 1)

theorem nWord_mem_Lam [CharP K 2] (ω : List ℕ) (hω : ∀ i ∈ ω, i % 7 ≠ 0) :
    ((nWord K ω : ↥(e7Data_valid.minGroup K)) : (Module.End K (V K))ˣ) ∈ Lam K := by
  induction ω with
  | nil => exact one_mem _
  | cons i ω ih =>
    have hi : letter i ≠ ⟨0, by decide⟩ := fun h => hω i (by simp) (congrArg Fin.val h)
    show ((nWord K ω * e7Data_valid.nm K (letter i) : ↥(e7Data_valid.minGroup K)) :
      (Module.End K (V K))ˣ) ∈ Lam K
    rw [Subgroup.coe_mul]
    exact mul_mem (ih fun j hj => hω j (List.mem_cons_of_mem i hj)) (nm_mem_Lam hi)

theorem nWord_mem_closure [CharP K 2] (ω : List ℕ) (hω : ∀ i ∈ ω, i % 7 ≠ 0) :
    nWord K ω ∈ Subgroup.closure {g : ↥(e7Data_valid.minGroup K) |
      ∃ j : Fin (Tag.rank .E7), j ≠ ⟨0, by decide⟩ ∧ g = e7Data_valid.nm K j} := by
  induction ω with
  | nil => exact one_mem _
  | cons i ω ih =>
    have hi : letter i ≠ ⟨0, by decide⟩ := fun h => hω i (by simp) (congrArg Fin.val h)
    show nWord K ω * e7Data_valid.nm K (letter i) ∈ _
    exact mul_mem (ih fun j hj => hω j (List.mem_cons_of_mem i hj))
      (Subgroup.subset_closure ⟨letter i, hi, rfl⟩)

theorem exists_conj_to_theta4_Lam [CharP K 2] {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) :
    ∃ g : ↥(e7Data_valid.minGroup K),
      ((g : ↥(e7Data_valid.minGroup K)) : (Module.End K (V K))ˣ) ∈ Lam K ∧
      g ∈ Subgroup.closure {g : ↥(e7Data_valid.minGroup K) |
        ∃ j : Fin (Tag.rank .E7), j ≠ ⟨0, by decide⟩ ∧ g = e7Data_valid.nm K j} ∧
      ∀ c : K, g * e7Data_valid.xm K β c * g⁻¹ = e7Data_valid.xm K theta4 c ∧
        g * e7Data_valid.xm K (-β) c * g⁻¹ = e7Data_valid.xm K (-theta4) c := by
  obtain ⟨ω, hω, hωβ⟩ := exists_word_perp_to_theta4 hβ
  have hR : IsRoot .E7 β := (perp_iff.1 hβ).1
  refine ⟨nWord K ω, nWord_mem_Lam ω hω, nWord_mem_closure ω hω, fun c => ⟨?_, ?_⟩⟩
  · have h := nWord_conj_xm ω β hR c
    rw [hωβ] at h
    exact h
  · have h := nWord_conj_xm ω (-β) (isRoot_neg hR) c
    rw [applyWord_neg, hωβ] at h
    exact h

end CFSG.RankThree.GF2n.Smith81.D6Spin
