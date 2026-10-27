module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08TestCert
public import CFSG.LocalAnalysis.StandardType.GGQ2S08PermLin

public section

namespace CFSG.StandardType.TestLin

open Matrix

variable {n : ℕ}

@[expose] def sortedVec (n a b : ℕ) : Vn n :=
  fun i => if i.val < a then 0 else if i.val < a + b then 1 else 2

private theorem mem_iff_lt_card_of_downward (D : Finset (Fin n))
    (hD : ∀ i j : Fin n, i ≤ j → j ∈ D → i ∈ D) (i : Fin n) : i ∈ D ↔ i.val < D.card := by
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ D := fun j hj => hD j i (Finset.mem_Iic.mp hj) hi
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    omega
  · intro hlt
    by_contra hi
    have hsub : D ⊆ Finset.Iio i := by
      intro j hj
      rw [Finset.mem_Iio]
      by_contra hji
      exact hi (hD i j (not_lt.mp hji) hj)
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    omega

theorem monotone_eq_sortedVec (c : Vn n) (hc : Monotone fun i => (c i).val) :
    ∃ a b, a + b ≤ n ∧ c = sortedVec n a b := by
  classical
  have key : ∀ t : ZMod 3, (t.val = 0 → t = 0) ∧ (t.val ≤ 1 → t ≠ 0 → t = 1) ∧
      (¬ t.val ≤ 1 → t = 2) ∧ (t = 0 → t.val = 0) := by decide
  let D0 : Finset (Fin n) := Finset.univ.filter fun i => c i = 0
  let D1 : Finset (Fin n) := Finset.univ.filter fun i => (c i).val ≤ 1
  have hD0 : ∀ i j : Fin n, i ≤ j → j ∈ D0 → i ∈ D0 := by
    intro i j hij hj
    simp only [D0, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    have h1 : (c i).val ≤ (c j).val := hc hij
    rw [(key (c j)).2.2.2 hj] at h1
    exact (key (c i)).1 (Nat.le_zero.mp h1)
  have hD1 : ∀ i j : Fin n, i ≤ j → j ∈ D1 → i ∈ D1 := by
    intro i j hij hj
    simp only [D1, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact (show (c i).val ≤ (c j).val from hc hij).trans hj
  have hsub : D0 ⊆ D1 := by
    intro i hi
    simp only [D0, D1, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [(key (c i)).2.2.2 hi]
    exact Nat.zero_le 1
  have hle : D0.card ≤ D1.card := Finset.card_le_card hsub
  have hD1n : D1.card ≤ n := (Finset.card_le_univ D1).trans (Fintype.card_fin n).le
  refine ⟨D0.card, D1.card - D0.card, by omega, funext fun i => ?_⟩
  have h0 : c i = 0 ↔ i.val < D0.card := by
    rw [← mem_iff_lt_card_of_downward D0 hD0 i]
    simp [D0]
  have h1 : (c i).val ≤ 1 ↔ i.val < D1.card := by
    rw [← mem_iff_lt_card_of_downward D1 hD1 i]
    simp [D1]
  unfold sortedVec
  by_cases hi0 : i.val < D0.card
  · rw [if_pos hi0]
    exact h0.mpr hi0
  · rw [if_neg hi0]
    by_cases hi1 : i.val < D0.card + (D1.card - D0.card)
    · rw [if_pos hi1]
      exact (key (c i)).2.1 (h1.mpr (by omega)) fun h => hi0 (h0.mp h)
    · rw [if_neg hi1]
      exact (key (c i)).2.2.1 fun h => hi1 (by have := h1.mp h; omega)

@[expose] def f3 (f : ZMod 3 × ZMod 3 × ZMod 3) (t : ZMod 3) : ZMod 3 :=
  if t = 0 then f.1 else if t = 1 then f.2.1 else f.2.2

@[expose] def triples : List (ZMod 3 × ZMod 3 × ZMod 3) :=
  [0, 1, 2].flatMap fun a => [0, 1, 2].flatMap fun b => [0, 1, 2].map fun c => (a, b, c)

theorem mem_triples (f : ZMod 3 × ZMod 3 × ZMod 3) : f ∈ triples := by
  revert f
  decide

theorem f3_eq (f : ZMod 3 → ZMod 3) (t : ZMod 3) : f3 (f 0, f 1, f 2) t = f t := by
  rcases (by decide : ∀ t : ZMod 3, t = 0 ∨ t = 1 ∨ t = 2) t with rfl | rfl | rfl <;> rfl

@[expose] def permCondB (c a : Vn n) : Bool :=
  decide (a ⬝ᵥ c = 2) && decide (a ⬝ᵥ oneN n ≠ 0) && decide (∀ μ : ZMod 3, c ≠ μ • oneN n) &&
    decide (∀ i j : Fin n, a i = a j ↔ c i = c j)

@[expose] def permCovB (n : ℕ) (pats : List ((Vn n × Vn n) × PatV n)) : Bool :=
  (List.range (n + 1)).all fun a => (List.range (n + 1 - a)).all fun b =>
    triples.all fun f =>
      !permCondB (sortedVec n a b) (fun i => f3 f (sortedVec n a b i)) ||
        decide ((sortedVec n a b, fun i => f3 f (sortedVec n a b i)) ∈ pats.map Prod.fst)

variable {W A M : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)}

theorem TestHyp.perm_cover [NeZero n] (hW : permGroup n ≤ W) (hT : TestHyp W (oneN n) A M)
    {pats : List ((Vn n × Vn n) × PatV n)} (hcov : permCovB n pats = true) :
    ∀ u ∈ A, IsRefl u → ¬ FixesLine (oneN n) u → ∃ w ∈ W, ∃ p ∈ pats,
      ∃ h : p.1.2 ⬝ᵥ p.1.1 = 2, w * u * w⁻¹ = refl p.1.1 p.1.2 h := by
  intro u hu huR hux
  obtain ⟨σ, c, f, hmono, hinj, hdot, hconst, h, hconj⟩ := hT.exists_sorted hW hu huR hux
  obtain ⟨a, b, hab, rfl⟩ := monotone_eq_sortedVec c hmono
  have hfc : (fun i => f3 (f 0, f 1, f 2) (sortedVec n a b i)) = f ∘ sortedVec n a b :=
    funext fun i => f3_eq f _
  have hcond : permCondB (sortedVec n a b) (f ∘ sortedVec n a b) = true := by
    simp only [permCondB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨h, hdot⟩, hconst⟩, hinj⟩
  have hc := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hcov a
    (List.mem_range.mpr (by omega))) b (List.mem_range.mpr (by omega))) _
    (mem_triples (f 0, f 1, f 2))
  rw [hfc, hcond, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc
  obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hc
  have hp2 : p.1.2 ⬝ᵥ p.1.1 = 2 := by
    rw [hpeq]
    exact h
  refine ⟨permN σ, hW ⟨σ, rfl⟩, p, hp, hp2, ?_⟩
  rw [hconj]
  exact refl_congr (congrArg Prod.fst hpeq).symm (congrArg Prod.snd hpeq).symm h hp2

theorem linTest_perm_of_certOK [NeZero n] {ℓ : ℕ} (S : Fin ℓ → (Vn n ≃ₗ[ZMod 3] Vn n))
    (gens : List (Vn n × Vn n)) (hlen : gens.length = ℓ)
    (hS : ∀ k : Fin ℓ, S k = letLin (letAt gens k))
    (hperm : permGroup n ≤ Subgroup.closure (Set.range S)) {sets : List (List (Vn n))}
    {pats : List ((Vn n × Vn n) × PatV n)} {reps : List (Vn n × Vn n)} {s2 : List (S2V n)}
    (hOK : certOK gens (oneN n) sets pats reps s2 = true) (hcov : permCovB n pats = true) :
    ∀ A Mg : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n),
      TestHyp (Subgroup.closure (Set.range S)) (oneN n) A Mg →
      ∀ r ∈ Mg, IsRefl r → ¬ FixesLine (oneN n) r →
      ∀ t ∈ A, IsRefl t → ¬ FixesLine (oneN n) t → t ∈ Mg := by
  intro A Mg hT r hr hrR hrx t ht htR htx
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
  exact hT.mem_of_certOK hOK hgW hWgen (hT.perm_cover hperm hcov) hr hrR hrx ht htR htx

theorem permGroup_le_of_gens {m ℓ : ℕ} (S : Fin ℓ → (Vn (m + 1) ≃ₗ[ZMod 3] Vn (m + 1)))
    (gens : List (Vn (m + 1) × Vn (m + 1))) (hS : ∀ k : Fin ℓ, S k = letLin (letAt gens k))
    (hm : m ≤ ℓ) (hadj : ∀ i : Fin m, letAt gens i =
      (Pi.single i.castSucc 1 - Pi.single i.succ 1, Pi.single i.castSucc 1 - Pi.single i.succ 1)) :
    permGroup (m + 1) ≤ Subgroup.closure (Set.range S) := by
  refine permGroup_le_of_adjacent fun i => ?_
  have hne : i.castSucc ≠ i.succ := Fin.castSucc_lt_succ.ne
  have h := letLin_of (Pi.single i.castSucc (1 : ZMod 3) - Pi.single i.succ 1,
    Pi.single i.castSucc (1 : ZMod 3) - Pi.single i.succ 1) (dot_sub_single_self _ _ hne)
  have hk : S ⟨i, by omega⟩ = refl (Pi.single i.castSucc 1 - Pi.single i.succ 1)
      (Pi.single i.castSucc 1 - Pi.single i.succ 1) (dot_sub_single_self _ _ hne) := by
    rw [hS]
    change letLin (letAt gens i) = _
    rw [hadj i]
    exact h
  rw [permN_swap _ _ hne, ← hk]
  exact Subgroup.subset_closure (Set.mem_range_self _)

end CFSG.StandardType.TestLin

end
