module

public import CFSG.LocalAnalysis.StandardType.PhanEMatchShape
public import CFSG.LocalAnalysis.StandardType.PhanEMatchDiagram

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Match

open CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.PhanCode

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}

theorem exists_code_matches_rank (hA : SLDiagram A) {J I : Set (Fin n)} (hIJ : I ⊆ J)
    {π : Fin n → Fin n} (hπI : ∀ i ∈ I, π i ∈ I) (hππ : ∀ i ∈ I, π (π i) = i)
    (hπA : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (A (π i) (π j) ≠ 0 ↔ A i j ≠ 0))
    (hJ : J.ncard = 2 ∨ J.ncard = 3) :
    ∃ (c : PhanCode) (σ : Fin c.rank → Fin n), (c.rank = 2 ∧ Shape2 c ∨ c.rank = 3 ∧ Shape3 c) ∧
      c.rank = J.ncard ∧ Function.Injective σ ∧ Set.range σ = J ∧
      (∀ i j : Fin c.rank, i ≠ j → A (σ i) (σ j) = if c.coxN i j = 3 then -1 else 0) ∧
      (∀ i : Fin c.rank, σ i ∈ I ↔ c.coreN i = true) ∧
      ∀ i : Fin c.rank, σ i ∈ I → ∃ j : Fin c.rank, j.val = c.permN i ∧ σ j = π (σ i) := by
  obtain ⟨c, σ, h3, h2, hr, hinj, hrange, hadj, hcore, hperm⟩ :=
    exists_code_matches hA hIJ hπI hππ hπA hJ
  refine ⟨c, fun i => σ (Fin.cast hr i), ?_, hr, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hJ with hJ | hJ
    · exact Or.inl ⟨hr.trans hJ, Shape2.of_mem (h2 hJ)⟩
    · exact Or.inr ⟨hr.trans hJ, Shape3.of_mem (h3 hJ)⟩
  · exact hinj.comp (Fin.cast_injective hr)
  · have hsurj : Function.Surjective (Fin.cast hr) := fun j =>
      ⟨Fin.cast hr.symm j, Fin.ext (by simp)⟩
    change Set.range (σ ∘ Fin.cast hr) = J
    rw [Set.range_comp, hsurj.range_eq, Set.image_univ, hrange]
  · intro i j hij
    have hne : Fin.cast hr i ≠ Fin.cast hr j := fun h => hij (Fin.cast_injective hr h)
    rw [hadj (Fin.cast hr i) (Fin.cast hr j) hne]
    simp
  · intro i
    rw [hcore (Fin.cast hr i)]
    simp
  · intro i hi
    obtain ⟨j, hjval, hjσ⟩ := hperm (Fin.cast hr i) hi
    refine ⟨Fin.cast hr.symm j, ?_, ?_⟩
    · rw [Fin.val_cast, hjval]
      simp
    · dsimp only
      rw [show Fin.cast hr (Fin.cast hr.symm j) = j from Fin.ext (by simp)]
      exact hjσ

theorem slice_core_left {a b : PhanCode} {I : Set (Fin n)} {σ : Fin (a.rank + b.rank) → Fin n}
    (hcore : ∀ i : Fin (a.rank + b.rank), σ i ∈ I ↔ (prod a b).coreN i = true) (k : Fin a.rank) :
    σ (Fin.castAdd b.rank k) ∈ I ↔ a.coreN k = true := by
  rw [hcore (Fin.castAdd b.rank k), Fin.val_castAdd, coreN_prod_left a b k.isLt]

theorem slice_core_right {a b : PhanCode} {I : Set (Fin n)} {σ : Fin (a.rank + b.rank) → Fin n}
    (hcore : ∀ i : Fin (a.rank + b.rank), σ i ∈ I ↔ (prod a b).coreN i = true) (k : Fin b.rank) :
    σ (Fin.natAdd a.rank k) ∈ I ↔ b.coreN k = true := by
  rw [hcore (Fin.natAdd a.rank k), Fin.val_natAdd, coreN_prod_right a b k.val]

theorem slice_perm_left {a b : PhanCode} {I : Set (Fin n)} {π : Fin n → Fin n}
    {σ : Fin (a.rank + b.rank) → Fin n}
    (hperm : ∀ i : Fin (a.rank + b.rank), σ i ∈ I →
      ∃ j : Fin (a.rank + b.rank), j.val = (prod a b).permN i ∧ σ j = π (σ i))
    (k : Fin a.rank) (hk : σ (Fin.castAdd b.rank k) ∈ I) :
    ∃ k' : Fin a.rank, k'.val = a.permN k ∧
      σ (Fin.castAdd b.rank k') = π (σ (Fin.castAdd b.rank k)) := by
  obtain ⟨j, hjval, hjσ⟩ := hperm (Fin.castAdd b.rank k) hk
  rw [Fin.val_castAdd, permN_prod_left a b k.isLt] at hjval
  refine ⟨⟨a.permN k, permN_lt a k.isLt⟩, rfl, ?_⟩
  have hj_eq : j = Fin.castAdd b.rank (⟨a.permN k, permN_lt a k.isLt⟩ : Fin a.rank) := by
    apply Fin.ext
    rw [Fin.val_castAdd]
    exact hjval
  rw [← hj_eq]
  exact hjσ

theorem slice_perm_right {a b : PhanCode} {I : Set (Fin n)} {π : Fin n → Fin n}
    {σ : Fin (a.rank + b.rank) → Fin n}
    (hperm : ∀ i : Fin (a.rank + b.rank), σ i ∈ I →
      ∃ j : Fin (a.rank + b.rank), j.val = (prod a b).permN i ∧ σ j = π (σ i))
    (k : Fin b.rank) (hk : σ (Fin.natAdd a.rank k) ∈ I) :
    ∃ k' : Fin b.rank, k'.val = b.permN k ∧
      σ (Fin.natAdd a.rank k') = π (σ (Fin.natAdd a.rank k)) := by
  obtain ⟨j, hjval, hjσ⟩ := hperm (Fin.natAdd a.rank k) hk
  rw [Fin.val_natAdd, permN_prod_right a b k.val] at hjval
  refine ⟨⟨b.permN k, permN_lt b k.isLt⟩, rfl, ?_⟩
  have hj_eq : j = Fin.natAdd a.rank (⟨b.permN k, permN_lt b k.isLt⟩ : Fin b.rank) := by
    apply Fin.ext
    rw [Fin.val_natAdd]
    exact hjval
  rw [← hj_eq]
  exact hjσ

theorem slice_adj_left {a b : PhanCode} {σ : Fin (a.rank + b.rank) → Fin n}
    (hadj : ∀ i j : Fin (a.rank + b.rank), i ≠ j →
      A (σ i) (σ j) = if (prod a b).coxN i j = 3 then -1 else 0)
    (i j : Fin a.rank) (hij : i ≠ j) :
    A (σ (Fin.castAdd b.rank i)) (σ (Fin.castAdd b.rank j)) =
      if a.coxN i j = 3 then -1 else 0 := by
  have hne : Fin.castAdd b.rank i ≠ Fin.castAdd b.rank j :=
    fun h => hij (Fin.castAdd_injective a.rank b.rank h)
  rw [hadj (Fin.castAdd b.rank i) (Fin.castAdd b.rank j) hne, Fin.val_castAdd, Fin.val_castAdd,
    coxN_prod_left a b i.isLt j.isLt]

theorem slice_adj_cross {a b : PhanCode} {σ : Fin (a.rank + b.rank) → Fin n}
    (hadj : ∀ i j : Fin (a.rank + b.rank), i ≠ j →
      A (σ i) (σ j) = if (prod a b).coxN i j = 3 then -1 else 0)
    (i : Fin a.rank) (j : Fin b.rank) :
    A (σ (Fin.castAdd b.rank i)) (σ (Fin.natAdd a.rank j)) = 0 := by
  have hne : Fin.castAdd b.rank i ≠ Fin.natAdd a.rank j := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
    omega
  rw [hadj (Fin.castAdd b.rank i) (Fin.natAdd a.rank j) hne, Fin.val_castAdd, Fin.val_natAdd,
    coxN_prod_cross a b i.isLt]
  simp

end CFSG.ClassicalInvolution.Phan.PhanE.Match

end
