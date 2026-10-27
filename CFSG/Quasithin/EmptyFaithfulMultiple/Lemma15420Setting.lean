module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Factors

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Perm

variable {G : Type*} [Group G]

theorem map_conj_mul (x y : G) (A : Subgroup G) :
    A.map (MulAut.conj (x * y)).toMonoidHom =
      (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext a
  simp [mul_assoc]

theorem map_conj_inv_map_conj (x : G) (A : Subgroup G) :
    (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = A := by
  rw [← map_conj_mul, inv_mul_cancel]
  ext a
  simp

theorem map_conj_injective (x : G) {A B : Subgroup G}
    (h : A.map (MulAut.conj x).toMonoidHom = B.map (MulAut.conj x).toMonoidHom) : A = B := by
  rw [← map_conj_inv_map_conj x A, h, map_conj_inv_map_conj]

@[expose] def PermutesPair (g : G) (A B : Subgroup G) : Prop :=
  (A.map (MulAut.conj g).toMonoidHom = A ∧ B.map (MulAut.conj g).toMonoidHom = B) ∨
    (A.map (MulAut.conj g).toMonoidHom = B ∧ B.map (MulAut.conj g).toMonoidHom = A)

theorem PermutesPair.mul {A B : Subgroup G} {x y : G} (hx : PermutesPair x A B)
    (hy : PermutesPair y A B) : PermutesPair (x * y) A B := by
  unfold PermutesPair at hx hy ⊢
  rw [map_conj_mul, map_conj_mul]
  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> rcases hx with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rw [h3, h4] <;> first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩

theorem PermutesPair.inv {A B : Subgroup G} {x : G} (hx : PermutesPair x A B) :
    PermutesPair x⁻¹ A B := by
  unfold PermutesPair at hx ⊢
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    constructor
    · conv_lhs => rw [← h1]
      exact map_conj_inv_map_conj x A
    · conv_lhs => rw [← h2]
      exact map_conj_inv_map_conj x B
  · right
    constructor
    · conv_lhs => rw [← h2]
      exact map_conj_inv_map_conj x B
    · conv_lhs => rw [← h1]
      exact map_conj_inv_map_conj x A

theorem PermutesPair.fix_mul_iff {A B : Subgroup G} (hAB : A ≠ B) {x y : G}
    (hx : PermutesPair x A B) (hy : PermutesPair y A B) :
    A.map (MulAut.conj (x * y)).toMonoidHom = A ↔
      (A.map (MulAut.conj x).toMonoidHom = A ↔ A.map (MulAut.conj y).toMonoidHom = A) := by
  rw [map_conj_mul]
  unfold PermutesPair at hx hy
  rcases hy with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1]
    simp
  · rw [h1]
    rcases hx with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h4, h3] <;> simp [hAB.symm]

theorem map_conj_one (A : Subgroup G) : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  ext a
  simp

theorem PermutesPair.commutator_fix {A B : Subgroup G} (hAB : A ≠ B) {x y : G}
    (hx : PermutesPair x A B) (hy : PermutesPair y A B) :
    A.map (MulAut.conj ⁅x, y⁆).toMonoidHom = A := by
  have hxi := hx.inv
  have hyi := hy.inv
  have hinv : ∀ {z : G}, PermutesPair z A B →
      (A.map (MulAut.conj z⁻¹).toMonoidHom = A ↔ A.map (MulAut.conj z).toMonoidHom = A) := by
    intro z hz
    have := PermutesPair.fix_mul_iff hAB hz hz.inv
    rw [mul_inv_cancel, map_conj_one] at this
    exact (this.mp rfl).symm
  have h1 := PermutesPair.fix_mul_iff hAB hx hy
  have h2 := PermutesPair.fix_mul_iff hAB (hx.mul hy) hxi
  have h3 := PermutesPair.fix_mul_iff hAB ((hx.mul hy).mul hxi) hyi
  rw [commutatorElement_def, h3, h2, h1, hinv hx, hinv hy]
  tauto

theorem mem_normalizer_iff_map_conj {H : Subgroup G} {g : G} :
    g ∈ Subgroup.normalizer (H : Set G) ↔ H.map (MulAut.conj g).toMonoidHom = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq

theorem PermutesPair.mem_normalizer_iff {A B : Subgroup G} (hAB : A ≠ B) {g : G}
    (hg : PermutesPair g A B) :
    g ∈ Subgroup.normalizer (A : Set G) ↔ g ∈ Subgroup.normalizer (B : Set G) := by
  rw [mem_normalizer_iff_map_conj, mem_normalizer_iff_map_conj]
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · rw [h1, h2]
    exact ⟨fun h => absurd h.symm hAB, fun h => absurd h hAB⟩

end Perm

section SixTwoPerm

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

omit [Finite G] in
theorem IsSixTwoData.ne {M Y Y₁ Y₂ : Subgroup G} (h : IsSixTwoData T M Y Y₁ Y₂) : Y₁ ≠ Y₂ := by
  intro e
  obtain ⟨-, -, -, -, -, -, hinf, hc₁, -⟩ := h
  rw [e, inf_idem] at hinf
  rw [e, hinf, Subgroup.card_bot] at hc₁
  omega

theorem sixTwo_permutesPair (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    {M Y Y₁ Y₂ : Subgroup G} (hM : InM T M) (hY : IsYFamily T Y) (hYM : Y ≤ M)
    (hd : IsSixTwoData T M Y Y₁ Y₂) {g : G} (hg : g ∈ M) : PermutesPair g Y₁ Y₂ := by
  obtain ⟨hMY, -⟩ := (h12 M hM).2 Y hY hYM
  have hne := hd.ne
  have hV := isElemAbelian_VZ_of_inM hyp hM
  have hYV : Y ≤ Subgroup.normalizer (VZ T M : Set G) :=
    hYM.trans (le_normalizer_conjClosure _ _)
  have hgV : g ∈ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _ hg
  have hgY : g ∈ Subgroup.normalizer (Y : Set G) := hMY hg
  obtain ⟨hYeq, hO₁, hO₂, hi₁, hi₂, -, hinf, hc₁, hc₂, -, -, -, -, ⟨t, -, ht₂⟩, -, hN₁, hN₂⟩ := hd
  have hcard : Nat.card Y₂ = Nat.card Y₁ := by rw [ht₂, card_map_mulEquiv]
  have h1 := map_conj_eq_or_eq hV hYV hYeq hO₁ hO₂ hi₁ hi₂ hinf hc₁ hc₂ hN₁ hN₂ hcard hgY hgV
  have h2 := map_conj_eq_or_eq hV hYV (hYeq.trans (sup_comm _ _)) hO₂ hO₁ hi₂ hi₁
    ((inf_comm _ _).trans hinf) hc₂ hc₁ hN₂ hN₁ hcard.symm hgY hgV
  have hinj : Y₁.map (MulAut.conj g).toMonoidHom ≠ Y₂.map (MulAut.conj g).toMonoidHom :=
    fun h => hne (map_conj_injective g h)
  unfold PermutesPair
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hinj
  · exact absurd (h1.trans h2.symm) hinj
  · exact Or.inr ⟨h1, h2⟩

end SixTwoPerm

namespace Setting15419

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

theorem permutesX (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (s : Setting15419 G T) {g : G} (hg : g ∈ s.M₁) : PermutesPair g s.X₁ s.X₂ :=
  sixTwo_permutesPair hyp h12 s.inM₁ s.famX s.le_X s.dataX hg

theorem permutesY (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (s : Setting15419 G T) {g : G} (hg : g ∈ s.M₂) : PermutesPair g s.Y₁ s.Y₂ :=
  sixTwo_permutesPair hyp h12 s.inM₂ s.famY s.le_Y s.dataY hg

omit [Finite G] in
theorem baum_le_T₀ (s : Setting15419 G T) : baum T ≤ s.T₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSY, -⟩ := s.dataY
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSX, -⟩ := s.dataX
  exact le_inf (le_inf (inf_le_left) hSY) hSX

omit [Finite G] in
theorem T₀_le (s : Setting15419 G T) : s.T₀ ≤ T := inf_le_left.trans inf_le_left

theorem commutator_le_T₀ (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (s : Setting15419 G T) : ⁅T, T⁆ ≤ s.T₀ := by
  have hTM₁ : T ≤ s.M₁ := s.inM₁.2
  have hTM₂ : T ≤ s.M₂ := s.inM₂.2
  rw [Subgroup.commutator_le]
  intro u hu v hv
  have h1 : ⁅u, v⁆ ∈ T := by
    rw [commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem hu hv) (T.inv_mem hu)) (T.inv_mem hv)
  have h2 : ⁅u, v⁆ ∈ Subgroup.normalizer (s.Y₁ : Set G) := by
    rw [mem_normalizer_iff_map_conj]
    exact PermutesPair.commutator_fix s.dataY.ne (s.permutesY hyp h12 (hTM₂ hu))
      (s.permutesY hyp h12 (hTM₂ hv))
  have h3 : ⁅u, v⁆ ∈ Subgroup.normalizer (s.X₁ : Set G) := by
    rw [mem_normalizer_iff_map_conj]
    exact PermutesPair.commutator_fix s.dataX.ne (s.permutesX hyp h12 (hTM₁ hu))
      (s.permutesX hyp h12 (hTM₁ hv))
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨h1, h2⟩, h3⟩

theorem conj_choice₁ (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (s : Setting15419 G T) {g : G} (hg : g ∈ s.M₁) :
    s.L₁.map (MulAut.conj g).toMonoidHom = s.X₁ ∨ s.L₁.map (MulAut.conj g).toMonoidHom = s.X₂ := by
  rcases s.choice₁ with h | h <;> rw [h] <;>
    rcases s.permutesX hyp h12 hg with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    first
    | (rw [h1]; first | exact Or.inl rfl | exact Or.inr rfl)
    | (rw [h2]; first | exact Or.inl rfl | exact Or.inr rfl)

theorem conj_choice₂ (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (s : Setting15419 G T) {g : G} (hg : g ∈ s.M₂) :
    s.L₂.map (MulAut.conj g).toMonoidHom = s.Y₁ ∨ s.L₂.map (MulAut.conj g).toMonoidHom = s.Y₂ := by
  rcases s.choice₂ with h | h <;> rw [h] <;>
    rcases s.permutesY hyp h12 hg with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    first
    | (rw [h1]; first | exact Or.inl rfl | exact Or.inr rfl)
    | (rw [h2]; first | exact Or.inl rfl | exact Or.inr rfl)

@[expose] def conjL (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (s : Setting15419 G T) (g : G) (hg : g ∈ s.M₁ ⊓ s.M₂) : Setting15419 G T where
  M₁ := s.M₁
  M₂ := s.M₂
  X := s.X
  Y := s.Y
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  L₁ := s.L₁.map (MulAut.conj g).toMonoidHom
  L₂ := s.L₂.map (MulAut.conj g).toMonoidHom
  inM₁ := s.inM₁
  inM₂ := s.inM₂
  ne := s.ne
  famX := s.famX
  le_X := s.le_X
  famY := s.famY
  le_Y := s.le_Y
  dataX := s.dataX
  dataY := s.dataY
  choice₁ := s.conj_choice₁ hyp h12 hg.1
  choice₂ := s.conj_choice₂ hyp h12 hg.2

theorem conjL_I (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (s : Setting15419 G T) (g : G) (hg : g ∈ s.M₁ ⊓ s.M₂)
    (hgT : g ∈ Subgroup.normalizer (s.T₀ : Set G)) :
    (s.conjL hyp h12 g hg).I = s.I.map (MulAut.conj g).toMonoidHom := by
  have hT := map_conj_eq_of_mem_normalizer hgT
  simp only [I, G₁, G₂, Subgroup.map_sup, hT]
  rfl

@[expose] def swap (s : Setting15419 G T) : Setting15419 G T where
  M₁ := s.M₂
  M₂ := s.M₁
  X := s.Y
  Y := s.X
  X₁ := s.Y₁
  X₂ := s.Y₂
  Y₁ := s.X₁
  Y₂ := s.X₂
  L₁ := s.L₂
  L₂ := s.L₁
  inM₁ := s.inM₂
  inM₂ := s.inM₁
  ne := s.ne.symm
  famX := s.famY
  le_X := s.le_Y
  famY := s.famX
  le_Y := s.le_X
  dataX := s.dataY
  dataY := s.dataX
  choice₁ := s.choice₂
  choice₂ := s.choice₁

omit [Finite G] in
theorem swap_T₀ (s : Setting15419 G T) : s.swap.T₀ = s.T₀ := by
  simp only [T₀, swap]
  exact inf_right_comm _ _ _

omit [Finite G] in
theorem swap_I (s : Setting15419 G T) : s.swap.I = s.I := by
  simp only [I, G₁, G₂, swap_T₀]
  simp only [swap]
  exact sup_comm _ _

end Setting15419

end CFSG.Quasithin.EmptyFaithfulMultiple
