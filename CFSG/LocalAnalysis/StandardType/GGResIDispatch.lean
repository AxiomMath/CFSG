module

public import CFSG.LocalAnalysis.StandardType.GGResIClassify

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure GGResIHyp (p : ℕ) [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] (b : Λ)
    (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ) (MK : CoxeterMatrix (Option {i : Λ // i ≠ b}))
    (CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (g : Option Λ → (V ≃ₗ[ZMod p] V)) (h : Option Λ → V)
    (α : Option Λ → Module.Dual (ZMod p) V) (x : V) : Prop where
  hp2 : p ≠ 2
  hWL : GGIsWeylMatrix ML
  hCL : GGIntCartan ML CL
  hWK : GGIsWeylMatrix MK
  hCK : GGIntCartan MK CK
  hconn : GGDeletedConnected ML b
  hnf : ¬ GGResIForkShape b CL CK
  hg : ∀ o w, g o w = w - α o w • h o
  hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p)
  hK : ∀ o o' : Option {i : Λ // i ≠ b},
    α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p)
  hind : LinearIndependent (ZMod p) h
  hspan : Submodule.span (ZMod p) (Set.range h) = ⊤
  hxL : ∀ i : Λ, α (some i) x = 0
  hfix : ∀ w : V, (∀ i : Λ, α (some i) w = 0) → w ∈ Submodule.span (ZMod p) {x}
  hx0 : x ≠ 0

section Checks

variable {n : ℕ}

@[expose] def ggKmatI (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i = ib then (if j = ib then 2 else if j = ic then e₁ else 0)
    else if j = ib then (if i = ic then e₂ else 0) else C i j

@[expose] def ggVecOK (A : Matrix (Fin n) (Fin n) ℤ) (u : List ℕ) : Bool :=
  (List.finRange n).any (fun i => u.getD i.val 0 != 0) &&
    (List.finRange n).all fun i => u.getD i.val 0 == 0 ||
      decide (∑ j : Fin n, A i j * (u.getD j.val 0 : ℤ) ≤ 0)

@[expose] def ggForkB (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ) : Bool :=
  decide (e₁ = -1) && decide (e₂ = -1) && (List.finRange n).all fun i => decide (i = ib) ||
    (decide (C ib i = if i = ic then -1 else 0) && decide (C i ib = if i = ic then -1 else 0))

@[expose] def ggCandB (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ)
    (shapes : List (Fin n × ℤ × ℤ)) (vecs : List (Fin n × ℤ × ℤ × List ℕ)) : Bool :=
  decide ((ic, e₁, e₂) ∈ shapes) || ggForkB C ib ic e₁ e₂ ||
    vecs.any fun w => decide (w.1 = ic) && decide (w.2.1 = e₁) && decide (w.2.2.1 = e₂) &&
      ggVecOK (ggKmatI C ib ic e₁ e₂) w.2.2.2

@[expose] def ggCycleAdj (C : Matrix (Fin n) (Fin n) ℤ) (ib j₁ j₂ i j : Fin n) : Bool :=
  if i = ib then decide (j = j₁) || decide (j = j₂)
  else if j = ib then decide (i = j₁) || decide (i = j₂) else decide (C i j ≠ 0)

theorem ggCycleAdj_spec (C : Matrix (Fin n) (Fin n) ℤ) (ib j₁ j₂ i j : Fin n) :
    ggCycleAdj C ib j₁ j₂ i j = true ↔ (i = ib ∧ (j = j₁ ∨ j = j₂)) ∨
      (i ≠ ib ∧ j = ib ∧ (i = j₁ ∨ i = j₂)) ∨ (i ≠ ib ∧ j ≠ ib ∧ C i j ≠ 0) := by
  by_cases hi : i = ib <;> by_cases hj : j = ib <;> simp [ggCycleAdj, hi, hj]

@[expose] def ggCycleOK (C : Matrix (Fin n) (Fin n) ℤ) (ib j₁ j₂ : Fin n) (S : List (Fin n)) :
    Prop :=
  ∀ i ∈ (ib :: S).toFinset,
    2 ≤ ((ib :: S).toFinset.filter fun j => j ≠ i ∧ ggCycleAdj C ib j₁ j₂ i j = true).card

instance (C : Matrix (Fin n) (Fin n) ℤ) (ib j₁ j₂ : Fin n) (S : List (Fin n)) :
    Decidable (ggCycleOK C ib j₁ j₂ S) := by
  unfold ggCycleOK
  infer_instance

end Checks

@[expose] def ggResIKIdx {Λ : Type} {b : Λ} {n : ℕ} (e : Fin n ≃ Λ) {ib : Fin n}
    (hib : e ib = b) : Fin n ≃ Option {i : Λ // i ≠ b} where
  toFun j := if hj : j = ib then none
    else some ⟨e j, fun he => hj (e.injective (he.trans hib.symm))⟩
  invFun o := match o with
    | none => ib
    | some l => e.symm l.val
  left_inv j := by
    by_cases hj : j = ib
    · simp [hj]
    · simp [hj]
  right_inv o := by
    cases o with
    | none => simp
    | some l =>
      have : e.symm l.val ≠ ib := fun h => l.2 (by
        have := congrArg e h
        rwa [e.apply_symm_apply, hib] at this)
      simp [this]

theorem ggResIKIdx_ib {Λ : Type} {b : Λ} {n : ℕ} (e : Fin n ≃ Λ) {ib : Fin n} (hib : e ib = b) :
    ggResIKIdx e hib ib = none := by
  simp [ggResIKIdx]

theorem ggResIKIdx_ne {Λ : Type} {b : Λ} {n : ℕ} (e : Fin n ≃ Λ) {ib : Fin n} (hib : e ib = b)
    {j : Fin n} (hj : j ≠ ib) :
    ggResIKIdx e hib j = some ⟨e j, fun he => hj (e.injective (he.trans hib.symm))⟩ := by
  simp [ggResIKIdx, hj]

section Dispatch

variable {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
  {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
  {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)} {h : Option Λ → V}
  {α : Option Λ → Module.Dual (ZMod p) V} {x : V}

theorem ggResI_dispatch_shape (H : GGResIHyp p b ML CL MK CK g h α x)
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j)
    {ib : Fin n} (hib : e ib = b) (j₀ : Fin n) (hj₀ : j₀ ≠ ib)
    (pt : Fin n → Fin n → List (Fin n))
    (hcyc : ∀ j₁ j₂ : Fin n, j₁ ≠ ib → j₂ ≠ ib → j₁ ≠ j₂ → ggCycleOK C ib j₁ j₂ (pt j₁ j₂))
    (shapes : List (Fin n × ℤ × ℤ)) (vecs : List (Fin n × ℤ × ℤ × List ℕ))
    (hcand : ∀ ic : Fin n, ic ≠ ib → ∀ pr ∈ ggCartanPairsNZ,
      ggCandB C ib ic pr.1 pr.2 shapes vecs = true) :
    ∃ (ic : Fin n) (e₁ e₂ : ℤ), ic ≠ ib ∧ (e₁, e₂) ∈ ggCartanPairsNZ ∧
      (ic, e₁, e₂) ∈ shapes ∧
      (∀ (j : Fin n) (hj : e j ≠ b),
        CK none (some ⟨e j, hj⟩) = if j = ic then e₁ else 0) ∧
      (∀ (j : Fin n) (hj : e j ≠ b),
        CK (some ⟨e j, hj⟩) none = if j = ic then e₂ else 0) := by
  classical
  have hne : ∀ j : Fin n, j ≠ ib → e j ≠ b := fun j hj he => hj (e.injective (he.trans hib.symm))
  set ψ := ggResIKIdx e hib with hψ
  set Km := CK.submatrix ψ ψ with hKm
  have hFT : TauCeti.IsFiniteType Km :=
    (isFiniteType_of_ggIsWeylMatrixFixed H.hWK H.hCK).submatrix ψ.injective
  have hdiagL : ∀ i, C i i = 2 := fun i => by rw [← hCe]; exact H.hCL.1 _
  have hψib : ψ ib = none := ggResIKIdx_ib e hib
  have hψne : ∀ j (hj : j ≠ ib), ψ j = some ⟨e j, hne j hj⟩ := fun j hj => ggResIKIdx_ne e hib hj
  have hKJ : ∀ i j, i ≠ ib → j ≠ ib → Km i j = C i j := by
    intro i j hi hj
    simp only [hKm, Matrix.submatrix_apply, hψne i hi, hψne j hj]
    by_cases hij : i = j
    · subst hij
      rw [H.hCK.1, hdiagL]
    · have hij' : (some ⟨e i, hne i hi⟩ : Option {i : Λ // i ≠ b}) ≠ some ⟨e j, hne j hj⟩ :=
        fun h => hij (e.injective (by simpa using h))
      have hpK := ggCartanPair_mem H.hCK hij'
      have hpL := ggCartanPair_mem H.hCL (fun h => hij (e.injective h))
      have h1 := H.hK (some ⟨e i, hne i hi⟩) (some ⟨e j, hne j hj⟩)
      have h2 := H.hK (some ⟨e j, hne j hj⟩) (some ⟨e i, hne i hi⟩)
      simp only [Option.map_some] at h1 h2
      rw [H.hL] at h1 h2
      exact ((ggCartanPair_eq H.hp2 hpK hpL h1.symm h2.symm).1).trans (hCe i j)
  have hKsym : ∀ i j, Km i j = 0 ↔ Km j i = 0 := fun i j => hFT.apply_eq_zero_iff
  have hex : ∃ j, j ≠ ib ∧ Km ib j ≠ 0 := by
    have hpath := ggRC_weyl_connected H.hWK none (ψ j₀)
    rcases Relation.ReflTransGen.cases_head hpath with h0 | ⟨c, hc, -⟩
    · rw [hψne j₀ hj₀] at h0
      exact absurd h0 (by simp)
    have hCc : CK none c ≠ 0 := by
      intro h0
      rcases H.hCK.2 none c hc.1 with ⟨hm, -, -⟩ | ⟨-, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩
      · exact hc.2 hm
      · rw [h0] at h1; norm_num at h1
      · rw [h0] at h1; exact lt_irrefl 0 h1
      · rw [h0] at h1; exact lt_irrefl 0 h1
    refine ⟨ψ.symm c, fun h => ?_, ?_⟩
    · have : c = ψ ib := by rw [← h, Equiv.apply_symm_apply]
      rw [this, hψib] at hc
      exact hc.1 rfl
    · simp only [hKm, Matrix.submatrix_apply, Equiv.apply_symm_apply, hψib]
      exact hCc
  have huniq : ∀ j₁ j₂, j₁ ≠ ib → j₂ ≠ ib → j₁ ≠ j₂ → Km ib j₁ ≠ 0 → Km ib j₂ ≠ 0 → False := by
    intro j₁ j₂ h₁ h₂ h12 hk₁ hk₂
    have hc := hcyc j₁ j₂ h₁ h₂ h12
    refine ggResI_no_cycle hFT (ib :: pt j₁ j₂).toFinset ⟨ib, by simp⟩ fun i hi =>
      (hc i hi).trans (Finset.card_le_card ?_)
    intro j hj
    simp only [Finset.mem_filter] at hj ⊢
    obtain ⟨hjS, hji, hadj⟩ := hj
    refine ⟨hjS, hji, ?_⟩
    rcases (ggCycleAdj_spec C ib j₁ j₂ i j).mp hadj with ⟨rfl, rfl | rfl⟩ | ⟨-, rfl, rfl | rfl⟩ |
        ⟨hi', hj', hC⟩
    · exact hk₁
    · exact hk₂
    · exact fun h0 => hk₁ ((hKsym _ _).mp h0)
    · exact fun h0 => hk₂ ((hKsym _ _).mp h0)
    · rw [hKJ i j hi' hj']
      exact hC
  obtain ⟨ic, hic, hKic⟩ := hex
  have hicne : ψ ib ≠ ψ ic := fun h => hic (ψ.injective h).symm
  have hpair : (Km ib ic, Km ic ib) ∈ ggCartanPairsNZ := by
    have hmem := ggCartanPair_mem H.hCK hicne
    simp only [ggCartanPairs, List.mem_cons, List.not_mem_nil, or_false] at hmem
    have hK0 : Km ib ic ≠ 0 := hKic
    simp only [hKm, Matrix.submatrix_apply] at hK0 ⊢
    simp only [ggCartanPairsNZ, List.mem_cons, List.not_mem_nil, or_false]
    rcases hmem with h0 | h0 | h0 | h0 | h0 | h0
    · exact absurd (Prod.mk.inj h0).1 hK0
    all_goals simp only [h0, true_or, or_true]
  have hrowK : ∀ j, j ≠ ib → Km ib j = if j = ic then Km ib ic else 0 := by
    intro j hj
    by_cases hjc : j = ic
    · rw [if_pos hjc, hjc]
    · rw [if_neg hjc]
      by_contra h0
      exact huniq j ic hj hic hjc h0 hKic
  have hcolK : ∀ j, j ≠ ib → Km j ib = if j = ic then Km ic ib else 0 := by
    intro j hj
    by_cases hjc : j = ic
    · rw [if_pos hjc, hjc]
    · rw [if_neg hjc]
      have := hrowK j hj
      rw [if_neg hjc] at this
      exact (hKsym _ _).mp this
  have hrow : ∀ (j : Fin n) (hj : e j ≠ b),
      CK none (some ⟨e j, hj⟩) = if j = ic then Km ib ic else 0 := by
    intro j hj
    have hj' : j ≠ ib := fun h => hj (by rw [h, hib])
    have := hrowK j hj'
    simpa [hKm, Matrix.submatrix_apply, hψib, hψne j hj'] using this
  have hcol : ∀ (j : Fin n) (hj : e j ≠ b),
      CK (some ⟨e j, hj⟩) none = if j = ic then Km ic ib else 0 := by
    intro j hj
    have hj' : j ≠ ib := fun h => hj (by rw [h, hib])
    have := hcolK j hj'
    simpa [hKm, Matrix.submatrix_apply, hψib, hψne j hj'] using this
  have hKaa : CK none none = 2 := H.hCK.1 none
  have hc := hcand ic hic (Km ib ic, Km ic ib) hpair
  simp only [ggCandB, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true]
    at hc
  rcases hc with (hmem | hfork) | ⟨w, -, ⟨⟨⟨hw1, hw2⟩, hw3⟩, hvec⟩⟩
  ·
    exact ⟨ic, Km ib ic, Km ic ib, hic, hpair, hmem, hrow, hcol⟩
  ·
    exfalso
    apply H.hnf
    simp only [ggForkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
      true_implies, Bool.or_eq_true] at hfork
    obtain ⟨⟨he₁, he₂⟩, hC⟩ := hfork
    refine ⟨⟨e ic, hne ic hic⟩, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
    all_goals
      obtain ⟨l, hl⟩ := i
      have hj' : e.symm l ≠ ib := fun h => hl (by rw [← hib, ← h, e.apply_symm_apply])
      have hiff : (⟨l, hl⟩ : {i : Λ // i ≠ b}) = ⟨e ic, hne ic hic⟩ ↔ e.symm l = ic := by
        rw [Subtype.mk.injEq, Equiv.symm_apply_eq]
      have hl' : l = e (e.symm l) := (e.apply_symm_apply l).symm
    · have := ((hC (e.symm l)).resolve_left hj').1
      rw [← hCe, ← hl', hib] at this
      rw [this]
      simp only [hiff]
    · have := ((hC (e.symm l)).resolve_left hj').2
      rw [← hCe, ← hl', hib] at this
      rw [this]
      simp only [hiff]
    · have := hrow (e.symm l) (by rwa [e.apply_symm_apply])
      simp only [e.apply_symm_apply, he₁] at this
      rw [this]
      simp only [hiff]
    · have := hcol (e.symm l) (by rwa [e.apply_symm_apply])
      simp only [e.apply_symm_apply, he₂] at this
      rw [this]
      simp only [hiff]
  ·
    exfalso
    have hmat : ∀ i j, Km i j = ggKmatI C ib ic (Km ib ic) (Km ic ib) i j := by
      intro i j
      unfold ggKmatI
      by_cases hi : i = ib
      · subst hi
        by_cases hj : j = i
        · subst hj
          rw [if_pos rfl, if_pos rfl]
          simp only [hKm, Matrix.submatrix_apply, hψib]
          exact hKaa
        · rw [if_pos rfl, if_neg hj, hrowK j hj]
      · rw [if_neg hi]
        by_cases hj : j = ib
        · subst hj
          rw [if_pos rfl, hcolK i hi]
        · rw [if_neg hj, hKJ i j hi hj]
    simp only [ggVecOK, Bool.and_eq_true, List.any_eq_true, List.mem_finRange, true_and,
      List.all_eq_true, true_implies, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
      bne_iff_ne, ne_eq] at hvec
    obtain ⟨⟨i₀, hi₀⟩, hle⟩ := hvec
    refine ggResI_finite_vec hFT (fun i => w.2.2.2.getD i.val 0) ⟨i₀, hi₀⟩ fun i hi => ?_
    rcases hle i with h0 | h0
    · exact absurd h0 hi
    · calc ∑ j, Km i j * ((w.2.2.2.getD j.val 0 : ℕ) : ℤ)
          = ∑ j, ggKmatI C ib ic (Km ib ic) (Km ic ib) i j * ((w.2.2.2.getD j.val 0 : ℕ) : ℤ) :=
            Finset.sum_congr rfl fun j _ => by rw [hmat i j]
        _ ≤ 0 := h0

theorem ggResI_dispatch_elim (H : GGResIHyp p b ML CL MK CK g h α x)
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j)
    {ib : Fin n} (hib : e ib = b) (j₀ : Fin n) (hj₀ : j₀ ≠ ib)
    (pt : Fin n → Fin n → List (Fin n))
    (hcyc : ∀ j₁ j₂ : Fin n, j₁ ≠ ib → j₂ ≠ ib → j₁ ≠ j₂ → ggCycleOK C ib j₁ j₂ (pt j₁ j₂))
    (shapes : List (Fin n × ℤ × ℤ)) (vecs : List (Fin n × ℤ × ℤ × List ℕ))
    (hcand : ∀ ic : Fin n, ic ≠ ib → ∀ pr ∈ ggCartanPairsNZ,
      ggCandB C ib ic pr.1 pr.2 shapes vecs = true)
    {Concl : Prop} (hconcl : ∀ (ic : Fin n) (e₁ e₂ : ℤ), ic ≠ ib →
      (e₁, e₂) ∈ ggCartanPairsNZ → (ic, e₁, e₂) ∈ shapes →
      (∀ (j : Fin n) (hj : e j ≠ b),
        CK none (some ⟨e j, hj⟩) = if j = ic then e₁ else 0) →
      (∀ (j : Fin n) (hj : e j ≠ b),
        CK (some ⟨e j, hj⟩) none = if j = ic then e₂ else 0) → Concl) : Concl := by
  rcases ggResI_dispatch_shape H e hCe hib j₀ hj₀ pt hcyc shapes vecs hcand with
    ⟨ic, e₁, e₂, hic, hpair, hmem, hrow, hcol⟩
  exact hconcl ic e₁ e₂ hic hpair hmem hrow hcol

theorem ggResI_dispatch_leaf [Module.Finite (ZMod p) V] [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x)
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j)
    {ib : Fin n} (hib : e ib = b) (j₀ : Fin n) (hj₀ : j₀ ≠ ib)
    (pt : Fin n → Fin n → List (Fin n))
    (hcyc : ∀ j₁ j₂ : Fin n, j₁ ≠ ib → j₂ ≠ ib → j₁ ≠ j₂ → ggCycleOK C ib j₁ j₂ (pt j₁ j₂))
    (shapes : List (Fin n × ℤ × ℤ)) (vecs : List (Fin n × ℤ × ℤ × List ℕ))
    (hcand : ∀ ic : Fin n, ic ≠ ib → ∀ pr ∈ ggCartanPairsNZ,
      ggCandB C ib ic pr.1 pr.2 shapes vecs = true)
    (hshapes : ∀ s ∈ shapes, GGResIShapeOK C ib s.1 s.2.1 s.2.2) :
    GGResILinConcl p b CL CK g h α x :=
  ggResI_dispatch_elim H e hCe hib j₀ hj₀ pt hcyc shapes vecs hcand
    fun ic e₁ e₂ hic _ hmem hrow hcol =>
      ggResI_transport H.hp2 H.hg H.hL H.hK H.hind H.hspan H.hxL H.hfix H.hx0 e hCe
        (fun i => by rw [← hCe]; exact H.hCL.1 _) hib (Ne.symm hic) hrow hcol (H.hCK.1 none)
        (hshapes _ hmem)

theorem ggResI_dispatch_cut [Finite V] (H : GGResIHyp p b ML CL MK CK g h α x) {n : ℕ}
    {C : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j)
    {ib : Fin n} (hib : e ib = b) (S : Finset (Fin n)) (j₁ j₂ : Fin n) (h₁ : j₁ ∈ S)
    (h₂ : j₂ ∉ S) (hj₁ : j₁ ≠ ib) (hj₂ : j₂ ≠ ib)
    (hcut : ∀ ac : Fin n × Fin n, ac.1 ∈ S → ac.2 ∉ S → ac.2 ≠ ib → C ac.1 ac.2 = 0) :
    GGResILinConcl p b CL CK g h α x :=
  (ggResII_leaf_cut H.hCL H.hconn e hCe hib S j₁ j₂ h₁ h₂ hj₁ hj₂
    fun a ha c hc hcb => hcut (a, c) ha hc hcb).elim

end Dispatch

end CFSG.StandardType
