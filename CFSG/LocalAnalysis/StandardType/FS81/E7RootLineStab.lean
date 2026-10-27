module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RootLineStabData
public import CFSG.LocalAnalysis.StandardType.FS81.SpMatAlg

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

@[expose] def e7CorootRefl (k : Fin 7) : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  1 - Matrix.of fun i j => if i = k then ((CartanMatrix.E 7 k j : ℤ) : ZMod 3) else 0

@[expose] def e7LocalGen (k : Fin 7) : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => (e7LocalRinv * e7CorootRefl k * e7LocalR) i' j') j) i

private def e7LocalS : Set (Matrix (Fin 8) (Fin 8) (ZMod 3)) :=
  spSet fun σ s => σ 0 = 0 ∧ s 0 = 1 ∧ σ 1 = 1 ∧ ∏ i : Fin 6, s i.succ.succ = 1

private def e7LocalT (l : Fin 63) : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => e7LocalT7 l i' j') j) i

private def e7LocalTinv (l : Fin 63) : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => e7LocalTinv7 l i' j') j) i

theorem e7LocalR_mul_Rinv : e7LocalR * e7LocalRinv = 1 := by
  decide +kernel

theorem e7LocalRinv_mul_R : e7LocalRinv * e7LocalR = 1 := by
  decide +kernel

theorem e7LocalGen_mul_self (k : Fin 7) : e7LocalGen k * e7LocalGen k = 1 := by
  fin_cases k <;> decide +kernel

private theorem e7LocalT_mul_Tinv (l : Fin 63) : e7LocalT l * e7LocalTinv l = 1 := by
  fin_cases l <;> decide +kernel

private theorem e7LocalT_zero : e7LocalT 0 = 1 := by
  decide +kernel

private theorem e7Local_mul_sign {a b : ZMod 3} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

private theorem e7LocalS_one : (1 : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ e7LocalS := by
  refine ⟨1, fun _ => 1, ?_, ⟨rfl, rfl, rfl, ?_⟩, ?_⟩
  · intro i; exact Or.inl rfl
  · simp
  · exact spMat_one.symm

private theorem e7LocalS_mul_mem {M N : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hM : M ∈ e7LocalS) (hN : N ∈ e7LocalS) : M * N ∈ e7LocalS := by
  obtain ⟨σ, s, hs, ⟨hσ0, hs0, hσ1, hprod⟩, rfl⟩ := hM
  obtain ⟨τ, t, ht, ⟨hτ0, ht0, hτ1, htprod⟩, rfl⟩ := hN
  refine ⟨σ * τ, fun j => s (τ j) * t j, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j
    exact e7Local_mul_sign (hs (τ j)) (ht j)
  · simp [Equiv.Perm.mul_apply, hτ0, hσ0]
  · simp [hτ0, hs0, ht0]
  · simp [Equiv.Perm.mul_apply, hτ1, hσ1]
  · rw [Finset.prod_mul_distrib]
    let T : Finset (Fin 8) := Finset.univ.filter (fun i => i ≠ 0 ∧ i ≠ 1)
    have hTmem : ∀ i : Fin 8, i ∈ T ↔ i ≠ 0 ∧ i ≠ 1 := by
      intro i
      simp [T]
    have himage : Finset.univ.image (fun i : Fin 6 => i.succ.succ) = T := by
      decide +kernel
    have hinj : Set.InjOn (fun i : Fin 6 => i.succ.succ) ↑(Finset.univ : Finset (Fin 6)) := by
      intro a _ b _ h
      simpa using h
    have hbij : (∏ i : Fin 6, s (i.succ.succ)) = Finset.prod T s := by
      calc ∏ i : Fin 6, s (i.succ.succ) =
            Finset.prod (Finset.univ.image (fun i : Fin 6 => i.succ.succ)) s :=
            (Finset.prod_image hinj).symm
        _ = Finset.prod T s := by rw [himage]
    have hbijt : (∏ i : Fin 6, t (i.succ.succ)) = Finset.prod T t := by
      calc ∏ i : Fin 6, t (i.succ.succ) =
            Finset.prod (Finset.univ.image (fun i : Fin 6 => i.succ.succ)) t :=
            (Finset.prod_image hinj).symm
        _ = Finset.prod T t := by rw [himage]
    have hbijτ : (∏ i : Fin 6, s (τ (i.succ.succ))) = Finset.prod T (fun j => s (τ j)) := by
      calc ∏ i : Fin 6, s (τ (i.succ.succ)) =
            Finset.prod (Finset.univ.image (fun i : Fin 6 => i.succ.succ)) (fun j => s (τ j)) :=
            (Finset.prod_image (f := fun j => s (τ j)) hinj).symm
        _ = Finset.prod T (fun j => s (τ j)) := by rw [himage]
    have hτT : Finset.prod T (fun j => s (τ j)) = Finset.prod T s := by
      refine Equiv.Perm.prod_comp τ T s ?_
      intro a ha
      exact (hTmem a).2 ⟨fun h => ha (by rw [h, hτ0]), fun h => ha (by rw [h, hτ1])⟩
    rw [hbijτ, hbijt, hτT, ← hbij, ← hbijt, hprod, htprod, mul_one]
  · exact spMat_mul σ τ s t

private theorem e7LocalS_mulVec_e1 {A : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hA : A ∈ e7LocalS) :
    A *ᵥ Pi.single 1 1 = Pi.single 1 1 ∨ A *ᵥ Pi.single 1 1 = -Pi.single 1 1 := by
  obtain ⟨σ, s, hs, ⟨-, -, hσ1, -⟩, rfl⟩ := hA
  rw [spMat_mulVec]
  have hfun :
      (fun i => s (σ.symm i) * ((Pi.single 1 (1 : ZMod 3) : Fin 8 → ZMod 3)) (σ.symm i)) =
        Pi.single 1 (s 1) := by
    funext i
    by_cases hi : i = 1
    · subst hi
      have hσ : σ.symm 1 = 1 := by
        have h := congrArg σ.symm hσ1
        simpa [Equiv.symm_apply_apply] using h.symm
      rw [hσ, Pi.single_eq_same, Pi.single_eq_same, mul_one]
    · have hne : σ.symm i ≠ 1 := by
        intro h
        have h1 : σ (σ.symm i) = σ 1 := by rw [h, hσ1]
        rw [Equiv.apply_symm_apply] at h1
        exact hi (h1.trans hσ1)
      rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hne, mul_zero]
  rw [hfun]
  rcases hs 1 with h | h
  · left
    rw [h]
  · right
    rw [h]
    funext i
    by_cases hi : i = 1
    · subst hi; simp
    · rw [Pi.single_eq_of_ne hi]
      change (0 : ZMod 3) = -((Pi.single 1 (1 : ZMod 3) : Fin 8 → ZMod 3) i)
      rw [Pi.single_eq_of_ne hi]
      have h0 : (-(0 : ZMod 3)) = 0 := neg_zero
      exact h0.symm

private abbrev e7LocalPermFix : Type :=
  {σ : Equiv.Perm (Fin 8) // σ 0 = 0 ∧ σ 1 = 1}

private theorem e7LocalPermFix_card_le : Nat.card e7LocalPermFix ≤ 720 := by
  let p8 : Fin 8 → Prop := fun i => i ≠ 0 ∧ i ≠ 1
  let inj : e7LocalPermFix → Equiv.Perm {i : Fin 8 // p8 i} := fun σ =>
    σ.1.subtypePerm (by
      intro x
      constructor <;> intro hx
      · exact ⟨fun h => hx.1 (by rw [h]; exact σ.2.1),
               fun h => hx.2 (by rw [h]; exact σ.2.2)⟩
      · exact ⟨fun h => hx.1 (σ.1.injective (h.trans σ.2.1.symm)),
               fun h => hx.2 (σ.1.injective (h.trans σ.2.2.symm))⟩)
  have hinj : Function.Injective inj := by
    intro σ σ' h
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : p8 x
    · have h1 := congrArg (fun y : {i : Fin 8 // p8 i} => y.1)
        (Equiv.ext_iff.mp h ⟨x, hx⟩)
      simpa [inj, Equiv.Perm.subtypePerm_apply] using h1
    · have hx' : x = 0 ∨ x = 1 := by
        by_cases h0 : x = 0
        · exact Or.inl h0
        · by_cases h1 : x = 1
          · exact Or.inr h1
          · exact absurd ⟨h0, h1⟩ hx
      rcases hx' with rfl | rfl
      · exact σ.2.1.trans σ'.2.1.symm
      · exact σ.2.2.trans σ'.2.2.symm
  have hcard6 : Nat.card {i : Fin 8 // p8 i} = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hperm : Nat.card (Equiv.Perm {i : Fin 8 // p8 i}) = 720 := by
    rw [Nat.card_perm, hcard6]
    norm_num
  calc Nat.card e7LocalPermFix ≤ Nat.card (Equiv.Perm {i : Fin 8 // p8 i}) :=
        Nat.card_le_card_of_injective inj hinj
    _ = 720 := hperm

private abbrev e7LocalSignFix : Type :=
  {s : Fin 8 → ZMod 3 // (∀ i, s i = 1 ∨ s i = -1) ∧ s 0 = 1 ∧
    (∏ i : Fin 6, s i.succ.succ) = 1}

private theorem e7LocalSignFix_card : Nat.card e7LocalSignFix = 64 := by
  rw [e7LocalSignFix, Nat.card_eq_fintype_card]
  decide +kernel

private abbrev e7LocalSParam : Type := e7LocalPermFix × e7LocalSignFix

private theorem e7LocalSParam_card : Nat.card e7LocalSParam ≤ 46080 := by
  rw [e7LocalSParam, Nat.card_prod]
  calc Nat.card e7LocalPermFix * Nat.card e7LocalSignFix
      ≤ 720 * 64 := Nat.mul_le_mul e7LocalPermFix_card_le (le_of_eq e7LocalSignFix_card)
    _ = 46080 := by norm_num

private theorem e7LocalS_card_le : Nat.card ↥e7LocalS ≤ 46080 := by
  let F : e7LocalSParam → Matrix (Fin 8) (Fin 8) (ZMod 3) := fun q => spMat q.1.1 q.2.1
  have hsub : e7LocalS ⊆ Set.range F := by
    rintro _ ⟨σ, s, hs, ⟨hσ0, hs0, hσ1, hp⟩, rfl⟩
    exact ⟨⟨⟨σ, hσ0, hσ1⟩, ⟨s, hs, hs0, hp⟩⟩, rfl⟩
  calc Nat.card ↥e7LocalS ≤ Nat.card ↥(Set.range F) := Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card e7LocalSParam :=
        Nat.card_le_card_of_surjective (Set.rangeFactorization F) Set.rangeFactorization_surjective
    _ ≤ 46080 := e7LocalSParam_card

private abbrev e7LocalTableOK (l : Fin 63) (k : Fin 7) : Prop :=
  (∀ i j : Fin 8, e7LocalTablePermFun l k i = e7LocalTablePermFun l k j → i = j) ∧
    (∀ j : Fin 8, ∃ i : Fin 8, e7LocalTablePermFun l k i = j) ∧
    (∀ i, e7LocalTableSign l k i = 1 ∨ e7LocalTableSign l k i = -1) ∧
    e7LocalTablePermFun l k 0 = 0 ∧ e7LocalTableSign l k 0 = 1 ∧
    e7LocalTablePermFun l k 1 = 1 ∧
    (∏ i : Fin 6, e7LocalTableSign l k i.succ.succ) = 1 ∧
    (∀ i j : Fin 8, (e7LocalTinv (e7LocalTable l k) * e7LocalGen k * e7LocalT l) i j =
      (if i = e7LocalTablePermFun l k j then e7LocalTableSign l k j else 0))

private theorem e7LocalTableOK_all : ∀ l : Fin 63, ∀ k : Fin 7, e7LocalTableOK l k := by
  decide +kernel

private theorem e7LocalTable_mem :
    ∀ (l : Fin 63) (k : Fin 7),
      e7LocalTinv (e7LocalTable l k) * e7LocalGen k * e7LocalT l ∈ e7LocalS := by
  intro l k
  obtain ⟨hinj, hsurj, hsign, h0, hs0, h1, hprod, hmat⟩ := e7LocalTableOK_all l k
  have hmatEq : e7LocalTinv (e7LocalTable l k) * e7LocalGen k * e7LocalT l =
      (fun i j => if i = e7LocalTablePermFun l k j then e7LocalTableSign l k j else 0) := by
    funext i j
    exact hmat i j
  have hsp : spMat (Equiv.ofBijective (e7LocalTablePermFun l k) ⟨hinj, hsurj⟩)
      (e7LocalTableSign l k) =
      (fun i j => if i = e7LocalTablePermFun l k j then e7LocalTableSign l k j else 0) := rfl
  refine ⟨Equiv.ofBijective (e7LocalTablePermFun l k) ⟨hinj, hsurj⟩,
    e7LocalTableSign l k, hsign, ⟨h0, hs0, h1, hprod⟩, ?_⟩
  show e7LocalTinv (e7LocalTable l k) * e7LocalGen k * e7LocalT l =
    spMat (Equiv.ofBijective (e7LocalTablePermFun l k) ⟨hinj, hsurj⟩)
      (e7LocalTableSign l k)
  rw [hsp]
  exact hmatEq

private abbrev e7LocalColOK (l : Fin 63) : Prop :=
  l ≠ 0 →
    (∃ i : Fin 8, e7LocalT l i 1 ≠ (Pi.single 1 1 : Fin 8 → ZMod 3) i) ∧
    (∃ i : Fin 8, e7LocalT l i 1 ≠ (-(Pi.single 1 1 : Fin 8 → ZMod 3)) i)

private theorem e7LocalColOK_all : ∀ l : Fin 63, e7LocalColOK l := by
  decide +kernel

private theorem e7LocalDecomp_of_mem_closure {M : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hM : M ∈ Submonoid.closure (Set.range e7LocalGen)) : ∃ l : Fin 63, ∃ s : Matrix (Fin 8) (Fin 8) (ZMod 3), s ∈ e7LocalS ∧ M = e7LocalT l * s := by
  refine Submonoid.closure_induction_left ?_ ?_ hM
  · exact ⟨0, 1, e7LocalS_one, by rw [e7LocalT_zero, one_mul]⟩
  · intro x hx y hy ih
    rw [Set.mem_range] at hx
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨l, s, hs, rfl⟩ := ih
    have htab : e7LocalTinv (e7LocalTable l k) * e7LocalGen k * e7LocalT l ∈ e7LocalS :=
      e7LocalTable_mem l k
    have hgt : e7LocalGen k * e7LocalT l =
        e7LocalT (e7LocalTable l k) *
          (e7LocalTinv (e7LocalTable l k) * e7LocalGen k * e7LocalT l) := by
      calc e7LocalGen k * e7LocalT l
          = (e7LocalT (e7LocalTable l k) * e7LocalTinv (e7LocalTable l k)) *
              (e7LocalGen k * e7LocalT l) := by rw [e7LocalT_mul_Tinv, one_mul]
        _ = e7LocalT (e7LocalTable l k) *
              (e7LocalTinv (e7LocalTable l k) * e7LocalGen k * e7LocalT l) := by
              simp only [mul_assoc]
    refine ⟨e7LocalTable l k,
      (e7LocalTinv (e7LocalTable l k) * e7LocalGen k * e7LocalT l) * s,
      e7LocalS_mul_mem htab hs, ?_⟩
    calc e7LocalGen k * (e7LocalT l * s)
        = (e7LocalGen k * e7LocalT l) * s := (mul_assoc _ _ _).symm
      _ = (e7LocalT (e7LocalTable l k) *
            (e7LocalTinv (e7LocalTable l k) * e7LocalGen k * e7LocalT l)) * s := by rw [hgt]
      _ = e7LocalT (e7LocalTable l k) *
            ((e7LocalTinv (e7LocalTable l k) * e7LocalGen k * e7LocalT l) * s) :=
            mul_assoc _ _ _

private noncomputable def e7LocalChosenL
    (M : ↥(Submonoid.closure (Set.range e7LocalGen))) : Fin 63 :=
  Classical.choose (e7LocalDecomp_of_mem_closure M.property)

private noncomputable def e7LocalChosenS
    (M : ↥(Submonoid.closure (Set.range e7LocalGen))) : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  Classical.choose (Classical.choose_spec (e7LocalDecomp_of_mem_closure M.property))

private theorem e7LocalChosenS_mem (M : ↥(Submonoid.closure (Set.range e7LocalGen))) :
    e7LocalChosenS M ∈ e7LocalS :=
  (Classical.choose_spec (Classical.choose_spec
    (e7LocalDecomp_of_mem_closure M.property))).1

private theorem e7LocalChosen_eq (M : ↥(Submonoid.closure (Set.range e7LocalGen))) :
    M.val = e7LocalT (e7LocalChosenL M) * e7LocalChosenS M :=
  (Classical.choose_spec (Classical.choose_spec
    (e7LocalDecomp_of_mem_closure M.property))).2

private noncomputable def e7LocalClosureToParam :
    ↥(Submonoid.closure (Set.range e7LocalGen)) → Fin 63 × ↥e7LocalS :=
  fun M => (e7LocalChosenL M, ⟨e7LocalChosenS M, e7LocalChosenS_mem M⟩)

private theorem e7LocalClosureToParam_injective :
    Function.Injective e7LocalClosureToParam := by
  intro M M' h
  apply Subtype.ext
  have h1 : e7LocalChosenL M = e7LocalChosenL M' := congrArg (fun q => q.1) h
  have h2 : e7LocalChosenS M = e7LocalChosenS M' := congrArg (fun q => q.2.1) h
  rw [e7LocalChosen_eq, e7LocalChosen_eq, h1, h2]

private theorem e7LocalClosure_card_le :
    Nat.card ↥(Submonoid.closure (Set.range e7LocalGen)) ≤ 63 * Nat.card ↥e7LocalS := by
  calc Nat.card ↥(Submonoid.closure (Set.range e7LocalGen)) ≤ Nat.card (Fin 63 × ↥e7LocalS) :=
        Nat.card_le_card_of_injective e7LocalClosureToParam e7LocalClosureToParam_injective
    _ = 63 * Nat.card ↥e7LocalS := by rw [Nat.card_prod, Nat.card_fin]

private theorem e7LocalS_subset_closure
    (hcard : 2903040 ≤ Nat.card ↥(Submonoid.closure (Set.range e7LocalGen))) :
    e7LocalS ⊆ (Submonoid.closure (Set.range e7LocalGen) : Set _) := by
  have h1 := e7LocalClosure_card_le
  have h2 := e7LocalS_card_le
  have h3 : 63 * Nat.card ↥e7LocalS ≤ 2903040 := by
    have h := Nat.mul_le_mul_left 63 h2
    norm_num at h ⊢
    exact h
  have hSeq : Nat.card ↥e7LocalS = 46080 := by omega
  have hclosed : Nat.card ↥(Submonoid.closure (Set.range e7LocalGen)) =
      63 * Nat.card ↥e7LocalS := by omega
  have hcard_eq : Nat.card ↥(Submonoid.closure (Set.range e7LocalGen)) =
      Nat.card (Fin 63 × ↥e7LocalS) := by
    rw [Nat.card_prod, Nat.card_fin]
    exact hclosed
  have hrange_card : Nat.card ↥(Set.range e7LocalClosureToParam) =
      Nat.card ↥(Submonoid.closure (Set.range e7LocalGen)) :=
    (Nat.card_congr (Equiv.ofInjective e7LocalClosureToParam e7LocalClosureToParam_injective)).symm
  have huniv : Nat.card ↥(Set.univ : Set (Fin 63 × ↥e7LocalS)) =
      Nat.card ↥(Set.range e7LocalClosureToParam) := by
    rw [Nat.card_congr (Equiv.Set.univ (Fin 63 × ↥e7LocalS)), hrange_card]
    exact hcard_eq.symm
  have hrange_eq : Set.range e7LocalClosureToParam = Set.univ := by
    refine Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) (Set.subset_univ _) ?_
    rw [huniv]
  have hsurj : Function.Surjective e7LocalClosureToParam := by
    intro y
    have hy : y ∈ Set.range e7LocalClosureToParam := by rw [hrange_eq]; exact Set.mem_univ y
    exact hy
  intro s hs
  obtain ⟨M, hM⟩ := hsurj (0, ⟨s, hs⟩)
  have h1 : e7LocalChosenL M = 0 := congrArg (fun q => q.1) hM
  have h2 : e7LocalChosenS M = s := congrArg (fun q => q.2.1) hM
  have hMs : M.val = s := by rw [e7LocalChosen_eq, h1, h2, e7LocalT_zero, one_mul]
  rw [← hMs]
  exact M.property

private theorem e7LocalT_mulVec_single (l : Fin 63) :
    e7LocalT l *ᵥ (Pi.single 1 1 : Fin 8 → ZMod 3) = fun i => e7LocalT l i 1 := by
  rw [Matrix.mulVec_single_one]
  rfl

private theorem e7LocalT_mulVec_neg_single (l : Fin 63) :
    e7LocalT l *ᵥ (-(Pi.single 1 1 : Fin 8 → ZMod 3)) = -(fun i => e7LocalT l i 1) := by
  calc e7LocalT l *ᵥ (-(Pi.single 1 1 : Fin 8 → ZMod 3))
      = -(e7LocalT l *ᵥ (Pi.single 1 1 : Fin 8 → ZMod 3)) :=
        Matrix.mulVec_neg (v := (Pi.single 1 1 : Fin 8 → ZMod 3)) (A := e7LocalT l)
    _ = -(fun i => e7LocalT l i 1) := by rw [e7LocalT_mulVec_single]

theorem e7Local_stab
    (hcard : 2903040 ≤ Nat.card (Submonoid.closure (Set.range e7LocalGen))) :
    {M | M ∈ Submonoid.closure (Set.range e7LocalGen) ∧
        (M *ᵥ Pi.single 1 1 = Pi.single 1 1 ∨ M *ᵥ Pi.single 1 1 = -Pi.single 1 1)} =
      spSet (fun σ s => σ 0 = 0 ∧ s 0 = 1 ∧ σ 1 = 1 ∧ ∏ i : Fin 6, s i.succ.succ = 1) := by
  have hSsub := e7LocalS_subset_closure hcard
  ext M
  constructor
  · rintro ⟨hM, hv⟩
    obtain ⟨l, s, hs, rfl⟩ := e7LocalDecomp_of_mem_closure hM
    change e7LocalT l * s ∈ e7LocalS
    by_cases hl : l = 0
    · rw [hl, e7LocalT_zero, one_mul]
      exact hs
    · exfalso
      have hcol := e7LocalColOK_all l hl
      have hcol0 : (fun i => e7LocalT l i 1) ≠ Pi.single 1 1 := by
        rintro h
        obtain ⟨i, hi⟩ := hcol.1
        exact hi (congrFun h i)
      have hcol1 : (fun i => e7LocalT l i 1) ≠ -Pi.single 1 1 := by
        rintro h
        obtain ⟨i, hi⟩ := hcol.2
        exact hi (congrFun h i)
      have hMv : (e7LocalT l * s) *ᵥ Pi.single 1 1 =
          e7LocalT l *ᵥ (s *ᵥ Pi.single 1 1) :=
        (Matrix.mulVec_mulVec (v := Pi.single 1 1) (M := e7LocalT l) (N := s)).symm
      rcases e7LocalS_mulVec_e1 hs with hsv | hsv
      · rw [hMv, hsv, e7LocalT_mulVec_single] at hv
        rcases hv with hv | hv
        · exact hcol0 hv
        · exact hcol1 hv
      · have hneg : e7LocalT l *ᵥ (s *ᵥ Pi.single 1 1) = -(fun i => e7LocalT l i 1) := by
          rw [hsv]
          exact e7LocalT_mulVec_neg_single l
        rw [hMv, hneg] at hv
        rcases hv with hv | hv
        · exact hcol1 (neg_eq_iff_eq_neg.mp hv)
        · exact hcol0 (neg_inj.mp hv)
  · intro hM
    have hS : M ∈ e7LocalS := hM
    exact ⟨hSsub hS, e7LocalS_mulVec_e1 hS⟩

end CFSG.StandardType.FrameRoute.FS81

end
