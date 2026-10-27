module

public import CFSG.Quasithin.Vol2.Ch10Reselect.ModelAlgId

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open Matrix

variable {K : Type*} [Field K]

@[expose] def lineAdd (K : Type*) [Field K] (w : Fin 2 → K) : AddSubgroup (UTilde K) where
  carrier := linePair K w
  add_mem' := by
    rintro _ _ ⟨v, rfl⟩ ⟨v', rfl⟩
    exact ⟨v + v', by simp [smul_add]⟩
  zero_mem' := ⟨0, by simp only [smul_zero]; rfl⟩
  neg_mem' := by
    rintro _ ⟨v, rfl⟩
    exact ⟨-v, by simp [smul_neg]⟩

theorem mem_lineAdd_iff {w : Fin 2 → K} {p : UTilde K} : p ∈ lineAdd K w ↔ p ∈ linePair K w :=
  Iff.rfl

private def natE12 (a : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩

private def natE21 (a : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two]⟩

private lemma natE12_mulVec (a : K) (u : Fin 2 → K) :
    (natE12 a : Matrix (Fin 2) (Fin 2) K) *ᵥ u = ![u 0 + a * u 1, u 1] := by
  funext i
  fin_cases i <;> simp [natE12, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma natE21_mulVec (a : K) (u : Fin 2 → K) :
    (natE21 a : Matrix (Fin 2) (Fin 2) K) *ᵥ u = ![u 0, a * u 0 + u 1] := by
  funext i
  fin_cases i <;> simp [natE21, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma natE12_mulVec_sub (a : K) (u : Fin 2 → K) :
    (natE12 a : Matrix (Fin 2) (Fin 2) K) *ᵥ u - u = (a * u 1) • (![1, 0] : Fin 2 → K) := by
  rw [natE12_mulVec]
  funext i
  fin_cases i <;> simp

private lemma natE21_mulVec_sub (a : K) (u : Fin 2 → K) :
    (natE21 a : Matrix (Fin 2) (Fin 2) K) *ᵥ u - u = (a * u 0) • (![0, 1] : Fin 2 → K) := by
  rw [natE21_mulVec]
  funext i
  fin_cases i <;> simp

private lemma rhoSL_sub_smul (g : Matrix.SpecialLinearGroup (Fin 2) K) (w u : Fin 2 → K) :
    rhoSL K g (w 0 • u, w 1 • u) - (w 0 • u, w 1 • u) =
      (w 0 • ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ u - u),
        w 1 • ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ u - u)) := by
  simp only [rhoSL_apply, Matrix.mulVec_smul, Prod.mk_sub_mk, smul_sub]

private lemma natE_basis (u : Fin 2 → K) :
    u = u 0 • (![1, 0] : Fin 2 → K) + u 1 • (![0, 1] : Fin 2 → K) := by
  funext i
  fin_cases i <;> simp

private lemma line_decomp (w u : Fin 2 → K) :
    (w 0 • u, w 1 • u) =
      (w 0 • (u 0 • (![1, 0] : Fin 2 → K)), w 1 • (u 0 • (![1, 0] : Fin 2 → K))) +
        (w 0 • (u 1 • (![0, 1] : Fin 2 → K)), w 1 • (u 1 • (![0, 1] : Fin 2 → K))) := by
  rw [Prod.mk_add_mk, ← smul_add, ← smul_add, ← natE_basis u]

private lemma natE_fixed_zero (u : Fin 2 → K)
    (ha : (natE12 (1 : K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u = u)
    (hb : (natE21 (1 : K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u = u) : u = 0 := by
  have hu1 : u 1 = 0 := by
    have h := congrFun ha 0
    rw [natE12_mulVec] at h
    simp only [Matrix.cons_val_zero] at h
    linear_combination h
  have hu0 : u 0 = 0 := by
    have h := congrFun hb 1
    rw [natE21_mulVec] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    linear_combination h
  funext i
  fin_cases i
  · exact hu0
  · exact hu1

theorem rhoSL_fixed_eq_zero [Nontrivial K] {p : UTilde K}
    (h : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, rhoSL K g p = p) : p = 0 := by
  have h1 := h (natE12 (1 : K))
  have h2 := h (natE21 (1 : K))
  rw [rhoSL_apply] at h1 h2
  exact Prod.ext (natE_fixed_zero p.1 (congrArg Prod.fst h1) (congrArg Prod.fst h2))
    (natE_fixed_zero p.2 (congrArg Prod.snd h1) (congrArg Prod.snd h2))

theorem rhoSL_mem_lineAdd (g : Matrix.SpecialLinearGroup (Fin 2) K) {w : Fin 2 → K}
    {p : UTilde K} (hp : p ∈ lineAdd K w) : rhoSL K g p ∈ lineAdd K w := by
  obtain ⟨v, rfl⟩ := mem_lineAdd_iff.mp hp
  refine mem_lineAdd_iff.mpr ⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ v, ?_⟩
  simp only [rhoSL_apply, Matrix.mulVec_smul]

theorem lineAdd_irreducible [Nontrivial K] {w : Fin 2 → K} (hw : w ≠ 0) (S : AddSubgroup (UTilde K))
    (hS : S ≤ lineAdd K w)
    (hinv : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (p : UTilde K), p ∈ S → rhoSL K g p ∈ S) :
    S = ⊥ ∨ S = lineAdd K w := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨p, hpS, hp0⟩ : ∃ p ∈ S, p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hbot ((AddSubgroup.eq_bot_iff_forall S).mpr hcon)
  obtain ⟨v, rfl⟩ := mem_lineAdd_iff.mp (hS hpS)
  have hT : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (u : Fin 2 → K),
      (w 0 • u, w 1 • u) ∈ S →
        (w 0 • ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ u - u),
          w 1 • ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ u - u)) ∈ S := by
    intro g u hu
    have h1 := S.sub_mem (hinv g _ hu) hu
    rwa [rhoSL_sub_smul] at h1
  have hA : ∀ (a : K) (u : Fin 2 → K), (w 0 • u, w 1 • u) ∈ S →
      (w 0 • ((a * u 1) • (![1, 0] : Fin 2 → K)), w 1 • ((a * u 1) • (![1, 0] : Fin 2 → K))) ∈ S := by
    intro a u hu
    have h1 := hT (natE12 a) u hu
    rwa [natE12_mulVec_sub] at h1
  have hB : ∀ (a : K) (u : Fin 2 → K), (w 0 • u, w 1 • u) ∈ S →
      (w 0 • ((a * u 0) • (![0, 1] : Fin 2 → K)), w 1 • ((a * u 0) • (![0, 1] : Fin 2 → K))) ∈ S := by
    intro a u hu
    have h1 := hT (natE21 a) u hu
    rwa [natE21_mulVec_sub] at h1
  have hv : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hp0
    have hv0 : v = 0 := by
      funext i
      fin_cases i
      · exact hcon.1
      · exact hcon.2
    rw [hv0]
    simp
  have hE : (w 0 • (![1, 0] : Fin 2 → K), w 1 • (![1, 0] : Fin 2 → K)) ∈ S ∧
      (w 0 • (![0, 1] : Fin 2 → K), w 1 • (![0, 1] : Fin 2 → K)) ∈ S := by
    by_cases h1 : v 1 = 0
    · have h0 : v 0 ≠ 0 := hv.resolve_right (fun hne => hne h1)
      have hE1 : (w 0 • (![0, 1] : Fin 2 → K), w 1 • (![0, 1] : Fin 2 → K)) ∈ S := by
        have h := hB (v 0)⁻¹ v hpS
        rwa [inv_mul_cancel₀ h0, one_smul] at h
      refine ⟨?_, hE1⟩
      have h := hA 1 (![0, 1] : Fin 2 → K) hE1
      simpa using h
    · have hE0 : (w 0 • (![1, 0] : Fin 2 → K), w 1 • (![1, 0] : Fin 2 → K)) ∈ S := by
        have h := hA (v 1)⁻¹ v hpS
        rwa [inv_mul_cancel₀ h1, one_smul] at h
      refine ⟨hE0, ?_⟩
      have h := hB 1 (![1, 0] : Fin 2 → K) hE0
      simpa using h
  obtain ⟨hE0, hE1⟩ := hE
  have hall0 : ∀ c : K,
      (w 0 • (c • (![1, 0] : Fin 2 → K)), w 1 • (c • (![1, 0] : Fin 2 → K))) ∈ S := by
    intro c
    have h := hA c (![0, 1] : Fin 2 → K) hE1
    simpa using h
  have hall1 : ∀ c : K,
      (w 0 • (c • (![0, 1] : Fin 2 → K)), w 1 • (c • (![0, 1] : Fin 2 → K))) ∈ S := by
    intro c
    have h := hB c (![1, 0] : Fin 2 → K) hE0
    simpa using h
  refine le_antisymm hS ?_
  intro q hq
  obtain ⟨u, rfl⟩ := mem_lineAdd_iff.mp hq
  rw [line_decomp w u]
  exact S.add_mem (hall0 (u 0)) (hall1 (u 1))

theorem lineAdd_perfect [Nontrivial K] {w : Fin 2 → K} (hw : w ≠ 0) :
    AddSubgroup.closure {x : UTilde K | ∃ (g : Matrix.SpecialLinearGroup (Fin 2) K)
      (p : UTilde K), p ∈ lineAdd K w ∧ x = rhoSL K g p - p} = lineAdd K w := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro x ⟨g, p, hp, rfl⟩
    exact AddSubgroup.sub_mem _ (rhoSL_mem_lineAdd g hp) hp
  · intro q hq
    obtain ⟨u, rfl⟩ := mem_lineAdd_iff.mp hq
    have hA : ∀ c : K, (w 0 • (c • (![1, 0] : Fin 2 → K)), w 1 • (c • (![1, 0] : Fin 2 → K))) ∈
        AddSubgroup.closure {x : UTilde K | ∃ (g : Matrix.SpecialLinearGroup (Fin 2) K)
          (p : UTilde K), p ∈ lineAdd K w ∧ x = rhoSL K g p - p} := by
      intro c
      apply AddSubgroup.subset_closure
      refine ⟨natE12 c, (w 0 • (![0, 1] : Fin 2 → K), w 1 • (![0, 1] : Fin 2 → K)),
        mem_lineAdd_iff.mpr ⟨(![0, 1] : Fin 2 → K), rfl⟩, ?_⟩
      rw [rhoSL_sub_smul (natE12 c) w (![0, 1] : Fin 2 → K), natE12_mulVec_sub]
      simp
    have hB : ∀ c : K, (w 0 • (c • (![0, 1] : Fin 2 → K)), w 1 • (c • (![0, 1] : Fin 2 → K))) ∈
        AddSubgroup.closure {x : UTilde K | ∃ (g : Matrix.SpecialLinearGroup (Fin 2) K)
          (p : UTilde K), p ∈ lineAdd K w ∧ x = rhoSL K g p - p} := by
      intro c
      apply AddSubgroup.subset_closure
      refine ⟨natE21 c, (w 0 • (![1, 0] : Fin 2 → K), w 1 • (![1, 0] : Fin 2 → K)),
        mem_lineAdd_iff.mpr ⟨(![1, 0] : Fin 2 → K), rfl⟩, ?_⟩
      rw [rhoSL_sub_smul (natE21 c) w (![1, 0] : Fin 2 → K), natE21_mulVec_sub]
      simp
    rw [line_decomp w u]
    exact AddSubgroup.add_mem _ (hA (u 0)) (hB (u 1))

theorem card_lineAdd [Finite K] {w : Fin 2 → K} (hw : w ≠ 0) :
    Nat.card (lineAdd K w) = Nat.card K ^ 2 := by
  let f : (Fin 2 → K) → lineAdd K w := fun u => ⟨(w 0 • u, w 1 • u), mem_lineAdd_iff.mpr ⟨u, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u u' huu
      have h : (w 0 • u, w 1 • u) = (w 0 • u', w 1 • u') := congrArg Subtype.val huu
      have h0 : w 0 • u = w 0 • u' := (Prod.mk.inj h).1
      have h1 : w 1 • u = w 1 • u' := (Prod.mk.inj h).2
      have key : ∀ j, w j • u = w j • u' := by
        intro j
        fin_cases j
        · exact h0
        · exact h1
      obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hw (funext hcon)
      have hu : (w i)⁻¹ • (w i • u) = (w i)⁻¹ • (w i • u') := by rw [key i]
      rwa [inv_smul_smul₀ hi, inv_smul_smul₀ hi] at hu
    · rintro ⟨p, hp⟩
      obtain ⟨u, rfl⟩ := mem_lineAdd_iff.mp hp
      exact ⟨u, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fun, Nat.card_fin]

theorem card_uTilde [Finite K] : Nat.card (UTilde K) = Nat.card K ^ 4 := by
  show Nat.card ((Fin 2 → K) × (Fin 2 → K)) = Nat.card K ^ 4
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fin]
  ring

end CFSG.Quasithin.Vol2.Ch10Reselect
