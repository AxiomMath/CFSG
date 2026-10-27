module

public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneShapes

public section

namespace CFSG.StandardType.GGQ2Frame.PlaneRaw

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def ExtPosition (kd : PlaneKind) {t : ℕ} (vx : V t) (ℓ : Code t)
    (U : Submodule F (V t)) (j : Code t) (z : V t) (k : Code t) : Prop :=
  vx ≠ 0 ∧ occurs (Submodule.span F {vx}) ℓ ∧ cent kd ℓ = Submodule.span F {vx} ∧
    vx ∉ inside kd ℓ ∧ finrank F U = 2 ∧ vx ∈ U ∧ occurs U j ∧ cent kd j = U ∧
    inside kd j ≤ inside kd ℓ ∧ z ∈ U ∧ z ∉ Submodule.span F {vx} ∧
    occurs (Submodule.span F {z}) k ∧ cent kd k = Submodule.span F {z} ∧ vx ∉ cent kd k ∧
    inside kd j ≤ inside kd k

@[expose] def ExtShapeA1 {t : ℕ} (vx : V t) (ℓ : Code t) (U : Submodule F (V t)) (j : Code t)
    (z : V t) (k : Code t) : Prop :=
  ∃ (a c : Fin t) (s s' : F), a ≠ c ∧ s ≠ 0 ∧ s' ≠ 0 ∧ vx = s • unitVec t a ∧
    z = s' • unitVec t c ∧ ℓ = .zero (Finset.univ.erase a) ∧ j = .zero (Finset.univ \ {a, c}) ∧
    k = .zero (Finset.univ.erase c) ∧ U = Submodule.span F {unitVec t a, unitVec t c}

@[expose] def ExtShapeA2 {t : ℕ} (vx : V t) (ℓ : Code t) (U : Submodule F (V t)) (j : Code t)
    (z : V t) (k : Code t) : Prop :=
  ∃ (a : Fin t) (e' : V t) (s β σ ε : F), s ≠ 0 ∧ β ≠ 0 ∧ σ ≠ 0 ∧ ε ≠ 0 ∧ e' a = 0 ∧
    (∀ i, i ≠ a → e' i ≠ 0) ∧ vx = s • unitVec t a ∧ ℓ = .zero (Finset.univ.erase a) ∧
    j = .extension e' ∧ U = Submodule.span F {unitVec t a, e'} ∧
    z = β • (e' + σ • unitVec t a) ∧ k = .extension (ε • (e' + σ • unitVec t a))

@[expose] def ExtShapeB2a {t : ℕ} (vx : V t) (ℓ : Code t) (U : Submodule F (V t)) (j : Code t)
    (z : V t) (k : Code t) : Prop :=
  ∃ (b : Fin t) (e' : V t) (μ ε σ β : F), μ ≠ 0 ∧ ε ≠ 0 ∧ σ ≠ 0 ∧ β ≠ 0 ∧ e' b = 0 ∧
    (∀ i, i ≠ b → e' i ≠ 0) ∧ vx = μ • (e' + σ • unitVec t b) ∧
    ℓ = .extension (ε • (e' + σ • unitVec t b)) ∧ j = .extension e' ∧
    U = Submodule.span F {unitVec t b, e'} ∧ z = β • unitVec t b ∧
    k = .zero (Finset.univ.erase b)

@[expose] def ExtShapeB2b {t : ℕ} (vx : V t) (ℓ : Code t) (U : Submodule F (V t)) (j : Code t)
    (z : V t) (k : Code t) : Prop :=
  ∃ (b : Fin t) (e' : V t) (μ ε ε' σ β : F), μ ≠ 0 ∧ ε ≠ 0 ∧ ε' ≠ 0 ∧ σ ≠ 0 ∧ β ≠ 0 ∧
    e' b = 0 ∧ (∀ i, i ≠ b → e' i ≠ 0) ∧ vx = μ • (e' + σ • unitVec t b) ∧
    ℓ = .extension (ε • (e' + σ • unitVec t b)) ∧ j = .extension e' ∧
    U = Submodule.span F {unitVec t b, e'} ∧ z = β • (e' - σ • unitVec t b) ∧
    k = .extension (ε' • (e' - σ • unitVec t b))

theorem exists_ne_two {t : ℕ} (ht : 3 ≤ t) (a c : Fin t) : ∃ i : Fin t, i ≠ a ∧ i ≠ c := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset (Fin t)) ⊆ {a, c} := fun i _ => by
    by_cases hia : i = a
    · simp [hia]
    · simp [hcon i hia]
  have h1 := Finset.card_le_card hsub
  have h2 : ({a, c} : Finset (Fin t)).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem vanish_of_mem_span_pair {t : ℕ} {b c : Fin t} {v : V t}
    (h : v ∈ Submodule.span F {unitVec t b, unitVec t c}) {i : Fin t} (hb : i ≠ b) (hc : i ≠ c) :
    v i = 0 := by
  obtain ⟨x, y, rfl⟩ := Submodule.mem_span_pair.mp h
  simp [unitVec, Pi.single_apply, hb, hc]

theorem unit_mem_span_pair {t : ℕ} {b c d : Fin t} {s : F} (hs : s ≠ 0)
    (h : s • unitVec t d ∈ Submodule.span F {unitVec t b, unitVec t c}) : d = b ∨ d = c := by
  by_contra hcon
  push Not at hcon
  have := vanish_of_mem_span_pair h hcon.1 hcon.2
  simp [unitVec, hs] at this

theorem full_not_mem_span_pair {t : ℕ} (ht : 3 ≤ t) {b c : Fin t} {v : V t} (hv : ∀ i, v i ≠ 0) :
    v ∉ Submodule.span F {unitVec t b, unitVec t c} := fun h => by
  obtain ⟨i, hib, hic⟩ := exists_ne_two ht b c
  exact hv i (vanish_of_mem_span_pair h hib hic)

theorem smul_unit_mem_span {t : ℕ} {a : Fin t} {s s'' : F} (hs : s ≠ 0) :
    s'' • unitVec t a ∈ Submodule.span F {s • unitVec t a} :=
  Submodule.mem_span_singleton.mpr ⟨s'' * s⁻¹, by
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hs, mul_one]⟩

theorem unit_mem_span_ext {t : ℕ} (ht : 3 ≤ t) {b : Fin t} {e' : V t} (he'i : ∀ i, i ≠ b → e' i ≠ 0)
    {c : Fin t} {s : F} (hs : s ≠ 0) (h : s • unitVec t c ∈ Submodule.span F {unitVec t b, e'}) :
    c = b := by
  obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.mp h
  obtain ⟨i, hib, hic⟩ := exists_ne_two ht b c
  have hy : y = 0 := by
    have := congrFun hxy i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitVec, Pi.single_apply, hib, hic,
      if_false, mul_zero, zero_add] at this
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd h0 (he'i i hib)
  by_contra hcb
  have := congrFun hxy c
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitVec, Pi.single_apply, hcb, if_false,
    if_true, mul_zero, zero_add, hy, mul_one, zero_mul] at this
  exact hs this.symm

theorem full_mem_span_ext {t : ℕ} (ht : 3 ≤ t) {b : Fin t} {e' : V t} (he'b : e' b = 0)
    (he'i : ∀ i, i ≠ b → e' i ≠ 0) {v : V t} (hv : ∀ i, v i ≠ 0)
    (h : v ∈ Submodule.span F {unitVec t b, e'}) :
    ∃ μ σ : F, μ ≠ 0 ∧ σ ≠ 0 ∧ v = μ • (e' + σ • unitVec t b) := by
  obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.mp h
  have hx : x ≠ 0 := by
    intro hx0
    apply hv b
    rw [← hxy]
    simp [unitVec, he'b, hx0]
  have hy : y ≠ 0 := by
    intro hy0
    obtain ⟨i, hib, -⟩ := exists_ne_two ht b b
    apply hv i
    rw [← hxy]
    simp [unitVec, Pi.single_apply, hib, hy0]
  refine ⟨y, x * y⁻¹, hy, mul_ne_zero hx (inv_ne_zero hy), ?_⟩
  rw [← hxy]
  funext i
  by_cases hi : i = b
  · subst hi
    simp [unitVec, he'b]
    field_simp
  · simp [unitVec, Pi.single_apply, hi]

theorem eq_neg_of_ne {σ τ : F} (hσ : σ ≠ 0) (hτ : τ ≠ 0) (h : τ ≠ σ) : τ = -σ := by
  revert σ τ
  decide

private theorem l08tpp_ext_eq_smul {t : ℕ} {v w : V t} {c : Code t}
    (h : c = .extension v ∨ c = .extension (-v)) {μ : F} (hμ : μ ≠ 0) (hv : v = μ • w) :
    ∃ ε : F, ε ≠ 0 ∧ c = .extension (ε • w) := by
  rcases h with h | h
  · exact ⟨μ, hμ, by rw [h, hv]⟩
  · exact ⟨-μ, by simpa using hμ, by rw [h, hv, neg_smul]⟩

theorem extPlaneShape_of_position (hL : LineShapes) (hP : PlaneShapes) (kd : PlaneKind) {t : ℕ}
    (ht : 4 ≤ t) {vx : V t} {ℓ : Code t} {U : Submodule F (V t)} {j : Code t} {z : V t}
    {k : Code t} (h : ExtPosition kd vx ℓ U j z k) :
    ExtShapeA1 vx ℓ U j z k ∨ ExtShapeA2 vx ℓ U j z k ∨ ExtShapeB2a vx ℓ U j z k ∨
      ExtShapeB2b vx ℓ U j z k := by
  obtain ⟨hvx0, hℓocc, hℓcent, -, hU, hvxU, hjocc, hjcent, -, hzU, hzvx, hkocc, hkcent, -, -⟩ := h
  have hz0 : z ≠ 0 := fun h0 => hzvx (h0 ▸ Submodule.zero_mem _)
  have ht3 : 3 ≤ t := by omega
  rcases hL t kd vx ℓ hvx0 hℓocc hℓcent with ⟨a, s, hs, hvxa, hℓ⟩ | ⟨hfull, hℓ⟩
  ·
    rcases hP t kd U j hU hjocc hjcent with ⟨b, c, hbc, hUbc, hj⟩ | ⟨b, e', he'b, he'i, hj, hUb⟩
    ·
      rw [hvxa, hUbc] at hvxU
      have habc := unit_mem_span_pair hs hvxU
      obtain ⟨c₁, hac, hUc, hjc⟩ : ∃ c₁, a ≠ c₁ ∧ U = Submodule.span F {unitVec t a, unitVec t c₁} ∧
          j = Code.zero (Finset.univ \ {a, c₁}) := by
        rcases habc with hab | hac
        · subst hab
          exact ⟨c, hbc, hUbc, hj⟩
        · subst hac
          exact ⟨b, hbc.symm, by rw [hUbc, Set.pair_comm], by rw [hj, Finset.pair_comm]⟩
      rcases hL t kd z k hz0 hkocc hkcent with ⟨c', s'', hs'', hzc, hk⟩ | ⟨hzfull, hk⟩
      · rw [hzc, hUc] at hzU
        rcases unit_mem_span_pair hs'' hzU with hca | hcc
        · exfalso
          apply hzvx
          rw [hzc, hca, hvxa]
          exact smul_unit_mem_span hs
        · subst hcc
          exact Or.inl ⟨a, c', s, s'', hac, hs, hs'', hvxa, hzc, hℓ, hjc, hk, hUc⟩
      · exact absurd (hUc ▸ hzU) (full_not_mem_span_pair ht3 hzfull)
    ·
      have hmem_a : s • unitVec t a ∈ Submodule.span F {unitVec t b, e'} := by
        simpa [hvxa, hUb] using hvxU
      have hab : a = b := unit_mem_span_ext ht3 he'i hs hmem_a
      have he'a : e' a = 0 := by rw [hab]; exact he'b
      have he'ia : ∀ i, i ≠ a → e' i ≠ 0 := fun i hi => he'i i (fun hib => hi (hib.trans hab.symm))
      have hUa : U = Submodule.span F {unitVec t a, e'} := by rw [hUb, ← hab]
      rcases hL t kd z k hz0 hkocc hkcent with ⟨c', s'', hs'', hzc, hk⟩ | ⟨hzfull, hk⟩
      ·
        have hmem_z : s'' • unitVec t c' ∈ Submodule.span F {unitVec t b, e'} := by
          simpa [hzc, hUb] using hzU
        have hcb : c' = b := unit_mem_span_ext ht3 he'i hs'' hmem_z
        exfalso
        apply hzvx
        rw [hzc, hcb, hvxa, hab]
        exact smul_unit_mem_span hs
      ·
        have hmem_z : z ∈ Submodule.span F {unitVec t b, e'} := by
          simpa [hUb] using hzU
        obtain ⟨μ, σ, hμ, hσ, hz_eq⟩ := full_mem_span_ext ht3 he'b he'i hzfull hmem_z
        obtain ⟨ε, hε, hkε⟩ := l08tpp_ext_eq_smul hk hμ hz_eq
        have hz_eq_a : z = μ • (e' + σ • unitVec t a) := by rw [hz_eq, ← hab]
        have hkε_a : k = .extension (ε • (e' + σ • unitVec t a)) := by rw [hkε, ← hab]
        exact Or.inr (Or.inl ⟨a, e', s, μ, σ, ε, hs, hμ, hσ, hε, he'a, he'ia, hvxa, hℓ, hj,
          hUa, hz_eq_a, hkε_a⟩)
  ·
    rcases hP t kd U j hU hjocc hjcent with ⟨b, c, hbc, hUbc, hj⟩ | ⟨b, e', he'b, he'i, hj, hUb⟩
    · exact absurd (hUbc ▸ hvxU) (full_not_mem_span_pair ht3 hfull)
    · have hmem_vx : vx ∈ Submodule.span F {unitVec t b, e'} := by
        simpa [hUb] using hvxU
      obtain ⟨μ, σ, hμ, hσ, hvx_eq⟩ := full_mem_span_ext ht3 he'b he'i hfull hmem_vx
      obtain ⟨ε, hε, hℓε⟩ := l08tpp_ext_eq_smul hℓ hμ hvx_eq
      rcases hL t kd z k hz0 hkocc hkcent with ⟨c', s'', hs'', hzc, hk⟩ | ⟨hzfull, hk⟩
      ·
        have hmem_z : s'' • unitVec t c' ∈ Submodule.span F {unitVec t b, e'} := by
          simpa [hzc, hUb] using hzU
        have hcb : c' = b := unit_mem_span_ext ht3 he'i hs'' hmem_z
        have hzc_b : z = s'' • unitVec t b := by rw [hzc, hcb]
        have hk_b : k = .zero (Finset.univ.erase b) := by rw [hk, hcb]
        exact Or.inr (Or.inr (Or.inl ⟨b, e', μ, ε, σ, s'', hμ, hε, hσ, hs'', he'b, he'i,
          hvx_eq, hℓε, hj, hUb, hzc_b, hk_b⟩))
      ·
        have hmem_z : z ∈ Submodule.span F {unitVec t b, e'} := by
          simpa [hUb] using hzU
        obtain ⟨μ', τ, hμ', hτ, hz_eq⟩ := full_mem_span_ext ht3 he'b he'i hzfull hmem_z
        have hτσ : τ ≠ σ := by
          intro hτσ
          apply hzvx
          rw [hz_eq, hτσ, hvx_eq]
          exact Submodule.mem_span_singleton.mpr ⟨μ' * μ⁻¹, by
            rw [smul_smul, mul_assoc, inv_mul_cancel₀ hμ, mul_one]⟩
        have hτeq : τ = -σ := eq_neg_of_ne hσ hτ hτσ
        have hz_eq' : z = μ' • (e' - σ • unitVec t b) := by
          rw [hz_eq, hτeq, neg_smul, sub_eq_add_neg]
        obtain ⟨ε', hε', hkε'⟩ := l08tpp_ext_eq_smul hk hμ' hz_eq'
        exact Or.inr (Or.inr (Or.inr ⟨b, e', μ, ε, ε', σ, μ', hμ, hε, hε', hσ, hμ', he'b, he'i,
          hvx_eq, hℓε, hj, hUb, hz_eq', hkε'⟩))

end

end CFSG.StandardType.GGQ2Frame.PlaneRaw
