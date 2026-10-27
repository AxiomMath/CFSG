module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs

public section

namespace CFSG.StandardType.ClassicalPosition.Block

@[expose] def IsPrimStarIdemIn {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (star : Matrix ι ι F → Matrix ι ι F) (A : Subalgebra F (Matrix ι ι F)) (ε : Matrix ι ι F) :
    Prop :=
  ε ∈ A ∧ IsIdempotentElem ε ∧ ε ≠ 0 ∧ star ε = ε ∧
    ∀ e' ∈ A, IsIdempotentElem e' → star e' = e' → e' * ε = e' → e' = 0 ∨ e' = ε

theorem isPrimStarIdemIn_id_iff {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : Subalgebra F (Matrix ι ι F)) (ε : Matrix ι ι F) :
    IsPrimStarIdemIn id A ε ↔ IsPrimIdemIn A ε := by
  simp [IsPrimStarIdemIn, IsPrimIdemIn]

theorem isPrimStarIdemIn_formAdj_iff {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (G : Matrix ι ι F) (A : Subalgebra F (Matrix ι ι F)) (ε : Matrix ι ι F) :
    IsPrimStarIdemIn (formAdj σ G) A ε ↔ IsPrimAdjIdemIn σ G A ε := by
  rfl

private lemma bd_mem_map_self {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : Subalgebra F (Matrix ι ι F)) (e : Matrix ι ι F) :
    e ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) := by
  rw [Submodule.mem_map]
  refine ⟨1, ?_, ?_⟩
  · simpa using A.one_mem
  · rw [LinearMap.mulRight_apply, one_mul]

private theorem bd_exists_aux {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (star : Matrix ι ι F → Matrix ι ι F) (A : Subalgebra F (Matrix ι ι F))
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hadd : ∀ a ∈ A, ∀ b ∈ A, star (a + b) = star a + star b) :
    ∀ k : ℕ, ∀ ε : Matrix ι ι F, ε ∈ A → IsIdempotentElem ε → star ε = ε →
      blockDegree A ε ≤ k →
      ∃ P : Finset (Matrix ι ι F), (∀ p ∈ P, IsPrimStarIdemIn star A p ∧ p * ε = p) ∧
        (∀ p ∈ P, ∀ q ∈ P, p ≠ q → p * q = 0) ∧ ∑ p ∈ P, p = ε := by
  classical
  intro k
  induction k with
  | zero =>
    intro ε hε hid hst hdeg
    have hdeg0 : blockDegree A ε = 0 := Nat.le_zero.mp hdeg
    have hbot : (Subalgebra.toSubmodule A).map (LinearMap.mulRight F ε) = ⊥ :=
      Submodule.finrank_eq_zero.mp hdeg0
    have hmem : ε ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F ε) :=
      bd_mem_map_self A ε
    rw [hbot] at hmem
    have hε0 : ε = 0 := by simpa using hmem
    refine ⟨∅, ?_, ?_, ?_⟩
    · simp
    · simp
    · rw [hε0]
      simp
  | succ k ih =>
    intro ε hε hid hst hdeg
    by_cases h0 : ε = 0
    · subst h0
      exact ⟨∅, by simp, by simp, by simp⟩
    by_cases hprim : IsPrimStarIdemIn star A ε
    · refine ⟨{ε}, ?_, ?_, ?_⟩
      · intro p hp
        rw [Finset.mem_singleton] at hp
        subst hp
        exact ⟨hprim, hid.eq⟩
      · intro p hp q hq hpq
        rw [Finset.mem_singleton] at hp hq
        subst hp
        subst hq
        exact (hpq rfl).elim
      · simp
    · have hforall : ¬ ∀ e' ∈ A, IsIdempotentElem e' → star e' = e' → e' * ε = e' →
          e' = 0 ∨ e' = ε := by
        intro h
        exact hprim ⟨hε, hid, h0, hst, h⟩
      push Not at hforall
      obtain ⟨e', he'A, hid', hste', he'εeq, he'0, he'ε⟩ := hforall
      set e'' : Matrix ι ι F := ε - e' with he''def
      have he''A : e'' ∈ A := by
        rw [he''def]
        exact A.sub_mem hε he'A
      have hee : ε * ε = ε := hid.eq
      have he'e' : e' * e' = e' := hid'.eq
      have hεe' : ε * e' = e' := by rw [hA ε hε e' he'A, he'εeq]
      have he''idem : IsIdempotentElem e'' := by
        rw [he''def]
        change (ε - e') * (ε - e') = ε - e'
        calc (ε - e') * (ε - e')
            = ε * (ε - e') - e' * (ε - e') := sub_mul _ _ _
          _ = (ε * ε - ε * e') - (e' * ε - e' * e') := by rw [mul_sub, mul_sub]
          _ = (ε - e') - (e' - e') := by rw [hee, hεe', he'εeq, he'e']
          _ = ε - e' := by rw [sub_self, sub_zero]
      have he'e'' : e' * e'' = 0 := by
        rw [he''def, mul_sub, he'εeq, he'e']
        exact sub_self e'
      have he''e' : e'' * e' = 0 := by
        rw [he''def, sub_mul, hεe', he'e']
        exact sub_self e'
      have he''eps : e'' * ε = e'' := by
        rw [he''def, sub_mul, hee, he'εeq]
      have heps_e'' : ε * e'' = e'' := by
        rw [he''def, mul_sub, hee, hεe']
      have hsum : e' + e'' = ε := by
        rw [he''def]
        exact add_sub_cancel e' ε
      have he''st : star e'' = e'' := by
        have h1 : star (e' + e'') = e' + e'' := by
          rw [hsum]
          exact hst
        rw [hadd e' he'A e'' he''A, hste'] at h1
        exact add_left_cancel h1
      have he''0 : e'' ≠ 0 := by
        intro h
        apply he'ε
        rw [he''def] at h
        exact (sub_eq_zero.mp h).symm
      have he''ε : e'' ≠ ε := by
        intro h
        apply he'0
        rw [he''def] at h
        exact sub_eq_self.mp h
      have he'_le : (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e') ≤
          (Subalgebra.toSubmodule A).map (LinearMap.mulRight F ε) := by
        intro x hx
        rw [Submodule.mem_map] at hx ⊢
        obtain ⟨a, ha, rfl⟩ := hx
        refine ⟨a * e', A.mul_mem ha he'A, ?_⟩
        rw [LinearMap.mulRight_apply, LinearMap.mulRight_apply, mul_assoc, he'εeq]
      have he'_not : ε ∉ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e') := by
        intro hmem
        rw [Submodule.mem_map] at hmem
        obtain ⟨a, ha, hae⟩ := hmem
        rw [LinearMap.mulRight_apply] at hae
        have hone : ε * e' = ε := by rw [← hae, mul_assoc, he'e']
        rw [hεe'] at hone
        exact he'ε hone
      have he'_lt : (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e') <
          (Subalgebra.toSubmodule A).map (LinearMap.mulRight F ε) := by
        refine lt_of_le_of_ne he'_le ?_
        intro hEq
        have hmem : ε ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F ε) :=
          bd_mem_map_self A ε
        rw [← hEq] at hmem
        exact he'_not hmem
      have hdeg_e' : blockDegree A e' ≤ k := by
        have hlt : blockDegree A e' < blockDegree A ε :=
          Submodule.finrank_lt_finrank_of_lt he'_lt
        omega
      have he''_le : (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e'') ≤
          (Subalgebra.toSubmodule A).map (LinearMap.mulRight F ε) := by
        intro x hx
        rw [Submodule.mem_map] at hx ⊢
        obtain ⟨a, ha, rfl⟩ := hx
        refine ⟨a * e'', A.mul_mem ha he''A, ?_⟩
        rw [LinearMap.mulRight_apply, LinearMap.mulRight_apply, mul_assoc, he''eps]
      have he''_not : ε ∉ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e'') := by
        intro hmem
        rw [Submodule.mem_map] at hmem
        obtain ⟨a, ha, hae⟩ := hmem
        rw [LinearMap.mulRight_apply] at hae
        have hone : ε * e'' = ε := by rw [← hae, mul_assoc, he''idem.eq]
        rw [heps_e''] at hone
        exact he''ε hone
      have he''_lt : (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e'') <
          (Subalgebra.toSubmodule A).map (LinearMap.mulRight F ε) := by
        refine lt_of_le_of_ne he''_le ?_
        intro hEq
        have hmem : ε ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F ε) :=
          bd_mem_map_self A ε
        rw [← hEq] at hmem
        exact he''_not hmem
      have hdeg_e'' : blockDegree A e'' ≤ k := by
        have hlt : blockDegree A e'' < blockDegree A ε :=
          Submodule.finrank_lt_finrank_of_lt he''_lt
        omega
      obtain ⟨P', hP'prim, hP'orth, hP'sum⟩ := ih e' he'A hid' hste' hdeg_e'
      obtain ⟨P'', hP''prim, hP''orth, hP''sum⟩ :=
        ih e'' he''A he''idem he''st hdeg_e''
      have hP'_e'' : ∀ p ∈ P', p * e'' = 0 := by
        intro p hp
        have hpe' : p * e' = p := (hP'prim p hp).2
        calc p * e'' = (p * e') * e'' := by rw [hpe']
          _ = p * (e' * e'') := by rw [mul_assoc]
          _ = p * 0 := by rw [he'e'']
          _ = 0 := by rw [mul_zero]
      have hP''_e' : ∀ p ∈ P'', p * e' = 0 := by
        intro p hp
        have hpe'' : p * e'' = p := (hP''prim p hp).2
        calc p * e' = (p * e'') * e' := by rw [hpe'']
          _ = p * (e'' * e') := by rw [mul_assoc]
          _ = p * 0 := by rw [he''e']
          _ = 0 := by rw [mul_zero]
      refine ⟨P' ∪ P'', ?_, ?_, ?_⟩
      · intro p hp
        rw [Finset.mem_union] at hp
        rcases hp with hp | hp
        · have h1 := hP'prim p hp
          refine ⟨h1.1, ?_⟩
          calc p * ε = (p * e') * ε := by rw [h1.2]
            _ = p * (e' * ε) := by rw [mul_assoc]
            _ = p * e' := by rw [he'εeq]
            _ = p := h1.2
        · have h1 := hP''prim p hp
          refine ⟨h1.1, ?_⟩
          calc p * ε = p * (e' + e'') := by rw [hsum]
            _ = p * e' + p * e'' := by rw [mul_add]
            _ = p * e' + p := by rw [h1.2]
            _ = 0 + p := by rw [hP''_e' p hp]
            _ = p := by rw [zero_add]
      · intro p hp q hq hpq
        rw [Finset.mem_union] at hp hq
        rcases hp with hp | hp <;> rcases hq with hq | hq
        · exact hP'orth p hp q hq hpq
        · have hp' : p * e' = p := (hP'prim p hp).2
          have hqA : q ∈ A := (hP''prim q hq).1.1
          calc p * q = (p * e') * q := by rw [hp']
            _ = p * (e' * q) := by rw [mul_assoc]
            _ = p * (q * e') := by rw [hA e' he'A q hqA]
            _ = p * 0 := by rw [hP''_e' q hq]
            _ = 0 := by rw [mul_zero]
        · have hp' : p * e' = 0 := hP''_e' p hp
          have hq' : q * e' = q := (hP'prim q hq).2
          have hqA : q ∈ A := (hP'prim q hq).1.1
          calc p * q = p * (q * e') := by rw [hq']
            _ = p * (e' * q) := by rw [hA e' he'A q hqA]
            _ = (p * e') * q := by rw [mul_assoc]
            _ = 0 * q := by rw [hp']
            _ = 0 := by rw [zero_mul]
        · exact hP''orth p hp q hq hpq
      · have hdisj : Disjoint P' P'' := by
          rw [Finset.disjoint_left]
          intro p hp' hp''
          have h1 : p * e' = p := (hP'prim p hp').2
          have h2 : p * e'' = p := (hP''prim p hp'').2
          have hp0 : p = 0 := by
            calc p = p * e'' := by rw [h2]
              _ = (p * e') * e'' := by rw [h1]
              _ = p * (e' * e'') := by rw [mul_assoc]
              _ = p * 0 := by rw [he'e'']
              _ = 0 := by rw [mul_zero]
          exact (hP'prim p hp').1.2.2.1 hp0
        calc ∑ p ∈ P' ∪ P'', p = ∑ p ∈ P', p + ∑ p ∈ P'', p :=
              Finset.sum_union hdisj
          _ = e' + e'' := by rw [hP'sum, hP''sum]
          _ = ε := hsum

theorem exists_finset_isPrimStarIdemIn_sum_eq {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (star : Matrix ι ι F → Matrix ι ι F) (A : Subalgebra F (Matrix ι ι F))
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hadd : ∀ a ∈ A, ∀ b ∈ A, star (a + b) = star a + star b) {ε : Matrix ι ι F} (hε : ε ∈ A)
    (hid : IsIdempotentElem ε) (hst : star ε = ε) :
    ∃ P : Finset (Matrix ι ι F), (∀ p ∈ P, IsPrimStarIdemIn star A p ∧ p * ε = p) ∧
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → p * q = 0) ∧ ∑ p ∈ P, p = ε := by
  classical
  exact bd_exists_aux star A hA hadd (blockDegree A ε) ε hε hid hst le_rfl

end CFSG.StandardType.ClassicalPosition.Block
