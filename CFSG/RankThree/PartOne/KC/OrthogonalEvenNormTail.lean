module

public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.GroupTheory.WeirSylow

section Defs

variable (K : Type) [Field K]

@[expose] noncomputable def hyperbolicPairsForm (r : ℕ) :
    QuadraticForm K ((Fin r → K) × (Fin r → K)) :=
  (quadPlus r K).comp (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin r) K K).symm.toLinearMap

theorem hyperbolicPairsForm_apply {r : ℕ} (x y : Fin r → K) :
    hyperbolicPairsForm K r (x, y) = ∑ i, x i * y i := by
  simp [hyperbolicPairsForm, quadPlus_apply, LinearEquiv.sumArrowLequivProdArrow]

variable {K} {E : Type} [Field E] [Algebra K E]

@[expose] noncomputable def evenNormTailForm (N : QuadraticForm K E) (r : ℕ) :
    QuadraticForm K (((Fin r → K) × (Fin r → K)) × E) :=
  (hyperbolicPairsForm K r).prod N

theorem evenNormTailForm_apply (N : QuadraticForm K E) {r : ℕ} (x y : Fin r → K) (z : E) :
    evenNormTailForm N r ((x, y), z) = ∑ i, x i * y i + N z := by
  rw [evenNormTailForm, QuadraticMap.prod_apply, hyperbolicPairsForm_apply]

end Defs

section Isometry

variable {K : Type} [Field K] {E : Type} [Field E] [Algebra K E]

@[expose] noncomputable def evenNormTailSplit {N : QuadraticForm K E} {b c : K}
    (θ : (binForm b c).IsometryEquiv N) (r : ℕ) :
    (evenNormTailForm N r).IsometryEquiv ((quadPlus r K).prod (binForm b c)) where
  toLinearEquiv := LinearEquiv.prodCongr
    (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin r) K K).symm θ.symm.toLinearEquiv
  map_app' := fun v => by
    obtain ⟨⟨x, y⟩, z⟩ := v
    change quadPlus r K (Sum.elim x y) + binForm b c (θ.symm z) = evenNormTailForm N r ((x, y), z)
    rw [evenNormTailForm_apply, quadPlus_apply]
    simp only [Sum.elim_inl, Sum.elim_inr]
    congr 1
    have := θ.map_app (θ.symm z)
    rw [QuadraticMap.IsometryEquiv.apply_symm_apply] at this
    exact this.symm

@[expose] noncomputable def evenNormTailIsometry {N : QuadraticForm K E} {b c : K}
    (θ : (binForm b c).IsometryEquiv N) (r : ℕ) :
    (evenNormTailForm N r).IsometryEquiv (quadMinus (r + 1) K b c) :=
  (evenNormTailSplit θ r).trans (quadMinusIsometry (r + 1) b c).symm

end Isometry

section Counting

variable {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [Field E] [Algebra K E]
  {N : QuadraticForm K E} {b c : K}

omit [CharP K 2] in
theorem evenNormTail_nondegenerate (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (θ : (binForm b c).IsometryEquiv N) (r : ℕ) :
    (polarBilin (evenNormTailForm N r)).Nondegenerate :=
  nondegenerate_polarBilin_of_isometryEquiv (evenNormTailIsometry θ r).symm
    (nondegenerate_polarBilin_quadMinus_of_finite (r + 1) K hirr)

omit [Finite K] [CharP K 2] in
theorem polar_isometryEquiv {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (e : Q.IsometryEquiv Q')
    (a a' : V) : polar Q' (e a) (e a') = polar Q a a' := by
  simp only [polar, ← map_add, e.map_app]

omit [Finite K] [CharP K 2] in
theorem card_nonzero_singular_add_one {V : Type*} [AddCommGroup V] [Module K V] [Finite V]
    (Q : QuadraticForm K V) :
    Nat.card {v // Q v = 0 ∧ v ≠ 0} + 1 = Nat.card {v // Q v = 0} := by
  classical
  have := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  have hsplit : Finset.univ.filter (fun x : V => Q x = 0) =
      insert 0 (Finset.univ.filter fun x : V => Q x = 0 ∧ x ≠ 0) := by
    ext x
    by_cases hx : x = 0 <;> simp [hx]
  rw [hsplit, Finset.card_insert_of_notMem (by simp)]

end Counting

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [Field E] [Algebra K E]
  {N : QuadraticForm K E} {b c : K}

omit [CharP K 2] in
theorem finite_evenNormTailSpace (θ : (binForm b c).IsometryEquiv N) (r : ℕ) :
    Finite (((Fin r → K) × (Fin r → K)) × E) :=
  Finite.of_equiv _ (evenNormTailIsometry θ r).toLinearEquiv.symm.toEquiv

theorem card_nonzero_singular_evenNormTail (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (θ : (binForm b c).IsometryEquiv N) (r : ℕ) :
    Nat.card {v // evenNormTailForm N r v = 0 ∧ v ≠ 0} =
      (Nat.card K ^ r - 1) * (Nat.card K ^ (r + 1) + 1) := by
  have := finite_evenNormTailSpace θ r
  have h1 := card_nonzero_singular_add_one (evenNormTailForm N r)
  have h2 := CFSG.Timmesfeld.ClassicalOrders.card_singular_congr (evenNormTailIsometry θ r)
  have h3 := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus r hirr).1
  rw [← h2] at h3
  have hq : 1 ≤ Nat.card K ^ r := Nat.one_le_pow _ _ Nat.card_pos
  have h1' : (Nat.card {v // evenNormTailForm N r v = 0 ∧ v ≠ 0} : ℤ) + 1 =
      Nat.card {v // evenNormTailForm N r v = 0} := by exact_mod_cast h1
  zify [hq]
  linear_combination h1' + h3

theorem card_partners_evenNormTail (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (θ : (binForm b c).IsometryEquiv N) (r : ℕ) {e : ((Fin r → K) × (Fin r → K)) × E}
    (he : evenNormTailForm N r e = 0) (he0 : e ≠ 0) :
    Nat.card {f // evenNormTailForm N r f = 0 ∧ polar (evenNormTailForm N r) e f = 1} =
      Nat.card K ^ (2 * r) := by
  have := finite_evenNormTailSpace θ r
  obtain _ | m := r
  · exfalso
    have h := card_nonzero_singular_evenNormTail hirr θ 0
    have h0 : Nat.card {v // evenNormTailForm N 0 v = 0 ∧ v ≠ 0} = 0 := by rw [h]; simp
    have hpos : 0 < Nat.card {v // evenNormTailForm N 0 v = 0 ∧ v ≠ 0} :=
      Nat.card_pos_iff.mpr ⟨⟨⟨e, he, he0⟩⟩, inferInstance⟩
    omega
  · set Ψ := (evenNormTailIsometry θ (m + 1)).trans
      (CFSG.Timmesfeld.ClassicalOrders.minusIsometry K m b c) with hΨ
    have hQ' := nondegenerate_polarBilin_quadMinus_of_finite (m + 1) K hirr
    have hx : CFSG.Timmesfeld.ClassicalOrders.hypSum (quadMinus (m + 1) K b c) (Ψ e) = 0 := by
      rw [Ψ.map_app]
      exact he
    have hx0 : Ψ e ≠ 0 := fun h => he0 (by simpa using congrArg Ψ.symm h)
    have key := CFSG.Timmesfeld.ClassicalOrders.card_partners hQ' CharTwo.two_eq_zero hx hx0
    have hcard : Nat.card {f // evenNormTailForm N (m + 1) f = 0 ∧
        polar (evenNormTailForm N (m + 1)) e f = 1} =
        Nat.card {y // CFSG.Timmesfeld.ClassicalOrders.hypSum (quadMinus (m + 1) K b c) y = 0 ∧
          polar (CFSG.Timmesfeld.ClassicalOrders.hypSum (quadMinus (m + 1) K b c)) (Ψ e) y = 1} :=
      Nat.card_congr (Equiv.subtypeEquiv Ψ.toLinearEquiv.toEquiv fun f => by
        change _ ↔ CFSG.Timmesfeld.ClassicalOrders.hypSum (quadMinus (m + 1) K b c) (Ψ f) = 0 ∧
          polar (CFSG.Timmesfeld.ClassicalOrders.hypSum (quadMinus (m + 1) K b c)) (Ψ e) (Ψ f) = 1
        rw [Ψ.map_app, polar_isometryEquiv])
    rw [hcard, key, CFSG.Timmesfeld.ClassicalOrders.card_coord_fun]
    simp only [Fintype.card_sum, Fintype.card_fin]
    congr 1
    omega

theorem evenNormTail_transitive (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (θ : (binForm b c).IsometryEquiv N) (r : ℕ) {e f e' f' : ((Fin r → K) × (Fin r → K)) × E}
    (he : evenNormTailForm N r e = 0) (hf : evenNormTailForm N r f = 0)
    (hef : polar (evenNormTailForm N r) e f = 1) (he' : evenNormTailForm N r e' = 0)
    (hf' : evenNormTailForm N r f' = 0) (hef' : polar (evenNormTailForm N r) e' f' = 1) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (evenNormTailForm N r), g e = e' ∧ g f = f' :=
  CFSG.Timmesfeld.ClassicalOrders.exists_mem_orthogonalGroup_apply_pair
    (evenNormTail_nondegenerate hirr θ r) CharTwo.two_eq_zero
    (⟨e, f, he, hf, hef⟩ : HypPair (evenNormTailForm N r)) ⟨e', f', he', hf', hef'⟩

end Main

section Final

variable {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [Field E] [Algebra K E]
  {N : QuadraticForm K E} {b c : K}

omit [CharP K 2] in
theorem finrank_evenNormTailSpace (hE : finrank K E = 2) (r : ℕ) :
    finrank K (((Fin r → K) × (Fin r → K)) × E) = 2 * r + 2 := by
  have : Module.Finite K E := Module.finite_of_finrank_pos (by omega)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun, hE]
  ring

omit [CharP K 2] in
theorem evenNormTail_totallySingular (hE : finrank K E = 2)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (θ : (binForm b c).IsometryEquiv N) (r : ℕ) :
    (∃ U : Submodule K (((Fin r → K) × (Fin r → K)) × E), finrank K U = r ∧
        ∀ u ∈ U, evenNormTailForm N r u = 0) ∧
      ∀ U : Submodule K (((Fin r → K) × (Fin r → K)) × E),
        (∀ u ∈ U, evenNormTailForm N r u = 0) → finrank K U ≤ r := by
  refine ⟨⟨((⊤ : Submodule K (Fin r → K)).prod ⊥).prod ⊥, ?_, ?_⟩, ?_⟩
  · rw [(Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod,
      (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]
    simp
  · rintro ⟨⟨x, y⟩, z⟩ hu
    simp only [Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot, true_and] at hu
    obtain ⟨rfl, rfl⟩ := hu
    rw [evenNormTailForm_apply]
    simp
  · intro U hU
    by_contra hlt
    push Not at hlt
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := U) (n := r + 1) hlt
    have hf' : LinearIndependent K (U.subtype ∘ f) := hf.map' U.subtype (Submodule.ker_subtype U)
    set W := Submodule.span K (Set.range (U.subtype ∘ f)) with hW
    have hWU : W ≤ U := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (f i).2)
    have hWdim : finrank K W = r + 1 := by
      rw [hW, finrank_span_eq_card hf']
      simp
    have hplus : IsPlusType (evenNormTailForm N r) :=
      ⟨W, by rw [hWdim, finrank_evenNormTailSpace hE]; ring, fun w hw => hU w (hWU hw)⟩
    exact not_isPlusType_quadMinus (Nat.succ_le_succ (Nat.zero_le r)) hirr
      ((isPlusType_congr (evenNormTailIsometry θ r)).mp hplus)

theorem card_orthogonalGroup_evenNormTail (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (θ : (binForm b c).IsometryEquiv N) (r : ℕ) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (evenNormTailForm N r)) =
      2 * Nat.card K ^ (r * (r + 1)) * (Nat.card K ^ (r + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 r, (Nat.card K ^ (2 * i) - 1) := by
  have h := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus r hirr).2
  rw [← CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr
    (evenNormTailIsometry θ r)] at h
  have hprod : ∀ i ∈ Finset.Icc 1 r, ((Nat.card K : ℤ) ^ (2 * i) - 1) =
      ((Nat.card K ^ (2 * i) - 1 : ℕ) : ℤ) := by
    intro i _
    rw [Nat.cast_sub (Nat.one_le_pow _ _ Nat.card_pos)]
    push_cast
    ring
  rw [Finset.prod_congr rfl hprod, ← Nat.cast_prod] at h
  exact_mod_cast h

end Final

end CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.RankThree.PartOne

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.GroupTheory.WeirSylow

theorem even_norm_tail_orthogonal_group_order {K E : Type} [Field K] [Finite K] [CharP K 2]
    [Field E] [Algebra K E] (hE : finrank K E = 2) (σ : E ≃ₐ[K] E) (hσ : σ ≠ 1)
    (N : QuadraticForm K E) (hN : ∀ z, algebraMap K E (N z) = z * σ z) (r : ℕ) :
    (polarBilin (evenNormTailForm N r)).Nondegenerate ∧
    ((∃ U : Submodule K (((Fin r → K) × (Fin r → K)) × E), finrank K U = r ∧
        ∀ u ∈ U, evenNormTailForm N r u = 0) ∧
      ∀ U : Submodule K (((Fin r → K) × (Fin r → K)) × E),
        (∀ u ∈ U, evenNormTailForm N r u = 0) → finrank K U ≤ r) ∧
    Nat.card {v // evenNormTailForm N r v = 0 ∧ v ≠ 0} =
      (Nat.card K ^ r - 1) * (Nat.card K ^ (r + 1) + 1) ∧
    (∀ e : ((Fin r → K) × (Fin r → K)) × E, evenNormTailForm N r e = 0 → e ≠ 0 →
      Nat.card {f // evenNormTailForm N r f = 0 ∧ polar (evenNormTailForm N r) e f = 1} =
        Nat.card K ^ (2 * r)) ∧
    (∀ e f e' f' : ((Fin r → K) × (Fin r → K)) × E,
      evenNormTailForm N r e = 0 → evenNormTailForm N r f = 0 →
      polar (evenNormTailForm N r) e f = 1 → evenNormTailForm N r e' = 0 →
      evenNormTailForm N r f' = 0 → polar (evenNormTailForm N r) e' f' = 1 →
      ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (evenNormTailForm N r),
        g e = e' ∧ g f = f') ∧
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (evenNormTailForm N r)) =
      2 * Nat.card K ^ (r * (r + 1)) * (Nat.card K ^ (r + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 r, (Nat.card K ^ (2 * i) - 1) ∧
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (evenNormTailForm N 1)) =
      2 * Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) ∧
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (evenNormTailForm N 2)) =
      2 * Nat.card K ^ 6 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1) *
        (Nat.card K ^ 4 - 1) := by
  have _hσ := hσ
  have hN0 : ∀ z, N z = 0 → z = 0 := fun z hz => by
    have h := hN z
    rw [hz, map_zero] at h
    rcases mul_eq_zero.mp h.symm with h1 | h1
    · exact h1
    · exact (map_eq_zero_iff σ σ.injective).mp h1
  obtain ⟨b, c, hirr, ⟨θ⟩⟩ := exists_binForm_isometryEquiv hE N hN0
  have hq : ∀ k : ℕ, 1 ≤ Nat.card K ^ k := fun k => Nat.one_le_pow _ _ Nat.card_pos
  refine ⟨evenNormTail_nondegenerate hirr θ r, evenNormTail_totallySingular hE hirr θ r,
    card_nonzero_singular_evenNormTail hirr θ r,
    fun e he he0 => card_partners_evenNormTail hirr θ r he he0,
    fun e f e' f' he hf hef he' hf' hef' => evenNormTail_transitive hirr θ r he hf hef he' hf' hef',
    card_orthogonalGroup_evenNormTail hirr θ r, ?_, ?_⟩
  · rw [card_orthogonalGroup_evenNormTail hirr θ 1]
    simp only [Finset.Icc_self, Finset.prod_singleton]
    zify [hq 2, hq 4]
    ring
  · rw [card_orthogonalGroup_evenNormTail hirr θ 2]
    have : Finset.Icc 1 2 = {1, 2} := by decide
    rw [this, Finset.prod_pair (by norm_num)]
    ring

end CFSG.RankThree.PartOne
