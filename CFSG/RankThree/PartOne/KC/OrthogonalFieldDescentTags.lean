module

public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTransport
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentScaled
public import CFSG.RankThree.CentralLift.ClassicalCenterTrivial

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalDescent

open Matrix Module CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.Classical2
  CFSG.RankThree.CentralLift

variable {K : Type} [Field K] {d : ℕ}

theorem coe_smul_fixedSpace (U : coordinateSemilinearGroup d K) (c : fixedField U)
    (x : fixedSpace U) : ((c • x : fixedSpace U) : Fin d → K) = (c : K) • (x : Fin d → K) := rfl

theorem scaled_coe {Q : QuadraticForm K (Fin d → K)} {U : similarityPairs Q} {c : Kˣ}
    {Q₀ : QuadraticForm (fixedField U.val) (fixedSpace U.val)} {m δ : ℕ}
    (H : HypSplit Q₀ m δ) (HK : HypSplit ((c : K) • Q) m δ)
    (hbK : ∀ a, HK.b a = ((H.b a : fixedSpace U.val) : Fin d → K)) (u : (fixedField U.val)ˣ)
    (a : Fin m ⊕ Fin m ⊕ Fin δ) :
    HK.scaled (Units.map (algebraMap (fixedField U.val) K).toMonoidHom u) a =
      ((H.scaled u a : fixedSpace U.val) : Fin d → K) := by
  rcases a with i | i | j
  · rw [HK.scaled_inl, H.scaled_inl, hbK]
  · rw [HK.scaled_inr_inl, H.scaled_inr_inl, hbK, coe_smul_fixedSpace]
    rfl
  · rw [HK.scaled_inr_inr, H.scaled_inr_inr, hbK]

theorem coe_polar_Q₀ {Q : QuadraticForm K (Fin d → K)} {U : similarityPairs Q} {c : Kˣ}
    {Q₀ : QuadraticForm (fixedField U.val) (fixedSpace U.val)}
    (hQ₀ : ∀ w, ((Q₀ w : fixedField U.val) : K) = c * Q w) (w w' : fixedSpace U.val) :
    ((QuadraticMap.polar Q₀ w w' : fixedField U.val) : K) =
      c * QuadraticMap.polar Q (w : Fin d → K) (w' : Fin d → K) := by
  simp only [QuadraticMap.polar, Subfield.coe_sub, hQ₀, Submodule.coe_add]
  ring

theorem smul_form_coe {Q : QuadraticForm K (Fin d → K)} {U : similarityPairs Q} {c : Kˣ}
    {Q₀ : QuadraticForm (fixedField U.val) (fixedSpace U.val)}
    (hQ₀ : ∀ w, ((Q₀ w : fixedField U.val) : K) = c * Q w) (w : fixedSpace U.val) :
    ((c : K) • Q) (w : Fin d → K) = ((Q₀ w : fixedField U.val) : K) := by
  rw [hQ₀]
  rfl

theorem coordinateQuadOdd_field (n : ℕ) (σ : K ≃+* K) (v : Fin (2 * n + 1) → K) :
    coordinateQuadOdd n K (fun i => σ (v i)) = σ (coordinateQuadOdd n K v) := by
  simp [coordinateQuadOdd_apply, map_sum, map_add, map_mul, map_pow]

theorem coordinateQuadPlus_field (n : ℕ) (σ : K ≃+* K) (v : Fin (2 * n) → K) :
    coordinateQuadPlus n K (fun i => σ (v i)) = σ (coordinateQuadPlus n K v) := by
  simp [coordinateQuadPlus_apply, map_sum, map_mul]

theorem coordinateQuadMinus_field (n : ℕ) (hn : 1 ≤ n) (b c : K) (σ : K ≃+* K) (hb : σ b = b)
    (hc : σ c = c) (v : Fin (2 * n) → K) :
    coordinateQuadMinus n K hn b c (fun i => σ (v i)) = σ (coordinateQuadMinus n K hn b c v) := by
  simp [coordinateQuadMinus_apply, map_sum, map_add, map_mul, map_pow, hb, hc]

theorem odd_field_descent {ℓ f p n : ℕ} [Finite K]
    {U : similarityPairs (coordinateQuadOdd n K)} {c : Kˣ}
    {Q₀ : QuadraticForm (fixedField U.val) (fixedSpace U.val)}
    (hQ₀ : ∀ w, ((Q₀ w : fixedField U.val) : K) = c * coordinateQuadOdd n K w)
    (hadm : StatedLieAdmissible .POmegaOdd n ℓ (f / p))
    (hcard : Nat.card (fixedField U.val) = ℓ ^ (f / p)) (H : HypSplit Q₀ n 1)
    (HK : HypSplit ((c : K) • coordinateQuadOdd n K) n 1)
    (hbK : ∀ a, HK.b a = ((H.b a : fixedSpace U.val) : Fin (2 * n + 1) → K)) :
    OddFieldDescent n ℓ f p (coordinateQuadOdd n K) U Q₀ := by
  have hα : Q₀ (H.b (.inr (.inr 0))) ≠ 0 := H.Q_tail_one_ne_zero
  let u : (fixedField U.val)ˣ := Units.mk0 _ hα
  have hu : (u : fixedField U.val) = Q₀ (H.b (.inr (.inr 0))) := rfl
  let uK : Kˣ := Units.map (algebraMap (fixedField U.val) K).toMonoidHom u
  have huK : (uK : K) = ((c : K) • coordinateQuadOdd n K) (HK.b (.inr (.inr 0))) := by
    rw [hbK, smul_form_coe hQ₀]
    rfl
  let bk := (H.scaled u).reindex (HypSplit.oddEquiv n)
  let bK := (HK.scaled uK).reindex (HypSplit.oddEquiv n)
  have hb : ∀ a, bK a = ((bk a : fixedSpace U.val) : Fin (2 * n + 1) → K) := fun a => by
    show ((HK.scaled uK).reindex (HypSplit.oddEquiv n)) a =
      (((H.scaled u).reindex (HypSplit.oddEquiv n)) a : fixedSpace U.val)
    rw [Basis.reindex_apply, Basis.reindex_apply]
    exact scaled_coe H HK hbK u _
  have hsim : ∀ w, StatedQuadOdd n (fixedField U.val) (bk.equivFun w) =
      (((u⁻¹ : (fixedField U.val)ˣ) : fixedField U.val)) * Q₀ w := fun w => H.displayOdd u hu w
  have hν : ∀ v, coordinateQuadOdd n K (fun j => bK.equivFun v ((oddIndexEquiv n).symm j)) =
      ((uK⁻¹ * c : Kˣ) : K) * coordinateQuadOdd n K v := by
    intro v
    have h1 := HK.displayOdd uK huK v
    have h2 : coordinateQuadOdd n K (fun j => bK.equivFun v ((oddIndexEquiv n).symm j)) =
        StatedQuadOdd n K (bK.equivFun v) := by
      rw [coordinateQuadOdd_apply]
      simp [StatedQuadOdd]
    rw [h2, Units.val_mul]
    change StatedQuadOdd n K (((HK.scaled uK).reindex (HypSplit.oddEquiv n)).equivFun v) = _ at h1
    rw [h1]
    have h3 : ((c : K) • coordinateQuadOdd n K) v = c * coordinateQuadOdd n K v := rfl
    rw [h3]
    ring
  have hmodel : StatedClassicalModel (ProjOrthDerived Q₀) .POmegaOdd n ℓ (f / p) := by
    refine ⟨hadm, fixedField U.val, inferInstance, inferInstance, hcard, ⟨?_⟩⟩
    have e1 := projOrthDerivedEquiv (Q₁ := CFSG.LieType.Universal.Spin.quadOdd n
      (fixedField U.val)) bk.equivFun u⁻¹ (fun w => by
        rw [show (CFSG.LieType.Universal.Spin.quadOdd n (fixedField U.val))
          (bk.equivFun w) = StatedQuadOdd n (fixedField U.val) (bk.equivFun w) from
          congrFun (CFSG.LieType.Universal.Spin.coe_quadOdd n (fixedField U.val)) _]
        exact hsim w)
    exact e1.trans (nonempty_statedProj_mulEquiv_projOrthDerived
      (CFSG.LieType.Universal.Spin.coe_quadOdd n (fixedField U.val))).some.symm
  let g' : similarityPairs (coordinateQuadOdd n K) :=
    ⟨SemidirectProduct.inr U.val.right,
      inr_mem_similarityPairs _ _ (coordinateQuadOdd_field n U.val.right)⟩
  exact ⟨u⁻¹, bk.equivFun, hsim, hmodel, transports_of_basis (oddIndexEquiv n)
    (coordinateQuadOdd n K) (coordinateQuadOdd n K) U bk bK hb (uK⁻¹ * c) hν g' (by simp [g'])
    rfl⟩

theorem plus_field_descent {ℓ f p n : ℕ} [Finite K]
    {U : similarityPairs (coordinateQuadPlus n K)} {c : Kˣ}
    {Q₀ : QuadraticForm (fixedField U.val) (fixedSpace U.val)}
    (hadm : StatedLieAdmissible .POmegaPlus n ℓ (f / p))
    (hcard : Nat.card (fixedField U.val) = ℓ ^ (f / p)) (H : HypSplit Q₀ n 0)
    (HK : HypSplit ((c : K) • coordinateQuadPlus n K) n 0)
    (hbK : ∀ a, HK.b a = ((H.b a : fixedSpace U.val) : Fin (2 * n) → K)) :
    PlusFieldDescent n ℓ f p (coordinateQuadPlus n K) U Q₀ := by
  let bk := H.b.reindex (HypSplit.plusEquiv n)
  let bK := HK.b.reindex (HypSplit.plusEquiv n)
  have hb : ∀ a, bK a = ((bk a : fixedSpace U.val) : Fin (2 * n) → K) := fun a => by
    show (HK.b.reindex (HypSplit.plusEquiv n)) a =
      ((H.b.reindex (HypSplit.plusEquiv n)) a : fixedSpace U.val)
    rw [Basis.reindex_apply, Basis.reindex_apply]
    exact hbK _
  have hsim : ∀ w, StatedQuadPlus n (fixedField U.val) (bk.equivFun w) =
      (((1 : (fixedField U.val)ˣ) : fixedField U.val)) * Q₀ w := fun w => by
    rw [Units.val_one, one_mul]
    exact H.displayPlus w
  have hν : ∀ v, coordinateQuadPlus n K (fun j => bK.equivFun v ((plusIndexEquiv n).symm j)) =
      (c : K) * coordinateQuadPlus n K v := by
    intro v
    have h1 := HK.displayPlus v
    have h2 : coordinateQuadPlus n K (fun j => bK.equivFun v ((plusIndexEquiv n).symm j)) =
        StatedQuadPlus n K (bK.equivFun v) := by
      rw [coordinateQuadPlus_apply]
      simp [StatedQuadPlus]
    rw [h2]
    exact h1
  have hmodel : StatedClassicalModel (ProjOrthDerived Q₀) .POmegaPlus n ℓ (f / p) := by
    refine ⟨hadm, fixedField U.val, inferInstance, inferInstance, hcard, ⟨?_⟩⟩
    have e1 := projOrthDerivedEquiv (Q₁ := CFSG.LieType.Universal.Spin.quadPlus n
      (fixedField U.val)) bk.equivFun 1 (fun w => by
        rw [show (CFSG.LieType.Universal.Spin.quadPlus n (fixedField U.val))
          (bk.equivFun w) = StatedQuadPlus n (fixedField U.val) (bk.equivFun w) from
          congrFun (CFSG.LieType.Universal.Spin.coe_quadPlus n (fixedField U.val)) _]
        exact hsim w)
    exact e1.trans (nonempty_statedProj_mulEquiv_projOrthDerived
      (CFSG.LieType.Universal.Spin.coe_quadPlus n (fixedField U.val))).some.symm
  let g' : similarityPairs (coordinateQuadPlus n K) :=
    ⟨SemidirectProduct.inr U.val.right,
      inr_mem_similarityPairs _ _ (coordinateQuadPlus_field n U.val.right)⟩
  exact ⟨1, bk.equivFun, hsim, hmodel, transports_of_basis (plusIndexEquiv n)
    (coordinateQuadPlus n K) (coordinateQuadPlus n K) U bk bK hb c hν g' (by simp [g']) rfl⟩

theorem minus_field_descent {ℓ f p n : ℕ} (hn : 1 ≤ n) [Finite K] (b₀ c₀ : K)
    {U : similarityPairs (coordinateQuadMinus n K hn b₀ c₀)} {s : Kˣ}
    {Q₀ : QuadraticForm (fixedField U.val) (fixedSpace U.val)}
    (hQ₀ : ∀ w, ((Q₀ w : fixedField U.val) : K) = s * coordinateQuadMinus n K hn b₀ c₀ w)
    (hadm : StatedLieAdmissible .POmegaMinus n ℓ (f / p))
    (hcard : Nat.card (fixedField U.val) = ℓ ^ (f / p)) (H : HypSplit Q₀ (n - 1) 2)
    (HK : HypSplit ((s : K) • coordinateQuadMinus n K hn b₀ c₀) (n - 1) 2)
    (hbK : ∀ a, HK.b a = ((H.b a : fixedSpace U.val) : Fin (2 * n) → K)) :
    MinusFieldDescent n ℓ f p hn (coordinateQuadMinus n K hn b₀ c₀) U Q₀ := by
  have hα : Q₀ (H.b (.inr (.inr 0))) ≠ 0 := H.Q_tail_two_ne_zero
  let u : (fixedField U.val)ˣ := Units.mk0 _ hα
  have hu : (u : fixedField U.val) = Q₀ (H.b (.inr (.inr 0))) := rfl
  let uK : Kˣ := Units.map (algebraMap (fixedField U.val) K).toMonoidHom u
  have huK : (uK : K) = ((s : K) • coordinateQuadMinus n K hn b₀ c₀) (HK.b (.inr (.inr 0))) := by
    rw [hbK, smul_form_coe hQ₀]
    rfl
  let t₀ := H.b (.inr (.inr 0))
  let t₁ := H.b (.inr (.inr 1))
  let b' : fixedField U.val := ((u⁻¹ : (fixedField U.val)ˣ) : fixedField U.val) *
    QuadraticMap.polar Q₀ t₀ t₁
  let c' : fixedField U.val := ((u⁻¹ : (fixedField U.val)ˣ) : fixedField U.val) * Q₀ t₁
  have hroot : ∀ r : fixedField U.val, r ^ 2 + b' * r + c' ≠ 0 := by
    intro r hr
    have h1 : Q₀ (∑ j, (![r, 1] : Fin 2 → fixedField U.val) j • H.b (.inr (.inr j))) = 0 := by
      rw [H.tail_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have h2 : (u : fixedField U.val) * (r ^ 2 + b' * r + c') = 0 := by rw [hr, mul_zero]
      have h3 : (u : fixedField U.val) * (r ^ 2 + b' * r + c') =
          r ^ 2 * Q₀ t₀ + 1 ^ 2 * Q₀ t₁ + r * 1 * QuadraticMap.polar Q₀ t₀ t₁ := by
        have h4 : (u : fixedField U.val) * ((u⁻¹ : (fixedField U.val)ˣ) : fixedField U.val) = 1 :=
          Units.mul_inv u
        simp only [b', c']
        rw [hu] at h4 ⊢
        linear_combination (Q₀ t₁ + r * QuadraticMap.polar Q₀ t₀ t₁) * h4
      rw [← h3]
      exact h2
    have h5 := H.aniso _ h1
    exact one_ne_zero (congrFun h5 1)
  let bk := H.scaled u
  let bK := HK.scaled uK
  have hb : ∀ a, bK a = ((bk a : fixedSpace U.val) : Fin (2 * n) → K) := fun a =>
    scaled_coe H HK hbK u a
  have hsim : ∀ w, StatedQuadMinus n (fixedField U.val) b' c' (bk.equivFun w) =
      (((u⁻¹ : (fixedField U.val)ˣ) : fixedField U.val)) * Q₀ w := fun w =>
    H.displayMinus u hu w
  have hinv : ((uK⁻¹ : Kˣ) : K) = (((u⁻¹ : (fixedField U.val)ˣ) : fixedField U.val) : K) := by
    rw [show uK⁻¹ = Units.map (algebraMap (fixedField U.val) K).toMonoidHom u⁻¹ from
      (map_inv _ u).symm]
    rfl
  have hpolK : QuadraticMap.polar ((s : K) • coordinateQuadMinus n K hn b₀ c₀)
      (HK.b (.inr (.inr 0))) (HK.b (.inr (.inr 1))) =
      ((QuadraticMap.polar Q₀ t₀ t₁ : fixedField U.val) : K) := by
    rw [hbK, hbK, coe_polar_Q₀ hQ₀]
    simp only [FunLike.coe_smul, QuadraticMap.polar_smul, smul_eq_mul]
    rfl
  have hQ1K : ((s : K) • coordinateQuadMinus n K hn b₀ c₀) (HK.b (.inr (.inr 1))) =
      ((Q₀ t₁ : fixedField U.val) : K) := by
    rw [hbK, smul_form_coe hQ₀]
  have hcoefb : ((uK⁻¹ : Kˣ) : K) * QuadraticMap.polar
      ((s : K) • coordinateQuadMinus n K hn b₀ c₀)
      (HK.b (.inr (.inr 0))) (HK.b (.inr (.inr 1))) = ((b' : fixedField U.val) : K) := by
    rw [hinv, hpolK]
    rfl
  have hcoefc : ((uK⁻¹ : Kˣ) : K) * ((s : K) • coordinateQuadMinus n K hn b₀ c₀)
      (HK.b (.inr (.inr 1))) = ((c' : fixedField U.val) : K) := by
    rw [hinv, hQ1K]
    rfl
  have hν : ∀ v, coordinateQuadMinus n K hn (b' : K) (c' : K)
      (fun j => bK.equivFun v ((minusIndexEquiv n hn).symm j)) =
      ((uK⁻¹ * s : Kˣ) : K) * coordinateQuadMinus n K hn b₀ c₀ v := by
    intro v
    have h1 := HK.displayMinus uK huK v
    rw [hcoefb, hcoefc] at h1
    have h2 : coordinateQuadMinus n K hn (b' : K) (c' : K)
        (fun j => bK.equivFun v ((minusIndexEquiv n hn).symm j)) =
        StatedQuadMinus n K (b' : K) (c' : K) (bK.equivFun v) := by
      rw [coordinateQuadMinus_apply]
      simp [StatedQuadMinus]
    rw [h2]
    change StatedQuadMinus n K (b' : K) (c' : K) ((HK.scaled uK).equivFun v) = _ at h1
    rw [h1, Units.val_mul]
    have h3 : ((s : K) • coordinateQuadMinus n K hn b₀ c₀) v =
        s * coordinateQuadMinus n K hn b₀ c₀ v := rfl
    rw [h3]
    ring
  have hmodel : StatedClassicalModel (ProjOrthDerived Q₀) .POmegaMinus n ℓ (f / p) := by
    refine ⟨hadm, fixedField U.val, inferInstance, inferInstance, hcard, b', c', hroot, ⟨?_⟩⟩
    have e1 := projOrthDerivedEquiv (Q₁ := CFSG.LieType.Universal.Spin.quadMinus n
      (fixedField U.val) b' c') bk.equivFun u⁻¹ (fun w => by
        rw [show (CFSG.LieType.Universal.Spin.quadMinus n (fixedField U.val) b' c')
          (bk.equivFun w) = StatedQuadMinus n (fixedField U.val) b' c' (bk.equivFun w) from
          congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus n (fixedField U.val) b' c') _]
        exact hsim w)
    exact e1.trans (nonempty_statedProj_mulEquiv_projOrthDerived
      (CFSG.LieType.Universal.Spin.coe_quadMinus n (fixedField U.val) b' c')).some.symm
  have hσb : U.val.right (b' : K) = b' := RingHom.mem_eqLocusField.mp b'.2
  have hσc : U.val.right (c' : K) = c' := RingHom.mem_eqLocusField.mp c'.2
  let g' : similarityPairs (coordinateQuadMinus n K hn (b' : K) (c' : K)) :=
    ⟨SemidirectProduct.inr U.val.right, inr_mem_similarityPairs _ _
      (coordinateQuadMinus_field n hn (b' : K) (c' : K) U.val.right hσb hσc)⟩
  exact ⟨b', c', hroot, u⁻¹, bk.equivFun, hsim, hmodel, transports_of_basis (minusIndexEquiv n hn)
    (coordinateQuadMinus n K hn b₀ c₀) (coordinateQuadMinus n K hn (b' : K) (c' : K)) U bk bK hb
    (uK⁻¹ * s) hν g' (by simp [g']) rfl⟩

end CFSG.RankThree.PartOne.KCOrthogonalDescent
