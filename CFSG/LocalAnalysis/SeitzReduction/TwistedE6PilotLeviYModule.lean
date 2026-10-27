module

public import CFSG.LieType.Chevalley.C2E6RootRestrictionD

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin QuadraticMap

section Module

variable (K : Type) [Field K]

noncomputable abbrev d4Vec (j : Fin 8) : RootModule Tag.E6 K := rootVec Tag.E6 K (rootD j)

@[expose] noncomputable def d4Module : Submodule K (RootModule Tag.E6 K) :=
  Submodule.span K (Set.range (d4Vec K))

variable {K}

theorem d4Vec_mem (j : Fin 8) : d4Vec K j ∈ d4Module K :=
  Submodule.subset_span ⟨j, rfl⟩

theorem linearIndependent_d4Vec :
    LinearIndependent K (d4Vec K) := by
  have h := (Finsupp.basisSingleOne (R := K) (ι := Label Tag.E6)).linearIndependent.comp
    (fun j => (Sum.inr ⟨rootD j, isRoot_rootD j⟩ : Label Tag.E6))
    (fun j j' h => rootD_injective (by simpa using h))
  convert h using 1
  funext j
  simp [d4Vec, CFSG.LieType.Chevalley.C2E6Std.rootVec_eq_single (isRoot_rootD j)]

variable (K) in
@[expose] noncomputable def d4Basis :
    Module.Basis (Fin 8) K (d4Module K) :=
  Module.Basis.span linearIndependent_d4Vec

theorem d4Basis_apply (j : Fin 8) :
    d4Basis K j = ⟨d4Vec K j, d4Vec_mem j⟩ :=
  Module.Basis.span_apply linearIndependent_d4Vec j

variable (K) in
@[expose] noncomputable def d4Phi :
    d4Module K ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
  (d4Basis K).equiv (Pi.basisFun K (Fin 4 ⊕ Fin 4)) eD

theorem d4Phi_vec (j : Fin 8) : d4Phi K ⟨d4Vec K j, d4Vec_mem j⟩ = Pi.single (natD j) 1 := by
  rw [← d4Basis_apply, d4Phi, Module.Basis.equiv_apply, Pi.basisFun_apply]
  rfl

theorem d4Phi_add_smul {a b : RootModule Tag.E6 K} (ha : a ∈ d4Module K) (hb : b ∈ d4Module K)
    (c : K) (h : a + c • b ∈ d4Module K) :
    d4Phi K ⟨a + c • b, h⟩ = d4Phi K ⟨a, ha⟩ + c • d4Phi K ⟨b, hb⟩ := by
  rw [← map_smul, ← map_add]
  rfl

theorem d4Module_le_comap {f : Module.End K (RootModule Tag.E6 K)}
    (hf : ∀ j, f (d4Vec K j) ∈ d4Module K) : ∀ v ∈ d4Module K, f v ∈ d4Module K := by
  intro v hv
  have : d4Module K ≤ (d4Module K).comap f := by
    rw [d4Module, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hf j
  exact this hv

end Module

section Natural

variable {K : Type} [Field K]

theorem d4ElementaryMap_single (p q s : Fin 4 ⊕ Fin 4) (t : K) :
    orthElementaryMap (quadPlus 4 K) (Pi.single p 1) (t • Pi.single q 1) (Pi.single s 1) =
      Pi.single s 1 + (if p.swap = s then t • Pi.single q 1 else 0) -
        (if q.swap = s then t • Pi.single p 1 else 0) := by
  rw [orthElementaryMap_apply, polar_single, polar_smul_right, polar_single,
    QuadraticMap.map_smul, CFSG.ClassicalGroups.Orthogonal.quadPlus_single, smul_zero, zero_mul,
    zero_smul, sub_zero]
  congr 1
  · congr 1
    split_ifs with h
    · subst h
      simp
    · simp [Ne.symm h]
  · split_ifs with h
    · subst h
      simp
    · simp [Ne.symm h]

theorem d4RootElt_simpleRoot (k : Fin 4) (c : K) :
    ((rootElt 4 K (OrthogonalSplit.simpleRoot 4 k) c : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _) :
      (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) =
      orthElementaryMap (quadPlus 4 K) (Pi.single (posCenter k) 1)
        ((-c) • Pi.single (posParam k) 1) := by
  fin_cases k
  · rw [show (⟨0, _⟩ : Fin 4) = 0 from rfl, simpleRoot_zero, rootElt_eps_sub_eps (by decide)]
    rfl
  · rw [show (⟨1, _⟩ : Fin 4) = 1 from rfl, simpleRoot_one, rootElt_eps_sub_eps (by decide)]
    rfl
  · rw [show (⟨2, _⟩ : Fin 4) = 2 from rfl, simpleRoot_two, rootElt_eps_sub_eps (by decide)]
    rfl
  · rw [show (⟨3, _⟩ : Fin 4) = 3 from rfl, simpleRoot_three, rootElt_eps_add_eps (by decide)]
    rfl

theorem d4RootElt_neg_simpleRoot (k : Fin 4) (c : K) :
    ((rootElt 4 K (-OrthogonalSplit.simpleRoot 4 k) c : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _) :
      (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) =
      orthElementaryMap (quadPlus 4 K) (Pi.single (negCenter k) 1)
        ((-c) • Pi.single (negParam k) 1) := by
  fin_cases k
  · rw [show (⟨0, _⟩ : Fin 4) = 0 from rfl, simpleRoot_zero, neg_sub, sub_eq_neg_add,
      rootElt_neg_eps_add_eps (by decide)]
    rfl
  · rw [show (⟨1, _⟩ : Fin 4) = 1 from rfl, simpleRoot_one, neg_sub, sub_eq_neg_add,
      rootElt_neg_eps_add_eps (by decide)]
    rfl
  · rw [show (⟨2, _⟩ : Fin 4) = 2 from rfl, simpleRoot_two, neg_sub, sub_eq_neg_add,
      rootElt_neg_eps_add_eps (by decide)]
    rfl
  · rw [show (⟨3, _⟩ : Fin 4) = 3 from rfl, simpleRoot_three, neg_add, ← sub_eq_add_neg,
      rootElt_neg_eps_sub_eps (by decide)]
    rfl

theorem d4ElementaryMap_single_charTwo [CharP K 2] {p q s : Fin 4 ⊕ Fin 4}
    (hpq : p.swap ≠ q.swap) (c : K) :
    orthElementaryMap (quadPlus 4 K) (Pi.single p 1) ((-c) • Pi.single q 1) (Pi.single s 1) =
      Pi.single s 1 + (if s = p.swap then c • Pi.single q 1
        else if s = q.swap then c • Pi.single p 1 else 0) := by
  rw [d4ElementaryMap_single]
  by_cases h1 : s = p.swap
  · subst h1
    rw [ite_eq_left rfl, ite_eq_right (fun h => hpq h.symm), ite_eq_left rfl, sub_zero,
      CharTwo.neg_eq]
  · rw [ite_eq_right (Ne.symm h1), ite_eq_right h1, add_zero]
    by_cases h2 : s = q.swap
    · subst h2
      rw [ite_eq_left rfl, ite_eq_left rfl, sub_eq_add_neg, neg_smul, neg_neg]
    · rw [ite_eq_right (Ne.symm h2), ite_eq_right h2, sub_zero, add_zero]

end Natural

section Operators

variable {K : Type} [Field K]

theorem xOp_d4Vec (j : Fin 8) (k : Fin 4) (c : K) :
    xOp Tag.E6 K (jD k) c (d4Vec K j) =
      d4Vec K j + c • rootVec Tag.E6 K (rootD j + Pi.single (jD k) 1) :=
  xOp_rootVec_E6 (jD k) c (isRoot_rootD j) (rootD_ne_single j k).1 (rootD_ne_single j k).2

theorem yOp_d4Vec (j : Fin 8) (k : Fin 4) (c : K) :
    yOp Tag.E6 K (jD k) c (d4Vec K j) =
      d4Vec K j + c • rootVec Tag.E6 K (rootD j - Pi.single (jD k) 1) :=
  yOp_rootVec_E6 (jD k) c (isRoot_rootD j) (rootD_ne_single j k).1 (rootD_ne_single j k).2

theorem rootVec_raise_mem_d4Module (j : Fin 8) (k : Fin 4) :
    rootVec Tag.E6 K (rootD j + Pi.single (jD k) 1) ∈ d4Module K := by
  rcases raiseD_or j k with ⟨j', hj'⟩ | h
  · rw [← hj']
    exact d4Vec_mem j'
  · rw [rootVec_eq_zero_of_not h]
    exact Submodule.zero_mem _

theorem rootVec_lower_mem_d4Module (j : Fin 8) (k : Fin 4) :
    rootVec Tag.E6 K (rootD j - Pi.single (jD k) 1) ∈ d4Module K := by
  rcases lowerD_or j k with ⟨j', hj'⟩ | h
  · rw [← hj']
    exact d4Vec_mem j'
  · rw [rootVec_eq_zero_of_not h]
    exact Submodule.zero_mem _

theorem xOp_mem_d4Module (k : Fin 4) (c : K) :
    ∀ v ∈ d4Module K, xOp Tag.E6 K (jD k) c v ∈ d4Module K :=
  d4Module_le_comap fun j => by
    rw [xOp_d4Vec]
    exact (d4Module K).add_mem (d4Vec_mem j)
      ((d4Module K).smul_mem c (rootVec_raise_mem_d4Module j k))

theorem yOp_mem_d4Module (k : Fin 4) (c : K) :
    ∀ v ∈ d4Module K, yOp Tag.E6 K (jD k) c v ∈ d4Module K :=
  d4Module_le_comap fun j => by
    rw [yOp_d4Vec]
    exact (d4Module K).add_mem (d4Vec_mem j)
      ((d4Module K).smul_mem c (rootVec_lower_mem_d4Module j k))

theorem d4Phi_shift {j : Fin 8} {e : Fin Tag.E6.rank → ℤ} {p q : Fin 4 ⊕ Fin 4}
    (hpq : p.swap ≠ q.swap) (c : K)
    (hraise : (∃ j', rootD j' = rootD j + e) ↔ (natD j = p.swap ∨ natD j = q.swap))
    (hnat : ∀ j', rootD j' = rootD j + e →
      (natD j = p.swap ∧ natD j' = q) ∨ (natD j = q.swap ∧ natD j' = p))
    (hor : (∃ j', rootD j' = rootD j + e) ∨ ¬IsRoot Tag.E6 (rootD j + e))
    (hmem : rootVec Tag.E6 K (rootD j + e) ∈ d4Module K) :
    Pi.single (natD j) 1 + c • d4Phi K ⟨rootVec Tag.E6 K (rootD j + e), hmem⟩ =
      Pi.single (natD j) 1 + (if natD j = p.swap then c • Pi.single q 1
        else if natD j = q.swap then c • Pi.single p 1 else 0) := by
  congr 1
  rcases hor with ⟨j', hj'⟩ | hnot
  · have hv : (⟨rootVec Tag.E6 K (rootD j + e), hmem⟩ : d4Module K) =
        ⟨d4Vec K j', d4Vec_mem j'⟩ :=
      Subtype.ext (show rootVec Tag.E6 K (rootD j + e) = d4Vec K j' by rw [← hj'])
    rw [hv, d4Phi_vec]
    rcases hnat j' hj' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [ite_eq_left h1, h2]
    · rw [ite_eq_right (fun h => hpq (h1.symm.trans h).symm), ite_eq_left h1, h2]
  · have hv : (⟨rootVec Tag.E6 K (rootD j + e), hmem⟩ : d4Module K) = 0 :=
      Subtype.ext (show rootVec Tag.E6 K (rootD j + e) = 0 from rootVec_eq_zero_of_not hnot)
    have hno : ¬(natD j = p.swap ∨ natD j = q.swap) := by
      rw [← hraise]
      rintro ⟨j', hj'⟩
      exact hnot (hj' ▸ isRoot_rootD j')
    push Not at hno
    rw [hv, map_zero, smul_zero, ite_eq_right hno.1, ite_eq_right hno.2]

variable [CharP K 2]

theorem d4Phi_xOp (k : Fin 4) (c : K) {v : RootModule Tag.E6 K} (hv : v ∈ d4Module K) :
    d4Phi K ⟨xOp Tag.E6 K (jD k) c v, xOp_mem_d4Module k c v hv⟩ =
      rootElt 4 K (OrthogonalSplit.simpleRoot 4 k) c (d4Phi K ⟨v, hv⟩) := by
  have key : (d4Phi K).toLinearMap ∘ₗ (xOp Tag.E6 K (jD k) c).restrict (xOp_mem_d4Module k c) =
      ((rootElt 4 K (OrthogonalSplit.simpleRoot 4 k) c : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _) :
        (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) ∘ₗ (d4Phi K).toLinearMap := by
    refine (d4Basis K).ext fun j => ?_
    have hR := LinearMap.congr_fun (d4RootElt_simpleRoot k c) (Pi.single (natD j) 1)
    rw [LinearEquiv.coe_coe] at hR
    rw [LinearMap.comp_apply, LinearMap.comp_apply, d4Basis_apply, LinearMap.restrict_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, d4Phi_vec, hR,
      d4ElementaryMap_single_charTwo (center_param_ne k).1]
    have hx : (⟨xOp Tag.E6 K (jD k) c (d4Vec K j), xOp_mem_d4Module k c _ (d4Vec_mem j)⟩ :
        d4Module K) =
        ⟨d4Vec K j + c • rootVec Tag.E6 K (rootD j + Pi.single (jD k) 1),
          (d4Module K).add_mem (d4Vec_mem j)
            ((d4Module K).smul_mem c (rootVec_raise_mem_d4Module j k))⟩ :=
      Subtype.ext (xOp_d4Vec j k c)
    rw [hx, d4Phi_add_smul (d4Vec_mem j) (rootVec_raise_mem_d4Module j k), d4Phi_vec]
    exact d4Phi_shift (center_param_ne k).1 c (raise_rootD j k) (fun j' => raise_natD j j' k)
      (raiseD_or j k) _
  exact congrArg (fun F : d4Module K →ₗ[K] (Fin 4 ⊕ Fin 4 → K) => F ⟨v, hv⟩) key

theorem d4Phi_yOp (k : Fin 4) (c : K) {v : RootModule Tag.E6 K} (hv : v ∈ d4Module K) :
    d4Phi K ⟨yOp Tag.E6 K (jD k) c v, yOp_mem_d4Module k c v hv⟩ =
      rootElt 4 K (-OrthogonalSplit.simpleRoot 4 k) c (d4Phi K ⟨v, hv⟩) := by
  have key : (d4Phi K).toLinearMap ∘ₗ (yOp Tag.E6 K (jD k) c).restrict (yOp_mem_d4Module k c) =
      ((rootElt 4 K (-OrthogonalSplit.simpleRoot 4 k) c : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _) :
        (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) ∘ₗ (d4Phi K).toLinearMap := by
    refine (d4Basis K).ext fun j => ?_
    have hR := LinearMap.congr_fun (d4RootElt_neg_simpleRoot k c) (Pi.single (natD j) 1)
    rw [LinearEquiv.coe_coe] at hR
    rw [LinearMap.comp_apply, LinearMap.comp_apply, d4Basis_apply, LinearMap.restrict_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, d4Phi_vec, hR,
      d4ElementaryMap_single_charTwo (center_param_ne k).2]
    have hy : (⟨yOp Tag.E6 K (jD k) c (d4Vec K j), yOp_mem_d4Module k c _ (d4Vec_mem j)⟩ :
        d4Module K) =
        ⟨d4Vec K j + c • rootVec Tag.E6 K (rootD j - Pi.single (jD k) 1),
          (d4Module K).add_mem (d4Vec_mem j)
            ((d4Module K).smul_mem c (rootVec_lower_mem_d4Module j k))⟩ :=
      Subtype.ext (yOp_d4Vec j k c)
    rw [hy, d4Phi_add_smul (d4Vec_mem j) (rootVec_lower_mem_d4Module j k), d4Phi_vec]
    simp only [sub_eq_add_neg]
    have hraise := lower_rootD j k
    have hnat := fun j' => lower_natD j j' k
    have hor := lowerD_or j k
    simp only [sub_eq_add_neg] at hraise hnat hor
    exact d4Phi_shift (center_param_ne k).2 c hraise hnat hor _
  exact congrArg (fun F : d4Module K →ₗ[K] (Fin 4 ⊕ Fin 4 → K) => F ⟨v, hv⟩) key

omit [CharP K 2] in
theorem mem_d4Module_of_mem_subsystemGroup {g : ModGL Tag.E6 K}
    (hg : g ∈ subsystemGroup Tag.E6 K setD) :
    ∀ v ∈ d4Module K, (g : Module.End K (RootModule Tag.E6 K)) v ∈ d4Module K := by
  refine mem_of_mem_subsystemGroup (fun i hi c => ?_) (fun i hi c => ?_) hg
  · obtain ⟨k, rfl⟩ := exists_jD_of_mem_setD hi
    exact xOp_mem_d4Module k c
  · obtain ⟨k, rfl⟩ := exists_jD_of_mem_setD hi
    exact yOp_mem_d4Module k c

end Operators

section Diagram

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def d4Swap : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
  LinearEquiv.funCongrLeft K K (Equiv.swap (.inl 3) (.inr 3))

variable (K) in
noncomputable abbrev d4Diag : Module.End K (RootModule Tag.E6 K) := (diagramMap TwistTag.E6 K).val

theorem d4Swap_apply (v : Fin 4 ⊕ Fin 4 → K) (s : Fin 4 ⊕ Fin 4) :
    d4Swap K v s = v (Equiv.swap (.inl 3) (.inr 3) s) :=
  rfl

theorem d4Swap_single (s : Fin 4 ⊕ Fin 4) :
    d4Swap K (Pi.single s (1 : K)) = Pi.single (Equiv.swap (.inl 3) (.inr 3) s) 1 := by
  funext x
  simp [d4Swap, Pi.single_apply, Equiv.swap_apply_eq_iff]

theorem diagramMap_d4Vec (j : Fin 8) :
    d4Diag K (d4Vec K j) =
      rootVec Tag.E6 K (rhoL (rootD j)) :=
  diagramMap_rootVec TwistTag.E6 K (rootD j) (isRoot_rootD j)

theorem diagramMap_mem_d4Module : ∀ v ∈ d4Module K, d4Diag K v ∈ d4Module K :=
  d4Module_le_comap fun j => by
    rw [diagramMap_d4Vec]
    obtain ⟨j', hj', -⟩ := diag_rootD j
    rw [← hj']
    exact d4Vec_mem j'

theorem d4Phi_diagramMap {v : RootModule Tag.E6 K} (hv : v ∈ d4Module K) :
    d4Phi K ⟨d4Diag K v, diagramMap_mem_d4Module v hv⟩ = d4Swap K (d4Phi K ⟨v, hv⟩) := by
  have key : (d4Phi K).toLinearMap ∘ₗ (d4Diag K).restrict diagramMap_mem_d4Module =
      (d4Swap K).toLinearMap ∘ₗ (d4Phi K).toLinearMap := by
    refine (d4Basis K).ext fun j => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, d4Basis_apply, LinearMap.restrict_apply]
    obtain ⟨j', hj', hnat⟩ := diag_rootD j
    have : (⟨d4Diag K (d4Vec K j), diagramMap_mem_d4Module _ (d4Vec_mem j)⟩ : d4Module K) =
        ⟨d4Vec K j', d4Vec_mem j'⟩ :=
      Subtype.ext (show d4Diag K (d4Vec K j) = d4Vec K j' by rw [diagramMap_d4Vec, ← hj'])
    refine (congrArg (d4Phi K) this).trans ?_
    rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, d4Phi_vec, d4Phi_vec, d4Swap_single, hnat]
  exact congrArg (fun F : d4Module K →ₗ[K] (Fin 4 ⊕ Fin 4 → K) => F ⟨v, hv⟩) key

end Diagram

end CFSG.SeitzReduction.TwistedE6Pilot
