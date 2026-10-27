module

public import CFSG.RankThree.SteinbergR3ECAEvenD4Centralizer
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessTransport
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEvenHerm

public section

namespace CFSG.RankThree.PartOne

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalD4 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.EvenD4Centralizer CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial

theorem even_D4_minus_four_fixed_component_point_family_witness (G : Type) [Group G] {f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 2 f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (A : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))))
    (hAH : A ≤ OuterAutomorphisms.inner (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    (hA : CFSG.IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2)
    (a : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) (haA : a ∈ A)
    (ha1 : a ≠ 1) :
    (∃! x : matrixDerived (coordinateQuadPlus 4 K), orderOf x = p ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) x) = a) ∧
      ∀ x : matrixDerived (coordinateQuadPlus 4 K), orderOf x = p →
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) x) = a →
        finrank K (matrixFixedSpace x.val) = 4 →
        (∀ S : Submodule K (matrixFixedSpace x.val), finrank K S = 2 →
          ∃ s ∈ S, coordinateQuadPlus 4 K (s : Fin (2 * 4) → K) ≠ 0) →
        EvenD4Witness (coordinateQuadPlus 4 K) a (matrixFixedSpace x.val) := by
  obtain ⟨hchar, hnd, hT, -, -, -⟩ := coordinate_model_witness_plus h K hK e
  have hpl : p ≠ ringChar K := by
    rw [hchar]
    omega
  have hd : 0 < 2 * 4 := by norm_num
  have hp2 : p ≠ 2 := by omega
  refine ⟨existsUnique_lift hd hnd hT hp hp2 hAH hA haA ha1, ?_⟩
  intro x hxp hxa hdim hW2
  have hx := oddOrderIsometry_matrix hnd hp hpl x hxp
  have hlist : FixedLayerListed (coordinateQuadPlus 4 K) (matrixLinearIso x.val) :=
    fixedLayerListed_of_nonsplit_four _ _ hdim hW2
  have hQW := hx.polarBilin_fixed_nondegenerate
  obtain ⟨E, instF, instA, D, ψ, ρ, hψ, hρψ, -, -, hρrange, hsimple, -⟩ :=
    even_minus_four_actual_derived_extraction
      ((coordinateQuadPlus 4 K).comp (matrixFixedSpace x.val).subtype) hQW hdim hW2
  have hS : IsSimpleGroup ↥(supportedFixedDerived (coordinateQuadPlus 4 K)
      (matrixLinearIso x.val)) := by
    have h1 : IsSimpleGroup ↥⁅TauCeti.QuadraticMap.orthogonalGroup
        ((coordinateQuadPlus 4 K).comp (matrixFixedSpace x.val).subtype),
        TauCeti.QuadraticMap.orthogonalGroup
        ((coordinateQuadPlus 4 K).comp (matrixFixedSpace x.val).subtype)⁆ := by
      rw [hρrange]
      exact hsimple
    have h2 : IsSimpleGroup ↥(orthDerived ((coordinateQuadPlus 4 K).comp
        (fixedSpace (matrixLinearIso x.val)).subtype)) := h1
    exact (supportedFixedDerivedEquiv hx).isSimpleGroup
  have hexg : ∀ u v : matrixFixedSpace x.val, ψ u = hermU D → ψ v = hermI D →
      LinearIndependent K ![(u : Fin (2 * 4) → K), (v : Fin (2 * 4) → K)] ∧
      coordinateQuadPlus 4 K (u : Fin (2 * 4) → K) = 1 ∧
      coordinateQuadPlus 4 K (v : Fin (2 * 4) → K) = 1 ∧
      polar (coordinateQuadPlus 4 K) (u : Fin (2 * 4) → K) (v : Fin (2 * 4) → K) = 0 ∧
      ∃ g : matrixDerived (coordinateQuadPlus 4 K),
        (matrixLinearEquiv g.val : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)) =
          orthElementaryMap (coordinateQuadPlus 4 K)
            ((u : Fin (2 * 4) → K) + (v : Fin (2 * 4) → K)) (u : Fin (2 * 4) → K) ∧
        g.val ∈ supportedMatrix (coordinateQuadPlus 4 K) (matrixFixedSpace x.val) ∧
        g ≠ 1 ∧ g * g = 1 ∧
        (∀ w : matrixFixedSpace x.val, matrixLinearEquiv g.val (w : Fin (2 * 4) → K) =
          (ψ.symm (hermFourRho D (hermSwap D) (ψ w)) : Fin (2 * 4) → K)) ∧
        (∀ z ∈ orthPerp (coordinateQuadPlus 4 K) (matrixFixedSpace x.val),
          matrixLinearEquiv g.val z = z) ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) ∈
          supportedInner (coordinateQuadPlus 4 K) (matrixFixedSpace x.val) ∧
        ∀ α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
          α ∈ Subgroup.centralizer
            ({MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g)} :
              Set (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) →
          α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    intro u v hu hv
    have hQu : coordinateQuadPlus 4 K (u : Fin (2 * 4) → K) = 1 := by
      have h1 := hψ u
      rw [hu, hermFourForm_hermU] at h1
      exact h1.symm
    have hQv : coordinateQuadPlus 4 K (v : Fin (2 * 4) → K) = 1 := by
      have h1 := hψ v
      rw [hv, hermFourForm_hermI] at h1
      exact h1.symm
    have huv : polar (coordinateQuadPlus 4 K) (u : Fin (2 * 4) → K) (v : Fin (2 * 4) → K) = 0 := by
      have h1 := polar_map_isometry ψ hψ u v
      rw [hu, hv, polar_hermU_hermI] at h1
      rw [← polar_comp_subtype (Q := coordinateQuadPlus 4 K) (matrixFixedSpace x.val) u v]
      exact h1.symm
    have hLI : LinearIndependent K ![(u : Fin (2 * 4) → K), (v : Fin (2 * 4) → K)] := by
      have h1 : LinearIndependent K ![u, v] := by
        have := (linearIndependent_hermU_hermI D).map' ψ.symm.toLinearMap (LinearEquiv.ker ψ.symm)
        convert this using 1
        ext i : 1
        fin_cases i
        · exact (ψ.symm_apply_eq.mpr hu.symm).symm
        · exact (ψ.symm_apply_eq.mpr hv.symm).symm
      have := h1.map' (matrixFixedSpace x.val).subtype (Submodule.ker_subtype _)
      convert this using 1
      ext i : 1
      fin_cases i <;> rfl
    obtain ⟨g, hgl, hgf, hg1, hgg, -, hα, -, -, -⟩ :=
      even_D4_rank_two_involution_full_centralizer_preserves_point_family G h K hK e hLI hQu hQv
        huv
    have hρ : ∀ r : matrixFixedSpace x.val, (ρ (hermSwap D) r : Fin (2 * 4) → K) =
        (r : Fin (2 * 4) → K) + polar (coordinateQuadPlus 4 K) (r : Fin (2 * 4) → K)
          (u : Fin (2 * 4) → K) • (u : Fin (2 * 4) → K) +
        polar (coordinateQuadPlus 4 K) (r : Fin (2 * 4) → K) (v : Fin (2 * 4) → K) •
          (v : Fin (2 * 4) → K) := by
      intro r
      have e1 : polar (hermFourForm D) (ψ r) (hermU D) =
          polar (coordinateQuadPlus 4 K) (r : Fin (2 * 4) → K) (u : Fin (2 * 4) → K) := by
        rw [← hu, polar_map_isometry ψ hψ, polar_comp_subtype]
      have e2 : polar (hermFourForm D) (ψ r) (hermI D) =
          polar (coordinateQuadPlus 4 K) (r : Fin (2 * 4) → K) (v : Fin (2 * 4) → K) := by
        rw [← hv, polar_map_isometry ψ hψ, polar_comp_subtype]
      have h1 : ρ (hermSwap D) r = r +
          polar (coordinateQuadPlus 4 K) (r : Fin (2 * 4) → K) (u : Fin (2 * 4) → K) • u +
          polar (coordinateQuadPlus 4 K) (r : Fin (2 * 4) → K) (v : Fin (2 * 4) → K) • v := by
        apply ψ.injective
        rw [hρψ, hermFourRho_swap_apply, e1, e2, map_add, map_add, map_smul, map_smul, hu, hv]
      rw [h1, Submodule.coe_add, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul]
    have hgW : ∀ r : matrixFixedSpace x.val, matrixLinearEquiv g.val (r : Fin (2 * 4) → K) =
        (ρ (hermSwap D) r : Fin (2 * 4) → K) := fun r => by
      rw [hρ r, hgf (r : Fin (2 * 4) → K)]
    have hperp : ∀ z ∈ orthPerp (coordinateQuadPlus 4 K) (matrixFixedSpace x.val),
        matrixLinearEquiv g.val z = z := by
      intro z hz
      rw [mem_orthPerp] at hz
      have hz1 := hz u u.2
      have hz2 := hz v v.2
      rw [hgf z, polar_comm _ z, hz1, polar_comm _ z, hz2, zero_smul, zero_smul, add_zero,
        add_zero]
    have hgS : g.val ∈ supportedMatrix (coordinateQuadPlus 4 K) (matrixFixedSpace x.val) := by
      change matrixLinearIso g.val ∈
        supportedOrthDerived (coordinateQuadPlus 4 K) (matrixFixedSpace x.val)
      refine ⟨ρ (hermSwap D), ?_, fun r => hgW r, hperp⟩
      have hmem : ρ (hermSwap D) ∈ ρ.range := ⟨hermSwap D, rfl⟩
      rw [← hρrange] at hmem
      exact hmem
    refine ⟨hLI, hQu, hQv, huv, g, hgl, hgS, hg1, hgg, fun w => ?_, hperp,
      mem_supportedInner.mpr ⟨g, hgS, rfl⟩, fun α hα' => ?_⟩
    · rw [hgW w]
      congr 1
      rw [ψ.eq_symm_apply, hρψ]
    · exact (hα α (mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp hα'))).2
  have hcJ : Subgroup.centralizer (supportedInner (coordinateQuadPlus 4 K)
      (matrixFixedSpace x.val) : Set (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) ≤
      matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    obtain ⟨-, -, -, -, g, -, -, -, -, -, -, hgJ, hgc⟩ :=
      hexg (ψ.symm (hermU D)) (ψ.symm (hermI D)) (by simp) (by simp)
    exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hgJ)).trans fun α hα => hgc α hα
  have hlayer : ∀ B : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))),
      OuterAutomorphisms.inner (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ≤ B →
      supportedInner (coordinateQuadPlus 4 K) (matrixFixedSpace x.val) ≤ layerCentralizer B a :=
    fun B hB => supportedInner_le_layerCentralizer hd hnd hT hp hp3 hpl A hAH hA hAcard haA ha1 hxp
      hxa B hB hlist
  unfold EvenD4Witness
  exact ⟨supportedMatrix_le_matrixDerived hx, fun B hB => supportedInner_isComponent hd hnd hT hp
    hp3 hpl A hAH hA hAcard haA ha1 hxp hxa hS B hB hlist, ⟨E, instF, instA, D, ψ, hψ, hexg⟩, hcJ,
    fun B hB => (Subgroup.centralizer_le (hlayer B hB)).trans hcJ⟩

end CFSG.RankThree.PartOne
