module

public import CFSG.RankThree.SteinbergR3ECAOddD4Centralizer
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessTransport
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessSim

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalD4

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Reflection

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem exists_reflection_matrix (h2 : (2 : K) ≠ 0) [Finite K] {p : ℕ} {x : matrixDerived Q}
    (hx : OddOrderIsometry Q p (matrixLinearIso x.val)) {u v : Fin d → K}
    (hu : u ∈ matrixFixedSpace x.val) (hv : v ∈ matrixFixedSpace x.val) (hQu : Q u = 1)
    (hQv : Q v = 1) (huv : polar Q u v = 0) :
    ∃ g : matrixDerived Q, matrixLinearEquiv g.val = reflect Q u * reflect Q v ∧
      g.val ∈ supportedMatrix Q (matrixFixedSpace x.val) := by
  have hmem : reflect Q u * reflect Q v ∈
      supportedOrthDerived Q (fixedSpace (matrixLinearIso x.val)) :=
    reflect_mul_reflect_mem_supportedOrthDerived h2 hu hv hQu hQv huv
  have hΩ : reflect Q u * reflect Q v ∈ orthDerived Q := by
    rw [supportedOrthDerived_fixedSpace hx] at hmem
    exact hx.supportedFixedDerived_le_orthDerived hmem
  have hval : matrixLinearIso ((derivedEquiv Q).symm ⟨_, hΩ⟩).val = reflect Q u * reflect Q v := by
    have := derivedEquiv_val Q ((derivedEquiv Q).symm ⟨_, hΩ⟩)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨(derivedEquiv Q).symm ⟨_, hΩ⟩, hval, ?_⟩
  change matrixLinearIso ((derivedEquiv Q).symm ⟨_, hΩ⟩).val ∈
    supportedOrthDerived Q (fixedSpace (matrixLinearIso x.val))
  rw [hval]
  exact hmem

end Reflection

end CFSG.RankThree.PartOne.KCOrthogonalD4

namespace CFSG.RankThree.PartOne

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalD4 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.OddD4Centralizer

theorem odd_D4_fixed_derived_component_point_family_witness (G : Type) [Group G] {ℓ f : ℕ}
    (hℓ : ℓ ≠ 2) (h : StatedClassicalModel G .POmegaPlus 4 ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    (A : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))))
    (hAH : A ≤ OuterAutomorphisms.inner (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    (hA : CFSG.IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2)
    (a : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) (haA : a ∈ A)
    (ha1 : a ≠ 1) :
    (∃! x : matrixDerived (coordinateQuadPlus 4 K), orderOf x = p ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) x) = a) ∧
      ∀ x : matrixDerived (coordinateQuadPlus 4 K), orderOf x = p →
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) x) = a →
        4 ≤ finrank K (matrixFixedSpace x.val) →
        (Nat.card K = 3 →
          ¬ IsSplitFourSpace ((coordinateQuadPlus 4 K).comp (matrixFixedSpace x.val).subtype)) →
        OddD4Witness (coordinateQuadPlus 4 K) a (matrixFixedSpace x.val) := by
  have hℓp : ℓ.Prime := h.1.1
  obtain ⟨hchar, hnd, hT, -, -, -⟩ := coordinate_model_witness_plus h K hK e
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hℓp.odd_of_ne_two hℓ).pow
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hpl : p ≠ ringChar K := by
    rw [hchar]
    exact hpℓ
  have hd : 0 < 2 * 4 := by norm_num
  have hp2 : p ≠ 2 := by omega
  refine ⟨existsUnique_lift hd hnd hT hp hp2 hAH hA haA ha1, ?_⟩
  intro x hxp hxa hdim hq3
  have hx := oddOrderIsometry_matrix hnd hp hpl x hxp
  have hlist : FixedLayerListed (coordinateQuadPlus 4 K) (matrixLinearIso x.val) :=
    fixedLayerListed_of_odd hodd _ _ hdim hq3
  have hQW := hx.polarBilin_fixed_nondegenerate
  have hex : ∃ u ∈ matrixFixedSpace x.val, ∃ v ∈ matrixFixedSpace x.val,
      coordinateQuadPlus 4 K u = 1 ∧ coordinateQuadPlus 4 K v = 1 ∧
        polar (coordinateQuadPlus 4 K) u v = 0 := by
    obtain ⟨u, v, hu, hv, huv⟩ := exists_map_eq_one_orthogonal hodd
      ((coordinateQuadPlus 4 K).comp (matrixFixedSpace x.val).subtype) hQW hdim
    exact ⟨u, u.2, v, v.2, hu, hv, by rwa [polar_comp_subtype] at huv⟩
  obtain ⟨g₀, hg₀l, -, hg₀ord, hg₀cent, hg₀E, -⟩ :=
    odd_D4_two_reflection_full_centralizer_preserves_point_family G hℓ h K hK e
  have hr : ∀ y, coordinateQuadPlus 4 K (reindexVectorEquiv (plusIndexEquiv 4) y) =
      quadPlus 4 K y := reindexQuadraticForm_map (plusIndexEquiv 4) (quadPlus 4 K)
  have hQu₀ : coordinateQuadPlus 4 K (reindexVectorEquiv (plusIndexEquiv 4)
      (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1)) = 1 := by
    rw [hr]
    exact quadPlus_single_add_single 0
  have hQv₀ : coordinateQuadPlus 4 K (reindexVectorEquiv (plusIndexEquiv 4)
      (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) = 1 := by
    rw [hr]
    exact quadPlus_single_add_single 1
  have huv₀ : polar (coordinateQuadPlus 4 K) (reindexVectorEquiv (plusIndexEquiv 4)
      (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1))
      (reindexVectorEquiv (plusIndexEquiv 4)
        (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) = 0 := by
    rw [CFSG.RankThree.EvenD4Centralizer.polar_map_isometry
      (reindexVectorEquiv (K := K) (plusIndexEquiv 4)) hr, polar_single_add_single]
    simp
  have hg : ∀ u ∈ matrixFixedSpace x.val, ∀ v ∈ matrixFixedSpace x.val,
      coordinateQuadPlus 4 K u = 1 → coordinateQuadPlus 4 K v = 1 →
      polar (coordinateQuadPlus 4 K) u v = 0 →
      ∃ g : matrixDerived (coordinateQuadPlus 4 K),
        matrixLinearEquiv g.val = reflect (coordinateQuadPlus 4 K) u *
          reflect (coordinateQuadPlus 4 K) v ∧
        g.val ∈ supportedMatrix (coordinateQuadPlus 4 K) (matrixFixedSpace x.val) ∧
        orderOf (MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g)) = 2 ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) ∈
          supportedInner (coordinateQuadPlus 4 K) (matrixFixedSpace x.val) ∧
        Subgroup.centralizer
          ({MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g)} :
            Set (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) ≤
          matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    intro u hu v hv hQu hQv huv
    obtain ⟨g, hgl, hgS⟩ := exists_reflection_matrix h2 hx hu hv hQu hQv huv
    obtain ⟨k, hkO, hku, hkv⟩ := exists_isometry_pair h2 (coordinateQuadPlus 4 K) hQu hQv huv
      hQu₀ hQv₀ huv₀
    have hconj : k * (reflect (coordinateQuadPlus 4 K) u * reflect (coordinateQuadPlus 4 K) v) *
        k⁻¹ = matrixLinearEquiv g₀.val := by
      rw [hg₀l]
      calc k * (reflect (coordinateQuadPlus 4 K) u * reflect (coordinateQuadPlus 4 K) v) * k⁻¹ =
          (k * reflect (coordinateQuadPlus 4 K) u * k⁻¹) *
            (k * reflect (coordinateQuadPlus 4 K) v * k⁻¹) := by group
        _ = _ := by rw [reflect_conj hkO, reflect_conj hkO, hku, hkv]
    have hkM : matrixLinearIso.symm k ∈ matrixIsometries (coordinateQuadPlus 4 K) := by
      change matrixLinearIso (matrixLinearIso.symm k) ∈
        TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 4 K)
      rw [MulEquiv.apply_symm_apply]
      exact hkO
    have hconjM : matrixLinearIso.symm k * g.val * (matrixLinearIso.symm k)⁻¹ = g₀.val := by
      apply matrixLinearIso.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact (congrArg (fun z => k * z * k⁻¹) hgl).trans hconj
    obtain ⟨β, hβE, hβ⟩ := exists_mem_projectiveImage_apply_eq (coordinateQuadPlus 4 K) hkM hconjM
    refine ⟨g, hgl, hgS, ?_, mem_supportedInner.mpr ⟨g, hgS, rfl⟩, ?_⟩
    · have := orderOf_conj_eq_of_apply_eq β (matrixProjectiveProjection (coordinateQuadPlus 4 K) g)
      rw [hβ, hg₀ord] at this
      exact this.symm
    · exact centralizer_conj_le_of_apply_eq _ hβE hβ (hg₀cent.trans hg₀E.le)
  have hcJ : Subgroup.centralizer (supportedInner (coordinateQuadPlus 4 K)
      (matrixFixedSpace x.val) : Set (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) ≤
      matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    obtain ⟨u, hu, v, hv, hQu, hQv, huv⟩ := hex
    obtain ⟨g, -, -, -, hgJ, hgc⟩ := hg u hu v hv hQu hQv huv
    exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hgJ)).trans hgc
  have hlayer : ∀ D : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))),
      OuterAutomorphisms.inner (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ≤ D →
      supportedInner (coordinateQuadPlus 4 K) (matrixFixedSpace x.val) ≤ layerCentralizer D a :=
    fun D hD => supportedInner_le_layerCentralizer hd hnd hT hp hp3 hpl A hAH hA hAcard haA ha1 hxp
      hxa D hD hlist
  unfold OddD4Witness
  exact ⟨supportedMatrix_le_matrixDerived hx, hlayer, hex, hg, hcJ, fun D hD =>
    (Subgroup.centralizer_le (hlayer D hD)).trans hcJ⟩

end CFSG.RankThree.PartOne
