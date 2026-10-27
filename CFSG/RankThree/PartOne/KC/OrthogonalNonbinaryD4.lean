module

public import CFSG.RankThree.PartOne.KC.OrthogonalNonbinaryEight
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalMatrixModelTransport
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinear

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalNonbinary

open Module QuadraticMap CFSG CFSG.Assembly CFSG.RankThree.Classical CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.PartOne.KCOrthogonalD4 CFSG.RankThree.PartOne.KCOrthogonalModel

section Generic

theorem symm_mem_centralizer_layerCentralizer {P T' : Type*} [Group P] [Group T']
    (ψ : MulAut P ≃* MulAut T') (D : Subgroup (MulAut T')) (a : MulAut P) (α : MulAut T')
    (h : ∀ δ ∈ layerCentralizer D (ψ a), α * δ = δ * α) :
    ψ.symm α ∈ Subgroup.centralizer
      ((layerCentralizer (D.comap ψ.toMonoidHom) a : Subgroup (MulAut P)) : Set (MulAut P)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro δ hδ
  have hmap := map_layerCentralizer ψ (D.comap ψ.toMonoidHom) a
  rw [Subgroup.map_comap_eq_self_of_surjective ψ.surjective D] at hmap
  have hψδ : ψ δ ∈ layerCentralizer D (ψ a) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hδ
  apply ψ.injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
  exact (h _ hψδ).symm

end Generic

section Transport

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem exists_matrix_data (hd : 0 < d) (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ S : Submodule K (Fin d → K), finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0) {p : ℕ}
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2)
    (α : MulAut (ProjOrthDerived Q))
    (hcent : ∀ a ∈ A, a ≠ 1 → ∀ δ ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
        ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
      α * (δ : MulAut (ProjOrthDerived Q)) = (δ : MulAut (ProjOrthDerived Q)) * α)
    (a : ProjOrthDerived Q) (haA : a ∈ A) (ha1 : a ≠ 1) :
    ∃ DP AP : Subgroup (MulAut (matrixProjectiveDerived Q)),
      OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ DP ∧
      AP ≤ OuterAutomorphisms.inner (matrixProjectiveDerived Q) ∧
      IsElementaryAbelian p AP ∧ Nat.card AP = p ^ 2 ∧
      liftConj Q hd a ∈ AP ∧ liftConj Q hd a ≠ 1 ∧
      (MulAut.congr (bridgeEquiv Q hd)).symm α ∈ Subgroup.centralizer
        ((layerCentralizer DP (liftConj Q hd a) : Subgroup (MulAut (matrixProjectiveDerived Q))) :
          Set (MulAut (matrixProjectiveDerived Q))) := by
  classical
  have hκinj : Function.Injective (liftConj Q hd) := fun c c' hcc =>
    (bridgeEquiv Q hd).symm.injective (conj_injective_matrixProjectiveDerived Q hd hnd hT hcc)
  have hinner : OuterAutomorphisms.inner (matrixProjectiveDerived Q) =
      (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range :=
    rfl
  refine ⟨D.comap (MulAut.congr (bridgeEquiv Q hd)).toMonoidHom, A.map (liftConj Q hd),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hinner]
    rintro _ ⟨g, rfl⟩
    show MulAut.congr (bridgeEquiv Q hd) (MulAut.conj g) ∈ D
    rw [OuterAutomorphisms.congr_conj]
    exact hD ⟨bridgeEquiv Q hd g, rfl⟩
  · rw [hinner]
    rintro _ ⟨c, -, rfl⟩
    exact ⟨(bridgeEquiv Q hd).symm c, rfl⟩
  · refine { is_comm := ⟨?_⟩, exponent_dvd_p := ?_ }
    · rintro ⟨_, c, hc, rfl⟩ ⟨_, c', hc', rfl⟩
      apply Subtype.ext
      have := hA.1
      have h1 : c * c' = c' * c := congrArg Subtype.val (mul_comm' (⟨c, hc⟩ : A) ⟨c', hc'⟩)
      show liftConj Q hd c * liftConj Q hd c' = liftConj Q hd c' * liftConj Q hd c
      rw [← map_mul, ← map_mul, h1]
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun g => ?_
      obtain ⟨_, c, hc, rfl⟩ := g
      apply Subtype.ext
      show (liftConj Q hd c) ^ p = 1
      rw [← map_pow (liftConj Q hd) c p, hA.2 c hc, map_one]
  · exact (Subgroup.card_map_of_injective hκinj (K := A)).trans hAc
  · exact Subgroup.mem_map_of_mem _ haA
  · intro h1
    exact ha1 (hκinj (h1.trans (map_one _).symm))
  · refine symm_mem_centralizer_layerCentralizer (MulAut.congr (bridgeEquiv Q hd)) D
      (liftConj Q hd a) α ?_
    rw [congr_liftConj Q hd a]
    intro δ hδ
    obtain ⟨δ', hδ', rfl⟩ := Subgroup.mem_map.mp hδ
    exact hcent a haA ha1 δ' hδ'

omit [Finite K] in
theorem exists_lift_of_orthDerived (hd : 0 < d) {p : ℕ} (hp : p.Prime) (a₀ : orthDerived Q)
    (ha₀p : a₀ ^ p = 1) (ha₀1 : a₀ ≠ 1) :
    ∃ x : matrixDerived Q, orderOf x = p ∧
      MulAut.conj (matrixProjectiveProjection Q x) = liftConj Q hd
        (QuotientGroup.mk' ((scalars K (Fin d → K)).subgroupOf (orthDerived Q)) a₀) ∧
      matrixFixedSpace x.val = LinearMap.ker
        (((a₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)).toLinearMap - LinearMap.id) := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨(derivedEquiv Q).symm a₀, ?_, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ha₀p, map_one]
    · intro h
      apply ha₀1
      have := congrArg (derivedEquiv Q) h
      rwa [MulEquiv.apply_symm_apply, map_one] at this
  · have h1 := bridgeEquiv_projection Q hd ((derivedEquiv Q).symm a₀)
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 : (bridgeEquiv Q hd).symm
        (QuotientGroup.mk' ((scalars K (Fin d → K)).subgroupOf (orthDerived Q)) a₀) =
        matrixProjectiveProjection Q ((derivedEquiv Q).symm a₀) :=
      (bridgeEquiv Q hd).symm_apply_eq.mpr h1.symm
    rw [liftConj_apply, h2]
  · have hlin : matrixLinearEquiv ((derivedEquiv Q).symm a₀).val =
        ((a₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) := by
      have h1 := derivedEquiv_val Q ((derivedEquiv Q).symm a₀)
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1.symm
    show LinearMap.ker ((matrixLinearEquiv ((derivedEquiv Q).symm a₀).val).toLinearMap - 1) = _
    rw [hlin]
    rfl

end Transport

end CFSG.RankThree.PartOne.KCOrthogonalNonbinary

namespace CFSG.RankThree.PartOne

open Module QuadraticMap CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCOrthogonalD4
  CFSG.RankThree.PartOne.KCOrthogonalNonbinary CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.RankThree.Classical2

theorem nonbinary_d4_induced_semilinear (G : Type) [Group G] {ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hpq : ¬ p ∣ Nat.card K ^ 2 - 1)
    (D : Subgroup (MulAut (ProjOrthDerived (coordinateQuadPlus 4 K))))
    (hD : (MulAut.conj : ProjOrthDerived (coordinateQuadPlus 4 K) →*
      MulAut (ProjOrthDerived (coordinateQuadPlus 4 K))).range ≤ D)
    (A : Subgroup (ProjOrthDerived (coordinateQuadPlus 4 K))) (hA : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) (α : MulAut (ProjOrthDerived (coordinateQuadPlus 4 K)))
    (hcent : ∀ a ∈ A, a ≠ 1 → ∀ δ ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
        ({MulAut.conj a} : Set (MulAut (ProjOrthDerived (coordinateQuadPlus 4 K))))),
      α * (δ : MulAut (ProjOrthDerived (coordinateQuadPlus 4 K))) =
        (δ : MulAut (ProjOrthDerived (coordinateQuadPlus 4 K))) * α) :
    InducedBySemilinear (coordinateQuadPlus 4 K) α := by
  obtain ⟨hchar, hnd, hT, -, -, -⟩ := coordinate_model_witness_plus h K hK e
  have hd : 0 < 2 * 4 := by norm_num
  have hpl : p ≠ ringChar K := by
    rw [hchar]
    exact hpℓ
  have hV : finrank K (Fin (2 * 4) → K) = 8 := by simp
  obtain ⟨a₀, ha₀p, ha₀A, ha₀1, hdim, hns⟩ :=
    exists_active_element_eight (coordinateQuadPlus 4 K) hnd hV hp hp3 hpl hpq A hA hAc
  have ha₀1' : a₀ ≠ 1 := fun h1 => ha₀1 (by rw [h1, map_one])
  obtain ⟨x, hxo, hxπ, hxW⟩ :=
    exists_lift_of_orthDerived (coordinateQuadPlus 4 K) hd hp a₀ ha₀p ha₀1'
  obtain ⟨DP, AP, hDP, hAPinner, hAPel, hAPcard, haPA, haP1, hαP⟩ :=
    exists_matrix_data (coordinateQuadPlus 4 K) hd hnd hT D hD A hA hAc α hcent _ ha₀A ha₀1
  have hdimP : 4 ≤ finrank K (matrixFixedSpace x.val) := by
    rw [hxW, hdim]
  have hnsP : ¬ ∃ S : Submodule K (matrixFixedSpace x.val), finrank K S = 2 ∧
      ∀ s ∈ S, ((coordinateQuadPlus 4 K).comp (matrixFixedSpace x.val).subtype) s = 0 := by
    rw [hxW]
    exact hns
  have hE : (MulAut.congr (bridgeEquiv (coordinateQuadPlus 4 K) hd)).symm α ∈
      matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      have : CharP K 2 := ringChar.of_eq hchar
      have hw := (even_D4_minus_four_fixed_component_point_family_witness G h K hK e hp hp3 AP
        hAPinner hAPel hAPcard _ haPA haP1).2 x hxo hxπ (by rw [hxW]; exact hdim)
        (fun S hS => by
          by_contra hcon
          push Not at hcon
          exact hnsP ⟨S, hS, fun s hs => hcon s hs⟩)
      exact hw.2.2.2.2 DP hDP hαP
    · have hw := (odd_D4_fixed_derived_component_point_family_witness G hℓ2 h K hK e hp hp3 hpℓ
        AP hAPinner hAPel hAPcard _ haPA haP1).2 x hxo hxπ hdimP
        (fun _ hsplit => by
          obtain ⟨-, hS⟩ := hsplit
          exact hnsP hS)
      exact hw.2.2.2.2.2 DP hDP hαP
  obtain ⟨σ, F, hF, μ, hμ, hQ, hind⟩ :=
    exists_semilin_of_mem_matrixProjectiveImage (coordinateQuadPlus 4 K) hd α hE
  exact ⟨σ, F, hF, μ, hμ, hQ, hind⟩

end CFSG.RankThree.PartOne
