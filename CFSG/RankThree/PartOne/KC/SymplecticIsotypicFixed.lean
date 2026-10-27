module

public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.RankThree.PartOne.KC.AlternatingSymplecticBasis
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartOne.KCSpIsotypic

open Module CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCAlternating CFSG.ClassicalGroups.Alternating CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

omit [FiniteDimensional K W] in
theorem bilinIsometryGroup_eq_sesqUnitaryGroup (B : LinearMap.BilinForm K W) :
    bilinIsometryGroup B = sesqUnitaryGroup B :=
  Subgroup.ext fun _ => Iff.rfl

theorem exists_mulEquiv_sesqUnitaryGroup_statedSp {B : LinearMap.BilinForm K W} (hB : B.IsAlt)
    (hn : B.Nondegenerate) :
    ∃ s : ℕ, finrank K W = 2 * s ∧ Nonempty (sesqUnitaryGroup B ≃* StatedSp s K) := by
  obtain ⟨s, b, hfin, -⟩ := exists_isSymplecticBasis hB hn
  have hfin' : finrank K W = finrank K (Fin s ⊕ Fin s → K) := by
    rw [hfin, Module.finrank_fintype_fun_eq_card]
    simp [two_mul]
  obtain ⟨φ, hφ⟩ := exists_isometry_of_finrank_eq hB hn (spForm_isAlt (r := s) (K := K))
    (spForm_nondegenerate (r := s) (K := K)) hfin'
  refine ⟨s, hfin, ⟨?_⟩⟩
  let e1 : LinearMap.GeneralLinearGroup K W ≃* LinearMap.GeneralLinearGroup K (Fin s ⊕ Fin s → K) :=
    LinearMap.GeneralLinearGroup.congrLinearEquiv φ
  have hmap : (sesqUnitaryGroup B).map e1.toMonoidHom = sesqUnitaryGroup (spForm s K) := by
    ext g'
    constructor
    · rintro ⟨g, hg, rfl⟩ u' v'
      have h1 := hg (φ.symm u') (φ.symm v')
      have h2 : ∀ w : Fin s ⊕ Fin s → K, ((e1 g : LinearMap.GeneralLinearGroup K
          (Fin s ⊕ Fin s → K)) : Module.End K (Fin s ⊕ Fin s → K)) w =
            φ (((g : LinearMap.GeneralLinearGroup K W) : Module.End K W) (φ.symm w)) := fun w => rfl
      rw [show (e1.toMonoidHom g : LinearMap.GeneralLinearGroup K (Fin s ⊕ Fin s → K)) = e1 g
        from rfl, h2, h2, hφ, h1, ← hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    · intro hg'
      refine ⟨e1.symm g', ?_, e1.apply_symm_apply g'⟩
      intro u v
      have h3 := hg' (φ u) (φ v)
      have h2 : ∀ w : W, ((g' : LinearMap.GeneralLinearGroup K (Fin s ⊕ Fin s → K)) :
          Module.End K (Fin s ⊕ Fin s → K)) (φ w) =
            φ (((e1.symm g' : LinearMap.GeneralLinearGroup K W) : Module.End K W) w) := by
        intro w
        simp [e1]
      rw [h2, h2, hφ, hφ] at h3
      exact h3
  let e2 : sesqUnitaryGroup B ≃* ↥((sesqUnitaryGroup B).map e1.toMonoidHom) :=
    (sesqUnitaryGroup B).equivMapOfInjective e1.toMonoidHom e1.injective
  exact ((e2.trans (MulEquiv.subgroupCongr hmap)).trans
    (MulEquiv.subgroupCongr range_spLin.symm)).trans
    (MonoidHom.ofInjective (spLin_injective (r := s) (K := K))).symm

theorem isQuasisimple_sesqUnitaryGroup_of_alt {B : LinearMap.BilinForm K W} (hB : B.IsAlt)
    (hn : B.Nondegenerate) (h2 : 2 ≤ finrank K W)
    (hK : 4 ≤ Nat.card K ∨ (Nat.card K = 3 ∧ 4 ≤ finrank K W) ∨
      (Nat.card K = 2 ∧ 6 ≤ finrank K W)) :
    CFSG.IsQuasisimple (sesqUnitaryGroup B) := by
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  have hs1 : 1 ≤ s := by omega
  have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs1 (by
    rcases hK with h4 | ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inl (Or.inr h4)
    · exact Or.inr (Or.inl ⟨h3, by omega⟩)
    · exact Or.inr (Or.inr ⟨h3, by omega⟩))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq

theorem exists_smul_of_commute_sesqUnitaryGroup_alt {B : LinearMap.BilinForm K W} (hB : B.IsAlt)
    (hn : B.Nondegenerate) (γ : Module.End K W)
    (h : ∀ g ∈ sesqUnitaryGroup B, Commute γ (g : Module.End K W)) :
    ∃ c : K, ∀ w, γ w = c • w := by
  have key : ∀ v : W, ∃ c : K, γ v = c • v := by
    intro v
    by_cases hv : v = 0
    · exact ⟨0, by rw [hv, map_zero, smul_zero]⟩
    obtain ⟨u, hu⟩ : ∃ u, B u v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv (hn.2 v hcon)
    set T := symplecticTransvection B hB v ((B u v)⁻¹) with hT
    have hTmem : T ∈ sesqUnitaryGroup B := by
      rw [← bilinIsometryGroup_eq_sesqUnitaryGroup]
      exact symplecticTransvection_mem_bilinIsometryGroup hB v _
    have hcomm := congrArg (fun f : Module.End K W => f u) (h T hTmem).eq
    simp only [Module.End.mul_apply] at hcomm
    have hTu : (T : Module.End K W) u = u + v := by
      rw [hT, symplecticTransvection_apply, inv_mul_cancel₀ hu, one_smul]
    rw [hTu, map_add, hT, symplecticTransvection_apply] at hcomm
    exact ⟨_, add_left_cancel hcomm⟩
  have hnl : ∀ v : W, ¬ LinearIndependent K ![v, γ v] := by
    intro v hli
    obtain ⟨c, hc⟩ := key v
    have := (LinearIndependent.pair_iff.mp hli) (-c) 1 (by
      simp only [one_smul, neg_smul, hc]
      exact neg_add_cancel _)
    exact one_ne_zero this.2
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hnl
  exact ⟨c, fun w => by rw [hc]; simp⟩

end CFSG.RankThree.PartOne.KCSpIsotypic
