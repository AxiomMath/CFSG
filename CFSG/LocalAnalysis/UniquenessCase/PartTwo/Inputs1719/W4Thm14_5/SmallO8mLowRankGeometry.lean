module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusModel
import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Module QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Spin.Twisted CFSG.RankThree.OrthogonalInvolutions
open CFSG.ClassicalGroups.Orthogonal

namespace SmallO8mLowRankGeometry

variable {K : Type} [Field K] {b c : K}

private abbrev FixShortBlock (r : Vm 4 K ≃ₗ[K] Vm 4 K) : Prop :=
  r (eVec 4 2) = eVec 4 2 ∧ r (fVec 4 2) = fVec 4 2 ∧
    ∀ p : Fin 2 → K, r (planeVec 4 p) = planeVec 4 p

private theorem independent_first_pair {w : Vm 4 K}
    (h0 : w (.inl 0) = 0) (h1 : w (.inl 1) = 1) :
    LinearIndependent K ![eVec 4 0, w] := by
  rw [LinearIndependent.pair_iff]
  intro a d h
  have ha := congrFun h (.inl 0)
  have hd := congrFun h (.inl 1)
  constructor
  · simpa [eVec, Pi.single_apply, h0] using ha
  · simpa [eVec, Pi.single_apply, h1] using hd

private theorem range_eichler_first {w : Vm 4 K}
    (hQ : (polarBilin (quadMinus 4 K b c)).Nondegenerate)
    (horth : polar (quadMinus 4 K b c) (eVec 4 0) w = 0)
    (hli : LinearIndependent K ![eVec 4 0, w]) :
    commSpace (eichler (quadMinus 4 K b c) (eVec 4 0) w) =
      Submodule.span K {eVec 4 0, w} :=
  le_antisymm (commSpace_eichler_le_span _ _)
    (span_le_commSpace_eichler hQ (quadMinus_eVec 4 b c 0) horth hli)

private theorem finrank_eichler_first {w : Vm 4 K}
    (hQ : (polarBilin (quadMinus 4 K b c)).Nondegenerate)
    (horth : polar (quadMinus 4 K b c) (eVec 4 0) w = 0)
    (hli : LinearIndependent K ![eVec 4 0, w]) :
    finrank K (commSpace (eichler (quadMinus 4 K b c) (eVec 4 0) w)) = 2 := by
  rw [range_eichler_first hQ horth hli]
  have h := finrank_span_eq_card hli
  rw [Matrix.range_cons_cons_empty, Fintype.card_fin] at h
  exact h

private theorem eichler_sq [CharP K 2] {u w : Vm 4 K}
    (horth : polar (quadMinus 4 K b c) u w = 0) :
    eichler (quadMinus 4 K b c) u w * eichler (quadMinus 4 K b c) u w = 1 := by
  rw [eichler_mul horth horth, CharTwo.add_self_eq_zero, eichler_zero_right]

private theorem fixes_short_block_eichler {w : Vm 4 K}
    (he : polar (quadMinus 4 K b c) (eVec 4 2) w = 0)
    (hf : polar (quadMinus 4 K b c) (fVec 4 2) w = 0)
    (hp : ∀ p : Fin 2 → K, polar (quadMinus 4 K b c) (planeVec 4 p) w = 0) :
    FixShortBlock (eichler (quadMinus 4 K b c) (eVec 4 0) w) := by
  refine ⟨eichler_apply_of_polar_eq_zero (polar_eVec_eVec 4 b c 2 0) he,
    eichler_apply_of_polar_eq_zero (by rw [polar_fVec_eVec 4 b c 2 0]; norm_num) hf, ?_⟩
  intro p
  exact eichler_apply_of_polar_eq_zero (polar_planeVec_eVec 4 b c p 0) (hp p)

private theorem reflection_representative [Finite K] [CharP K 2]
    (hirrQ : ∀ z : K, z ^ 2 + b * z + c ≠ 0) :
    ∃ r : Vm 4 K ≃ₗ[K] Vm 4 K,
      r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) ∧
      r * r = 1 ∧ finrank K (commSpace r) = 1 ∧ FixShortBlock r := by
  let v : Vm 4 K := eVec 4 0 + fVec 4 0
  have hv : quadMinus 4 K b c v = 1 := by
    rw [quadMinus_apply 4 K b c]
    simp [v, eVec, fVec, Pi.single_apply]
  let _ : Invertible (quadMinus 4 K b c v) := invertibleOfNonzero (by rw [hv]; exact one_ne_zero)
  refine ⟨TauCeti.QuadraticMap.reflection (quadMinus 4 K b c) v,
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup _ _,
    TauCeti.QuadraticMap.reflection_mul_self _ _,
    finrank_commSpace_reflection (nondegenerate_polarBilin_quadMinus_of_finite 4 K hirrQ) v, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [TauCeti.QuadraticMap.reflection_apply]
      have hpol : polar (quadMinus 4 K b c) v (eVec 4 2) = 0 := by
        dsimp only [v]
        rw [polar_add_left, polar_eVec_eVec 4 b c 0 2, polar_fVec_eVec 4 b c 0 2]
        simp
      rw [hpol]
      simp
    · rw [TauCeti.QuadraticMap.reflection_apply]
      have hpol : polar (quadMinus 4 K b c) v (fVec 4 2) = 0 := by
        dsimp only [v]
        rw [polar_add_left, polar_eVec_fVec 4 b c 0 2, polar_fVec_fVec 4 b c 0 2]
        simp
      rw [hpol]
      simp
    · intro p
      rw [TauCeti.QuadraticMap.reflection_apply]
      have hpol : polar (quadMinus 4 K b c) v (planeVec 4 p) = 0 := by
        dsimp only [v]
        rw [polar_add_left, polar_eVec_planeVec 4 b c 0 p,
          polar_fVec_planeVec 4 b c 0 p, add_zero]
      rw [hpol]
      simp

private theorem singular_representative [Finite K] [CharP K 2]
    (hirrQ : ∀ z : K, z ^ 2 + b * z + c ≠ 0) :
    ∃ r : Vm 4 K ≃ₗ[K] Vm 4 K,
      r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) ∧
      r * r = 1 ∧ finrank K (commSpace r) = 2 ∧
      (∀ x ∈ commSpace r, quadMinus 4 K b c x = 0) ∧ FixShortBlock r := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 4 K hirrQ
  have horth := polar_eVec_eVec 4 b c 0 1
  have hli : LinearIndependent K ![eVec 4 0, eVec 4 1] :=
    independent_first_pair (by simp [eVec]) (by simp [eVec])
  refine ⟨eichler (quadMinus 4 K b c) (eVec 4 0) (eVec 4 1),
    eichler_mem_orthogonalGroup _ _ _, eichler_sq horth,
    finrank_eichler_first hQ horth hli, ?_, ?_⟩
  · intro x hx
    rw [range_eichler_first hQ horth hli, Submodule.mem_span_pair] at hx
    obtain ⟨a, d, rfl⟩ := hx
    rw [QuadraticMap.map_add (f := quadMinus 4 K b c),
      QuadraticMap.map_smul (quadMinus 4 K b c),
      QuadraticMap.map_smul (quadMinus 4 K b c), quadMinus_eVec 4 b c 0, quadMinus_eVec 4 b c 1,
      polar_smul_left, polar_smul_right, polar_eVec_eVec 4 b c 0 1]
    simp
  · exact fixes_short_block_eichler (polar_eVec_eVec 4 b c 2 1)
      (by rw [polar_fVec_eVec 4 b c 2 1]; norm_num) (fun p => polar_planeVec_eVec 4 b c p 1)

private theorem nonsingular_representative [Finite K] [CharP K 2]
    (hirrQ : ∀ z : K, z ^ 2 + b * z + c ≠ 0) :
    ∃ r : Vm 4 K ≃ₗ[K] Vm 4 K,
      r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) ∧
      r * r = 1 ∧ finrank K (commSpace r) = 2 ∧
      (∃ x ∈ commSpace r, quadMinus 4 K b c x ≠ 0) ∧ FixShortBlock r := by
  let w : Vm 4 K := eVec 4 1 + fVec 4 1
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 4 K hirrQ
  have horth : polar (quadMinus 4 K b c) (eVec 4 0) w = 0 := by
    dsimp only [w]
    rw [polar_add_right, polar_eVec_eVec 4 b c 0 1, polar_eVec_fVec 4 b c 0 1]
    simp
  have hli : LinearIndependent K ![eVec 4 0, w] :=
    independent_first_pair (by simp [w, eVec, fVec])
      (by simp [w, eVec, fVec])
  refine ⟨eichler (quadMinus 4 K b c) (eVec 4 0) w,
    eichler_mem_orthogonalGroup _ _ _, eichler_sq horth,
    finrank_eichler_first hQ horth hli, ?_, ?_⟩
  · refine ⟨w, ?_, ?_⟩
    · rw [range_eichler_first hQ horth hli]
      exact Submodule.subset_span (by simp)
    · have hw : quadMinus 4 K b c w = 1 := by
        rw [quadMinus_apply 4 K b c]
        simp [w, eVec, fVec, Pi.single_apply]
      rw [hw]
      exact one_ne_zero
  · exact fixes_short_block_eichler
      (by dsimp only [w]; rw [polar_add_right, polar_eVec_eVec 4 b c 2 1,
        polar_eVec_fVec 4 b c 2 1]; simp)
      (by dsimp only [w]; rw [polar_add_right, polar_fVec_eVec 4 b c 2 1,
        polar_fVec_fVec 4 b c 2 1]; simp)
      (fun p => by dsimp only [w]; rw [polar_add_right, polar_planeVec_eVec 4 b c p 1,
        polar_planeVec_fVec 4 b c p 1, add_zero])

end SmallO8mLowRankGeometry

theorem exists_conj_fix_short_block_of_rank_le_two
    {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirrQ : ∀ r : K, r ^ 2 + b * r + c ≠ 0)
    {s : Vm 4 K ≃ₗ[K] Vm 4 K}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c))
    (hs2 : s * s = 1)
    (hrank : finrank K (LinearMap.range (s.toLinearMap - 1)) ≤ 2) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c),
      (g * s * g⁻¹) (eVec 4 2) = eVec 4 2 ∧
      (g * s * g⁻¹) (fVec 4 2) = fVec 4 2 ∧
      ∀ p : Fin 2 → K, (g * s * g⁻¹) (planeVec 4 p) = planeVec 4 p := by
  classical
  by_cases hs1 : s = 1
  · subst s
    exact ⟨1, Subgroup.one_mem _, by simp⟩
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 4 K hirrQ
  have hsord : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  have hpos := one_le_finrank_commSpace hs1
  change finrank K (commSpace s) ≤ 2 at hrank
  have hreps : ∃ r : Vm 4 K ≃ₗ[K] Vm 4 K,
      r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) ∧
      r * r = 1 ∧ finrank K (commSpace r) = finrank K (commSpace s) ∧
      suzukiLetter (quadMinus 4 K b c) r = suzukiLetter (quadMinus 4 K b c) s ∧
      SmallO8mLowRankGeometry.FixShortBlock r := by
    by_cases hr1 : finrank K (commSpace s) = 1
    · obtain ⟨r, hrO, hr2, hrank1, hfix⟩ :=
        SmallO8mLowRankGeometry.reflection_representative hirrQ
      refine ⟨r, hrO, hr2, hrank1.trans hr1.symm, ?_, hfix⟩
      exact (suzukiLetter_eq_b_iff.mpr (by rw [hrank1]; decide)).trans
        (suzukiLetter_eq_b_iff.mpr (by rw [hr1]; decide)).symm
    · have hr2 : finrank K (commSpace s) = 2 := by omega
      by_cases hzero : ∀ x ∈ commSpace s, quadMinus 4 K b c x = 0
      · obtain ⟨r, hrO, hrr, hrank2, hrzero, hfix⟩ :=
          SmallO8mLowRankGeometry.singular_representative hirrQ
        refine ⟨r, hrO, hrr, hrank2.trans hr2.symm, ?_, hfix⟩
        exact (suzukiLetter_eq_a_iff.mpr ⟨by rw [hrank2]; decide, hrzero⟩).trans
          (suzukiLetter_eq_a_iff.mpr ⟨by rw [hr2]; decide, hzero⟩).symm
      · push Not at hzero
        obtain ⟨r, hrO, hrr, hrank2, hrnon, hfix⟩ :=
          SmallO8mLowRankGeometry.nonsingular_representative hirrQ
        refine ⟨r, hrO, hrr, hrank2.trans hr2.symm, ?_, hfix⟩
        exact (suzukiLetter_eq_c_iff.mpr ⟨by rw [hrank2]; decide, hrnon⟩).trans
          (suzukiLetter_eq_c_iff.mpr ⟨by rw [hr2]; decide, hzero⟩).symm
  obtain ⟨r, hrO, hr2, hdim, hletter, hfix⟩ := hreps
  have hr1 : r ≠ 1 := by
    rintro rfl
    have hz : commSpace (1 : Vm 4 K ≃ₗ[K] Vm 4 K) = ⊥ := by
      change LinearMap.range (LinearMap.id - LinearMap.id) = ⊥
      rw [sub_self, LinearMap.range_zero]
    have hzero : finrank K (commSpace s) = 0 := hdim.symm.trans (by rw [hz, finrank_bot])
    omega
  have hrord : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1
  obtain ⟨g, hg, hgs⟩ := (isConj_iff_suzukiLetter_eq hQ hs hsord hrO hrord).mpr ⟨hletter, hdim⟩
  exact ⟨g, hg, by simpa only [hgs] using hfix⟩

theorem exists_spin_conj_fix_short_block_of_rank_le_two
    {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirrQ : ∀ r : K, r ^ 2 + b * r + c ≠ 0)
    {s : Vm 4 K ≃ₗ[K] Vm 4 K}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c))
    (hs2 : s * s = 1)
    (hrank : Module.finrank K (LinearMap.range (s.toLinearMap - 1)) ≤ 2) :
    ∃ u : spinGroup (quadMinus 4 K b c),
      let g := spinAction (quadMinus 4 K b c) u
      (g * s * g⁻¹) (eVec 4 2) = eVec 4 2 ∧
      (g * s * g⁻¹) (fVec 4 2) = fVec 4 2 ∧
      ∀ p : Fin 2 → K, (g * s * g⁻¹) (planeVec 4 p) = planeVec 4 p := by
  classical
  obtain ⟨g, hgO, he, hf, hp⟩ := exists_conj_fix_short_block_of_rank_le_two hirrQ hs hs2 hrank
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 4 K hirrQ
  have hspin : ∀ d : Vm 4 K ≃ₗ[K] Vm 4 K, d ∈ omegaGroup (quadMinus 4 K b c) hQ →
      ∃ u : spinGroup (quadMinus 4 K b c), spinAction (quadMinus 4 K b c) u = d :=
    fun d hd => CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_minus
      hirrQ (by norm_num) hd
  by_cases hgeven : Even (finrank K (commSpace g))
  · obtain ⟨u, hu⟩ := hspin g ⟨hgO, hgeven⟩
    refine ⟨u, ?_⟩
    dsimp only
    rw [hu]
    exact ⟨he, hf, hp⟩
  let v : Vm 4 K := eVec 4 2 + fVec 4 2
  have hv : quadMinus 4 K b c v = 1 := by
    rw [quadMinus_apply 4 K b c]
    simp [v, eVec, fVec, Pi.single_apply]
  let _ : Invertible (quadMinus 4 K b c v) := invertibleOfNonzero (by rw [hv]; exact one_ne_zero)
  let r : Vm 4 K ≃ₗ[K] Vm 4 K := TauCeti.QuadraticMap.reflection (quadMinus 4 K b c) v
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup _ _
  have hgv : (g * s * g⁻¹) v = v := by
    dsimp only [v]
    rw [map_add, he, hf]
  have hconjO : g * s * g⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) :=
    mul_mem (mul_mem hgO hs) (inv_mem hgO)
  have hcomm : (g * s * g⁻¹) * r = r * (g * s * g⁻¹) :=
    reflection_mul_comm hconjO hgv
  have heven : Even (finrank K (commSpace (r * g))) := by
    rw [← ZMod.natCast_eq_zero_iff_even,
      natCast_finrank_commSpace_mul hQ hrO hgO,
      finrank_commSpace_reflection hQ v,
      (ZMod.natCast_eq_one_iff_odd).mpr (Nat.not_even_iff_odd.mp hgeven), Nat.cast_one]
    rfl
  obtain ⟨u, hu⟩ := hspin (r * g) ⟨mul_mem hrO hgO, heven⟩
  have hsame : (r * g) * s * (r * g)⁻¹ = g * s * g⁻¹ := by
    calc
      (r * g) * s * (r * g)⁻¹ = r * (g * s * g⁻¹) * r⁻¹ := by group
      _ = (g * s * g⁻¹) * r * r⁻¹ := by rw [← hcomm]
      _ = g * s * g⁻¹ := by group
  refine ⟨u, ?_⟩
  dsimp only
  rw [hu, hsame]
  exact ⟨he, hf, hp⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
