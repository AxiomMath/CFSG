module

public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.Blueprint.ChevalleyRoots

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts
open scoped commutatorElement

namespace GGRootF4

abbrev i0 : Fin (Tag.rank .F4) := ⟨0, by decide⟩
abbrev i1 : Fin (Tag.rank .F4) := ⟨1, by decide⟩
abbrev i2 : Fin (Tag.rank .F4) := ⟨2, by decide⟩
abbrev i3 : Fin (Tag.rank .F4) := ⟨3, by decide⟩

@[expose] def theta : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

@[expose] def thetaS : Fin (Tag.rank .F4) → ℤ := ![1, 2, 3, 2]

@[expose] def rootNine : Fin (Tag.rank .F4) → ℤ := ![1, 2, 4, 2]

@[expose] def rootTen : Fin (Tag.rank .F4) → ℤ := ![1, 3, 4, 2]

theorem root_facts_check : ∀ k < 48,
    height (f4Certificate.root k) ≤ 11 ∧
    (9 ≤ height (f4Certificate.root k) →
      (f4Certificate.root k = rootNine ∨ f4Certificate.root k = rootTen ∨
        f4Certificate.root k = theta)) := by
  decide +kernel

theorem length_roots : f4Certificate.roots.length = 48 := by
  decide +kernel

section Roots

theorem height_le_of_isRoot {v : Fin (Tag.rank .F4) → ℤ} (hv : IsRoot .F4 v) : height v ≤ 11 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff f4Certificate_check).1 hv
  exact (root_facts_check k (length_roots ▸ hk)).1

theorem eq_of_nine_le_height {v : Fin (Tag.rank .F4) → ℤ} (hv : IsRoot .F4 v)
    (h : 9 ≤ height v) : v = rootNine ∨ v = rootTen ∨ v = theta := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff f4Certificate_check).1 hv
  exact (root_facts_check k (length_roots ▸ hk)).2 h

theorem isRoot_of_exists {v : Fin (Tag.rank .F4) → ℤ}
    (h : ∃ k < 48, f4Certificate.root k = v) : IsRoot .F4 v :=
  (RootCertificate.isRoot_iff f4Certificate_check).2 (length_roots ▸ h)

theorem isRoot_theta : IsRoot .F4 theta := isRoot_of_exists (by decide +kernel)

theorem isRoot_thetaS : IsRoot .F4 thetaS := isRoot_of_exists (by decide +kernel)

theorem isRoot_sub_two_smul_thetaS {v : Fin (Tag.rank .F4) → ℤ}
    (hv : v = rootNine ∨ v = rootTen ∨ v = theta) : IsRoot .F4 (v - 2 • thetaS) := by
  rcases hv with rfl | rfl | rfl <;> exact isRoot_of_exists (by decide +kernel)

end Roots

theorem theta_eq_reflect :
    reflect .F4 i0 (reflect .F4 i1 (reflect .F4 i2 (reflect .F4 i1 (reflect .F4 i3
      (reflect .F4 i2 (reflect .F4 i1 (Pi.single i0 1))))))) = theta := by
  decide +kernel

theorem thetaS_eq_reflect :
    reflect .F4 i3 (reflect .F4 i2 (reflect .F4 i1 (reflect .F4 i2 (reflect .F4 i0
      (reflect .F4 i1 (reflect .F4 i2 (Pi.single i3 1))))))) = thetaS := by
  decide +kernel

noncomputable abbrev sF4 (i : Fin (Tag.rank .F4)) :
    (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)).Group :=
  (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)).toCoxeterSystem.simple i

noncomputable abbrev wTheta :
    (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)).Group :=
  sF4 i0 * sF4 i1 * sF4 i2 * sF4 i1 * sF4 i3 * sF4 i2 * sF4 i1

noncomputable abbrev wThetaS :
    (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)).Group :=
  sF4 i3 * sF4 i2 * sF4 i1 * sF4 i2 * sF4 i0 * sF4 i1 * sF4 i2

theorem height_theta : height theta = 11 := by decide +kernel

theorem height_thetaS : height thetaS = 8 := by decide +kernel

theorem height_nsmul_add (a b : ℕ) (v w : Fin (Tag.rank .F4) → ℤ) :
    height (a • v + b • w) = a * height v + b * height w := by
  simp [height, Finset.sum_add_distrib, Finset.mul_sum]

theorem height_neg (v : Fin (Tag.rank .F4) → ℤ) : height (-v) = -height v := by
  simp [height]

section Weyl

theorem weylAction_sF4 (i : Fin (Tag.rank .F4)) (γ : Fin (Tag.rank .F4) → ℤ) :
    weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) (sF4 i) γ = reflect .F4 i γ :=
  weylAction_simple_eq_reflect _ i γ

theorem exists_single_eq (j : Fin (Tag.rank .F4)) :
    ∃ v, ∃ c ∈ ({theta, thetaS} : Set (Fin (Tag.rank .F4) → ℤ)),
      Pi.single j 1 = weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) v c := by
  have hθ : weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) wTheta (Pi.single i0 1) =
      theta := by
    simp only [wTheta, weylAction_mul_apply, weylAction_sF4]
    exact theta_eq_reflect
  have hθs : weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) wThetaS
      (Pi.single i3 1) = thetaS := by
    simp only [wThetaS, weylAction_mul_apply, weylAction_sF4]
    exact thetaS_eq_reflect
  have h01 : weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) (sF4 i0 * sF4 i1)
      (Pi.single i0 1) = Pi.single i1 1 := by
    simp only [weylAction_mul_apply, weylAction_sF4]
    decide +kernel
  have h32 : weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) (sF4 i3 * sF4 i2)
      (Pi.single i3 1) = Pi.single i2 1 := by
    simp only [weylAction_mul_apply, weylAction_sF4]
    decide +kernel
  match j with
  | ⟨0, _⟩ => exact ⟨wTheta⁻¹, theta, Or.inl rfl, by rw [← hθ, weylAction_inv_apply_apply]⟩
  | ⟨1, _⟩ =>
    exact ⟨sF4 i0 * sF4 i1 * wTheta⁻¹, theta, Or.inl rfl, by
      rw [weylAction_mul_apply, ← hθ, weylAction_inv_apply_apply, h01]⟩
  | ⟨2, _⟩ =>
    exact ⟨sF4 i3 * sF4 i2 * wThetaS⁻¹, thetaS, Or.inr rfl, by
      rw [weylAction_mul_apply, ← hθs, weylAction_inv_apply_apply, h32]⟩
  | ⟨3, _⟩ => exact ⟨wThetaS⁻¹, thetaS, Or.inr rfl, by rw [← hθs, weylAction_inv_apply_apply]⟩

end Weyl

section Group

variable {k : Type} [Field k]

theorem posUnipotent_le_centralizer_thetaS [CharP k 2] :
    posUnipotent (f4Datum k) ≤
      Subgroup.centralizer ((f4Datum k).rootGroup thetaS : Set (adjointGroup .F4 k)) := by
  refine iSup₂_le fun δ hδ => ?_
  obtain ⟨hδr, hδpos⟩ := hδ
  have hδ' : IsRoot .F4 δ := mem_adjDatum_roots.1 hδr
  have hδh : 0 < height (τ := .F4) δ := hδpos
  have hθh := height_thetaS
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := (mem_rootGroup_iff isRoot_thetaS x).1 hx
  obtain ⟨b, rfl⟩ := (mem_rootGroup_iff hδ' y).1 hy
  by_cases hEq : thetaS = δ
  · subst hEq
    rw [← xPar_add, ← xPar_add, add_comm]
  have hne' : thetaS ≠ -δ := fun h => by
    have := congrArg height h
    rw [height_neg] at this
    omega
  rw [← commutatorElement_eq_one_iff_mul_comm,
    commutator_xPar f4Data_valid noG2_F4 isRoot_thetaS hδ' hEq hne' a b]
  have h21 : ¬IsRoot .F4 (2 • thetaS + δ) := fun h => by
    have h1 := height_le_of_isRoot h
    have h2 := height_nsmul_add 2 1 thetaS δ
    rw [one_smul] at h2
    rw [h2] at h1
    push_cast at h1
    omega
  have h12 : ¬IsRoot .F4 (thetaS + 2 • δ) := fun h => by
    have h2 := height_nsmul_add 1 2 thetaS δ
    rw [one_smul] at h2
    have h9 : 9 ≤ height (thetaS + 2 • δ) := by
      rw [h2]
      push_cast
      omega
    have hc : thetaS i2 = 3 := rfl
    rcases eq_of_nine_le_height h h9 with e | e | e
    · have := congrFun e i2
      rw [Pi.add_apply, Pi.smul_apply, hc, nsmul_eq_mul] at this
      have h4 : rootNine i2 = 4 := rfl
      rw [h4] at this
      omega
    · have := congrFun e i2
      rw [Pi.add_apply, Pi.smul_apply, hc, nsmul_eq_mul] at this
      have h4 : rootTen i2 = 4 := rfl
      rw [h4] at this
      omega
    · have := congrFun e i2
      rw [Pi.add_apply, Pi.smul_apply, hc, nsmul_eq_mul] at this
      have h4 : theta i2 = 4 := rfl
      rw [h4] at this
      omega
  rw [xPar_of_not_isRoot h12, xPar_of_not_isRoot h21, mul_one, mul_one]
  by_cases h11 : IsRoot .F4 (thetaS + δ)
  · have h9 : 9 ≤ height (thetaS + δ) := by
      have h2 := height_nsmul_add 1 1 thetaS δ
      rw [one_smul, one_smul] at h2
      rw [h2]
      push_cast
      omega
    have hsub : IsRoot .F4 (δ - thetaS) := by
      have := isRoot_sub_two_smul_thetaS (eq_of_nine_le_height h11 h9)
      convert this using 1
      rw [two_nsmul]
      abel
    have hN : (RootOperatorFamily'.coeff11 (CFSG.LieType.Chevalley.rootOperatorFamily .F4)
        f4Data_valid ⟨thetaS, isRoot_thetaS⟩ ⟨δ, hδ'⟩).natAbs = 2 := by
      rw [RootOperatorFamily'.coeff11,
        RootOperatorFamily'.bracketCoeff_natAbs _ _
          (fun h => hne' (by
            have h' : δ = -thetaS := h
            rw [h', neg_neg])) h11]
      exact stringNorm_of_isRoot hsub
    have hc : ((RootOperatorFamily'.coeff11 (CFSG.LieType.Chevalley.rootOperatorFamily .F4)
        f4Data_valid ⟨thetaS, isRoot_thetaS⟩ ⟨δ, hδ'⟩ : ℤ) : k) = 0 := by
      rcases Int.natAbs_eq_iff.1 hN with h | h <;> rw [h] <;> simp [CharTwo.two_eq_zero]
    rw [hc, zero_mul, zero_mul, xPar_zero]
  · exact xPar_of_not_isRoot h11 _

theorem exists_weylAction_theta_or_thetaS {γ : Fin (f4Datum k).rank → ℤ}
    (hγ : γ ∈ (f4Datum k).roots) :
    ∃ w, ∃ c ∈ ({theta, thetaS} : Set (Fin (f4Datum k).rank → ℤ)),
      γ = weylAction (f4Datum k).isFiniteType w c := by
  rcases hγ with ⟨w, j, rfl⟩ | ⟨_, _, hj, -⟩
  · obtain ⟨v, c, hc, hv⟩ := exists_single_eq j
    exact ⟨w * v, c, hc, by rw [weylAction_mul_apply, ← hv]⟩
  · exact hj.elim

theorem ggRootSylowCentral_f4 [Finite k] [CharP k 2] (t : StatedLieTag) :
    GGRootSylowCentral (f4Datum k) t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθ : theta ∈ (f4Datum k).roots := mem_adjDatum_roots.2 isRoot_theta
  have hθs : thetaS ∈ (f4Datum k).roots := mem_adjDatum_roots.2 isRoot_thetaS
  have hmax : ∀ δ ∈ (f4Datum k).roots, ht δ ≤ ht theta := fun δ hδ => by
    have h1 := height_le_of_isRoot (mem_adjDatum_roots.1 hδ)
    have h2 := height_theta
    show height (τ := .F4) δ ≤ height theta
    omega
  refine ggRootSylowCentral_of_orbit (f4_isCTGroupDatum k) (f4_steinbergExtras k)
    (f4_bruhatExtras k)
    (fun γ hγ => isPGroup_of_isParametrization (f4_isParametrization k) hγ)
    (coprime_two_card_iSup_range_units (fun i => torusHom (τ := .F4) k i)
      fun i j h hh h' hh' => (f4_steinbergExtras k).torus_commute i j h hh h' hh')
    (C := {theta, thetaS}) ?_ fun γ hγ => exists_weylAction_theta_or_thetaS hγ.1
  rintro c (rfl | rfl)
  · exact ⟨hθ, ht_pos_of_maxHeight hθ hmax,
      posUnipotent_le_centralizer_of_maxHeight (f4_steinbergExtras k) hθ hmax
        (mul_comm_of_isParametrization (f4_isParametrization k) hθ)
        fun _ hδ e => absurd e (not_eq_two_smul_of_divisible_eq_empty rfl hδ hθ)⟩
  · refine ⟨hθs, ?_, posUnipotent_le_centralizer_thetaS⟩
    have := height_thetaS
    show 0 < height thetaS
    omega

end Group

end GGRootF4

end CFSG.StandardType
