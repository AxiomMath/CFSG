module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import Mathlib.RingTheory.Trace.Defs
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.StandardType.OrthAnchor

open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

theorem exists_hypPair_of_normFrame {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {A : Subgroup ↥(orthDerived Q)}
    (hsc : ∀ g ∈ Subgroup.centralizer (A : Set ↥(orthDerived Q)), g ^ 3 = 1 → g ∈ A)
    {k : ℕ} {M : Type} [Field M] [Algebra F M] {τ : M ≃+* M}
    {U : Type} [AddCommGroup U] [Module F U] (Φ : ((Fin k → M) × U) ≃ₗ[F] V)
    (hU : Module.finrank F U = 2)
    (hpolar : ∀ d d' w w', QuadraticMap.polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, Algebra.trace F M (τ (d i) * d' i) +
        QuadraticMap.polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (hN : ∀ d w, algebraMap F M (Q (Φ (d, w))) =
      ∑ i, τ (d i) * d i + algebraMap F M (Q (Φ (0, w))))
    (hdiag : ∀ e ∈ A, ∃ a : Fin k → M,
      ∀ d w, (e : V ≃ₗ[F] V) (Φ (d, w)) = Φ (fun i => a i * d i, w)) :
    ∃ e f : U, Q (Φ (0, e)) = 0 ∧ Q (Φ (0, f)) = 0 ∧
      QuadraticMap.polarBilin Q (Φ (0, e)) (Φ (0, f)) = 1 :=
  by
    classical
    have hval : ∀ x : F, x = 0 ∨ x = 1 := by
      obtain ⟨y, _hy0, huniq⟩ := (Nat.card_eq_two_iff' (0 : F)).mp hF
      have hy1 : y = 1 := (huniq 1 one_ne_zero).symm
      intro x
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr ((huniq x hx).trans hy1)
    have htwo : (2 : F) = 0 := by
      have h11 : (1 : F) + 1 = 0 := by
        rcases hval ((1 : F) + 1) with h | h
        · exact h
        · exfalso
          have h1 : (1 : F) = 0 := by
            have h' : (1 : F) + 1 = 1 + 0 := by rw [h, add_zero]
            exact add_left_cancel h'
          exact one_ne_zero h1
      rw [← one_add_one_eq_two, h11]
    have hselfF : ∀ x : F, x + x = 0 := fun x => by
      rw [← two_mul, htwo, zero_mul]
    let QU : U → F := fun w => Q (Φ (0, w))
    let BU : U → U → F := fun w w' =>
      QuadraticMap.polarBilin Q (Φ (0, w)) (Φ (0, w'))
    have hBU_sep : ∀ w, (∀ w', BU w w' = 0) → w = 0 := by
      intro w hw
      have hz : Φ (0, w) = 0 := by
        refine eq_zero_of_polar_eq_zero hQ fun x => ?_
        obtain ⟨⟨d', w'⟩, rfl⟩ := Φ.surjective x
        have hww' : QuadraticMap.polarBilin Q (Φ (0, w)) (Φ (0, w')) = 0 := by
          simpa [BU] using hw w'
        rw [← QuadraticMap.polarBilin_apply_apply, hpolar 0 d' w w', hww']
        simp
      have hpair : ((0 : Fin k → M), w) = (0, 0) := Φ.injective (by simpa using hz)
      exact congrArg Prod.snd hpair
    have hex : ∃ e : U, e ≠ 0 ∧ QU e = 0 := by
      by_contra hno
      have hQU1 : ∀ w, w ≠ 0 → QU w = 1 := by
        intro w hw
        rcases hval (QU w) with h0 | h1
        · exact absurd ⟨w, hw, h0⟩ hno
        · exact h1
      have hfin : Module.Finite F U :=
        Module.finite_of_finrank_eq_succ (n := 1) (by simpa using hU)
      let b : Module.Basis (Fin 2) F U :=
        @Module.finBasisOfFinrankEq F U _ _ _ _ _ hfin 2 hU
      have hselfU : ∀ x : U, x + x = 0 := fun x => by
        rw [← two_smul F x, htwo, zero_smul]
      let rLin : U →ₗ[F] U := b.constr F ![b 1, b 0 + b 1]
      let rInv : U →ₗ[F] U := b.constr F ![b 0 + b 1, b 0]
      have hr0 : rLin (b 0) = b 1 := by
        simp [rLin]
      have hr1 : rLin (b 1) = b 0 + b 1 := by
        simp [rLin]
      have hri0 : rInv (b 0) = b 0 + b 1 := by
        simp [rInv]
      have hri1 : rInv (b 1) = b 0 := by
        simp [rInv]
      have hcomp1 : rLin.comp rInv = LinearMap.id := by
        apply b.ext
        intro i
        fin_cases i
        · change rLin (rInv (b 0)) = b 0
          rw [hri0, map_add, hr0, hr1, add_comm (b 1) (b 0 + b 1), add_assoc,
            hselfU (b 1), add_zero]
        · change rLin (rInv (b 1)) = b 1
          rw [hri1, hr0]
      have hcomp2 : rInv.comp rLin = LinearMap.id := by
        apply b.ext
        intro i
        fin_cases i
        · change rInv (rLin (b 0)) = b 0
          rw [hr0, hri1]
        · change rInv (rLin (b 1)) = b 1
          rw [hr1, map_add, hri0, hri1, add_comm (b 0 + b 1) (b 0), ← add_assoc,
            hselfU (b 0), zero_add]
      let r : U ≃ₗ[F] U := LinearEquiv.ofLinear rLin rInv hcomp1 hcomp2
      have hr_apply : ∀ x, r x = rLin x := fun _ => rfl
      have hr0' : r (b 0) = b 1 := by rw [hr_apply, hr0]
      have hr1' : r (b 1) = b 0 + b 1 := by rw [hr_apply, hr1]
      have hr3 : r ^ 3 = 1 := by
        refine LinearEquiv.toLinearMap_inj.mp ?_
        apply b.ext
        intro i
        fin_cases i
        · rw [pow_three']
          change r (r (r (b 0))) = b 0
          rw [hr0', hr1', map_add, hr0', hr1', add_comm (b 1) (b 0 + b 1), add_assoc,
            hselfU (b 1), add_zero]
        · rw [pow_three']
          change r (r (r (b 1))) = b 1
          rw [hr1', map_add, hr0', hr1', map_add, hr1', map_add, hr0', hr1',
            add_comm (b 1) (b 0 + b 1), ← add_assoc, hselfU (b 0 + b 1), zero_add]
      let sLin : U →ₗ[F] U := b.constr F ![b 1, b 0]
      have hs0 : sLin (b 0) = b 1 := by
        simp [sLin]
      have hs1 : sLin (b 1) = b 0 := by
        simp [sLin]
      have hss : sLin.comp sLin = LinearMap.id := by
        apply b.ext
        intro i
        fin_cases i
        · change sLin (sLin (b 0)) = b 0
          rw [hs0, hs1]
        · change sLin (sLin (b 1)) = b 1
          rw [hs1, hs0]
      let s : U ≃ₗ[F] U := LinearEquiv.ofLinear sLin sLin hss hss
      have hs_apply : ∀ x, s x = sLin x := fun _ => rfl
      have hs0' : s (b 0) = b 1 := by rw [hs_apply, hs0]
      have hs1' : s (b 1) = b 0 := by rw [hs_apply, hs1]
      have hss2 : s * s = 1 := by
        refine LinearEquiv.toLinearMap_inj.mp ?_
        apply b.ext
        intro i
        fin_cases i
        · change (s * s : U ≃ₗ[F] U) (b 0) = b 0
          rw [LinearEquiv.mul_apply]
          change s (s (b 0)) = b 0
          rw [hs0', hs1']
        · change (s * s : U ≃ₗ[F] U) (b 1) = b 1
          rw [LinearEquiv.mul_apply]
          change s (s (b 1)) = b 1
          rw [hs1', hs0']
      have hss_apply : ∀ w, s (s w) = w := by
        intro w
        have := LinearEquiv.congr_fun hss2 w
        simpa [LinearEquiv.mul_apply] using this
      have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss2
      have hrinv_apply : ∀ x, r⁻¹ x = rInv x := by
        intro x
        change (LinearEquiv.ofLinear rLin rInv hcomp1 hcomp2).symm x = rInv x
        rw [LinearEquiv.ofLinear_symm_apply]
      have hrinv0 : r⁻¹ (b 0) = b 0 + b 1 := by rw [hrinv_apply, hri0]
      have hrinv1 : r⁻¹ (b 1) = b 0 := by rw [hrinv_apply, hri1]
      have hsrs : s * r * s⁻¹ = r⁻¹ := by
        refine LinearEquiv.toLinearMap_inj.mp ?_
        apply b.ext
        intro i
        fin_cases i
        · change (s * r * s⁻¹ : U ≃ₗ[F] U) (b 0) = r⁻¹ (b 0)
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsinv]
          change s (r (s (b 0))) = r⁻¹ (b 0)
          rw [hs0', hr1', map_add, hs0', hs1', hrinv0, add_comm]
        · change (s * r * s⁻¹ : U ≃ₗ[F] U) (b 1) = r⁻¹ (b 1)
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsinv]
          change s (r (s (b 1))) = r⁻¹ (b 1)
          rw [hs1', hr0', hs1', hrinv1]
      have hsrs_apply : ∀ w, s (r (s w)) = r⁻¹ w := by
        intro w
        have := LinearEquiv.congr_fun hsrs w
        simpa [LinearEquiv.mul_apply, hsinv] using this
      let R : V ≃ₗ[F] V :=
        (Φ.symm.trans ((LinearEquiv.refl F (Fin k → M)).prodCongr r)).trans Φ
      let S : V ≃ₗ[F] V :=
        (Φ.symm.trans ((LinearEquiv.refl F (Fin k → M)).prodCongr s)).trans Φ
      have hR_apply : ∀ d w, R (Φ (d, w)) = Φ (d, r w) := by
        intro d w
        dsimp only [R]
        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
          LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
      have hS_apply : ∀ d w, S (Φ (d, w)) = Φ (d, s w) := by
        intro d w
        dsimp only [S]
        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
          LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
      have hQU_r : ∀ w, QU (r w) = QU w := by
        intro w
        by_cases hw : w = 0
        · subst w
          simp [QU]
        · have hrw : r w ≠ 0 := by
            intro h
            exact hw (r.injective (by simpa using h))
          rw [hQU1 (r w) hrw, hQU1 w hw]
      have hQU_s : ∀ w, QU (s w) = QU w := by
        intro w
        by_cases hw : w = 0
        · subst w
          simp [QU]
        · have hsw : s w ≠ 0 := by
            intro h
            exact hw (s.injective (by simpa using h))
          rw [hQU1 (s w) hsw, hQU1 w hw]
      have hR_mem : R ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
        rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
        intro v
        obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
        rw [hR_apply]
        apply (algebraMap F M).injective
        rw [hN d (r w), hN d w]
        rw [show Q (Φ (0, r w)) = Q (Φ (0, w)) from hQU_r w]
      have hS_mem : S ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
        rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
        intro v
        obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
        rw [hS_apply]
        apply (algebraMap F M).injective
        rw [hN d (s w), hN d w]
        rw [show Q (Φ (0, s w)) = Q (Φ (0, w)) from hQU_s w]
      have hR3 : R ^ 3 = 1 := by
        rw [show (1 : V ≃ₗ[F] V) = LinearEquiv.refl F V from LinearEquiv.one_eq_refl]
        apply LinearEquiv.ext
        intro v
        obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
        rw [pow_three', LinearEquiv.mul_apply, LinearEquiv.mul_apply, hR_apply, hR_apply,
          hR_apply]
        have h3w : r (r (r w)) = w := by
          have := LinearEquiv.congr_fun hr3 w
          simpa [pow_three', LinearEquiv.mul_apply] using this
        rw [h3w, LinearEquiv.refl_apply]
      have hS2 : S * S = 1 := by
        rw [show (1 : V ≃ₗ[F] V) = LinearEquiv.refl F V from LinearEquiv.one_eq_refl]
        apply LinearEquiv.ext
        intro v
        obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
        rw [LinearEquiv.mul_apply, hS_apply, hS_apply, hss_apply, LinearEquiv.refl_apply]
      have hSinv : S⁻¹ = S := inv_eq_of_mul_eq_one_left hS2
      have hS_inv_apply : ∀ d w, S⁻¹ (Φ (d, w)) = Φ (d, s w) := by
        intro d w
        rw [hSinv]
        exact hS_apply d w
      have hRinv_apply : ∀ d w, R⁻¹ (Φ (d, w)) = Φ (d, r⁻¹ w) := by
        intro d w
        apply R.injective
        rw [show R (R⁻¹ (Φ (d, w))) = Φ (d, w) by
          rw [show R⁻¹ = R.symm from rfl, LinearEquiv.apply_symm_apply], hR_apply]
        simp
      have hSR : S * R * S⁻¹ = R⁻¹ := by
        apply LinearEquiv.ext
        intro v
        obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hS_inv_apply, hR_apply, hS_apply,
          hRinv_apply]
        rw [hsrs_apply w]
      have hR3' : R * R * R = 1 := by
        rw [← pow_three']
        exact hR3
      have hR2 : R * R = R⁻¹ :=
        eq_inv_of_mul_eq_one_right (a := R) (b := R * R) (by
          rw [← mul_assoc]
          exact hR3')
      have hR4 : R⁻¹ * R⁻¹ = R := by
        rw [← mul_inv_rev, hR2, inv_inv]
      have hRder : R ∈ orthDerived Q := by
        have hcomm : ⁅S, R⁆ = R := by
          rw [commutatorElement_def, hSR, hR4]
        rw [← hcomm]
        exact Subgroup.commutator_mem_commutator hS_mem hR_mem
      let R' : ↥(orthDerived Q) := ⟨R, hRder⟩
      have hR'3 : R' ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow]
        change R ^ 3 = 1
        exact hR3
      have hR'_cent : R' ∈ Subgroup.centralizer (A : Set ↥(orthDerived Q)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        obtain ⟨a, ha⟩ := hdiag e he
        apply Subtype.ext
        change (e : V ≃ₗ[F] V) * R = R * (e : V ≃ₗ[F] V)
        apply LinearEquiv.ext
        intro v
        obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hR_apply, ha d (r w), ha d w,
          hR_apply]
      have hR'A : R' ∈ A := hsc R' hR'_cent hR'3
      obtain ⟨a, ha⟩ := hdiag R' hR'A
      have hfix : R (Φ (0, b 0)) = Φ (0, b 0) := by
        have h0 := ha (0 : Fin k → M) (b 0)
        change R (Φ (0, b 0)) = Φ ((fun i => a i * (0 : Fin k → M) i), b 0) at h0
        have hz : (fun i : Fin k => a i * (0 : Fin k → M) i) = 0 := by
          funext i
          simp
        rw [hz] at h0
        simpa using h0
      have hmove : R (Φ (0, b 0)) = Φ (0, b 1) := by
        rw [hR_apply, hr0']
      have heq : Φ (0, b 1) = Φ (0, b 0) := by rw [← hmove, hfix]
      have hpair : ((0 : Fin k → M), b 1) = (0, b 0) := Φ.injective heq
      have hb : b 1 = b 0 := congrArg Prod.snd hpair
      have h01 : b 0 ≠ b 1 := by
        intro h
        have hrepr : (b.repr (b 0)) 1 = (b.repr (b 1)) 1 := by rw [h]
        have h0 : (b.repr (b 0)) 1 = 0 := by
          rw [Module.Basis.repr_self]
          simp
        have h1 : (b.repr (b 1)) 1 = 1 := by
          rw [Module.Basis.repr_self]
          simp
        rw [h0, h1] at hrepr
        exact zero_ne_one hrepr
      exact h01 hb.symm
    obtain ⟨e, he0, hQe⟩ := hex
    have hQe' : Q (Φ (0, e)) = 0 := hQe
    have hBU_exists : ∃ w, BU e w ≠ 0 := by
      by_contra h
      apply he0
      apply hBU_sep e
      intro w
      by_contra hw
      exact h ⟨w, hw⟩
    obtain ⟨w, hw⟩ := hBU_exists
    have hw1 : BU e w = 1 := by
      rcases hval (BU e w) with h0 | h1
      · exact absurd h0 hw
      · exact h1
    let q : F := QU w
    let f : U := w + q • e
    have hsplit : Φ (0, f) = Φ (0, w) + q • Φ (0, e) := by
      have hpair : ((0 : Fin k → M), f) =
          ((0 : Fin k → M), w) + q • ((0 : Fin k → M), e) := by
        simp [f]
      rw [hpair, map_add, map_smul]
    have hwe : QuadraticMap.polar Q (Φ (0, w)) (Φ (0, e)) = 1 := by
      rw [QuadraticMap.polar_comm Q (Φ (0, w)) (Φ (0, e))]
      simpa [BU, QuadraticMap.polarBilin_apply_apply] using hw1
    have hQU_f : Q (Φ (0, f)) = 0 := by
      rw [hsplit, QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq]
      rw [hQe', mul_zero, add_zero, hwe, mul_one]
      change QU w + q = 0
      exact hselfF q
    have hBU_ef : BU e f = 1 := by
      dsimp only [BU]
      rw [QuadraticMap.polarBilin_apply_apply]
      rw [hsplit, QuadraticMap.polar_add_right, polar_smul_right_eq]
      rw [polar_self_eq_two_mul, hQe', mul_zero, mul_zero, add_zero]
      simpa [BU, QuadraticMap.polarBilin_apply_apply] using hw1
    refine ⟨e, f, ?_, hQU_f, ?_⟩
    · exact hQe'
    · simpa [BU] using hBU_ef


end CFSG.StandardType.OrthAnchor

end
