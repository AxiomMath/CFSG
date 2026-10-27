module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Transvection
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAction
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.Arithmetic
import CFSG.Walter.PSL2Facts.FieldAut
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride.PSL2Three

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo

theorem exists_std_aut {p : ℕ} (hp : p.Prime) :
    ∃ σ : GaloisField 3 p ≃+* GaloisField 3 p,
      orderOf (psl2FieldAut (GaloisField 3 p) σ) = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hGal : Nat.card (GaloisField 3 p ≃+* GaloisField 3 p) = p :=
    natCard_ringEquiv_galoisField 3 hp.ne_zero
  have : Finite (GaloisField 3 p ≃+* GaloisField 3 p) :=
    Nat.finite_of_card_ne_zero (by rw [hGal]; exact hp.ne_zero)
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' p (by rw [hGal])
  refine ⟨σ, ?_⟩
  rw [orderOf_injective (psl2FieldAut (GaloisField 3 p))
    (psl2FieldAut_injective (GaloisField 3 p)) σ, hσ]

theorem exists_pglAction_of_coprime_orderOf {p : ℕ} (hp : p.Prime)
    (g : MulAut PSL(2, GaloisField 3 p)) (hg : Nat.Coprime p (orderOf g)) :
    ∃ y : PGL2 (GaloisField 3 p), g = pglAction (GaloisField 3 p) y := by
  classical
  set K := GaloisField 3 p
  let e := semilinearEquivAut K
  set y := e.symm g with hydef
  have hGal : Nat.card (K ≃+* K) = p := natCard_ringEquiv_galoisField 3 hp.ne_zero
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hGal]; exact hp.ne_zero)
  have hπ : (SemidirectProduct.rightHom y : K ≃+* K) = 1 := by
    have hdvd1 : orderOf (SemidirectProduct.rightHom y) ∣ orderOf g := by
      rw [← MulEquiv.orderOf_eq e.symm g]
      exact orderOf_map_dvd _ _
    have hdvd2 : orderOf (SemidirectProduct.rightHom y) ∣ p :=
      (orderOf_dvd_natCard _).trans (dvd_of_eq hGal)
    have h := Nat.dvd_gcd hdvd2 hdvd1
    rw [hg.gcd_eq_one] at h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)
  have hy : y = SemidirectProduct.inl y.left := SemidirectProduct.ext rfl (by simpa using hπ)
  refine ⟨y.left, ?_⟩
  calc g = e y := (e.apply_symm_apply g).symm
    _ = e (SemidirectProduct.inl y.left) := by rw [← hy]
    _ = pglAction K y.left := by
        change semilinearAction K _ = _
        rw [semilinearAction_inl]

section Transvections

variable {K : Type*} [Field K]

theorem map_transvecUp (σ : K ≃+* K) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (transvecUp K) = transvecUp K := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvecUp]

theorem map_transvecLow (σ : K ≃+* K) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (transvecLow K) = transvecLow K := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvecLow]

theorem psl2FieldAut_transvecUp (σ : K ≃+* K) :
    psl2FieldAut K σ (QuotientGroup.mk (transvecUp K)) = QuotientGroup.mk (transvecUp K) := by
  rw [CFSG.Walter.psl2FieldAut_eq_psl2Map, CFSG.Walter.psl2Map_mk, map_transvecUp]

theorem psl2FieldAut_transvecLow (σ : K ≃+* K) :
    psl2FieldAut K σ (QuotientGroup.mk (transvecLow K)) = QuotientGroup.mk (transvecLow K) := by
  rw [CFSG.Walter.psl2FieldAut_eq_psl2Map, CFSG.Walter.psl2Map_mk, map_transvecLow]

theorem eq_toPGL_of_pglAction {y : PGL2 K} {c : PSL2 K}
    (h1 : pglAction K y (QuotientGroup.mk (transvecUp K)) =
      c * QuotientGroup.mk (transvecUp K) * c⁻¹)
    (h2 : pglAction K y (QuotientGroup.mk (transvecLow K)) =
      c * QuotientGroup.mk (transvecLow K) * c⁻¹) :
    y = Matrix.ProjectiveSpecialLinearGroup.toPGL c := by
  have key : ∀ x : PSL2 K, pglAction K y x = c * x * c⁻¹ →
      (Matrix.ProjectiveSpecialLinearGroup.toPGL c)⁻¹ * y *
        Matrix.ProjectiveSpecialLinearGroup.toPGL x *
        ((Matrix.ProjectiveSpecialLinearGroup.toPGL c)⁻¹ * y)⁻¹ =
      Matrix.ProjectiveSpecialLinearGroup.toPGL x := by
    intro x hx
    have h := toPGL_pglAction K y x
    rw [hx, map_mul, map_mul, map_inv] at h
    calc (Matrix.ProjectiveSpecialLinearGroup.toPGL c)⁻¹ * y *
          Matrix.ProjectiveSpecialLinearGroup.toPGL x *
          ((Matrix.ProjectiveSpecialLinearGroup.toPGL c)⁻¹ * y)⁻¹
        = (Matrix.ProjectiveSpecialLinearGroup.toPGL c)⁻¹ *
            (y * Matrix.ProjectiveSpecialLinearGroup.toPGL x * y⁻¹) *
            Matrix.ProjectiveSpecialLinearGroup.toPGL c := by group
      _ = Matrix.ProjectiveSpecialLinearGroup.toPGL x := by rw [← h]; group
  have hz := eq_one_of_conj_transvecs (key _ h1) (key _ h2)
  exact (inv_mul_eq_one.mp hz).symm

theorem eq_one_of_pglAction_fixes {y : PGL2 K}
    (h1 : pglAction K y (QuotientGroup.mk (transvecUp K)) = QuotientGroup.mk (transvecUp K))
    (h2 : pglAction K y (QuotientGroup.mk (transvecLow K)) =
      QuotientGroup.mk (transvecLow K)) : y = 1 := by
  have := eq_toPGL_of_pglAction (c := 1) (by rw [h1]; simp) (by rw [h2]; simp)
  rwa [map_one] at this

end Transvections

theorem perfect_le_range_conj (K : Type*) [Field K] [Finite K]
    (P : Subgroup (MulAut PSL(2, K))) (hP : Group.IsPerfect P) :
    P ≤ (MulAut.conj : PSL(2, K) →* MulAut PSL(2, K)).range := by
  intro g hg
  have : Group.IsPerfect P := hP
  have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      PSL(2, K)) := outer_solvable K
  obtain ⟨x, hx⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
    (A := P) (G := PSL(2, K)) P.subtype ⟨g, hg⟩
  exact ⟨x, hx.symm⟩

end CFSG.SignalizerFunctorTheorem.McBride.PSL2Three
