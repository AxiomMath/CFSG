module

public import CFSG.Quasithin.H13.KGFactF618Gen
public import CFSG.Quasithin.H13.KGFactL2
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases7

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

namespace KGF618

theorem conclusion_of_mulEquiv {D Q : Type*} [Group D] [Group Q] [Finite D] (e : D ≃* Q)
    {N : Subgroup Q} (hsq : ∀ x : Q, x * x ∈ N) (h : Good ↥N) :
    CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup D)) ∧
      ∀ b : ℕ, Nat.card ↥(oTwoUpper (⊤ : Subgroup D)) ≠ 60 * 2 ^ b := by
  refine conclusion_of_good (N := N.map e.symm.toMonoidHom) (fun y => ?_)
    (good_of_mulEquiv (N.equivMapOfInjective _ e.symm.injective) h)
  refine ⟨e y * e y, hsq (e y), ?_⟩
  simp

theorem exists_good_pgl2 {K : Type} [Field K] [Finite K] {q : ℕ} (hq : q.Prime)
    (hq24 : q % 24 = 11 ∨ q % 24 = 13) (hK : Nat.card K = q) :
    ∃ N : Subgroup (GL (Fin 2) K ⧸ StatedScalars (Fin 2) K), (∀ x, x * x ∈ N) ∧ Good ↥N := by
  refine ⟨(StatedSL 2 K).map (QuotientGroup.mk' (StatedScalars (Fin 2) K)), ?_, ?_⟩
  · intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (StatedScalars (Fin 2) K) x
    set c : Kˣ := Matrix.GeneralLinearGroup.det g with hc
    have hz : Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈ StatedScalars (Fin 2) K := ⟨c, rfl⟩
    refine ⟨(Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * (g * g),
      Subgroup.subset_closure ?_, ?_⟩
    · have hdg : (g : Matrix (Fin 2) (Fin 2) K).det = (c : K) :=
        (Matrix.GeneralLinearGroup.val_det_apply g).symm
      show (((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * (g * g) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K).det = 1
      rw [← map_inv, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.det_mul, Matrix.det_mul, hdg]
      simp
      rw [← sq]
      exact inv_mul_cancel₀ (pow_ne_zero 2 c.ne_zero)
    · have h1 : QuotientGroup.mk' (StatedScalars (Fin 2) K)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 1 := (QuotientGroup.eq_one_iff _).2 hz
      rw [map_mul, map_inv, h1, inv_one, one_mul, map_mul]
  · set S := StatedSL 2 K
    set Z := StatedScalars (Fin 2) K
    let f : ↥S →* GL (Fin 2) K ⧸ Z := (QuotientGroup.mk' Z).comp S.subtype
    have hker : f.ker = Z.subgroupOf S := by
      ext s
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact QuotientGroup.eq_one_iff _
    have hrange : f.range = S.map (QuotientGroup.mk' Z) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    let iso : StatedProj S ≃* ↥(S.map (QuotientGroup.mk' Z)) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))
    have hL2 : F6.IsL2 q 1 (StatedProj S) := by
      refine ⟨⟨hq, le_rfl, le_rfl, fun h => ?_, fun h => ?_⟩, K, inferInstance, inferInstance,
        by rw [hK, pow_one], ⟨MulEquiv.refl _⟩⟩
      · simp only [pow_one, Prod.mk.injEq, true_and] at h
        omega
      · simp only [pow_one, Prod.mk.injEq, true_and] at h
        omega
    obtain ⟨hqs, hcd, -⟩ := factL2Three_holds q (StatedProj S) hq hq24 hL2
    exact good_of_mulEquiv iso ⟨hqs, hcd⟩

theorem conclusion_caseFive {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}
    (h : F6.IsF618CaseFive G₁ G₂) :
    CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup D)) ∧
      ∀ b : ℕ, Nat.card ↥(oTwoUpper (⊤ : Subgroup D)) ≠ 60 * 2 ^ b := by
  obtain ⟨⟨q, hq, hq24, K, _, _, hK, ⟨e⟩⟩, -⟩ := h
  obtain ⟨N, hsq, hN⟩ := exists_good_pgl2 hq hq24 hK
  exact conclusion_of_mulEquiv e hsq hN

theorem good_isSLEps3 {X : Type} [Group X] [Finite X] {p : ℕ} (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    (hSL : F6.IsSLEps3 p X) : Good X := by
  obtain ⟨hqs, hdvd⟩ := CFSG.Quasithin.Insp9.isSLEps3_qs_dvd hSL
  have hp : p.Prime := hSL.1
  have hp2 : p ≠ 2 := by omega
  refine ⟨hqs, ne_sixty_mul_two_pow (d := p ^ 2) ((pow_dvd_pow p (by norm_num)).trans hdvd)
    (Nat.Coprime.pow_left 2 ((Nat.coprime_primes hp Nat.prime_two).2 hp2)) fun h15 => ?_⟩
  have h1 := Nat.le_of_dvd (by norm_num) h15
  have hp3 : p ≤ 3 := by nlinarith
  have hp3' : p = 3 := by omega
  subst hp3'
  norm_num at h15

theorem good_caseTen {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}
    (h : F6.IsF618CaseTen G₁ G₂) : Good D := by
  obtain ⟨⟨p, hp8, hSL⟩, -⟩ := h
  exact good_isSLEps3 hp8 hSL

end KGF618

end CFSG.Quasithin.H13.A5
