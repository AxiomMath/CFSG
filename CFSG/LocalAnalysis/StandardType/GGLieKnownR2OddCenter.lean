module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.HighestRoot.ModelCenter
public import CFSG.ClassicalInvolution.Q3.ModelCenter
public import CFSG.LieType.Steinberg.TwistedD4.Quasisimple
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

namespace CFSG.StandardType.LieKnownR2.OddCenter

open CFSG.ComponentClassification.RankTwoOddLie CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg.Exceptional

private theorem centerPPrime_two_spin {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K]
    [CharP K 2] (Q : QuadraticForm K (σ → K))
    (hcen : Subgroup.center (spinGroup Q) ≤ (CFSG.Open.StatedScalars σ K).comap (spinMatrix Q))
    (hker : ∀ x : spinGroup Q, x ∈ (spinMatrix Q).ker ↔ x = 1 ∨ (x : CliffordAlgebra Q) = -1) :
    CenterPPrime (spinGroup Q) 2 := by
  intro z hz hz2
  have h1 : spinMatrix Q z = 1 := eq_one_of_mem_statedScalars (Subgroup.mem_comap.mp (hcen hz))
    (by rw [← map_pow, hz2, map_one])
  rcases (hker z).1 h1 with h | h
  · exact h
  · have h2 : (2 : CliffordAlgebra Q) = 0 := by
      rw [← map_ofNat (algebraMap K (CliffordAlgebra Q)) 2, CharTwo.two_eq_zero, map_zero]
    apply Subtype.ext
    have h3 : ((1 : spinGroup Q) : CliffordAlgebra Q) = 1 := rfl
    rw [h, h3, neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]

theorem odd_card_center_of_centerPPrime_two {K : Type} [Group K] [Finite K]
    (h : CenterPPrime K 2) : Odd (Nat.card (Subgroup.center K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center K) :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) 2 h2
  have hg2 : (g : K) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one, Subgroup.coe_one]
  have hg1 : g = 1 := Subtype.ext (h (g : K) g.2 hg2)
  rw [hg1, orderOf_one] at hg
  omega

private theorem finite_spinGroup_two {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K]
    [Finite K] (Q : QuadraticForm K (σ → K)) {x : spinGroup Q}
    (hker : ((spinMatrix Q).ker : Set (spinGroup Q)) = {1, x}) : Finite (spinGroup Q) := by
  rw [MonoidHom.finite_iff_finite_ker_range (spinMatrix Q)]
  refine ⟨?_, inferInstance⟩
  have hfin : ((spinMatrix Q).ker : Set (spinGroup Q)).Finite :=
    hker ▸ (Set.finite_singleton x).insert 1
  exact hfin.to_subtype

private theorem finite_adjointGroup_two
    (τ : CFSG.Blueprint.Chevalley.Tag) (K : Type*)
    [Field K] [Finite K] : Finite (CFSG.Blueprint.Chevalley.adjointGroup τ K) := by
  have : Finite (Module.End K (CFSG.Blueprint.Chevalley.RootModule τ K)) :=
    Module.finite_of_finite K
  infer_instance

private theorem finite_minGroup_two
    {τ : CFSG.Blueprint.Chevalley.Tag}
    {D : CFSG.LieType.Steinberg.Minuscule.MinData τ} (hV : D.Valid) (K : Type*) [Field K]
    [Finite K] : Finite ↥(hV.minGroup K) := by
  have : Finite (Module.End K (Fin D.d →₀ K)) := Module.finite_of_finite K
  infer_instance

theorem finite_ggU
    {t : CFSG.Open.StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .F4 ∨ t = .E6 ∨
      t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    {n f : ℕ} (hadm : CFSG.Open.StatedLieAdmissible t n 2 f) : Finite (ggU t n f).K := by
  have hf : 1 ≤ f := hadm.2.1
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    change Finite (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))
    infer_instance
  · have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
    have hK : ggU .PSU n f = ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * f)) 2 f) n, Unitary.rootDatum hF n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [hK]
    change Finite ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * f)) 2 f) n)
    infer_instance
  · change Finite ↥(CFSG.Open.StatedSp n (GaloisField 2 f))
    infer_instance
  · have hn : 3 ≤ n := by have := hadm.2.2; omega
    have hK : ggU .POmegaPlus n f = ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
        Spin.plusDatum n (GaloisField 2 f) hn⟩ := by
      simp only [ggU, lieUniversal, hn, ↓reduceDIte]
    rw [hK]
    haveI : NeZero n := ⟨by omega⟩
    exact finite_spinGroup_two _
      (coe_ker_spinMatrix_quadPlus (n := n) (K := GaloisField 2 f))
  · exact finite_spinGroup_two _
      (coe_ker_spinMatrix_quadMinus (minusCoeffs_irr 2 f))
  · change Finite (CFSG.Blueprint.Chevalley.adjointGroup .F4 (GaloisField 2 f))
    exact finite_adjointGroup_two _ _
  · change Finite (CFSG.LieType.Steinberg.Exceptional.e6UniversalGroup 2 f)
    exact finite_minGroup_two (D := CFSG.LieType.Steinberg.Minuscule.e6Data)
      CFSG.LieType.Steinberg.Minuscule.e6Data_valid _
  · change Finite (CFSG.LieType.Steinberg.Exceptional.e7UniversalGroup 2 f)
    exact finite_minGroup_two (D := CFSG.LieType.Steinberg.Minuscule.e7Data)
      CFSG.LieType.Steinberg.Minuscule.e7Data_valid _
  · change Finite (CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 2 f))
    exact finite_adjointGroup_two _ _
  · change Finite (CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 f)
    have hfin : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
        (GaloisField 2 (2 * f))) :=
      finite_minGroup_two (D := CFSG.LieType.Steinberg.Minuscule.e6Data)
        CFSG.LieType.Steinberg.Minuscule.e6Data_valid _
    infer_instance

private theorem centerPPrime_ggU
    {t : CFSG.Open.StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .F4 ∨ t = .E6 ∨
      t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    {n f : ℕ} (hadm : CFSG.Open.StatedLieAdmissible t n 2 f) : CenterPPrime (ggU t n f).K 2 := by
  have hf : 1 ≤ f := hadm.2.1
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    exact centerPPrime_specialLinear m (GaloisField 2 f)
  · have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
    have hK : ggU .PSU n f = ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * f)) 2 f) n, Unitary.rootDatum hF n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [hK]
    exact centerPPrime_unitary hF hadm.2.2.1 hadm.2.2.2
  · exact centerPPrime_statedSp n (GaloisField 2 f)
  · have hn : 3 ≤ n := by have := hadm.2.2; omega
    have hK : ggU .POmegaPlus n f = ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
        Spin.plusDatum n (GaloisField 2 f) hn⟩ := by
      simp only [ggU, lieUniversal, hn, ↓reduceDIte]
    rw [hK]
    refine centerPPrime_two_spin _ ?_ mem_ker_spinMatrix_quadPlus_iff
    rw [← (spinToStatedProj_quadPlus (K := GaloisField 2 f) hn).2.1,
      (spinToStatedProj_quadPlus (K := GaloisField 2 f) hn).2.2]
  · refine centerPPrime_two_spin _ ?_ (mem_ker_spinMatrix_quadMinus_iff (minusCoeffs_irr 2 f))
    rw [← (spinToStatedProj_quadMinus hadm.2.2 (minusCoeffs_irr 2 f)).2.1,
      (spinToStatedProj_quadMinus hadm.2.2 (minusCoeffs_irr 2 f)).2.2]
  · exact centerPPrime_adjoint .F4 (GaloisField 2 f)
  · exact centerPPrime_e6 (GaloisField 2 f)
  · exact centerPPrime_e7 (GaloisField 2 f)
  · exact centerPPrime_adjoint .E8 (GaloisField 2 f)
  · exact centerPPrime_fixedGroup (frobQ 2 f) (frobQ_frobQ 2 f hf)

theorem odd_card_center_ggU
    {t : CFSG.Open.StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .F4 ∨ t = .E6 ∨
      t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    {n f : ℕ} (hadm : CFSG.Open.StatedLieAdmissible t n 2 f) :
    Odd (Nat.card (Subgroup.center (ggU t n f).K)) := by
  haveI := finite_ggU ht hadm
  exact odd_card_center_of_centerPPrime_two (centerPPrime_ggU ht hadm)

end CFSG.StandardType.LieKnownR2.OddCenter
