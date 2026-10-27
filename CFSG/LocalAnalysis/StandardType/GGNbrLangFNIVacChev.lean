module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIVacDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.FPFieldN
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09Field
import CFSG.LocalAnalysis.StandardType.MarkingChevalley
import CFSG.LieType.Steinberg.Adjoint.Perfect
import CFSG.LieType.Steinberg.G2.Perfect
import CFSG.LieType.Simplicity.Exceptional

public section

namespace CFSG.StandardType

open CFSG.Assembly


private theorem l02qf2_chev_field_pow {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type)
    [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    ∀ f ∈ LargeEvenChevFieldImage A K (LargeEvenChevH A K false), f ^ n = 1 := by
  intro f hf
  have hstab : ∀ σ : K ≃+* K, ∀ h ∈ LargeEvenChevH A K false,
      CFSG.LocalAnalysis.GLTheoremA.YS09Field.chevAct A K σ h ∈ LargeEvenChevH A K false :=
    fun σ h hh => CFSG.LocalAnalysis.GLTheoremA.YS09Field.chevH_stable A K false σ h hh
  have hdvd : orderOf f ∣ Nat.card (K ≃+* K) :=
    CFSG.LocalAnalysis.GLTheoremA.FP.chevField_orderOf_dvd A K (LargeEvenChevH A K false) hstab
      f hf
  rw [CFSG.LocalAnalysis.GLTheoremA.FP.natCard_ringEquiv_of_card hK] at hdvd
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

theorem kgfni_fieldExponent_chev : KGFNIFieldExponentOn KGFNIChevalleyLabel := by
  intro lab _ h
  obtain ⟨t, l, n⟩ := lab
  dsimp only [KGFNIChevalleyLabel] at h
  intro Q hQ
  rcases h with rfl | rfl | rfl | rfl | rfl
  · dsimp only [LargeEvenRawDatum, kgfniFieldDegree] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    refine ⟨K, hKf, hKfin, hKcard, hq, ?_⟩
    intro f hf
    simpa only [one_mul] using l02qf2_chev_field_pow LargeEvenCartanG2 K hKcard f hf
  · dsimp only [LargeEvenRawDatum, kgfniFieldDegree] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    refine ⟨K, hKf, hKfin, hKcard, hq, ?_⟩
    intro f hf
    simpa only [one_mul] using l02qf2_chev_field_pow LargeEvenCartanF4 K hKcard f hf
  · dsimp only [LargeEvenRawDatum, kgfniFieldDegree] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    refine ⟨K, hKf, hKfin, hKcard, hq, ?_⟩
    intro f hf
    simpa only [one_mul] using l02qf2_chev_field_pow (LargeEvenCartanE 6) K hKcard f hf
  · dsimp only [LargeEvenRawDatum, kgfniFieldDegree] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    refine ⟨K, hKf, hKfin, hKcard, hq, ?_⟩
    intro f hf
    simpa only [one_mul] using l02qf2_chev_field_pow (LargeEvenCartanE 7) K hKcard f hf
  · dsimp only [LargeEvenRawDatum, kgfniFieldDegree] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    refine ⟨K, hKf, hKfin, hKcard, hq, ?_⟩
    intro f hf
    simpa only [one_mul] using l02qf2_chev_field_pow (LargeEvenCartanE 8) K hKcard f hf

private theorem l02qf2c_nonabelian_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul, h']))⟩

private theorem l02qf2c_centerQuot_simple {τ : CFSG.Blueprint.Chevalley.Tag} (K : Type) [Field K]
    (hq : CFSG.IsQuasisimple ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K)) :
    IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false)) ∧
      ∃ a b : LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false), a * b ≠ b * a := by
  obtain ⟨eR⟩ := centerQuot_chevGroup_equiv K τ
  refine ⟨?_, l02qf2c_nonabelian_of_mulEquiv eR.symm hq.2.2⟩
  have := hq.2.1
  exact eR.isSimpleGroup

theorem kgfni_rawSimple_chev : KGFNIRawSimpleOn KGFNIChevalleyLabel := by
  intro lab hΛ h
  obtain ⟨t, l, n⟩ := lab
  dsimp only [KGFNIChevalleyLabel] at h
  intro Q hQ
  rcases h with rfl | rfl | rfl | rfl | rfl
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    have hn : 2 ≤ n := by
      dsimp only [LargeEvenInLambda2] at hΛ
      exact hΛ.2.2
    have hK3 : 3 ≤ Nat.card K := by
      rw [hKcard]
      have h4 : 4 ≤ 2 ^ n := by
        simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) hn : 2 ^ 2 ≤ 2 ^ n)
      omega
    exact ⟨K, hKf, hKfin, hKcard, hq,
      l02qf2c_centerQuot_simple (τ := .G2) K
        (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K hK3)⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    exact ⟨K, hKf, hKfin, hKcard, hq,
      l02qf2c_centerQuot_simple (τ := .F4) K
        (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 K)⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    exact ⟨K, hKf, hKfin, hKcard, hq,
      l02qf2c_centerQuot_simple (τ := .E6) K
        (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K)⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    exact ⟨K, hKf, hKfin, hKcard, hq,
      l02qf2c_centerQuot_simple (τ := .E7) K
        (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K)⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    exact ⟨K, hKf, hKfin, hKcard, hq,
      l02qf2c_centerQuot_simple (τ := .E8) K
        (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K)⟩

end CFSG.StandardType
