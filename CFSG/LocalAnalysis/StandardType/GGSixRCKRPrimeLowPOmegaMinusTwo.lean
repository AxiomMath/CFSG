module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeInnerDiagTransport
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAt
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoOmTwo
import CFSG.LieType.Universal.Spin.Roots.TypeB
import CFSG.LieType.Universal.Spin.Twisted.Datum
import CFSG.LieType.Universal.SpecialLinearRoots

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg
open CFSG.Open (StatedLieTag)

private theorem rckLow2_ht {K : Type} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {γ : Fin (minusDatum 2 hirr).rank → ℤ} {i : Fin (2 - 1)} {s : Bool}
    (h : toStdB (2 - 1) γ = Pi.single i (boolSign s)) : ht γ = boolSign s := by
  have h1 := ht_of_toStdB_eq_single (n := 2 - 1) h
  have hi : (i : ℕ) = 0 := by have := i.isLt; omega
  refine h1.trans ?_
  rw [hi]
  simp

private theorem rckLow2_longRoot_single {K : Type} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i0 : Fin (minusDatum 2 hirr).rank)
    (hβ : (Pi.single i0 1 : Fin (minusDatum 2 hirr).rank → ℤ) ∈ (minusDatum 2 hirr).roots) :
    GGLongRoot (minusDatum 2 hirr) (Pi.single i0 1) := by
  have hmax : ∀ δ ∈ (minusDatum 2 hirr).roots, ht δ ≤ 1 := by
    intro δ hδ
    rcases exists_toStdB_eq_of_mem_roots (n := 2) hδ with ⟨i, j, hij, -⟩ | ⟨i, s', hδs⟩
    · exact absurd (Fin.ext (by have := i.isLt; have := j.isLt; omega)) hij
    · rw [rckLow2_ht hirr hδs]
      cases s' <;> simp [boolSign]
  have hht : ht (Pi.single i0 1 : Fin (minusDatum 2 hirr).rank → ℤ) = 1 := by simp [ht]
  refine ⟨1, Pi.single i0 1, hβ, fun δ hδ => ?_, by simp⟩
  have h1 : ht δ ≤ 1 := hmax δ hδ
  rw [← hht] at h1
  exact h1

private theorem rckLow2_roots_sl2 {F : Type} [Field F] {γ : Fin 1 → ℤ}
    (hγ : γ ∈ (SpecialLinear.rootDatum 1 F).roots) :
    ∀ δ : Fin 1 → ℤ, δ ∈ (SpecialLinear.rootDatum 1 F).roots → δ = γ ∨ δ = -γ := by
  have hpair : ∀ i j : Fin 2, i ≠ j →
      (Pi.single i 1 - Pi.single j 1 : Fin 2 → ℤ) = Pi.single 0 1 - Pi.single 1 1 ∨
        (Pi.single i 1 - Pi.single j 1 : Fin 2 → ℤ) = -(Pi.single 0 1 - Pi.single 1 1) := by
    decide +kernel
  have hcases : ∀ δ : Fin 1 → ℤ, δ ∈ (SpecialLinear.rootDatum 1 F).roots →
      SpecialLinear.toStd 1 δ = Pi.single 0 1 - Pi.single 1 1 ∨
        SpecialLinear.toStd 1 δ = -(Pi.single 0 1 - Pi.single 1 1) := by
    intro δ hδ
    have hδ' : δ ∈ CFSG.LieType.RootSystem.roots (SpecialLinear.isFiniteType_A 1) ∅ := hδ
    rw [SpecialLinear.roots_eq] at hδ'
    obtain ⟨i, j, hij, hδe⟩ := hδ'
    rw [hδe]
    exact hpair i j hij
  intro δ hδ
  have hinj := SpecialLinear.toStd_injective 1
  rcases hcases δ hδ with h1 | h1 <;> rcases hcases γ hγ with h2 | h2
  · exact Or.inl (hinj (h1.trans h2.symm))
  · refine Or.inr (hinj ?_)
    rw [SpecialLinear.toStd_neg, h1, h2, neg_neg]
  · refine Or.inr (hinj ?_)
    rw [SpecialLinear.toStd_neg, h1, h2]
  · exact Or.inl (hinj (h1.trans h2.symm))

theorem rckInnerDiag_omegaMinus_two_to_PSL
    {X : Type} [Group X] {g : ℕ} {e : (ggU .POmegaMinus 2 g).K ≃* (ggU .PSL 2 (2 * g)).K}
    (he : IRGIsoCompat e) (φ : (ggU .POmegaMinus 2 g).K →* X) {b : X}
    (hbK : ∀ k ∈ φ.range, b⁻¹ * k * b ∈ φ.range)
    (hb : GGPsiInnerDiag (ggU .POmegaMinus 2 g).D φ b) :
    GGPsiInnerDiag (ggU .PSL 2 (2 * g)).D (φ.comp e.symm.toMonoidHom) b := by
  have hrank : 0 < (ggU .POmegaMinus 2 g).D.rank := by
    first
      | exact Nat.one_pos
      | (show 0 < 2 - 1; norm_num; done)
      | (simp only [ggU, lieUniversal, Spin.Twisted.minusDatum]; omega)
  let i0 : Fin (ggU .POmegaMinus 2 g).D.rank := ⟨0, hrank⟩
  have hβ' : (Pi.single i0 1 : Fin (ggU .POmegaMinus 2 g).D.rank → ℤ) ∈
      (ggU .POmegaMinus 2 g).D.roots :=
    CFSG.StandardType.single_mem_roots (D := (ggU .POmegaMinus 2 g).D) i0
  have hβ'n : -(Pi.single i0 1 : Fin (ggU .POmegaMinus 2 g).D.rank → ℤ) ∈
      (ggU .POmegaMinus 2 g).D.roots :=
    CFSG.StandardType.neg_single_mem_roots (D := (ggU .POmegaMinus 2 g).D) i0
  have hlong : GGLongRoot (ggU .POmegaMinus 2 g).D (Pi.single i0 1) :=
    rckLow2_longRoot_single (minusCoeffs_irr 2 g) i0 hβ'
  obtain ⟨γ, hgood, w, h1, h2⟩ := he _ hβ' hlong
  have hγ : γ ∈ (SpecialLinear.rootDatum 1 (GaloisField 2 (2 * g))).roots := hgood.1
  have hroots : ∀ δ ∈ (ggU .PSL 2 (2 * g)).D.roots, δ = γ ∨ δ = -γ :=
    rckLow2_roots_sl2 hγ
  exact ggPsiInnerDiag_comp_symm_of_opposite_pair (Δ' := (ggU .POmegaMinus 2 g).D)
    (Δ := (ggU .PSL 2 (2 * g)).D) e hβ' hβ'n hroots h1 h2 φ hbK hb

theorem rckClassicalModelIDAt_PSL_of_omegaMinus_two
    {X : Type} [Group X] {g : ℕ} (hg : 1 ≤ g) {K B : Subgroup X}
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) (φ : (ggU .POmegaMinus 2 g).K →* X)
    (hφr : φ.range = K) (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaMinus 2 g).K)
    (hdiag : ∀ b ∈ B, GGPsiInnerDiag (ggU .POmegaMinus 2 g).D φ b) :
    RCKClassicalModelIDAt .PSL K B := by
  obtain ⟨e, he⟩ := irgIsoCompat_omegaMinus_two hg
  refine ⟨2, 2 * g, φ.comp e.symm.toMonoidHom, by omega, ?_, ?_, ?_⟩
  · rw [← hφr]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨e y, ?_⟩
      show φ (e.symm (e y)) = φ y
      rw [MulEquiv.symm_apply_apply]
  · intro x hx
    have hx' : φ (e.symm x) = 1 := hx
    have hc : e.symm x ∈ Subgroup.center (ggU .POmegaMinus 2 g).K :=
      hφk (MonoidHom.mem_ker.mpr hx')
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    have h := congrArg e (hc (e.symm y))
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h
    exact h
  · intro b hb
    refine rckInnerDiag_omegaMinus_two_to_PSL he φ ?_ (hdiag b hb)
    intro k hk
    rw [hφr] at hk ⊢
    exact (Subgroup.mem_normalizer_iff''.mp (hBK hb) k).mp hk

end CFSG.StandardType.RCKRP
