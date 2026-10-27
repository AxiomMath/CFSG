module

public import CFSG.Quasithin.Background.HStandard
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4aIA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H Subgroup

theorem s16h_H5_omegaMinusFour_two_inf_ne_bot {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {D : Subgroup (MulAut (StdMod (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K))}
    (hDN : D ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)))
    (hDab : IsElemAbelian 3 D) (hDcard : Nat.card ↥D = 3 ^ 2)
    (hCD : natImage (StatedScalars (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) ≤ D)
    (hC3 : Nat.card (natImage (StatedScalars (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)) = 3)
    (hcent : Subgroup.centralizer (natImage (StatedOmega (StatedQuadMinus 2 K b c)) :
        Set (MulAut (StdMod (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K))) ≤
      natImage (StatedScalars (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)) :
    ∃ y ∈ D ⊓ natImage (StatedOmega (StatedQuadMinus 2 K b c)), y ≠ 1 := by
  classical
  let Γ : Subgroup (GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :=
    StatedOmega (StatedQuadMinus 2 K b c)
  let Ω : Subgroup (MulAut (StdMod (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)) := natImage Γ
  let C : Subgroup (MulAut (StdMod (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)) :=
    natImage (StatedScalars (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)
  have hCD' : C ≤ D := hCD
  have hC3' : Nat.card ↥C = 3 := hC3
  have hcent' : Subgroup.centralizer
      (Ω : Set (MulAut (StdMod (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K))) ≤ C := hcent
  have hDneC : D ≠ C := by
    intro h
    have hcard : Nat.card ↥D = Nat.card ↥C := by rw [h]
    rw [hDcard, hC3'] at hcard
    norm_num at hcard
  have hnotle : ¬ D ≤ C := fun hle => hDneC (le_antisymm hle hCD')
  obtain ⟨d, hdD, hdC⟩ := Set.not_subset.mp hnotle
  have hdN : d ∈ Subgroup.normalizer
      (Ω : Set (MulAut (StdMod (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K))) := hDN hdD
  have hd3 : d ^ 3 = 1 := hDab.2 d hdD
  let dN : Subgroup.normalizer
      (Ω : Set (MulAut (StdMod (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K))) := ⟨d, hdN⟩
  let α : MulAut ↥Ω := Subgroup.normalizerMonoidHom Ω dN
  have hdN3 : dN ^ 3 = 1 := by
    apply Subtype.ext
    simpa [dN] using hd3
  have hα3 : α ^ 3 = 1 := by
    change (Subgroup.normalizerMonoidHom Ω dN) ^ 3 = 1
    rw [← map_pow, hdN3, map_one]
  have hInj : Function.Injective (natAut Γ) :=
    matHom_injective.comp (Subgroup.subtype_injective Γ)
  let eImg : ↥Γ ≃* ↥Ω := MonoidHom.ofInjective hInj
  have hL2 : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 ↥Ω (2 * 2) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22d_isL2_of_omegaMinus4
      (k := 2) (by norm_num) hK b c hirr eImg.symm
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥Ω) ∣ 4 :=
    s16h_H5_l2_four_outer_card_dvd_four hL2
  have hαinner : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥Ω :=
    s16h_H5_isInner_of_pow_three hOut hα3
  obtain ⟨y₀, hy₀⟩ := hαinner
  let y : MulAut (StdMod (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) := y₀
  have hyΩ : y ∈ Ω := y₀.2
  have hconj : ∀ x ∈ Ω, y * x * y⁻¹ = d * x * d⁻¹ := by
    intro x hx
    have h1 : (MulAut.conj y₀) ⟨x, hx⟩ = α ⟨x, hx⟩ := by rw [hy₀]
    have h2 := congrArg (Subtype.val) h1
    simpa [y, α, MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] using h2
  have hc : ∀ z ∈ Ω, (y⁻¹ * d) * z * (y⁻¹ * d)⁻¹ = z := by
    intro z hz
    have h : y * z * y⁻¹ = d * z * d⁻¹ := hconj z hz
    calc (y⁻¹ * d) * z * (y⁻¹ * d)⁻¹
        = y⁻¹ * (d * z * d⁻¹) * y := by group
      _ = y⁻¹ * (y * z * y⁻¹) * y := by rw [← h]
      _ = z := by group
  have hcy : d * y⁻¹ ∈ Subgroup.centralizer
      (Ω : Set (MulAut (StdMod (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : y⁻¹ * x * y ∈ Ω := Ω.mul_mem (Ω.mul_mem (Ω.inv_mem hyΩ) hx) hyΩ
    have hcz : (y⁻¹ * d) * (y⁻¹ * x * y) * (y⁻¹ * d)⁻¹ = y⁻¹ * x * y := hc _ hx'
    have hcz' : (y⁻¹ * d) * (y⁻¹ * x * y) = (y⁻¹ * x * y) * (y⁻¹ * d) := by
      calc (y⁻¹ * d) * (y⁻¹ * x * y)
          = ((y⁻¹ * d) * (y⁻¹ * x * y) * (y⁻¹ * d)⁻¹) * (y⁻¹ * d) := by group
        _ = (y⁻¹ * x * y) * (y⁻¹ * d) := by rw [hcz]
    calc x * (d * y⁻¹)
        = y * ((y⁻¹ * x * y) * (y⁻¹ * d)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * d) * (y⁻¹ * x * y)) * y⁻¹ := by rw [← hcz']
      _ = (d * y⁻¹) * x := by group
  have hdcyC : d * y⁻¹ ∈ C := hcent' hcy
  have hdcyD : d * y⁻¹ ∈ D := hCD' hdcyC
  have hyD : y ∈ D := by
    have hyeq : y = (d * y⁻¹)⁻¹ * d := by group
    rw [hyeq]
    exact D.mul_mem (D.inv_mem hdcyD) hdD
  have hyne : y ≠ 1 := by
    intro hy1
    apply hdC
    have hd : d = d * y⁻¹ := by rw [hy1, inv_one, mul_one]
    rw [hd]
    exact hdcyC
  exact ⟨y, ⟨hyD, hyΩ⟩, hyne⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
