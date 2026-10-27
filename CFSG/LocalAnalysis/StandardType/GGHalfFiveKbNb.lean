module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveBElt
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveSl3Facts
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveLeviBlock
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveAlphaZeta
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveConjFive
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveLbLayer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)

include h

theorem kb_le_of_pComponent {N : Subgroup G}
    (hN : LargeEvenPComponent p (Subgroup.centralizer ({bElt φ₁ φ₂} : Set G)) N)
    (hL₁ : sl3four.map φ₁ ≤ N) : sl3four.map φ₂ ≤ N := by
  haveI : Fact p.Prime := ⟨by rw [h.nbr.2.1]; exact Nat.prime_three⟩
  set y₁ : G := (gElt φ₁)⁻¹ * hElt φ₂ with hy₁
  have hgconj : (gElt φ₁)⁻¹ * bElt φ₁ φ₂ * (gElt φ₁) = bElt φ₁ φ₂ := by
    calc (gElt φ₁)⁻¹ * bElt φ₁ φ₂ * (gElt φ₁)
        = (gElt φ₁)⁻¹ * (bElt φ₁ φ₂ * gElt φ₁) := by group
      _ = (gElt φ₁)⁻¹ * (gElt φ₁ * bElt φ₁ φ₂) := by rw [← gElt_comm_b h]
      _ = bElt φ₁ φ₂ := by group
  have hhconj : hElt φ₂ * bElt φ₁ φ₂ * (hElt φ₂)⁻¹ = bElt φ₁ φ₂ := by
    calc hElt φ₂ * bElt φ₁ φ₂ * (hElt φ₂)⁻¹
        = (hElt φ₂ * bElt φ₁ φ₂) * (hElt φ₂)⁻¹ := by group
      _ = (bElt φ₁ φ₂ * hElt φ₂) * (hElt φ₂)⁻¹ := by rw [hElt_comm_b h]
      _ = bElt φ₁ φ₂ := by group
  have hyb : y₁ * bElt φ₁ φ₂ * y₁⁻¹ = bElt φ₁ φ₂ := by
    rw [hy₁]
    calc (gElt φ₁)⁻¹ * hElt φ₂ * bElt φ₁ φ₂ * ((gElt φ₁)⁻¹ * hElt φ₂)⁻¹
        = (gElt φ₁)⁻¹ * (hElt φ₂ * bElt φ₁ φ₂ * (hElt φ₂)⁻¹) * gElt φ₁ := by group
      _ = (gElt φ₁)⁻¹ * bElt φ₁ φ₂ * gElt φ₁ := by rw [hhconj]
      _ = bElt φ₁ φ₂ := hgconj
  have hN' : LargeEvenPComponent p (Subgroup.centralizer ({bElt φ₁ φ₂} : Set G))
      (N.map (MulAut.conj y₁).toMonoidHom) := by
    have hconj := largeEvenPComponent_conj_centralizer_singleton hN y₁
    rwa [hyb] at hconj
  obtain ⟨α, hα⟩ := exists_alpha_five h
  have hαζ : α zeta5 = zeta5 := alpha_zeta5 h hα
  have hmap : sl3four.map α.toMonoidHom = sl3four := map_sl3four_of_fix hαζ
  have hconjα : ∀ s ∈ sl3four,
      y₁ * φ₁ (α s) * y₁⁻¹ = φ₂ s := by
    intro s _
    have h1 : hElt φ₂ * φ₁ (α s) * (hElt φ₂)⁻¹ = gElt φ₁ * φ₂ s * (gElt φ₁)⁻¹ := hα s
    rw [hy₁]
    calc (gElt φ₁)⁻¹ * hElt φ₂ * φ₁ (α s) * ((gElt φ₁)⁻¹ * hElt φ₂)⁻¹
        = (gElt φ₁)⁻¹ * (hElt φ₂ * φ₁ (α s) * (hElt φ₂)⁻¹) * gElt φ₁ := by group
      _ = (gElt φ₁)⁻¹ * (gElt φ₁ * φ₂ s * (gElt φ₁)⁻¹) * gElt φ₁ := by rw [h1]
      _ = φ₂ s := by group
  have hK_in : sl3four.map φ₂ ≤ N.map (MulAut.conj y₁).toMonoidHom := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hz
    have has : α s ∈ sl3four := by
      have h := Subgroup.mem_map_of_mem α.toMonoidHom hs
      rwa [hmap] at h
    have hmemN : φ₁ (α s) ∈ N := hL₁ (Subgroup.mem_map_of_mem φ₁ has)
    have hmemN' : y₁ * φ₁ (α s) * y₁⁻¹ ∈ N.map (MulAut.conj y₁).toMonoidHom := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj y₁).toMonoidHom hmemN
      change (MulAut.conj y₁) (φ₁ (α s)) ∈ N.map (MulAut.conj y₁).toMonoidHom at h
      rwa [MulAut.conj_apply] at h
    rw [← hconjα s hs]
    exact hmemN'
  obtain ⟨P, hPcomm, ⟨g₀, hg₀P, hg₀1, hg₀3⟩, hPL, hPU⟩ := exists_levi_perfect
  let Pb : Subgroup G := P.map (φ₁.comp (slLower2Hom 3))
  have hPb_le_N : Pb ≤ N := by
    calc Pb = (P.map (slLower2Hom 3)).map φ₁ :=
          (Subgroup.map_map P φ₁ (slLower2Hom 3)).symm
      _ ≤ sl3four.map φ₁ := Subgroup.map_mono hPL
      _ ≤ N := hL₁
  have hPb_le_N' : Pb ≤ N.map (MulAut.conj y₁).toMonoidHom := by
    calc Pb = P.map (φ₂.comp (slUpper2Hom 3)) := by
          show P.map (φ₁.comp (slLower2Hom 3)) = P.map (φ₂.comp (slUpper2Hom 3))
          rw [h.coords.agree]
      _ = (P.map (slUpper2Hom 3)).map φ₂ :=
          (Subgroup.map_map P φ₂ (slUpper2Hom 3)).symm
      _ ≤ sl3four.map φ₂ := Subgroup.map_mono hPU
      _ ≤ N.map (MulAut.conj y₁).toMonoidHom := hK_in
  have hPb_comm : ⁅Pb, Pb⁆ = Pb := by
    have h := Subgroup.map_commutator P P (φ₁.comp (slLower2Hom 3))
    rw [hPcomm] at h
    exact h.symm
  have hg : (φ₁.comp (slLower2Hom 3)) g₀ ∈ ⁅Pb, Pb⁆ := by
    rw [hPb_comm]
    exact Subgroup.mem_map_of_mem (φ₁.comp (slLower2Hom 3)) hg₀P
  have hg1 : (φ₁.comp (slLower2Hom 3)) g₀ ≠ 1 := by
    intro h1
    have h2 : slLower2Hom 3 g₀ = 1 := by
      apply h.coords.inj₁
      simpa only [MonoidHom.comp_apply, map_one] using h1
    exact hg₀1 (slLower2Hom_injective 3 (h2.trans (map_one _).symm))
  have hgp : (φ₁.comp (slLower2Hom 3)) g₀ ^ p = 1 := by
    have h3 : (φ₁.comp (slLower2Hom 3)) g₀ ^ 3 = 1 := by
      show φ₁ (slLower2Hom 3 g₀) ^ 3 = 1
      calc φ₁ (slLower2Hom 3 g₀) ^ 3 = φ₁ ((slLower2Hom 3 g₀) ^ 3) :=
            (map_pow φ₁ (slLower2Hom 3 g₀) 3).symm
        _ = φ₁ (slLower2Hom 3 (g₀ ^ 3)) := by rw [map_pow (slLower2Hom 3) g₀ 3]
        _ = φ₁ (slLower2Hom 3 1) := by rw [hg₀3]
        _ = 1 := by rw [map_one, map_one]
    rw [h.nbr.2.1]
    exact h3
  have heq : N = N.map (MulAut.conj y₁).toMonoidHom :=
    eq_of_pComponents_of_common_derived hN hN' hPb_le_N hPb_le_N' hg hg1 hgp
  rw [← heq] at hK_in
  exact hK_in

end GGHalfCtx

end CFSG.StandardType

end
