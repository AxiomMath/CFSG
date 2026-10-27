module

public import CFSG.LocalAnalysis.StandardType.GGHalfInnerLocal
public import CFSG.LocalAnalysis.StandardType.GGHalfEndNodes

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

theorem conj_tEps {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) (e : ℕ) :
    hElt φ₂ * φ₁ (tEps m e (by have := h.nbr.2.2.1; omega)) * (hElt φ₂)⁻¹ =
      vElt φ₁ * wElt φ₂ ^ e := by
  have hm : 1 ≤ m := by have := h.nbr.2.2.1; omega
  have hv : vElt φ₁ * hElt φ₂ = hElt φ₂ * vElt φ₁ := by
    obtain ⟨-, -, -, -, -, -, -, hyK, -, -⟩ := h.basic
    have hvz : vElt φ₁ ∈ Subgroup.zpowers y := by
      rw [h.zpowers_y]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvz
    have hhK : hElt φ₂ ∈ K := by
      rw [hElt, ← h.coords.range₂]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have hycomm : Commute y (hElt φ₂) := hyK (hElt φ₂) hhK
    rw [← hk]
    exact hycomm.zpow_left k
  have ht : φ₁ (tEps m e hm) = vElt φ₁ * uElt φ₂ ^ e := by
    unfold tEps
    rw [map_mul, map_pow]
    rw [show φ₁ (omegaBlock (m + 1 + 1) ⟨2, by omega⟩) = uElt φ₂ from h.uElt_eq.symm]
    rfl
  rw [ht]
  have hvconj : hElt φ₂ * vElt φ₁ * (hElt φ₂)⁻¹ = vElt φ₁ := by
    rw [← hv]; group
  have huconj : ∀ n : ℕ, hElt φ₂ * uElt φ₂ ^ n * (hElt φ₂)⁻¹ = wElt φ₂ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc hElt φ₂ * uElt φ₂ ^ (n + 1) * (hElt φ₂)⁻¹
            = (hElt φ₂ * uElt φ₂ * (hElt φ₂)⁻¹) *
                (hElt φ₂ * uElt φ₂ ^ n * (hElt φ₂)⁻¹) := by
              rw [pow_succ]; group
          _ = wElt φ₂ * wElt φ₂ ^ n := by rw [h.h_u, ih]
          _ = wElt φ₂ ^ (n + 1) := by rw [pow_succ]; group
  calc hElt φ₂ * (vElt φ₁ * uElt φ₂ ^ e) * (hElt φ₂)⁻¹
      = (hElt φ₂ * vElt φ₁ * (hElt φ₂)⁻¹) *
          (hElt φ₂ * uElt φ₂ ^ e * (hElt φ₂)⁻¹) := by group
    _ = vElt φ₁ * wElt φ₂ ^ e := by rw [hvconj, huconj]

end GGHalfCtx

end CFSG.StandardType

end
