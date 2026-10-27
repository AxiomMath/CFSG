module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F9Eighteen

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem clause_two (h : HypF918 T V L V₁ Vp H K) :
    ∃ B : Subgroup G, B ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T) ∧
      (∀ b ∈ B, (∀ k ∈ conjClosure K T, b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → b ∈ pCoreOf 2 H) ∧
      autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H)) ∈
        @Qset ↥(tildeOf V₁ (conjClosure Vp H))
          (commGroupOfElemAbelian h.toHypF98.toHypF91.isElemAbelian_tilde)
          (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) := by
  obtain ⟨B, ⟨hBL, -, hfaith⟩, hQ⟩ := h.F918_2
  exact ⟨B, hBL, hfaith, hQ⟩

theorem commutator_kernel_le_pCoreOf (h : HypF918 T V L V₁ Vp H K) {F E : Subgroup G}
    (hF : conjClosure K T ⊔ T ≤ Subgroup.normalizer (F : Set G))
    (hE : conjClosure K T ⊔ T ≤ Subgroup.normalizer (E : Set G))
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ e ∈ E, k * e * k⁻¹ * e⁻¹ ∈ F) :
    ⁅centralizerMod F (conjClosure K T ⊔ T) E, conjClosure K T⁆ ≤ pCoreOf 2 H := by
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hXn : conjClosure K T ⊔ T ≤
      Subgroup.normalizer ((conjClosure K T ⊔ T : Subgroup G) : Set G) := Subgroup.le_normalizer
  have hK₀n : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    HypF918.K₀T_le_normalizer_K₀ T K
  set Nx : Subgroup G := centralizerMod F (conjClosure K T ⊔ T) E with hNx
  have hNxX : Nx ≤ conjClosure K T ⊔ T := centralizerMod_le_left _ _ _
  have hNxn : conjClosure K T ⊔ T ≤ Subgroup.normalizer (Nx : Set G) :=
    le_normalizer_centralizerMod hF hXn hE
  have hDK₀ : ⁅Nx, conjClosure K T⁆ ≤ conjClosure K T :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp (hNxX.trans hK₀n)
  have hDNx : ⁅Nx, conjClosure K T⁆ ≤ Nx := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hNxn)
  have hDn : conjClosure K T ⊔ T ≤
      Subgroup.normalizer ((⁅Nx, conjClosure K T⁆ : Subgroup G) : Set G) :=
    F9.le_normalizer_commutator_of_le hNxn hK₀n
  have hcomm : ⁅⁅Nx, conjClosure K T⁆, conjClosure K T⁆ ≤ pCoreOf 2 H := by
    rcases exists_le_or_commutator_le_pCoreOf h.K_cComp h.T_le_H h.K_quasisimple hDK₀
        (le_sup_left.trans hDn) (le_sup_right.trans hDn) with hle | hcomm
    · exact absurd (fun k hk e he => (hDNx (hle hk)).2.2 e he) hnt
    · exact hcomm
  refine commutator_le_of_commutator_commutator_le
    (hNxX.trans (h.K₀T_le_H.trans hQn)) (h.K₀_le_H.trans hQn) h.K₀_perfect ?_
  rw [Subgroup.commutator_comm (conjClosure K T) Nx]
  exact hcomm

theorem clause_one_core (h : HypF918 T V L V₁ Vp H K) :
    IsSylowTwoOf T H ∧ oTwoRes (conjClosure K T) = conjClosure K T ∧
      H ≤ Subgroup.normalizer (conjClosure K T : Set G) ∧
      V₁ ≤ conjClosure Vp H ∧ conjClosure Vp H ≤ pCoreOf 2 H ∧
      H ≤ Subgroup.normalizer (V₁ : Set G) ∧
      H ≤ Subgroup.normalizer (conjClosure Vp H : Set G) ∧
      IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)) ∧
      (∀ E : Subgroup G, E ≤ conjClosure K T → conjClosure K T ≤ Subgroup.normalizer (E : Set G) →
        (∀ e ∈ E, ∃ k : ℕ, e ^ 2 ^ k ∈ pCoreOf 2 H) → E ≤ pCoreOf 2 H) := by
  have h1 := h.toHypF98.toHypF91
  obtain ⟨-, h2, h3, h4⟩ := h.F918_1
  exact ⟨h1.sylow_H, h2, h3, h1.V₁_le_Vp.trans (le_conjClosure Vp H), h1.conjClosure_Vp_le_pCoreOf,
    h1.H_normalizes_V₁, le_normalizer_conjClosure Vp H, h1.isElemAbelian_tilde, h4⟩

end CFSG.Quasithin.RonanF918
