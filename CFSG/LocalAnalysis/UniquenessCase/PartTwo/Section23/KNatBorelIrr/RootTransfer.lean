module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Model
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open Matrix CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped MatrixGroups

private lemma mem_normalizer_map_normalizer_L07 {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {G : Type} [Group G] {Γ : Subgroup (GL ι K)} (φ : G ≃* ↥Γ)
    (U₀ : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (U₀ : Set G)) :
    φ g ∈ Subgroup.normalizer ((U₀.map φ.toMonoidHom : Subgroup ↥Γ) : Set ↥Γ) := by
  rw [Subgroup.mem_set_normalizer_iff] at hg ⊢
  intro x
  change x ∈ (U₀.map φ.toMonoidHom : Subgroup ↥Γ) ↔
    φ g * x * (φ g)⁻¹ ∈ (U₀.map φ.toMonoidHom : Subgroup ↥Γ)
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  have hconj : φ.symm (φ g * x * (φ g)⁻¹) = g * φ.symm x * g⁻¹ := by simp
  rw [hconj]
  exact hg (φ.symm x)

theorem hasRootSL2_of_leastParabolic {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (GL ι K)} {e₀ : ι → K} {G : Type} [Group G] [Finite G] (φ : G ≃* ↥Γ)
    (U₀ : Sylow 2 G) (Qα Q₀ : Subgroup G) (ρ₀ : SL(2, K) →* G)
    (hQ₀ : Q₀.map φ.toMonoidHom = KTabD.lineStab Γ e₀) (hUQ₀ : (U₀ : Subgroup G) ≤ Q₀)
    (hleast : ∀ P : Subgroup G, IsParabolicTwo G P → (U₀ : Subgroup G) ≤ P → ¬ P ≤ Q₀ → Qα ≤ P)
    (hrange : ρ₀.range ≤ Qα)
    (htor : ∀ c : Kˣ, ρ₀ (torusSL c) ∈ Subgroup.normalizer ((U₀ : Subgroup G) : Set G) ∧
      (((φ (ρ₀ (torusSL c)) : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ e₀ = (c : K) • e₀) :
    HasRootSL2 Γ e₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ' : G →* ↥Γ := φ.toMonoidHom
  let U : Sylow 2 ↥Γ := U₀.mapSurjective (f := φ') φ.surjective
  let ρ : SL(2, K) →* ↥Γ := φ'.comp ρ₀
  have hNmap : ∀ g ∈ Subgroup.normalizer ((U₀ : Subgroup G) : Set G),
      φ g ∈ Subgroup.normalizer ((U : Subgroup ↥Γ) : Set ↥Γ) := by
    intro g hg
    exact mem_normalizer_map_normalizer_L07 φ U₀ hg
  refine ⟨U, ρ, ?_, ?_, ?_⟩
  · change (U₀ : Subgroup G).map φ' ≤ KTabD.lineStab Γ e₀
    exact (Subgroup.map_mono hUQ₀).trans (le_of_eq hQ₀)
  · intro P hNP hnot
    let P' : Subgroup G := P.comap φ'
    have hN0 : Subgroup.normalizer ((U₀ : Subgroup G) : Set G) ≤ P' := by
      intro g hg
      exact Subgroup.mem_comap.mpr (hNP (hNmap g hg))
    have hpar : IsParabolicTwo G P' := ⟨U₀, hN0⟩
    have hU0P' : (U₀ : Subgroup G) ≤ P' := Subgroup.le_normalizer.trans hN0
    have hnotP' : ¬ P' ≤ Q₀ := by
      intro hle
      apply hnot
      calc P = (P.comap φ').map φ' :=
            (Subgroup.map_comap_eq_self_of_surjective φ.surjective P).symm
        _ ≤ Q₀.map φ' := Subgroup.map_mono hle
        _ = KTabD.lineStab Γ e₀ := hQ₀
    have hQαP' : Qα ≤ P' := hleast P' hpar hU0P' hnotP'
    intro y hy
    obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hy
    exact Subgroup.mem_comap.mp (hrange.trans hQαP' (MonoidHom.mem_range.mpr ⟨B, rfl⟩))
  · intro c
    exact ⟨hNmap (ρ₀ (torusSL c)) (htor c).1, (htor c).2⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
