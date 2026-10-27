module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Fixed
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.RankThree.PartTwo.Sec18.Components
public import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open Matrix CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped MatrixGroups commutatorElement

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def torusSL (c : Kˣ) : SL(2, K) :=
  ⟨!![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

@[expose] def BorelScalars (Γ : Subgroup (GL ι K)) (U : Subgroup ↥Γ) (e₀ : ι → K) : Prop :=
  ∀ P : Subgroup ↥Γ, Subgroup.normalizer (U : Set ↥Γ) ≤ P → ¬ P ≤ KTabD.lineStab Γ e₀ →
    ∀ c : K, c ≠ 0 → ∃ t ∈ Hinf P ⊓ Subgroup.normalizer (U : Set ↥Γ),
      ((t : GL ι K) : Matrix ι ι K) *ᵥ e₀ = c • e₀

@[expose] def HasBorelScalars (Γ : Subgroup (GL ι K)) (e₀ : ι → K) : Prop :=
  ∃ U : Sylow 2 ↥Γ, (U : Subgroup ↥Γ) ≤ KTabD.lineStab Γ e₀ ∧
    BorelScalars Γ (U : Subgroup ↥Γ) e₀

@[expose] def HasRootSL2 (Γ : Subgroup (GL ι K)) (e₀ : ι → K) : Prop :=
  ∃ (U : Sylow 2 ↥Γ) (ρ : SL(2, K) →* ↥Γ), (U : Subgroup ↥Γ) ≤ KTabD.lineStab Γ e₀ ∧
    (∀ P : Subgroup ↥Γ, Subgroup.normalizer (U : Set ↥Γ) ≤ P → ¬ P ≤ KTabD.lineStab Γ e₀ →
      ρ.range ≤ P) ∧
    ∀ c : Kˣ, ρ (torusSL c) ∈ Subgroup.normalizer (U : Set ↥Γ) ∧
      (((ρ (torusSL c) : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ e₀ = (c : K) • e₀

private lemma commutator_range_eq_self_L04 {G H : Type} [Group G] [Group H] (f : G →* H)
    (hG : Group.IsPerfect G) : ⁅f.range, f.range⁆ = f.range := by
  haveI : Group.IsPerfect G := hG
  exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range f)

theorem borelScalars_of_roots {Γ : Subgroup (GL ι K)} {U : Subgroup ↥Γ} {e₀ : ι → K}
    (𝒳 : Set (Subgroup ↥Γ)) (hperf : ∀ X ∈ 𝒳, ⁅X, X⁆ = X)
    (hleast : ∀ P : Subgroup ↥Γ, Subgroup.normalizer (U : Set ↥Γ) ≤ P →
      ¬ P ≤ KTabD.lineStab Γ e₀ → ∃ X ∈ 𝒳, X ≤ P)
    (htor : ∀ X ∈ 𝒳, ∀ c : K, c ≠ 0 → ∃ t ∈ X ⊓ Subgroup.normalizer (U : Set ↥Γ),
      ((t : GL ι K) : Matrix ι ι K) *ᵥ e₀ = c • e₀) :
    BorelScalars Γ U e₀ := by
  intro P hNP hnot c hc
  obtain ⟨X, hX, hXP⟩ := hleast P hNP hnot
  have hXle : X ≤ Hinf P :=
    CFSG.RankThree.PartTwo.Sec18.le_inSubgroup_perfectResidual (hperf X hX) hXP
  obtain ⟨t, ht, htval⟩ := htor X hX c hc
  exact ⟨t, ⟨hXle ht.1, ht.2⟩, htval⟩

theorem borelScalars_of_rootHom [Finite K] (hK : 4 ≤ Nat.card K) {Γ : Subgroup (GL ι K)}
    {U : Subgroup ↥Γ} {e₀ : ι → K} (ρ : SL(2, K) →* ↥Γ)
    (hleast : ∀ P : Subgroup ↥Γ, Subgroup.normalizer (U : Set ↥Γ) ≤ P →
      ¬ P ≤ KTabD.lineStab Γ e₀ → ρ.range ≤ P)
    (htor : ∀ c : Kˣ, ρ (torusSL c) ∈ Subgroup.normalizer (U : Set ↥Γ) ∧
      (((ρ (torusSL c) : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ e₀ = (c : K) • e₀) :
    BorelScalars Γ U e₀ := by
  have hSLperf : Group.IsPerfect (SL(2, K)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  refine borelScalars_of_roots ({ρ.range} : Set (Subgroup ↥Γ)) ?_ ?_ ?_
  · intro X hX
    rw [Set.mem_singleton_iff] at hX
    subst hX
    exact commutator_range_eq_self_L04 ρ hSLperf
  · intro P hNP hnot
    exact ⟨ρ.range, Set.mem_singleton _, hleast P hNP hnot⟩
  · intro X hX c hc
    rw [Set.mem_singleton_iff] at hX
    subst hX
    refine ⟨ρ (torusSL (Units.mk0 c hc)),
      ⟨⟨torusSL (Units.mk0 c hc), rfl⟩, (htor (Units.mk0 c hc)).1⟩, ?_⟩
    rw [(htor (Units.mk0 c hc)).2, Units.val_mk0]

theorem hasBorelScalars_of_hasRootSL2 [Finite K] (hK : 4 ≤ Nat.card K)
    {Γ : Subgroup (GL ι K)} {e₀ : ι → K} (h : HasRootSL2 Γ e₀) : HasBorelScalars Γ e₀ := by
  obtain ⟨U, ρ, hU, hleast, htor⟩ := h
  exact ⟨U, hU, borelScalars_of_rootHom hK ρ hleast htor⟩

theorem borelScalars_of_card_two (hK : Nat.card K = 2) (Γ : Subgroup (GL ι K))
    (U : Subgroup ↥Γ) (e₀ : ι → K) : BorelScalars Γ U e₀ := by
  intro P hNP hnot c hc
  have hc1 : c = 1 := by
    obtain ⟨x, _hx0, hx⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
    exact (hx c hc).trans (hx 1 one_ne_zero).symm
  subst c
  exact ⟨1, ⟨one_mem _, one_mem _⟩, by simp⟩

theorem card_eq_two_or_four_le [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card K = 2 ∨ 4 ≤ Nat.card K := by
  rcases n with _ | _ | n
  · have h1 : Nat.card K = 1 := hK.trans (pow_zero 2)
    have hlt : 1 < Nat.card K := by
      haveI : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    rw [h1] at hlt
    exact absurd hlt (by norm_num)
  · exact Or.inl (hK.trans (pow_one 2))
  · have h : 4 ≤ 2 ^ (n + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Or.inr (by rw [hK]; exact h)

theorem hasBorelScalars_of_four_le [Finite K] {Γ : Subgroup (GL ι K)} {e₀ : ι → K}
    (hline : KTabC.SylowFixedLine Γ e₀) {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (h4 : 4 ≤ Nat.card K → HasBorelScalars Γ e₀) : HasBorelScalars Γ e₀ := by
  rcases card_eq_two_or_four_le hK with h2 | h4le
  · obtain ⟨U, hU⟩ := exists_sylow_le_lineStab hline
    exact ⟨U, hU, borelScalars_of_card_two h2 Γ ↑U e₀⟩
  · exact h4 h4le

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
