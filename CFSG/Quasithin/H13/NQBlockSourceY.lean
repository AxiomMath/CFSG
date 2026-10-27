module

public import CFSG.Quasithin.H13.NQBlockOriginalKSingleton
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

variable {G : Type} [Group G]

@[expose] def nqComplementaryLayer (H A : Subgroup G) : Subgroup G :=
  sSup {C | C ∈ cComp H ∧ C ≠ A}

@[expose] def OriginalKComplementaryLayerControl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → nqOriginalK T L ⊔ T ≤ H → H ≠ M →
      ∃ A ∈ cComp H, nqOriginalK T L ≤ A ∧
        (∀ A' ∈ cComp H, nqOriginalK T L ≤ A' → A' = A) ∧
        ⁅nqOriginalK T L, nqComplementaryLayer H A⁆ ≤ pCoreOf 2 (nqComplementaryLayer H A)

@[expose] def OriginalKContainingConfinement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → nqOriginalK T L ⊔ T ≤ H → H ≠ M →
    ∀ A ∈ cComp H, nqOriginalK T L ≤ A → (∀ A' ∈ cComp H, nqOriginalK T L ≤ A' → A' = A) →
      nqComplementaryLayer H A ≤ M → ∀ C ∈ cComp H, C ≤ M

@[expose] def AllComponentsContainedSourceY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → nqOriginalK T L ⊔ T ≤ H → H ≠ M →
    (∀ C ∈ cComp H, C ≤ M) →
    ∀ A ∈ cComp H, nqOriginalK T L ≤ A → (∀ A' ∈ cComp H, nqOriginalK T L ≤ A' → A' = A) →
      ∃ (r : ℕ) (Y : Subgroup G), r.Prime ∧ r ≠ 2 ∧ Y ≤ H ∧ (Y.subgroupOf H).Normal ∧
        ¬ Y ≤ M ∧ Monoid.exponent (Y ⧸ CFSG.pCore 2 Y) = r ∧
        Subgroup.upperCentralSeries (Y ⧸ CFSG.pCore 2 Y) 2 = ⊤ ∧
        CFSG.pRank r (Y ⧸ CFSG.pCore 2 Y) ≤ 2 ∧ Nat.card (Y ⧸ CFSG.pCore 2 Y) ≤ r ^ 3 ∧
        ⁅nqOriginalK T L, Y⁆ ≤ pCoreOf 2 (nqOriginalK T L) ⊓ pCoreOf 2 Y

@[expose] def ComplementaryEscapeSimpleSourceY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → nqOriginalK T L ⊔ T ≤ H → H ≠ M →
    ∀ A ∈ cComp H, nqOriginalK T L ≤ A → (∀ A' ∈ cComp H, nqOriginalK T L ≤ A' → A' = A) →
      ¬ nqComplementaryLayer H A ≤ M →
      ∃ B ∈ cComp H, B ≠ A ∧ ¬ B ≤ M ∧ B ≤ H ∧ (B.subgroupOf H).Normal ∧
        (Nonempty (B ⧸ CFSG.pCore 2 B ≃* alternatingGroup (Fin 5)) ∨
          CFSG.Blueprint.LieModel (B ⧸ CFSG.pCore 2 B) .PSL 3 2 1)

theorem commutator_le_pCoreOf_of_le_layer {K H B Y : Subgroup G} (hKH : K ≤ H) (hBH : B ≤ H)
    (hBn : (B.subgroupOf H).Normal) (hBY : B ≤ Y) (hKY : ⁅K, Y⁆ ≤ pCoreOf 2 Y) :
    ⁅K, B⁆ ≤ pCoreOf 2 B := by
  have h1 : ⁅K, B⁆ ≤ pCoreOf 2 Y := (commutator_mono le_rfl hBY).trans hKY
  have hHB : H ≤ normalizer (B : Set G) := (normal_subgroupOf_iff_le_normalizer hBH).mp hBn
  have h2 : ⁅K, B⁆ ≤ B := by
    rw [commutator_le]
    intro k hk b hb
    have hkb : k * b * k⁻¹ ∈ B := (mem_normalizer_iff.mp (hHB (hKH hk)) b).mp hb
    rw [commutatorElement_def]
    exact mul_mem hkb (inv_mem hb)
  have hYN : Y ≤ normalizer (pCoreOf 2 Y : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 Y
  have hQ2 : IsPGroup 2 (pCoreOf 2 Y ⊓ B : Subgroup G) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 Y).to_le inf_le_left
  have hQn : ((pCoreOf 2 Y ⊓ B).subgroupOf B).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro b hb
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
      exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hYN (hBY hb)) x).mp hx1,
        mul_mem (mul_mem hb hx2) (inv_mem hb)⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
      have hx3 : x = b⁻¹ * (b * x * b⁻¹) * b := by group
      refine mem_inf.mpr ⟨(mem_normalizer_iff.mp (hYN (hBY hb)) x).mpr hx1, ?_⟩
      rw [hx3]
      exact mul_mem (mul_mem (inv_mem hb) hx2) hb
  exact (le_inf h1 h2).trans (le_pCoreOf_of_subgroupOf_normal inf_le_right hQn hQ2)

theorem originalKEscapingSourceY_of (hC : OriginalKComplementaryLayerControl)
    (hF : OriginalKContainingConfinement) (hA : AllComponentsContainedSourceY)
    (hB : ComplementaryEscapeSimpleSourceY) : OriginalKEscapingSourceY := by
  intro G _ _ T L M h H hH hKTH hHM
  obtain ⟨A, hAc, hKA, hAu, hKY⟩ := hC G T L M h H hH hKTH hHM
  by_cases hYM : nqComplementaryLayer H A ≤ M
  · obtain ⟨r, Y, hr, hr2, hYH, hYn, hYM', hexp, hcl, hrk, hcard, hKY'⟩ :=
      hA G T L M h H hH hKTH hHM (hF G T L M h H hH hKTH hHM A hAc hKA hAu hYM) A hAc hKA hAu
    exact ⟨Y, hYH, hYn, hYM', hKY'.trans inf_le_right,
      Or.inl ⟨r, hr, hr2, hexp, hcl, hrk, hcard⟩⟩
  · obtain ⟨B, hBc, hBA, hBM, hBH, hBn, hBmod⟩ :=
      hB G T L M h H hH hKTH hHM A hAc hKA hAu hYM
    have hBY : B ≤ nqComplementaryLayer H A := le_sSup ⟨hBc, hBA⟩
    refine ⟨B, hBH, hBn, hBM,
      commutator_le_pCoreOf_of_le_layer (le_sup_left.trans hKTH) hBH hBn hBY hKY, ?_⟩
    rcases hBmod with h5 | hL
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr (CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL))

end CFSG.Quasithin.H13.NQBlock
