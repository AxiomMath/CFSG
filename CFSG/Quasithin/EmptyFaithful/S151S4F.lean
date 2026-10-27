module

public import CFSG.Quasithin.EmptyFaithful.S151S4B
public import CFSG.Quasithin.EmptyFaithful.S151XF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Statements

variable {G : Type} [Group G] [Finite G]

@[expose] def BaumNormalizesComponentsStatement : Prop :=
  ∀ H T V L : Subgroup G, CharTwo H → IsTwoReducedIn H V → IsSylowTwoOf T H → IsSQTKTC H →
    L ∈ cComp H →
    (∃ (Q : Type) (_ : Group Q) (φ : ↥L →* Q), Function.Surjective φ ∧
      φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L ∧ CFSG.IsQuasisimple Q) →
    ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (V : Set G) →
      baum T ≤ Subgroup.normalizer (L : Set G)

end Statements

@[expose] def TheoremC116Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BaumNormalizesComponentsStatement (G := G)

namespace S151S4

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_of_isSubnormal {H K : Subgroup G} (h : IsSubnormal H K) :
    pCoreOf 2 H ≤ pCoreOf 2 K := by
  induction h with
  | refl => exact le_rfl
  | @step H M K hle hN _ ih =>
    refine le_trans ?_ ih
    have hHM : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hle)
      (hHM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)

theorem center_eq_bot_of_isPSL2 {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    Subgroup.center X = ⊥ := by
  obtain ⟨K, hF, hfin, hchar, hcard, ⟨e⟩⟩ := exists_equiv_sl2 h
  rw [eq_bot_iff]
  intro x hx
  have h1 : e x ∈ Subgroup.center (SL2 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  rw [center_sl2_eq_bot K, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (by simpa using h1)

end S151S4

@[expose] def Input15120WreathChar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → ListA15120 L → ¬ IsBlock2 (L ⊔ s1516 T Z₁) L →
    ¬ s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) → CharTwo (L ⊔ s1516 T Z₁)

end CFSG.Quasithin
