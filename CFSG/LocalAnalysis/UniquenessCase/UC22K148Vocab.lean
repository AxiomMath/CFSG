module

public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.ComponentSection
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b (antiProjEquiv)

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V} {A : Subgroup G}

theorem mem_calP_iff : A ∈ calP ρ ↔ A ≠ ⊥ ∧ IsElemBestOffender ρ A := by
  rw [calP, Set.mem_setOf_eq, IsElemBestOffender,
    CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian]

theorem isElementaryAbelian_of_mem_calP (hA : A ∈ calP ρ) : CFSG.IsElementaryAbelian 2 ↥A :=
  (mem_calP_iff.1 hA).2.1

theorem isElemBestOffender_of_mem_calP (hA : A ∈ calP ρ) : IsElemBestOffender ρ A :=
  (mem_calP_iff.1 hA).2

theorem le_hP_of_mem_calP (hA : A ∈ calP ρ) : A ≤ hP ρ :=
  le_iSup₂_of_le A hA le_rfl

theorem hP_eq_bestOffenderSub (ρ : Representation (ZMod 2) G V) : hP ρ = bestOffenderSub ρ := by
  rw [bestOffenderSub_eq_iSup_ne_bot]
  refine le_antisymm (iSup₂_le fun B hB => le_iSup₂_of_le B (mem_calP_iff.1 hB) le_rfl)
    (iSup₂_le fun B hB => le_iSup₂_of_le B (mem_calP_iff.2 hB) le_rfl)

theorem isBestOffenderOn_of_mem_calP (hρ : Function.Injective ρ) (hA : A ∈ calP ρ) :
    IsBestOffenderOn ρ A ⊤ := by
  refine (isBestOffender_iff_on ρ A fun a _ ha => hρ ?_).1 (isElemBestOffender_of_mem_calP hA)
  ext w
  simp [ha w]

theorem hP_le_normalizer [Finite G] [Finite V] (hρ : Function.Injective ρ) {L : Subgroup G}
    (hL : IsComponentOf L ⊤) : hP ρ ≤ Subgroup.normalizer (L : Set G) := by
  rw [hP_eq_bestOffenderSub]
  exact bestOffenderSub_le_normalizer_component ρ hρ ((CFSG.isComponent_iff_open L).2 hL)

theorem le_normalizer_of_mem_calP [Finite G] [Finite V] (hρ : Function.Injective ρ) {L : Subgroup G}
    (hL : IsComponentOf L ⊤) (hA : A ∈ calP ρ) : A ≤ Subgroup.normalizer (L : Set G) :=
  (le_hP_of_mem_calP hA).trans (hP_le_normalizer hρ hL)

theorem commutator_eq_self_of_mem_calP [Finite G] [Finite V] (hρ : Function.Injective ρ)
    {L : Subgroup G} (hL : IsComponentOf L ⊤) (hA : A ∈ calP ρ) (h : ⁅L, A⁆ ≠ ⊥) : ⁅L, A⁆ = L :=
  commutator_eq_of_ne_bot ((CFSG.isComponent_iff_open L).2 hL).1 (le_normalizer_of_mem_calP hρ hL hA) h

theorem exists_antiSp_of_isSp4 {X : Type} [Group X] {n : ℕ} (h : IsSp4 X n) :
    2 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* antiSp K) := by
  have hn : 2 ≤ n := by
    obtain ⟨-, hf, -, hne⟩ := CFSG.Blueprint.LieModel.admissible h
    by_contra hlt
    obtain rfl : n = 1 := by omega
    exact hne (by simp)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  exact ⟨hn, K, inferInstance, Fintype.ofFinite K, inferInstance, hK,
    ⟨e.trans (antiProjEquiv K).symm⟩⟩

theorem four_le_card {K : Type} {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) : 4 ≤ Nat.card K := by
  rw [hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem isSimpleGroup_antiSp_of_four_le {K : Type} [Field K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    IsSimpleGroup (antiSp K) := by
  have : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr h4))
  exact (antiProjEquiv K).isSimpleGroup

theorem isSimpleGroup_of_isSp4 {X : Type} [Group X] {n : ℕ} (h : IsSp4 X n) : IsSimpleGroup X := by
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := exists_antiSp_of_isSp4 h
  have := isSimpleGroup_antiSp_of_four_le (four_le_card hn hK)
  exact e.isSimpleGroup

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
