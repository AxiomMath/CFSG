module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRCor
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRS3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRA5

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F53Mod

variable {G : Type} [Group G] [Finite G]

theorem prop41_s3 {X P Z : Subgroup G} (h : PushHyp X P Z)
    (he : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3))) (hnc : NoCharNormal P X)
    (hB : BaumannC X Z) {y : G} (hy : y ∈ Subgroup.normalizer (P : Set G))
    (hne : ⁅Z, cj y Z⁆ ≠ ⊥) :
    y * y ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) ∧
      y ∉ Subgroup.normalizer (pCoreOf 2 X : Set G) ∧ cj y (pCoreOf 2 X) ≠ pCoreOf 2 X ∧
      ∀ n ∈ Subgroup.normalizer (P : Set G), n ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) →
        n ∈ Subgroup.normalizer ((cj y (pCoreOf 2 X) : Subgroup G) : Set G) := by
  obtain ⟨e⟩ := he
  exact prop41 h hB (natFacts_of_s3 h e hnc) hy hne

theorem cor42_s3 {X P Z H₀ : Subgroup G} (h : PushHyp X P Z)
    (he : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3))) (hnc : NoCharNormal P X)
    (hB : BaumannC X Z) (hH₀ : H₀ ≤ Subgroup.normalizer (P : Set G))
    (hodd : Odd ((Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ H₀).relIndex H₀)) :
    (∀ g ∈ H₀, cj g Z ≤ pCoreOf 2 X) ∧ conjJoinOf H₀ Z ≤ pCoreOf 2 X ∧
      (P ≤ Subgroup.normalizer (conjJoinOf H₀ Z : Set G) →
        X ≤ Subgroup.normalizer (conjJoinOf H₀ Z : Set G)) := by
  obtain ⟨e⟩ := he
  have hN := natFacts_of_s3 h e hnc
  have hle := cor42_join_le h hB hN hH₀ hodd
  exact ⟨cor42_cj_le h hB hN hH₀ hodd, hle, fun hP =>
    le_normalizer_of_core h hB hP hle (le_trans (cj_one Z).symm.le (cj_le_conjJoin H₀.one_mem))⟩

theorem cor42_a5 {X P Z H₀ : Subgroup G} (h : PushHyp X P Z)
    (he : Nonempty (OTwoQuot X ≃* ↥(alternatingGroup (Fin 5))))
    (hnat : IsNatSecA5 X (zZero X Z) Z) (hB : BaumannC X Z)
    (hH₀ : H₀ ≤ Subgroup.normalizer (P : Set G))
    (hodd : Odd ((Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ H₀).relIndex H₀)) :
    (∀ g ∈ H₀, cj g Z ≤ pCoreOf 2 X) ∧ conjJoinOf H₀ Z ≤ pCoreOf 2 X ∧
      (P ≤ Subgroup.normalizer (conjJoinOf H₀ Z : Set G) →
        X ≤ Subgroup.normalizer (conjJoinOf H₀ Z : Set G)) := by
  obtain ⟨e⟩ := he
  have hN := natFacts_of_a5 h e hnat
  have hle := cor42_join_le h hB hN hH₀ hodd
  exact ⟨cor42_cj_le h hB hN hH₀ hodd, hle, fun hP =>
    le_normalizer_of_core h hB hP hle (le_trans (cj_one Z).symm.le (cj_le_conjJoin H₀.one_mem))⟩

theorem cor42S3P (G : Type) [Group G] [Finite G] :
    ∀ X P Z H₀ : Subgroup G, PushHyp X P Z → Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3)) →
      NoCharNormal P X → BaumannC X Z → H₀ ≤ Subgroup.normalizer (P : Set G) → P ≤ H₀ →
      Odd ((Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ H₀).relIndex H₀) → Cor42Concl X Z H₀ := by
  intro X P Z H₀ h he hnc hB hH₀ hPH hodd
  obtain ⟨e⟩ := he
  exact cor42 h hB (natFacts_of_s3 h e hnc) hH₀ hPH hodd

theorem cor42A5P (G : Type) [Group G] [Finite G] :
    ∀ X P Z H₀ : Subgroup G, PushHyp X P Z →
      Nonempty (OTwoQuot X ≃* ↥(alternatingGroup (Fin 5))) → IsNatSecA5 X (zZero X Z) Z →
      NoCharNormal P X → BaumannC X Z → H₀ ≤ Subgroup.normalizer (P : Set G) → P ≤ H₀ →
      Odd ((Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ H₀).relIndex H₀) → Cor42Concl X Z H₀ := by
  intro X P Z H₀ h he hnat _ hB hH₀ hPH hodd
  obtain ⟨e⟩ := he
  exact cor42 h hB (natFacts_of_a5 h e hnat) hH₀ hPH hodd

end CFSG.Quasithin.F53Push
