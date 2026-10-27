module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ReeSylowGenerationHolds
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open scoped commutatorElement

@[expose] def UC2_10_7OddReeSeven : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A), L.Normal → IsSimpleGroup ↥L →
    centralizer (L : Set A) = ⊥ → ∀ f : ℕ, CFSG.Blueprint.LieModel ↥L .twistedG2 0 3 f →
    ∀ (T B M : Subgroup A), CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
      B ≤ normalizer (T : Set A) → Nat.card B = 7 →
      L ⊔ T ⊔ B = ⊤ → T ≤ M → B ≤ M → (∀ g : A, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) →
      L ≤ M ∨ ⁅T, B⁆ = ⊥

theorem commutator_eq_bot_of_card_lt_prime {A : Type} [Group A] {T B : Subgroup A} [Finite T]
    {p : ℕ} (hp : p.Prime) (hBp : Nat.card B = p) (hBT : B ≤ normalizer (T : Set A))
    (hT : Nat.card T < p) : ⁅T, B⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer]
  intro t ht
  rw [mem_centralizer_iff]
  intro b hb
  let φ : ↥B →* Equiv.Perm ↥T :=
    (MulAut.toPerm ↥T).comp (T.normalizerMonoidHom.comp (inclusion hBT))
  have hord : orderOf (φ ⟨b, hb⟩) = 1 := by
    have h1 : orderOf (φ ⟨b, hb⟩) ∣ p :=
      hBp ▸ (orderOf_map_dvd φ _).trans (orderOf_dvd_natCard _)
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact h
    · have h2 : p ∣ (Nat.card T).factorial := by
        rw [← h, ← Nat.card_perm]
        exact orderOf_dvd_natCard _
      exact absurd (hp.dvd_factorial.mp h2) (not_le.mpr hT)
  have h3 : b * t * b⁻¹ = t :=
    congrArg Subtype.val (Equiv.ext_iff.mp (orderOf_eq_one_iff.mp hord) ⟨t, ht⟩)
  calc b * t = b * t * b⁻¹ * b := by group
    _ = t * b := by rw [h3]

theorem uc2_10_7OddRee_of_seven
    (h7 : UC2_10_7OddReeSeven) : UC2_10_7OddRee := by
  intro A _ _ L hLn hLs hCL f hmod s p T B M hs hp hdvd hT hBT hBp hsup hTM hBM hstar
  by_cases hp7 : p = 7
  · subst hp7
    exact h7 A L hLn hLs hCL f hmod T B M hT hBT hBp hsup hTM hBM hstar
  right
  have h8 : 8 < p := by
    have h7le : 7 ≤ p := PartTwo.s13_seven_le_of_dvd hs hp hdvd
    rcases Nat.lt_or_ge 8 p with h | h
    · exact h
    · interval_cases p
      · exact absurd rfl hp7
      · norm_num at hp
  obtain ⟨-, -, -, -, ⟨k, rfl⟩, hf3⟩ := CFSG.Blueprint.LieModel.admissible hmod
  obtain ⟨-, hout, hsyl⟩ :=
    k_ReeSylowGeneration_holds ↥L (3 ^ (2 * k + 1)) k ⟨k, rfl, hmod⟩ rfl (by omega)
  have hTL : T ≤ L := by
    intro t ht
    obtain ⟨n, hn⟩ := hT.isPGroup ⟨t, ht⟩
    have htn : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hN : t ∈ normalizer (L : Set A) := by
      rw [normalizer_eq_top_iff.mpr hLn]
      exact mem_top t
    have h := CFSG.AGLEmbedding.mem_sup_centralizer_of_not_dvd_card_outer Nat.prime_two
      hout.not_two_dvd_nat hN htn
    rwa [hCL, sup_bot_eq] at h
  have hT8 : Nat.card T ≤ 8 := by
    obtain ⟨Q, hQ⟩ := (hT.isPGroup.comap_of_injective L.subtype L.subtype_injective).exists_le_sylow
    have h1 : Nat.card (T.comap L.subtype) ≤ Nat.card (Q : Subgroup ↥L) := card_le_of_le hQ
    have h2 : Nat.card (T.comap L.subtype) = Nat.card T :=
      Nat.card_congr (subgroupOfEquivOfLe hTL).toEquiv
    rw [h2, (hsyl Q).2.1] at h1
    exact h1
  exact commutator_eq_bot_of_card_lt_prime hp hBp hBT (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
