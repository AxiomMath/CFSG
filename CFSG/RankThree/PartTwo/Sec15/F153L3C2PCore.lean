module

public import CFSG.GH74.GLS.Basic
public import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3C2

open CFSG CFSG.GH74.GLS

variable {X : Type*} [Group X]

theorem pPrimeCoreOf_le_self (p : ℕ) (K : Subgroup X) : pPrimeCoreOf p K ≤ K := by
  rintro _ ⟨k, -, rfl⟩
  exact k.2

theorem le_normalizer_pPrimeCoreOf_gen (p : ℕ) (C : Subgroup X) :
    C ≤ Subgroup.normalizer (pPrimeCoreOf p C : Set X) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨o, ho, rfl⟩
    refine ⟨⟨g, hg⟩ * o * ⟨g, hg⟩⁻¹, ?_, rfl⟩
    exact (inferInstance : (pPrimeCore p ↥C).Normal).conj_mem o ho ⟨g, hg⟩
  · rintro ⟨o, ho, hoe⟩
    refine ⟨⟨g, hg⟩⁻¹ * o * ⟨g, hg⟩, ?_, ?_⟩
    · have := (inferInstance : (pPrimeCore p ↥C).Normal).conj_mem o ho ⟨g, hg⟩⁻¹
      simpa using this
    · have : (C.subtype o : X) = g * h * g⁻¹ := hoe
      show (g⁻¹ * (o : X) * g : X) = h
      rw [show (o : X) = g * h * g⁻¹ from this]
      group

theorem coprime_card_pPrimeCoreOf [Finite X] (p : ℕ) (K : Subgroup X) :
    Nat.Coprime p (Nat.card (pPrimeCoreOf p K)) := by
  have e : Nat.card (pPrimeCoreOf p K) = Nat.card (pPrimeCore p ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  rw [e]
  exact coprime_card_pPrimeCore p ↥K

theorem le_pPrimeCoreOf_of_normalized [Finite X] {p : ℕ} {C W : Subgroup X} (hWC : W ≤ C)
    (hnorm : ∀ c ∈ C, ∀ w ∈ W, c * w * c⁻¹ ∈ W) (hcop : Nat.Coprime p (Nat.card W)) :
    W ≤ pPrimeCoreOf p C := by
  have hN : (W.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn⟩
  have hcard : Nat.card (W.subgroupOf C) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv
  have hle : W.subgroupOf C ≤ pPrimeCore p ↥C :=
    le_sSup ⟨hN, by rw [hcard]; exact hcop⟩
  intro w hw
  exact ⟨⟨w, hWC hw⟩, hle (Subgroup.mem_subgroupOf.mpr hw), rfl⟩

end CFSG.RankThree.PartTwo.Sec15.F153L3C2
