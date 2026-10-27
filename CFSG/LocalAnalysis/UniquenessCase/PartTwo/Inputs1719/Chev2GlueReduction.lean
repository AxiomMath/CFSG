module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

theorem le_normalizer_inf_of_permutes {Y : Type} [Group Y] [Finite Y] {Kb Eb Tb : Subgroup Y}
    {r : ℕ} (hKn : Kb.Normal) (hTb : IsPGroup 2 Tb) (hr : r.Prime) (hr2 : r ≠ 2)
    (hcard : Nat.card Eb = r) (hEK : Eb ⊓ Kb = ⊥) (hperm : Permutes Eb Tb) :
    Eb ≤ normalizer ((Tb ⊓ Kb : Subgroup Y) : Set Y) := by
  have hcop2 : ∀ k : ℕ, Nat.Coprime r (2 ^ k) := fun k =>
    ((Nat.coprime_primes hr Nat.prime_two).2 hr2).pow_right k
  have key : ∀ e ∈ Eb, ∀ u ∈ Tb ⊓ Kb, e * u * e⁻¹ ∈ Tb ⊓ Kb := by
    intro e he u hu
    have hmem : u * e⁻¹ ∈ (Tb : Set Y) * (Eb : Set Y) := Set.mul_mem_mul hu.1 (Eb.inv_mem he)
    rw [← hperm] at hmem
    obtain ⟨e₁, he₁, t₁, ht₁, h1⟩ := hmem
    have hK : e * u * e⁻¹ ∈ Kb := hKn.conj_mem u hu.2 e
    have heq : e * u * e⁻¹ = (e * e₁) * t₁ := by
      rw [mul_assoc, ← h1, mul_assoc]
    have he₂E : e * e₁ ∈ Eb := Eb.mul_mem he he₁
    have he₂ : e * e₁ ∈ Kb := by
      let π := QuotientGroup.mk' Kb
      have hπ : π (e * e₁) = (π t₁)⁻¹ := by
        have h0 : π ((e * e₁) * t₁) = 1 := by
          rw [← heq]
          exact (QuotientGroup.eq_one_iff _).2 hK
        rw [map_mul] at h0
        exact eq_inv_of_mul_eq_one_left h0
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hTb) ⟨t₁, ht₁⟩
      have hd1 : orderOf (π (e * e₁)) ∣ r :=
        (orderOf_map_dvd π _).trans (hcard ▸ Subgroup.orderOf_dvd_natCard Eb he₂E)
      have hd2 : orderOf (π (e * e₁)) ∣ 2 ^ k := by
        rw [hπ, orderOf_inv]
        refine (orderOf_map_dvd π t₁).trans ?_
        rw [← Subgroup.orderOf_mk t₁ ht₁, hk]
      have h1' : orderOf (π (e * e₁)) = 1 :=
        Nat.eq_one_of_dvd_one ((Nat.dvd_gcd hd1 hd2).trans (hcop2 k).gcd_eq_one.dvd)
      exact (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.mp h1')
    have he₂1 : e * e₁ = 1 := by
      have : e * e₁ ∈ Eb ⊓ Kb := ⟨he₂E, he₂⟩
      rw [hEK] at this
      exact this
    rw [heq, he₂1, one_mul]
    rw [heq, he₂1, one_mul] at hK
    exact ⟨ht₁, hK⟩
  intro e he
  rw [mem_normalizer_iff]
  intro u
  refine ⟨fun hu => key e he u hu, fun hu => ?_⟩
  have := key e⁻¹ (Eb.inv_mem he) _ hu
  simpa [mul_assoc] using this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
