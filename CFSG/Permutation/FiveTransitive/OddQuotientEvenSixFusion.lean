module

public import CFSG.Permutation.FiveTransitive.OddQuotientCosetFusion
public import CFSG.Permutation.FiveTransitive.EvenSixInvolutionConjugacy

public section

namespace CFSG

namespace FiveTransitive.OddQuotientEvenSixFusion

open Equiv

theorem exists_conjugator_mod_subgroup
    (G X : Type*) [Group G] [Finite G] [Fintype X] [DecidableEq X]
    (f : G →* Perm X) (hX : Fintype.card X = 6) (hf : f.range = alternatingGroup X)
    (Q : Subgroup G) [Q.Normal] (hQ : Q ≤ f.ker)
    (hodd : Odd (Nat.card (f.ker.map (QuotientGroup.mk' Q))))
    (a b : G) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hfa : f a ≠ 1) (hfb : f b ≠ 1) :
    ∃ c : G, (c * a * c⁻¹) * b⁻¹ ∈ Q := by
  have heven (g : G) : (f g).sign = 1 := by
    apply Perm.mem_alternatingGroup.mp
    rw [← hf]
    exact ⟨g, rfl⟩
  obtain ⟨d, hd, hdeq⟩ := EvenSixInvolutionConjugacy.exists_even_conjugator hX
    (f a) (f b) (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one])
    (heven a) (heven b) hfa hfb
  have hdmem : d ∈ f.range := by rw [hf]; exact Perm.mem_alternatingGroup.mpr hd
  obtain ⟨g, hg⟩ := hdmem
  have heq : f (g * a * g⁻¹) = f b := by rw [map_mul, map_mul, map_inv, hg]; exact hdeq
  have hpow : (g * a * g⁻¹) ^ 2 = 1 := by rw [conj_pow, ha]; group
  obtain ⟨k, _, hk⟩ := OddQuotientCosetFusion.exists_ker_conjugator_mod_subgroup f Q hQ hodd
    (g * a * g⁻¹) b hpow hb heq hfb
  refine ⟨k * g, ?_⟩
  have heq' : ((k * g) * a * (k * g)⁻¹) * b⁻¹ = (k * (g * a * g⁻¹) * k⁻¹) * b⁻¹ := by group
  rw [heq']
  exact hk

end FiveTransitive.OddQuotientEvenSixFusion

end CFSG
