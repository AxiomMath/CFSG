module

public import CFSG.Permutation.FiveTransitive.SylowPreimageNormalizer

public section

namespace CFSG

namespace FiveTransitive.InvolutionSylowPreimageNormalizer

variable {H : Type*} [Group H]

private theorem mem_zpowers_iff_of_order_two [Finite H] (t : H) (ht : orderOf t = 2) (y : H) :
    y ∈ Subgroup.zpowers t ↔ y = 1 ∨ y = t := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ht]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, he⟩
    have hn2 : n = 0 ∨ n = 1 := by omega
    rcases hn2 with rfl | rfl
    · exact Or.inl (by simpa only [pow_zero] using he.symm)
    · exact Or.inr (by simpa only [pow_one] using he.symm)
  · rintro (rfl | rfl)
    · exact ⟨0, by omega, pow_zero t⟩
    · exact ⟨1, by omega, pow_one _⟩

theorem normalizer_zpowers_eq_centralizer [Finite H] (t : H) (ht : orderOf t = 2) :
    Subgroup.normalizer (Subgroup.zpowers t : Set H) = Subgroup.centralizer ({t} : Set H) := by
  ext x
  constructor
  · intro hx
    have hc := (Subgroup.mem_normalizer_iff.mp hx t).mp (Subgroup.mem_zpowers t)
    rcases (mem_zpowers_iff_of_order_two t ht _).mp hc with he | he
    · have ht1 : t = 1 := by
        apply (MulAut.conj x).injective
        simpa using he
      simp [ht1] at ht
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have he' := congrArg (fun z : H => z * x) he
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using he'
  · intro hx
    apply Subgroup.centralizer_le_normalizer (Subgroup.zpowers t : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp hx
    exact (hc.zpow_right k).symm.eq

private theorem zpowers_isTwoGroup (t : H) (ht : orderOf t = 2) : IsPGroup 2 (Subgroup.zpowers t) := by
  apply IsPGroup.of_card (n := 1)
  rw [Nat.card_zpowers, ht, pow_one]

variable {G : Type*} [Group G] [Finite G] [Finite H]

theorem normalizer_map_eq_centralizer (f : G →* H) (hf : Function.Surjective f)
    (t : H) (ht : orderOf t = 2) (R : Sylow 2 ((Subgroup.zpowers t).comap f)) :
    (Subgroup.normalizer (SylowPreimageNormalizer.ambient f (Subgroup.zpowers t) R : Set G)).map f =
      Subgroup.centralizer ({t} : Set H) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [SylowPreimageNormalizer.normalizer_map f hf (Subgroup.zpowers t)
    (zpowers_isTwoGroup t ht) R, normalizer_zpowers_eq_centralizer t ht]

end FiveTransitive.InvolutionSylowPreimageNormalizer

end CFSG
