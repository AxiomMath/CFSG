module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

theorem ggExists_weylElt_of_mem_ggAutomizer {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer X Bs) (hr2 : r * r = 1) :
    ∃ n ∈ ggRankOneIn X Bs r, n ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹ := by
  obtain ⟨n₁, hn₁X, hn₁N, hn₁⟩ := mem_ggAutomizer_iff.mp hr
  obtain ⟨a, m, _hm_odd, ho⟩ :=
    Nat.exists_eq_two_pow_mul_odd (ne_of_gt (orderOf_pos n₁))
  have ha_eq : ggConjAut Bs hn₁N = r := by
    ext b
    rw [ggConjAut_apply Bs hn₁N b, hn₁ b]
  have hact : ∀ (j : ℕ) (b : ↥Bs),
      (((r ^ j) b : ↥Bs) : G) = n₁ ^ j * b * (n₁ ^ j)⁻¹ := by
    intro j b
    rw [← ha_eq]
    exact ggConjAut_pow_apply Bs hn₁N j b
  have hrpow : r ^ m = r := by
    obtain ⟨c, rfl⟩ := _hm_odd
    show r ^ (2 * c + 1) = r
    rw [pow_succ, pow_mul, pow_two, hr2, one_pow, one_mul]
  have hactm : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n₁ ^ m * b * (n₁ ^ m)⁻¹ := by
    intro b
    have h := hact m b
    rwa [hrpow] at h
  have hpow : (n₁ ^ m) ^ (2 ^ a) = 1 := by
    rw [← pow_mul, Nat.mul_comm m (2 ^ a), ← ho]
    exact pow_orderOf_eq_one n₁
  have hnorm : n₁ ^ m ∈ Subgroup.normalizer (Bs : Set G) :=
    pow_mem hn₁N m
  have hcent : n₁ ^ m ∈ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [ggHyperplane] at hh
    obtain ⟨b, hb, hbh⟩ := Subgroup.mem_map.mp hh
    rw [← hbh]
    have hrb : r b = b := hb
    have hb_eq : ((b : ↥Bs) : G) = n₁ ^ m * ((b : ↥Bs) : G) * (n₁ ^ m)⁻¹ := by
      have h := hactm b
      rwa [hrb] at h
    have hb_comm : ((b : ↥Bs) : G) * n₁ ^ m = n₁ ^ m * ((b : ↥Bs) : G) := by
      conv_lhs => rw [hb_eq]
      group
    exact hb_comm
  refine ⟨n₁ ^ m, ?_, hnorm, hactm⟩
  rw [ggRankOneIn, ggOTwoPrime]
  exact Subgroup.subset_closure
    ⟨⟨pow_mem hn₁X m, hcent⟩, a, hpow⟩

end CFSG.StandardType

end
