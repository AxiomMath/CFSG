module

public import CFSG.Permutation.FiveTransitive.FixedFiveInvolutionGeometry

public section

namespace CFSG

namespace FiveTransitive.ElementaryPairOrientation

open MulAction

theorem invariant_difference
    {G X : Type*} [CommGroup G] [MulAction G X] (a b g : G) :
    ∀ t ∈ fixedBy X b \ fixedBy X a, g • t ∈ fixedBy X b \ fixedBy X a := by
  intro t ht
  refine ⟨FixedFiveInvolutionGeometry.mem_fixedBy_smul_of_commute b g (mul_comm _ _) ht.1, ?_⟩
  intro hf
  apply ht.2
  have hh := FixedFiveInvolutionGeometry.mem_fixedBy_smul_of_commute a g⁻¹ (mul_comm _ _) hf
  simpa only [inv_smul_smul] using hh

private theorem fixes_pair_or_mul
    {G X : Type*} [CommGroup G] [MulAction G X]
    (a c : G) (ha : a * a = 1) (U : Set X) (hU : U.ncard = 2)
    (hafree : ∀ t ∈ U, a • t ≠ t)
    (haU : ∀ t ∈ U, a • t ∈ U) (hcU : ∀ t ∈ U, c • t ∈ U) :
    U ⊆ fixedBy X c ∨ U ⊆ fixedBy X (a * c) := by
  obtain ⟨u, v, huv, hset⟩ := Set.ncard_eq_two.mp hU
  have hu : u ∈ U := by rw [hset]; simp
  have hv : v ∈ U := by rw [hset]; simp
  have hav : a • u = v := by
    have hh := haU u hu
    rw [hset] at hh
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, hafree u hu, false_or] using hh
  have hau : a • v = u := by rw [← hav, ← mul_smul, ha, one_smul]
  have hc := hcU u hu
  rw [hset] at hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  have hext (g : G) (hg : g • u = u) : U ⊆ fixedBy X g := by
    intro t ht
    rw [hset] at ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact hg
    · rw [← hav]
      exact FixedFiveInvolutionGeometry.mem_fixedBy_smul_of_commute g a (mul_comm _ _) hg
  rcases hc with hc | hc
  · exact Or.inl (hext c hc)
  · exact Or.inr (hext (a * c) (by rw [mul_smul, hc, hau]))

theorem orient
    {G X : Type*} [CommGroup G] [Finite X] [MulAction G X]
    (h2 : ∀ g : G, g * g = 1) (a b c : G)
    (hb : (fixedBy X b \ fixedBy X a).ncard = 2)
    (hab : (fixedBy X (a * b) \ fixedBy X a).ncard = 2)
    (hc : (fixedBy X c \ fixedBy X a).ncard = 2)
    (hac : (fixedBy X (a * c) \ fixedBy X a).ncard = 2) :
    ((fixedBy X c \ fixedBy X a = fixedBy X b \ fixedBy X a) ∧
      (fixedBy X (a * c) \ fixedBy X a = fixedBy X (a * b) \ fixedBy X a)) ∨
    ((fixedBy X (a * c) \ fixedBy X a = fixedBy X b \ fixedBy X a) ∧
      (fixedBy X c \ fixedBy X a = fixedBy X (a * b) \ fixedBy X a)) := by
  let F := fixedBy X a
  let U := fixedBy X b \ F
  let V := fixedBy X (a * b) \ F
  have hUn : U.ncard = 2 := hb
  have hdis : Disjoint U V := by
    rw [Set.disjoint_left]
    intro t ht ht'
    apply ht.2
    change a • t = t
    have he := ht'.1
    change (a * b) • t = t at he
    rwa [mul_smul, ht.1] at he
  have hor (g : G) (S : Set X) (hS : S.ncard = 2)
      (hout : S ⊆ Fᶜ) (has : ∀ t ∈ S, a • t ∈ S)
      (hgs : ∀ t ∈ S, g • t ∈ S) :
      S ⊆ fixedBy X g ∨ S ⊆ fixedBy X (a * g) :=
    fixes_pair_or_mul a g (h2 a) S hS (fun t ht => hout ht) has hgs
  have hU := hor c U hb (fun _ ht => ht.2)
    (invariant_difference a b a) (invariant_difference a b c)
  have hV := hor c V hab (fun _ ht => ht.2)
    (invariant_difference a (a * b) a) (invariant_difference a (a * b) c)
  have heq (g : G) (S : Set X) (hS : S.ncard = 2)
      (hout : S ⊆ Fᶜ) (hsub : S ⊆ fixedBy X g)
      (hcard : (fixedBy X g \ F).ncard = 2) : fixedBy X g \ F = S := by
    have hs : S ⊆ fixedBy X g \ F := fun t ht => ⟨hsub ht, hout ht⟩
    apply (Set.eq_of_subset_of_ncard_le hs ?_).symm
    rw [hcard, hS]
  rcases hU with hU | hU
  · have heU := heq c U hb (fun _ ht => ht.2) hU hc
    refine Or.inl ⟨heU, ?_⟩
    rcases hV with hV | hV
    · have heV := heq c V hab (fun _ ht => ht.2) hV hc
      have hUV : U = V := heU.symm.trans heV
      have he : U = ∅ := disjoint_self.mp (by simpa only [← hUV] using hdis)
      have hn : U.ncard = 0 := by rw [he, Set.ncard_empty]
      omega
    · exact heq (a * c) V hab (fun _ ht => ht.2) hV hac
  · have heU := heq (a * c) U hb (fun _ ht => ht.2) hU hac
    refine Or.inr ⟨heU, ?_⟩
    rcases hV with hV | hV
    · exact heq c V hab (fun _ ht => ht.2) hV hc
    · have heV := heq (a * c) V hab (fun _ ht => ht.2) hV hac
      have hUV : U = V := heU.symm.trans heV
      have he : U = ∅ := disjoint_self.mp (by simpa only [← hUV] using hdis)
      have hn : U.ncard = 0 := by rw [he, Set.ncard_empty]
      omega

end FiveTransitive.ElementaryPairOrientation

end CFSG
