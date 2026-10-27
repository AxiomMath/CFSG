module

public import CFSG.Permutation.FiveTransitive.ElementarySemiregularFromPairs
public import CFSG.Permutation.FiveTransitive.ElementaryPairOrientation

public section

namespace CFSG

namespace FiveTransitive.ElementaryOrientedSemiregular

open MulAction

theorem fixed_inter_mul
    {G X : Type*} [CommGroup G] [MulAction G X] (a g : G) :
    fixedBy X (a * g) ∩ fixedBy X a = fixedBy X g ∩ fixedBy X a := by
  ext t
  constructor
  · rintro ⟨hg, ha⟩
    refine ⟨?_, ha⟩
    change (a * g) • t = t at hg
    rwa [mul_comm a g, mul_smul, ha] at hg
  · rintro ⟨hg, ha⟩
    refine ⟨?_, ha⟩
    change (a * g) • t = t
    rw [mul_smul, hg, ha]

private theorem fixed_sdiff_of_four
    {G X : Type*} [CommGroup G] [Finite X] [MulAction G X]
    (hmax : ∀ g : G, g ≠ 1 → (fixedBy X g).ncard ≤ 7)
    (a g : G) (ha : (fixedBy X a).ncard = 7)
    (hloc : (fixedBy X g ∩ fixedBy X a).ncard = 3)
    (W : Set X) (hW : W.ncard = 4) (hsub : W ⊆ fixedBy X g \ fixedBy X a) :
    fixedBy X g \ fixedBy X a = W := by
  have hg : g ≠ 1 := by
    intro he
    have hf : fixedBy X g ∩ fixedBy X a = fixedBy X a := by
      rw [he]; ext t; simp [fixedBy]
    rw [hf, ha] at hloc
    contradiction
  have hsum := Set.ncard_inter_add_ncard_sdiff_eq_ncard (fixedBy X g) (fixedBy X a)
  have hm := hmax g hg
  apply (Set.eq_of_subset_of_ncard_le hsub ?_).symm
  omega

theorem semiregular
    {G X : Type*} [CommGroup G] [Finite X] [MulAction G X]
    (h2 : ∀ g : G, g * g = 1)
    (hmax : ∀ g : G, g ≠ 1 → (fixedBy X g).ncard ≤ 7)
    (a b c d : G) (ha : (fixedBy X a).ncard = 7)
    (hb : (fixedBy X b \ fixedBy X a).ncard = 2)
    (hab : (fixedBy X (a * b) \ fixedBy X a).ncard = 2)
    (hc : fixedBy X c \ fixedBy X a = fixedBy X b \ fixedBy X a)
    (hd : fixedBy X d \ fixedBy X a = fixedBy X b \ fixedBy X a)
    (hac : fixedBy X (a * c) \ fixedBy X a = fixedBy X (a * b) \ fixedBy X a)
    (had : fixedBy X (a * d) \ fixedBy X a = fixedBy X (a * b) \ fixedBy X a)
    (hbc : (fixedBy X (b * c) ∩ fixedBy X a).ncard = 3)
    (hbd : (fixedBy X (b * d) ∩ fixedBy X a).ncard = 3)
    (hcd : (fixedBy X (c * d) ∩ fixedBy X a).ncard = 3) :
    let E := (fixedBy X b \ fixedBy X a) ∪ (fixedBy X (a * b) \ fixedBy X a)
    E.ncard = 4 ∧ ∀ g : G, g ≠ 1 → ∀ t ∉ fixedBy X a ∪ E, g • t ≠ t := by
  let F := fixedBy X a
  let U := fixedBy X b \ F
  let V := fixedBy X (a * b) \ F
  let E := U ∪ V
  let T := F ∪ E
  have hdis : Disjoint U V := by
    rw [Set.disjoint_left]
    intro t ht ht'
    apply ht.2
    have he := ht'.1
    change (a * b) • t = t at he
    rwa [mul_smul, ht.1] at he
  have hE : E.ncard = 4 := by
    change (U ∪ V).ncard = 4
    rw [Set.ncard_union_eq hdis]
    change (fixedBy X b \ fixedBy X a).ncard + (fixedBy X (a * b) \ fixedBy X a).ncard = 4
    rw [hb, hab]
  have hUU (u : G) (hu : fixedBy X u \ F = U) : U ⊆ fixedBy X u := by
    intro t ht
    rw [← hu] at ht
    exact ht.1
  have hVV (u : G) (hu : fixedBy X (a * u) \ F = V) : V ⊆ fixedBy X (a * u) := by
    intro t ht
    rw [← hu] at ht
    exact ht.1
  have hpairs (u v : G) (hu : fixedBy X u \ F = U) (hv : fixedBy X v \ F = U)
      (hau : fixedBy X (a * u) \ F = V) (hav : fixedBy X (a * v) \ F = V)
      (hloc : (fixedBy X (u * v) ∩ F).ncard = 3) : fixedBy X (u * v) \ F = E := by
    apply fixed_sdiff_of_four hmax a (u * v) ha hloc E hE
    intro t ht
    refine ⟨?_, ?_⟩
    · rcases ht with ht | ht
      · change (u * v) • t = t
        rw [mul_smul, hUU v hv ht, hUU u hu ht]
      · have he : (a * u) * (a * v) = u * v := by
          calc
            (a * u) * (a * v) = (a * a) * (u * v) := by ac_rfl
            _ = u * v := by rw [h2, one_mul]
        change (u * v) • t = t
        rw [← he, mul_smul, hVV v hav ht, hVV u hau ht]
    · rcases ht with ht | ht <;> exact ht.2
  have hbcE := hpairs b c rfl hc rfl hac hbc
  have hbdE := hpairs b d rfl hd rfl had hbd
  have hcdE := hpairs c d hc hd hac had hcd
  have hT : ∀ (g : G) (t : X), t ∈ T → g • t ∈ T := by
    intro g t ht
    rcases ht with ht | ht | ht
    · exact Or.inl (FixedFiveInvolutionGeometry.mem_fixedBy_smul_of_commute a g (mul_comm _ _) ht)
    · exact Or.inr (Or.inl (ElementaryPairOrientation.invariant_difference a b g t ht))
    · exact Or.inr (Or.inr (ElementaryPairOrientation.invariant_difference a (a * b) g t ht))
  have hbase (g : G) (he : fixedBy X g \ F = U ∨ fixedBy X g \ F = V ∨ fixedBy X g \ F = E) :
      ∀ t ∉ T, g • t ≠ t := by
    intro t ht hf
    have hout : t ∉ F := fun hh => ht (Or.inl hh)
    have hm : t ∈ fixedBy X g \ F := ⟨hf, hout⟩
    apply ht
    rcases he with he | he | he
    · exact Or.inr (Or.inl (he ▸ hm))
    · exact Or.inr (Or.inr (he ▸ hm))
    · exact Or.inr (he ▸ hm)
  have hmove : ∀ g ∈ ({a, b, c, d, a * b, a * c, a * d, b * c, b * d, c * d} : Set G),
      ∀ t ∉ T, g • t ≠ t := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fun t ht hf => ht (Or.inl hf)
    · exact hbase g (Or.inl rfl)
    · exact hbase g (Or.inl hc)
    · exact hbase g (Or.inl hd)
    · exact hbase _ (Or.inr (Or.inl rfl))
    · exact hbase _ (Or.inr (Or.inl hac))
    · exact hbase _ (Or.inr (Or.inl had))
    · exact hbase _ (Or.inr (Or.inr hbcE))
    · exact hbase _ (Or.inr (Or.inr hbdE))
    · exact hbase _ (Or.inr (Or.inr hcdE))
  have habcF : (fixedBy X (a * b * c) ∩ F).ncard = 3 := by
    rw [mul_assoc, fixed_inter_mul]
    exact hbc
  have habc : a * b * c ≠ 1 := by
    intro he
    have hf : fixedBy X (a * b * c) ∩ F = F := by rw [he]; ext t; simp [fixedBy]
    rw [hf] at habcF
    change (fixedBy X a).ncard = 3 at habcF
    omega
  have hinside : 3 ≤ (fixedBy X (a * b * c) ∩ T).ncard := by
    rw [← habcF]
    exact Set.ncard_le_ncard (fun _ ht => ⟨ht.1, Or.inl ht.2⟩ :
      fixedBy X (a * b * c) ∩ F ⊆ fixedBy X (a * b * c) ∩ T)
  exact ⟨hE, ElementarySemiregularFromPairs.semiregular h2 hmax T hT a b c d hmove habc hinside⟩

end FiveTransitive.ElementaryOrientedSemiregular

end CFSG
