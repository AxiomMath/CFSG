module

public import CFSG.Permutation.FiveTransitive.FixedFiveInvolutionGeometry
public import CFSG.Permutation.FiveTransitive.OddStableInvolution

public section

namespace CFSG

namespace FiveTransitive.OyamaFiveFirstPair

open MulAction FixedFiveInvolutionGeometry

theorem enumerate_fixed_five
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (a b : G) (hb : b * b = 1) (hab : a * b = b * a)
    (hFa : (fixedBy X a).ncard = 5) (hFb : (fixedBy X b).ncard ≤ 5)
    (s : Set X) (hs : s.ncard = 4) (hdisj : Disjoint s (fixedBy X a))
    (hbs : s ⊆ fixedBy X b) :
    ∃ e : Fin 5 ↪ X, Set.range e = fixedBy X a ∧
      fixedBy X b = insert (e 0) s ∧
      b • e 0 = e 0 ∧ b • e 1 = e 2 ∧ b • e 2 = e 1 ∧
      b • e 3 = e 4 ∧ b • e 4 = e 3 := by
  have hstable : ∀ x ∈ fixedBy X a, b • x ∈ fixedBy X a := by
    intro x hx
    exact mem_fixedBy_smul_of_commute a b hab hx
  obtain ⟨u, hu, hbu⟩ := OddStableInvolution.exists_fixed b hb (fixedBy X a)
    (by rw [hFa]; decide) hstable
  have hus : u ∉ s := fun h => (Set.disjoint_left.mp hdisj) h hu
  have hfixb : fixedBy X b = insert u s := by
    apply fixedBy_eq_of_five b hFb
    · rw [Set.ncard_insert_of_notMem hus, hs]
    · intro x hx
      rcases hx with rfl | hx
      · exact hbu
      · exact hbs hx
  have huniq : ∀ x ∈ fixedBy X a, b • x = x → x = u := by
    intro x hxa hxb
    have hx : x ∈ fixedBy X b := hxb
    rw [hfixb] at hx
    rcases hx with hx | hx
    · exact hx
    · exact ((Set.disjoint_left.mp hdisj) hx hxa).elim
  obtain ⟨e, he, he0, hb0, hb12, hb21, hb34, hb43⟩ :=
    OddStableInvolution.enumerate_five b hb (fixedBy X a) hFa hstable u hu hbu huniq
  exact ⟨e, he, by rwa [he0], hb0, hb12, hb21, hb34, hb43⟩

end FiveTransitive.OyamaFiveFirstPair

end CFSG
