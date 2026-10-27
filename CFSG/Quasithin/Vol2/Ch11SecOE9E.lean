module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.Quasithin.Background.A1bGroups

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X7a
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj projUnipotent)
open CFSG.QuasithinUnique.Vol2Native.A312L (blkN blkN_surjective blkN_ker_isPGroup)

namespace Sp4

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_perfectCore {T P : Subgroup G}
    (h : T ≤ Subgroup.normalizer (P : Set G)) :
    T ≤ Subgroup.normalizer (perfectCore P : Set G) := by
  intro t ht
  rw [← A1b.conjSub_eq_iff_mem_normalizer, A1b.conjSub, map_perfectCore,
    ← A1b.conjSub, A1b.conjSub_eq_iff_mem_normalizer.mpr (h ht)]

omit [Finite G] in
theorem isPGroup_ker_comp {A B C : Type*} [Group A] [Group B] [Group C] (f : B →* C)
    (e : A ≃* B) (h : IsPGroup 2 f.ker) : IsPGroup 2 (f.comp e.toMonoidHom).ker := by
  intro x
  obtain ⟨k, hk⟩ := h ⟨e x.1, x.2⟩
  have h1 : (e x.1) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, Subtype.ext (e.injective ?_)⟩
  rw [Subgroup.coe_pow, map_pow, h1, OneMemClass.coe_one, map_one]

theorem exists_finset_card_four' {K : Type} [Finite K] (h : 4 ≤ Nat.card K) :
    ∃ s : Finset K, s.card = 4 := by
  have := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h)
  exact ⟨s, hs⟩

end Sp4

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
