module

public import CFSG.RankThree.PartTwo.Sec5.Item57
public import CFSG.RankThree.PartTwo.Sec5.Item58

public section

namespace CFSG.RankThree.PartTwo.Sec5

open CFSG

universe u

variable {G : Type u} [Group G] [Finite G]

theorem rank3II_5_1 {A S : Subgroup G} (h : SectionFiveHyp A S) :
    Statement51 A S := by
  induction hn : Nat.card S using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  have ih' : ∀ S' : Subgroup G, S' < S → SectionFiveHyp A S' → Statement51 A S' :=
    fun S' hS' h' => ih (Nat.card S') (hn ▸ Subgroup.card_lt_of_lt hS') h' rfl
  rcases rank3II_5_6_of_ih h ih' with h2 | ⟨U, hU⟩
  · exact Or.inr h2
  · left
    have h58 := rank3II_5_8 h hU
    obtain ⟨hSA, hΩ⟩ := rank3II_5_7 h hU h58
    have hAS : A ⊓ Subgroup.centralizer (S : Set G) = A ⊓ Subgroup.centralizer (U : Set G) := by
      apply le_antisymm
      · exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hU.le))
      · refine le_inf inf_le_left ?_
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact h58
    refine ⟨by rw [hAS]; exact card_inf_centralizer_fourGroup h hU, hSA, ?_, ?_⟩
    · rw [hΩ]
      exact hU.elemAbelian
    · rw [hΩ]
      exact hU.card_eq

theorem rank3II_5_6 {A S : Subgroup G} (h : SectionFiveHyp A S) :
    (∀ W : Subgroup G, W ≤ S → A ≤ Subgroup.normalizer (W : Set G) → IsMulCommutative W →
      IsCyclic W) ∨ ∃ U : Subgroup G, IsNormalFourGroup A S U :=
  rank3II_5_6_of_ih h fun _ _ h' => rank3II_5_1 h'

omit [Finite G] in
theorem isSymplecticType_of_forall_isCyclic {A S : Subgroup G}
    (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (h2 : ∀ W : Subgroup G, W ≤ S → A ≤ Subgroup.normalizer (W : Set G) →
      IsMulCommutative W → IsCyclic W) : IsSymplecticType S := by
  intro W hchar hW
  have hAW' : A ≤ Subgroup.normalizer ((W.map S.subtype : Subgroup G) : Set G) := by
    intro g hg
    set φ := S.normalizerMonoidHom ⟨g, hAS hg⟩
    have hφ : W.map φ.toMonoidHom = W := Subgroup.characteristic_iff_map_eq.mp hchar φ
    have hφs : W.map φ.symm.toMonoidHom = W := Subgroup.characteristic_iff_map_eq.mp hchar _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hmem : φ y ∈ W := hφ ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hy
      exact ⟨φ y, hmem, rfl⟩
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hxS : x ∈ S := (Subgroup.mem_normalizer_iff.mp (hAS hg) x).mpr (hyx ▸ y.2)
      have hmem : φ.symm y ∈ W := hφs ▸ Subgroup.mem_map_of_mem φ.symm.toMonoidHom hy
      refine ⟨φ.symm y, hmem, ?_⟩
      have hφx : φ ⟨x, hxS⟩ = y := Subtype.ext hyx.symm
      rw [← hφx, MulEquiv.symm_apply_apply]
      rfl
  have hW'c : IsMulCommutative (W.map S.subtype) := ⟨⟨fun x y => by
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    change (x : G) * y = y * x
    rw [← hux, ← hvy]
    have := congrArg (fun w : W => ((w : S) : G)) (hW.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    simpa using this⟩⟩
  have := h2 _ (Subgroup.map_subtype_le W) hAW' hW'c
  exact isCyclic_of_surjective (W.equivMapOfInjective S.subtype S.subtype_injective).symm
    (W.equivMapOfInjective S.subtype S.subtype_injective).symm.surjective

end CFSG.RankThree.PartTwo.Sec5
