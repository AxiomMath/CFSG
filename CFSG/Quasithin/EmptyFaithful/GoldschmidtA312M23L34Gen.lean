module

public import CFSG.LieType.Multipliers.L34Model
public import CFSG.LieType.Multipliers.CoverBounds
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Sporadic.Mathieu.Simple

public section

namespace CFSG.Quasithin.A312M23

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.Quasithin
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

theorem nonempty_mulEquiv_of_isPresentation {X Y : Type*} [Group X] [Group Y] {ι : Type*}
    {g : ι → X} {h : ι → Y} {R : Set (FreeGroup ι)} (hg : IsPresentation g R)
    (hh : IsPresentation h R) : Nonempty (X ≃* Y) :=
  ⟨(QuotientGroup.quotientKerEquivOfSurjective (FreeGroup.lift g) hg.lift_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (hg.ker_lift.trans hh.ker_lift.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (FreeGroup.lift h) hh.lift_surjective))⟩

theorem isPSL_three_four_of_mulEquiv {X : Type} [Group X] (ψ : PSL3 ≃* X) : IsPSL 3 2 2 X := by
  refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, CFSG.Fischer.F4,
    inferInstance, inferInstance, ?_, ⟨ψ.symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 CFSG.Fischer.F4)⟩⟩
  rw [Nat.card_eq_fintype_card, CFSG.Fischer.F4.card]
  norm_num

theorem isPSL_three_four_of_gens {Γ : Type} [Group Γ]
    {N : Subgroup Γ} {u v : Γ} (hu : u ∈ N) (hv : v ∈ N) (hgen : N = Subgroup.closure {u, v})
    (hrel : ∀ w ∈ rels.map (List.map fun l => (l.1.val, l.2)), wordProd (img2 u v) w = 1)
    (hcard : 20160 ≤ Nat.card N) : IsPSL 3 2 2 ↥N := by
  have hgen' : Subgroup.closure ({⟨u, hu⟩, ⟨v, hv⟩} : Set ↥N) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top hgen hu hv
  have hrel' : ∀ w ∈ rels.map (List.map fun l => (l.1.val, l.2)),
      wordProd (img2 (⟨u, hu⟩ : ↥N) ⟨v, hv⟩) w = 1 := fun w hw => by
    apply Subtype.ext
    have h1 := coe_wordProd (K := N) (img2 (⟨u, hu⟩ : ↥N) ⟨v, hv⟩) w
    have h2 : (fun i => ((img2 (⟨u, hu⟩ : ↥N) ⟨v, hv⟩ i : ↥N) : Γ)) = img2 u v := by
      funext i
      unfold img2
      split_ifs <;> rfl
    rw [h1, h2]
    exact hrel w hw
  have hP : IsPresentation (fun i : Fin 2 => img2 (⟨u, hu⟩ : ↥N) ⟨v, hv⟩ i.val) (wordSet rels) :=
    IsPresentation.of_wordProd_of_card hgen' hrel' cyclic_card_le hcard
  obtain ⟨ψ⟩ := nonempty_mulEquiv_of_isPresentation isPresentation_genX hP
  exact isPSL_three_four_of_mulEquiv ψ

end CFSG.Quasithin.A312M23
