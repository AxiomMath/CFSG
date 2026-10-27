module

public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.Native.ONTripleSylow
public import CFSG.RankThree.PartTwo.Late.Defs
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.ProjLine

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.ONTriple416

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Subgroup
open CFSG.RankThree.Native.ONTriple
open CFSG.RankThree.PartOne.Torsion37 (isExtraspecialPGroup_of_mulEquiv center_map_mulEquiv)
open scoped Pointwise

section Embedding

variable {H : Type} [Group H] {G : Subgroup H}

abbrev ι (ψ : G ≃* GM) : GM →* H := G.subtype.comp ψ.symm.toMonoidHom

theorem ι_injective (ψ : G ≃* GM) : Function.Injective (ι ψ) :=
  Subtype.val_injective.comp ψ.symm.injective

theorem ι_apply (ψ : G ≃* GM) (g : GM) : ι ψ g = ((ψ.symm g : G) : H) := rfl

theorem ι_psi (ψ : G ≃* GM) (x : G) : ι ψ (ψ x) = x := by
  rw [ι_apply, MulEquiv.symm_apply_apply]

theorem range_ι (ψ : G ≃* GM) : (ι ψ).range = G := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (ψ.symm y).2
  · intro hx
    exact ⟨ψ ⟨x, hx⟩, ι_psi ψ ⟨x, hx⟩⟩

theorem map_comap_ι (ψ : G ≃* GM) {X : Subgroup H} (hX : X ≤ G) :
    (X.comap (ι ψ)).map (ι ψ) = X := by
  rw [map_comap_eq, range_ι, inf_eq_right.2 hX]

theorem card_comap_ι (ψ : G ≃* GM) {X : Subgroup H} (hX : X ≤ G) :
    Nat.card (X.comap (ι ψ)) = Nat.card X := by
  conv_rhs => rw [← map_comap_ι ψ hX]
  rw [card_map_of_injective (ι_injective ψ)]

theorem isE27_comap (ψ : G ≃* GM) {A : Subgroup H} (hAG : A ≤ G) (hA : Late.IsE27 A) :
    Late.IsE27 (A.comap (ι ψ)) := by
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, by rw [card_comap_ι ψ hAG, hA.2]⟩
  · apply Subtype.ext
    apply ι_injective ψ
    have := congrArg Subtype.val (hA.1.1.is_comm.comm ⟨ι ψ x, x.2⟩ ⟨ι ψ y, y.2⟩)
    simpa [map_mul] using this
  · apply ι_injective ψ
    rw [map_pow, map_one]
    exact hA.1.2 _ hx

end Embedding

end CFSG.RankThree.PartTwo.Sec4.Sporadic.ONTriple416

