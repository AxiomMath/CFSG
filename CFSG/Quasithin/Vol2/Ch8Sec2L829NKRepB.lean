module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKRepDefs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L829NK

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace CFSG.Quasithin.H.SL3Rep

theorem card_comm_tt : (Finset.univ.filter fun M : Matrix (Fin 3) (Fin 3) (ZMod 2) =>
    CFSG.Quasithin.H.SL3Six.mul3 M (ttSL : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      CFSG.Quasithin.H.SL3Six.mul3 (ttSL : Matrix (Fin 3) (Fin 3) (ZMod 2)) M).card = 32 := by
  decide +kernel

theorem nk_adj_fixed_le {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (f : U ≃ₗ[ZMod 2] traceZeroEnd VS) (r : U →ₗ[ZMod 2] U)
    (hr : ∀ u, ((f (r u) : traceZeroEnd VS) : Module.End (ZMod 2) VS) =
      (ttGS : VS →ₗ[ZMod 2] VS) ∘ₗ ((f u : traceZeroEnd VS) : Module.End (ZMod 2) VS) ∘ₗ
        (ttGS.symm : VS →ₗ[ZMod 2] VS)) :
    Nat.card {u : U // r u = u} ≤ 32 := by
  have httm : LinearMap.toMatrix' (ttGS : VS →ₗ[ZMod 2] VS) =
      (ttSL : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    have : (ttGS : VS →ₗ[ZMod 2] VS) = Matrix.toLin' (ttSL : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
      rfl
    rw [this, LinearMap.toMatrix'_toLin']
  rw [← card_comm_tt, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  refine Nat.card_le_card_of_injective (fun u => ⟨LinearMap.toMatrix'
    ((f u.1 : traceZeroEnd VS) : Module.End (ZMod 2) VS), ?_⟩) ?_
  · have h1 := hr u.1
    rw [u.2] at h1
    have h3 : ((f u.1 : traceZeroEnd VS) : Module.End (ZMod 2) VS) ∘ₗ
        (ttGS : VS →ₗ[ZMod 2] VS) = (ttGS : VS →ₗ[ZMod 2] VS) ∘ₗ
          ((f u.1 : traceZeroEnd VS) : Module.End (ZMod 2) VS) := by
      conv_lhs => rw [h1]
      ext w
      simp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [CFSG.Quasithin.H.SL3Six.mul3_eq, CFSG.Quasithin.H.SL3Six.mul3_eq, ← httm,
      ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp, h3]
  · intro u w hvw
    have h1 := congrArg Subtype.val hvw
    simp only at h1
    exact Subtype.ext (f.injective (Subtype.ext (LinearMap.toMatrix'.injective h1)))

end CFSG.Quasithin.H13.L829NK
