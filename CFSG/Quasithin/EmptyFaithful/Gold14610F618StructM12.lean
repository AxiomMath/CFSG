module

public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructIso
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut

public section

namespace CFSG.Quasithin

open CFSG.ComponentClassification.OuterAutomorphisms

namespace Gold14610

namespace Struct

theorem conjHom_injective_of_center_eq_bot {M : Type} [Group M] (hM : Subgroup.center M = ⊥) :
    Function.Injective (MulAut.conj : M →* MulAut M) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hmem : a ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : a * g * a⁻¹ = g := by
      simpa [MulAut.conj_apply] using congrArg (fun σ : MulAut M => σ g) ha
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  rw [hM] at hmem
  exact Subgroup.mem_bot.mp hmem

variable {D : Type} [Group D]

theorem idx2Data_of_isAutM12
    (h : F6.IsAutM12 D) : Idx2Data D := by
  obtain ⟨e⟩ := h
  have hsimple : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M12 :=
    CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have hinj : Function.Injective (MulAut.conj :
      CFSG.Blueprint.NativeSporadic.M12 →* MulAut CFSG.Blueprint.NativeSporadic.M12) :=
    conjHom_injective_of_center_eq_bot CFSG.ComponentClassification.M12Cover.m12_center
  have eI : CFSG.Blueprint.NativeSporadic.M12 ≃* ↥(inner CFSG.Blueprint.NativeSporadic.M12) :=
    MonoidHom.ofInjective hinj
  have hidx : (inner CFSG.Blueprint.NativeSporadic.M12).index = 2 :=
    CFSG.ComponentClassification.M12Cover.card_outer
  refine Idx2Data.of_mulEquiv e (idx2Data_of_index_two hidx ?_ (Or.inl eI.symm.isSimpleGroup))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨eI.symm⟩))))))

end Struct

end Gold14610

end CFSG.Quasithin
