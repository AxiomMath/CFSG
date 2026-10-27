module

public import CFSG.Quasithin.Background.G9GolayTransport
public import CFSG.Quasithin.Background.SmithB45MatIndM24
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Bridge
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Toolkit

public section

namespace CFSG.Quasithin.G11

open CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

theorem mathieu24_golay_realization
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {H : Subgroup (GLV V)} (irreducible : IsIrr H ⊤)
    (marking : Nonempty (↥H ≃* ↥CFSG.Blueprint.NativeSporadic.M24))
    (dimension : Module.finrank (ZMod 2) V = 11) : IsMathieu24CodeOrCocode H := by
  obtain ⟨m₀⟩ := marking
  have hsrc := mem_sourceGolayCode_iff_permAct_golayRelabel_mem_C
  have hcard : Nat.card (Multiplicative V) ≤ 2 ^ 36 := by
    rw [natCard_multiplicative]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hΓ : ∀ g : Equiv.Perm (Fin 24), g ∈ CFSG.Monster.Code.AutPerm ↔
      ((∀ w : GolayAmbient, w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
          permAct (golayRelabel⁻¹ * g * golayRelabel) w ∈
            CFSG.Blueprint.EvenSource.sourceGolayCode) ∧
        (false = true → (golayRelabel⁻¹ * g * golayRelabel) 0 = 0 ∧
          (golayRelabel⁻¹ * g * golayRelabel) 1 = 1)) := by
    intro g
    rw [mem_AutPerm_iff_conj_preserves_source hsrc g]
    simp
  have hΓcard : Nat.card ↥CFSG.Monster.Code.AutPerm ≤
      Nat.card ↥CFSG.Blueprint.NativeSporadic.M24 := by
    rw [CFSG.Monster.Code.card_AutPerm, CFSG.Sporadic.Mathieu.card_M24]
  rcases mathieuSmallIrr24_holds (Multiplicative V) mul_self_eq_one_multiplicative (toMulSub H)
      ⟨(toMulSubEquiv H).symm.trans m₀⟩ (isIrrOn_toMulSub irreducible).2 hcard with h | h
  · exact Or.inl (isGolaySectionModule_of_realizes m₀ false golayRelabel hΓ
      (golayCorr_source hsrc) (golayCorr_constantLine _) h hΓcard)
  · exact Or.inr (isGolaySectionModule_of_realizes m₀ false golayRelabel hΓ
      (golayCorr_permCore _) (golayCorr_source hsrc) h hΓcard)

end CFSG.Quasithin.G11
