module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CNat4B
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204QCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace S15223P4

namespace C

namespace Nat4

theorem pCore_sl_four : CFSG.Open.pCore 2 (SLt 4) = ⊥ := by
  have : IsSimpleGroup (SLt 4) := CFSG.QuasithinUnique.Bridge.isSimple_sl_zmod2 4 (by norm_num)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.Open.pCore 2 (SLt 4)) with h | h
  · exact h
  · exfalso
    have h2 : IsPGroup 2 (SLt 4) := by
      intro g
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 :
        IsPGroup 2 ↥(CFSG.Open.pCore 2 (SLt 4))) ⟨g, h ▸ Subgroup.mem_top g⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnt : Nontrivial ↥(Subgroup.center (SLt 4)) := h2.center_nontrivial
    rw [CFSG.QuasithinUnique.Bridge.center_sl_zmod2 4] at hnt
    exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt rfl

theorem nonempty_oTwoQuot_sl_four :
    Nonempty (oTwoQuot (SLt 4) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq pCore_sl_four).trans QuotientGroup.quotientBot).trans
    ((QuotientGroup.quotientMulEquivOfEq (CFSG.QuasithinUnique.Bridge.center_sl_zmod2 4)).trans
      QuotientGroup.quotientBot).symm⟩

end Nat4

namespace CData

theorem isLnTwo_four_kI {G : Type} [Group G] [Finite G] {T Mc M H : Subgroup G}
    {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}
    (d : CData T Mc M H B₀ I X) (hF : ¬ X ≤ Mc) {W : ℕ → Subgroup G}
    (D : FLc.P0Setup X (sOf152 T Mc M B₀) (uLOf1527 (zSOf T Mc M B₀) X) 5 W)
    (hZW : zUOf1528 (zSOf T Mc M B₀) X = W 1) :
    IsLnTwo 4 (OTwoQuot (kI T Mc M B₀)) := by
  obtain ⟨e⟩ := CFSG.Quasithin.N204.nonempty_oTwoQuot_equiv_of_surjective (d.psi hF D hZW)
    (d.psi_surjective hF D hZW) (d.psi_ker_isPGroup hF D hZW)
  obtain ⟨e'⟩ := Nat4.nonempty_oTwoQuot_sl_four
  exact ⟨e.trans e'⟩

end CData

end C

end S15223P4

end CFSG.Quasithin
