module

public import CFSG.LocalAnalysis.StandardType.GGNineDepRowLin
public import CFSG.LocalAnalysis.StandardType.GGNineDepRowImprim
public import CFSG.LocalAnalysis.StandardType.GGNineDepRowSym
public import CFSG.LocalAnalysis.StandardType.GGNineDepRowExc
public import CFSG.LocalAnalysis.StandardType.GGNineDepRowOrth
public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGNineDepFixLineLin : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] (h : Fin (9 - 1) → V)
    (α : Fin (9 - 1) → Module.Dual (ZMod 3) V) (r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V)) (T : Type)
    (s : T → (V ≃ₗ[ZMod 3] V)) (x : V), GGNineLinHyp 3 9 h α r s x →
    ¬ LinearIndependent (ZMod 3) h →
    Nat.card ↥(ggLargeGrp r s ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) x) ≤
      12 * Nat.card ↥(Subgroup.closure (Set.range s)) →
    (∃ M : CoxeterMatrix (Fin (9 - 1)), GGIsWeylMatrix M ∧
      Nonempty (M.Group ≃* ↥(Subgroup.closure (Set.range s)))) →
    Module.finrank (ZMod 3) ↥(ggLinFix (Set.range r)) ≤ 1

theorem ggNineDepFixLineLin_of_omega (hK : GGReflClassOmegaInput) (hK2 : GGNineDepRowLinInput)
    (hK3 : GGNineDepRowImprimInput) (hK4a : GGNineDepRowSymSuccInput)
    (hK4b : GGNineDepRowSymSuccTwoInput) (hK5a : GGNineDepRowE7Input)
    (hK5b : GGNineDepRowE8Input) (hK6 : GGNineDepRowOrthInput) : GGNineDepFixLineLin := by
  intro V _ _ h α r T s x hlin hdep hstab hweyl
  by_contra hcon
  have htwo : 2 ≤ Module.finrank (ZMod 3) ↥(ggLinFix (Set.range r)) := by omega
  have C : GGNineDepCase 3 9 h α r s x := ⟨hlin, hdep, hstab.trans_eq (by norm_num), htwo, hweyl⟩
  have X : GGNineDepCtx h α r s x := ggNineDepCtx_of_case C
  haveI : Finite T := hlin.finT
  haveI : Module.Finite (ZMod 3) V := ggFixLine_finite s hlin.s_refl hlin.fix_s
  have hirr : ZS.AbsIrred 3 (ggNineQ X) := X.restr.2.1
  have hgen : ggNineQ X = Subgroup.closure {q | q ∈ ggNineQ X ∧ GGLinRefl q} := X.restr.2.2
  have hd7 := X.d_ge
  have hd9 := X.d_le
  by_cases h9 : 9 ≤ Module.finrank (ZMod 3) ↥(ggFixLineT r s)
  · rcases hK.1 3 (by norm_num) ↥(ggFixLineT r s) _ rfl h9 (ggNineQ X) hirr hgen with
      h1 | h2 | h3 | h4 | h5
    · exact hK3 V h α r T s x X h1
    · exact hK2 V h α r T s x X h2
    · exact hK6 V h α r T s x X h3
    · exact hK4a V h α r T s x X h4
    · exact hK4b V h α r T s x X h5
  · rcases hK.2 ↥(ggFixLineT r s) _ rfl (by omega) (by omega) (ggNineQ X) hirr hgen with
      h1 | h2 | h3 | h4 | h5 | h6 | h7
    · exact hK3 V h α r T s x X h1
    · exact hK2 V h α r T s x X h2
    · exact hK6 V h α r T s x X h3
    · exact hK4a V h α r T s x X h4
    · exact hK4b V h α r T s x X h5
    · exact hK5a V h α r T s x X h6
    · exact hK5b V h α r T s x X h7

end CFSG.StandardType

end
