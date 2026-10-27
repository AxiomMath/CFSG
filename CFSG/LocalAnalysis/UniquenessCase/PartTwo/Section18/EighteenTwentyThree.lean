module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsC
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.WeakClosure81.Eleven
public import CFSG.LocalAnalysis.WeakClosure81.W19Min
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnPre

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeven
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def lineCoords {W : Type*} [Group W] {F : Type} [Field F]
    (ψ : W ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) : Subgroup W :=
  (Submodule.span F {w}).toAddSubgroup.toSubgroup.map ψ.symm.toMonoidHom

@[expose] noncomputable def lineTil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    {F : Type} [Field F]
    (ψ : ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≃*
      Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) : Subgroup G :=
  preTil V₀ V hV ((lineCoords ψ w).map (⊤ : Subgroup (Vtil V₀ V hV)).subtype)

theorem lineTil_ne_bot (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    {F : Type} [Field F]
    (ψ : ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≃*
      Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    {w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F} (hw : w ≠ 0) :
    lineTil V₀ V hV ψ w ≠ ⊥ := by
  intro hbot
  have hq : (ψ.symm (Multiplicative.ofAdd w) : ↥(⊤ : Subgroup (Vtil V₀ V hV))) ∈
      lineCoords ψ w := by
    refine Subgroup.mem_map.mpr ⟨Multiplicative.ofAdd w, ?_, rfl⟩
    have hwspan : w ∈ Submodule.span F ({w} : Set (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)) :=
      Submodule.subset_span (Set.mem_singleton w)
    simpa using hwspan
  have hqne : ((ψ.symm (Multiplicative.ofAdd w) : ↥(⊤ : Subgroup (Vtil V₀ V hV))) :
      Vtil V₀ V hV) ≠ 1 := by
    intro h1
    have h2 : Multiplicative.ofAdd w =
        (1 : Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)) := by
      calc Multiplicative.ofAdd w = ψ (ψ.symm (Multiplicative.ofAdd w)) :=
            (ψ.apply_symm_apply _).symm
        _ = ψ 1 := by
          rw [show (ψ.symm (Multiplicative.ofAdd w) :
            ↥(⊤ : Subgroup (Vtil V₀ V hV))) = 1 from Subtype.ext h1]
        _ = 1 := map_one ψ
    exact hw (by simpa using congrArg Multiplicative.toAdd h2)
  have hSne : (lineCoords ψ w).map (⊤ : Subgroup (Vtil V₀ V hV)).subtype ≠ ⊥ := by
    intro hSbot
    have hmem : ((ψ.symm (Multiplicative.ofAdd w) : ↥(⊤ : Subgroup (Vtil V₀ V hV))) :
        Vtil V₀ V hV) ∈ (lineCoords ψ w).map (⊤ : Subgroup (Vtil V₀ V hV)).subtype :=
      Subgroup.mem_map.mpr ⟨_, hq, rfl⟩
    rw [hSbot] at hmem
    exact hqne (Subgroup.mem_bot.mp hmem)
  apply hSne
  have hbot' : preTil V₀ V hV ((lineCoords ψ w).map
      (⊤ : Subgroup (Vtil V₀ V hV)).subtype) = ⊥ := hbot
  rw [← imgTil_preTil V₀ V hV ((lineCoords ψ w).map (⊤ : Subgroup (Vtil V₀ V hV)).subtype),
    hbot', TwelveSeventeen.imgTil_bot]

@[expose] def SingularLine_18_23 (D : Data G) (V₀ V : Subgroup G) (p : ℕ)
    (L : Subgroup G) (h : Hyp18 D V₀ V p L) : Prop :=
  P18_13_2 D V₀ V p L h 1 →
    let H := barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)
    ∀ (n : ℕ), IsOmegaMinus ↥H 6 n → IsU4 ↥H n → V₀ = ⊥ →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (b c : F),
        Nat.card F = 2 ^ n ∧ (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
          ∃ (ε : ↥H ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
            (ψ : ↥(⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) ≃*
              Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
            NatCoordsOmegaMinusOn H ⊤ (fun _ _ _ _ => trivial) F b c ε ψ ∧
              ∃ w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
                w ≠ 0 ∧ StatedQuadMinus 3 F b c w = 0 ∧
                  lineTil V₀ V h.hyp125.isElemAbelian ψ w ≤
                    V ⊓ centralizer ((F12.Wi 2 D.T V : Subgroup G) : Set G)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
