module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneBlocks
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal
open CFSG.Open (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (lam)

variable {G : Type} [Group G]

theorem GGSecFiveBPermSpPlaneFrame.longBlock_sl2Diag_eq_coordinate [Finite G]
    {p n r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) F →* G} {χ : Multiplicative (ZMod p) →* Fˣ}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs L eta π κ
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.sl2Diag.comp χ))
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p (π 0))
    (i : Fin (r + 1)) (b : ↥Bs) (hb1 : b ≠ 1) (hoff : ∀ k, k ≠ π i.succ → eta b k = 1) :
    orderOf (χ (eta b (π i.succ))) = p ∧
      κ (longBlock F (r + 1) i
        (CFSG.LocalAnalysis.ComponentInitial.sl2Diag F (χ (eta b (π i.succ))))) = (b : G) := by
  obtain ⟨-, hBsEA, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  set c := eta b (π i.succ) with hc
  have hc1 : c ≠ 1 := by
    intro h1
    apply hb1
    have hb : eta b = 1 := funext fun k =>
      if hk : k = π i.succ then hk ▸ h1 else hoff k hk
    exact eta.injective (hb.trans (map_one eta).symm)
  have hcp : c ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hχ : Function.Injective χ := fun a a' h =>
    hκ.2.2.1 (show (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.sl2Diag.comp χ) a =
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.sl2Diag.comp χ) a' by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h])
  refine ⟨(orderOf_injective χ hχ c).trans (orderOf_eq_prime hcp hc1), ?_⟩
  have hv := hκ.spPlaneTorus_eq_coordinate hp2 hF hBsEA hcfg.2.1.2.2.2 hxBs hx1 hLx hN hA
    (Pi.mulSingle i c)
  have hcoord : (Fin.cases 1 (Pi.mulSingle i c) : Fin (r + 2) → Multiplicative (ZMod p)) ∘ π.symm =
      eta b := by
    funext k
    obtain ⟨j, rfl⟩ := π.surjective k
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨m, rfl⟩
    · rw [Fin.cases_zero]
      exact (hoff _ fun h => Fin.succ_ne_zero i (π.injective h).symm).symm
    · rw [Fin.cases_succ]
      by_cases hm : m = i
      · subst hm
        rw [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hm]
        exact (hoff _ fun h => hm (Fin.succ_injective _ (π.injective h))).symm
  rw [hcoord, MulEquiv.symm_apply_apply, SpJoin.spPlaneTorus_mulSingle] at hv
  have hlam : lam i ((CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.sl2Diag.comp χ) c) =
      longBlock F (r + 1) i (CFSG.LocalAnalysis.ComponentInitial.sl2Diag F (χ c)) := by
    apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    rfl
  rw [← hlam]
  exact hv

theorem GGSecFiveBPermSpPlaneFrame.sl2Diag_eq_coordinate_of_axis [Finite G]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {π : Fin 4 ≃ Fin 4}
    {κ : StatedSp 3 F →* G} {χ : Multiplicative (ZMod p) →* Fˣ}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs L eta π κ
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.sl2Diag.comp χ))
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p (π 0))
    (i : Fin 3) (b : ↥Bs) (hb1 : b ≠ 1) (hoff : ∀ k, k ≠ π i.succ → eta b k = 1) :
    orderOf (χ (eta b (π i.succ))) = p ∧
      κ (longBlock F 3 i
        (CFSG.LocalAnalysis.ComponentInitial.sl2Diag F (χ (eta b (π i.succ))))) = (b : G) :=
  hκ.longBlock_sl2Diag_eq_coordinate (r := 2) hp2 hF hcfg hN hA i b hb1 hoff

end CFSG.StandardType

end
