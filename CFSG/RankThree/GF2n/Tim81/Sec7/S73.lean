module

public import CFSG.Holt.H78.Defs
public import CFSG.RankThree.GF2n.Tim81.Induction
public import CFSG.RankThree.GF2n.Tim81.Sec7.S73BarIso
import CFSG.GroupTheory.Fitting.MulEquiv
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Cen
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Delta
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Holt
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Induct
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Unitary

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n.Tim81.Sec7 (yOf rOf oOf)
open CFSG.Timmesfeld.Transvection CFSG.LieType.Universal CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {M V A B : Subgroup G} {h : G} {n f : ℕ}

theorem Sec7Hyp.exists_unitary_barY (hS : Sec7Hyp M V n f) (hT : Theorem1Below (Nat.card G))
    (h72 : Sec7.Stmt72 M V n f) (h73a : Sec7.Stmt73alpha M V) (h73g : Sec7.Stmt73gamma M V)
    (hD : L2Datum M V A B h) (hOY : inSubgroup (pPrimeCore 2) (yOf h) = oOf M h) :
    Subgroup.normalClosure (barY h V : Set (YBar h)) = generalizedFitting (YBar h) ∧
    ∃ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n) →* YBar h,
      Φ.range = Subgroup.normalClosure (barY h V : Set (YBar h)) ∧
      Φ.ker = Subgroup.center _ ∧
      IsSUImage (generalizedFitting (YBar h)) (barRoots h V) f n hS.one_le
        (Nat.le_trans (Nat.le_add_left 2 2) hS.four_le) := by
  have hE := hS.epsIn h72 h73a h73g (hS.stmt73delta h72) hD
  have hP := inSubgroup_pCore_barY_rOf hS.toSec6Hyp hD h73a hOY
  have hHyp := hE.hyp_barY hS.toSec6Hyp hD h72 h73a h73g hOY
  obtain ⟨f', _, hcard, hnc, m, hm, Φ, hrange, hker, hclass⟩ :=
    hS.unitaryConclusion_barY hT h72 h73a h73g hD hOY
  have hff : f = f' := Nat.pow_right_injective le_rfl
    (hS.card_V.symm.trans (hE.card_barY_self.symm.trans hcard))
  subst hff
  have hSUm : IsSUImage (generalizedFitting (YBar h)) (barRoots h V) f m hS.one_le
      (Nat.le_trans (Nat.le_add_left 2 2) hm) := ⟨Φ, hker.le, hrange.trans hnc, hclass⟩
  haveI : (generalizedFitting (YBar h)).Normal := by rw [← hnc]; infer_instance
  have h4 : 4 ≤ Nat.card (barY h V) := by
    rw [hE.card_barY_self]
    exact hE.root.four_le_card
  have hC := hHyp.centralizer_generalizedFitting_eq_bot h4
  have hnm : n = m := (hE.eq_of_isSUImage_barY hS hD h72 hP hm hC hSUm).symm
  subst hnm
  exact ⟨hnc, Φ, hrange, hker, hSUm⟩

theorem Sec7Hyp.stmt73 (hS : Sec7Hyp M V n f) (hT : Theorem1Below (Nat.card G))
    (h72 : Sec7.Stmt72 M V n f) (h73a : Sec7.Stmt73alpha M V) (h73g : Sec7.Stmt73gamma M V)
    (h73e : Sec7.Stmt73eps M V) : Sec7.Stmt73 M V n f := by
  intro A B h hD
  have hOY := (h73e A B h hD).1
  have hE := hS.epsIn h72 h73a h73g (hS.stmt73delta h72) hD
  have hP := inSubgroup_pCore_barY_rOf hS.toSec6Hyp hD h73a hOY
  have hHyp := hE.hyp_barY hS.toSec6Hyp hD h72 h73a h73g hOY
  obtain ⟨hnc, Φ, hrange, hker, hSU⟩ :=
    hS.exists_unitary_barY hT h72 h73a h73g hD hOY
  haveI : (generalizedFitting (YBar h)).Normal := by rw [← hnc]; infer_instance
  have h4 : 4 ≤ Nat.card (barY h V) := by
    rw [hE.card_barY_self]
    exact hE.root.four_le_card
  have hC := hHyp.centralizer_generalizedFitting_eq_bot h4
  obtain ⟨c, hcX, hcM⟩ := hS.exists_mem_cenOf_not_mem h72 hD
  have hY₀ : barY h (y0Of V (Subgroup.zpowers h)) = generalizedFitting (YBar h) :=
    hE.barY_y0Of.trans hnc
  have hSU₀ : IsSUImage (barY h (y0Of V (Subgroup.zpowers h))) (barRoots h V) f n hS.one_le
      (Nat.le_trans (Nat.le_add_left 2 2) hS.four_le) := by
    rw [hY₀]
    exact hSU
  refine ⟨hE.y0Of_le_cenOf hD hP (fun α => CFSG.WholeGroup.generalizedFitting_map_mulEquiv α)
      hC hS.one_le hS.four_le hSU hcX hcM,
    fun y hy => hE.exists_conj_eq_y0Of hSU₀ hy,
    hE.pCore_y0Of_eq_bot hHyp.o2, hE.pPrimeCore_y0Of_le_center, ?_⟩
  obtain ⟨Ψ, hΨs, hΨk⟩ := hE.exists_surjective_y0Of Φ (hrange.trans hE.barY_y0Of.symm)
  exact ⟨Ψ, hΨs, hΨk.trans hker⟩

theorem Sec7Hyp.stmt73_of_holt (hS : Sec7Hyp M V n f) (hT : Theorem1Below (Nat.card G))
    (h72 : Sec7.Stmt72 M V n f) (h73a : Sec7.Stmt73alpha M V) (h73g : Sec7.Stmt73gamma M V)
    (hHolt : CFSG.Holt.H78.HoltTheorem1) : Sec7.Stmt73 M V n f :=
  hS.stmt73 hT h72 h73a h73g
    (fun A B h hD => hS.oddCore_yOf hHolt h72 h73a h73g (hS.stmt73delta h72) hD)

end CFSG.RankThree.GF2n.Tim81
