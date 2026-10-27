module

public import CFSG.RankThree.GF2n.Tim81.Sec7.S73BarHyp
public import CFSG.RankThree.GF2n.Tim81.Induction
import CFSG.Assembly.SectionInduction
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Delta
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Holt
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Split

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n.Tim81.Sec7 (yOf rOf oOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V A B : Subgroup G} {h : G} {n f : ℕ}

theorem EpsIn.weaklyClosedIn_barY (hE : EpsIn M V h) (hS : Sec6Hyp M V)
    (hD : L2Datum M V A B h) (h73a : Sec7.Stmt73alpha M V)
    (hOY : inSubgroup (pPrimeCore 2) (yOf h) = oOf M h)
    (hP : inSubgroup (pCore 2) (barY h (rOf M h)) = barY h (p0Of M V (A ⊔ B))) :
    WeaklyClosedIn (barY h V) (inSubgroup (pCore 2) (barY h (rOf M h))) := by
  rw [hP]
  refine ⟨barY_mono h (hD.V_le_p0 hS), fun g hg => ?_⟩
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(yOf h)) g
  rw [barY_conj h hy hE.le_yOf] at hg ⊢
  have hα := h73a A B h hD
  have hle : conjSubgroup y V ≤ Pc M V := by
    intro w hw
    have hwY : w ∈ yOf h := hE.conjSubgroup_le_yOf hy hw
    have hw2 : IsPGroup 2 (Subgroup.zpowers w) :=
      (hE.root.isPGroup_V.map (MulAut.conj y).toMonoidHom).to_le (Subgroup.zpowers_le.mpr hw)
    have hw' : QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨w, hwY⟩ ∈
        barY h (conjSubgroup y V) := ⟨⟨w, hwY⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
    have hwbar : QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨w, hwY⟩ ∈
        barY h (oOf M h ⊔ p0Of M V (A ⊔ B)) := barY_mono h le_sup_right (hg hw')
    have hwU : w ∈ oOf M h ⊔ p0Of M V (A ⊔ B) :=
      (hE.mk_mem_barY_iff_of_oddCore_le (hOY.le.trans le_sup_left) hwY).mp hwbar
    exact (hα.2.2.2.2.1 w (hα.1.ge hwU) hw2).1
  rw [hE.root.weaklyClosed_P.2 y hle]

theorem EpsIn.not_weaklyClosedIn_barY (hE : EpsIn M V h) :
    ¬ WeaklyClosedIn (barY h V) (barY h (rOf M h)) := by
  rintro ⟨-, hwc⟩
  obtain ⟨c, hcY, hcV, hcM⟩ := hE.moved
  have hle : barY h (conjSubgroup c V) ≤ barY h (rOf M h) :=
    barY_mono h (le_inf hcM (hE.conjSubgroup_le_yOf hcY))
  rw [← barY_conj h hcY hE.le_yOf] at hle
  have hN : QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨c, hcY⟩ ∈ barY h (rOf M h) := by
    rw [← hE.normalizer_barY]
    exact conjSubgroup_eq_self_iff.mp (hwc _ hle)
  exact hcV (conjSubgroup_eq_self_iff.mpr
    (hE.root.le_normalizer (hE.mem_rOf_of_bar_mem hcY hN).1))

theorem EpsIn.isHMember_barY (hE : EpsIn M V h) {P : Subgroup G}
    (hP : inSubgroup (pCore 2) (barY h (rOf M h)) = barY h P) {H₀ : Subgroup G}
    (hH₀Y : H₀ ≤ yOf h) (hPH₀ : P ≤ H₀) (hH₀M : ¬ H₀ ≤ M)
    (hO₂ : inSubgroup (pCore 2) H₀ ≠ ⊥) :
    IsHMember (barY h (rOf M h)) (barY h V) (barY h H₀) := by
  obtain ⟨hQ2, hQH, hHQ⟩ := inSubgroup_pCore_two H₀
  refine ⟨?_, inf_le_left.trans (hP.le.trans (barY_mono h hPH₀)), ?_⟩
  · intro hbot
    have hle : barY h (inSubgroup (pCore 2) H₀) ≤ inSubgroup (pCore 2) (barY h H₀) :=
      le_inSubgroup_pCore (barY_mono h hQH) (barY_le_normalizer h hHQ) (isPGroup_barY h hQ2)
    rw [hbot, le_bot_iff] at hle
    have hcard := hE.card_barY_of_disjoint (hQH.trans hH₀Y)
      (hE.disjoint_oddCore_of_isPGroup hQ2)
    rw [hle, Subgroup.card_bot] at hcard
    exact hO₂ (Subgroup.eq_bot_of_card_eq _ hcard.symm)
  · intro hle
    obtain ⟨c, hcH, hcM⟩ := SetLike.not_le_iff_exists.mp hH₀M
    have hc' : QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨c, hH₀Y hcH⟩ ∈ barY h H₀ :=
      ⟨⟨c, hH₀Y hcH⟩, Subgroup.mem_subgroupOf.mpr hcH, rfl⟩
    exact hcM (hE.mem_rOf_of_bar_mem (hH₀Y hcH) (hle hc')).1

theorem card_yBar_lt {t : G} (ht : t * h * t⁻¹ = h⁻¹) (hh : h * h ≠ 1) :
    Nat.card (YBar h) < Nat.card G := by
  have htY : t ∉ yOf h := by
    intro htY
    have hc := Subgroup.mem_centralizer_iff.mp htY h (Subgroup.mem_zpowers h)
    apply hh
    have hinv : h⁻¹ = h := by rw [← ht, ← hc, mul_inv_cancel_right]
    calc h * h = h * h⁻¹ := by rw [hinv]
      _ = 1 := mul_inv_cancel h
  exact CFSG.Assembly.card_section_lt (K := yOf h)
    (fun htop => htY (by rw [htop]; exact Subgroup.mem_top t)) (pPrimeCore 2 ↥(yOf h))

theorem Sec7Hyp.unitaryConclusion_barY (hS : Sec7Hyp M V n f) (hT : Theorem1Below (Nat.card G))
    (h72 : Sec7.Stmt72 M V n f) (h73a : Sec7.Stmt73alpha M V) (h73g : Sec7.Stmt73gamma M V)
    (hD : L2Datum M V A B h) (hOY : inSubgroup (pPrimeCore 2) (yOf h) = oOf M h) :
    UnitaryConclusion (barY h V) := by
  have h73d := hS.stmt73delta h72
  have hE := hS.epsIn h72 h73a h73g h73d hD
  have hP := inSubgroup_pCore_barY_rOf hS.toSec6Hyp hD h73a hOY
  have hHyp := hE.hyp_barY hS.toSec6Hyp hD h72 h73a h73g hOY
  have h4 : 4 ≤ Nat.card (barY h V) := by
    rw [hE.card_barY_self]
    exact hE.root.four_le_card
  have hwc := hE.weaklyClosedIn_barY hS.toSec6Hyp hD h73a hOY hP
  obtain ⟨t, -, ht⟩ := hD.exists_mem_conj_eq_inv.1
  have hlt := card_yBar_lt ht (hD.mul_self_ne_one hE.root)
  rcases hT (YBar h) hlt (barY h (rOf M h)) (barY h V) hHyp h4 hwc with hW | hU | hH
  · exact absurd hW hE.not_weaklyClosedIn_barY
  · exact hU
  · obtain ⟨H₀, hH₀Y, hP₀H₀, hH₀M, hO₂, -⟩ := h73d A B h hD
    exact absurd (hE.isHMember_barY hP hH₀Y hP₀H₀ hH₀M hO₂) (hH _)

end CFSG.RankThree.GF2n.Tim81
