module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2WeakClosureAux1
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem commutator_mem_inf_conjSubgroup (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) {h w : G} (hh : h ∈ H) (hwM : w ∈ M)
    (hwW : w ∈ conjSubgroup V h) :
    ∀ a ∈ U ⊔ V₀, ⁅a, w⁆ ∈ V ⊓ conjSubgroup V₀ h := by
  intro a ha
  have hU'V : U ⊔ V₀ ≤ V := sup_le c.cex.le c.cex.hyp.h6.le
  have haV : a ∈ V := hU'V ha
  have hMnormV : M ≤ Subgroup.normalizer (V : Set G) :=
    le_of_eq c.cex.hyp.h6.normalizer_eq.symm
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.zpowers_le.2 (hMnormV hwM)
  have hVmem : ⁅a, w⁆ ∈ V :=
    ((Subgroup.le_normalizer_iff_commutator_le_left).1 hwN)
      (Subgroup.commutator_mem_commutator haV (Subgroup.mem_zpowers w))
  have haI : a ∈ conjClosure (U ⊔ V₀) H := le_conjClosure (U ⊔ V₀) H ha
  have hwa : ⁅w, a⁆ ∈ conjSubgroup V₀ h :=
    comm_conj_conjClosure_le h1 hS c hh
      (Subgroup.commutator_mem_commutator hwW haI)
  have hV₀'mem : ⁅a, w⁆ ∈ conjSubgroup V₀ h := by
    have heq : ⁅a, w⁆ = ⁅w, a⁆⁻¹ := by
      rw [← inv_inv (⁅a, w⁆), commutatorElement_inv]
    rw [heq]
    exact (conjSubgroup V₀ h).inv_mem hwa
  exact Subgroup.mem_inf.2 ⟨hVmem, hV₀'mem⟩

theorem mQuot_sup_inf_centralizer_le (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) {h w : G} (hh : h ∈ H) (hhM : h ∉ M)
    (hwM : w ∈ M) (hwW : w ∈ conjSubgroup V h) :
    E3.mQuot (U ⊔ V₀) ((U ⊔ V₀) ⊓ Subgroup.centralizer ({w} : Set G)) ≤
      E3.mQuot V (U ⊔ V₀) := by
  have hU'V : U ⊔ V₀ ≤ V := sup_le c.cex.le c.cex.hyp.h6.le
  have hcommA := commutator_mem_inf_conjSubgroup h1 h5 h15 hS c hh hwM hwW
  have hB : E3.mQuot (U ⊔ V₀) ((U ⊔ V₀) ⊓ Subgroup.centralizer ({w} : Set G)) ≤
      rk ↥(V ⊓ conjSubgroup V₀ h) :=
    mQuot_inf_centralizer_le_rk c.cex.hyp.h6.elemAbelian hU'V inf_le_left hcommA
  have hhinv : h⁻¹ ∉ M := fun hmem => hhM (by simpa using M.inv_mem hmem)
  have hrk : rk ↥(V ⊓ conjSubgroup V₀ h) ≤ E3.mQuot V (U ⊔ V₀) := by
    rw [inf_comm]
    exact c.rk_conjSubgroup_inf_le (x := h) hhM
  exact hB.trans hrk

theorem preTil_fixV_inf_sup_eq_centralizer (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) {h w : G} (hh : h ∈ H) (hhM : h ∉ M)
    (hwM : w ∈ M) (hwW : w ∈ conjSubgroup V h) (hwst : w ∈ stabTil V₀ V) :
    preTil V₀ V c.cex.hyp.h6.elemAbelian
        (fixV (Subgroup.zpowers
          (actTil V₀ V c.cex.hyp.h6.elemAbelian ⟨w, hwst⟩))) ⊓ (U ⊔ V₀) =
      (U ⊔ V₀) ⊓ Subgroup.centralizer ({w} : Set G) := by
  have hV := c.cex.hyp.h6.elemAbelian
  have hU'V : U ⊔ V₀ ≤ V := sup_le c.cex.le c.cex.hyp.h6.le
  have hbot : V₀ ⊓ conjSubgroup V₀ h = ⊥ := by
    rw [inf_comm]
    exact c.cex.hyp.conj_inf_eq_bot hhM
  ext a
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨haC, haU'⟩
    refine ⟨haU', ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    rw [hb]
    have hwa : ⁅w, a⁆ ∈ V₀ := by
      rw [mem_preTil_iff_of_mem V₀ V hV _ (hU'V haU'), mem_fixV_zpowers, actTil_mk,
        mkTil_eq_iff, actStab_apply_val] at haC
      simpa only [commutatorElement_def, IntMod.mk, IntMod.val] using haC
    have haw : ⁅a, w⁆ ∈ V₀ := by
      have heq : ⁅a, w⁆ = ⁅w, a⁆⁻¹ := by
        rw [← inv_inv (⁅a, w⁆), commutatorElement_inv]
      rw [heq]
      exact V₀.inv_mem hwa
    have hawX := commutator_mem_inf_conjSubgroup h1 h5 h15 hS c hh hwM hwW a haU'
    have hawbot : ⁅a, w⁆ ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_inf.2 ⟨haw, hawX.2⟩
    have h1' : ⁅a, w⁆ = 1 := Subgroup.mem_bot.1 hawbot
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1').symm
  · rintro ⟨haU', hac⟩
    refine ⟨?_, haU'⟩
    rw [Subgroup.mem_centralizer_iff] at hac
    have hwa : w * a = a * w := hac w (Set.mem_singleton w)
    rw [mem_preTil_iff_of_mem V₀ V hV _ (hU'V haU'), mem_fixV_zpowers, actTil_mk,
      mkTil_eq_iff, actStab_apply_val]
    simp only [IntMod.mk, IntMod.val]
    have hone : w * a * w⁻¹ * a⁻¹ = 1 := by
      rw [hwa]
      group
    rw [hone]
    exact V₀.one_mem

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
