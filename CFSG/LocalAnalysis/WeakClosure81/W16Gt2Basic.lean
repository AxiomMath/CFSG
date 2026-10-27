module

public import CFSG.LocalAnalysis.WeakClosure81.W16Cfg
public import CFSG.LocalAnalysis.WeakClosure81.W16Seventeen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem one_le_mQuot (c : Cfg1620 M V₀ V U S R H g B) : 1 ≤ E3.mQuot V (U ⊔ V₀) := by
  by_contra hlt
  have hzero : E3.mQuot V (U ⊔ V₀) = 0 := by omega
  have hsup : U ⊔ V₀ = V :=
    (E3.mQuot_eq_zero_iff c.cex.hyp.isPGroup (sup_le c.cex.le c.cex.hyp.h6.le)).1 hzero
  have hx_cent : conjSubgroup V₀ g ≤ centralizer (V : Set G) := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact Subgroup.one_mem _
    · have h := c.centralizer_eq x hx hx1
      rw [hsup] at h
      have hle : V ≤ centralizer ({x} : Set G) := by rw [← h]; exact inf_le_right
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (Subgroup.mem_centralizer_iff.1 (hle hv) x (Set.mem_singleton x)).symm
  obtain ⟨m, hmM, hBm⟩ := c.B_conj
  have hmN : m ∈ normalizer (V : Set G) := by
    rw [c.cex.hyp.h6.normalizer_eq]
    exact hmM
  have hB_cent : B ≤ centralizer (V : Set G) := by
    rw [hBm]
    calc conjSubgroup (conjSubgroup V₀ g) m ≤ conjSubgroup (centralizer (V : Set G)) m :=
          E3.conjSubgroup_mono_left m hx_cent
      _ = centralizer (V : Set G) := by
          rw [E3.conjSubgroup_centralizer V m, conjSubgroup_eq_iff_mem_normalizer.2 hmN]
  have hU_cent : U ≤ centralizer (B : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.1 (hB_cent hb) u (c.cex.le hu)).symm
  exact c.not_comm hU_cent

theorem conjClosure_le_R (h1 : W16One G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) :
    conjClosure (U ⊔ V₀) H ≤ R :=
  (c.cex.conjClosure_le_S h1 hS c.S_le c.mem).trans c.S_le

theorem V_le_R (c : Cfg1620 M V₀ V U S R H g B) : V ≤ R :=
  c.cex.V_le_S.trans c.S_le

theorem comm_V_R_le (c : Cfg1620 M V₀ V U S R H g B) : ⁅V, R⁆ ≤ V₀ := by
  rw [Subgroup.commutator_le]
  intro v hv r hr
  have hrC : r ∈ F11.CTilde M V₀ V := c.sylow.le hr
  have hcomm : ⁅r, v⁆ ∈ V₀ := (FourteenTwo.mem_cTilde_iff_comm.1 hrC).2.2 v hv
  rw [← commutatorElement_inv r v]
  exact V₀.inv_mem hcomm

theorem comm_conj_conjClosure_le (h1 : W16One G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) {h : G} (hh : h ∈ H) :
    ⁅conjSubgroup V h, conjClosure (U ⊔ V₀) H⁆ ≤ conjSubgroup V₀ h := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [mem_conjSubgroup_iff] at hx ⊢
  have hy' : h * y * h⁻¹ ∈ conjClosure (U ⊔ V₀) H := by
    have hnorm : h ∈ Subgroup.normalizer (conjClosure (U ⊔ V₀) H : Set G) :=
      le_normalizer_conjClosure (U ⊔ V₀) H hh
    exact (Subgroup.mem_normalizer_iff.1 hnorm y).1 hy
  have hcomm : ⁅h * x * h⁻¹, h * y * h⁻¹⁆ ∈ V₀ :=
    comm_V_R_le c (Subgroup.commutator_mem_commutator hx ((conjClosure_le_R h1 hS c) hy'))
  have key : h * ⁅x, y⁆ * h⁻¹ = ⁅h * x * h⁻¹, h * y * h⁻¹⁆ := by
    rw [conjugate_commutatorElement]
  rw [key]
  exact hcomm

theorem L_le_centralizer (c : Cfg1620 M V₀ V U S R H g B) :
    V ⊔ conjSubgroup V g ≤ centralizer (U : Set G) :=
  sup_le c.cex.V_le_centralizer (c.cex.conj_le_centralizer c.g_mem.2)

theorem L_le_conjClosure (c : Cfg1620 M V₀ V U S R H g B) :
    V ⊔ conjSubgroup V g ≤ conjClosure V H :=
  sup_le (le_conjClosure V H) (conjSubgroup_le_conjClosure_of_mem c.g_mem.1 le_rfl)

theorem inf_centralizer_L (c : Cfg1620 M V₀ V U S R H g B) :
    V₀ ⊓ centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G) = ⊥ := by
  have hle : V₀ ⊓ centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G) ≤ U := by
    calc V₀ ⊓ centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G)
        ≤ V ⊓ centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G) :=
          inf_le_inf c.cex.hyp.h6.le le_rfl
      _ = U := c.centralizer_L
  have hbot : V₀ ⊓ centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G) ≤ ⊥ := by
    rw [← c.cex.inf_eq_bot]
    exact le_inf hle inf_le_left
  exact le_bot_iff.mp hbot

theorem rk_conjSubgroup_inf_le (c : Cfg1620 M V₀ V U S R H g B) {x : G} (hx : x ∉ M) :
    rk ↥(conjSubgroup V₀ x ⊓ V) ≤ E3.mQuot V (U ⊔ V₀) := by
  obtain ⟨m, hmM, hBm⟩ := c.B_conj
  have hB_ctilde : B ≤ F11.CTilde M V₀ V := c.B_le.trans c.sylow.le
  have hm_ctilde : m⁻¹ ∈ Subgroup.normalizer (F11.CTilde M V₀ V : Set G) :=
    le_normalizer_cTilde_of_hyp15 c.cex.hyp (M.inv_mem hmM)
  have hV0g_ctilde : conjSubgroup V₀ g ≤ F11.CTilde M V₀ V := by
    have h1 : conjSubgroup V₀ g = conjSubgroup B m⁻¹ := by
      rw [hBm, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    rw [h1]
    calc conjSubgroup B m⁻¹ ≤ conjSubgroup (F11.CTilde M V₀ V) m⁻¹ :=
          E3.conjSubgroup_mono_left m⁻¹ hB_ctilde
      _ = F11.CTilde M V₀ V := conjSubgroup_eq_iff_mem_normalizer.2 hm_ctilde
  have hne : conjSubgroup V₀ g ≠ ⊥ := by
    intro hbot
    apply c.cex.hyp.ne_bot
    have h := congrArg (fun A : Subgroup G => conjSubgroup A g⁻¹) hbot
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one, E3.conjSubgroup_bot] at h
    exact h
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hy1' : (y : G) ≠ 1 := fun e => hy1 (Subtype.ext e)
  have hyC : (y : G) ∈ F11.CTilde M V₀ V := hV0g_ctilde y.2
  have hy_cent : V ⊓ centralizer ({(y : G)} : Set G) = U ⊔ V₀ :=
    c.centralizer_eq (y : G) y.2 hy1'
  have hyV : ¬ V ≤ centralizer ({(y : G)} : Set G) := by
    intro hle
    have hUV : U ⊔ V₀ = V := by
      rw [← hy_cent, inf_eq_left.2 hle]
    have h1 := one_le_mQuot c
    rw [hUV, E3.mQuot_self] at h1
    omega
  have hmain := mQuot_centralizer_ge_rk_conjSubgroup_inf c.cex.hyp.h6.elemAbelian
    c.cex.hyp.h6.le (le_of_eq c.cex.hyp.h6.normalizer_eq.symm) c.cex.hyp.normalizer₀
    c.cex.hyp.isTI (c.cex.hyp.h6.conjGenerated c.cex.hyp.ne_bot) hx hyC hyV
  rw [hy_cent] at hmain
  exact hmain

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
