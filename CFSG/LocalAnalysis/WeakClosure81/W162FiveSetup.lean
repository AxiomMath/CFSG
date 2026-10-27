module

public import CFSG.LocalAnalysis.WeakClosure81.W16Four
public import CFSG.LocalAnalysis.WeakClosure81.W16Seventeen
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Conj
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PGroup
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E3OffenderB
import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cex16

variable {M V₀ V U S : Subgroup G}

private theorem w162_U_le_inf_conj (h : Cex16 M V₀ V U S) {g : G}
    (hg : g ∈ centralizer (U : Set G)) :
    U ≤ V ⊓ conjSubgroup M g ∧ U ≤ conjSubgroup V g ⊓ M := by
  have hfix : ∀ x ∈ U, g * x * g⁻¹ = x := by
    intro x hx
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 hg x hx).symm
  refine ⟨fun x hx => Subgroup.mem_inf.2 ⟨h.le hx, ?_⟩,
    fun x hx => Subgroup.mem_inf.2 ⟨?_, h.hyp.le_M (h.le hx)⟩⟩
  · rw [mem_conjSubgroup_iff, hfix x hx]
    exact h.hyp.le_M (h.le hx)
  · rw [mem_conjSubgroup_iff, hfix x hx]
    exact h.le hx

private theorem w162_conj_mem_pCoreOf_iff {H : Subgroup G} {g : G} (hg : g ∈ H) (y : G) :
    g * y * g⁻¹ ∈ pCoreOf 2 H ↔ y ∈ pCoreOf 2 H :=
  (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hg) y).symm

theorem w162_commute_of_conj_le_M (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S)
    {g : G} (hg : g ∈ centralizer (U : Set G)) (hle : conjSubgroup V g ≤ M) :
    ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x := by
  have hH := h.hyp
  have hp : IsPGroup 2 (conjSubgroup V g) := E3.isPGroup_conjSubgroup hH.isPGroup g
  obtain ⟨c, hc, hcle⟩ := E3.exists_le_conj_of_isSylowIn h.sylow
    (le_inf hle (h.conj_le_centralizer hg)) hp
  have h1' : conjSubgroup V (g * c⁻¹) ≤ S := by
    have := E3.conjSubgroup_mono_left c⁻¹ hcle
    rwa [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, mul_inv_cancel,
      conjSubgroup_one] at this
  have h2 : conjSubgroup V (g * c⁻¹) ≤ E3.wClos V 0 S :=
    E3.le_wClos ⟨h1', g * c⁻¹, le_rfl, E3.mQuot_self _⟩
  have h3 : conjSubgroup V (g * c⁻¹) ≤ centralizer (V : Set G) :=
    h2.trans (h.wClos_le_centralizer h1 hS)
  intro x hx y hy
  have hcN : c ∈ normalizer (V : Set G) := by rw [hH.h6.normalizer_eq]; exact hc.1
  have hz : c * y * c⁻¹ ∈ conjSubgroup V (g * c⁻¹) := by
    rw [mem_conjSubgroup_iff] at hy ⊢
    have e : g * c⁻¹ * (c * y * c⁻¹) * (g * c⁻¹)⁻¹ = g * y * g⁻¹ := by group
    rw [e]
    exact hy
  have hx' : c * x * c⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hcN x).1 hx
  have hcomm := Subgroup.mem_centralizer_iff.1 (h3 hz) (c * x * c⁻¹) hx'
  have e1 : c * (x * y) * c⁻¹ = c * (y * x) * c⁻¹ :=
    calc c * (x * y) * c⁻¹ = c * x * c⁻¹ * (c * y * c⁻¹) := by group
      _ = c * y * c⁻¹ * (c * x * c⁻¹) := hcomm
      _ = c * (y * x) * c⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel e1)

theorem w162_not_conj_le_M (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S) {g : G}
    (hg : g ∈ centralizer (U : Set G))
    (hc : ¬ ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x) : ¬ conjSubgroup V g ≤ M :=
  fun hle => hc (h.w162_commute_of_conj_le_M h1 hS hg hle)

theorem w162_not_V_le_conj_M (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S) {g : G}
    (hg : g ∈ centralizer (U : Set G))
    (hc : ¬ ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x) : ¬ V ≤ conjSubgroup M g := by
  intro hle
  have hinv : conjSubgroup V g⁻¹ ≤ M := (E3.le_conjSubgroup_iff_inv_le g).1 hle
  have hcomm := h.w162_commute_of_conj_le_M h1 hS ((centralizer (U : Set G)).inv_mem hg) hinv
  apply hc
  intro x hx y hy
  have hy' : g * y * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 hy
  have hx' : g * x * g⁻¹ ∈ conjSubgroup V g⁻¹ := by
    rw [mem_conjSubgroup_iff]
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e]
    exact hx
  have hxy := hcomm (g * y * g⁻¹) hy' (g * x * g⁻¹) hx'
  have e1 : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ :=
    calc g * (y * x) * g⁻¹ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := hxy
      _ = g * (x * y) * g⁻¹ := by group
  exact (mul_left_cancel (mul_right_cancel e1)).symm

theorem w162_inf_conj_ne_bot (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S) {g : G}
    (hg : g ∈ centralizer (U : Set G)) :
    V₀ ⊓ conjSubgroup M g ≠ ⊥ ∧ conjSubgroup V₀ g ⊓ M ≠ ⊥ := by
  have hH := h.hyp
  have hne : V₀ ⊓ centralizer (S : Set G) ≠ ⊥ :=
    CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot Nat.prime_two
      h.sylow.isPGroup hH.elemAbelian₀.isPGroup hH.ne_bot (h.S_le_M.trans hH.normalizer₀.symm.le)
  have hU2 : IsPGroup 2 U := hH.isPGroup.to_le h.le
  have hN : CFSG.QuasithinUnique.CharTwo (normalizer (U : Set G)) :=
    hS.charTwo _ ⟨U, h.ne_bot, hU2, rfl⟩
  have hCh : CFSG.QuasithinUnique.CharTwo (centralizer (U : Set G)) := by
    have h1' := CFSG.QuasithinUnique.CharTwo.inf_centralizer hN Subgroup.le_normalizer hU2
    rwa [inf_eq_right.2 (Subgroup.centralizer_le_normalizer (U : Set G))] at h1'
  have hF : Fam16 M U S (centralizer (U : Set G)) := ⟨h.S_le_centralizer, le_rfl, h.not_le⟩
  have hOS : pCoreOf 2 (centralizer (U : Set G)) ≤ S := h.pCoreOf_le_S h1 hS hF
  have hV₀C : V₀ ≤ centralizer (U : Set G) := h.V₀_le_S.trans h.S_le_centralizer
  obtain ⟨⟨w, hwmem⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hw1' : w ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
  have hwV₀ : w ∈ V₀ := (Subgroup.mem_inf.1 hwmem).1
  have hwO : w ∈ pCoreOf 2 (centralizer (U : Set G)) :=
    hCh (Subgroup.mem_inf.2 ⟨hV₀C hwV₀,
      Subgroup.centralizer_le (fun y hy => hOS hy) (Subgroup.mem_inf.1 hwmem).2⟩)
  refine ⟨fun hbot => hw1' ?_, fun hbot => hw1' ?_⟩
  · have hOg : w ∈ conjSubgroup M g := by
      rw [mem_conjSubgroup_iff]
      exact h.S_le_M (hOS ((w162_conj_mem_pCoreOf_iff hg w).2 hwO))
    have hmem : w ∈ V₀ ⊓ conjSubgroup M g := Subgroup.mem_inf.2 ⟨hwV₀, hOg⟩
    rwa [hbot, Subgroup.mem_bot] at hmem
  · have hx : g⁻¹ * w * g ∈ conjSubgroup V₀ g ⊓ M := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [mem_conjSubgroup_iff, show g * (g⁻¹ * w * g) * g⁻¹ = w by group]
        exact hwV₀
      · have h1' := (w162_conj_mem_pCoreOf_iff ((centralizer (U : Set G)).inv_mem hg) w).2 hwO
        rw [inv_inv] at h1'
        exact h.S_le_M (hOS h1')
    rw [hbot, Subgroup.mem_bot] at hx
    have hwe : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
    rw [hwe, hx]
    group

theorem w162_mQuot_conj_le (h : Cex16 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) :
    E3.mQuot V (conjSubgroup M g) ≤ E3.mQuot V U ∧
      E3.mQuot (conjSubgroup V g) M ≤ E3.mQuot V U := by
  obtain ⟨hU1, hU2⟩ := w162_U_le_inf_conj h hg
  refine ⟨E3.mQuot_mono (hU1.trans inf_le_right), ?_⟩
  have hUg : conjSubgroup U g = U :=
    conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.centralizer_le_normalizer (U : Set G) hg)
  calc E3.mQuot (conjSubgroup V g) M ≤ E3.mQuot (conjSubgroup V g) U :=
        E3.mQuot_mono (hU2.trans inf_le_right)
    _ = E3.mQuot (conjSubgroup V g) (conjSubgroup U g) := by rw [hUg]
    _ = E3.mQuot V U := E3.mQuot_conjSubgroup V U g

theorem w162_inf_conj_le_cTilde (h : Cex16 M V₀ V U S) {g : G}
    (hg : g ∈ centralizer (U : Set G)) : conjSubgroup V g ⊓ M ≤ F11.CTilde M V₀ V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  obtain ⟨hxV, hxM⟩ := Subgroup.mem_inf.1 hx
  have hp : IsPGroup 2 (conjSubgroup V g) := E3.isPGroup_conjSubgroup h.hyp.isPGroup g
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hp) ⟨x, hxV⟩
  exact h.mem_cTilde_of_orderOf ⟨hxM, h.conj_le_centralizer hg hxV⟩
    ⟨k, by rw [← hk]; exact Subgroup.orderOf_coe (⟨x, hxV⟩ : conjSubgroup V g)⟩

theorem w162_oneFirst (h : Cex16 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) :
    OneFirst M V₀ V g := fun _ hx => h.w162_inf_conj_le_cTilde hg hx.1

theorem w162_oneDual (h : Cex16 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) :
    OneDual M V₀ V g :=
  (oneDual_iff_oneFirst_inv M V₀ V g).2 (h.w162_oneFirst ((centralizer (U : Set G)).inv_mem hg))

theorem w162_inCalO1 (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S) {g : G}
    (hg : g ∈ centralizer (U : Set G))
    (hc : ¬ ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x) :
    InCalO1 (E3.mQuot V U) M V₀ V g :=
  ⟨⟨⟨h.w162_not_conj_le_M h1 hS hg hc, (h.w162_mQuot_conj_le hg).1,
      fun _ => (h.w162_inf_conj_ne_bot h1 hS hg).1⟩,
    ⟨h.w162_not_V_le_conj_M h1 hS hg hc, (h.w162_mQuot_conj_le hg).2,
      fun _ => (h.w162_inf_conj_ne_bot h1 hS hg).2⟩⟩, h.w162_oneFirst hg, h.w162_oneDual hg⟩

theorem w162_hyp65 (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S) {g : G}
    (hg : g ∈ centralizer (U : Set G))
    (hc : ¬ ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x) :
    Hyp65 (E3.mQuot V U) M V₀ V g :=
  ⟨h.hyp.h6.elemAbelian, h.hyp.h6.le, h.hyp.ne_bot, h.hyp.h6.normalizer_eq, h.hyp.normalizer₀,
    h.hyp.isTI, h.w162_inCalO1 h1 hS hg hc⟩

theorem w162_eq_of_not_centralizer_le (h : Cex16 M V₀ V U S) {C : Subgroup G} (hUC : U ≤ C)
    (hCV : C ≤ V) (hnot : ¬ centralizer (C : Set G) ≤ M) : C = U := by
  have hH := h.hyp
  have hq1 : (E3.mQuot V U : ℕ∞) ≤ E3.mQuot V C := by
    rw [h.mquot]
    exact rMV_le_mQuot M V C hCV hnot
  have hq2 : E3.mQuot V C ≤ E3.mQuot V U := E3.mQuot_mono hUC
  have hq : E3.mQuot V C = E3.mQuot V U := le_antisymm hq2 (by exact_mod_cast hq1)
  have hcard : Nat.card C = Nat.card U := by
    have e1 := E3.card_eq_two_pow_mul hH.isPGroup hCV
    have e2 := E3.card_eq_two_pow_mul hH.isPGroup h.le
    rw [hq] at e1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) (e1.symm.trans e2)
  exact (Subgroup.eq_of_le_of_card_ge hUC (le_of_eq hcard)).symm

end Cex16

end CFSG.LocalAnalysis.WeakClosure81
