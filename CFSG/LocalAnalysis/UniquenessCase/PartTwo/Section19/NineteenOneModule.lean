module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenOneWeakShape
public import CFSG.GroupTheory.InvertingInvolutionRank
public import CFSG.Quasithin.Background.B69Schur
public import CFSG.Quasithin.Background.SzG11TensorD
public import CFSG.CGT.PushingUpLit.CGT6.Diag.BoundBasic
public import CFSG.GroupTheory.AltFiveConjCommutator
public import CFSG.Walter.J1.A5Sub

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.GroupTheory (eight_dvd_rk_of_inverting normalizes_zpowers_of_conj_mem
  rk_commV_conj_comm_le exists_inv_mul_conj_order_three_or_five)
open CFSG.GH74.Generic.S45 (a5_exists_five)

variable {W : Type} [CommGroup W]

theorem rk_commV_eq_eight_and_trivial [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Lb Kb : Subgroup (MulAut W)} (hAltL : IsAlt ↥Lb 5) (hAltK : IsAlt ↥Kb 5)
    (hcommLK : ∀ x ∈ Lb, ∀ z ∈ Kb, x * z = z * x)
    {f : MulAut W} (hford : orderOf f = 5) (hffix : fixV (Subgroup.zpowers f) = ⊥)
    (hfcent : ∀ x ∈ Lb ⊔ Kb, x * f = f * x)
    {y : MulAut W} (hyL : y ∈ Lb) (hyord : orderOf y = 3 ∨ orderOf y = 5)
    (hy16 : rk ↥(commV (Subgroup.zpowers y)) < 16) :
    rk ↥(commV (Subgroup.zpowers y)) = 8 ∧
      ∀ k ∈ Kb, ∀ a ∈ commV (Subgroup.zpowers y), k a = a := by
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyord
    rcases hyord with h | h <;> omega
  have hy15 : y ^ 15 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rcases hyord with h | h <;> rw [h] <;> norm_num)
  obtain ⟨c, hcL, hc2', -, hcy⟩ :=
    CFSG.Walter.J1.A5Sub.exists_inv (Classical.choice hAltL) hyL hy1 hy15
  have hc2 : c * c = 1 := (pow_two c).symm.trans hc2'
  have hyodd : Odd (orderOf y) := by
    rcases hyord with h | h <;> rw [h] <;> decide
  have hf5 : f ^ 5 = 1 := by rw [← hford]; exact pow_orderOf_eq_one f
  have hfc : f * c = c * f := (hfcent c (Subgroup.mem_sup_left hcL)).symm
  have hfy : f * y = y * f := (hfcent y (Subgroup.mem_sup_left hyL)).symm
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hfy' : f⁻¹ * y = y * f⁻¹ := (show Commute f y from hfy).inv_left.eq
  have hUcomm : ∀ g : MulAut W, g * y = y * g →
      ∀ u ∈ commV (Subgroup.zpowers y), g u ∈ commV (Subgroup.zpowers y) := by
    intro g hg u hu
    refine commV_apply_mem_of_normalizes (normalizes_zpowers_of_conj_mem ?_) hu
    rw [hg, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers y
  have hUy : ∀ u ∈ commV (Subgroup.zpowers y), y u ∈ commV (Subgroup.zpowers y) :=
    hUcomm y rfl
  have hUf : ∀ u ∈ commV (Subgroup.zpowers y), f u ∈ commV (Subgroup.zpowers y) :=
    hUcomm f hfy
  have hUc : ∀ u ∈ commV (Subgroup.zpowers y), c u ∈ commV (Subgroup.zpowers y) := by
    intro u hu
    refine commV_apply_mem_of_normalizes (normalizes_zpowers_of_conj_mem ?_) hu
    rw [hcy]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y)
  have hfixU : ∀ u ∈ commV (Subgroup.zpowers y), y u = u → u = 1 := fun u hu hyu =>
    CFSG.CGT.PushingUpLit.CGT6.Diag.Bound.eq_one_of_mem_commV_zpowers_of_fixed hW hyodd hu hyu
  have h8J : ∀ J : Subgroup W, J ≤ commV (Subgroup.zpowers y) → (∀ u ∈ J, y u ∈ J) →
      (∀ u ∈ J, c u ∈ J) → (∀ u ∈ J, f u ∈ J) → 8 ∣ rk ↥J := fun J hJU hJy hJc hJf =>
    eight_dvd_rk_of_inverting hW hc2 hcy hyodd hf5 hffix hfc hJy hJc hJf
      (fun u hu hyu => hfixU u (hJU hu) hyu)
  have hUne : commV (Subgroup.zpowers y) ≠ ⊥ := by
    intro hU
    apply hy1
    refine CFSG.CGT.PushingUpLit.CGT6.eq_one_of_trivial_on_commV hW (Subgroup.mem_zpowers y)
      hyodd ?_
    intro w hw
    rw [hU, Subgroup.mem_bot] at hw
    rw [hw, map_one]
  have hrk0 : rk ↥(commV (Subgroup.zpowers y)) ≠ 0 := fun h0 => hUne ((rk_eq_zero_iff hW).mp h0)
  have hrk8 : rk ↥(commV (Subgroup.zpowers y)) = 8 := by
    obtain ⟨m, hm⟩ := h8J _ le_rfl hUy hUc hUf
    omega
  refine ⟨hrk8, ?_⟩
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup (MulAut W), H = Subgroup.closure {f, y, c} := ⟨_, rfl⟩
  have hfH : f ∈ H := by rw [hHdef]; exact Subgroup.subset_closure (by simp)
  have hyH : y ∈ H := by rw [hHdef]; exact Subgroup.subset_closure (by simp)
  have hcH : c ∈ H := by rw [hHdef]; exact Subgroup.subset_closure (by simp)
  have hHU2 : ∀ x ∈ H, ∀ u ∈ commV (Subgroup.zpowers y),
      x u ∈ commV (Subgroup.zpowers y) ∧ x⁻¹ u ∈ commV (Subgroup.zpowers y) := by
    intro x hx
    rw [hHdef] at hx
    induction hx using Subgroup.closure_induction with
    | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact fun u hu => ⟨hUf u hu, hUcomm _ hfy' u hu⟩
      · exact fun u hu => ⟨hUy u hu, hUcomm _ (by group) u hu⟩
      · exact fun u hu => ⟨hUc u hu, by rw [hcinv]; exact hUc u hu⟩
    | one => exact fun u hu => ⟨by simpa using hu, by simpa using hu⟩
    | mul a b _ _ ha hb =>
      exact fun u hu => ⟨by rw [MulAut.mul_apply]; exact (ha _ (hb u hu).1).1,
        by rw [mul_inv_rev, MulAut.mul_apply]; exact (hb _ (ha u hu).2).2⟩
    | inv a _ ha => exact fun u hu => ⟨(ha u hu).2, by rw [inv_inv]; exact (ha u hu).1⟩
  have hHU : ∀ x ∈ H, ∀ u ∈ commV (Subgroup.zpowers y), x u ∈ commV (Subgroup.zpowers y) :=
    fun x hx u hu => (hHU2 x hx u hu).1
  have hfixH : commV (Subgroup.zpowers y) ⊓ fixV H = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    exact Subgroup.mem_bot.mpr (hfixU w hw.1 (hw.2 y hyH))
  have hIrr : commV (Subgroup.zpowers y) ∈ IrrPlus H (⊤ : Subgroup W) := by
    rw [mem_irrPlus_top_iff]
    refine ⟨hHU, ?_, ?_, ?_⟩
    · apply le_antisymm
      · rw [commSub, Subgroup.closure_le]
        rintro _ ⟨x, hx, w, hw, rfl⟩
        exact Subgroup.mul_mem _ (hHU x hx w hw) (Subgroup.inv_mem _ hw)
      · intro r hr
        obtain ⟨u, hu, rfl⟩ := CFSG.CGT.PushingUpLit.CGT6.Diag.Bound.exists_comm_eq hW hyodd hr
        rw [commSub]
        exact Subgroup.subset_closure ⟨y, hyH, u, hu, rfl⟩
    · rw [hfixH]
      exact bot_lt_iff_ne_bot.mpr hUne
    · intro J hJinv _ hJU
      rw [hfixH]
      obtain ⟨m, hm⟩ := h8J J hJU (hJinv y hyH) (hJinv c hcH) (hJinv f hfH)
      have hJle : rk ↥J ≤ rk ↥(commV (Subgroup.zpowers y)) := rk_mono hJU
      by_cases hm0 : m = 0
      · left
        rw [hm0, mul_zero] at hm
        exact (rk_eq_zero_iff hW).mp hm
      · right
        exact eq_of_le_of_rk_le hW hJU (by omega)
  have hKperf : Group.IsPerfect ↥Kb := by
    obtain ⟨e⟩ := hAltK
    exact CFSG.Quasithin.G11.SzG11S.Tensor.isPerfect_of_alt_five e
  have hHC : H ≤ Subgroup.centralizer (Kb : Set (MulAut W)) := by
    rw [hHdef, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro k hk
    rcases hg with rfl | rfl | rfl
    · exact hfcent k (Subgroup.mem_sup_right hk)
    · exact (hcommLK _ hyL k hk).symm
    · exact (hcommLK _ hcL k hk).symm
  have hKH : ∀ k ∈ Kb, ∀ l ∈ H, k * l = l * k := fun k hk l hl =>
    Subgroup.mem_centralizer_iff.mp (hHC hl) k hk
  have hKU : ∀ k ∈ Kb, ∀ u ∈ commV (Subgroup.zpowers y), k u ∈ commV (Subgroup.zpowers y) :=
    fun k hk u hu => hUcomm k (hcommLK y hyL k hk).symm u hu
  exact B69.trivial_of_perfect_commute hW hIrr hKperf hKH hKU

theorem sixteen_le_rk_of_A5A5 [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Lb Kb : Subgroup (MulAut W)} (hAltL : IsAlt ↥Lb 5) (hAltK : IsAlt ↥Kb 5)
    (hcommLK : ∀ x ∈ Lb, ∀ z ∈ Kb, x * z = z * x)
    {f : MulAut W} (hford : orderOf f = 5) (hffix : fixV (Subgroup.zpowers f) = ⊥)
    (hfcent : ∀ x ∈ Lb ⊔ Kb, x * f = f * x) : 16 ≤ rk W := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨s, hsL, hsord⟩ := a5_exists_five (Classical.choice hAltL)
  obtain ⟨s', hsK, hs'ord⟩ := a5_exists_five (Classical.choice hAltK)
  have hle : ∀ U : Subgroup W, rk ↥U ≤ rk W := fun U => (rk_mono le_top).trans_eq rk_top
  have hcommKL : ∀ x ∈ Kb, ∀ z ∈ Lb, x * z = z * x := fun x hx z hz => (hcommLK z hz x hx).symm
  have hfcent' : ∀ x ∈ Kb ⊔ Lb, x * f = f * x := fun x hx => hfcent x (by rwa [sup_comm])
  obtain ⟨h1, -⟩ := rk_commV_eq_eight_and_trivial hW hAltL hAltK hcommLK hford hffix hfcent
    hsL (Or.inr hsord) ((hle _).trans_lt hlt)
  obtain ⟨h2, hL2⟩ := rk_commV_eq_eight_and_trivial hW hAltK hAltL hcommKL hford hffix hfcent'
    hsK (Or.inr hs'ord) ((hle _).trans_lt hlt)
  have hsodd : Odd (orderOf s) := by rw [hsord]; decide
  have hinf : commV (Subgroup.zpowers s) ⊓ commV (Subgroup.zpowers s') = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    exact Subgroup.mem_bot.mpr
      (CFSG.CGT.PushingUpLit.CGT6.Diag.Bound.eq_one_of_mem_commV_zpowers_of_fixed hW hsodd hw.1
        (hL2 s hsL w hw.2))
  have hsum := rk_sup_add_rk_inf (commV (Subgroup.zpowers s)) (commV (Subgroup.zpowers s'))
  rw [hinf, rk_bot] at hsum
  have := hle (commV (Subgroup.zpowers s) ⊔ commV (Subgroup.zpowers s'))
  omega

theorem centralizes_one_of_normalizes_A5A5 [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Lb Kb : Subgroup (MulAut W)} (hAltL : IsAlt ↥Lb 5) (hAltK : IsAlt ↥Kb 5)
    (hcommLK : ∀ x ∈ Lb, ∀ z ∈ Kb, x * z = z * x)
    {f : MulAut W} (hford : orderOf f = 5) (hffix : fixV (Subgroup.zpowers f) = ⊥)
    (hfcent : ∀ x ∈ Lb ⊔ Kb, x * f = f * x)
    {φ : MulAut W} (hd : rkIdx (fixV (Subgroup.zpowers φ)) ≤ 7)
    (hnL : ∀ x ∈ Lb, φ * x * φ⁻¹ ∈ Lb) (hnK : ∀ x ∈ Kb, φ * x * φ⁻¹ ∈ Kb) :
    (∀ x ∈ Lb, φ * x = x * φ) ∨ (∀ x ∈ Kb, φ * x = x * φ) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hneL, hneK⟩ := hcon
  have hcommKL : ∀ x ∈ Kb, ∀ z ∈ Lb, x * z = z * x := fun x hx z hz => (hcommLK z hz x hx).symm
  have hfcent' : ∀ x ∈ Kb ⊔ Lb, x * f = f * x := fun x hx => hfcent x (by rwa [sup_comm])
  have hφ7 : rk ↥(commV (Subgroup.zpowers φ)) ≤ 7 := by
    rw [← rkIdx_fixV_zpowers φ]
    exact hd
  obtain ⟨x, hxL, hxord⟩ :=
    exists_inv_mul_conj_order_three_or_five (Classical.choice hAltL) hnL hneL
  obtain ⟨x', hx'K, hx'ord⟩ :=
    exists_inv_mul_conj_order_three_or_five (Classical.choice hAltK) hnK hneK
  obtain ⟨y, hydef⟩ : ∃ y, y = x⁻¹ * (φ * x * φ⁻¹) := ⟨_, rfl⟩
  obtain ⟨y', hy'def⟩ : ∃ y', y' = x'⁻¹ * (φ * x' * φ⁻¹) := ⟨_, rfl⟩
  rw [← hydef] at hxord
  rw [← hy'def] at hx'ord
  have hyL : y ∈ Lb := by rw [hydef]; exact Lb.mul_mem (Lb.inv_mem hxL) (hnL x hxL)
  have hy'K : y' ∈ Kb := by rw [hy'def]; exact Kb.mul_mem (Kb.inv_mem hx'K) (hnK x' hx'K)
  have hry := rk_commV_conj_comm_le hydef
  have hry' := rk_commV_conj_comm_le hy'def
  obtain ⟨hr8, hKy⟩ := rk_commV_eq_eight_and_trivial hW hAltL hAltK hcommLK hford hffix hfcent
    hyL hxord (by omega)
  obtain ⟨hr8', hLy'⟩ := rk_commV_eq_eight_and_trivial hW hAltK hAltL hcommKL hford hffix
    hfcent' hy'K hx'ord (by omega)
  have hyodd : Odd (orderOf y) := by rcases hxord with h | h <;> rw [h] <;> decide
  have hy'odd : Odd (orderOf y') := by rcases hx'ord with h | h <;> rw [h] <;> decide
  have hg : (x * x')⁻¹ * (φ * (x * x') * φ⁻¹) = y * y' := by
    have hc : x'⁻¹ * y = y * x'⁻¹ := (hcommLK y hyL x'⁻¹ (Kb.inv_mem hx'K)).symm
    calc (x * x')⁻¹ * (φ * (x * x') * φ⁻¹)
        = x'⁻¹ * (x⁻¹ * (φ * x * φ⁻¹)) * (φ * x' * φ⁻¹) := by group
      _ = x'⁻¹ * y * (φ * x' * φ⁻¹) := by rw [hydef]
      _ = y * x'⁻¹ * (φ * x' * φ⁻¹) := by rw [hc]
      _ = y * y' := by rw [hy'def]; group
  have hrg := rk_commV_conj_comm_le hg.symm
  have hmemg : ∀ u : W, (y * y') u * u⁻¹ ∈ commV (Subgroup.zpowers (y * y')) := fun u =>
    Subgroup.subset_closure ⟨y * y', Subgroup.mem_zpowers _, u, rfl⟩
  have hUy : commV (Subgroup.zpowers y) ≤ commV (Subgroup.zpowers (y * y')) := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := CFSG.CGT.PushingUpLit.CGT6.Diag.Bound.exists_comm_eq hW hyodd hr
    have h1 : (y * y') u = y u := by rw [MulAut.mul_apply, hKy y' hy'K u hu]
    rw [← h1]
    exact hmemg u
  have hUy' : commV (Subgroup.zpowers y') ≤ commV (Subgroup.zpowers (y * y')) := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := CFSG.CGT.PushingUpLit.CGT6.Diag.Bound.exists_comm_eq hW hy'odd hr
    have hy'u : y' u ∈ commV (Subgroup.zpowers y') := by
      refine commV_apply_mem_of_normalizes (normalizes_zpowers_of_conj_mem ?_) hu
      rw [mul_inv_cancel_right]
      exact Subgroup.mem_zpowers y'
    have h1 : (y * y') u = y' u := by rw [MulAut.mul_apply, hLy' y hyL _ hy'u]
    rw [← h1]
    exact hmemg u
  have hinf : commV (Subgroup.zpowers y) ⊓ commV (Subgroup.zpowers y') = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    exact Subgroup.mem_bot.mpr
      (CFSG.CGT.PushingUpLit.CGT6.Diag.Bound.eq_one_of_mem_commV_zpowers_of_fixed hW hyodd hw.1
        (hLy' y hyL w hw.2))
  have hsum := rk_sup_add_rk_inf (commV (Subgroup.zpowers y)) (commV (Subgroup.zpowers y'))
  rw [hinf, rk_bot] at hsum
  have h16 := rk_mono (sup_le hUy hUy')
  omega

@[expose] def Shape19_1Min (X Lb Kb : Subgroup (MulAut W)) : Prop :=
  Lb ≤ X ∧ Kb ≤ X ∧ IsAlt ↥Lb 5 ∧ IsAlt ↥Kb 5 ∧
    (∀ x ∈ Lb, ∀ y ∈ Kb, x * y = y * x) ∧
  (∀ φ ∈ X,
      ((∀ x ∈ Lb, φ * x * φ⁻¹ ∈ Lb) ∧ (∀ x ∈ Kb, φ * x * φ⁻¹ ∈ Kb)) ∨
      ((∀ x ∈ Lb, φ * x * φ⁻¹ ∈ Kb) ∧ (∀ x ∈ Kb, φ * x * φ⁻¹ ∈ Lb))) ∧
  (∃ f ∈ X, orderOf f = 5 ∧ fixV (Subgroup.zpowers f) = ⊥ ∧
    (∀ φ ∈ X, φ * f * φ⁻¹ ∈ Subgroup.zpowers f) ∧
    ∀ x ∈ Lb ⊔ Kb, x * f = f * x)

theorem shape19_1W_of_min [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {X Lb Kb : Subgroup (MulAut W)} (h : Shape19_1Min X Lb Kb) : Shape19_1W X Lb Kb := by
  obtain ⟨hLX, hKX, hAltL, hAltK, hcomm, hact, f, hfX, hford, hffix, hfnorm, hfcent⟩ := h
  refine ⟨hLX, hKX, hAltL, hAltK, hcomm, hact,
    sixteen_le_rk_of_A5A5 hW hAltL hAltK hcomm hford hffix hfcent,
    ⟨f, hfX, hford, hffix, hfnorm, hfcent⟩, ?_⟩
  intro φ _ hd hnL hnK
  exact centralizes_one_of_normalizes_A5A5 hW hAltL hAltK hcomm hford hffix hfcent hd hnL hnK

theorem invFix_of_shape_min [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {X Lb Kb : Subgroup (MulAut W)} (h : Shape19_1Min X Lb Kb) : s16n9bInvFix X 5 7 :=
  invFix_of_shape_W hW (shape19_1W_of_min hW h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
