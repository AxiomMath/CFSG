module

public import CFSG.Sporadic.ONOddCore.LiftSets

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier

theorem piR_qM :
    piR qM = 1 := by
  have h : qM ∈ piR.ker := by
    rw [ker_piR, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers _
  exact h

theorem piR_candElem
    (k a i : ℕ) : piR (candElem k a i) = piR (lwElem k i) := by
  rw [candElem, map_mul, map_pow, piR_qM, one_pow, mul_one]

theorem mem_lifts_iff {k : ℕ} {e : LiftEntry} :
    e ∈ (recK k).lifts ↔ ∃ i < (recK k).lifts.length, (recK k).lifts.getD i default = e := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, List.getD_eq_getElem _ _ hi⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, (List.getD_eq_getElem _ _ hi).symm⟩

theorem piR_liftHom
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) (m : onM) :
    piR (liftHom hk he m) = tauAut k (piR m) := by
  obtain ⟨i, hi, rfl⟩ := mem_lifts_iff.1 he
  obtain ⟨a, ha, hc⟩ := exists_cand_of_lift hk hi
  obtain ⟨-, himg⟩ := candOK_lift hk ha hc
  have h : piR.comp (liftHom hk he) = (tauAut k).toMonoidHom.comp piR := by
    apply hom_ext_hGens
    intro j hj
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [liftHom_gen hk he hj, himg j hj, piR_candElem, tau_piR_hGen hk hj]
  exact DFunLike.congr_fun h m

theorem orderOf_qM :
    orderOf qM = 4 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_onq

theorem liftHom_injective
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    Function.Injective (liftHom hk he) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 : piR x = 1 := by
    have := piR_liftHom hk he x
    rw [hx, map_one] at this
    exact (map_eq_one_iff _ (tauAut k).injective).1 this.symm
  obtain ⟨m, hm, rfl⟩ := eq_qM_pow_of_piR h1
  rw [map_pow, liftHom_q hk he, ← pow_mul] at hx
  have hdvd := orderOf_dvd_of_pow_eq_one hx
  rw [orderOf_qM] at hdvd
  have hp := (lift_form hk he).2.2
  rw [Subgroup.mem_bot]
  have hm0 : m = 0 := by
    rcases hp with hp | hp <;> rw [hp] at hdvd <;> omega
  rw [hm0, pow_zero]

@[expose] def liftAut
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    MulAut onM :=
  MulEquiv.ofBijective (liftHom hk he) (Finite.injective_iff_bijective.1 (liftHom_injective hk he))

theorem liftAut_apply
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) (m : onM) :
    liftAut hk he m = liftHom hk he m := rfl

theorem liftAut_mem
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    liftAut hk he ∈ liftSet k := by
  refine MulEquiv.ext fun r => ?_
  obtain ⟨m, rfl⟩ := piR_surjective r
  rw [descendAut_piR, liftAut_apply, piR_liftHom hk he]

theorem liftAut_eq_liftFun
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    ⇑(liftAut hk he) = liftFun e := liftHom_eq_liftFun hk he

theorem liftAut_q
    {k : ℕ} (hk : k < 12) {e : LiftEntry} (he : e ∈ (recK k).lifts) :
    liftAut hk he qM = qM ^ e.power := liftHom_q hk he

theorem digit_mk {a₀ a₁ a₂ : ℕ} (_h₀ : a₀ < 4) (h₁ : a₁ < 4) (h₂ : a₂ < 4) :
    digit (16 * a₀ + 4 * a₁ + a₂) 0 = a₀ ∧ digit (16 * a₀ + 4 * a₁ + a₂) 1 = a₁ ∧
      digit (16 * a₀ + 4 * a₁ + a₂) 2 = a₂ := by
  simp only [digit]
  omega

theorem exists_candidate
    {k : ℕ} (hk : k < 12) {β : MulAut onM} (hβ : β ∈ liftSet k) :
    ∃ a < 64, ∀ i < 3, β (hGen i) = candElem k a i := by
  obtain ⟨a₀, h₀, e₀⟩ := fibre hk hβ (i := 0) (by norm_num)
  obtain ⟨a₁, h₁, e₁⟩ := fibre hk hβ (i := 1) (by norm_num)
  obtain ⟨a₂, h₂, e₂⟩ := fibre hk hβ (i := 2) (by norm_num)
  obtain ⟨d₀, d₁, d₂⟩ := digit_mk h₀ h₁ h₂
  refine ⟨16 * a₀ + 4 * a₁ + a₂, by omega, fun i hi => ?_⟩
  interval_cases i
  · rw [candElem, d₀, e₀]
  · rw [candElem, d₁, e₁]
  · rw [candElem, d₂, e₂]

theorem eq_liftAut_of_cand
    {k : ℕ} (hk : k < 12) {β : MulAut onM} {a : ℕ}
    (hβa : ∀ i < 3, β (hGen i) = candElem k a i) {i : ℕ} (hi : i < (recK k).lifts.length)
    (himg : ∀ j < 3, liftImg ((recK k).lifts.getD i default) j = candElem k a j) :
    β = liftAut hk (getD_mem hi default) := by
  have h : β.toMonoidHom = (liftAut hk (getD_mem hi default)).toMonoidHom := by
    apply hom_ext_hGens
    intro j hj
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hβa j hj, liftAut_apply, liftHom_gen hk _ hj, himg j hj]
  exact MulEquiv.toMonoidHom_injective h

theorem mem_liftSet_iff
    {k : ℕ} (hk : k < 12) {β : MulAut onM} :
    β ∈ liftSet k ↔
      ∃ i, ∃ hi : i < (recK k).lifts.length, β = liftAut hk (getD_mem hi default) := by
  constructor
  · intro hβ
    obtain ⟨a, ha, hβa⟩ := exists_candidate hk hβ
    cases hc : (liftData.cands.getD k []).getD a default with
    | rel w w' => exact (not_hom_of_rel hk ha hc β.toMonoidHom hβa).elim
    | lift i =>
      obtain ⟨hi, himg⟩ := candOK_lift hk ha hc
      exact ⟨i, hi, eq_liftAut_of_cand hk hβa hi himg⟩
  · rintro ⟨i, hi, rfl⟩
    exact liftAut_mem hk _

theorem liftAut_injective
    {k : ℕ} (hk : k < 12) {i j : ℕ} (hi : i < (recK k).lifts.length)
    (hj : j < (recK k).lifts.length)
    (h : liftAut hk (getD_mem hi default) = liftAut hk (getD_mem hj default)) : i = j := by
  obtain ⟨a, ha, hca⟩ := exists_cand_of_lift hk hi
  obtain ⟨b, hb, hcb⟩ := exists_cand_of_lift hk hj
  obtain ⟨-, himga⟩ := candOK_lift hk ha hca
  obtain ⟨-, himgb⟩ := candOK_lift hk hb hcb
  have hab : ∀ t < 3, candElem k a t = candElem k b t := by
    intro t ht
    rw [← himga t ht, ← himgb t ht, ← liftHom_gen hk (getD_mem hi default) ht,
      ← liftHom_gen hk (getD_mem hj default) ht, ← liftAut_apply, ← liftAut_apply, h]
  have hdig : ∀ t < 3, digit a t = digit b t := by
    intro t ht
    have e := hab t ht
    rw [candElem, candElem, mul_right_inj] at e
    have hda : digit a t < 4 := by interval_cases t <;> simp only [digit] <;> omega
    have hdb : digit b t < 4 := by interval_cases t <;> simp only [digit] <;> omega
    exact pow_injOn_Iio_orderOf (by rw [orderOf_qM]; exact hda) (by rw [orderOf_qM]; exact hdb) e
  have hab' : a = b := by
    have h0 := hdig 0 (by norm_num)
    have h1 := hdig 1 (by norm_num)
    have h2 := hdig 2 (by norm_num)
    simp only [digit] at h0 h1 h2
    omega
  rw [hab', hcb] at hca
  exact (Cand.lift.inj hca).symm

theorem ncard_liftSet
    {k : ℕ} (hk : k < 12) : (liftSet k).ncard = (recK k).lifts.length := by
  have hset : liftSet k = (fun i : Fin (recK k).lifts.length =>
      liftAut hk (getD_mem i.2 default)) '' Set.univ := by
    ext β
    rw [mem_liftSet_iff hk]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨i, -, rfl⟩
      exact ⟨i, i.2, rfl⟩
  rw [hset, Set.ncard_image_of_injective _ (fun i j h => Fin.ext (liftAut_injective hk i.2 j.2 h)),
    Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

end CFSG.Sporadic.ONOddCore
