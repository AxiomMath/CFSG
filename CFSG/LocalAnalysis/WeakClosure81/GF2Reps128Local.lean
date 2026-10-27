module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Swap

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem rk_commSub_eq_rkIdx_autSub {C I : Subgroup W} {t : MulAut W} (htC : t ∈ stabSub C)
    (hIt : I.map t.toMonoidHom = I) :
    rk ↥(commSub (I.map (QuotientGroup.mk' C)) (Subgroup.zpowers (quotHom C ⟨t, htC⟩))) =
      rkIdx (fixV (autSub (autQuot (Subgroup.zpowers t) C) (I.map (QuotientGroup.mk' C)))) := by
  have htS := mem_secStab_of_map_eq htC hIt
  set I' := I.map (QuotientGroup.mk' C) with hI'
  set t₀ : ↥(secStab C I') := ⟨⟨t, htC⟩, htS⟩ with ht₀
  have hT : autSub (autQuot (Subgroup.zpowers t) C) I' = Subgroup.zpowers (secHom C I' t₀) :=
    autSub_autQuot_zpowers t₀
  rw [hT]
  set τ := quotHom C ⟨t, htC⟩ with hτ
  have hτI : τ ∈ stabSub I' := htS
  have hzI : ∀ x ∈ Subgroup.zpowers τ, ∀ w ∈ I', x w ∈ I' := fun x hx w hw =>
    (((Subgroup.zpowers_le.mpr hτI) hx) w).mpr hw
  have h1 : rk ↥(commV (Subgroup.zpowers (secHom C I' t₀))) =
      rk ↥(commSub I' (Subgroup.zpowers τ)) := rk_commV_resHom hτI hzI
  have h5 : rk ↥(commV (Subgroup.zpowers (secHom C I' t₀))) +
      rk ↥(fixV (Subgroup.zpowers (secHom C I' t₀))) = rk ↥I' :=
    rk_commV_add_rk_fixV (secHom C I' t₀)
  have h6 : rk ↥(fixV (Subgroup.zpowers (secHom C I' t₀))) +
      rkIdx (fixV (Subgroup.zpowers (secHom C I' t₀))) = rk ↥I' :=
    rk_add_rkIdx (fixV (Subgroup.zpowers (secHom C I' t₀)))
  have h7 : rk ↥(commV (Subgroup.zpowers (secHom C I' t₀))) =
      rkIdx (fixV (Subgroup.zpowers (secHom C I' t₀))) := by
    have h8 := h5.trans h6.symm
    omega
  exact h1.symm.trans h7

theorem exists_rk_commSub_eq (hD : W4Lem6_3Swap) (hW : ∀ w : W, w ^ 2 = 1)
    {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X)
    {t : MulAut W} (ht : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : rkIdx (fixV (Subgroup.zpowers t)) < dMinDeg ↥L)
    (hmove : L.map (MulAut.conj t).toMonoidHom ≠ L) (htC : t ∈ stabSub (fixV H))
    {I : Subgroup W} (hI : I ∈ irrSet H) (hIt : I.map t.toMonoidHom = I)
    (hLI : ¬ commSub I L ≤ fixV H) :
    ∃ e : ℕ, dMinDeg ↥L ≤ 2 * e ∧
      rk ↥(commSub (I.map (QuotientGroup.mk' (fixV H)))
        (Subgroup.zpowers (quotHom (fixV H) ⟨t, htC⟩))) = e := by
  obtain ⟨e, hde, -, hrk, -⟩ := exists_o4_of_map_ne hD hW hL hH ht ht2 hm hmove hI hIt hLI
  obtain ⟨-, -, hdL⟩ := isQuasisimple_autSub hL hH hI hLI
  exact ⟨e, hdL.trans hde.le, (rk_commSub_eq_rkIdx_autSub htC hIt).trans hrk⟩

omit [Finite W] in
theorem map_mk_inf_eq_bot {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) {I U : Subgroup W} (hI : I ∈ irrSet H) (hU : U ∈ irrSet H)
    (hIU : I ⊔ fixV H ≠ U ⊔ fixV H) :
    U.map (QuotientGroup.mk' (fixV H)) ⊓ I.map (QuotientGroup.mk' (fixV H)) = ⊥ := by
  obtain ⟨-, -, hHY, hn, -, -⟩ := h_facts hL hH
  have hHstab : H ≤ stabSub (fixV H) := hHY.trans (le_stabSub_fixV hn)
  have hirrU := map_mk_stable_irr hHstab hU
  have hirrI := map_mk_stable_irr hHstab hI
  rcases hirrU.2 _ (stableUnder_inf hirrU.1 hirrI.1) inf_le_left with h | h
  · exact h
  · exfalso
    have hle : U.map (QuotientGroup.mk' (fixV H)) ≤ I.map (QuotientGroup.mk' (fixV H)) :=
      h.ge.trans inf_le_right
    have hUne : U.map (QuotientGroup.mk' (fixV H)) ≠ ⊥ := by
      intro h0
      apply not_le_fixV_of_mem_irrSet hU
      have h2 : U ≤ (QuotientGroup.mk' (fixV H)).ker := by
        rw [← Subgroup.map_eq_bot_iff, h0]
      rwa [QuotientGroup.ker_mk'] at h2
    rcases hirrI.2 _ hirrU.1 hle with h' | h'
    · exact hUne h'
    · apply hIU
      have h3 := congrArg (Subgroup.comap (QuotientGroup.mk' (fixV H))) h'
      rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h3
      exact h3.symm

theorem rk_commSub_add_le_rkIdx {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) {t : MulAut W} (htC : t ∈ stabSub (fixV H))
    {U I : Subgroup W} (hU : U ∈ irrSet H) (hUt : U.map t.toMonoidHom = U) (hI : I ∈ irrSet H)
    (hIt : I.map t.toMonoidHom = I) (hIU : I ⊔ fixV H ≠ U ⊔ fixV H) :
    rk ↥(commSub (U.map (QuotientGroup.mk' (fixV H)))
        (Subgroup.zpowers (quotHom (fixV H) ⟨t, htC⟩))) +
      rk ↥(commSub (I.map (QuotientGroup.mk' (fixV H)))
        (Subgroup.zpowers (quotHom (fixV H) ⟨t, htC⟩))) ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have hτz : ∀ {J : Subgroup W}, J.map t.toMonoidHom = J →
      ∀ x ∈ Subgroup.zpowers (quotHom (fixV H) ⟨t, htC⟩),
        ∀ w ∈ J.map (QuotientGroup.mk' (fixV H)), x w ∈ J.map (QuotientGroup.mk' (fixV H)) := by
    intro J hJt x hx w hw
    have hτJ : quotHom (fixV H) ⟨t, htC⟩ ∈ stabSub (J.map (QuotientGroup.mk' (fixV H))) :=
      mem_secStab_of_map_eq htC hJt
    exact (((Subgroup.zpowers_le.mpr hτJ) hx) w).mpr hw
  have hUI := map_mk_inf_eq_bot hL hH hI hU hIU
  set τ := quotHom (fixV H) ⟨t, htC⟩ with hτ
  have hA : commSub (U.map (QuotientGroup.mk' (fixV H))) (Subgroup.zpowers τ) ≤
      U.map (QuotientGroup.mk' (fixV H)) := commSub_le_of_invariant (hτz hUt)
  have hB' : commSub (I.map (QuotientGroup.mk' (fixV H))) (Subgroup.zpowers τ) ≤
      I.map (QuotientGroup.mk' (fixV H)) := commSub_le_of_invariant (hτz hIt)
  have hAB := eq_bot_iff.mpr ((inf_le_inf hA hB').trans hUI.le)
  have h2 := rk_sup_add_rk_inf (commSub (U.map (QuotientGroup.mk' (fixV H)))
    (Subgroup.zpowers τ)) (commSub (I.map (QuotientGroup.mk' (fixV H))) (Subgroup.zpowers τ))
  rw [hAB, rk_bot] at h2
  have h3 : rk ↥(commSub (U.map (QuotientGroup.mk' (fixV H))) (Subgroup.zpowers τ) ⊔
      commSub (I.map (QuotientGroup.mk' (fixV H))) (Subgroup.zpowers τ)) ≤
        rk ↥(commV (Subgroup.zpowers τ)) := by
    refine rk_mono (sup_le ?_ ?_) <;>
    · rw [commV_eq_commSub (Subgroup.zpowers τ)]
      exact commSub_mono le_top le_rfl
  have h4 := rk_commV_add_rk_fixV τ
  have h5 := rk_add_rkIdx (fixV (Subgroup.zpowers τ))
  have h6 := rkIdx_fixV_quotHom_le htC
  rw [← hτ] at h6
  omega

theorem sup_fixV_eq_of_not_commSub_le (hD : W4Lem6_3Swap) (hW : ∀ w : W, w ^ 2 = 1)
    {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X)
    {t : MulAut W} (ht : t ∈ Y) (ht2 : orderOf t = 2)
    (hfix : ∀ I ∈ irrSet H, I.map t.toMonoidHom = I)
    (hm : rkIdx (fixV (Subgroup.zpowers t)) < dMinDeg ↥L)
    (hmove : L.map (MulAut.conj t).toMonoidHom ≠ L) {U I : Subgroup W} (hU : U ∈ irrSet H)
    (hLU : ¬ commSub U L ≤ fixV H) (hI : I ∈ irrSet H) (hLI : ¬ commSub I L ≤ fixV H) :
    I ⊔ fixV H = U ⊔ fixV H := by
  by_contra hIU
  obtain ⟨-, -, -, hn, -, -⟩ := h_facts hL hH
  have htC : t ∈ stabSub (fixV H) := le_stabSub_fixV hn ht
  obtain ⟨eU, hdU, hrkU⟩ :=
    exists_rk_commSub_eq hD hW hL hH ht ht2 hm hmove htC hU (hfix U hU) hLU
  obtain ⟨eI, hdI, hrkI⟩ :=
    exists_rk_commSub_eq hD hW hL hH ht ht2 hm hmove htC hI (hfix I hI) hLI
  have h := rk_commSub_add_le_rkIdx hL hH htC hU (hfix U hU) hI (hfix I hI) hIU
  omega

theorem local_cases (hD : W4Lem6_3Swap) (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hO : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X)
    {t : MulAut W} (ht : t ∈ Y) (ht2 : orderOf t = 2)
    (hfix : ∀ I ∈ irrSet H, I.map t.toMonoidHom = I)
    (hm : rkIdx (fixV (Subgroup.zpowers t)) < dMinDeg ↥L)
    {U : Subgroup W} (hU : U ∈ irrSet H) (hLU : ¬ commSub U L ≤ fixV H)
    (htU : ¬ commSub U (Subgroup.zpowers t) ≤ fixV H) :
    (L.map (MulAut.conj t).toMonoidHom = L ∧ (¬ ∀ x ∈ L, t * x = x * t) ∧
        ∀ X ∈ conjSet L Y, ¬ commSub U X ≤ fixV H → X = L) ∨
      (L.map (MulAut.conj t).toMonoidHom ≠ L ∧
        (∀ X ∈ conjSet L Y, ¬ commSub U X ≤ fixV H →
          X = L ∨ X = L.map (MulAut.conj t).toMonoidHom) ∧
        ∃ e : ℕ, dMinDeg ↥L = 2 * e ∧
          IsNaturalO4Plus (autSub (autQuot (L ⊔ L.map (MulAut.conj t).toMonoidHom ⊔
            Subgroup.zpowers t) (fixV H)) (U.map (QuotientGroup.mk' (fixV H)))) e ∧
          rkIdx (fixV (autSub (autQuot (Subgroup.zpowers t) (fixV H))
            (U.map (QuotientGroup.mk' (fixV H))))) = e) := by
  have hUt := hfix U hU
  have hun : ∀ X ∈ conjSet L Y, ¬ commSub U X ≤ fixV H →
      X = L ∨ X = L.map (MulAut.conj t).toMonoidHom := by
    intro X hX hXU
    by_contra hne
    push Not at hne
    exact hXU (commSub_le_of_ne_of_ne hW hL hH ht ht2 hm hU hUt hLU htU hX hne.1 hne.2)
  by_cases hLt : L.map (MulAut.conj t).toMonoidHom = L
  · left
    refine ⟨hLt, not_commute_of_not_commSub_le hW hL hH ht hm hU hUt htU
      (self_mem_conjSet L Y) hLU, fun X hX hXU => ?_⟩
    rcases hun X hX hXU with h | h
    · exact h
    · exact h.trans hLt
  · right
    refine ⟨hLt, hun, ?_⟩
    obtain ⟨e, hde, hnat, hrk, -⟩ := exists_o4_of_map_ne hD hW hL hH ht ht2 hm hLt hU hUt hLU
    refine ⟨e, ?_, hnat, hrk⟩
    rw [← hde]
    obtain ⟨h1, hLH, hHY, hn, hnorm, hne⟩ := h_facts hL hH
    have hstab : Y ≤ stabSub (fixV H) := le_stabSub_fixV hn
    have hHstab : H ≤ stabSub (fixV H) := hHY.trans hstab
    have hLC : L ≤ stabSub (fixV H) := hLH.trans hHstab
    have hLS := fun l (hl : l ∈ L) => mem_secStab_of_mem hL hH hU (hLH hl) (hLC hl)
    have htop : (⨆ I ∈ irrSet H, I) = ⊤ :=
      ((w4Lem12_5_holds W hW Y hO hB H hne hHY hnorm).2 L hL h1).1.1
    have hinj : Function.Injective (secRes hLC hLS) := by
      rw [injective_iff_map_eq_one]
      rintro ⟨l, hl⟩ hl1
      have hlU : ∀ u ∈ U ⊔ fixV H, l u * u⁻¹ ∈ fixV H := by
        intro u hu
        obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu
        have h2 := congrArg (fun φ : ↥(autSub (autQuot L (fixV H)) (U.map (QuotientGroup.mk' (fixV H)))) =>
          (((φ : MulAut ↥(U.map (QuotientGroup.mk' (fixV H)))) ⟨_, a, ha, rfl⟩ :
            ↥(U.map (QuotientGroup.mk' (fixV H)))) : W ⧸ fixV H)) hl1
        simp only [secRes_apply, OneMemClass.coe_one, MulAut.one_apply, QuotientGroup.mk'_apply,
          quotHom_mk] at h2
        have h3 := (mk_eq_mk_iff _ _).mp h2
        rw [map_mul, hc l (hLH hl), mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
        exact h3
      have hall : ∀ w : W, l w * w⁻¹ ∈ fixV H := by
        intro w
        have hw : w ∈ ⨆ I ∈ irrSet H, I := by rw [htop]; trivial
        rw [iSup_subtype'] at hw
        refine Subgroup.iSup_induction (fun I : irrSet H => (I : Subgroup W))
          (C := fun w => l w * w⁻¹ ∈ fixV H) hw ?_ ?_ ?_
        · intro I w hw
          by_cases hLI : commSub (I : Subgroup W) L ≤ fixV H
          · exact hLI (Subgroup.subset_closure ⟨l, hl, w, hw, rfl⟩)
          · by_cases hIU : (I : Subgroup W) ⊔ fixV H = U ⊔ fixV H
            · exact hlU w (hIU ▸ le_sup_left (α := Subgroup W) hw)
            · exact absurd (sup_fixV_eq_of_not_commSub_le hD hW hL hH ht ht2 hfix hm hLt hU hLU
                I.2 hLI) hIU
        · simp
        · intro a b ha hb
          have he : l (a * b) * (a * b)⁻¹ = (l a * a⁻¹) * (l b * b⁻¹) := by
            rw [map_mul, mul_inv, mul_mul_mul_comm]
          rw [he]
          exact (fixV H).mul_mem ha hb
      exact Subtype.ext (eq_one_of_mem_fixV_quot hW hO hB hL hH (hHY (hLH hl)) hall)
    exact dMinDeg_congr (MulEquiv.ofBijective (secRes hLC hLS) ⟨hinj, secRes_surjective hLC hLS⟩)

end CFSG.LocalAnalysis.WeakClosure81
