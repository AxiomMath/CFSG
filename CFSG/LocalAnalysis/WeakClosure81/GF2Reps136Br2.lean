module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Br1
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136BridgeNat
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136BridgeOrder
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136BridgeA7
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136IrrCorr
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_mQuot_eq_rk_map (C V : Subgroup W) :
    E3.mQuot V C = rk ↥(V.map (QuotientGroup.mk' C)) := by
  have h := Subgroup.relIndex_ker (QuotientGroup.mk' C : W →* W ⧸ C) (K := V)
  rw [QuotientGroup.ker_mk'] at h
  rw [E3.mQuot, rk, h]

private theorem w1369_tcost_le_rk_top (t : MulAut W) (L : Subgroup (MulAut W)) :
    tcost t L (Wd L) ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
  let X := commSub (Wd L) (Subgroup.zpowers t)
  have hXA : X ≤ commSub ⊤ (Subgroup.zpowers t) := commSub_mono le_top le_rfl
  have hCmap : (Cd L).map (QuotientGroup.mk' (Cd L)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨y, hy, rfl⟩
    rw [Subgroup.mem_bot]
    exact MonoidHom.mem_ker.mp (by rwa [QuotientGroup.ker_mk'])
  calc tcost t L (Wd L)
      = E3.mQuot (X ⊔ Cd L) (Cd L) := rfl
    _ = rk ↥((X ⊔ Cd L).map (QuotientGroup.mk' (Cd L))) :=
        w1369_mQuot_eq_rk_map (Cd L) (X ⊔ Cd L)
    _ = rk ↥(X.map (QuotientGroup.mk' (Cd L))) := by
        rw [Subgroup.map_sup, hCmap, sup_bot_eq]
    _ ≤ rk ↥X := padicValNat_two_le_of_dvd (card_subgroup_pos X).ne'
        (Subgroup.card_map_dvd (H := X) (QuotientGroup.mk' (Cd L)))
    _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := rk_mono hXA

private theorem w1369_conc4_135_of_a7Four {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    {m : ℕ} (h : A7Four H U Z) : Conc4_135 H U Z m := by
  unfold Conc4_135
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

private theorem w1369_stabPair_zpowers {U Z : Subgroup W} {t : MulAut W}
    (htU : ∀ u ∈ U, t u ∈ U) (htZ : ∀ z ∈ Z, t z ∈ Z) :
    StabPair (Subgroup.zpowers t) U Z := by
  intro a ha
  exact ⟨fun u hu => (mem_stabSub.mp (Subgroup.zpowers_le.2
      (mem_stabSub_of_invariant htU (inv_mem_of_forall_mem t htU)) ha) u).2 hu,
    fun z hz => (mem_stabSub.mp (Subgroup.zpowers_le.2
      (mem_stabSub_of_invariant htZ (inv_mem_of_forall_mem t htZ)) ha) z).2 hz⟩

theorem bridge_ineq (h135 : W4Lem13_5) (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L) (hf : FaithOn L (Wd L) (Cd L))
    (hirr : IsIrrOn L (Wd L) (Cd L)) :
    Conc4_135 L (Wd L) (Cd L) (tcost t L (Wd L)) ∨ Row1Ineq L (Wd L) (Cd L) (tcost t L (Wd L)) := by
  classical
  have hZU : Cd L ≤ Wd L := hirr.1.le
  have hstabL : StabPair L (Wd L) (Cd L) := fun a ha => ⟨hirr.2.1 a ha, hirr.2.2.1 a ha⟩
  have hfixL : L.map (MulAut.conj t).toMonoidHom = L := c.hfix L c.comp
  have htN : t ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfixL
  obtain ⟨hWdmap, hCdmap, -⟩ := irr_stab (L := L) htN
  have htU : ∀ u ∈ Wd L, t u ∈ Wd L := fun u hu => by
    rw [← hWdmap]
    exact Subgroup.mem_map_of_mem t.toMonoidHom hu
  have htZ : ∀ z ∈ Cd L, t z ∈ Cd L := fun z hz => by
    rw [← hCdmap]
    exact Subgroup.mem_map_of_mem t.toMonoidHom hz
  have hstab_t : StabPair (Subgroup.zpowers t) (Wd L) (Cd L) := w1369_stabPair_zpowers htU htZ
  let tbar : MulAut (Sect (Wd L) (Cd L)) := secAut (Wd L) (Cd L) t htU htZ
  have htbar2 : tbar ^ 2 = 1 := by
    rw [pow_two]
    ext m
    induction m using QuotientGroup.induction_on with
    | H u =>
      rw [MulAut.mul_apply, MulAut.one_apply, secAut_mk, secAut_mk]
      congr 1
      exact Subtype.ext (by
        have ht2w : t * t = 1 := by
          have hpow := pow_orderOf_eq_one t
          rw [c.std.t2] at hpow
          rwa [pow_two] at hpow
        have h := congrFun (congrArg (fun f : MulAut W => (f : W → W)) ht2w) (u : W)
        simpa [MulAut.mul_apply] using h)
  have hLne : L ≠ ⊥ := by
    intro hbot
    haveI : Subsingleton ↥L := by rw [hbot]; infer_instance
    haveI : Nontrivial (↥L ⧸ Subgroup.center ↥L) := c.comp.2.2.2.toNontrivial
    exact (not_subsingleton_iff_nontrivial.mpr (inferInstance : Nontrivial _))
      (inferInstance : Subsingleton (↥L ⧸ Subgroup.center ↥L))
  have htbar1 : tbar ≠ 1 := by
    intro h1
    have hsec_t : secSub (Wd L) (Cd L) (Subgroup.zpowers t) = ⊥ := by
      have h1' : secAut (Wd L) (Cd L) t htU htZ = 1 := h1
      rw [secSub_zpowers htU htZ, h1', Subgroup.zpowers_one_eq_bot]
    have hsec_L : secSub (Wd L) (Cd L) L = ⊥ := by
      have h := secSub_commutator hstabL hstab_t
      rw [c.Lt, hsec_t, Subgroup.commutator_bot_right] at h
      exact h.symm
    obtain ⟨e⟩ := mulEquiv_secSub hstabL hf
    haveI : Subsingleton ↥(secSub (Wd L) (Cd L) L) := by rw [hsec_L]; infer_instance
    haveI : Subsingleton ↥L := ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩
    exact hLne (Subgroup.eq_bot_of_subsingleton (H := L))
  have htbar_ord : orderOf tbar = 2 := orderOf_eq_prime htbar2 htbar1
  have hcost0 : rk ↥(commSub ⊤ (Subgroup.zpowers tbar)) = tcost t L (Wd L) :=
    rk_secAut_comm (Z := Cd L) hZU htU htZ
  have hm_eq : E3.mQuot ⊤ (fixV (Subgroup.zpowers tbar)) = tcost t L (Wd L) := by
    rw [show E3.mQuot ⊤ (fixV (Subgroup.zpowers tbar)) = rkIdx (fixV (Subgroup.zpowers tbar))
        from by
      unfold E3.mQuot rkIdx
      rw [Subgroup.relIndex_top_right]]
    rw [rkIdx_fixV_zpowers, commV_eq_commSub]
    exact hcost0
  have hm_le : E3.mQuot ⊤ (fixV (Subgroup.zpowers tbar)) ≤ 3 := by
    rw [hm_eq]
    exact (w1369_tcost_le_rk_top t L).trans c.std.cost
  have h135ctx : Is135Context (secSub (Wd L) (Cd L) (L ⊔ Subgroup.zpowers t))
      (secSub (Wd L) (Cd L) L) := is135_section hw2 c hf hirr
  have hmem : tbar ∈ secSub (Wd L) (Cd L) (L ⊔ Subgroup.zpowers t) := by
    rw [secSub_sup hstabL hstab_t, secSub_zpowers htU htZ]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers tbar)
  have hconcl : W4Lem13_5Concl (Sect (Wd L) (Cd L))
      (secSub (Wd L) (Cd L) (L ⊔ Subgroup.zpowers t)) (secSub (Wd L) (Cd L) L) tbar :=
    (w4Lem13_5_iff_concl.mp h135) (Sect (Wd L) (Cd L)) (sect_exp_two hw2 (Wd L) (Cd L))
      (secSub (Wd L) (Cd L) (L ⊔ Subgroup.zpowers t)) (secSub (Wd L) (Cd L) L) tbar
      h135ctx hmem htbar_ord hm_le
  unfold W4Lem13_5Concl at hconcl
  rw [hm_eq] at hconcl
  rcases hconcl with ⟨n, a, ha, hrow1⟩ | hrest
  · exact bridge_rows_nat hZU hstabL hf (Or.inl ⟨n, a, ha, hrow1⟩)
  rcases hrest with ⟨n, hrow2⟩ | hrest
  · exact bridge_rows_nat hZU hstabL hf (Or.inr (Or.inl ⟨n, hrow2⟩))
  rcases hrest with hrow3 | hrest
  · exact Or.inl (bridge_rows_order hw2 hZU hstabL hf hirr (Or.inl hrow3))
  rcases hrest with hrow4 | hrest
  · exact Or.inl (bridge_rows_order hw2 hZU hstabL hf hirr (Or.inr (Or.inl hrow4)))
  rcases hrest with ⟨n, hrow5⟩ | hrest
  · exact bridge_rows_nat hZU hstabL hf (Or.inr (Or.inr ⟨n, hrow5⟩))
  rcases hrest with hrow6 | hrest
  · exact Or.inl (w1369_conc4_135_of_a7Four (bridge_row_a7 hw2 hZU hstabL hf hirr hrow6))
  rcases hrest with hrow7 | hrest
  · exact Or.inl (bridge_rows_order hw2 hZU hstabL hf hirr
      (Or.inr (Or.inr (Or.inl hrow7))))
  rcases hrest with hrow8 | hrest
  · exact Or.inl (bridge_rows_order hw2 hZU hstabL hf hirr
      (Or.inr (Or.inr (Or.inr (Or.inl hrow8)))))
  rcases hrest with hrow9 | hrest
  · exact Or.inl (bridge_rows_order hw2 hZU hstabL hf hirr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hrow9))))))
  rcases hrest with hrow10 | hrow11
  · exact Or.inl (bridge_rows_order hw2 hZU hstabL hf hirr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hrow10)))))))
  · exact Or.inl (bridge_rows_order hw2 hZU hstabL hf hirr
      (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr hrow11))

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
