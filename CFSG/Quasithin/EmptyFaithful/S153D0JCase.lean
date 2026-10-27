module

public import CFSG.Quasithin.EmptyFaithful.S153D0RCase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem Sgp153_le_normalizer_Yp (h : Hyp15310 G T Mc M V₁ V₂ Yp t) :
    Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := by
  rcases h.cases with hY | ⟨-, hY⟩
  · rw [hY]
    exact fun g hg => le_normalizer_Y153 Mc M (h.hyp.T_le hg.1)
  · rw [hY]
    exact Sgp153_le_normalizer_Yplus h.hyp

theorem Yp_le_thompsonJ (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) {I : Subgroup G}
    (hI : IsHPlus Yp (Sgp153 T V₁) M I)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T M : Set G)) : Yp ≤ thompsonJ I := by
  classical
  have hh := h.hyp
  obtain ⟨A, B, hc⟩ := exists_starCoords h113 hh h.decomp
  set Ys : Subgroup (OTwoQuot M) := imageOTwoQuot M (Y153 Mc M) with hYs
  have hYpY : Yp ≤ Y153 Mc M := h.Yp_le_Y153
  have hYpI : Yp ≤ I := le_sup_left.trans hI.1.1
  have hAY : A ∈ Ys := imageOTwoQuot_mono inf_le_left hc.A_mem
  have hBY : B ∈ Ys := hc.B_mem
  have hz := hc.comm_mem
  have hZ := Zstar_structure h113 hh hAY hBY hz hc.gen
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := h.lemma_15_3_11_one h11 h113 hI
  have hJS : thompsonJ T ≤ Sgp153 T V₁ := hc.J_le hJ
  have hJTI : thompsonJ T ≤ thompsonJ I :=
    (GammaExtra.thompsonJ_eq_of_le hJS inf_le_left).symm.le.trans
      (thompsonJ_le_thompsonJ_of_isSylowTwoOf hsyl)
  have hIN : I ≤ Subgroup.normalizer (thompsonJ I : Set G) :=
    Subgroup.le_normalizer.trans (GammaExtra.normalizer_le_normalizer_thompsonJ I)
  have hSYp : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := Sgp153_le_normalizer_Yp h
  set Q : Subgroup G := Yp ⊓ thompsonJ I with hQ
  have hcommN : ∀ (j : G) (hj : j ∈ thompsonJ T) (u : OTwoQuot M), u ∈ imageOTwoQuot M Yp →
      u * starOf hh j (thompsonJ_le_self T hj) * u⁻¹ * (starOf hh j (thompsonJ_le_self T hj))⁻¹ ∈
        imageOTwoQuot M Q := by
    intro j hj u hu
    obtain ⟨y, hyM, hyYp, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    have hjT : j ∈ T := thompsonJ_le_self T hj
    have hjM : j ∈ M := hh.T_le hjT
    have hjN : j ∈ Subgroup.normalizer (Yp : Set G) := hSYp (hJS hj)
    have hjJ : j ∈ thompsonJ I := hJTI hj
    have hyJ : y * j * y⁻¹ ∈ thompsonJ I :=
      (Subgroup.mem_normalizer_iff.mp (hIN (hYpI hyYp)) j).mp hjJ
    have hcQ : y * j * y⁻¹ * j⁻¹ ∈ Q := by
      refine ⟨?_, Subgroup.mul_mem _ hyJ (Subgroup.inv_mem _ hjJ)⟩
      have h1 : j * y⁻¹ * j⁻¹ ∈ Yp :=
        (Subgroup.mem_normalizer_iff.mp hjN _).mp (Subgroup.inv_mem _ hyYp)
      have e : y * j * y⁻¹ * j⁻¹ = y * (j * y⁻¹ * j⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hyYp h1
    refine mem_imageOTwoQuot_iff.mpr ⟨y * j * y⁻¹ * j⁻¹,
      M.mul_mem (M.mul_mem (M.mul_mem hyM hjM) (M.inv_mem hyM)) (M.inv_mem hjM), hcQ, ?_⟩
    show (QuotientGroup.mk (⟨y, hyM⟩ * ⟨j, hjM⟩ * ⟨y, hyM⟩⁻¹ * ⟨j, hjM⟩⁻¹ : ↥M) : OTwoQuot M) = _
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv]
    rfl
  set N' : Subgroup (OTwoQuot M) := imageOTwoQuot M Q with hN'
  obtain ⟨j₂, hj₂, ⟨⟨cA, hcA, hA⟩, ⟨cB, hcB, hB⟩⟩⟩ := hc.inv₂ hJ
  obtain ⟨j₁, hj₁, ⟨⟨cA', hcA', hA'⟩, ⟨cB', hcB', hB'⟩⟩⟩ := hc.inv₁ hJ
  rw [zpow_neg_one] at hA
  rw [zpow_one] at hB
  rw [zpow_one] at hA'
  rw [zpow_neg_one] at hB'
  obtain ⟨hAYp, hzYp, hYpgen⟩ : A ∈ imageOTwoQuot M Yp ∧ ⁅A, B⁆ ∈ imageOTwoQuot M Yp ∧
      (∀ y ∈ imageOTwoQuot M Yp, ∃ (i j : ℤ), ∃ c ∈ ZstarOf hh,
        y = B ^ i * A ^ j * c ∧ (i ≠ 0 → B ∈ imageOTwoQuot M Yp)) := by
    rcases h.cases with hY | ⟨-, hY⟩
    · rw [hY]
      refine ⟨hAY, hz.2, fun y hy => ?_⟩
      obtain ⟨i, j, c, hc', rfl⟩ := hc.gen y hy
      exact ⟨i, j, c, hc', rfl, fun _ => hBY⟩
    · have hYpK : imageOTwoQuot M Yp =
          imageOTwoQuot M (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) := by
        rw [hY]
        exact imageOTwoQuot_oTwoUpper_eq h113 hh inf_le_left
      rw [hYpK]
      refine ⟨hc.A_mem, Zstar_le_imageK hh h.decomp hz, fun y hy => ?_⟩
      obtain ⟨j, c, hc', rfl⟩ := hc.genK y hy
      exact ⟨0, j, c, hc', by simp, fun h0 => absurd rfl h0⟩
  have hρ₂comm := hcommN j₂ hj₂
  have hρ₁comm := hcommN j₁ hj₁
  have hzN : ⁅A, B⁆ ∈ N' ∧ ZstarOf hh ≤ N' := by
    rcases hZ with hZ0 | ⟨hz1, hZz⟩
    · have h1 : ⁅A, B⁆ = 1 := by
        have := hz
        rw [hZ0, Subgroup.mem_bot] at this
        exact this
      rw [hZ0]
      exact ⟨h1 ▸ N'.one_mem, bot_le⟩
    · have hinv : starOf hh j₂ (thompsonJ_le_self T hj₂) * ⁅A, B⁆ *
          (starOf hh j₂ (thompsonJ_le_self T hj₂))⁻¹ = ⁅A, B⁆⁻¹ :=
        conj_comm_of_inv_left (Zstar_central h113 hh hz hAY) (Zstar_central h113 hh hcA hBY)
          (Zstar_central h113 hh hcA hcB.2) (Zstar_central h113 hh hcB (Ys.inv_mem hAY)) hA hB
      have hzN : ⁅A, B⁆ ∈ N' :=
        mem_of_commutator_inv (star_cube h113 hh hz.2) (c := 1) (by simp) N'.one_mem
          (by rw [mul_one]; exact hinv) (hρ₂comm _ hzYp)
      refine ⟨hzN, fun c hc' => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hZz hc')
      exact N'.zpow_mem hzN k
  have hAN : A ∈ N' :=
    mem_of_commutator_inv (star_cube h113 hh hAY) (Zstar_central h113 hh hcA hAY) (hzN.2 hcA) hA
      (hρ₂comm A hAYp)
  have hBN : B ∈ imageOTwoQuot M Yp → B ∈ N' := fun hBYp =>
    mem_of_commutator_inv (star_cube h113 hh hBY) (Zstar_central h113 hh hcB' hBY) (hzN.2 hcB') hB'
      (hρ₁comm B hBYp)
  have hYpN : imageOTwoQuot M Yp ≤ N' := by
    intro y hy
    obtain ⟨i, j, c, hc', rfl, hi⟩ := hYpgen y hy
    have hBi : B ^ i ∈ N' := by
      by_cases h0 : i = 0
      · rw [h0, zpow_zero]
        exact N'.one_mem
      · exact N'.zpow_mem (hBN (hi h0)) i
    exact N'.mul_mem (N'.mul_mem hBi (N'.zpow_mem hAN j)) (hzN.2 hc')
  have hnorm : (Q.subgroupOf Yp).Normal := ⟨fun n hn g => by
    have hnJ : (n : G) ∈ thompsonJ I := (Subgroup.mem_subgroupOf.mp hn).2
    have hgI : (g : G) ∈ I := hYpI g.2
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
    · exact Yp.mul_mem (Yp.mul_mem g.2 n.2) (Yp.inv_mem g.2)
    · exact (Subgroup.mem_normalizer_iff.mp (hIN hgI) n).mp hnJ⟩
  rw [← h.oTwoUpper_eq]
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hxM : x ∈ M := Y153_le Mc M (hYpY hx)
  have hxN' : (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : OTwoQuot M) ∈ N' :=
    hYpN (mem_imageOTwoQuot_iff.mpr ⟨x, hxM, hx, rfl⟩)
  obtain ⟨q, hqM, hqQ, hq⟩ := mem_imageOTwoQuot_iff.mp hxN'
  have hdM : q⁻¹ * x ∈ pCoreOf 2 M := by
    refine (mk_eq_one_iff_mem_pCoreOf (⟨q⁻¹ * x, M.mul_mem (M.inv_mem hqM) hxM⟩ : ↥M)).1 ?_
    have e : (⟨q⁻¹ * x, M.mul_mem (M.inv_mem hqM) hxM⟩ : ↥M) = ⟨q, hqM⟩⁻¹ * ⟨x, hxM⟩ := rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hq, inv_mul_cancel]
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 M) ⟨q⁻¹ * x, hdM⟩
  have hk' : (q⁻¹ * x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, ?_⟩
  have hqYp : q ∈ Yp := hqQ.1
  have hdYp : q⁻¹ * x ∈ Yp := Yp.mul_mem (Yp.inv_mem hqYp) hx
  have key := pow_mem_of_mul_of_pow (Q.subgroupOf Yp) (x := (⟨x, hx⟩ : ↥Yp))
    (q := ⟨q, hqYp⟩) (d := ⟨q⁻¹ * x, hdYp⟩) (k := k) (Subgroup.mem_subgroupOf.mpr hqQ)
    (Subtype.ext (by simpa using hk')) (Subtype.ext (by simp))
  have key' := Subgroup.mem_subgroupOf.mp key
  simp only [Subgroup.coe_pow] at key'
  exact key'.2

theorem not_thompsonJ_le_M_of_not_le (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) {I : Subgroup G}
    (hI : IsHPlus Yp (Sgp153 T V₁) M I)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T M : Set G)) : ¬ thompsonJ I ≤ M := by
  intro hJM
  have hYpJ : Yp ≤ thompsonJ I := Yp_le_thompsonJ h11 h113 h hI hJ
  have hJMI : thompsonJ I ≤ M ⊓ I := le_inf hJM (thompsonJ_le_self I)
  have hθ : thetaOf (thompsonJ I) = Yp := by
    refine le_antisymm ?_ ((h.Yp_le_thetaOf h113).trans (thetaOf_mono hYpJ))
    rw [h.theta_eq h113 hI]
    exact thetaOf_mono hJMI
  have hIN : I ≤ Subgroup.normalizer (thompsonJ I : Set G) :=
    Subgroup.le_normalizer.trans (GammaExtra.normalizer_le_normalizer_thompsonJ I)
  have hIY : I ≤ Subgroup.normalizer (Yp : Set G) := fun g hg => by
    have := normalizer_le_normalizer_thetaOf (thompsonJ I) (hIN hg)
    rwa [hθ] at this
  apply hI.2
  have h4 := h.lemma_15_3_11_four h113 hI
  intro g hg
  have : g ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := ⟨hg, hIY hg⟩
  rw [h4] at this
  exact this.1

end S153D

end CFSG.Quasithin
