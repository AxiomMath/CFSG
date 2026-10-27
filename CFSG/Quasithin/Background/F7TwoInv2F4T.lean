module

public import CFSG.Quasithin.Background.F7TwoInv2F4Oct
public import CFSG.Quasithin.Background.F7TwoInvL3TwoSl2
public import CFSG.GH74.GLS.SP.GlueDefs
public import CFSG.Quasithin.Background.F7TwoDefs
public import CFSG.Quasithin.Background.F7TwoInvExcBasic
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4

public section

namespace CFSG.Quasithin.F7Two

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.TwoF4
  CFSG.LieType.Ree.LargeReeCover

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {m : ℕ}

local notation "X[" k "]" => largeReeBlockGroup K m (octBlock k)
local notation "Γ" => F4.reeGamma K m
local notation "wT" => weylTwo K * weylOne K * weylTwo K

theorem forall_invAutGen_rankOneGroupOne (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ∀ φ : MulAut ↥(rankOneGroupOne K m), φ * φ = 1 → φ ≠ 1 →
      InvAutGen ↥(rankOneGroupOne K m) φ :=
  invAutGen_of_mulEquiv_forall (rankOneEquivSL K m hK).symm
    (invAutGen_sl2_involution ⟨2 * m + 1, by omega, hK⟩)

theorem rankOneGroupOne_le_closure_invXi (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {u : ModGL F4.tag K} (hu : u ∈ rankOneGroupOne K m) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    rankOneGroupOne K m ≤ Subgroup.closure (invXi (rankOneGroupOne K m) u) :=
  le_closure_invXi_of_forall_invAutGen (forall_invAutGen_rankOneGroupOne hm hK)
    (isSimpleGroup_rankOneGroupOne hm hK).1 (isSimpleGroup_rankOneGroupOne hm hK).2 hu hu2 hu1

theorem weylOne_mem_rankOneGroupOne : weylOne K ∈ rankOneGroupOne K m :=
  Subgroup.subset_closure (Or.inr rfl)

theorem sylowVec_mem_tKernel (hK : Nat.card K = 2 ^ (2 * m + 1)) {x : Fin 12 → K} (h0 : x 0 = 0)
    (h1 : x 1 = 0) (h3 : x 3 = 0) : sylowVec m K x ∈ tKernel K m := by
  rw [← SetLike.mem_coe, coe_tKernel hK]
  exact ⟨x, ⟨h0, h1, h3⟩, rfl⟩

theorem octX_two_le_tKernel (hK : Nat.card K = 2 ^ (2 * m + 1)) : X[2] ≤ tKernel K m := by
  intro g hg
  obtain ⟨j, rfl⟩ := exists_twoCoordG_eq hK 1 (show g ∈ largeReeBlockGroup K m (twoSet 1) from hg)
  rw [← sylowJ_eq]
  have e : sylowJ m K j = sylowVec m K ![0, 0, 0, 0, 0, 0, 0, 0, 0, j, 0, 0] := by
    simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowK, sylowL, sylowX,
      largeReeSigma_zero, pinnedX_zero]
  rw [e]
  exact sylowVec_mem_tKernel hK (by simp) (by simp) (by simp)

theorem octX_six_le_tKernel (hK : Nat.card K = 2 ^ (2 * m + 1)) : X[6] ≤ tKernel K m := by
  intro g hg
  obtain ⟨k, rfl⟩ := exists_twoCoordG_eq hK 2 (show g ∈ largeReeBlockGroup K m (twoSet 2) from hg)
  rw [← sylowK_eq]
  have e : sylowK m K k = sylowVec m K ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, k, 0] := by
    simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowL, sylowX,
      largeReeSigma_zero, pinnedX_zero]
  rw [e]
  exact sylowVec_mem_tKernel hK (by simp) (by simp) (by simp)

theorem octX_three_le_tKernel (hK : Nat.card K = 2 ^ (2 * m + 1)) : X[3] ≤ tKernel K m := by
  intro g hg
  obtain ⟨f, f', rfl⟩ :=
    exists_fourCoordG_eq hK 2 (show g ∈ largeReeBlockGroup K m (fourSet 2) from hg)
  rw [← sylowF_eq]
  have e : sylowF m K f f' = sylowVec m K ![0, 0, 0, 0, 0, f, f', 0, 0, 0, 0, 0] := by
    simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowH, sylowJ, sylowK, sylowL, sylowX,
      largeReeSigma_zero, pinnedX_zero]
  rw [e]
  exact sylowVec_mem_tKernel hK (by simp) (by simp) (by simp)

theorem octX_five_le_tKernel (hK : Nat.card K = 2 ^ (2 * m + 1)) : X[5] ≤ tKernel K m := by
  intro g hg
  obtain ⟨h, i, rfl⟩ :=
    exists_fourCoordG_eq hK 3 (show g ∈ largeReeBlockGroup K m (fourSet 3) from hg)
  rw [← sylowH_eq]
  have e : sylowH m K h i = sylowVec m K ![0, 0, 0, 0, 0, 0, 0, h, i, 0, 0, 0] := by
    simp [sylowVec, sylowV, sylowA, sylowB, sylowD, sylowF, sylowJ, sylowK, sylowL, sylowX,
      largeReeSigma_zero, pinnedX_zero]
  rw [e]
  exact sylowVec_mem_tKernel hK (by simp) (by simp) (by simp)

theorem map_conj_nL_octX_six :
    (X[6]).map (MulAut.conj ((wT) * weylOne K * (wT)⁻¹)).toMonoidHom = X[-2] := by
  simp only [mul_inv_rev, conjSub_mul]
  rw [map_conj_weylTwo_inv (k := 6) (by decide), show octSig₁ 6 = 4 by decide,
    map_conj_weylOne_inv (k := 4) (by decide), show octSig₂ 4 = 4 by decide,
    map_conj_weylTwo_inv (k := 4) (by decide), show octSig₁ 4 = 6 by decide,
    map_conj_weylOne (k := 6) (by decide), show octSig₂ 6 = 2 by decide,
    map_conj_weylTwo (k := 2) (by decide), show octSig₁ 2 = 8 by decide,
    map_conj_weylOne (k := 8) (by decide), show octSig₂ 8 = -8 by decide,
    map_conj_weylTwo (k := -8) (by decide), show octSig₁ (-8) = -2 by decide]

theorem map_conj_nL_octX_five :
    (X[5]).map (MulAut.conj ((wT) * weylOne K * (wT)⁻¹)).toMonoidHom = X[-3] := by
  simp only [mul_inv_rev, conjSub_mul]
  rw [map_conj_weylTwo_inv (k := 5) (by decide), show octSig₁ 5 = 5 by decide,
    map_conj_weylOne_inv (k := 5) (by decide), show octSig₂ 5 = 3 by decide,
    map_conj_weylTwo_inv (k := 3) (by decide), show octSig₁ 3 = 7 by decide,
    map_conj_weylOne (k := 7) (by decide), show octSig₂ 7 = 1 by decide,
    map_conj_weylTwo (k := 1) (by decide), show octSig₁ 1 = -1 by decide,
    map_conj_weylOne (k := -1) (by decide), show octSig₂ (-1) = -7 by decide,
    map_conj_weylTwo (k := -7) (by decide), show octSig₁ (-7) = -3 by decide]

theorem map_conj_weylTwo_rankOneGroupOne (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    (rankOneGroupOne K m).map (MulAut.conj (weylTwo K)).toMonoidHom = X[2] ⊔ X[-2] := by
  rw [rankOneGroupOne_eq_octX hK, Subgroup.map_sup, map_conj_weylTwo (k := 8) (by decide),
    map_conj_weylTwo (k := -8) (by decide), show octSig₁ 8 = 2 by decide,
    show octSig₁ (-8) = -2 by decide]

theorem map_conj_nJ_octX_neg_three :
    (X[-3]).map (MulAut.conj (weylTwo K * weylOne K * (weylTwo K)⁻¹)).toMonoidHom = X[1] := by
  simp only [conjSub_mul]
  rw [map_conj_weylTwo_inv (k := -3) (by decide), show octSig₁ (-3) = -7 by decide,
    map_conj_weylOne (k := -7) (by decide), show octSig₂ (-7) = -1 by decide,
    map_conj_weylTwo (k := -1) (by decide), show octSig₁ (-1) = 1 by decide]

theorem map_conj_nJ_octX_three :
    (X[3]).map (MulAut.conj (weylTwo K * weylOne K * (weylTwo K)⁻¹)).toMonoidHom = X[-1] := by
  simp only [conjSub_mul]
  rw [map_conj_weylTwo_inv (k := 3) (by decide), show octSig₁ 3 = 7 by decide,
    map_conj_weylOne (k := 7) (by decide), show octSig₂ 7 = 1 by decide,
    map_conj_weylTwo (k := 1) (by decide), show octSig₁ 1 = -1 by decide]

theorem invGen_tOne (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    InvGen (F4.reeGamma K m) (sylowL m K 1) := by
  have hwΓ : wT ∈ Γ := mul_mem (mul_mem weylTwo_mem weylOne_mem) weylTwo_mem
  have ht : wT * sylowA m K 1 * (wT)⁻¹ = sylowL m K 1 := weyl_conj_sylowA_one
  have hA : sylowA m K 1 ∈ X[8] := by
    rw [octX_eight]
    exact sylowA_mem_U1 hK 1
  have hAR : sylowA m K 1 ∈ rankOneGroupOne K m := by
    rw [rankOneGroupOne_eq_octX hK]
    exact Subgroup.mem_sup_left hA
  have hA2 : sylowA m K 1 * sylowA m K 1 = 1 := by
    have e : sylowA m K 1 = (wT)⁻¹ * sylowL m K 1 * wT := by rw [← ht]; group
    have htt : sylowL m K 1 * sylowL m K 1 = 1 := by rw [← sq]; exact tOne_sq
    rw [e]
    calc (wT)⁻¹ * sylowL m K 1 * wT * ((wT)⁻¹ * sylowL m K 1 * wT) =
        (wT)⁻¹ * (sylowL m K 1 * sylowL m K 1) * wT := by group
      _ = 1 := by rw [htt]; group
  have hA1 : sylowA m K 1 ≠ 1 := by
    intro h
    rw [h] at ht
    exact tOne_ne_one hK (by rw [← ht]; group)
  have hRΓ : rankOneGroupOne K m ≤ Γ := rankOneGroupOne_le_reeGamma hK
  have hR := rankOneGroupOne_le_closure_invXi hm hK hAR hA2 hA1
  have h1 : (rankOneGroupOne K m).map (MulAut.conj wT).toMonoidHom ≤
      Subgroup.closure (invXi Γ (sylowL m K 1)) := by
    have h := (Subgroup.map_mono hR).trans (map_closure_invXi_le hRΓ (sylowA m K 1) hwΓ)
    rwa [ht] at h
  have hnL : wT * weylOne K * (wT)⁻¹ ∈ Subgroup.closure (invXi Γ (sylowL m K 1)) :=
    h1 (Subgroup.mem_map.2 ⟨weylOne K, weylOne_mem_rankOneGroupOne, rfl⟩)
  have hne : (invXi Γ (sylowL m K 1)).Nonempty := by
    have := (isSimpleGroup_rankOneGroupOne hm hK).1
    have hR' : (rankOneGroupOne K m) ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
    obtain ⟨x, hx⟩ := nonempty_invXi_of_le_closure hR hR'
    have h := conj_mem_invXi_of_le hRΓ hwΓ hx
    rw [ht] at h
    exact ⟨_, h⟩
  have hC := centralizer_le_closure_invXi hne
  rw [reeGamma_inf_centralizer_tOne_eq hK] at hC
  have hQ : tKernel K m ≤ Subgroup.closure (invXi Γ (sylowL m K 1)) := le_sup_left.trans hC
  have hR1 : rankOneGroupOne K m ≤ Subgroup.closure (invXi Γ (sylowL m K 1)) :=
    le_sup_right.trans hC
  have h2 := (octX_two_le_tKernel hK).trans hQ
  have h3 := (octX_three_le_tKernel hK).trans hQ
  have h5 := (octX_five_le_tKernel hK).trans hQ
  have h6 := (octX_six_le_tKernel hK).trans hQ
  have h2' : X[-2] ≤ Subgroup.closure (invXi Γ (sylowL m K 1)) := by
    rw [← map_conj_nL_octX_six]
    exact conjSub_le_of_mem hnL h6
  have h3' : X[-3] ≤ Subgroup.closure (invXi Γ (sylowL m K 1)) := by
    rw [← map_conj_nL_octX_five]
    exact conjSub_le_of_mem hnL h5
  have hnJ : weylTwo K * weylOne K * (weylTwo K)⁻¹ ∈
      Subgroup.closure (invXi Γ (sylowL m K 1)) := by
    have hmem : weylTwo K * weylOne K * (weylTwo K)⁻¹ ∈
        (rankOneGroupOne K m).map (MulAut.conj (weylTwo K)).toMonoidHom :=
      Subgroup.mem_map.2 ⟨weylOne K, weylOne_mem_rankOneGroupOne, rfl⟩
    rw [map_conj_weylTwo_rankOneGroupOne hK] at hmem
    exact (sup_le h2 h2') hmem
  have h1' : X[1] ≤ Subgroup.closure (invXi Γ (sylowL m K 1)) := by
    rw [← map_conj_nJ_octX_neg_three]
    exact conjSub_le_of_mem hnJ h3'
  have h1'' : X[-1] ≤ Subgroup.closure (invXi Γ (sylowL m K 1)) := by
    rw [← map_conj_nJ_octX_three]
    exact conjSub_le_of_mem hnJ h3
  rw [rankOneGroupOne_eq_octX hK] at hR1
  have hge := reeGamma_le_of_octX hK (le_sup_left.trans hR1) (le_sup_right.trans hR1) h1' h1''
  exact le_antisymm closure_invXi_le hge

end CFSG.Quasithin.F7Two
