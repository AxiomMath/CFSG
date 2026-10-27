module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2CaseB3
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Core

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_natural_chief_of_conj_generated
    {H S X V D : Subgroup G} {w : G} {m : ℕ}
    (hVH : V ≤ H) (hgen : X = conjClosure V H)
    (hXe : IsElemAbelian 2 X) (hXQ : X ≤ pCoreOf 2 H)
    (hnc : ∃ c, 0 < c ∧ IsChiefSeriesFrom H X X c)
    (hnat : ∀ (L N : Subgroup G) (hstep : IsChiefStep H X L N) (hUH : X ≤ H),
      ¬ IsCentralStep H L N → ∀ hE : IsElemAbelian 2 (Ch3z.chiefMod L N),
        IsNaturalChiefStep H X L N hstep hUH hE m)
    (hDH : D ≤ H) (hDodd : Odd (Nat.card D)) (hDne : D ≠ ⊥)
    (hDV : D ≤ Subgroup.centralizer (V : Set G))
    (hS : IsSylowTwoOf S H) (hVS : S ≤ Subgroup.normalizer (V : Set G))
    (hwH : w ∈ H) (hwD : w ∈ Subgroup.normalizer (D : Set G))
    (hSw : S ⊔ conjugate S w = H) : False := by
  classical
  have hXH : X ≤ H := by
    rw [hgen]
    exact conjClosure_le fun h hh z hz => H.mul_mem (H.mul_mem hh (hVH hz)) (H.inv_mem hh)
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := by
    rw [hgen]
    exact le_normalizer_conjClosure V H
  have hXnormal : IsNormalIn H X X := F112W.isNormalIn_of_le_normalizer le_rfl hHX
  obtain ⟨c, hcpos, hser⟩ := hnc
  obtain ⟨M, L, hLM, -, hstep, hncstep, hbetween⟩ :=
    exists_topmost_noncentral_factor hser hcpos
  have hHN : H ≤ Subgroup.normalizer (M : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hNX : M ≤ X := hstep.1.1
  have hVX : V ≤ X := by
    rw [hgen]
    exact le_conjClosure V H
  have hO2 : ⁅X, oTwoUpper H⁆ ≤ M :=
    (F112W.isChiefSeriesBetween_zero_iff hXH hXQ hstep.1 hXnormal hNX).mp hbetween
  have hD2H : D ≤ oTwoUpper H := by
    intro d hd
    exact mem_oTwoUpper_of_odd (hDH hd)
      (Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard D hd))
  have hC : ∀ x ∈ M, (∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ L) → x ∈ L := by
    intro x hx hxd
    obtain ⟨d0, hd0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
    have hd0D : (d0 : G) ∈ D := d0.2
    have hd0neG : (d0 : G) ≠ 1 :=
      fun h => hd0ne (Subtype.ext (by simpa using h))
    have hodd : Odd (orderOf (d0 : G)) :=
      Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard D hd0D)
    have hd0Q : (d0 : G) ∉ pCoreOf 2 H := by
      intro hmem
      exact hd0neG (CFSG.Quasithin.Vol2.Ch10.SecA.eq_one_of_isPGroup_of_odd
        (pCoreOf_isPGroup 2 H) hmem hodd)
    have hnatstep := hnat L M hstep hXH hncstep
      (CFSG.Quasithin.isElemAbelian_chiefMod hstep hXH hXe.isPGroup)
    have hcomm : (d0 : G) * x * (d0 : G)⁻¹ * x⁻¹ ∈ L := by
      have h := L.inv_mem (hxd (d0 : G) hd0D)
      rwa [show (x * (d0 : G) * x⁻¹ * (d0 : G)⁻¹)⁻¹ =
        (d0 : G) * x * (d0 : G)⁻¹ * x⁻¹ by group] at h
    exact mem_of_conj_mem_of_isNaturalChiefStep hnatstep (hDH hd0D) hd0Q hodd hx hcomm
  have heq : M = L :=
    topmost_factor_eq_of_le hXH hHX hXe hHN hHL hLM hNX hVX hgen hDodd hD2H hDV
      hS hVS hSw hwH hwD hO2 hC
  exact hstep.2.2.1.ne heq.symm


variable {L1 L2 S : Subgroup G} {a : ℕ}

structure Str83CaseBFrame (L1 L2 S : Subgroup G) (a : ℕ) : Prop where
  hQ2S : Q2 L1 L2 S ≤ S
  hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S
  hsyl2 : IsSylowTwoOf S (L2 ⊔ S)
  hZ1_le : Z1 L1 L2 S ≤ L2 ⊔ S
  hSnorm : S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G)

theorem str83CaseBFrame_of_hyp
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hBc : Z1 L1 L2 S ≤ Q2 L1 L2 S) : Str83CaseBFrame L1 L2 S a := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := sup_eq_of_S_eq_right hS2
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hsyl2 : IsSylowTwoOf S (L2 ⊔ S) := by
    rw [hsup2]
    have h := isSylowTwoOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
      (by simpa [Q1, Q2, P1, P2, bigB_comm] using hS2)
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hZ1_le : Z1 L1 L2 S ≤ L2 ⊔ S :=
    hBc.trans (hQ2S.trans le_sup_right)
  have hSnorm : S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans (bigB_le_normalizer_Z1 L1 L2 S)
  exact ⟨hQ2S, hpCore2, hsyl2, hZ1_le, hSnorm⟩

theorem str83_partTwo_caseB_false
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S)
    (hBc : Z1 L1 L2 S ≤ Q2 L1 L2 S) : False := by
  classical
  obtain ⟨D1, D2, hD1, hD2, hB1D, hB2D, hcomm, hBE, hdelta⟩ :=
    str83_exists_cartan_delta hF.1 ha hSz
  have hframe := str83CaseBFrame_of_hyp hF hB ha hL2 hBc
  have hD2C : D2 ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    str83_partTwo_caseB_step4 hF hB ha hSz hL2 hII hZ2 hJ hBc hD1 hD2 hB2D hdelta
  obtain ⟨hXe0, hXQ0, hCount0, hNat0⟩ :=
    str83_partTwo_caseB_steps123 hF hB ha hSz hL2 hII hZ2 hJ hBc
  obtain ⟨w, hwH0, hwD0, -, -, hSw0⟩ :=
    frameT1 hF hB ha hSz hL2 hD2.1 hD2.2.1 hB2D.symm
  have hD2ne : D2 ≠ ⊥ := by
    intro hbot
    have hB2eq : borelOf L2 S = S ⊓ L2 := by
      rw [hB2D, hbot, sup_bot_eq]
    refine not_isPGroup_borelOf_of_l2_local hF.1.h2.sylow (by omega) hL2 ?_
    rw [hB2eq]
    exact hF.1.h2.pgroup.to_le inf_le_left
  set V : Subgroup G := Z1 L1 L2 S with hV
  clear_value V
  have hVH : V ≤ L2 ⊔ S := hBc.trans (hframe.hQ2S.trans le_sup_right)
  have hD2H : D2 ≤ L2 ⊔ S :=
    hD2.1.trans ((F1.borelOf_le L2 S).trans le_sup_left)
  have hDV : D2 ≤ Subgroup.centralizer (V : Set G) := hD2C
  have hVS : S ≤ Subgroup.normalizer (V : Set G) := by
    rw [hV]
    exact hframe.hSnorm
  have hXe : IsElemAbelian 2 (conjClosure V (L2 ⊔ S)) := hXe0
  have hXQ : conjClosure V (L2 ⊔ S) ≤ pCoreOf 2 (L2 ⊔ S) := by
    rw [hframe.hpCore2]
    exact hXQ0.trans inf_le_right
  have hXnormal : IsNormalIn (L2 ⊔ S) (conjClosure V (L2 ⊔ S))
      (conjClosure V (L2 ⊔ S)) :=
    F112W.isNormalIn_of_le_normalizer le_rfl (le_normalizer_conjClosure V (L2 ⊔ S))
  obtain ⟨c, hser⟩ :=
    D15Proof.exists_isChiefSeriesFrom (H := L2 ⊔ S) (U := conjClosure V (L2 ⊔ S))
      (conjClosure V (L2 ⊔ S)) hXnormal
  have hc2 : c = 2 := hCount0 c hser
  have hnc : ∃ c, 0 < c ∧ IsChiefSeriesFrom (L2 ⊔ S)
      (conjClosure V (L2 ⊔ S)) (conjClosure V (L2 ⊔ S)) c :=
    ⟨c, by rw [hc2]; norm_num, hser⟩
  exact false_of_natural_chief_of_conj_generated (H := L2 ⊔ S) (S := S)
    (X := conjClosure V (L2 ⊔ S)) (V := V) (D := D2) (w := w) (m := 2 * a + 1)
    hVH rfl hXe hXQ hnc hNat0 hD2H hD2.2.1 hD2ne hDV hframe.hsyl2 hVS hwH0 hwD0 hSw0

end CFSG.Quasithin.Stroth

end
