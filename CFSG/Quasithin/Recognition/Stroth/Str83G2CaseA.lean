module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2Tools3
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIPushUp
public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.Quasithin.Vol2.GoldschmidtF112TD
public import CFSG.Quasithin.Recognition.Stroth.Str83G2PartTwoSzK

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender
open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem cartan_fixed_point_free_of_bender
    {K : Type} [Group K] [Finite K] {n i : ℕ} (hB : BenderType K n i 1)
    (Q : Sylow 2 K) {D : Subgroup K} (hDle : D ≤ borel (Q : Subgroup K))
    (hDodd : Odd (Nat.card D)) (hDsup : (Q : Subgroup K) ⊔ D = borel (Q : Subgroup K))
    {d x : K} (hd : d ∈ D) (hd1 : d ≠ 1) (hx : x ∈ (Q : Subgroup K))
    (hcomm : d * x * d⁻¹ = x) : x = 1 := by
  obtain ⟨t, ht2, htnot, hcart⟩ := exists_involution_cartan_eq hB Q hDle hDodd hDsup
  obtain ⟨t₀, hc₀⟩ := hB.exists_benderCore Q
  have hc : BenderCore (2 ^ n) i 1 (Q : Subgroup K) t := hc₀.of_involution ht2 htnot
  have hxd : x * d = d * x := by
    calc x * d = (d * x * d⁻¹) * d := by rw [hcomm]
      _ = d * x := by group
  exact hc.eq_one_of_commute_cartan Q.isPGroup' (by rwa [← hcart] at hd) hd1 hx hxd

structure Str83CaseAFrame (L1 L2 S : Subgroup G) (a : ℕ) : Type where
  hF : F112HypW L1 L2 S
  hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)
  ha : 1 ≤ a
  hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)
  hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2)
  hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)
  hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G)
  hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S
  hA : ¬ Z1 L1 L2 S ≤ Q2 L1 L2 S
  hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S
  hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S
  hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S
  hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S
  hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S
  hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S
  hQ1S : Q1 L1 L2 S ≤ S
  hQ2S : Q2 L1 L2 S ≤ S
  hsyl1 : IsSylowTwoOf S (L1 ⊔ S)
  hsyl2 : IsSylowTwoOf S (L2 ⊔ S)
  hVea : IsElemAbelian 2 (Z1 L1 L2 S)
  hVS : Z1 L1 L2 S ≤ S
  hVnorm1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G)
  hSnormV : S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G)
  hQ1centV : Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)
  hQ2normV : Q2 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G)
  hT2 : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S
  hJQ1 : thompsonJ S ≤ Q1 L1 L2 S
  hJQ2 : ¬ thompsonJ S ≤ Q2 L1 L2 S
  hF6 : S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) = Q1 L1 L2 S
  hC7 : (L2 ⊔ S) ⊓ Subgroup.centralizer (Q2 L1 L2 S : Set G) ≤ Q2 L1 L2 S

def str83CaseAFrame_of_hyp
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S)
    (hA : ¬ Z1 L1 L2 S ≤ Q2 L1 L2 S) :
    Str83CaseAFrame L1 L2 S a := by
  classical
  have hB1 : VSzBig L1 ∨ VU3Big L1 := Or.inl ⟨a, ha, hSz⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := sup_eq_of_S_eq_right hS2
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hsyl1 : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hsyl2 : IsSylowTwoOf S (L2 ⊔ S) := by
    rw [hsup2]
    have h := isSylowTwoOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
      (by simpa [Q1, Q2, P1, P2, bigB_comm] using hS2)
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hVea : IsElemAbelian 2 (Z1 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)
  have hVS : Z1 L1 L2 S ≤ S := (omegaOneCenterOf_le (Q1 L1 L2 S)).trans hQ1S
  have hP1normV : P1 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S)
  have hVnorm1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (by
      refine sup_le ((le_sup_left : L1 ≤ P1 L1 L2 S).trans hP1normV) ?_
      exact ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right).trans hP1normV)
  have hSnormV : S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (le_sup_right : S ≤ L1 ⊔ S).trans hVnorm1
  have hQ1centV : Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P1 L1 L2 S)
  have hQ2normV : Q2 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    hQ2S.trans hSnormV
  have hT2 : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S :=
    q1_sup_q2_eq_s_of_caseII hF ha hSz hL2
      (thompsonJ_le_Q1_of_caseII hF hB hB1 hII)
      (not_thompsonJ_le_Q2_of_caseII hF hB hB1 hII)
  have hJQ1 : thompsonJ S ≤ Q1 L1 L2 S := thompsonJ_le_Q1_of_caseII hF hB hB1 hII
  have hJQ2 : ¬ thompsonJ S ≤ Q2 L1 L2 S := not_thompsonJ_le_Q2_of_caseII hF hB hB1 hII
  have hF6 : S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) = Q1 L1 L2 S :=
    inf_centralizer_z1_eq_q1_of_caseII hF hB hB1 hII
  have hC7 : (L2 ⊔ S) ⊓ Subgroup.centralizer (Q2 L1 L2 S : Set G) ≤ Q2 L1 L2 S :=
    inf_centralizer_pCoreOf_right_of_hyp111 hF.1
  exact ⟨hF, hB, ha, hSz, hL2, hII, hZ2, hJ, hA, hS1, hS2, hsup1, hsup2, hpCore1, hpCore2,
    hQ1S, hQ2S, hsyl1, hsyl2, hVea, hVS, hVnorm1, hSnormV, hQ1centV, hQ2normV, hT2,
    hJQ1, hJQ2, hF6, hC7⟩


structure Str83CaseAData (F : Str83CaseAFrame L1 L2 S a) : Type where
  D1 : Subgroup G
  D2 : Subgroup G
  hD1hall : RonanF13.HallTwoPrime D1 (borelOf L1 S)
  hD2hall : RonanF13.HallTwoPrime D2 (borelOf L2 S)
  hD1sup : borelOf L1 S = (S ⊓ L1) ⊔ D1
  hD2sup : borelOf L2 S = (S ⊓ L2) ⊔ D2
  hcomm : ∀ x ∈ D1, ∀ y ∈ D2, x * y = y * x
  hBsplit : bigB L1 L2 S = S ⊔ D1 ⊔ D2
  hdelta : ∀ d ∈ D2, ∃ δ ∈ D1, ∀ l ∈ L1,
    (d * δ⁻¹) * l * (d * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L1
  hD1odd : Odd (Nat.card D1)
  hD2odd : Odd (Nat.card D2)
  hD2inf : D2 ⊓ (S ⊓ L2) = ⊥
  w : G
  hwH2 : w ∈ L2 ⊔ S
  hwD2 : w ∈ Subgroup.normalizer (D2 : Set G)
  hwInv : ∀ d ∈ D2, w * d * w⁻¹ = d⁻¹
  hwNotN : w ∉ Subgroup.normalizer (S : Set G)
  hwTop : S ⊔ conjugate S w = L2 ⊔ S

theorem str83CaseAData_of_frame
    (F : Str83CaseAFrame L1 L2 S a) : Nonempty (Str83CaseAData F) := by
  classical
  obtain ⟨D1, D2, hD1hall, hD2hall, hD1sup, hD2sup, hcomm, hBsplit, hdelta⟩ :=
    str83_exists_cartan_delta F.hF.1 F.ha F.hSz
  have hD2odd : Odd (Nat.card D2) := hD2hall.2.1
  have hD2inf : D2 ⊓ (S ⊓ L2) = ⊥ := by
    have h := CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd
      F.hF.1.h2.sylow.2.1 hD2odd
    rwa [inf_comm] at h
  obtain ⟨w₀, hw₀H2, hw₀D2, hw₀Inv, hw₀NotN, hw₀Top⟩ :=
    frameT1 F.hF F.hB F.ha F.hSz F.hL2 hD2hall.1 hD2odd hD2sup.symm
  let data : Str83CaseAData F :=
    { D1 := D1, D2 := D2, hD1hall := hD1hall, hD2hall := hD2hall,
      hD1sup := hD1sup, hD2sup := hD2sup, hcomm := hcomm, hBsplit := hBsplit,
      hdelta := hdelta, hD1odd := hD1hall.2.1, hD2odd := hD2odd, hD2inf := hD2inf,
      w := w₀⁻¹, hwH2 := ?_, hwD2 := ?_, hwInv := ?_, hwNotN := ?_, hwTop := ?_ }
  exact ⟨data⟩
  · exact (L2 ⊔ S).inv_mem hw₀H2
  · exact (Subgroup.normalizer (D2 : Set G)).inv_mem hw₀D2
  · intro d hd
    have h := hw₀Inv d hd
    have h1 := congrArg (fun x => w₀⁻¹ * x * w₀) h
    have h2 : w₀⁻¹ * (w₀ * d * w₀⁻¹) * w₀ = d := by group
    rw [h2] at h1
    have hX : w₀⁻¹ * d * w₀ = (w₀⁻¹ * d⁻¹ * w₀)⁻¹ := by group
    have hY : (w₀⁻¹ * d⁻¹ * w₀)⁻¹ = d⁻¹ := by rw [← congrArg Inv.inv h1]
    simpa using hX.trans hY
  · intro hw
    exact hw₀NotN (by simpa using (Subgroup.normalizer (S : Set G)).inv_mem hw)
  · have h := congrArg (fun X : Subgroup G => conjugate X w₀⁻¹) hw₀Top
    rw [conjugate, Subgroup.map_sup] at h
    change conjugate S w₀⁻¹ ⊔ conjugate (conjugate S w₀) w₀⁻¹ = conjugate (L2 ⊔ S) w₀⁻¹ at h
    rw [conjugate_conjugate, mul_inv_cancel, conjugate_one,
      conjugate_eq_self_of_mem_normalizer ((L2 ⊔ S).le_normalizer ((L2 ⊔ S).inv_mem hw₀H2))] at h
    rwa [sup_comm] at h


theorem str83_caseA_sup_Q2_eq_S
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) :
    Z1 L1 L2 S ⊔ Q2 L1 L2 S = S := by
  classical
  have hF := F.hF
  have hB := F.hB
  have hA := F.hA
  have hVS := F.hVS
  have hQ2S := F.hQ2S
  have hL2 := F.hL2
  have ha := F.ha
  set V : Subgroup G := Z1 L1 L2 S with hV
  set Q : Subgroup G := Q2 L1 L2 S with hQ
  have hn : 2 ≤ 2 * a + 1 := by omega
  have hPS : V ⊔ Q ≤ S := sup_le hVS hQ2S
  have hB2 : VBig L2 := CFSG.Quasithin.vBig_of_isL2Quot hn hL2
  have hVL2 : VL2 L2 := ⟨2 * a + 1, hL2⟩
  have hD2cart : IsCartanOf D.D2 (borelOf L2 S) :=
    ⟨D.hD2hall.1, D.hD2hall.2.1, D.hD2hall.2.2⟩
  have hBigBV : bigB L1 L2 S ≤ Subgroup.normalizer (V : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S))
  refine le_antisymm hPS ?_
  by_contra hnot
  obtain ⟨y, hyS, hyP⟩ := Set.not_subset.mp hnot
  obtain ⟨x, hxV, hxQ⟩ := Set.not_subset.mp hA
  have hxP : x ∈ V ⊔ Q := Subgroup.mem_sup_left hxV
  have hxQ' : x ∉ Q := hxQ
  have hxS : x ∈ S := hVS hxV
  have hyQ : y ∉ Q := fun hyQ => hyP (Subgroup.mem_sup_right hyQ)
  have hnotS : ¬ S ≤ Q := fun hle => hA (hVS.trans hle)
  have htrans : ∀ x ∈ S, x ∉ Q → ∀ y ∈ S, y ∉ Q →
      ∃ d ∈ D.D2, d⁻¹ * x * d * y⁻¹ ∈ Q := by
    intro x hx hxq y hy hyq
    exact str86_cartan_transitive (L1 := L1) (L2 := L2) (S := S) (P := S)
      hF hB hB2 hVL2 le_rfl hB hnotS hD2cart D.hD2inf D.hD2sup.symm x hx hxq y hy hyq
  obtain ⟨d, hdD, hdx⟩ := htrans x hxS hxQ y hyS hyQ
  have hdBigB : d ∈ bigB L1 L2 S := by
    rw [D.hBsplit]
    exact Subgroup.mem_sup_right hdD
  have hdP : d⁻¹ * x * d ∈ V ⊔ Q := by
    have h := (Subgroup.mem_normalizer_iff.mp
      (hBigBV (Subgroup.inv_mem (bigB L1 L2 S) hdBigB)) x).mp hxV
    exact Subgroup.mem_sup_left (by simpa using h)
  have hy : y ∈ V ⊔ Q := by
    have hq : d⁻¹ * x * d * y⁻¹ ∈ Q := hdx
    have hq' : (d⁻¹ * x * d * y⁻¹)⁻¹ ∈ Q := Q.inv_mem hq
    have e : y = (d⁻¹ * x * d * y⁻¹)⁻¹ * (d⁻¹ * x * d) := by group
    rw [e]
    exact (V ⊔ Q).mul_mem (Subgroup.mem_sup_right hq') hdP
  exact hyP hy



theorem fixed_point_free_of_bender_quotient
    {H Q S D BL L : Subgroup G} {n i : ℕ}
    (hQ : Q = pCoreOf 2 H) (hSH : IsSylowTwoOf S H) (hQS : Q ≤ S)
    (hSdecomp : S = (S ⊓ L) ⊔ Q)
    (hDleH : D ≤ H) (hDhall : RonanF13.HallTwoPrime D BL)
    (hBL : BL = (S ⊓ L) ⊔ D) (hBLH : BL ≤ H)
    (hNHS : H ⊓ Subgroup.normalizer (S : Set G) = BL ⊔ Q)
    (hDinfQ : D ⊓ Q = ⊥)
    (hBT : BenderType (oTwoQuot ↥H) n i 1)
    {d x : G} (hdH : d ∈ H) (hxS : x ∈ S) (hdD : d ∈ D) (hd1 : d ≠ 1)
    (hcomm : d * x * d⁻¹ * x⁻¹ ∈ Q) : x ∈ Q := by
  classical
  let K := oTwoQuot ↥H
  let π : ↥H →* K := QuotientGroup.mk' (pCore 2 ↥H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = (pCore 2 ↥H) := QuotientGroup.ker_mk' _
  let Psub : Subgroup K := (S.subgroupOf H).map π
  have hP : IsSylowTwoOf Psub ⊤ := by
    have h := CFSG.QuasithinUnique.Setup.Wreath.isSylowTwoOf_map_hom hSH π
    simpa [Psub, MonoidHom.range_eq_top_of_surjective π hπ] using h
  have hPidx : ¬ 2 ∣ Psub.index := by
    rw [← Subgroup.relIndex_top_right (H := Psub)]
    exact hP.2.2
  let P : Sylow 2 K := hP.2.1.toSylow hPidx
  have hPcoe : (P : Subgroup K) = Psub := IsPGroup.toSylow_coe hP.2.1 hPidx
  let Dbar : Subgroup K := (D.subgroupOf H).map π
  have hQH : Q ≤ H := hQS.trans hSH.1
  have hSLH : S ⊓ L ≤ H := inf_le_left.trans hSH.1
  have hDLH : D ≤ H := hDleH
  have hBLH' : BL ≤ H := hBLH
  have hcomapP : Subgroup.comap π (P : Subgroup K) = S.subgroupOf H := by
    rw [hPcoe]
    change Subgroup.comap π ((S.subgroupOf H).map π) = S.subgroupOf H
    rw [Subgroup.comap_map_eq, hker, ← CFSG.openPCoreOf_subgroupOf 2 H, ← hQ]
    exact sup_eq_left.mpr (Subgroup.subgroupOf_mono H hQS)
  have hcomapN : Subgroup.comap π (GH74.Uniqueness.Bender.borel (P : Subgroup K)) =
      (H ⊓ Subgroup.normalizer (S : Set G)).subgroupOf H := by
    rw [GH74.Uniqueness.Bender.borel,
      Subgroup.comap_normalizer_eq_of_surjective (H := (P : Subgroup K)) hπ]
    rw [hcomapP]
    exact (CFSG.Quasithin.RonanE611.subgroupOf_normalizer_eq hSH.1).symm
  have hborel_eq : GH74.Uniqueness.Bender.borel (P : Subgroup K) =
      ((H ⊓ Subgroup.normalizer (S : Set G)).subgroupOf H).map π := by
    rw [← hcomapN]
    exact (Subgroup.map_comap_eq_self_of_surjective hπ
      (GH74.Uniqueness.Bender.borel (P : Subgroup K))).symm
  have hmapS : Psub = ((S ⊓ L).subgroupOf H).map π := by
    change (S.subgroupOf H).map π = ((S ⊓ L).subgroupOf H).map π
    conv_lhs => rw [hSdecomp]
    rw [Subgroup.subgroupOf_sup hSLH hQH, Subgroup.map_sup,
      show (Q.subgroupOf H).map π = ⊥ from by
        rw [Subgroup.map_eq_bot_iff, hker, ← CFSG.openPCoreOf_subgroupOf 2 H, ← hQ],
      sup_bot_eq]
  have hmapQ : (Q.subgroupOf H).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hker, ← CFSG.openPCoreOf_subgroupOf 2 H, ← hQ]
  have hmapBL : BL.subgroupOf H = (S ⊓ L).subgroupOf H ⊔ D.subgroupOf H := by
    conv_lhs => rw [hBL]
    rw [Subgroup.subgroupOf_sup hSLH hDLH]
  have hmapBL' : (BL.subgroupOf H).map π = Psub ⊔ Dbar := by
    rw [hmapBL, Subgroup.map_sup, hmapS]
  have hborel_sup : (P : Subgroup K) ⊔ Dbar = GH74.Uniqueness.Bender.borel (P : Subgroup K) := by
    rw [hborel_eq, hNHS, Subgroup.subgroupOf_sup hBLH' hQH, Subgroup.map_sup,
      hmapBL', hmapQ, sup_bot_eq, hPcoe]
  have hDbarLe : Dbar ≤ GH74.Uniqueness.Bender.borel (P : Subgroup K) := by
    rw [← hborel_sup]
    exact le_sup_right
  have hDbarOdd : Odd (Nat.card Dbar) := by
    have hinj : Function.Injective (fun y : ↥(D.subgroupOf H) => π y) := by
      intro a b hab
      have h1 : π ((a⁻¹ * b : ↥(D.subgroupOf H))) = 1 := by
        have hcoe : ((a⁻¹ * b : ↥(D.subgroupOf H)) : ↥H) =
            (a : ↥H)⁻¹ * (b : ↥H) := by simp
        rw [hcoe, map_mul, map_inv]
        have hab' : π (a : ↥H) = π (b : ↥H) := hab
        rw [hab']
        simp
      have h2 : ((a⁻¹ * b : ↥(D.subgroupOf H)) : ↥H) ∈ pCore 2 ↥H := by
        rw [← hker]
        exact MonoidHom.mem_ker.mpr h1
      have h3 : (((a⁻¹ * b : ↥(D.subgroupOf H)) : ↥H) : G) ∈ D ⊓ Q := by
        refine ⟨Subgroup.mem_subgroupOf.mp (a⁻¹ * b).2, ?_⟩
        rw [hQ]
        exact (F1.mem_pCore_iff_coe _).mp h2
      rw [hDinfQ] at h3
      have h4 : (((a⁻¹ * b : ↥(D.subgroupOf H)) : ↥H) : G) = 1 := Subgroup.mem_bot.mp h3
      have h5 : a⁻¹ * b = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        exact h4
      exact inv_mul_eq_one.mp h5
    have hcard : Nat.card Dbar = Nat.card D := by
      have hbij : Function.Bijective
          (fun y : ↥(D.subgroupOf H) =>
            (⟨π y, Subgroup.mem_map_of_mem π y.2⟩ : Dbar)) := by
        constructor
        · intro a b hab
          exact hinj (congrArg Subtype.val hab)
        · intro z
          obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp z.2
          exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩
      have hcard1 : Nat.card Dbar = Nat.card ↥(D.subgroupOf H) :=
        Nat.card_congr (Equiv.ofBijective _ hbij).symm
      rw [hcard1]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleH).toEquiv
    rw [hcard]
    exact hDhall.2.1
  have hfpf : ∀ {d x : K}, d ∈ Dbar → d ≠ 1 → x ∈ (P : Subgroup K) →
      d * x * d⁻¹ = x → x = 1 :=
    fun {d x} hd hd1 hx hfix =>
      cartan_fixed_point_free_of_bender hBT P hDbarLe hDbarOdd hborel_sup hd hd1 hx hfix
  let dH : ↥H := ⟨d, hdH⟩
  let xH : ↥H := ⟨x, hSH.1 hxS⟩
  have hdbar : π dH ∈ Dbar := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hdD)
  have hdbar1 : π dH ≠ 1 := by
    intro h1
    have h2 : dH ∈ pCore 2 ↥H := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr h1
    have h3 : d ∈ D ⊓ Q := by
      refine ⟨hdD, ?_⟩
      rw [hQ]
      exact (F1.mem_pCore_iff_coe _).mp h2
    rw [hDinfQ] at h3
    exact hd1 (Subgroup.mem_bot.mp h3)
  have hxbar : π xH ∈ (P : Subgroup K) := by
    rw [hPcoe]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hxS)
  have hfix : π dH * π xH * (π dH)⁻¹ = π xH := by
    have hmem : (⟨d * x * d⁻¹ * x⁻¹, hQH hcomm⟩ : ↥H) ∈ pCore 2 ↥H :=
      (F1.mem_pCore_iff_coe _).mpr (by simpa [hQ] using hcomm)
    have hcoeq : dH * xH * dH⁻¹ * xH⁻¹ =
        (⟨d * x * d⁻¹ * x⁻¹, hQH hcomm⟩ : ↥H) := by
      apply Subtype.ext
      simp [dH, xH]
    have h : π (dH * xH * dH⁻¹ * xH⁻¹) = 1 := by
      rw [hcoeq]
      exact (QuotientGroup.eq_one_iff (N := pCore 2 ↥H) _).mpr hmem
    have h' : π dH * π xH * (π dH)⁻¹ * (π xH)⁻¹ = 1 := by
      simpa [map_mul, map_inv] using h
    calc π dH * π xH * (π dH)⁻¹
        = (π dH * π xH * (π dH)⁻¹ * (π xH)⁻¹) * π xH := by group
      _ = π xH := by rw [h', one_mul]
  have hxbar1 : π xH = 1 := hfpf hdbar hdbar1 hxbar hfix
  have hxQ : xH ∈ pCore 2 ↥H := by
    rw [← hker]
    exact MonoidHom.mem_ker.mpr hxbar1
  rw [hQ]
  exact (F1.mem_pCore_iff_coe _).mp hxQ

theorem normalizer_inf_eq_borel_sup_q1
    (F : Str83CaseAFrame L1 L2 S a) (H : Subgroup G) (hH : H = L1 ⊔ S) :
    H ⊓ Subgroup.normalizer (S : Set G) = borelOf L1 S ⊔ Q1 L1 L2 S := by
  classical
  have hF := F.hF
  have hH' : H = L1 ⊔ Q1 L1 L2 S := hH.trans F.hsup1
  have hQ1S : Q1 L1 L2 S ≤ S := F.hQ1S
  have hQ1H : Q1 L1 L2 S ≤ H := by rw [hH']; exact le_sup_right
  have hB1H : borelOf L1 S ≤ H := by
    rw [hH]
    exact (F1.borelOf_le L1 S).trans le_sup_left
  have hBigBNL1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le (sup_le ((F1.borelOf_le L1 S).trans Subgroup.le_normalizer)
      hF.1.h1.borel_le) hF.1.h1.normalizes
  have hP1NL1 : P1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le Subgroup.le_normalizer hBigBNL1
  have hQ1NL : Q1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (pCoreOf_le 2 (P1 L1 L2 S)).trans hP1NL1
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨hgH, hgN⟩ := Subgroup.mem_inf.mp hg
    rw [hH'] at hgH
    obtain ⟨l, hl, q, hq, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hQ1NL).mp hgH
    have hqN : q ∈ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer (hQ1S hq)
    have hlN : l ∈ Subgroup.normalizer (S : Set G) := by
      have h1 : l = (l * q) * q⁻¹ := by group
      rw [h1]
      exact (Subgroup.normalizer (S : Set G)).mul_mem hgN
        (Subgroup.inv_mem _ hqN)
    have hlN' : l ∈ Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact ⟨(Subgroup.mem_normalizer_iff.mp hlN x).mp hx.1,
          L1.mul_mem (L1.mul_mem hl hx.2) (L1.inv_mem hl)⟩
      · intro hx
        refine ⟨(Subgroup.mem_normalizer_iff.mp hlN x).mpr hx.1, ?_⟩
        have hx' : x = l⁻¹ * (l * x * l⁻¹) * l := by group
        rw [hx']
        exact L1.mul_mem (L1.mul_mem (L1.inv_mem hl) hx.2) hl
    have hlB : l ∈ borelOf L1 S := Subgroup.mem_inf.mpr ⟨hl, hlN'⟩
    exact (borelOf L1 S ⊔ Q1 L1 L2 S).mul_mem (Subgroup.mem_sup_left hlB)
      (Subgroup.mem_sup_right hq)
  · refine sup_le ?_ ?_
    · have hB1bigB : borelOf L1 S ≤ bigB L1 L2 S := by
        show borelOf L1 S ≤ (borelOf L1 S ⊔ borelOf L2 S) ⊔ S
        exact le_sup_of_le_left le_sup_left
      exact le_inf hB1H (hB1bigB.trans F.hB)
    · exact le_inf hQ1H (hQ1S.trans Subgroup.le_normalizer)


theorem str83_caseA_fpf_D2
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) {d x : G}
    (hdD : d ∈ D.D2) (hd1 : d ≠ 1) (hxS : x ∈ S)
    (hcomm : d * x * d⁻¹ * x⁻¹ ∈ Q2 L1 L2 S) : x ∈ Q2 L1 L2 S := by
  classical
  have hF := F.hF
  have ha := F.ha
  have hn : 2 ≤ 2 * a + 1 := by omega
  have hH : u3H L1 L2 S = L2 ⊔ S := by
    rw [u3H, ← F.hsup2]
  have hSH : IsSylowTwoOf S (u3H L1 L2 S) := by
    rw [hH]
    exact F.hsyl2
  have hQ : Q2 L1 L2 S = pCoreOf 2 (u3H L1 L2 S) :=
    (str86_pCoreOf_u3H hF).symm
  have hDleH : D.D2 ≤ u3H L1 L2 S :=
    (D.hD2hall.1.trans (F1.borelOf_le L2 S)).trans
      (by rw [hH]; exact le_sup_left)
  have hBLH : borelOf L2 S ≤ u3H L1 L2 S :=
    (F1.borelOf_le L2 S).trans (by rw [hH]; exact le_sup_left)
  have hDinfQ : D.D2 ⊓ Q2 L1 L2 S = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyS : y ∈ S := F.hQ2S hy.2
    have hyL2 : y ∈ L2 := (D.hD2hall.1.trans (F1.borelOf_le L2 S)) hy.1
    have hy' : y ∈ D.D2 ⊓ (S ⊓ L2) := ⟨hy.1, ⟨hyS, hyL2⟩⟩
    rw [D.hD2inf] at hy'
    exact hy'
  obtain ⟨e⟩ := str86_isL2Quot_u3H hF F.hL2
  have hBT : BenderType (oTwoQuot ↥(u3H L1 L2 S)) (2 * a + 1) 1 1 :=
    BenderType.linear (2 * a + 1) hn
      (show oTwoQuot ↥(u3H L1 L2 S) ≃* CFSG.Theory.Comparator.PSL2Model (2 * a + 1) from e)
  exact fixed_point_free_of_bender_quotient (L := L2) hQ hSH F.hQ2S F.hS2 hDleH
    D.hD2hall D.hD2sup hBLH
    (normalizer_inf_eq_borel_sup_q2 hF F.hB ha F.hSz F.hL2 (u3H L1 L2 S) hH)
    hDinfQ hBT (hDleH hdD) hxS hdD hd1 hcomm


theorem str83_caseA_fpf_D1
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) {d x : G}
    (hdD : d ∈ D.D1) (hd1 : d ≠ 1) (hxS : x ∈ S)
    (hcomm : d * x * d⁻¹ * x⁻¹ ∈ Q1 L1 L2 S) : x ∈ Q1 L1 L2 S := by
  classical
  have hF := F.hF
  have ha := F.ha
  have hn : 2 ≤ 2 * a + 1 := by omega
  let H : Subgroup G := L1 ⊔ Q1 L1 L2 S
  have hH : H = L1 ⊔ S := F.hsup1.symm
  have hSH : IsSylowTwoOf S H := by
    rw [hH]
    exact F.hsyl1
  have hQ : Q1 L1 L2 S = pCoreOf 2 H := (pCoreOf_sup_pCoreOf hF.1).symm
  have hDleH : D.D1 ≤ H :=
    (D.hD1hall.1.trans (F1.borelOf_le L1 S)).trans (by rw [hH]; exact le_sup_left)
  have hBLH : borelOf L1 S ≤ H :=
    (F1.borelOf_le L1 S).trans (by rw [hH]; exact le_sup_left)
  have hDinfQ : D.D1 ⊓ Q1 L1 L2 S = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyS : y ∈ S := F.hQ1S hy.2
    have hyL1 : y ∈ L1 := (D.hD1hall.1.trans (F1.borelOf_le L1 S)) hy.1
    have h1 : y ∈ D.D1 ⊓ (S ⊓ L1) := ⟨hy.1, ⟨hyS, hyL1⟩⟩
    have h2 : (S ⊓ L1) ⊓ D.D1 = ⊥ :=
      CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd
        F.hF.1.h1.sylow.2.1 D.hD1odd
    rw [inf_comm] at h1
    exact h2 ▸ h1
  have hBT : BenderType (oTwoQuot ↥H) (2 * a + 1) 2 1 := by
    obtain ⟨eSz⟩ := F.hSz
    have e : oTwoQuot ↥H ≃* CFSG.Open.Sz a :=
      (oTwoQuotSupEquiv hF.1).trans eSz
    exact BenderType.suzuki a ha
      (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  exact fixed_point_free_of_bender_quotient (L := L1) hQ hSH F.hQ1S F.hS1 hDleH
    D.hD1hall D.hD1sup hBLH
    (normalizer_inf_eq_borel_sup_q1 F H hH)
    hDinfQ hBT (hDleH hdD) hxS hdD hd1 hcomm


theorem str83_caseA_delta_trivial_imp_false
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) {d : G}
    (hdD : d ∈ D.D2) (hd1 : d ≠ 1)
    (hd : ∀ l ∈ L1, d * l * d⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) : False := by
  classical
  have hF := F.hF
  have hVQ2 : Z1 L1 L2 S ⊔ Q2 L1 L2 S = S := str83_caseA_sup_Q2_eq_S F D
  have hdB : d ∈ bigB L1 L2 S := by
    rw [D.hBsplit]
    exact Subgroup.mem_sup_right hdD
  have hdZ2 : d ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    F.hZ2 ((le_sup_left : L2 ≤ L2 ⊔ S) ((D.hD2hall.1.trans (F1.borelOf_le L2 S)) hdD))
  have hK : d ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    str83_partTwo_lemmaK_centralizes hF F.hB F.ha F.hSz F.hL2 F.hII F.hZ2 F.hJ
      hdB hdZ2 hd
  have hnot : ¬ S ≤ Q2 L1 L2 S := fun hle => F.hA (F.hVS.trans hle)
  obtain ⟨s, hsS, hsQ⟩ := Set.not_subset.mp hnot
  have hSNQ2 : S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S))).trans
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hBigBNQ2 : bigB L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hVNQ2 : Z1 L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    F.hVS.trans hSNQ2
  obtain ⟨v, hvV, q, hqQ, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes F.hQ2normV).mp
      (by rw [hVQ2]; exact hsS)
  have hdv : d * v * d⁻¹ = v := by
    have h := (Subgroup.mem_centralizer_iff.mp hK) v hvV
    rw [← h]
    group
  have hdq : d * q * d⁻¹ * q⁻¹ ∈ Q2 L1 L2 S := by
    have h1 : d * q * d⁻¹ ∈ Q2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hBigBNQ2 hdB) q).mp hqQ
    exact (Q2 L1 L2 S).mul_mem h1 ((Q2 L1 L2 S).inv_mem hqQ)
  have hvq : v * (d * q * d⁻¹ * q⁻¹) * v⁻¹ ∈ Q2 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hVNQ2 hvV) _).mp hdq
  have hcommS : d * (v * q) * d⁻¹ * (v * q)⁻¹ ∈ Q2 L1 L2 S := by
    have e : d * (v * q) * d⁻¹ * (v * q)⁻¹ =
        v * (d * q * d⁻¹ * q⁻¹) * v⁻¹ := by
      rw [show d * (v * q) * d⁻¹ = v * (d * q * d⁻¹) by
        calc d * (v * q) * d⁻¹ = (d * v * d⁻¹) * (d * q * d⁻¹) := by group
          _ = v * (d * q * d⁻¹) := by rw [hdv]]
      group
    rw [e]
    exact hvq
  exact hsQ (str83_caseA_fpf_D2 F D hdD hd1 hsS hcommS)


theorem str83_caseA_trivial_on_sup
    (F : Str83CaseAFrame L1 L2 S a) {k : G}
    (hkB : k ∈ bigB L1 L2 S)
    (hk : ∀ l ∈ L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) :
    ∀ x ∈ L1 ⊔ S, k * x * k⁻¹ * x⁻¹ ∈ Q1 L1 L2 S := by
  classical
  have hF := F.hF
  have hBigBNL1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le (sup_le ((F1.borelOf_le L1 S).trans Subgroup.le_normalizer)
      hF.1.h1.borel_le) hF.1.h1.normalizes
  have hP1NL1 : P1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le Subgroup.le_normalizer hBigBNL1
  have hQ1NL1 : Q1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (pCoreOf_le 2 (P1 L1 L2 S)).trans hP1NL1
  have hBigBNQ1 : bigB L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans
      (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hL1NQ1 : L1 ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (le_sup_left : L1 ≤ P1 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  intro x hx
  have hx' : x ∈ L1 ⊔ Q1 L1 L2 S := by rwa [F.hsup1] at hx
  obtain ⟨l, hl, q, hq, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hQ1NL1).mp hx'
  have hkl : k * l * k⁻¹ * l⁻¹ ∈ Q1 L1 L2 S :=
    (Hyp111.pCoreOf_le_pCoreOf_vertex hF.1) (hk l hl)
  have hkq : k * q * k⁻¹ * q⁻¹ ∈ Q1 L1 L2 S := by
    have h1 : k * q * k⁻¹ ∈ Q1 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hBigBNQ1 hkB) q).mp hq
    exact (Q1 L1 L2 S).mul_mem h1 ((Q1 L1 L2 S).inv_mem hq)
  have hconj : l * (k * q * k⁻¹ * q⁻¹) * l⁻¹ ∈ Q1 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hL1NQ1 hl) _).mp hkq
  have e : k * (l * q) * k⁻¹ * (l * q)⁻¹ =
      (k * l * k⁻¹ * l⁻¹) * (l * (k * q * k⁻¹ * q⁻¹) * l⁻¹) := by
    group
  rw [e]
  exact (Q1 L1 L2 S).mul_mem hkl hconj


theorem str83_caseA_centralizer_mod_R
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) {d q : G}
    (hdD : d ∈ D.D2) (hd1 : d ≠ 1) (hqQ2 : q ∈ Q2 L1 L2 S)
    (hcomm : d * q * d⁻¹ * q⁻¹ ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S) :
    q ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S := by
  classical
  by_cases hqQ1 : q ∈ Q1 L1 L2 S
  · exact ⟨hqQ1, hqQ2⟩
  exfalso
  obtain ⟨δ, hδD1, hδ⟩ := D.hdelta d hdD
  have hD1bigB : D.D1 ≤ bigB L1 L2 S := by
    rw [D.hBsplit]
    exact le_sup_of_le_left le_sup_right
  have hdBigB : d ∈ bigB L1 L2 S := by
    rw [D.hBsplit]
    exact Subgroup.mem_sup_right hdD
  have hδ1 : δ ≠ 1 := by
    intro hδ1
    apply str83_caseA_delta_trivial_imp_false F D hdD hd1
    intro l hl
    have h := hδ l hl
    simpa [hδ1] using h
  have hqS : q ∈ S := F.hQ2S hqQ2
  set k : G := d * δ⁻¹ with hkdef
  have hkB : k ∈ bigB L1 L2 S := by
    rw [hkdef]
    exact (bigB L1 L2 S).mul_mem hdBigB ((bigB L1 L2 S).inv_mem (hD1bigB hδD1))
  have hkq : k * q * k⁻¹ * q⁻¹ ∈ Q1 L1 L2 S :=
    str83_caseA_trivial_on_sup F hkB hδ q ((le_sup_right : S ≤ L1 ⊔ S) hqS)
  set r : G := d * q * d⁻¹ * q⁻¹ with hrdef
  have hr : r ∈ Q1 L1 L2 S := (inf_le_left : Q1 L1 L2 S ⊓ Q2 L1 L2 S ≤ Q1 L1 L2 S) hcomm
  set c : G := q * k * q⁻¹ * k⁻¹ with hcdef
  have hc : c ∈ Q1 L1 L2 S := by
    have e : c = (k * q * k⁻¹ * q⁻¹)⁻¹ := by rw [hcdef]; group
    rw [e]
    exact (Q1 L1 L2 S).inv_mem hkq
  have hBigBNQ1 : bigB L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans
      (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hconj : k⁻¹ * (r * c) * k ∈ Q1 L1 L2 S := by
    have h := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (hBigBNQ1 hkB)) (r * c)).mp
      ((Q1 L1 L2 S).mul_mem hr hc)
    simpa using h
  have e : δ * q * δ⁻¹ * q⁻¹ = k⁻¹ * (r * c) * k := by
    rw [hrdef, hcdef, hkdef]
    group
  exact hqQ1 (str83_caseA_fpf_D1 F D hδD1 hδ1 hqS (by rwa [e]))


theorem str83_caseA_D2_ne_bot
    (F : Str83CaseAFrame L1 L2 S a) (D : Str83CaseAData F) : D.D2 ≠ ⊥ := by
  classical
  intro hbot
  have hF := F.hF
  have hn : 2 ≤ 2 * a + 1 := by have := F.ha; omega
  let K : Type := oTwoQuot ↥L2
  let π : ↥L2 →* K := QuotientGroup.mk' (pCore 2 ↥L2)
  let S2 : Subgroup G := S ⊓ L2
  let Qimg : Subgroup K := (S2.subgroupOf L2).map π
  obtain ⟨hQimg2, hQimgodd, hMmap⟩ := F1.map_borelOf_eq_normalizer hF.1.h2.sylow
  let Qsyl : Sylow 2 K := hQimg2.toSylow hQimgodd
  have hQcoe : (Qsyl : Subgroup K) = Qimg := IsPGroup.toSylow_coe hQimg2 hQimgodd
  obtain ⟨eL2⟩ := F.hL2
  have hBT : BenderType K (2 * a + 1) 1 1 :=
    BenderType.linear (2 * a + 1) hn eL2
  obtain ⟨t, hc⟩ := hBT.exists_benderCore Qsyl
  have hDleB : D.D2 ≤ borelOf L2 S := D.hD2hall.1
  have hDinf : D.D2 ⊓ (S ⊓ L2) = ⊥ := D.hD2inf
  have hcart_le : cartan (Qsyl : Subgroup K) t ≤ borel (Qsyl : Subgroup K) :=
    cartan_le_borel _ _
  have hcard : Nat.card ↥(cartan (Qsyl : Subgroup K) t) = 2 ^ (2 * a + 1) - 1 := by
    rw [hc.card_cartan, mul_one]
  have hq8 : 8 ≤ 2 ^ (2 * a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcard_gt : 1 < Nat.card ↥(cartan (Qsyl : Subgroup K) t) := by
    rw [hcard]
    omega
  haveI : Fintype ↥(cartan (Qsyl : Subgroup K) t) := Fintype.ofFinite _
  obtain ⟨ybar, hybar1⟩ := Fintype.exists_ne_of_one_lt_card
    (by simpa [Nat.card_eq_fintype_card] using hcard_gt)
    (1 : ↥(cartan (Qsyl : Subgroup K) t))
  have hybarCart : (ybar : K) ∈ cartan (Qsyl : Subgroup K) t := ybar.2
  have hybar_ne : (ybar : K) ≠ 1 := by
    intro h
    exact hybar1 (Subtype.ext h)
  have hybarB : (ybar : K) ∈ borel (Qsyl : Subgroup K) := hcart_le hybarCart
  have hybarImg : (ybar : K) ∈ ((borelOf L2 S).subgroupOf L2).map π := by
    rwa [hMmap]
  obtain ⟨yL, hyL, hyLy⟩ := Subgroup.mem_map.mp hybarImg
  let y : G := (yL : L2)
  have hyB : y ∈ borelOf L2 S := Subgroup.mem_subgroupOf.mp hyL
  have hyImg : π yL = (ybar : K) := hyLy
  have hyNotS2 : y ∉ S2 := by
    intro hyS2
    have hyS2L : yL ∈ S2.subgroupOf L2 := Subgroup.mem_subgroupOf.mpr hyS2
    have hmemQ : π yL ∈ Qimg := Subgroup.mem_map_of_mem π hyS2L
    have hmemCart : π yL ∈ cartan (Qsyl : Subgroup K) t := by rwa [hyImg]
    have hbot' : π yL ∈ (Qsyl : Subgroup K) ⊓ cartan (Qsyl : Subgroup K) t := by
      rw [hQcoe]
      exact ⟨hmemQ, hmemCart⟩
    rw [hc.inf_eq] at hbot'
    exact hybar_ne (Subgroup.mem_bot.mp hbot' ▸ hyImg.symm)
  have hD2N : D.D2 ≤ Subgroup.normalizer (S2 : Set G) :=
    hDleB.trans (F1.borelOf_le_normalizer L2 S)
  have hyDecomp : y ∈ (S2 : Subgroup G) ⊔ D.D2 := by
    rw [← D.hD2sup]
    exact hyB
  obtain ⟨s, hsS2, d, hdD, hsd⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hD2N).mp hyDecomp
  have hdne : d ≠ 1 := by
    intro hd1
    apply hyNotS2
    rw [hsd, hd1, mul_one]
    exact hsS2
  exact hdne (Subgroup.mem_bot.mp (hbot ▸ hdD))

end CFSG.Quasithin.Stroth

end

