module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res3ProofModel
public import CFSG.RankThree.PartTwo.Sec16.Item16Res3ProofHeis
public import CFSG.RankThree.PartTwo.Sec16.Item163ResProofU35
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res3U35

open CFSG.RankThree.PartOne.HNB CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts CFSG.Quasithin.H13 Matrix
open CFSG.Assembly.RankThreeEven (projSU)
open scoped commutatorElement

@[expose] def XM : Matrix (Fin 3) (Fin 3) F25 :=
  !![fe 3 0, fe 0 0, fe 0 2; fe 0 3, fe 0 0, fe 2 0; fe 0 0, fe 1 0, fe 0 0]

@[expose] def YM : Matrix (Fin 3) (Fin 3) F25 :=
  !![fe 0 0, fe 1 2, fe 4 2; fe 4 3, fe 4 4, fe 3 0; fe 1 3, fe 3 0, fe 4 1]

@[expose] def ZM : Matrix (Fin 3) (Fin 3) F25 :=
  !![fe 1 1, fe 1 0, fe 1 0; fe 4 0, fe 1 2, fe 0 2; fe 4 0, fe 0 2, fe 1 2]

@[expose] def TM : Matrix (Fin 3) (Fin 3) F25 :=
  !![fe 0 0, fe 4 0, fe 0 0; fe 4 3, fe 0 0, fe 1 2; fe 4 2, fe 0 0, fe 4 2]

theorem borel_facts :
    (det3 XM = 1 ∧ (XM.map (· ^ (5 ^ 1)))ᵀ * XM = 1) ∧
    (det3 YM = 1 ∧ (YM.map (· ^ (5 ^ 1)))ᵀ * YM = 1) ∧
    (det3 ZM = 1 ∧ (ZM.map (· ^ (5 ^ 1)))ᵀ * ZM = 1) ∧
    (det3 TM = 1 ∧ (TM.map (· ^ (5 ^ 1)))ᵀ * TM = 1) ∧
    XM ^ 5 = 1 ∧ YM ^ 5 = 1 ∧ ZM * XM * YM = YM * XM ∧ ZM * XM = XM * ZM ∧
    ZM * YM = YM * ZM ∧ TM * XM = YM * TM ∧ TM * YM = XM ^ 3 * ZM ^ 4 * TM ∧
    TM ^ 4 * XM = XM ^ 4 * ZM ^ 3 * TM ^ 4 ∧ TM ^ 4 * YM = YM ^ 4 * ZM * TM ^ 4 := by
  decide +kernel

theorem ZM_ne_smul : ∀ c : F25, ZM ≠ c • 1 := by decide +kernel

@[expose] noncomputable def xS : SU5 :=
  mkSU XM (by rw [det_eq_det3]; exact borel_facts.1.1) borel_facts.1.2

@[expose] noncomputable def yS : SU5 :=
  mkSU YM (by rw [det_eq_det3]; exact borel_facts.2.1.1) borel_facts.2.1.2

@[expose] noncomputable def zS : SU5 :=
  mkSU ZM (by rw [det_eq_det3]; exact borel_facts.2.2.1.1) borel_facts.2.2.1.2

@[expose] noncomputable def tS : SU5 :=
  mkSU TM (by rw [det_eq_det3]; exact borel_facts.2.2.2.1.1) borel_facts.2.2.2.1.2

noncomputable abbrev xP : PU5 := (xS : PU5)

noncomputable abbrev yP : PU5 := (yS : PU5)

noncomputable abbrev zP : PU5 := (zS : PU5)

noncomputable abbrev tP : PU5 := (tS : PU5)

theorem mk_eq_of_mat {g k : SU5}
    (h : ((g : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) =
      ((k : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25)) : (g : PU5) = (k : PU5) :=
  congrArg _ (SU5_ext h)

theorem coe_one' : (((1 : SU5) : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = 1 := by
  rw [Subgroup.coe_one, Units.val_one]

theorem coe_xS : ((xS : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = XM := coe_mkSU _ _ _

theorem coe_yS : ((yS : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = YM := coe_mkSU _ _ _

theorem coe_zS : ((zS : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = ZM := coe_mkSU _ _ _

theorem coe_tS : ((tS : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = TM := coe_mkSU _ _ _

theorem rels :
    xP ^ 5 = 1 ∧ yP ^ 5 = 1 ∧ zP * xP * yP = yP * xP ∧ zP * xP = xP * zP ∧
      zP * yP = yP * zP ∧ tP * xP = yP * tP ∧ tP * yP = xP ^ 3 * zP ^ 4 * tP ∧
      tP ^ 4 * xP = xP ^ 4 * zP ^ 3 * tP ^ 4 ∧ tP ^ 4 * yP = yP ^ 4 * zP * tP ^ 4 := by
  obtain ⟨-, -, -, -, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := borel_facts
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_one]
    exact mk_eq_of_mat (by rw [coe_pow, coe_xS, h1, coe_one'])
  · rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_one]
    exact mk_eq_of_mat (by rw [coe_pow, coe_yS, h2, coe_one'])
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact mk_eq_of_mat (by rw [coe_mul, coe_mul, coe_mul, coe_xS, coe_yS, coe_zS, h3])
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact mk_eq_of_mat (by rw [coe_mul, coe_mul, coe_xS, coe_zS, h4])
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact mk_eq_of_mat (by rw [coe_mul, coe_mul, coe_yS, coe_zS, h5])
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact mk_eq_of_mat (by rw [coe_mul, coe_mul, coe_xS, coe_yS, coe_tS, h6])
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact mk_eq_of_mat (by
      rw [coe_mul, coe_mul, coe_mul, coe_pow, coe_pow, coe_xS, coe_yS, coe_zS, coe_tS, h7])
  · rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow,
      ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact mk_eq_of_mat (by
      rw [coe_mul, coe_mul, coe_mul, coe_pow, coe_pow, coe_pow, coe_xS, coe_zS, coe_tS, h8])
  · rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact mk_eq_of_mat (by
      rw [coe_mul, coe_mul, coe_mul, coe_pow, coe_pow, coe_yS, coe_zS, coe_tS, h9])

theorem zP_ne_one : zP ≠ 1 := mk_ne_one_of fun c => by
  rw [coe_zS]
  exact ZM_ne_smul c

theorem zP_eq : zP = ⁅yP, xP⁆ := by
  obtain ⟨-, -, h, -⟩ := rels
  rw [commutatorElement_def]
  calc zP = zP * xP * yP * yP⁻¹ * xP⁻¹ := by group
    _ = yP * xP * yP⁻¹ * xP⁻¹ := by rw [h]

noncomputable abbrev RP : Subgroup PU5 := Subgroup.closure ({xP, yP} : Set PU5)

theorem commute_of_mem_RP {g : PU5} (hx : g * xP = xP * g) (hy : g * yP = yP * g) {r : PU5}
    (hr : r ∈ RP) : g * r = r * g := by
  induction hr using Subgroup.closure_induction with
  | mem q hq =>
    rcases hq with rfl | hq
    · exact hx
    · rw [Set.mem_singleton_iff] at hq
      rw [hq]
      exact hy
  | one => simp
  | mul a b _ _ ha hb =>
    calc g * (a * b) = (g * a) * b := by group
      _ = a * (g * b) := by rw [ha]; group
      _ = a * b * g := by rw [hb]; group
  | inv a _ ha =>
    calc g * a⁻¹ = a⁻¹ * (a * g) * a⁻¹ := by group
      _ = a⁻¹ * (g * a) * a⁻¹ := by rw [ha]
      _ = a⁻¹ * g := by group

theorem card_RP : Nat.card RP = 125 := by
  obtain ⟨hx5, hy5, -, hzx, hzy, -⟩ := rels
  refine card_closure_heis hx5 hy5 ?_ ?_ (zP_eq ▸ zP_ne_one)
  · rw [← zP_eq]
    exact hzx
  · rw [← zP_eq]
    exact hzy

theorem zP_comm {r : PU5} (hr : r ∈ RP) : zP * r = r * zP := by
  obtain ⟨-, -, -, hzx, hzy, -⟩ := rels
  exact commute_of_mem_RP hzx hzy hr

theorem zpowers_comm {a : PU5} (ha : a ∈ Subgroup.zpowers zP) {r : PU5} (hr : r ∈ RP) :
    a * r = r * a := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact ((Commute.zpow_left (zP_comm hr) n)).eq

theorem zP_mem : zP ∈ RP := by
  rw [zP_eq, commutatorElement_def]
  have hx : xP ∈ RP := Subgroup.subset_closure (Set.mem_insert _ _)
  have hy : yP ∈ RP := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact RP.mul_mem (RP.mul_mem (RP.mul_mem hy hx) (RP.inv_mem hy)) (RP.inv_mem hx)

theorem zP_pow_five : zP ^ 5 = 1 := by
  obtain ⟨hx5, -, -, hzx, -⟩ := rels
  rw [zP_eq] at hzx ⊢
  exact CGT.PushingUpLit.CGT6M.commutator_pow_eq_one_of_commute hzx hx5

theorem orderOf_zP : orderOf zP = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime zP_pow_five zP_ne_one

theorem commutator_mem {a b : PU5} (ha : a ∈ RP) (hb : b ∈ RP) :
    a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers zP := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hZR : Subgroup.zpowers zP ≤ RP := Subgroup.zpowers_le.mpr zP_mem
  set Z' := (Subgroup.zpowers zP).subgroupOf RP with hZ'
  have hZn : Z'.Normal := ⟨fun n hn g => by
    rw [hZ', Subgroup.mem_subgroupOf] at hn ⊢
    have e : ((g * n * g⁻¹ : RP) : PU5) = (n : PU5) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← zpowers_comm hn g.2]
      group
    rw [e]
    exact hn⟩
  have hZ'5 : Nat.card Z' = 5 := by
    rw [hZ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv, Nat.card_zpowers,
      orderOf_zP]
  have hQ : Nat.card (RP ⧸ Z') = 5 ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
    rw [card_RP, hZ'5] at h1
    omega
  have hc := IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ
  have h1 := hc.is_comm.comm (QuotientGroup.mk (⟨b, hb⟩ : RP) : RP ⧸ Z')
    (QuotientGroup.mk (⟨a, ha⟩ : RP))
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hZ',
    Subgroup.mem_subgroupOf] at h1
  have hw : a⁻¹ * b⁻¹ * a * b ∈ Subgroup.zpowers zP := by
    have e : (((⟨b, hb⟩ * ⟨a, ha⟩ : RP)⁻¹ * (⟨a, ha⟩ * ⟨b, hb⟩) : RP) : PU5) =
        a⁻¹ * b⁻¹ * a * b := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [← e]
    exact h1
  have e2 : a * b * a⁻¹ * b⁻¹ = (a * b) * (a⁻¹ * b⁻¹ * a * b) * (a * b)⁻¹ := by group
  rw [e2, ← zpowers_comm hw (RP.mul_mem ha hb), mul_inv_cancel_right]
  exact hw

theorem conj_tP_xP : tP * xP * tP⁻¹ = yP := by
  obtain ⟨-, -, -, -, -, h, -⟩ := rels
  rw [h, mul_inv_cancel_right]

theorem conj_tP_yP : tP * yP * tP⁻¹ = xP ^ 3 * zP ^ 4 := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := rels
  rw [h, mul_inv_cancel_right]

theorem tP_mem_normalizer : tP ∈ Subgroup.normalizer (RP : Set PU5) := by
  have hx : xP ∈ RP := Subgroup.subset_closure (Set.mem_insert _ _)
  have hy : yP ∈ RP := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  refine Subgroup.mem_normalizer_fintype fun r hr => ?_
  induction hr using Subgroup.closure_induction with
  | mem q hq =>
    rcases hq with rfl | hq
    · rw [conj_tP_xP]
      exact hy
    · rw [Set.mem_singleton_iff] at hq
      rw [hq, conj_tP_yP]
      exact RP.mul_mem (RP.pow_mem hx _) (RP.pow_mem zP_mem _)
  | one => simp
  | mul a b _ _ ha hb =>
    have e : tP * (a * b) * tP⁻¹ = (tP * a * tP⁻¹) * (tP * b * tP⁻¹) := by group
    rw [e]
    exact RP.mul_mem ha hb
  | inv a _ ha =>
    have e : tP * a⁻¹ * tP⁻¹ = (tP * a * tP⁻¹)⁻¹ := by group
    rw [e]
    exact RP.inv_mem ha

theorem tP_pow_four_inv {r : PU5} (hr : r ∈ RP) :
    tP ^ 4 * r * (tP ^ 4)⁻¹ * r ∈ Subgroup.zpowers zP := by
  obtain ⟨hx5, hy5, -, hzx, hzy, -, -, h8, h9⟩ := rels
  induction hr using Subgroup.closure_induction with
  | mem q hq =>
    rcases hq with rfl | hq
    · have e : tP ^ 4 * xP * (tP ^ 4)⁻¹ * xP = zP ^ 3 := by
        rw [h8, mul_inv_cancel_right, mul_assoc, (Commute.pow_left hzx 3).eq, ← mul_assoc,
          ← pow_succ, hx5, one_mul]
      rw [e]
      exact Subgroup.npow_mem_zpowers _ _
    · rw [Set.mem_singleton_iff] at hq
      rw [hq]
      have e : tP ^ 4 * yP * (tP ^ 4)⁻¹ * yP = zP := by
        rw [h9, mul_inv_cancel_right, mul_assoc, hzy, ← mul_assoc, ← pow_succ, hy5, one_mul]
      rw [e]
      exact Subgroup.mem_zpowers _
  | one => simp
  | mul a b haR hbR ha hb =>
    set α := tP ^ 4 * a * (tP ^ 4)⁻¹ * a with hα
    set β := tP ^ 4 * b * (tP ^ 4)⁻¹ * b with hβ
    have hβa : β * a⁻¹ = a⁻¹ * β := zpowers_comm hb (RP.inv_mem haR)
    have e : tP ^ 4 * (a * b) * (tP ^ 4)⁻¹ * (a * b) =
        α * β * (a⁻¹ * b⁻¹ * a⁻¹⁻¹ * b⁻¹⁻¹) := by
      calc tP ^ 4 * (a * b) * (tP ^ 4)⁻¹ * (a * b) = α * a⁻¹ * (β * b⁻¹) * a * b := by
            rw [hα, hβ]
            group
        _ = α * (a⁻¹ * β) * b⁻¹ * a * b := by group
        _ = α * (β * a⁻¹) * b⁻¹ * a * b := by rw [← hβa]
        _ = α * β * (a⁻¹ * b⁻¹ * a⁻¹⁻¹ * b⁻¹⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (commutator_mem (RP.inv_mem haR) (RP.inv_mem hbR))
  | inv a haR ha =>
    set α := tP ^ 4 * a * (tP ^ 4)⁻¹ * a with hα
    have hαa : α * a = a * α := zpowers_comm ha haR
    have e : tP ^ 4 * a⁻¹ * (tP ^ 4)⁻¹ * a⁻¹ = α⁻¹ := by
      calc tP ^ 4 * a⁻¹ * (tP ^ 4)⁻¹ * a⁻¹ = a * α⁻¹ * a⁻¹ := by
            rw [hα]
            group
        _ = α⁻¹ * a * a⁻¹ := by rw [(Commute.inv_left hαa).eq.symm]
        _ = α⁻¹ := mul_inv_cancel_right _ _
    rw [e]
    exact Subgroup.inv_mem _ ha

theorem ks163U35NoIndex25 : KS163U35NoIndex25 := by
  intro _ H hH
  have hs : IsSimpleGroup PU5 := by
    have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 5 1 le_rfl (by norm_num)
    exact equivPU.symm.isSimpleGroup
  refine card_ne_5040 hs card_PU5 card_RP (fun a ha r hr => zpowers_comm ha hr)
    (fun a ha b hb => commutator_mem ha hb) tP_mem_normalizer (fun r hr => tP_pow_four_inv hr)
    (H.map equivPU.toMonoidHom) ?_
  rw [Subgroup.card_map_of_injective equivPU.injective, hH]

end CFSG.RankThree.PartTwo.Sec16.Res3U35
