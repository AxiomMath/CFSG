module

public import CFSG.Quasithin.H13.A6S13824n
public import CFSG.Quasithin.H13.A6S13824l
public import CFSG.Quasithin.H13.A6S13824h
public import CFSG.Quasithin.H13.A6S13824i
public import CFSG.Quasithin.Background.HA7Rec
public import CFSG.Quasithin.H13.A6S13824f
public import CFSG.Quasithin.H13.A6S13824m

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative commutatorElement

theorem lem13824_of
    (h1376 : Lem1376Full) (h21 : Lem13821) (h16 : Lem13816)
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two)
    (hred : ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
      S.Hyp138 → ∀ H ∈ S.Hz, ∀ K ∈ cComp H, IsAlt 7 ↥(S.KSt H K) →
      ∀ [IsMulCommutative ↥(conjClosure S.V3 H)] (W : Subgroup G), fsuV1 T V ≤ W →
      W < conjClosure S.V3 H → H ≤ Subgroup.normalizer (W : Set G) →
      (∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
        H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H) →
      (∀ x ∈ pCoreOf 2 (S.L1 ⊔ T), ¬ InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V)) →
      XMod.IsIrrSec ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        (W.subgroupOf (conjClosure S.V3 H)))
        (⊥ : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
          (W.subgroupOf (conjClosure S.V3 H)))) ⊤) : Lem13824 := by
  intro G _ _ T L V S hS H hH K hK h7
  obtain ⟨hL1K, -, ⟨hKT, -⟩, hUK⟩ := h21 G T L V S hS H hH K hK
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := (h16 G T L V S hS H hH K hK).1.1
  have hKH : K ≤ H := le_of_mem_cComp hK
  obtain ⟨α, hαs, hαk⟩ := S.exists_alpha7 hS hH hKH h7
  have hsimp : IsSimpleGroup ↥(S.KSt H K) := by
    obtain ⟨e⟩ := h7
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    exact e.isSimpleGroup
  have hnab : ∃ k ∈ K, ∃ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∉ pCoreOf 2 H := by
    obtain ⟨a, ha⟩ := hαs ⟨_, A7F.a7_mem⟩
    obtain ⟨b, hb⟩ := hαs ⟨_, A7F.b7_mem⟩
    refine ⟨a, a.2, b, b.2, fun h => ?_⟩
    have h1 : α (a * b * a⁻¹ * b⁻¹) = 1 := (hαk _).2 (by simpa using h)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb] at h1
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h2
    exact A7F.ab7_ne_ba7 (mul_inv_eq_one.1 (by rw [mul_inv_rev, ← mul_assoc]; exact h2))
  have hd : S.DK H K := ⟨hS, hH, hK, hKn, hKT.symm, hL1K, hUK, hsimp, hnab⟩
  have hF := hd.hF
  have hF1 := hF.toHypF91
  have hab := L13825.isElemAbelian_UH hS hH
  have : IsMulCommutative ↥(conjClosure S.V3 H) := hab.1
  obtain ⟨ρ, -, hρk, hρ1⟩ := hd.exists_rho7 hαs hαk
  obtain ⟨W, hV1W, hWU, hHW, hmax⟩ := hd.exists_max
  have htriv := hd.triv_of_max7 h21 h16 h36 h139 h1334 h13 h13314 h13315 h1356two hαs hαk
    (ρ := ρ) (fun k => hρk k) hρ1 hV1W hWU hHW hmax
  have hW : ∀ u ∈ conjClosure S.V3 H, u ∈ W ↔ ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V :=
    fun u hu => hd.mem_max_iff_of_triv hWU hmax htriv hu
  have hsU := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
  have hsV := hd.secU le_rfl hd.V1_lt_UH.le le_rfl (le_normalizer_conjClosure _ _)
    hF1.H_normalizes_V₁ (hd.knt_top hd.V1_lt_UH)
  have hcomm : commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊤ := hd.commV_autSec_eq_top
  obtain ⟨hirrK, hcard⟩ : XMod.IsIrrSec ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      (W.subgroupOf (conjClosure S.V3 H)))
      (⊥ : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        (W.subgroupOf (conjClosure S.V3 H)))) ⊤ ∧
      Nat.card (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        (W.subgroupOf (conjClosure S.V3 H))) ≤ 2 ^ 12 := by
    by_cases hA : ∃ x ∈ pCoreOf 2 (S.L1 ⊔ T),
        InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V)
    · obtain ⟨h, hhP, ht⟩ := hA
      have hh : h ∈ H := hF1.L₁T_le_H (pCoreOf_le 2 _ hhP)
      have hhQ : h ∉ pCoreOf 2 H := fun hq => ht.1 fun x hx => by
        rw [hF1.pCoreOf_eq_centralizerMod] at hq
        exact hq.2.2 x hx
      obtain ⟨hne, w, hw⟩ := L13825.exists_transvectionWith_sigmaH hd.hH hh ht
      have hsq := B1.tv_sq (fun v => by rw [pow_two]; exact hsV.sec_sq v) hw hne
      have hh2 : h * h ∈ pCoreOf 2 H := by
        have h1 := (L13825.sigmaH_eq_one_iff hd.hH hF1 (⟨h, hh⟩ * ⟨h, hh⟩)).1
          (by rw [map_mul]; exact hsq)
        simpa using h1
      obtain ⟨c, hc⟩ := ht.2
      have h64 := hsU.card_le_64_of_transv hmax hαs (ρ := ρ) (fun k => hρk k) hρ1 hh hhQ hh2
        (z := c) fun x hx => (hc x hx).imp (fun h => hV1W h) (fun h => hV1W h)
      exact ⟨hsU.irrK7 hmax hαs hαk h64, h64.trans (by norm_num)⟩
    · push Not at hA
      obtain ⟨γ, γ', g, s, hDγ, -, hpos, hle⟩ := S.case2_of_no_transv_loc hF hA
      obtain ⟨hq, -⟩ := hF.F916_2_aux s hpos hle
      have hUγel := hF.isElemAbelian_Uγ (g := g)
      refine ⟨hred G T L V S hS H hH K hK h7 W hV1W hWU hHW hmax hA, ?_⟩
      refine hsU.card_le_4096_of_le_sq hmax hαs (ρ := ρ) (fun k => hρk k) hρ1 (hF.Uγ_le_H s)
        (hd.not_Uγ_le s hDγ) (A6Gen.comm_mem_of_elem hUγel _) (A6Gen.sq_mem_of_elem hUγel _) ?_
      refine (Subgroup.relIndex_le_of_le_left ?_ (relIndex_ne_zero' _ _)).trans hq.2.2.2.2
      intro x hx
      exact ⟨hx.1, hHW (hd.UH_le_H hx.1), fun u hu => hV1W (hx.2.2 u hu)⟩
  obtain ⟨-, -, h3, -, h4, -⟩ := h1376 G T L V S hS.hNS hS.hNU H hH hab K hK
  rcases hsU.ident7 hmax hαs hαk hirrK hcard with ⟨π, hπ⟩ | h16'
  ·
    obtain ⟨π', hπ'⟩ := hd.exists_realizesVia_top (FFModel.altDn_isActionModel 7) hV1W hWU hHW
      hW hπ
    obtain ⟨-, -, -, hcases⟩ := h3 7 (by rw [hcomm, inf_top_eq]; exact ⟨π', hπ'⟩)
    rcases hcases with ⟨h6, -⟩ | ⟨-, hhat, π₁, β₁, hRB, -, hV3⟩
    · exact absurd h6 (by norm_num)
    refine hd.false_of_D7 hhat hRB hV3 ?_
    by_cases hA : ∃ x ∈ pCoreOf 2 (S.L1 ⊔ T),
        InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V)
    · exact Or.inl hA
    right
    push Not at hA
    obtain ⟨γ, γ', g, s, hDγ, hDH, -, hle⟩ := S.case2_of_no_transv_loc hF hA
    have hHK' : H = K ⊔ (S.L1 ⊔ T) := by
      rw [← sup_assoc, sup_eq_left.2 hL1K]
      exact hKT.symm
    have hgen := lem13818Gen_holds h36 h139 h1334 h13 G T L V S hS H hH K hK hKn hHK' γ γ' g s
      (conjClosure S.V3 H) le_rfl hDH.not_ge
    have hm := S.lem13818Four_loc hS.hNS h13315 h1356two hH hF h13314 hA s hDγ hDH hle hgen
    obtain ⟨c, hcH, hcR⟩ := exists_conj_Vγ_le hF s
    refine ⟨conjSub c (F8.Uγ V H (g : G)), hcR, ?_, ?_⟩
    · have h1 := congrArg (conjSub c) (S.comm_comm_UH_Vγ hF s)
      rwa [← conjSub_commutator, ← conjSub_commutator,
        conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure S.V3 H hcH), conjSub_bot] at h1
    · have hY2 : IsPGroup 2 (conjSub c (F8.Uγ V H (g : G))) :=
        (pCoreOf_isPGroup 2 _).to_le hcR
      rw [HypF98.relIndex_eq_two_pow_mIdx hY2]
      have hQ : conjSub c (pCoreOf 2 H) = pCoreOf 2 H :=
        conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hcH)
      rw [← hQ, ← conjSub_inf, F9.mIdx_conjSub]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ mIdx (F8.Uγ V H (g : G)) (F8.Uγ V H (g : G) ⊓ pCoreOf 2 H) :=
          Nat.pow_le_pow_right (by norm_num) hm
  ·
    have hiso := hsU.nonempty_iso7 hαs hαk
    have hA4 := CFSG.Quasithin.H.A7.a7Four_of_faithful hiso (fun _ _ _ _ => Subgroup.mem_top _)
      (fun u _ => hsU.sec_sq u) (by rw [Subgroup.card_top, h16']; norm_num)
      (fun h _ hfix => MulEquiv.ext fun u => hfix u (Subgroup.mem_top u))
    obtain ⟨α₄, π₄, hπ₄⟩ := hA4
    obtain ⟨π', hπ'⟩ := hd.exists_realizesVia_top (FFModel.a7Four_isActionModel α₄) hV1W hWU
      hHW hW hπ₄
    exact h4 ⟨α₄, by rw [hcomm, inf_top_eq]; exact ⟨π', hπ'⟩⟩

end CFSG.Quasithin.H13.A6
