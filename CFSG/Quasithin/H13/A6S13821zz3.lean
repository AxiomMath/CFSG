module

public import CFSG.Quasithin.H13.A6S13821zz2
public import CFSG.Quasithin.H13.A6S13821p
public import CFSG.Quasithin.H13.A6S13821za
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.H13.A6S13824o
public import CFSG.Quasithin.H13.J4Classes
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix11

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.E1.LiftS5
open scoped commutatorElement

attribute [local instance] commGroupOfFact

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem false_of_alt5_13820a
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h1337 : Stmt13_3_7) (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hHK : H = K ⊔ (S.L1 ⊔ T)) {n : ℕ}
    (hn : 2 ≤ n) (hLie : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))
    (hF : HypF918 T V L (fsuV1 T V) S.V3 H K) (hK₀ : conjClosure K T = K)
    (hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) {I : Subgroup G} (hV₁I : fsuV1 T V ≤ I)
    (hIU : I ≤ conjClosure S.V3 H) (hirr : IsIrrPlusTilde (fsuV1 T V) (conjClosure K T) I)
    (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))]
    (hA5 : AlternatingNatural (autSec (autSub (autIH (fsuV1 T V) I H K)
        (subM (fsuV1 T V) (conjClosure I H) I)) ⊤
        ((subM (fsuV1 T V) (conjClosure I H) I ⊓
          fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
            (subM (fsuV1 T V) (conjClosure I H) I))) ⊤ ⊥ 5)
    {c : G} (hcX : c ∈ S.X13820) (hc3 : c ^ 3 = 1)
    (hfpf : ∀ u ∈ conjClosure S.V3 H, c * u * c⁻¹ * u⁻¹ ∈ fsuV1 T V → u ∈ fsuV1 T V)
    (htri : ∀ y ∈ S.X13820, y ∈ pCoreOf 2 H ∨ y * c⁻¹ ∈ pCoreOf 2 H ∨ y * c ∈ pCoreOf 2 H)
    (hdich : ∀ h ∈ H, h * c * h⁻¹ * c⁻¹ ∈ pCoreOf 2 H ∨ h * c * h⁻¹ * c ∈ pCoreOf 2 H)
    {s : G} (hsT : s ∈ T) (hsc : s * c * s⁻¹ * c ∈ pCoreOf 2 H)
    (hsK : ∀ k ∈ K, s * k * s⁻¹ * k⁻¹ ∈ pCoreOf 2 H) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF1 := (hS.hF H hH).toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hLTH : S.L1 ⊔ T ≤ H := hF1.L₁T_le_H
  have hcH : c ∈ H := hLTH (Subgroup.mem_sup_left (S.plusData_X13820.le_L1 hcX))
  have hcV := S.not_mem_centralizer_of_fpf hS hH hfpf
  have hsyl := S.isSylowTwoOf_TK hH hKH hKn
  obtain ⟨p₀, hp₀, hp₀'⟩ := A6L24.exists_p0 hKH hKn e hsyl
  have hiff := A6L24.fix_iff hKH hKn e hsyl (S.pCoreOf_le_TK hH hKH hKn) hp₀ hp₀'
  have hNTK := S.L1T_le_normalizer_TK h1334 hS hH hKH hKn hn hLie
  have hfixLT : ∀ g : ↥H, (g : G) ∈ S.L1 ⊔ T → quotPerm hKn e g p₀ = p₀ := fun g hg =>
    (hiff g).mpr (hNTK hg)
  have hBM := S.borel_le_M h13 h1334 hS hH hKH hKn hn hLie
  obtain ⟨d, hdH, hdL, -, -, hd3, hψd⟩ :=
    S.exists_d_13820a h1337 hS hH hKH hKn e hiff hBM hcX hc3 hcV htri hsT hsc hsK
  have hTKR : T ⊓ K ≤ pCoreOf 2 (S.L1 ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right) hNTK hsyl.2.1
  rcases S.exists_transv_or_quad h36c h139 h1334 h13 h13314 h13315 h1356two hS hH hK hKn hHK
    with ⟨x, hxR, htr⟩ | ⟨Y, hYR, hYq, hY4⟩
  ·
    have hxH : x ∈ H := hLTH (pCoreOf_le 2 _ hxR)
    have h1 := (pCoreOf 2 H).inv_mem (S.comm_c_of_mem_R hS hH hcX hc3 hfpf hdich hxR)
    have e' : (c * x * c⁻¹ * x⁻¹)⁻¹ = x * c * x⁻¹ * c⁻¹ := by group
    rw [e'] at h1
    exact S.not_transv_of_comm hS hH hcH hfpf hxH h1 htr
  ·
    obtain ⟨y₁, hy₁Y, y₂, hy₂Y, hy₁Q, hy₂Q, hy₁₂⟩ :=
      A6S20.exists_two_cosets (Y := Y) (Q := pCoreOf 2 H) (by omega)
    have hlift : ∀ y ∈ Y, ∃ t ∈ K, y ∈ Subgroup.normalizer (I : Set G) ∧
        t⁻¹ * y ∈ pCoreOf 2 H := by
      intro y hyY
      have hyR := hYR hyY
      have hyH : y ∈ H := hLTH (pCoreOf_le 2 _ hyR)
      have hV4 := S.isV4_of_mem_R_13820a hLTH hKn e hfixLT hdH hdL hd3 hψd hyR
      obtain ⟨t, htTK, hψt⟩ := hp₀' _ hV4
      have htR := hTKR htTK
      have htyR : t⁻¹ * y ∈ pCoreOf 2 (S.L1 ⊔ T) := (pCoreOf 2 _).mul_mem
        ((pCoreOf 2 _).inv_mem htR) hyR
      have htyH : t⁻¹ * y ∈ H := hLTH (pCoreOf_le 2 _ htyR)
      have hψ1 : quotPerm hKn e ⟨t⁻¹ * y, htyH⟩ = 1 := by
        have e' : (⟨t⁻¹ * y, htyH⟩ : ↥H) = (⟨t, hKH htTK.2⟩ : ↥H)⁻¹ * ⟨y, hyH⟩ := rfl
        rw [e', map_mul, map_inv, hψt]
        exact inv_mul_cancel _
      refine ⟨t, htTK.2, hTI (hF.pCoreOf_L₁T_le_T hyR), ?_⟩
      exact S.mem_QH_of_mem_R hS hH hK hKn hHK e htyR htyH hψ1
    obtain ⟨t₁, ht₁K, hy₁I, hyt₁⟩ := hlift y₁ hy₁Y
    obtain ⟨t₂, ht₂K, hy₂I, hyt₂⟩ := hlift y₂ hy₂Y
    have hq : ∀ u ∈ conjClosure S.V3 H, ⁅⁅u, y₁⁆, y₂⁆ = 1 ∧ ⁅⁅u, y₁⁆, y₁⁆ = 1 := by
      intro u hu
      have hc1 : ⁅u, y₁⁆ ∈ ⁅conjClosure S.V3 H, Y⁆ := Subgroup.commutator_mem_commutator hu hy₁Y
      have h2 : ⁅⁅u, y₁⁆, y₂⁆ ∈ ⁅⁅conjClosure S.V3 H, Y⁆, Y⁆ :=
        Subgroup.commutator_mem_commutator hc1 hy₂Y
      have h3 : ⁅⁅u, y₁⁆, y₁⁆ ∈ ⁅⁅conjClosure S.V3 H, Y⁆, Y⁆ :=
        Subgroup.commutator_mem_commutator hc1 hy₁Y
      rw [hYq, Subgroup.mem_bot] at h2 h3
      exact ⟨h2, h3⟩
    exact A6S20.false_of_quad_alt5 hF hV₁I hIU hK₀ hS' hirr hA5 ht₁K ht₂K hy₁I hy₂I hyt₁ hyt₂ hy₁Q
      hy₂Q hy₁₂ hq

theorem false_of_l2_13820a
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hA21 : AsA21SQTKSection) (h42 : AsB42)
    (hF10 : Vol2.Ch10.SecA.Facts10_1) (h1337 : Stmt13_3_7) (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) {H K : Subgroup G} {n : ℕ}
    (hC : S.Ctx13820 H K n) (ha : S.Case13820aHyp H K)
    (hL2 : IsPSL 2 2 n (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hF, I, hV₁I, hIU, hirrT, hTI, hFF⟩ :=
    S.exists_ff_13820a h36c h37 h38 h139 h1334 h13 hD310 hD391 hI4 hC ha
  obtain ⟨hS, hH, hK, hKn, hHK, hn, hLie⟩ := hC
  obtain ⟨-, hXc, hHX, t, htH, htK, htX⟩ := ha
  obtain ⟨e₁⟩ := S.kst_equiv hS hH hK
  have hLieQ : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n := lieF2n_congr e₁.symm hLie
  have h1 : IsPSL 2 2 n ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    IsPSL.of_mulEquiv (QuotientGroup.congr _ _ e₁.symm (Subgroup.map_center_eq e₁.symm)) hL2
  have hperf : commutator (↥K ⧸ CFSG.pCore 2 ↥K) = ⊤ := by
    have hK' : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK)
    have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact Group.isPerfect_def.mp this
  obtain ⟨hZ, F, hFf, hFfin, hFn, ⟨eK⟩⟩ := A6S20.exists_equiv_sl2_of_perfect hperf
    E1.ThinA5.odd_card_center_quot_pCore hn h1
  have hQs : IsSimpleGroup ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (CFSG.QuasithinUnique.A5.C25.fusionIsBenderGroup_of_isPSL h1)
  have hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).isSimpleGroup
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hK₀ : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun t ht k hk =>
      (Subgroup.mem_normalizer_iff.mp (hKn (hTH ht)) k).mp hk) (le_conjClosure K T)
  have := factElem hF hIU
  have hSQ := S.sqtkGroup_of_mem_Hz hH
  have hirr := isIrrPlusTilde_of_module hF hV₁I hIU hirrT
  obtain ⟨c, hcX, hc3, hθ, hfpf, htri, hdich⟩ := S.exists_c_13820a' hS hH hHX
  have P := S.plusData_X13820
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hcH : c ∈ H := hL1H (P.le_L1 hcX)
  have hXO : pCoreOf 2 S.X13820 ≤ pCoreOf 2 H := by
    have hchar : (CFSG.Open.pCore 2 ↥S.X13820).Characteristic := by
      infer_instance
    have hHO : H ≤ Subgroup.normalizer ((pCoreOf 2 S.X13820 : Subgroup G) : Set G) :=
      hHX.trans (normalizer_le_normalizer_map_of_characteristic (CFSG.Open.pCore 2 ↥S.X13820))
    exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (P.le_L1.trans hL1H)) hHO
      (pCoreOf_isPGroup 2 _)
  obtain ⟨s₀, hs₀H, hs₀2, hs₀c, hs₀K⟩ := A6S20.exists_two_part (le_normalizer_pCoreOf 2 H)
    hKH htH hcH (hXO (htX c hcX)) htK
  have hTsyl : IsSylowTwoOf T H := hF.toHypF98.toHypF91.sylow_H
  obtain ⟨s, hsT, ⟨e₂, hs2⟩, hsc, hsK⟩ := A6S20.exists_two_part_mem (le_normalizer_pCoreOf 2 H)
    hKn hTsyl hcH hdich hs₀H hs₀2 hs₀c hs₀K
  have hcK : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 H := hXc c hcX
  have hII := A6S20.inf_conj_le_centralizerMod hF hK₀ hV₁I hIU hirrT hTI hcH hc3 hθ hcK hsT
    hsK hsc hs2
  have hKI : K ≤ Subgroup.normalizer (I : Set G) := (le_conjClosure K T).trans hirr.1
  have hJN := (A6S20.sup_conj_le_normalizer hV₁I hIU hθ (F7.isSylowTwoOf_pCoreOf_le hTsyl) hTI
    hKI (le_normalizer_pCoreOf 2 H hcH) (hKn hcH)
    (fun t ht => (Subgroup.mem_normalizer_iff.mp (hHX (hTH ht)) c).mp hcX) htri).1
  have hRc : ∀ b ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T), c * b * c⁻¹ * b⁻¹ ∈ pCoreOf 2 H :=
    fun b hb => S.comm_c_of_mem_R hS hH hcX hc3 hfpf hdich hb
  have hUJ := A6S20.commutator_le_sup_sl2 hA21 h42 hF10 hSQ hF hK₀ hn hFn eK hS' hV₁I hIU hirrT
    hTI hFF hcH hII hJN hRc
  rcases A6S20.ff_cases_sl2 hA21 h42 hF10 hSQ hF hK₀ hn hFn eK hS' hV₁I hIU hirrT hTI hFF with
    ⟨m, -, hnat⟩ | hA5
  ·
    have hcV := S.not_mem_centralizer_of_fpf hS hH hfpf
    have hBM := S.borel_le_M h13 h1334 hS hH hKH hKn hn hLieQ
    exact A6S20.false_of_natural hF hK₀ hS' hn hFn eK hV₁I hIU hirr hnat hcH hII hUJ
      (S.isSylowTwoOf_TK hH hKH hKn) fun b hb =>
        S.borel_comm_V3_13820a hS hH hKH hKn hBM hcX hc3 hcV hfpf hcK htri hsT hsc hsK hb
  ·
    obtain ⟨-, -, -, ⟨eL⟩, -, -⟩ :=
      A6S20.ff_data_sl2 hA21 hSQ hF hK₀ eK hS' hV₁I hIU hirrT hTI hFF
    obtain ⟨π, Ψ, hπs, -⟩ := Vol2.Ch10.SecD.C10P06.exists_isA5Coord hA5
    have hdvd := Subgroup.card_dvd_of_surjective hπs
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      try rfl
    have hcardL : Nat.card ↥(autSec (autSub (autIH (fsuV1 T V) I H K)
        (subM (fsuV1 T V) (conjClosure I H) I)) ⊤
        ((subM (fsuV1 T V) (conjClosure I H) I ⊓
          fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
            (subM (fsuV1 T V) (conjClosure I H) I))) = 2 ^ n * (2 ^ n * 2 ^ n - 1) := by
      rw [Nat.card_congr eL.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hFn]
      have e2 : ∀ q : ℕ, ∏ j ∈ Finset.Icc 2 2, (q ^ j - 1) = q ^ 2 - 1 := fun q => by
        rw [Finset.Icc_self, Finset.prod_singleton]
      rw [e2]
      ring_nf
    rw [hcardL, h60] at hdvd
    have hn2 : n = 2 := by
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      have hq4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have hq : 2 ^ n ≤ 4 := by
        by_contra hgt
        push Not at hgt
        have h5 : 5 ≤ 2 ^ n := hgt
        have h24 : 24 ≤ 2 ^ n * 2 ^ n - 1 := by
          have : 25 ≤ 2 ^ n * 2 ^ n := by nlinarith
          omega
        have : 5 * 24 ≤ 2 ^ n * (2 ^ n * 2 ^ n - 1) := Nat.mul_le_mul h5 h24
        omega
      have h4 : 2 ^ n = 2 ^ 2 := by omega
      exact Nat.pow_right_injective (le_refl 2) h4
    subst hn2
    obtain ⟨e⟩ := S.exists_equiv_alt_of_l24 hS hH hK hL2
    exact S.false_of_alt5_13820a h36c h139 h1334 h13 h13314 h13315 h1356two h1337 hS hH hK hKn
      hHK hn hLieQ e hF hK₀ hS' hV₁I hIU hirr hTI hA5 hcX hc3 hfpf htri hdich hsT hsc hsK

end Setting4

end CFSG.Quasithin.H13.A6
