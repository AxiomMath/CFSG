module

public import CFSG.Quasithin.H13.L32A771g
public import CFSG.Quasithin.H13.L32A771d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx72

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx72 G T L V l₀)
include C

theorem Q_le_R1 (h13314 : A6.Stmt13_3_14) :
    pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  rw [← lemma14_7_4_four C.setting C.hF C.h1222 C.h1332 C.h1334 h13314]
  exact le_sup_left

theorem Q_le_centralizer : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) := by
  rw [← C.hF.cT]
  exact inf_le_right

theorem T_le_normalizer_sL' : T ≤ Subgroup.normalizer (sL T L V : Set G) := fun _ ht =>
  mem_normalizer_conjClosure_of
    (le_normalizer_conjClosure V _ (C.hF.T_normalizes_V₁ ht)) (C.hyp.normalizes C.h13322 ht)

theorem T_le_normalizer_l1 : T ≤ Subgroup.normalizer (L₁Of L (fsuV1 T V) : Set G) := by
  obtain ⟨V₂, hV2⟩ := C.hyp.exists_V2 C.h13322 C.hMod C.h1222
  have : IsMulCommutative ↥V := (C.hMod G T L V C.hyp.hyp C.hyp.fsu).1.1
  exact (C.hyp.set14 C.h1222 C.h1332 C.h1334 hV2).T_Lp

variable {x : G} (hxL1 : x ∈ L₁Of L (fsuV1 T V)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
include hxL1 hx3 hx1

theorem relIndex_pCoreOf_l1 (hu0 : u0 T V = fsuV1 T V)
    (hQL : IsL24Section (kz T V) (pCoreOf 2 (hz T V))
      (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G))) :
    (pCoreOf 2 (L₁Of L (fsuV1 T V)) ⊓ Subgroup.centralizer ({x} : Set G)).relIndex
      (pCoreOf 2 (L₁Of L (fsuV1 T V))) = 4 ^ 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTH : T ≤ hz T V := C.hF.T_le_H
  have hL1H : L₁Of L (fsuV1 T V) ≤ hz T V := le_sup_left.trans C.hF.L₁T_le_H
  have hQHR1 : pCoreOf 2 (hz T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le_of_le C.hyp hTH).trans le_sup_right)
      ((sup_le hL1H hTH).trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hR14 : (pCoreOf 2 (hz T V)).relIndex (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) = 4 :=
    (R1_le_kz_sup C.setting C.hF C.h63 C.h1222 C.h1332 C.h1334).2
  have hR1T : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T := pCoreOf_le_of_le C.hyp le_sup_right
  have hTL1 := C.T_le_normalizer_l1
  have hTP1 : T ≤ Subgroup.normalizer (pCoreOf 2 (L₁Of L (fsuV1 T V)) : Set G) :=
    hTL1.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hcR := relIndex_inf_centralizer_mul hQHR1 (C.inf_centralizer_R1_le hxL1 hx3 hx1)
  rw [hR14, (C.relIndex_centralizer_QH hxL1 hx3 hx1 hu0 hQL).2.2] at hcR
  have hP1R1 : pCoreOf 2 (L₁Of L (fsuV1 T V)) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 _) hTP1) (pCoreOf_isPGroup 2 _)
  have hxR1 : x ∈ Subgroup.normalizer (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hxL1)
  have hL1R : L₁Of L (fsuV1 T V) ⊓ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤
      pCoreOf 2 (L₁Of L (fsuV1 T V)) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun l hl => mem_normalizer_inf_of (Subgroup.le_normalizer hl)
        (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hl)))
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
  have hcP := relIndex_inf_centralizer_eq hx3 hP1R1 (hR1T.trans hTP1)
    (le_normalizer_pCoreOf 2 _ hxL1)
    (not_dvd_card_of_isPGroup_two (pCoreOf_isPGroup 2 _) Nat.prime_three (by norm_num))
    (fun g hg => hL1R (Subgroup.mem_inf.mpr ⟨?_, ?_⟩))
  · rw [← hcP, hcR]
    norm_num
  · have h1 := (Subgroup.mem_normalizer_iff.mp (hTL1 (inv_mem (hR1T hg))) x).mp hxL1
    rw [inv_inv] at h1
    exact mul_mem h1 (inv_mem hxL1)
  · rw [show g⁻¹ * x * g * x⁻¹ = g⁻¹ * (x * g * x⁻¹) by group]
    exact mul_mem (inv_mem hg) ((Subgroup.mem_normalizer_iff.mp hxR1 g).mp hg)

theorem relIndex_sL (hu0 : u0 T V = fsuV1 T V) (h13314 : A6.Stmt13_3_14)
    (hQL : IsL24Section (kz T V) (pCoreOf 2 (hz T V))
      (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)))
    (hα : (pCoreOf 2 (hz T V)).relIndex (conjSub l₀ (fsuU T V) ⊔ pCoreOf 2 (hz T V)) = 2) :
    (sL T L V ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (sL T L V) = 4 ^ 4 := by
  have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
  have hTH : T ≤ hz T V := C.hF.T_le_H
  have hQHT : pCoreOf 2 (hz T V) ≤ T := pCoreOf_le_of_le C.hyp hTH
  have hSQ : sL T L V ≤ pCoreOf 2 (L ⊔ T) := sL_le_pCoreOf C.setting C.hF C.hMod
  have hSR := hSQ.trans (C.Q_le_R1 h13314)
  obtain ⟨hc, hr4, hr3, hs16, hs3, hs16'⟩ := C.relIndex_cent_B hxL1 hx3 hx1 hu0 h13314 hQL
    hSR (hSQ.trans C.Q_le_centralizer) (le_conjClosure _ _) (le_normalizer_conjClosure _ _ hxL)
    (hQHT.trans C.T_le_normalizer_sL')
  have hr1 : (sL T L V ⊓ pCoreOf 2 (hz T V)).relIndex (sL T L V) ≠ 1 := by
    intro h1
    have hle := Subgroup.relIndex_eq_one.mp h1
    have hαQ : conjSub l₀ (fsuU T V) ≤ pCoreOf 2 (hz T V) := fun t ht =>
      (Subgroup.mem_inf.mp (hle (HypF91.conjSub_le_conjClosure C.mem ht))).2
    rw [sup_eq_right.mpr hαQ, Subgroup.relIndex_self] at hα
    exact absurd hα (by norm_num)
  have hr : (sL T L V ⊓ pCoreOf 2 (hz T V)).relIndex (sL T L V) = 4 :=
    eq_four_of_dvd_sixteen (hr4.trans (by norm_num)) hr3 hr1
      (fun h => by have := Nat.le_of_dvd (by norm_num) hr4; omega)
  have hs1 : (sL T L V ⊓ (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G))).relIndex
      (sL T L V ⊓ pCoreOf 2 (hz T V)) ≠ 1 := by
    intro h1
    have hle := Subgroup.relIndex_eq_one.mp h1
    obtain ⟨w, hw, hwX⟩ := C.exists_mem_sL_inf hQL hα hSR
    exact hwX (Subgroup.mem_inf.mp (hle hw)).2
  have hs := eq_four_of_dvd_sixteen hs16 hs3 hs1 hs16'
  rw [hc, hr, hs]
  norm_num

theorem relIndex_Q_le (hu0 : u0 T V = fsuV1 T V) (h13314 : A6.Stmt13_3_14)
    (hQL : IsL24Section (kz T V) (pCoreOf 2 (hz T V))
      (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G))) :
    (pCoreOf 2 (L ⊔ T) ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (pCoreOf 2 (L ⊔ T)) ≤
      4 ^ 4 := by
  have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
  have hTH : T ≤ hz T V := C.hF.T_le_H
  have hQHT : pCoreOf 2 (hz T V) ≤ T := pCoreOf_le_of_le C.hyp hTH
  have hSQ : sL T L V ≤ pCoreOf 2 (L ⊔ T) := sL_le_pCoreOf C.setting C.hF C.hMod
  obtain ⟨hc, hr4, -, hs16, hs3, hs16'⟩ := C.relIndex_cent_B hxL1 hx3 hx1 hu0 h13314 hQL
    (C.Q_le_R1 h13314) C.Q_le_centralizer ((le_conjClosure _ _).trans hSQ)
    (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hxL))
    ((hQHT.trans le_sup_right).trans (le_normalizer_pCoreOf 2 _))
  rw [hc]
  have h1 := Nat.le_of_dvd (by norm_num) hr4
  have h2 := le_four_of_dvd_sixteen hs16 hs3 hs16'
  calc _ ≤ 4 * (4 * 16) := Nat.mul_le_mul h1 (Nat.mul_le_mul_right _ h2)
    _ = 4 ^ 4 := by norm_num

omit hxL1 hx3 hx1 in
theorem commutator_Q_L_le (hu0 : u0 T V = fsuV1 T V) (h13314 : A6.Stmt13_3_14)
    (hQL : IsL24Section (kz T V) (pCoreOf 2 (hz T V))
      (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)))
    (hα : (pCoreOf 2 (hz T V)).relIndex (conjSub l₀ (fsuU T V) ⊔ pCoreOf 2 (hz T V)) = 2) :
    ⁅pCoreOf 2 (L ⊔ T), L⁆ ≤ sL T L V := by
  obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨y, hyL1, hy3, hy1, hyV⟩ := C.exists_x3
  have hyL : y ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hyL1
  have hSQ : sL T L V ≤ pCoreOf 2 (L ⊔ T) := sL_le_pCoreOf C.setting C.hF C.hMod
  have hQT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_sup_le C.hyp
  have hQS : pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (sL T L V : Set G) :=
    hQT.trans C.T_le_normalizer_sL'
  set D := (pCoreOf 2 (L ⊔ T) ⊓ Subgroup.centralizer ({y} : Set G)) ⊔ sL T L V with hD
  have hDQ : D ≤ pCoreOf 2 (L ⊔ T) := sup_le inf_le_left hSQ
  have hCS : pCoreOf 2 (L ⊔ T) ⊓ Subgroup.centralizer ({y} : Set G) ≤
      Subgroup.normalizer (sL T L V : Set G) := inf_le_left.trans hQS
  have e1 := B6.relIndex_inf_eq_relIndex_sup hCS
  have e2 : pCoreOf 2 (L ⊔ T) ⊓ Subgroup.centralizer ({y} : Set G) ⊓ sL T L V =
      sL T L V ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [inf_comm, ← inf_assoc, inf_eq_left.mpr hSQ]
  rw [e2, C.relIndex_sL hyL1 hy3 hy1 hu0 h13314 hQL hα] at e1
  have hm := Subgroup.relIndex_mul_relIndex _ _ _
    (le_sup_left : pCoreOf 2 (L ⊔ T) ⊓ Subgroup.centralizer ({y} : Set G) ≤ D) hDQ
  rw [← e1] at hm
  have hle := C.relIndex_Q_le hyL1 hy3 hy1 hu0 h13314 hQL
  rw [← hm] at hle
  have hne0 : D.relIndex (pCoreOf 2 (L ⊔ T)) ≠ 0 := by
    show (D.subgroupOf (pCoreOf 2 (L ⊔ T))).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have h1 : D.relIndex (pCoreOf 2 (L ⊔ T)) = 1 := by
    have : 4 ^ 4 * D.relIndex (pCoreOf 2 (L ⊔ T)) ≤ 4 ^ 4 * 1 := by rw [mul_one]; exact hle
    have := Nat.le_of_mul_le_mul_left this (by norm_num)
    omega
  have hQD := Subgroup.relIndex_eq_one.mp h1
  have hyQ : ∀ q ∈ pCoreOf 2 (L ⊔ T), y * q * y⁻¹ * q⁻¹ ∈ sL T L V := by
    intro q hq
    have hq' := hQD hq
    rw [hD, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCS] at hq'
    obtain ⟨c, hc, s, hs, rfl⟩ := hq'
    have hcy := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
    have hys : y * s * y⁻¹ * s⁻¹ ∈ sL T L V :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hyL) s).mp hs)
        (inv_mem hs)
    have h2 := (Subgroup.mem_normalizer_iff.mp (hCS hc) _).mp hys
    convert h2 using 1
    calc y * (c * s) * y⁻¹ * (c * s)⁻¹ = (y * c) * s * y⁻¹ * s⁻¹ * c⁻¹ := by group
      _ = (c * y) * s * y⁻¹ * s⁻¹ * c⁻¹ := by rw [hcy]
      _ = c * (y * s * y⁻¹ * s⁻¹) * c⁻¹ := by group
  have hN : L ⊓ L32NSet14.trivSub (pCoreOf 2 (L ⊔ T)) (sL T L V) = L := by
    refine normal_eq_of_not_mem_centralizer C.hyp C.h13322 C.hMod C.h1222 C.h1332 C.h1334
      inf_le_left (fun l hl n hn => Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      (Subgroup.mem_inf.mpr ⟨hyL, le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hyL),
        le_normalizer_conjClosure _ _ hyL, hyQ⟩) hyV
    · exact mul_mem (mul_mem hl (Subgroup.mem_inf.mp hn).1) (inv_mem hl)
    · exact L32NSet14.conj_mem_trivSub (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hl))
        (le_normalizer_conjClosure _ _ hl) (Subgroup.mem_inf.mp hn).2
  rw [Subgroup.commutator_le]
  intro q hq l hl
  rw [← hN] at hl
  have h3 := ((Subgroup.mem_inf.mp hl).2).2.2 q⁻¹ (inv_mem hq)
  rw [commutatorElement_def]
  have h4 := (Subgroup.mem_normalizer_iff.mp (hQS hq) _).mp h3
  rwa [show q * (l * q⁻¹ * l⁻¹ * q⁻¹⁻¹) * q⁻¹ = q * l * q⁻¹ * l⁻¹ by group] at h4

end Ctx72

theorem lemma14_7_71_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h13314 : A6.Stmt13_3_14) (h63 : Thm14_7_63)
    (h68 : Lemma14_7_68) (h69 : Lemma14_7_69) (h70 : Lemma14_7_70) : Lemma14_7_71 := by
  have h1334 : A6.Stmt13_3_4 := U3.stmt13_3_4_of h1332
  intro G _ _ T L V h
  have hF : HypF98 T V L (fsuV1 T V) V (hz T V) :=
    Setting147.hypF98 ⟨h, h.isHzOne_hz h63⟩ (stmt13_3_2_two_of_stmt13_3_2 h1332)
      (stmtL32NModule_of_inputs h1332 h1334) h1222
  obtain ⟨l₀, C, hα, -⟩ := exists_ctx72_of h h1222 h1332 h1334 h63 hF h69 h70
  have hu0 := C.u0_eq h68
  have hQL := C.isL24Section_QH hu0 h13314
  refine ⟨⟨hQL, C.h71⟩, fun x hxL1 hx3 hx1 => ⟨?_, ?_⟩, C.commutator_Q_L_le hu0 h13314 hQL hα⟩
  · rw [inf_comm]
    exact C.relIndex_pCoreOf_l1 hxL1 hx3 hx1 hu0 hQL
  · rw [inf_comm]
    exact C.relIndex_sL hxL1 hx3 hx1 hu0 h13314 hQL hα

end CFSG.Quasithin.H13.L32A
