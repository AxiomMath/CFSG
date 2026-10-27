module

public import CFSG.Quasithin.H13.L32A771f

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_kz_le_QH {T V : Subgroup G} :
    pCoreOf 2 (kz T V) ≤ pCoreOf 2 (hz T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (oTwoUpper_le _))
    ((le_normalizer_oTwoUpper (hz T V)).trans (normalizer_le_normalizer_pCoreOf 2 _))
    (pCoreOf_isPGroup 2 _)

namespace Ctx72

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx72 G T L V l₀)
include C

theorem not_QH_le_centralizer (h13314 : A6.Stmt13_3_14) :
    ¬ pCoreOf 2 (hz T V) ≤ Subgroup.centralizer (V : Set G) := by
  intro hle
  obtain ⟨-, -, -, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨V₂, hV2⟩ := C.hyp.exists_V2 C.h13322 C.hMod C.h1222
  have h4 := lemma14_7_4_one C.hyp C.h13322 C.hMod h13314 hV2
  have hg1 : A6.g1 T V = hz T V := normalizer_eq_centralizer_of_card_two hV1
  rw [hg1] at h4
  have hbot : ⁅V₂, pCoreOf 2 (hz T V)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (hle hq) v (hV2.2.1 hv)).symm
  rw [hbot] at h4
  have h0 : Nat.card ↥(⊥ : Subgroup G) = 2 := by rw [h4]; exact hV1
  rw [Subgroup.card_bot] at h0
  exact absurd h0 (by norm_num)

theorem exists_mem_sL_inf
    (hQL : IsL24Section (kz T V) (pCoreOf 2 (hz T V))
      (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)))
    (hα : (pCoreOf 2 (hz T V)).relIndex (conjSub l₀ (fsuU T V) ⊔ pCoreOf 2 (hz T V)) = 2)
    (hSR : sL T L V ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) :
    ∃ w ∈ sL T L V ⊓ pCoreOf 2 (hz T V),
      w ∉ pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) := by
  have hTH : T ≤ hz T V := C.hF.T_le_H
  have hQHT : pCoreOf 2 (hz T V) ≤ T := pCoreOf_le_of_le C.hyp hTH
  have hQHn : hz T V ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hR1H : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ hz T V :=
    (pCoreOf_le_of_le C.hyp le_sup_right).trans hTH
  have hTS : T ≤ Subgroup.normalizer (sL T L V : Set G) := fun _ ht =>
    mem_normalizer_conjClosure_of
      (le_normalizer_conjClosure V _ (C.hF.T_normalizes_V₁ ht)) (C.hyp.normalizes C.h13322 ht)
  obtain ⟨t, htα, htQ⟩ : ∃ t ∈ conjSub l₀ (fsuU T V), t ∉ pCoreOf 2 (hz T V) := by
    by_contra hne
    push Not at hne
    rw [sup_eq_right.mpr hne, Subgroup.relIndex_self] at hα
    exact absurd hα (by norm_num)
  have htS : t ∈ sL T L V := HypF91.conjSub_le_conjClosure C.mem htα
  have htH : t ∈ hz T V := hR1H (hSR htS)
  have htK := (R1_le_kz_sup C.setting C.hF C.h63 C.h1222 C.h1332 C.h1334).1 (hSR htS)
  have hKN : kz T V ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
    (oTwoUpper_le _).trans hQHn
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKN] at htK
  obtain ⟨k, hk, q₀, hq₀, rfl⟩ := htK
  have hkO : k ∉ pCoreOf 2 (kz T V) := fun h' => htQ (mul_mem (pCoreOf_kz_le_QH h') hq₀)
  obtain ⟨hKQ, π, β, hπs, hπk, hβs, hβk, hβe⟩ := hQL
  have hπ1 : π ⟨k, hk⟩ ≠ 1 := fun h1 => by
    have h2 : (⟨k, hk⟩ : ↥(kz T V)) ∈ π.ker := h1
    rw [hπk, Subgroup.mem_subgroupOf] at h2
    exact hkO h2
  obtain ⟨v, hv⟩ : ∃ v : Fin 2 → F4,
      ((π ⟨k, hk⟩ : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec v ≠ v := by
    by_contra hne
    push Not at hne
    exact hπ1 (sl24_eq_one_of_fix _ hne)
  obtain ⟨q, hq⟩ := hβs (Multiplicative.ofAdd v)
  have hqT : (q : G) ∈ T := hQHT q.2
  have hkH : k ∈ hz T V := oTwoUpper_le _ hk
  have hq₀H : q₀ ∈ hz T V := pCoreOf_le 2 _ hq₀
  refine ⟨(k * q₀) * q * (k * q₀)⁻¹ * (q : G)⁻¹, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, fun hw => ?_⟩
  · rw [show (k * q₀) * q * (k * q₀)⁻¹ * (q : G)⁻¹ = (k * q₀) * (q * (k * q₀)⁻¹ * (q : G)⁻¹) by
      group]
    exact mul_mem htS ((Subgroup.mem_normalizer_iff.mp (hTS hqT) _).mp (inv_mem htS))
  · exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hQHn htH) q).mp q.2) (inv_mem q.2)
  have hy : q₀ * q * q₀⁻¹ ∈ pCoreOf 2 (hz T V) :=
    (Subgroup.mem_normalizer_iff.mp (hQHn hq₀H) q).mp q.2
  have hky : k * (q₀ * q * q₀⁻¹) * k⁻¹ ∈ pCoreOf 2 (hz T V) :=
    (Subgroup.mem_normalizer_iff.mp (hQHn hkH) _).mp hy
  have h1 := hβe ⟨k, hk⟩ ⟨_, hy⟩ ⟨_, hky⟩ rfl
  have hβy : β ⟨_, hy⟩ = β q := by
    have e : (⟨_, hy⟩ : ↥(pCoreOf 2 (hz T V))) = ⟨q₀, hq₀⟩ * q * ⟨q₀, hq₀⟩⁻¹ :=
      Subtype.ext (by simp)
    rw [e, map_mul, map_mul, map_inv, mul_comm (β ⟨q₀, hq₀⟩), mul_assoc, mul_inv_cancel,
      mul_one]
  rw [hβy, hq, toAdd_ofAdd] at h1
  have hw' : β (⟨_, hky⟩ * q⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
    convert hw using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [map_mul, map_inv, h1, hq, mul_inv_eq_one] at hw'
  exact hv (by simpa using congrArg Multiplicative.toAdd hw')

variable {x : G} (hxL1 : x ∈ L₁Of L (fsuV1 T V)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
include hxL1 hx3 hx1

theorem relIndex_cent_B (hu0 : u0 T V = fsuV1 T V) (h13314 : A6.Stmt13_3_14)
    (hQL : IsL24Section (kz T V) (pCoreOf 2 (hz T V))
      (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)))
    {B : Subgroup G} (hBR : B ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hBV : B ≤ Subgroup.centralizer (V : Set G)) (hUB : fsuU T V ≤ B)
    (hxB : x ∈ Subgroup.normalizer (B : Set G))
    (hQHB : pCoreOf 2 (hz T V) ≤ Subgroup.normalizer (B : Set G)) :
    (B ⊓ Subgroup.centralizer ({x} : Set G)).relIndex B =
        (B ⊓ pCoreOf 2 (hz T V)).relIndex B *
          ((B ⊓ (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G))).relIndex
            (B ⊓ pCoreOf 2 (hz T V)) * 16) ∧
      (B ⊓ pCoreOf 2 (hz T V)).relIndex B ∣ 4 ∧
      (B ⊓ pCoreOf 2 (hz T V)).relIndex B ≡ 1 [MOD 3] ∧
      (B ⊓ (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G))).relIndex
        (B ⊓ pCoreOf 2 (hz T V)) ∣ 16 ∧
      (B ⊓ (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G))).relIndex
        (B ⊓ pCoreOf 2 (hz T V)) ≡ 1 [MOD 3] ∧
      (B ⊓ (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G))).relIndex
        (B ⊓ pCoreOf 2 (hz T V)) ≠ 16 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxK : x ∈ kz T V := l1_le_kz C.hyp C.hMod hxL1
  have hxH : x ∈ hz T V := oTwoUpper_le _ hxK
  have hxO : x ∉ pCoreOf 2 (kz T V) := not_mem_pCoreOf_of_pow_three hx3 hx1
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hTH : T ≤ hz T V := C.hF.T_le_H
  have hL1H : L₁Of L (fsuV1 T V) ≤ hz T V := le_sup_left.trans C.hF.L₁T_le_H
  have hQHn : hz T V ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hQHR1 : pCoreOf 2 (hz T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le_of_le C.hyp hTH).trans le_sup_right)
      ((sup_le hL1H hTH).trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hR14 : (pCoreOf 2 (hz T V)).relIndex (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) = 4 :=
    (R1_le_kz_sup C.setting C.hF C.h63 C.h1222 C.h1332 C.h1334).2
  set X := pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) with hX
  have hXQ : X ≤ pCoreOf 2 (hz T V) := inf_le_left
  have hHX : hz T V ≤ Subgroup.normalizer (X : Set G) := C.hz_le_normalizer_X
  obtain ⟨hcU, -, -⟩ := C.relIndex_centralizer_QH hxL1 hx3 hx1 hu0 hQL
  have hxQH : x ∈ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) := hQHn hxH
  have hxBQ := mem_normalizer_inf_of hxB hxQH
  have hxBX := mem_normalizer_inf_of hxB (hHX hxH)
  have hBQ_le : B ⊓ X ≤ B ⊓ pCoreOf 2 (hz T V) := inf_le_inf_left _ hXQ
  have hC1 : B ⊓ Subgroup.centralizer ({x} : Set G) ≤ B ⊓ pCoreOf 2 (hz T V) :=
    fun b hb => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hb).1,
      C.inf_centralizer_R1_le hxL1 hx3 hx1 (Subgroup.mem_inf.mpr
        ⟨hBR (Subgroup.mem_inf.mp hb).1, (Subgroup.mem_inf.mp hb).2⟩)⟩
  have hl1 := relIndex_inf_centralizer_mul inf_le_left hC1
  have hC2 : (B ⊓ pCoreOf 2 (hz T V)) ⊓ Subgroup.centralizer ({x} : Set G) ≤ B ⊓ X := by
    intro b hb
    obtain ⟨⟨hbB, hbQ⟩, hbC⟩ := Subgroup.mem_inf.mp hb |>.imp_left Subgroup.mem_inf.mp
    refine Subgroup.mem_inf.mpr ⟨hbB, fixed_mem_of_isL24Section hQL hxK hx3 hxO hbQ ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hbC
    rw [show x * b * x⁻¹ * b⁻¹ = (x * b) * (b * x)⁻¹ by group, ← hbC, mul_inv_cancel]
    exact one_mem _
  have hl2 := relIndex_inf_centralizer_mul hBQ_le hC2
  have hUBX : fsuU T V ≤ B ⊓ X := le_inf hUB (le_inf C.fsuU_le_QH fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => F7.isElemAbelian_comm hUe hw hu)
  have hBXU : B ⊓ X ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    ((inf_le_right.trans hXQ).trans (pCoreOf_le 2 _)).trans C.hz_le_normalizer_fsuU'
  have hp3U : ¬ 3 ∣ Nat.card ↥(fsuU T V) :=
    not_dvd_card_of_isPGroup_two ((pCoreOf_isPGroup 2 _).to_le C.fsuU_le_QH) Nat.prime_three
      (by norm_num)
  have hl3 := relIndex_inf_centralizer_eq hx3 hUBX hBXU (C.hz_le_normalizer_fsuU' hxH) hp3U
    (fun g hg => by
      have h1 := C.h71 (Subgroup.commutator_mem_commutator (inv_mem (Subgroup.mem_inf.mp hg).2)
        hxK)
      rwa [commutatorElement_def, inv_inv] at h1)
  rw [hcU] at hl3
  refine ⟨by rw [hl1, hl2, hl3], ?_, ?_, ?_, ?_, ?_⟩
  ·
    have e := B6.relIndex_inf_eq_relIndex_sup hQHB
    rw [inf_comm] at e
    rw [e, ← hR14, ← Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_left :
      pCoreOf 2 (hz T V) ≤ pCoreOf 2 (hz T V) ⊔ B) (sup_le hQHR1 hBR)]
    exact Dvd.intro _ rfl
  · exact relIndex_modEq_one_of_card Nat.prime_three inf_le_left
      (card_modEq_card_of_fix hx3 inf_le_left hxBQ hxB hC1)
      (not_dvd_card_of_isPGroup_two ((pCoreOf_isPGroup 2 _).to_le inf_le_right) Nat.prime_three
        (by norm_num))
  ·
    have hXN : X ≤ Subgroup.normalizer ((B ⊓ pCoreOf 2 (hz T V) : Subgroup G) : Set G) :=
      fun y hy => mem_normalizer_inf_of (hQHB (hXQ hy)) (hQHn (pCoreOf_le 2 _ (hXQ hy)))
    have e := B6.relIndex_inf_eq_relIndex_sup hXN
    have e2 : X ⊓ (B ⊓ pCoreOf 2 (hz T V)) = B ⊓ X := by
      rw [inf_comm, inf_assoc, inf_eq_right.mpr hXQ]
    rw [e2] at e
    rw [e, ← hQL.relIndex_eq, ← Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_left :
      X ≤ X ⊔ (B ⊓ pCoreOf 2 (hz T V))) (sup_le hXQ inf_le_right)]
    exact Dvd.intro _ rfl
  · exact relIndex_modEq_one_of_card Nat.prime_three hBQ_le
      (card_modEq_card_of_fix hx3 hBQ_le hxBX hxBQ hC2)
      (not_dvd_card_of_isPGroup_two ((pCoreOf_isPGroup 2 _).to_le
        ((inf_le_right.trans hXQ))) Nat.prime_three (by norm_num))
  ·
    intro h16
    have hXN : X ≤ Subgroup.normalizer ((B ⊓ pCoreOf 2 (hz T V) : Subgroup G) : Set G) :=
      fun y hy => mem_normalizer_inf_of (hQHB (hXQ hy)) (hQHn (pCoreOf_le 2 _ (hXQ hy)))
    have e := B6.relIndex_inf_eq_relIndex_sup hXN
    have e2 : X ⊓ (B ⊓ pCoreOf 2 (hz T V)) = B ⊓ X := by
      rw [inf_comm, inf_assoc, inf_eq_right.mpr hXQ]
    rw [e2, h16] at e
    have hm := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_left :
      X ≤ X ⊔ (B ⊓ pCoreOf 2 (hz T V))) (sup_le hXQ inf_le_right)
    rw [← e, hQL.relIndex_eq] at hm
    have h1 : (X ⊔ (B ⊓ pCoreOf 2 (hz T V))).relIndex (pCoreOf 2 (hz T V)) = 1 := by omega
    have hle := Subgroup.relIndex_eq_one.mp h1
    apply C.not_QH_le_centralizer h13314
    refine hle.trans (sup_le ?_ (inf_le_left.trans hBV))
    exact inf_le_right.trans (Subgroup.centralizer_le fun v hv => v_le_fsuU hv)

end Ctx72

end CFSG.Quasithin.H13.L32A
