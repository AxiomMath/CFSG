module

public import CFSG.Quasithin.H13.L32A771e
public import CFSG.Quasithin.H13.L32A771a
public import CFSG.Quasithin.H13.L32A773o

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_inf_centralizer_mul {x : G} {N P : Subgroup G} (hNP : N ≤ P)
    (hC : P ⊓ Subgroup.centralizer ({x} : Set G) ≤ N) :
    (P ⊓ Subgroup.centralizer ({x} : Set G)).relIndex P =
      N.relIndex P * (N ⊓ Subgroup.centralizer ({x} : Set G)).relIndex N := by
  have e : P ⊓ Subgroup.centralizer ({x} : Set G) = N ⊓ Subgroup.centralizer ({x} : Set G) :=
    le_antisymm (le_inf hC inf_le_right) (inf_le_inf_right _ hNP)
  rw [e, ← Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left hNP, mul_comm]

omit [Finite G] in
theorem mem_normalizer_inf_of {g : G} {A B : Subgroup G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [← conjSub_eq_self_iff, conjSub_inf, conjSub_eq_self_iff.mpr hA, conjSub_eq_self_iff.mpr hB]

namespace Ctx72

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx72 G T L V l₀)
include C

theorem hz_le_normalizer_fsuU' : hz T V ≤ Subgroup.normalizer (fsuU T V : Set G) := by
  rw [fsuU_eq_conjClosure_hz C.hMod C.hyp]
  exact le_normalizer_conjClosure V _

theorem fsuU_le_QH : fsuU T V ≤ pCoreOf 2 (hz T V) := by
  rw [fsuU_eq_conjClosure_hz C.hMod C.hyp]
  exact C.hF.conjClosure_Vp_le_pCoreOf

theorem hz_le_normalizer_X : hz T V ≤ Subgroup.normalizer
    ((pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) : Subgroup G) : Set G) := by
  intro k hk
  rw [← conjSub_eq_self_iff, conjSub_inf, conjSub_eq_self_iff.mpr (le_normalizer_pCoreOf 2 _ hk),
    ← conjSub_centralizer, conjSub_eq_self_iff.mpr (C.hz_le_normalizer_fsuU' hk)]

variable {x : G} (hxL1 : x ∈ L₁Of L (fsuV1 T V)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
include hxL1 hx3 hx1

theorem inf_centralizer_R1_le :
    pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ Subgroup.centralizer ({x} : Set G) ≤
      pCoreOf 2 (hz T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hs, hk⟩ := exists_phi C.hyp C.h63
  have hφ1 : ∀ y : ↥(hz T V), φ y = 1 ↔ (y : G) ∈ pCoreOf 2 (hz T V) := fun y => by
    rw [← MonoidHom.mem_ker, hk, ← mem_pCoreOf_iff']
  have hTH : T ≤ hz T V := C.hF.T_le_H
  have hL1H : L₁Of L (fsuV1 T V) ≤ hz T V := le_sup_left.trans C.hF.L₁T_le_H
  have hxH : x ∈ hz T V := hL1H hxL1
  have hR1T : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T := pCoreOf_le_of_le C.hyp le_sup_right
  have hR1H := hR1T.trans hTH
  have hQHR1 : pCoreOf 2 (hz T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le_of_le C.hyp hTH).trans le_sup_right)
      ((sup_le hL1H hTH).trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hR14 : (pCoreOf 2 (hz T V)).relIndex (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) = 4 :=
    (R1_le_kz_sup C.setting C.hF C.h63 C.h1222 C.h1332 C.h1334).2
  have hQHn : hz T V ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
    le_normalizer_pCoreOf 2 _
  set D := (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ Subgroup.centralizer ({x} : Set G)) ⊔
    pCoreOf 2 (hz T V) with hD
  have hDR : D ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := sup_le inf_le_left hQHR1
  have hDH : D ≤ hz T V := hDR.trans hR1H
  have hxR1 : x ∈ Subgroup.normalizer (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hxL1)
  have hxC : x ∈ Subgroup.normalizer
      ((pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ Subgroup.centralizer ({x} : Set G) :
        Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj_mem (fun w hw => ?_) (fun w hw => ?_)
    · have hc := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hw).2
      rwa [show x * w * x⁻¹ = w by rw [← hc]; group]
    · have hc := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hw).2
      rwa [show x⁻¹ * w * x = w by rw [show x⁻¹ * w * x = x⁻¹ * (w * x) by group, hc]; group]
  have hxD : x ∈ Subgroup.normalizer (D : Set G) :=
    le_normalizer_sup_of (K := Subgroup.zpowers x) (Subgroup.zpowers_le.mpr hxC)
      (Subgroup.zpowers_le.mpr (hQHn hxH)) (Subgroup.mem_zpowers x)
  have hφx3 : φ ⟨x, hxH⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have e : (⟨x, hxH⟩ : ↥(hz T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [e, map_one]
  have hφx1 : φ ⟨x, hxH⟩ ≠ 1 := fun h' =>
    not_mem_pCoreOf_of_pow_three hx3 hx1 ((hφ1 _).mp h')
  have hsub : (D.subgroupOf (hz T V)).map φ ≤
      Subgroup.centralizer ({φ ⟨x, hxH⟩} : Set (Equiv.Perm (Fin 5))) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hd
    have hd' : (d : G) ∈ ((pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓
        Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) *
          (pCoreOf 2 (hz T V) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
        ((inf_le_left.trans hR1H).trans hQHn)]
      exact hd
    obtain ⟨r, hr, q, hq, hrq⟩ := hd'
    have hrH : r ∈ hz T V := hR1H (Subgroup.mem_inf.mp hr).1
    have hqH : q ∈ hz T V := pCoreOf_le 2 _ hq
    have e : d = ⟨r, hrH⟩ * ⟨q, hqH⟩ := Subtype.ext hrq.symm
    rw [Subgroup.mem_centralizer_singleton_iff, e, map_mul, (hφ1 ⟨q, hqH⟩).mpr hq, mul_one,
      ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hr).2)
  have h6 : (pCoreOf 2 (hz T V)).relIndex D ∣ 6 := by
    rw [← card_map_phi hk hDH, ← perm5_card_centralizer hφx3 hφx1]
    exact Subgroup.card_dvd_of_le hsub
  have h4 : (pCoreOf 2 (hz T V)).relIndex D ∣ 4 := by
    rw [← hR14, ← Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right :
      pCoreOf 2 (hz T V) ≤ D) hDR]
    exact Dvd.intro _ rfl
  have h2 : (pCoreOf 2 (hz T V)).relIndex D ∣ 2 := by
    have := Nat.dvd_gcd h6 h4
    rwa [show Nat.gcd 6 4 = 2 by norm_num] at this
  have hmod := card_modEq_card_of_fix hx3 hDR hxD hxR1 (le_sup_left :
    pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ Subgroup.centralizer ({x} : Set G) ≤ D)
  have hc1 := Subgroup.relIndex_mul_card (pCoreOf 2 (hz T V)) (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
  rw [inf_eq_left.mpr hQHR1, hR14] at hc1
  have hc2 := Subgroup.relIndex_mul_card (pCoreOf 2 (hz T V)) D
  rw [inf_eq_left.mpr (le_sup_right : pCoreOf 2 (hz T V) ≤ D)] at hc2
  rw [← hc1, ← hc2] at hmod
  have h3 : ¬ 3 ∣ Nat.card ↥(pCoreOf 2 (hz T V)) :=
    not_dvd_card_of_isPGroup_two (pCoreOf_isPGroup 2 _) Nat.prime_three (by norm_num)
  have hcop : Nat.Coprime 3 (Nat.card ↥(pCoreOf 2 (hz T V))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hm := Nat.ModEq.cancel_right_of_coprime hcop hmod
  unfold Nat.ModEq at hm
  have hr1 : (pCoreOf 2 (hz T V)).relIndex D = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) h2
    have hne0 : (pCoreOf 2 (hz T V)).relIndex D ≠ 0 := by
      show ((pCoreOf 2 (hz T V)).subgroupOf D).index ≠ 0
      exact Subgroup.index_ne_zero_of_finite
    interval_cases hr : (pCoreOf 2 (hz T V)).relIndex D <;> omega
  exact (le_sup_left :
    pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ Subgroup.centralizer ({x} : Set G) ≤ D).trans
      (Subgroup.relIndex_eq_one.mp hr1)

theorem relIndex_centralizer_QH (hu0 : u0 T V = fsuV1 T V)
    (hQL : IsL24Section (kz T V) (pCoreOf 2 (hz T V))
      (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G))) :
    (fsuU T V ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (fsuU T V) = 16 ∧
    ((pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)) ⊓
      Subgroup.centralizer ({x} : Set G)).relIndex
        (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)) = 16 ∧
    (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (pCoreOf 2 (hz T V)) =
      4 ^ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxK : x ∈ kz T V := l1_le_kz C.hyp C.hMod hxL1
  have hxH : x ∈ hz T V := oTwoUpper_le _ hxK
  have hxO : x ∉ pCoreOf 2 (kz T V) := not_mem_pCoreOf_of_pow_three hx3 hx1
  have hL24 : IsL24Section (kz T V) (fsuU T V) (fsuV1 T V) := by
    rw [← hu0]
    exact isL24Section_u0 C.hyp C.hMod C.h63
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hV1U : fsuV1 T V ≤ fsuU T V := inf_le_left.trans (le_conjClosure V _)
  have hfixU : fsuU T V ⊓ Subgroup.centralizer ({x} : Set G) ≤ fsuV1 T V := by
    intro u hu
    obtain ⟨huU, huC⟩ := Subgroup.mem_inf.mp hu
    refine fixed_mem_of_isL24Section hL24 hxK hx3 hxO huU ?_
    rw [Subgroup.mem_centralizer_singleton_iff] at huC
    rw [show x * u * x⁻¹ * u⁻¹ = (x * u) * (u * x)⁻¹ by group, ← huC, mul_inv_cancel]
    exact one_mem _
  have hV1C : fsuV1 T V ≤ Subgroup.centralizer ({x} : Set G) := fun z hz => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hxH z hz
  have hcV1 : (fsuV1 T V ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (fsuV1 T V) = 1 := by
    rw [inf_eq_left.mpr hV1C, Subgroup.relIndex_self]
  have hcU : (fsuU T V ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (fsuU T V) = 16 := by
    rw [relIndex_inf_centralizer_mul hV1U hfixU, hcV1, mul_one]
    have := relIndex_u0 C.hyp C.hMod C.h63
    rwa [hu0] at this
  have hUX : fsuU T V ≤ pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) :=
    le_inf C.fsuU_le_QH fun u hu => Subgroup.mem_centralizer_iff.mpr fun w hw =>
      F7.isElemAbelian_comm hUe hw hu
  have hXU : pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) ≤
      Subgroup.normalizer (fsuU T V : Set G) :=
    (inf_le_left.trans (pCoreOf_le 2 _)).trans C.hz_le_normalizer_fsuU'
  have hp3U : ¬ 3 ∣ Nat.card ↥(fsuU T V) :=
    not_dvd_card_of_isPGroup_two ((pCoreOf_isPGroup 2 _).to_le C.fsuU_le_QH) Nat.prime_three
      (by norm_num)
  have hcX := relIndex_inf_centralizer_eq hx3 hUX hXU (C.hz_le_normalizer_fsuU' hxH) hp3U
    (fun g hg => by
      have h1 := C.h71 (Subgroup.commutator_mem_commutator (inv_mem hg) hxK)
      rwa [commutatorElement_def, inv_inv] at h1)
  rw [hcU] at hcX
  have hfixQ : pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer ({x} : Set G) ≤
      pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) := by
    intro q hq
    obtain ⟨hqQ, hqC⟩ := Subgroup.mem_inf.mp hq
    refine fixed_mem_of_isL24Section hQL hxK hx3 hxO hqQ ?_
    rw [Subgroup.mem_centralizer_singleton_iff] at hqC
    rw [show x * q * x⁻¹ * q⁻¹ = (x * q) * (q * x)⁻¹ by group, ← hqC, mul_inv_cancel]
    exact one_mem _
  have hcQ := relIndex_inf_centralizer_mul inf_le_left hfixQ
  rw [hQL.relIndex_eq, hcX] at hcQ
  exact ⟨hcU, hcX, hcQ⟩

end Ctx72

end CFSG.Quasithin.H13.L32A
