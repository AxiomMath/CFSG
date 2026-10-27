module

public import CFSG.Quasithin.H13.L32A773h

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem IsL24Section.relIndex_eq {K X Y : Subgroup G} (h : IsL24Section K X Y) :
    Y.relIndex X = 16 := by
  obtain ⟨-, π, β, -, -, hβs, hβk, -⟩ := h
  rw [Subgroup.relIndex, ← hβk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hβs,
    Subgroup.card_top, Nat.card_eq_fintype_card]
  decide

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem card_v : Nat.card ↥V = 8 := (C.hMod G T L V C.hyp.hyp C.hyp.fsu).2.1

theorem card_sL : Nat.card ↥(sL T L V) = 2 ^ 11 := by
  obtain ⟨θ, hθs, hθk, -⟩ := C.exists_theta1
  obtain ⟨χ, hχk, hχtr, hχs, -⟩ :=
    C.isSteinbergSection C.u0_eq C.vh63 C.vh65 C.l71 θ hθs hθk
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup χ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv, hχk,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe v_le_sL).toEquiv, C.card_v] at h1
  have hr : Nat.card ↥χ.range = 256 := by
    rw [← H6.card_st]
    refine Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.toAdd x.1, by
          obtain ⟨s, hs⟩ := x.2
          rw [← hs]
          exact hχtr s⟩
        invFun := fun A => ⟨Multiplicative.ofAdd A.1, hχs A.1 A.2⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun A => Subtype.ext (by simp) }
  rw [h1, hr]
  norm_num

theorem card_L : Nat.card ↥L = 2 ^ 14 * 21 := by
  have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 L) L
  rw [C.relIndex_pCoreOf, inf_eq_left.mpr (pCoreOf_le 2 L), C.pCoreOf_eq_sL, C.card_sL] at h1
  rw [← h1]
  norm_num

theorem card_T : Nat.card ↥T = 2 ^ 14 := by
  have hT := C.hyp.fsu.sylow
  have hTL := C.T_le_L
  have hL := C.card_L
  have hodd : ¬ 2 ∣ T.relIndex L := by
    intro hd
    apply hT.2
    rw [← Subgroup.relIndex_mul_index hTL]
    exact Dvd.dvd.mul_right hd _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hT.1)
  have h2 := Subgroup.relIndex_mul_card T L
  rw [inf_eq_left.mpr hTL, hn, hL] at h2
  have hcop : Nat.Coprime 2 (T.relIndex L) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
  have h3 : 2 ^ 14 ∣ 2 ^ n := by
    have : 2 ^ 14 ∣ T.relIndex L * 2 ^ n := ⟨21, by rw [h2]⟩
    exact (Nat.Coprime.pow_left 14 hcop).dvd_of_dvd_mul_left this
  have h4 : 2 ^ n ∣ 2 ^ 14 := by
    have : 2 ^ n ∣ 2 ^ 14 * 21 := ⟨T.relIndex L, by rw [← h2]; ring⟩
    exact (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 21)).dvd_of_dvd_mul_right this
  rw [hn, Nat.dvd_antisymm h4 h3]

theorem relIndex_QH_T : (pCoreOf 2 (hz T V)).relIndex T = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hs, hk⟩ := exists_phi C.hyp C.h63
  have hT := C.hyp.fsu.sylow
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hTi : ¬ 2 ∣ (T.subgroupOf (hz T V)).index := by
    intro hd
    apply hT.2
    rw [← Subgroup.relIndex_mul_index hTH]
    exact Dvd.dvd.mul_right hd _
  exact relIndex_phi_sylow hs hk hTH hT.1 hTi

theorem card_QH : Nat.card ↥(pCoreOf 2 (hz T V)) = 2 ^ 11 := by
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 (hz T V)) T
  rw [C.relIndex_QH_T, inf_eq_left.mpr (pCoreOf_le_of_le C.hyp hTH), C.card_T] at h1
  omega

theorem R1_eq_inf : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) = T ⊓ kz T V := by
  refine le_antisymm (le_inf (pCoreOf_le_of_le C.hyp le_sup_right) ?_) C.T_inf_kz_le_R1
  rw [← C.sup_eq_R1, C.pCoreOf_hz_eq]
  exact sup_le C.sL_le_kz (pCoreOf_le 2 _)

theorem relIndex_T_inf_kz : (T ⊓ kz T V).relIndex T = 2 := by
  obtain ⟨-, h4⟩ := R1_le_kz_sup C.setting C.hF C.h63 C.h1222 C.h1332 C.h1334
  have hQR : pCoreOf 2 (hz T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := C.QH_le_R1
  have hRT : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T := pCoreOf_le_of_le C.hyp le_sup_right
  have h1 := Subgroup.relIndex_mul_relIndex _ _ T hQR hRT
  rw [h4, C.relIndex_QH_T] at h1
  rw [← C.R1_eq_inf]
  omega

theorem R1_eq_pCoreOf_l1 :
    pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) = pCoreOf 2 (L₁Of L (fsuV1 T V)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR1L1 : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ L₁Of L (fsuV1 T V) := by
    rw [← C.sup_eq_R1]
    exact sup_le C.sL_le_l1 C.QH_le_l1
  have hTN : T ≤ Subgroup.normalizer (L₁Of L (fsuV1 T V) : Set G) := by
    intro t ht
    have htL : t ∈ Subgroup.normalizer (L : Set G) := C.hyp.normalizes C.h13322 ht
    have htV1 : t ∈ Subgroup.normalizer (fsuV1 T V : Set G) :=
      C.hF.H_normalizes_V₁ (le_sup_right.trans C.hF.L₁T_le_H ht)
    have htX : t ∈ Subgroup.normalizer ((L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) :
        Subgroup G) : Set G) :=
      le_normalizer_of_conj_mem' (H := Subgroup.normalizer (L : Set G) ⊓
        Subgroup.normalizer (fsuV1 T V : Set G)) (fun g hg x hx => Subgroup.mem_inf.mpr
          ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hg).1 x).mp
            (Subgroup.mem_inf.mp hx).1, mul_mem (mul_mem (Subgroup.mem_inf.mp hg).2
              (Subgroup.mem_inf.mp hx).2) (inv_mem (Subgroup.mem_inf.mp hg).2)⟩)
        (Subgroup.mem_inf.mpr ⟨htL, htV1⟩)
    rw [L₁Of, oTwoRes_eq_oTwoUpper]
    exact normalizer_le_normalizer_oTwoUpper _ htX
  refine le_antisymm (le_pCoreOf_of_le_normalizer 2 hR1L1
    (le_sup_left.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)) ?_
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
    (sup_le (le_normalizer_pCoreOf 2 _) (hTN.trans (normalizer_le_normalizer_pCoreOf 2 _)))
    (pCoreOf_isPGroup 2 _)

theorem card_sL_inf_QH : Nat.card ↥(sL T L V ⊓ pCoreOf 2 (hz T V)) = 2 ^ 9 := by
  obtain ⟨-, h4⟩ := R1_le_kz_sup C.setting C.hF C.h63 C.h1222 C.h1332 C.h1334
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hQN : pCoreOf 2 (hz T V) ≤ Subgroup.normalizer (sL T L V : Set G) :=
    (pCoreOf_le_of_le C.hyp hTH).trans C.T_le_normalizer_sL
  have h1 := B6.relIndex_inf_eq_relIndex_sup hQN
  rw [sup_comm, C.sup_eq_R1, h4] at h1
  have h2 := Subgroup.relIndex_mul_card (pCoreOf 2 (hz T V) ⊓ sL T L V) (sL T L V)
  rw [h1, inf_eq_left.mpr inf_le_right, C.card_sL, inf_comm] at h2
  omega

theorem card_fsuU : Nat.card ↥(fsuU T V) = 2 ^ 5 := by
  obtain ⟨-, -, -, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨-, -, -, -, -, -, U₀, hU₀, hL24⟩ := C.h63 G T L V C.hyp
  have hU0 : U₀ = fsuV1 T V := by
    ext u
    rw [hU₀]
    constructor
    · rintro ⟨huU, hk⟩
      exact (C.lemma14_7_72).2.2.2.1 u huU hk
    · intro hu
      refine ⟨v_le_fsuU (Subgroup.mem_inf.mp hu).1, fun k hk => ?_⟩
      have hkH : k ∈ hz T V := oTwoUpper_le _ hk
      rw [← Subgroup.mem_centralizer_iff.mp hkH u hu, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  have h1 := hL24.relIndex_eq
  rw [hU0] at h1
  have h2 := Subgroup.relIndex_mul_card (fsuV1 T V) (fsuU T V)
  rw [h1, inf_eq_left.mpr (fun x hx => v_le_fsuU (Subgroup.mem_inf.mp hx).1), hV1] at h2
  omega

theorem card_CU :
    Nat.card ↥(pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)) = 2 ^ 7 := by
  have h1 := ((C.l71 G T L V C.hyp).1.1).relIndex_eq
  have h2 := Subgroup.relIndex_mul_card
    (pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)) (pCoreOf 2 (hz T V))
  rw [h1, inf_eq_left.mpr inf_le_left, C.card_QH] at h2
  omega

end Ctx73

end CFSG.Quasithin.H13.L32A
