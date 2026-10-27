module

public import CFSG.Quasithin.H13.L32A773o

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

omit [Finite G] C in
theorem l1_eq : l1 T L V = L₁Of L (fsuV1 T V) := by
  rw [L₁Of, oTwoRes_eq_oTwoUpper]

theorem lemma14_7_73 :
    (sL T L V ⊔ pCoreOf 2 (kz T V) = pCoreOf 2 (l1 T L V) ∧
      pCoreOf 2 (l1 T L V) ≤ kz T V ∧
      ¬ 2 ∣ (pCoreOf 2 (l1 T L V)).relIndex (kz T V)) ∧
    (T ⊓ kz T V).relIndex (T ⊓ L) = 2 ∧
    ∀ k ∈ kz T V, k ∉ m1 T L V →
      kz T V = sL T L V ⊔ (sL T L V).map (MulAut.conj k).toMonoidHom ∧
      pCoreOf 2 (kz T V) = (sL T L V ⊓ pCoreOf 2 (kz T V)) ⊔
        ((sL T L V).map (MulAut.conj k).toMonoidHom ⊓ pCoreOf 2 (kz T V)) ∧
      Nat.card ↥(pCoreOf 2 (kz T V)) = 2 ^ 11 ∧
      sL T L V ⊓ (sL T L V).map (MulAut.conj k).toMonoidHom =
        pCoreOf 2 (kz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) ∧
      IsElemSection (pCoreOf 2 (kz T V)) (fsuU T V) ∧
      (fsuU T V).relIndex (pCoreOf 2 (kz T V)) = 2 ^ 6 ∧
      IsIndecOnSection (kz T V) (pCoreOf 2 (kz T V)) (fsuU T V) ∧
      (∀ q ∈ pCoreOf 2 (kz T V), (∀ k' ∈ kz T V, k' * q * k'⁻¹ * q⁻¹ ∈ fsuU T V) ↔
        q ∈ sL T L V ⊓ (sL T L V).map (MulAut.conj k).toMonoidHom) ∧
      IsElemSection (sL T L V ⊓ (sL T L V).map (MulAut.conj k).toMonoidHom) (fsuU T V) ∧
      (fsuU T V).relIndex (sL T L V ⊓ (sL T L V).map (MulAut.conj k).toMonoidHom) = 4 ∧
      IsL24Section (kz T V) (pCoreOf 2 (kz T V))
        (sL T L V ⊓ (sL T L V).map (MulAut.conj k).toMonoidHom) := by
  have hO := C.pCoreOf_hz_eq
  have hR1 : pCoreOf 2 (l1 T L V) = pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    rw [l1_eq, C.R1_eq_pCoreOf_l1]
  have hUCc : fsuU T V ≤ pCoreOf 2 (kz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) := by
    rw [← hO]
    exact C.fsuU_le_CU
  have hCc7 : Nat.card ↥(pCoreOf 2 (kz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)) =
      2 ^ 7 := by
    rw [← hO]
    exact C.card_CU
  have hL24 : IsL24Section (kz T V) (pCoreOf 2 (kz T V))
      (pCoreOf 2 (kz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G)) := by
    rw [← hO]
    exact (C.l71 G T L V C.hyp).1.1
  refine ⟨⟨?_, ?_, ?_⟩, ?_, fun k hk hkM => ?_⟩
  · rw [hR1, ← C.sup_eq_R1, hO]
  · rw [hR1, C.R1_eq_inf]
    exact inf_le_right
  · obtain ⟨φ, hs, hk⟩ := exists_phi C.hyp C.h63
    obtain ⟨-, h4⟩ := R1_le_kz_sup C.setting C.hF C.h63 C.h1222 C.h1332 C.h1334
    have hKH : kz T V ≤ hz T V := oTwoUpper_le _
    have h60 : (pCoreOf 2 (hz T V)).relIndex (kz T V) = 60 := by
      rw [← card_map_phi hk hKH, show kz T V = oTwoUpper (hz T V) from rfl, phi_map_kz hs hk,
        nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hRK : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ kz T V := by
      rw [C.R1_eq_inf]
      exact inf_le_right
    have hmul := Subgroup.relIndex_mul_relIndex _ _ (kz T V) C.QH_le_R1 hRK
    rw [h4, h60] at hmul
    rw [hR1]
    omega
  · rw [inf_eq_left.mpr C.T_le_L]
    exact C.relIndex_T_inf_kz
  have hSS := C.sL_inf_conj_eq hk hkM
  refine ⟨C.kz_eq_sup hk hkM, C.pCoreOf_kz_eq_sup hk hkM, by rw [← hO]; exact C.card_QH, hSS,
    C.isElemSection_kz hk hkM, ?_, C.isIndec_kz hk hkM, fun q hq => ⟨fun hq' => ?_,
      fun hq' k' hk' => C.comm_mem_fsuU_of_mem_inf hk hkM hq' hk'⟩, ?_, ?_, by rw [hSS]; exact hL24⟩
  · have hc : Nat.card ↥(pCoreOf 2 (kz T V)) = 2 ^ 11 := by rw [← hO]; exact C.card_QH
    have h1 := Subgroup.relIndex_mul_card (fsuU T V) (pCoreOf 2 (kz T V))
    rw [inf_eq_left.mpr (hUCc.trans inf_le_left), C.card_fsuU, hc] at h1
    omega
  · rw [hSS]
    exact hL24.mem_of_comm hq fun k' hk' => hUCc (hq' k' hk')
  · refine ⟨le_inf (le_conjClosure _ _) (C.fsuU_le_conj hk), fun x hx x' hx' =>
      ⟨v_le_fsuU (C.comm_mem C.u0_eq (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx').1),
        v_le_fsuU (C.sq_mem C.u0_eq (Subgroup.mem_inf.mp hx).1)⟩⟩
  · rw [hSS]
    have h1 := Subgroup.relIndex_mul_card (fsuU T V)
      (pCoreOf 2 (kz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G))
    rw [inf_eq_left.mpr hUCc, C.card_fsuU, hCc7] at h1
    omega

end Ctx73

theorem lemma14_7_73_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h63 : Thm14_7_63)
    (h68 : Lemma14_7_68) (h69 : Lemma14_7_69) (h70 : Lemma14_7_70) (h71 : Lemma14_7_71)
    (vh63 : H6.VolI_H_6_3) (vh65 : H6.VolI_H_6_5) : Lemma14_7_73 := by
  have h1334 : A6.Stmt13_3_4 := U3.stmt13_3_4_of h1332
  intro G _ _ T L V h
  have hF : HypF98 T V L (fsuV1 T V) V (hz T V) :=
    Setting147.hypF98 ⟨h, h.isHzOne_hz h63⟩ (stmt13_3_2_two_of_stmt13_3_2 h1332)
      (stmtL32NModule_of_inputs h1332 h1334) h1222
  obtain ⟨l₀, C⟩ := exists_ctx73 h h1222 h1332 h1334 h63 hF h68 h69 h70 h71 vh63 vh65
  exact C.lemma14_7_73

end CFSG.Quasithin.H13.L32A
