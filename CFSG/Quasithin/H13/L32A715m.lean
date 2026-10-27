module

public import CFSG.Quasithin.H13.L32A715l

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Pull

variable {G : Type} [Group G] [Finite G]

theorem eq_of_modO2Image_eq {H K A W : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hQA : pCoreOf 2 K ≤ A) (hWK : W ≤ K)
    (hAW : A ≤ W) (h : modO2Image H W = modO2Image H A) : W = A := by
  refine le_antisymm (fun w hw => ?_) hAW
  have hm : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨w, hKH (hWK hw)⟩ ∈ modO2Image H A := by
    rw [← h]
    exact mem_modO2Image_iff.mpr ⟨_, hw, rfl⟩
  obtain ⟨a, haA, hae⟩ := mem_modO2Image_iff.mp hm
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hae
  have hq : (a : G)⁻¹ * w ∈ pCoreOf 2 H := ⟨_, hae, rfl⟩
  have hqK : (a : G)⁻¹ * w ∈ K := K.mul_mem (K.inv_mem (hWK (hAW haA))) (hWK hw)
  have hqA : (a : G)⁻¹ * w ∈ A := by
    apply hQA
    rw [pCoreOf_eq_inf_pCoreOf hKH hHK]
    exact ⟨hqK, hq⟩
  have e : w = a * ((a : G)⁻¹ * w) := by group
  rw [e]
  exact A.mul_mem haA hqA

end Pull

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
include E

theorem lemma14_7_15_five (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H))
    (hs : F8Setup T V L H γ γ' g) :
    F8.Dγ V (fsuV1 T V) H (g : G) < F8.Uγ V H (g : G) := by
  obtain ⟨hL1K, -, -, -, hHL1⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  exact ((E.h75 G T L V H E.S (modO2Image_normal hHL1)).1 γ γ' g hs).1

theorem r1_irred : ∀ W : Subgroup G, l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ≤ W →
    W ≤ oTwoUpper H → pCoreOf 2 (l1 T L V ⊔ T) ≤ Subgroup.normalizer (W : Set G) →
    W = l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ∨ W = oTwoUpper H := by
  intro W hAW hWK hRW
  obtain ⟨hL1K, -, -, -, hHL1⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  obtain ⟨-, y, hyT, hyC, -, -, -, -, hirr⟩ :=
    lemma14_7_15_two E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.h75 E.S E.three
  obtain ⟨-, -, -, -, hR1C, -⟩ := E.h75 G T L V H E.S (modO2Image_normal hHL1)
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hyR : y ∈ modO2Image H (pCoreOf 2 (l1 T L V ⊔ T)) := by
    rw [hR1C]
    exact ⟨hyT, hyC⟩
  obtain ⟨r, hrR, rfl⟩ := mem_modO2Image_iff.mp hyR
  have hWH : W ≤ H := hWK.trans hKH
  have hA : modO2Image H (l1 T L V ⊔ pCoreOf 2 (oTwoUpper H)) = modO2Image H (l1 T L V) :=
    modO2Image_sup_of_le_pCoreOf (hL1K.trans hKH)
      (by rw [pCoreOf_eq_inf_pCoreOf hKH hHK]; exact inf_le_right)
  have hinv : ∀ w ∈ modO2Image H W, QuotientGroup.mk' (CFSG.pCore 2 ↥H) r * w *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) r)⁻¹ ∈ modO2Image H W := by
    intro w hw
    obtain ⟨w', hw'W, rfl⟩ := mem_modO2Image_iff.mp hw
    refine mem_modO2Image_iff.mpr ⟨r * w' * r⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp (hRW hrR) w').mp hw'W
  have hLW : modO2Image H (l1 T L V) ≤ modO2Image H W := by
    rw [← hA]
    exact modO2Image_mono hAW
  have hWK' : modO2Image H W ≤ oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rw [← modO2Image_oTwoUpper]
    exact modO2Image_mono hWK
  rcases hirr _ hLW hWK' hinv with he | he
  · left
    refine eq_of_modO2Image_eq hKH hHK le_sup_right hWK hAW ?_
    rw [he, hA]
  · right
    symm
    refine eq_of_modO2Image_eq hKH hHK ((le_sup_right).trans hAW) le_rfl hWK ?_
    rw [modO2Image_oTwoUpper, he]

variable (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include hF

theorem two_three : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3 := by
  intro p hp hpd
  have hH := (E.lemma14_7_15_three_of hF).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(hz T V))
  have hpd' : p ∣ Nat.card (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) *
      Nat.card ↥(CFSG.pCore 2 ↥(hz T V)) := by
    rw [← hc, ← hH]
    exact hpd
  rcases (Nat.Prime.dvd_mul hp).mp hpd' with h1 | h2
  · exact E.prime_dvd_card hp h1
  · left
    have hP2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥(hz T V)) := CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    rw [hk] at h2
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)

theorem u_eq : ⁅fsuU T V, l1 T L V⁆ = fsuU T V := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have hH := (E.lemma14_7_15_three_of hF).1
  have hUeq := fsuU_eq_conjClosure_hz hMod E.S.hyp
  obtain ⟨hL1K, -, -, -, hHL1⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  have h5 := (E.h75 G T L V H E.S (modO2Image_normal hHL1)).2.2.2.2.2.2
  rw [hH, ← hUeq] at h5
  have hVL := C.le_commutator_l1 E.h1222 E.h1332 E.h1334 E.S.hyp
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hV1 : fsuV1 T V ≤ ⁅fsuU T V, l1 T L V⁆ :=
    (inf_le_left.trans hVL).trans (Subgroup.commutator_mono hVU le_rfl)
  rw [sup_eq_left.mpr hV1] at h5
  exact h5

end Ctx7153

end CFSG.Quasithin.H13.L32A
