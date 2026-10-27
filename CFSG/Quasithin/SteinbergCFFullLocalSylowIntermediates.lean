module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.Quasithin.SteinbergCF

open CFSG Subgroup

variable {G : Type*} [Group G]

theorem charTwo_iff_isCharacteristicP {K : Subgroup G} :
    CFSG.QuasithinUnique.CharTwo K ↔ IsCharacteristicP 2 K :=
  CFSG.QuasithinUnique.charTwo_iff_isCharacteristicP

theorem pCore_map_eq_pCoreOf (K : Subgroup G) :
    (pCore 2 K).map K.subtype = CFSG.Open.pCoreOf 2 K := by
  rw [CFSG.Open.pCoreOf]

theorem quasithinEvenCharacteristic_of_isEvenCharacteristic (hev : IsEvenCharacteristic G) :
    CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G := fun H hH hS =>
  charTwo_iff_isCharacteristicP.mpr (hev H hH hS)

theorem isEvenCharacteristic_of_quasithinEvenCharacteristic
    (h : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) : IsEvenCharacteristic G :=
  fun H hH hS => charTwo_iff_isCharacteristicP.mp (h H hH hS)

theorem quasithinEvenCharacteristic_iff_isEvenCharacteristic :
    CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G ↔ IsEvenCharacteristic G :=
  ⟨isEvenCharacteristic_of_quasithinEvenCharacteristic,
    quasithinEvenCharacteristic_of_isEvenCharacteristic⟩

theorem charTwo_of_sylow_le [Finite G] {X J P : Subgroup G}
    (hX : CFSG.QuasithinUnique.CharTwo X) (hP : CFSG.QuasithinUnique.IsSylowTwoOf P X)
    (hPJ : P ≤ J) (hJX : J ≤ X) :
    CFSG.QuasithinUnique.CharTwo J :=
  CFSG.QuasithinUnique.charTwo_of_pCore_centralizer_le hX hJX
    (inf_le_left.trans ((CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hP).trans
      hPJ))

theorem isSylowTwoOf_of_le_of_le {P X H : Subgroup G}
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf P H) (hPX : P ≤ X) (hXH : X ≤ H) :
    CFSG.QuasithinUnique.IsSylowTwoOf P X := by
  refine ⟨hPX, hP.2.1, fun h => hP.2.2 ?_⟩
  change 2 ∣ P.relIndex H
  change 2 ∣ P.relIndex X at h
  exact h.trans ⟨_, (relIndex_mul_relIndex P X H hPX hXH).symm⟩

theorem full_local_Sylow_intermediates_centralizer_controls_char_two_test [Finite G]
    (hev : IsEvenCharacteristic G) (T : Sylow 2 G) {B H I : Subgroup G} (hBT : B ≤ T)
    (hBH : B ⊔ centralizer (B : Set G) ≤ H) (hHB : H ≤ normalizer (B : Set G))
    (hR : ¬ 2 ∣ ((T : Subgroup G) ⊓ H).relIndex H) (hRI : (T : Subgroup G) ⊓ H ≤ I)
    (hIH : I ≤ H) :
    let R : Subgroup G := (T : Subgroup G) ⊓ H
    let Z : Subgroup G := ((omega₁ (center (T : Subgroup G)) (p := 2)).map
      (center (T : Subgroup G)).subtype).map (T : Subgroup G).subtype
    B ≤ (pCore 2 I).map I.subtype ∧ Z ≤ (center R).map R.subtype ∧
      (∀ z ∈ Z, z ≠ 1 → ∀ M ∈ maximalTwoLocalsContaining (centralizer ({z} : Set G) : Set G),
        R ≤ M ∧ IsCharacteristicP 2 M ∧ IsCharacteristicP 2 (I ⊓ M : Subgroup G) ∧
        centralizer ({z} : Set G) ≤ M ∧
        (pCore 2 M).map M.subtype ⊓ centralizer
          (((pCore 2 (I ⊓ M : Subgroup G)).map (I ⊓ M).subtype : Subgroup G) : Set G) ≤ I) ∧
      (Z ⊓ (pCore 2 I).map I.subtype ≠ ⊥ → IsCharacteristicP 2 I) := by
  intro R Z
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hev' := quasithinEvenCharacteristic_of_isEvenCharacteristic hev
  have hT2 : CFSG.QuasithinUnique.IsSylowTwoOf (T : Subgroup G) ⊤ := by
    refine ⟨le_top, T.isPGroup', ?_⟩
    rw [← relIndex, relIndex_top_right]
    exact T.not_dvd_index
  have hB2 : IsPGroup 2 B := T.isPGroup'.to_le hBT
  have hBH' : B ≤ H := le_sup_left.trans hBH
  have hCH : centralizer (B : Set G) ≤ H := le_sup_right.trans hBH
  have hRT : R ≤ T := inf_le_left
  have hRH : R ≤ H := inf_le_right
  have hBR : B ≤ R := le_inf hBT hBH'
  have hBI : B ≤ I := hBR.trans hRI
  have hRsyl : CFSG.QuasithinUnique.IsSylowTwoOf R H := ⟨hRH, T.isPGroup'.to_le hRT, hR⟩
  have hZT : ∀ z ∈ Z, z ∈ (T : Subgroup G) ∧ ∀ t ∈ (T : Subgroup G), z * t = t * z := by
    rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    refine ⟨(w : T).2, fun t ht => ?_⟩
    have h := mem_center_iff.mp w.2 ⟨t, ht⟩
    exact (congrArg Subtype.val h).symm
  have hBO : B ≤ (pCore 2 I).map I.subtype := by
    rw [pCore_map_eq_pCoreOf]
    exact CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer hBI (hIH.trans hHB) hB2
  have hZR : Z ≤ (center R).map R.subtype := by
    intro z hz
    obtain ⟨hzT, hzc⟩ := hZT z hz
    have hzC : z ∈ centralizer (B : Set G) :=
      mem_centralizer_iff.mpr fun b hb => (hzc b (hBT hb)).symm
    have hzR : z ∈ R := ⟨hzT, hCH hzC⟩
    exact ⟨⟨z, hzR⟩, mem_center_iff.mpr fun r => Subtype.ext (hzc r (hRT r.2)).symm, rfl⟩
  have hHM : ∀ M : Subgroup G, CFSG.QuasithinUnique.CharTwo M → B ≤ M →
      CFSG.QuasithinUnique.CharTwo (H ⊓ M) := by
    intro M hM hBM
    refine CFSG.QuasithinUnique.charTwo_of_centralizer_sup_le_of_le_normalizer hM hBM hB2
      (sup_le (le_inf hBH' hBM) (le_inf (inf_le_right.trans hCH) inf_le_left))
      (le_inf inf_le_right (inf_le_left.trans hHB))
  refine ⟨hBO, hZR, fun z hz hz1 M hM => ?_, fun hZD => ?_⟩
  · obtain ⟨hMloc, hCM⟩ := hM
    obtain ⟨hzT, hzc⟩ := hZT z hz
    have hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G) := fun t ht => by
      rw [mem_centralizer_iff]
      rintro _ rfl
      exact hzc t ht
    have hCzM : centralizer ({z} : Set G) ≤ M := fun x hx => hCM hx
    have hTM : (T : Subgroup G) ≤ M := hTC.trans hCzM
    have hMchar : IsCharacteristicP 2 M := hev M hMloc.1 ⟨T, hTM⟩
    have hMc : CFSG.QuasithinUnique.CharTwo M := charTwo_iff_isCharacteristicP.mpr hMchar
    have hRM : R ≤ M := hRT.trans hTM
    have hHMc := hHM M hMc (hBT.trans hTM)
    have hRsylHM : CFSG.QuasithinUnique.IsSylowTwoOf R (H ⊓ M) :=
      isSylowTwoOf_of_le_of_le hRsyl (le_inf hRH hRM) inf_le_left
    have hIMc : CFSG.QuasithinUnique.CharTwo (I ⊓ M) :=
      charTwo_of_sylow_le hHMc hRsylHM (le_inf hRI hRM) (inf_le_inf_right M hIH)
    refine ⟨hRM, hMchar, charTwo_iff_isCharacteristicP.mp hIMc, hCzM, ?_⟩
    rw [pCore_map_eq_pCoreOf, pCore_map_eq_pCoreOf]
    intro x hx
    have hBIM : B ≤ CFSG.Open.pCoreOf 2 (I ⊓ M) :=
      CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer (le_inf hBI (hBT.trans hTM))
        (inf_le_left.trans (hIH.trans hHB)) hB2
    have hxC : x ∈ centralizer (B : Set G) :=
      centralizer_le (SetLike.coe_subset_coe.mpr hBIM) hx.2
    have hxT : x ∈ (T : Subgroup G) :=
      CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
        (CFSG.QuasithinUnique.isSylowTwoOf_of_le hT2 hTM) hx.1
    exact hRI ⟨hxT, hCH hxC⟩
  ·
    set D : Subgroup G := CFSG.Open.pCoreOf 2 I with hD
    have hD2 : IsPGroup 2 D := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 I
    have hDZ : D ⊓ ((T : Subgroup G) ⊓ centralizer ((T : Subgroup G) : Set G)) ≠ ⊥ := by
      intro hbot
      apply hZD
      rw [eq_bot_iff] at hbot ⊢
      intro x hx
      obtain ⟨hxT, hxc⟩ := hZT x hx.1
      refine hbot ⟨?_, hxT, mem_centralizer_iff.mpr fun t ht => (hxc t ht).symm⟩
      have := hx.2
      rwa [pCore_map_eq_pCoreOf] at this
    have hNc := CFSG.QuasithinUnique.charTwo_normalizer_of_inf_center hev' hT2 hD2 hDZ
    have hIN : I ≤ normalizer (D : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 I
    have hHNc := hHM _ hNc (hBI.trans hIN)
    have hRsylHN : CFSG.QuasithinUnique.IsSylowTwoOf R (H ⊓ normalizer (D : Set G)) :=
      isSylowTwoOf_of_le_of_le hRsyl (le_inf hRH (hRI.trans hIN)) inf_le_left
    exact charTwo_iff_isCharacteristicP.mp
      (charTwo_of_sylow_le hHNc hRsylHN hRI (le_inf hIH hIN))

end CFSG.Quasithin.SteinbergCF
