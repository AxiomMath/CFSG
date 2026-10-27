module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenSwapInFSq
public import CFSG.GroupTheory.ElementaryAbelianNine
public import CFSG.GroupTheory.SupMulCommutative
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarImageCalC
public import CFSG.GroupTheory.BarImageConj
public import CFSG.GroupTheory.SupCommute
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem gap17_15_swapOrbit_of {D : Data G} {L : Subgroup G}
    (h3 : ¬ 2 < (conjSetOf D.M L).ncard)
    (hN : ¬ (L.subgroupOf (L ⊔ D.T)).Normal) :
    Gap17_15_swapOrbit D L := by
  obtain ⟨L₂, ⟨t₀, ht₀, rfl⟩, hne, hall⟩ := exists_conj_pair_of_not_normal h3 hN
  have hmapc : ∀ s ∈ D.T, s ∉ normalizer (L : Set G) →
      L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj t₀⁻¹).toMonoidHom := by
    intro s hs hsN
    rcases hall s⁻¹ (D.T.inv_mem hs) with h | h
    · refine absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_) hsN
      simpa [CFSG.Quasithin.conjSubgroup] using h
    · simpa [CFSG.Quasithin.conjSubgroup] using h
  have hprod : ∀ a ∈ D.T, ∀ b ∈ D.T, a ∉ normalizer (L : Set G) →
      b ∉ normalizer (L : Set G) → a * b ∈ normalizer (L : Set G) := by
    intro a ha b hb haN hbN
    have haN' : a⁻¹ ∉ normalizer (L : Set G) := fun h =>
      haN (by simpa using (normalizer (L : Set G)).inv_mem h)
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    change L.map (MulAut.conj (a * b)).toMonoidHom = L
    rw [← Subgroup.map_conj_map_conj, hmapc b hb hbN,
      ← hmapc a⁻¹ (D.T.inv_mem ha) haN', Subgroup.map_conj_map_conj, mul_inv_cancel]
    ext x
    simp
  have hpar : ∀ a ∈ D.T, ∀ b ∈ D.T, (a * b ∈ normalizer (L : Set G) ↔
      (a ∈ normalizer (L : Set G) ↔ b ∈ normalizer (L : Set G))) := by
    intro a ha b hb
    constructor
    · intro hab
      constructor
      · intro haN
        exact (Subgroup.mul_mem_cancel_left _ haN).mp hab
      · intro hbN
        exact (Subgroup.mul_mem_cancel_right _ hbN).mp hab
    · intro hiff
      by_cases haN : a ∈ normalizer (L : Set G)
      · exact (normalizer (L : Set G)).mul_mem haN (hiff.mp haN)
      · exact hprod a ha b hb haN (fun hbN => haN (hiff.mpr hbN))
  have ht₀N : t₀ ∉ normalizer (L : Set G) := by
    intro h
    apply hne
    have h' : t₀⁻¹ ∈ normalizer (L : Set G) := (normalizer (L : Set G)).inv_mem h
    rw [CFSG.Quasithin.conjSubgroup]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp h').symm
  have hinvN : ∀ u : G, (u⁻¹ ∈ normalizer (L : Set G) ↔ u ∈ normalizer (L : Set G)) := by
    intro u
    constructor <;> intro h <;> simpa using (normalizer (L : Set G)).inv_mem h
  refine ⟨fun u hu => ?_, t₀⁻¹, D.T.inv_mem ht₀, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [SetLike.mem_coe, NTL17, Subgroup.mem_inf]
    have hT : x ∈ D.T ↔ u * x * u⁻¹ ∈ D.T := by
      constructor
      · intro hx
        exact D.T.mul_mem (D.T.mul_mem hu hx) (D.T.inv_mem hu)
      · intro hx
        have := D.T.mul_mem (D.T.mul_mem (D.T.inv_mem hu) hx) hu
        simpa [mul_assoc] using this
    constructor
    · rintro ⟨hxT, hxN⟩
      refine ⟨hT.mp hxT, ?_⟩
      have h1 := hpar (u * x) (D.T.mul_mem hu hxT) u⁻¹ (D.T.inv_mem hu)
      have h2 := hpar u hu x hxT
      have h4 := hinvN u
      have hux : u * x ∈ normalizer (L : Set G) ↔ u ∈ normalizer (L : Set G) :=
        h2.trans ⟨fun h => h.mpr hxN, fun h => ⟨fun _ => hxN, fun _ => h⟩⟩
      exact h1.mpr (hux.trans h4.symm)
    · rintro ⟨hxT, hxN⟩
      have hxT' := hT.mpr hxT
      refine ⟨hxT', ?_⟩
      have h1 := hpar (u * x) (D.T.mul_mem hu hxT') u⁻¹ (D.T.inv_mem hu)
      have h2 := hpar u hu x hxT'
      have h4 := hinvN u
      have hux : u * x ∈ normalizer (L : Set G) ↔ u ∈ normalizer (L : Set G) :=
        (h1.mp hxN).trans h4
      by_cases hu' : u ∈ normalizer (L : Set G)
      · exact (h2.mp (hux.mpr hu')).mp hu'
      · by_contra hx'
        exact hu' (hux.mp (h2.mpr ⟨fun h => absurd h hu', fun h => absurd h hx'⟩))
  · intro h
    simp only [NTL17, Subgroup.mem_inf] at h
    exact ht₀N ((hinvN t₀).mp h.2)
  · intro s hs
    by_cases hsN : s ∈ normalizer (L : Set G)
    · left
      show s ∈ D.T ⊓ normalizer (L : Set G)
      exact Subgroup.mem_inf.mpr ⟨hs, hsN⟩
    · right
      rw [inv_inv]
      show t₀ * s ∈ D.T ⊓ normalizer (L : Set G)
      exact Subgroup.mem_inf.mpr ⟨D.T.mul_mem ht₀ hs, hprod t₀ ht₀ s hs ht₀N hsN⟩

section SwapStep

variable {D : Data G} {V₀ V L X : Subgroup G} {r q : ℕ} {t : G}

theorem gap17_15_barImage_card (hX3 : Nat.card X = 3) (htT : t ∈ D.T) :
    Nat.card (barImage (X ⊔ D.T) X) = 3 ∧
      Nat.card (barImage (X ⊔ D.T) (X.map (MulAut.conj t).toMonoidHom)) = 3 := by
  have hXt3 : Nat.card (X.map (MulAut.conj t).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, hX3]
  have hXtH : X.map (MulAut.conj t).toMonoidHom ≤ X ⊔ D.T := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact (X ⊔ D.T).mul_mem
      ((X ⊔ D.T).mul_mem (Subgroup.mem_sup_right htT) (Subgroup.mem_sup_left hx))
      ((X ⊔ D.T).inv_mem (Subgroup.mem_sup_right htT))
  have hdisjX : X ⊓ pCoreOf 2 (X ⊔ D.T) = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) X (pCoreOf 2 (X ⊔ D.T))
      (IsPGroup.of_card (n := 1) (by rw [hX3]; norm_num))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ D.T)))
  have hdisjXt : X.map (MulAut.conj t).toMonoidHom ⊓ pCoreOf 2 (X ⊔ D.T) = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num)
      (X.map (MulAut.conj t).toMonoidHom) (pCoreOf 2 (X ⊔ D.T))
      (IsPGroup.of_card (n := 1) (by rw [hXt3]; norm_num))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ D.T)))
  exact ⟨(CFSG.Quasithin.P134.card_modO2Image le_sup_left hdisjX).trans hX3,
    (CFSG.Quasithin.P134.card_modO2Image hXtH hdisjXt).trans hXt3⟩

theorem gap17_15_barImage_commute (hC : Ctx17_6 D V₀ V L r q) (hXL : X ≤ L) (htT : t ∈ D.T)
    (htS : t ∉ NTL17 D L) :
    ∀ a ∈ barImage (X ⊔ D.T) X,
      ∀ b ∈ barImage (X ⊔ D.T) (X.map (MulAut.conj t).toMonoidHom), a * b = b * a := by
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hLM : L ≤ D.M := hC.memL.1.le
  have hO2L_O2M : pCoreOf 2 L ≤ pCoreOf 2 D.M :=
    CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hC.memL.1
  have hMt : D.M.map (MulAut.conj t).toMonoidHom = D.M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hTM htT))
  have hLtcal : L.map (MulAut.conj t).toMonoidHom ∈ calC D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map D.M (MulAut.conj t) hMt hC.memL
  have hLt_ne : L ≠ L.map (MulAut.conj t).toMonoidHom := by
    intro h
    exact htS (Subgroup.mem_inf.mpr ⟨htT, Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm⟩)
  have hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ ≤ pCoreOf 2 D.M :=
    ((calC_commutator_le_of_ne hC.memL hLtcal hLt_ne).trans inf_le_left).trans hO2L_O2M
  have hO2M_le_T : pCoreOf 2 D.M ≤ D.T :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf
      (CFSG.QuasithinUnique.Setup.Lift.isSylowTwoOf_of_isSylowOf D.sylowM)
  have hH_le_M : X ⊔ D.T ≤ D.M := sup_le (hXL.trans hLM) hTM
  have hO2M_le_O2H : pCoreOf 2 D.M ≤ pCoreOf 2 (X ⊔ D.T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (hO2M_le_T.trans le_sup_right)
      (hH_le_M.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
  have hXtH : X.map (MulAut.conj t).toMonoidHom ≤ X ⊔ D.T := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact (X ⊔ D.T).mul_mem
      ((X ⊔ D.T).mul_mem (Subgroup.mem_sup_right htT) (Subgroup.mem_sup_left hx))
      ((X ⊔ D.T).inv_mem (Subgroup.mem_sup_right htT))
  refine CFSG.Quasithin.modO2Image_commute ?_
  exact ((Subgroup.commutator_mono hXL (Subgroup.map_mono hXL)).trans hcomm).trans hO2M_le_O2H

theorem gap17_15_barImage_inf (hC : Ctx17_6 D V₀ V L r q) (h7 : IsL2Over17 (Bar2 L) 7)
    (hXL : X ≤ L) (hX3 : Nat.card X = 3) (htT : t ∈ D.T) (htS : t ∉ NTL17 D L) :
    barImage (X ⊔ D.T) X ⊓ barImage (X ⊔ D.T) (X.map (MulAut.conj t).toMonoidHom) = ⊥ := by
  classical
  let H : Subgroup G := X ⊔ D.T
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hLM : L ≤ D.M := hC.memL.1.le
  have hMt : D.M.map (MulAut.conj t).toMonoidHom = D.M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hTM htT))
  have hLtcal : L.map (MulAut.conj t).toMonoidHom ∈ calC D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map D.M (MulAut.conj t) hMt hC.memL
  have hLt_ne : L ≠ L.map (MulAut.conj t).toMonoidHom := by
    intro h
    exact htS (Subgroup.mem_inf.mpr ⟨htT, Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm⟩)
  have hXtH : X.map (MulAut.conj t).toMonoidHom ≤ H := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact H.mul_mem (H.mul_mem (Subgroup.mem_sup_right htT) (Subgroup.mem_sup_left hx))
      (H.inv_mem (Subgroup.mem_sup_right htT))
  have hXt_ne : X.map (MulAut.conj t).toMonoidHom ≠ X :=
    map_conj_ne_of_mem_calC hC.memL h7 (hTM htT) hLt_ne.symm hXL hX3
  obtain ⟨hA3, hB3⟩ := gap17_15_barImage_card (D := D) (X := X) (t := t) hX3 htT
  by_contra hne
  have hAB : barImage H X = barImage H (X.map (MulAut.conj t).toMonoidHom) := by
    have hcard : Nat.card ↥(barImage H X ⊓
        barImage H (X.map (MulAut.conj t).toMonoidHom)) = 3 := by
      have hdvd : Nat.card ↥(barImage H X ⊓
          barImage H (X.map (MulAut.conj t).toMonoidHom)) ∣ 3 := by
        rw [← hA3]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (Subgroup.card_eq_one.mp h1) hne
      · exact h3
    have hAle : barImage H X ≤ barImage H (X.map (MulAut.conj t).toMonoidHom) := by
      have h1 : barImage H X ⊓ barImage H (X.map (MulAut.conj t).toMonoidHom) =
          barImage H X :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (hA3.trans hcard.symm))
      calc barImage H X = barImage H X ⊓
            barImage H (X.map (MulAut.conj t).toMonoidHom) := h1.symm
        _ ≤ barImage H (X.map (MulAut.conj t).toMonoidHom) := inf_le_right
    exact Subgroup.eq_of_le_of_card_ge hAle (le_of_eq (hB3.trans hA3.symm))
  have hXt_le : X.map (MulAut.conj t).toMonoidHom ≤ X ⊔ pCoreOf 2 H := by
    intro y hy
    have hyH : y ∈ H := hXtH hy
    have hmemB : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨y, hyH⟩ ∈
        barImage H (X.map (MulAut.conj t).toMonoidHom) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy)
    rw [← hAB] at hmemB
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hmemB
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hker : (⟨y, hyH⟩ : ↥H) * x⁻¹ ∈ CFSG.pCore 2 ↥H := by
      rw [← QuotientGroup.eq_one_iff]
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ((⟨y, hyH⟩ : ↥H) * x⁻¹) = 1
      rw [map_mul, map_inv, hxeq]
      simp
    have hO2 : y * (x : G)⁻¹ ∈ pCoreOf 2 H :=
      (CFSG.mem_openPCoreOf_iff ((⟨y, hyH⟩ : ↥H) * x⁻¹)).mpr hker
    have hy_eq : y = (y * (x : G)⁻¹) * (x : G) := by group
    rw [hy_eq, sup_comm]
    exact Subgroup.mul_mem_sup hO2 hxX
  have hXtM : X.map (MulAut.conj t).toMonoidHom ≤ D.M := by
    calc X.map (MulAut.conj t).toMonoidHom ≤ L.map (MulAut.conj t).toMonoidHom :=
          Subgroup.map_mono hXL
      _ ≤ D.M.map (MulAut.conj t).toMonoidHom := Subgroup.map_mono hLM
      _ = D.M := hMt
  have hdisjXM : X ⊓ pCoreOf 2 D.M = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) X (pCoreOf 2 D.M)
      (IsPGroup.of_card (n := 1) (by rw [hX3]; norm_num))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M))
  have hXt3 : Nat.card (X.map (MulAut.conj t).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, hX3]
  have hdisjXtM : X.map (MulAut.conj t).toMonoidHom ⊓ pCoreOf 2 D.M = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num)
      (X.map (MulAut.conj t).toMonoidHom) (pCoreOf 2 D.M)
      (IsPGroup.of_card (n := 1) (by rw [hXt3]; norm_num))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M))
  have hXbarM3 : Nat.card (barImage D.M X) = 3 :=
    (CFSG.Quasithin.P134.card_modO2Image (hXL.trans hLM) hdisjXM).trans hX3
  have hXtbarM3 : Nat.card (barImage D.M (X.map (MulAut.conj t).toMonoidHom)) = 3 :=
    (CFSG.Quasithin.P134.card_modO2Image hXtM hdisjXtM).trans hXt3
  have hcommM : ∀ a ∈ barImage D.M X,
      ∀ b ∈ barImage D.M (X.map (MulAut.conj t).toMonoidHom), a * b = b * a := by
    refine CFSG.Quasithin.modO2Image_commute ?_
    have hO2L_O2M : pCoreOf 2 L ≤ pCoreOf 2 D.M :=
      CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hC.memL.1
    have hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ ≤ pCoreOf 2 D.M :=
      ((calC_commutator_le_of_ne hC.memL hLtcal hLt_ne).trans inf_le_left).trans hO2L_O2M
    exact (Subgroup.commutator_mono hXL (Subgroup.map_mono hXL)).trans hcomm
  have hdisjM : barImage D.M X ⊓ barImage D.M (X.map (MulAut.conj t).toMonoidHom) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzX, hzXt⟩ := Subgroup.mem_inf.mp hz
    have hzL : z ∈ barImage D.M L := barImage_mono hXL hzX
    have hzLt : z ∈ barImage D.M (L.map (MulAut.conj t).toMonoidHom) :=
      barImage_mono (Subgroup.map_mono hXL) hzXt
    have hLtM : L.map (MulAut.conj t).toMonoidHom ≤ D.M := by
      calc L.map (MulAut.conj t).toMonoidHom ≤ D.M.map (MulAut.conj t).toMonoidHom :=
            Subgroup.map_mono hLM
        _ = D.M := hMt
    have hcommL : ∀ a ∈ barImage D.M L,
        ∀ b ∈ barImage D.M (L.map (MulAut.conj t).toMonoidHom), a * b = b * a := by
      refine CFSG.Quasithin.modO2Image_commute ?_
      have hO2L_O2M : pCoreOf 2 L ≤ pCoreOf 2 D.M :=
        CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hC.memL.1
      exact ((calC_commutator_le_of_ne hC.memL hLtcal hLt_ne).trans inf_le_left).trans hO2L_O2M
    have hcent : (⟨z, hzL⟩ : ↥(barImage D.M L)) ∈
        Subgroup.center (barImage D.M L) := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      exact hcommL (w : Bar2 D.M) w.2 z hzLt
    rw [center_barImage_eq_bot_of_isSubnormal hC.memL.1
      (center_eq_bot_of_isL3 (isL3_one_of_isL2Over17_seven h7))] at hcent
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hcent)
  have hcard9 : Nat.card ↥(barImage D.M X ⊔
      barImage D.M (X.map (MulAut.conj t).toMonoidHom)) = 9 := by
    rw [CFSG.card_sup_eq_mul_of_commute _ _ hcommM hdisjM, hXbarM3, hXtbarM3]
  have hO2H_T : pCoreOf 2 H ≤ D.T := by
    have hTsylOf : CFSG.ABGLocalTools.IsSylowOf 2 D.T H :=
      D.sylowM.of_le le_sup_right (sup_le (hXL.trans hLM) hTM)
    exact CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf
      ((CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf).mpr hTsylOf)
  have hXO2_card : Nat.card ↥(X ⊔ pCoreOf 2 H) = 3 * Nat.card (pCoreOf 2 H) := by
    have hXnorm : X ≤ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
      (le_sup_left : X ≤ H).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
    have hdisjXH : X ⊓ pCoreOf 2 H = ⊥ :=
      disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) X (pCoreOf 2 H)
        (IsPGroup.of_card (n := 1) (by rw [hX3]; norm_num))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H))
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      hXnorm
    rw [hdisjXH, Subgroup.card_bot, hX3, mul_one] at h
    linarith
  have h9dvd : 9 ∣ Nat.card ↥(X ⊔ pCoreOf 2 H) := by
    have hle : barImage D.M X ⊔ barImage D.M (X.map (MulAut.conj t).toMonoidHom) ≤
        barImage D.M (X ⊔ pCoreOf 2 H) := by
      rw [← s13_barImage_sup (hXL.trans hLM) hXtM]
      exact barImage_mono (sup_le le_sup_left hXt_le)
    calc 9 = Nat.card ↥(barImage D.M X ⊔
          barImage D.M (X.map (MulAut.conj t).toMonoidHom)) := hcard9.symm
      _ ∣ Nat.card ↥(barImage D.M (X ⊔ pCoreOf 2 H)) := Subgroup.card_dvd_of_le hle
      _ ∣ Nat.card ↥((X ⊔ pCoreOf 2 H).subgroupOf D.M) := by
            rw [barImage]
            exact Subgroup.card_map_dvd _ _
      _ = Nat.card ↥(X ⊔ pCoreOf 2 H) := Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (show X ⊔ pCoreOf 2 H ≤ D.M from
              sup_le (hXL.trans hLM) (hO2H_T.trans hTM))).toEquiv
  rw [hXO2_card] at h9dvd
  obtain ⟨k, hk⟩ := h9dvd
  have h3dvd : 3 ∣ Nat.card (pCoreOf 2 H) := ⟨k, by omega⟩
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).exists_card_eq
  rw [ha] at h3dvd
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd) (by norm_num)


theorem nonempty_bar2_P17_equiv_perm (hK : K_L27PermutesS3) (hC : Ctx17_6 D V₀ V L r q)
    (h7 : IsL2Over17 (Bar2 L) 7) (hXL : X ≤ L) (hX3 : Nat.card X = 3)
    (hperm : Permutes X (NTL17 D L)) :
    Nonempty (Bar2 (P17 D X L) ≃* Equiv.Perm (Fin 3)) := by
  classical
  set S0 : Subgroup G := D.T ⊓ L with hS0def
  set P1 : Subgroup G := P17 D X L with hP1def
  have hLM : L ≤ D.M := hC.memL.1.le
  have hS0L : S0 ≤ L := inf_le_right
  have hS0S : S0 ≤ NTL17 D L := fun x hx =>
    Subgroup.mem_inf.mpr ⟨hx.1, Subgroup.le_normalizer hx.2⟩
  have hP1L : P1 ≤ L := by
    rw [hP1def, P17]
    exact sup_le (sup_le hXL hS0L) (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  have hS0syl2 : CFSG.QuasithinUnique.IsSylowTwoOf S0 L :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal
      (CFSG.QuasithinUnique.Setup.Lift.isSylowTwoOf_of_isSylowOf D.sylowM) hLM
      ((CFSG.Quasithin.isSubnormal_iff_subgroupOf hLM).mp hC.memL.1)
  have hS0sylIn : IsSylowIn 2 S0 L :=
    (CFSG.ABGLocalTools.isSylowOf_iff).mp
      ((CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf).mp hS0syl2)
  let πL : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let Xbar : Subgroup (Bar2 L) := (X.subgroupOf L).map πL
  let S0bar : Subgroup (Bar2 L) := (S0.subgroupOf L).map πL
  have hS0bar_syl : IsSylowIn 2 S0bar ⊤ :=
    CFSG.LocalAnalysis.WeakClosure81.isSylowIn_barImage hS0sylIn
  have hXp : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by rw [hX3]; norm_num)
  have hXO : X ⊓ pCoreOf 2 L = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) X (pCoreOf 2 L) hXp
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L))
  have hXker : (X.subgroupOf L) ⊓ πL.ker = ⊥ := by
    rw [show πL.ker = CFSG.pCore 2 ↥L from QuotientGroup.ker_mk' _]
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzX, hzP⟩ := Subgroup.mem_inf.mp hz
    have hzG : (z : G) ∈ X ⊓ pCoreOf 2 L := by
      refine ⟨Subgroup.mem_subgroupOf.mp hzX, ?_⟩
      have hpcmap : (CFSG.pCore 2 ↥L).map L.subtype = pCoreOf 2 L :=
        (CFSG.openPCoreOf_eq_map_pCore 2 L).symm
      rw [← hpcmap]
      exact Subgroup.mem_map_of_mem L.subtype hzP
    rw [hXO] at hzG
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hzG))
  have hXbar_card : Nat.card Xbar = 3 := by
    rw [show Nat.card Xbar = Nat.card ↥(X.subgroupOf L) from
      CFSG.card_map_eq_card_of_inf_ker_eq_bot πL hXker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv, hX3]
  have hpermS0 : Permutes X S0 := by
    have hsub : ((X : Set G) * (S0 : Set G)) ⊆ ((S0 : Set G) * (X : Set G)) := by
      rintro _ ⟨x, hx, s, hs, rfl⟩
      have hsS : s ∈ NTL17 D L := hS0S hs
      have hmem : x * s ∈ (NTL17 D L : Set G) * (X : Set G) := by
        rw [← hperm]
        exact Set.mul_mem_mul hx hsS
      obtain ⟨s', hs', x', hx', hxs⟩ := hmem
      have hs'L : s' ∈ L := by
        have e : s' = x * s * x'⁻¹ := by rw [← hxs]; group
        rw [e]
        exact L.mul_mem (L.mul_mem (hXL hx) (hS0L hs)) (L.inv_mem (hXL hx'))
      exact ⟨s', ⟨hs'.1, hs'L⟩, x', hx', hxs⟩
    have hsub' : ((S0 : Set G) * (X : Set G)) ⊆ ((X : Set G) * (S0 : Set G)) := by
      rintro _ ⟨s, hs, x, hx, rfl⟩
      have hsS : s ∈ NTL17 D L := hS0S hs
      have hmem : s * x ∈ (NTL17 D L : Set G) * (X : Set G) := Set.mul_mem_mul hsS hx
      rw [← hperm] at hmem
      obtain ⟨x', hx', s', hs', hxs⟩ := hmem
      have hs'L : s' ∈ L := by
        have e : s' = x'⁻¹ * (s * x) := by rw [← hxs]; group
        rw [e]
        exact L.mul_mem (L.inv_mem (hXL hx')) (L.mul_mem (hS0L hs) (hXL hx))
      exact ⟨x', hx', s', ⟨hs'.1, hs'L⟩, hxs⟩
    exact Set.Subset.antisymm hsub hsub'
  have hpermSub : Permutes (X.subgroupOf L) (S0.subgroupOf L) :=
    CFSG.Quasithin.H.Tri.subgroupOf_mul_comm hXL hS0L hpermS0
  have hpermbar : Permutes Xbar S0bar := CFSG.GroupTheory.map_permutes_map πL hpermSub
  have hL2odd : IsL2Odd (Bar2 L) 7 := isL2Odd_seven_of_isL2Over17_seven h7
  obtain ⟨-, -, ⟨eS3⟩, -⟩ :=
    hK (Bar2 L) hL2odd S0bar hS0bar_syl Xbar hXbar_card hpermbar
  let ψ : ↥P1 →* Bar2 L := πL.comp (Subgroup.inclusion hP1L)
  have hψrange : ψ.range = Xbar ⊔ S0bar := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    have hsub : P1.subgroupOf L = X.subgroupOf L ⊔ S0.subgroupOf L ⊔ CFSG.pCore 2 ↥L := by
      rw [hP1def, P17]
      rw [Subgroup.subgroupOf_sup (sup_le hXL hS0L) (CFSG.LieType.BorelTits.pCoreOf_le 2 L),
        Subgroup.subgroupOf_sup hXL hS0L]
      congr 1
      exact CFSG.Quasithin.A4.subgroupOf_map_subtype' L (CFSG.pCore 2 ↥L)
    rw [hsub, Subgroup.map_sup, Subgroup.map_sup]
    have hbot : (CFSG.pCore 2 ↥L).map πL = ⊥ :=
      (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 ↥L) (f := πL)).mpr
        (by rw [QuotientGroup.ker_mk'])
    rw [hbot, sup_bot_eq]
  have hψmem : ∀ z : ↥P1, ψ z ∈ Xbar ⊔ S0bar := by
    intro z
    rw [← hψrange]
    exact ⟨z, rfl⟩
  let φ : ↥P1 →* ↥(Xbar ⊔ S0bar) := ψ.codRestrict _ hψmem
  have hφsurj : Function.Surjective φ := by
    intro w
    have hw : (w : Bar2 L) ∈ ψ.range := by rw [hψrange]; exact w.2
    obtain ⟨z, hz⟩ := hw
    exact ⟨z, Subtype.ext hz⟩
  have hφker_eq : φ.ker = (pCoreOf 2 L).subgroupOf P1 := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hz
      have h1 : (φ z : Bar2 L) = 1 := congrArg Subtype.val hz
      rw [show (φ z : Bar2 L) = πL ⟨(z : G), hP1L z.2⟩ from rfl,
        show πL ⟨(z : G), hP1L z.2⟩ = QuotientGroup.mk ⟨(z : G), hP1L z.2⟩ from rfl,
        QuotientGroup.eq_one_iff] at h1
      exact (CFSG.mem_openPCoreOf_iff (⟨(z : G), hP1L z.2⟩ : ↥L)).mpr h1
    · intro hz
      have h1 : πL ⟨(z : G), hP1L z.2⟩ = 1 := by
        rw [show πL ⟨(z : G), hP1L z.2⟩ = QuotientGroup.mk ⟨(z : G), hP1L z.2⟩ from rfl]
        exact (QuotientGroup.eq_one_iff _).mpr ((CFSG.mem_openPCoreOf_iff _).mp hz)
      apply Subtype.ext
      change (φ z : Bar2 L) = 1
      rwa [show (φ z : Bar2 L) = πL ⟨(z : G), hP1L z.2⟩ from rfl]
  have hφker : IsPGroup 2 φ.ker := by
    rw [hφker_eq]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).of_equiv
      (Subgroup.subgroupOfEquivOfLe (show pCoreOf 2 L ≤ P1 from le_sup_right)).symm
  obtain ⟨e⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker
    φ hφsurj hφker
  exact ⟨e.trans eS3⟩

theorem map_conj_le_sup_pCoreOf_of_mem_NTL17 (hK : K_L27PermutesS3)
    (hC : Ctx17_6 D V₀ V L r q) (h7 : IsL2Over17 (Bar2 L) 7)
    (h7S : IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7) (hXL : X ≤ L) (hX3 : Nat.card X = 3)
    (hperm : Permutes X (NTL17 D L))
    (hSnorm : D.T ≤ normalizer ((NTL17 D L : Subgroup G) : Set G)) (htT : t ∈ D.T)
    (htS : t ∉ NTL17 D L) (hcoset : ∀ s ∈ D.T, s ∈ NTL17 D L ∨ t⁻¹ * s ∈ NTL17 D L)
    {s : G} (hs : s ∈ NTL17 D L) :
    X.map (MulAut.conj s).toMonoidHom ≤ X ⊔ pCoreOf 2 (X ⊔ D.T) := by
  classical
  have hP1L : P17 D X L ≤ L := by
    rw [P17]
    exact sup_le (sup_le hXL inf_le_right) (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  have hX_P1 : X ≤ P17 D X L := by
    rw [P17]
    exact le_sup_left.trans le_sup_left
  have hSP1 : s ∈ Subgroup.normalizer ((P17 D X L : Subgroup G) : Set G) :=
    ntl17_le_normalizer_P1 hC h7 h7S hXL hs
  obtain ⟨e⟩ := nonempty_bar2_P17_equiv_perm hK hC h7 hXL hX3 hperm
  have hP1bar : Nat.card (Bar2 (P17 D X L)) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    norm_num
  have hXdisj : X ⊓ pCoreOf 2 (P17 D X L) = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) X (pCoreOf 2 (P17 D X L))
      (IsPGroup.of_card (n := 1) (by rw [hX3]; norm_num))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P17 D X L)))
  have hXbar_card : Nat.card (barImage (P17 D X L) X) = 3 :=
    (CFSG.Quasithin.P134.card_modO2Image hX_P1 hXdisj).trans hX3
  have hXs_P1 : X.map (MulAut.conj s).toMonoidHom ≤ P17 D X L := by
    calc X.map (MulAut.conj s).toMonoidHom
        ≤ (P17 D X L).map (MulAut.conj s).toMonoidHom := Subgroup.map_mono hX_P1
      _ = P17 D X L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hSP1
  have hXs3 : Nat.card (X.map (MulAut.conj s).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj s).injective, hX3]
  have hXsdisj : X.map (MulAut.conj s).toMonoidHom ⊓ pCoreOf 2 (P17 D X L) = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num)
      (X.map (MulAut.conj s).toMonoidHom) (pCoreOf 2 (P17 D X L))
      (IsPGroup.of_card (n := 1) (by rw [hXs3]; norm_num))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P17 D X L)))
  have hXsbar_card :
      Nat.card (barImage (P17 D X L) (X.map (MulAut.conj s).toMonoidHom)) = 3 :=
    (CFSG.Quasithin.P134.card_modO2Image hXs_P1 hXsdisj).trans hXs3
  have hEq : barImage (P17 D X L) X =
      barImage (P17 D X L) (X.map (MulAut.conj s).toMonoidHom) :=
    CFSG.Quasithin.H13.A5.eq_of_card_three_of_card_six hP1bar hXbar_card hXsbar_card
  have hO2H : pCoreOf 2 (P17 D X L) ≤ pCoreOf 2 (X ⊔ D.T) :=
    pCoreOf_P1_le_pCoreOf_H hC h7 h7S hXL ⟨hSnorm, t, htT, htS, hcoset⟩
  intro y hy
  have hyP1 : y ∈ P17 D X L := hXs_P1 hy
  have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥(P17 D X L))) ⟨y, hyP1⟩ ∈
      barImage (P17 D X L) (X.map (MulAut.conj s).toMonoidHom) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy)
  rw [← hEq] at hmem
  obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hmem
  have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
  have hker : (⟨y, hyP1⟩ : ↥(P17 D X L)) * x⁻¹ ∈ CFSG.pCore 2 ↥(P17 D X L) := by
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥(P17 D X L)))
      ((⟨y, hyP1⟩ : ↥(P17 D X L)) * x⁻¹) = 1
    rw [map_mul, map_inv, hxeq]
    simp
  have hO2P1 : y * (x : G)⁻¹ ∈ pCoreOf 2 (P17 D X L) :=
    (CFSG.mem_openPCoreOf_iff ((⟨y, hyP1⟩ : ↥(P17 D X L)) * x⁻¹)).mpr hker
  have hy_eq : y = (y * (x : G)⁻¹) * (x : G) := by group
  rw [hy_eq, sup_comm]
  exact Subgroup.mul_mem_sup (hO2H hO2P1) hxX

theorem gap17_15_barImage_normal (hK : K_L27PermutesS3) (hC : Ctx17_6 D V₀ V L r q)
    (h7 : IsL2Over17 (Bar2 L) 7) (h7S : IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7) (hXL : X ≤ L)
    (hX3 : Nat.card X = 3) (hperm : Permutes X (NTL17 D L))
    (hSnorm : D.T ≤ normalizer ((NTL17 D L : Subgroup G) : Set G)) (htT : t ∈ D.T)
    (htS : t ∉ NTL17 D L) (hcoset : ∀ s ∈ D.T, s ∈ NTL17 D L ∨ t⁻¹ * s ∈ NTL17 D L) :
    (barImage (X ⊔ D.T) X ⊔ barImage (X ⊔ D.T) (X.map (MulAut.conj t).toMonoidHom)).Normal := by
  classical
  let H : Subgroup G := X ⊔ D.T
  have hSH : NTL17 D L ≤ H := inf_le_left.trans le_sup_right
  have hTH : D.T ≤ H := le_sup_right
  have hbar_pcore : barImage H (pCoreOf 2 H) = ⊥ := by
    rw [barImage, CFSG.openPCoreOf_subgroupOf, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hbar_sup_X : barImage H (X ⊔ pCoreOf 2 H) = barImage H X := by
    rw [s13_barImage_sup (le_sup_left : X ≤ H) (CFSG.LieType.BorelTits.pCoreOf_le 2 H),
      hbar_pcore, sup_bot_eq]
  have hXtH : X.map (MulAut.conj t).toMonoidHom ≤ H := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact H.mul_mem (H.mul_mem (Subgroup.mem_sup_right htT) (Subgroup.mem_sup_left hx))
      (H.inv_mem (Subgroup.mem_sup_right htT))
  have hbar_sup_Xt : barImage H (X.map (MulAut.conj t).toMonoidHom ⊔ pCoreOf 2 H) =
      barImage H (X.map (MulAut.conj t).toMonoidHom) := by
    rw [s13_barImage_sup hXtH (CFSG.LieType.BorelTits.pCoreOf_le 2 H), hbar_pcore, sup_bot_eq]
  have hA_conj_le : ∀ s ∈ NTL17 D L,
      barImage H (X.map (MulAut.conj s).toMonoidHom) ≤ barImage H X := by
    intro s hs
    calc barImage H (X.map (MulAut.conj s).toMonoidHom)
        ≤ barImage H (X ⊔ pCoreOf 2 H) :=
          barImage_mono (map_conj_le_sup_pCoreOf_of_mem_NTL17 hK hC h7 h7S hXL hX3 hperm
            hSnorm htT htS hcoset hs)
      _ = barImage H X := hbar_sup_X
  have hB_conj_le : ∀ s ∈ NTL17 D L,
      barImage H ((X.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom) ≤
        barImage H (X.map (MulAut.conj t).toMonoidHom) := by
    intro s hs
    have hσS : t⁻¹ * s * t ∈ NTL17 D L := by
      have h1 : (NTL17 D L).map (MulAut.conj t⁻¹).toMonoidHom = NTL17 D L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSnorm (D.T.inv_mem htT))
      have h2 : (MulAut.conj t⁻¹) s ∈ (NTL17 D L).map (MulAut.conj t⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hs
      rw [h1] at h2
      simpa [MulAut.conj_apply] using h2
    have hEq : (X.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom =
        (X.map (MulAut.conj (t⁻¹ * s * t)).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have hle : (X.map (MulAut.conj (t⁻¹ * s * t)).toMonoidHom).map
          (MulAut.conj t).toMonoidHom ≤ X.map (MulAut.conj t).toMonoidHom ⊔ pCoreOf 2 H := by
      calc (X.map (MulAut.conj (t⁻¹ * s * t)).toMonoidHom).map (MulAut.conj t).toMonoidHom
          ≤ (X ⊔ pCoreOf 2 H).map (MulAut.conj t).toMonoidHom :=
            Subgroup.map_mono (map_conj_le_sup_pCoreOf_of_mem_NTL17 hK hC h7 h7S hXL hX3 hperm
              hSnorm htT htS hcoset hσS)
        _ = X.map (MulAut.conj t).toMonoidHom ⊔ (pCoreOf 2 H).map (MulAut.conj t).toMonoidHom :=
            Subgroup.map_sup _ _ _
        _ = X.map (MulAut.conj t).toMonoidHom ⊔ pCoreOf 2 H := by
            have hO2t : (pCoreOf 2 H).map (MulAut.conj t).toMonoidHom = pCoreOf 2 H :=
              Subgroup.mem_normalizer_iff_map_conj_eq.mp
                (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hTH htT))
            rw [hO2t]
    rw [hEq]
    calc barImage H ((X.map (MulAut.conj (t⁻¹ * s * t)).toMonoidHom).map
          (MulAut.conj t).toMonoidHom)
        ≤ barImage H (X.map (MulAut.conj t).toMonoidHom ⊔ pCoreOf 2 H) := barImage_mono hle
      _ = barImage H (X.map (MulAut.conj t).toMonoidHom) := hbar_sup_Xt
  obtain ⟨hA3, hB3⟩ := gap17_15_barImage_card (D := D) (X := X) (t := t) hX3 htT
  have hAt : (barImage H X).map
      (MulAut.conj (QuotientGroup.mk ⟨t, hTH htT⟩)).toMonoidHom =
      barImage H (X.map (MulAut.conj t).toMonoidHom) := by
    exact (CFSG.GroupTheory.barImage_map_conj H X le_sup_left (hTH htT)).symm
  have ht2S : t ^ 2 ∈ NTL17 D L := sq_mem_ntl17 htT htS hcoset
  have hBt_le : (barImage H (X.map (MulAut.conj t).toMonoidHom)).map
      (MulAut.conj (QuotientGroup.mk ⟨t, hTH htT⟩)).toMonoidHom ≤ barImage H X := by
    erw [← CFSG.GroupTheory.barImage_map_conj H _ hXtH (hTH htT)]
    have hEq : (X.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom =
        X.map (MulAut.conj (t ^ 2)).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, pow_two, mul_assoc]
    rw [hEq]
    exact hA_conj_le (t ^ 2) ht2S
  have hBt : (barImage H (X.map (MulAut.conj t).toMonoidHom)).map
      (MulAut.conj (QuotientGroup.mk ⟨t, hTH htT⟩)).toMonoidHom = barImage H X := by
    refine Subgroup.eq_of_le_of_card_ge hBt_le ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact le_of_eq (hA3.trans hB3.symm)
  have hR_S : ∀ (s : G) (hs : s ∈ NTL17 D L),
      (barImage H X ⊔ barImage H (X.map (MulAut.conj t).toMonoidHom)).map
        (MulAut.conj (QuotientGroup.mk ⟨s, hSH hs⟩)).toMonoidHom =
      (barImage H X ⊔ barImage H (X.map (MulAut.conj t).toMonoidHom)) := by
    intro s hs
    rw [Subgroup.map_sup]
    have hcard1 : Nat.card ↥(barImage H (X.map (MulAut.conj s).toMonoidHom)) =
        Nat.card ↥(barImage H X) := by
      rw [show barImage H (X.map (MulAut.conj s).toMonoidHom) = _ from
        CFSG.GroupTheory.barImage_map_conj H X le_sup_left (hSH hs)]
      exact Subgroup.card_map_of_injective (MulAut.conj _).injective
    have h1 : (barImage H X).map
        (MulAut.conj (QuotientGroup.mk ⟨s, hSH hs⟩)).toMonoidHom = barImage H X := by
      erw [← CFSG.GroupTheory.barImage_map_conj H X le_sup_left (hSH hs)]
      exact Subgroup.eq_of_le_of_card_ge (hA_conj_le s hs) (le_of_eq hcard1.symm)
    have hcard2 : Nat.card ↥(barImage H
        ((X.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom)) =
        Nat.card ↥(barImage H (X.map (MulAut.conj t).toMonoidHom)) := by
      rw [show barImage H ((X.map (MulAut.conj t).toMonoidHom).map
          (MulAut.conj s).toMonoidHom) = _ from
        CFSG.GroupTheory.barImage_map_conj H _ hXtH (hSH hs)]
      exact Subgroup.card_map_of_injective (MulAut.conj _).injective
    have h2 : (barImage H (X.map (MulAut.conj t).toMonoidHom)).map
        (MulAut.conj (QuotientGroup.mk ⟨s, hSH hs⟩)).toMonoidHom =
        barImage H (X.map (MulAut.conj t).toMonoidHom) := by
      erw [← CFSG.GroupTheory.barImage_map_conj H _ hXtH (hSH hs)]
      exact Subgroup.eq_of_le_of_card_ge (hB_conj_le s hs) (le_of_eq hcard2.symm)
    rw [h1, h2]
  have hR_t : (barImage H X ⊔ barImage H (X.map (MulAut.conj t).toMonoidHom)).map
      (MulAut.conj (QuotientGroup.mk ⟨t, hTH htT⟩)).toMonoidHom =
      (barImage H X ⊔ barImage H (X.map (MulAut.conj t).toMonoidHom)) := by
    rw [Subgroup.map_sup, hAt, hBt, sup_comm]
  have hgen : barImage H X ⊔ barImage H D.T = ⊤ := by
    rw [barImage, barImage, ← Subgroup.map_sup]
    have hsup : X.subgroupOf H ⊔ D.T.subgroupOf H = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (A := X) (A' := D.T) (B := H)
        le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    rw [hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hnorm : (barImage H X ⊔ barImage H (X.map (MulAut.conj t).toMonoidHom)).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen]
    apply sup_le
    · exact (le_sup_left : barImage H X ≤
        barImage H X ⊔ barImage H (X.map (MulAut.conj t).toMonoidHom)).trans Subgroup.le_normalizer
    · intro g hg
      obtain ⟨s, hs, hgs⟩ := Subgroup.mem_map.mp hg
      have hgs' : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) s = g := hgs
      rw [← hgs']
      rcases hcoset s hs with hsS | hsS
      · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        exact hR_S s hsS
      ·
        have hσS : t⁻¹ * s ∈ NTL17 D L := hsS
        have hσH : t⁻¹ * s ∈ H := hSH hσS
        have hs_eq : s = t * (t⁻¹ * s) := by group
        have hg_eq : (QuotientGroup.mk ⟨s, hTH hs⟩ : Bar2 H) =
            QuotientGroup.mk ⟨t, hTH htT⟩ * QuotientGroup.mk ⟨t⁻¹ * s, hσH⟩ := by
          have h1 : (⟨s, hTH hs⟩ : ↥H) = ⟨t, hTH htT⟩ * ⟨t⁻¹ * s, hσH⟩ := by
            ext
            simpa using hs_eq
          change (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨s, hTH hs⟩ =
            (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨t, hTH htT⟩ *
              (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨t⁻¹ * s, hσH⟩
          rw [← map_mul, h1]
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        calc (barImage H X ⊔ barImage H (X.map (MulAut.conj t).toMonoidHom)).map
              (MulAut.conj (QuotientGroup.mk ⟨s, hTH hs⟩)).toMonoidHom
            = ((barImage H X ⊔ barImage H (X.map (MulAut.conj t).toMonoidHom)).map
                (MulAut.conj (QuotientGroup.mk ⟨t⁻¹ * s, hσH⟩)).toMonoidHom).map
                (MulAut.conj (QuotientGroup.mk ⟨t, hTH htT⟩)).toMonoidHom := by
              rw [hg_eq, Subgroup.map_map]
              congr 1
              ext x
              simp [MulAut.conj_apply, mul_assoc]
          _ = (barImage H X ⊔ barImage H (X.map (MulAut.conj t).toMonoidHom)).map
                (MulAut.conj (QuotientGroup.mk ⟨t, hTH htT⟩)).toMonoidHom := by
              rw [hR_S (t⁻¹ * s) hσS]
          _ = barImage H X ⊔ barImage H (X.map (MulAut.conj t).toMonoidHom) := hR_t
  exact hnorm

theorem gap17_15_barImage_minimal (hK : K_L27PermutesS3) (hC : Ctx17_6 D V₀ V L r q)
    (h7 : IsL2Over17 (Bar2 L) 7) (h7S : IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7) (hXL : X ≤ L)
    (hX3 : Nat.card X = 3) (hperm : Permutes X (NTL17 D L))
    (hSnorm : D.T ≤ normalizer ((NTL17 D L : Subgroup G) : Set G)) (htT : t ∈ D.T)
    (htS : t ∉ NTL17 D L) (hcoset : ∀ s ∈ D.T, s ∈ NTL17 D L ∨ t⁻¹ * s ∈ NTL17 D L) :
    ∀ N : Subgroup (Bar2 (X ⊔ D.T)), N.Normal →
      N ≤ barImage (X ⊔ D.T) X ⊔ barImage (X ⊔ D.T) (X.map (MulAut.conj t).toMonoidHom) →
        N = ⊥ ∨
          N = barImage (X ⊔ D.T) X ⊔ barImage (X ⊔ D.T) (X.map (MulAut.conj t).toMonoidHom) := by
  classical
  let H : Subgroup G := X ⊔ D.T
  let A : Subgroup (Bar2 H) := barImage H X
  let B : Subgroup (Bar2 H) := barImage H (X.map (MulAut.conj t).toMonoidHom)
  let R : Subgroup (Bar2 H) := A ⊔ B
  have hTH : D.T ≤ H := le_sup_right
  have hA3 : Nat.card ↥A = 3 :=
    (gap17_15_barImage_card (D := D) (X := X) (t := t) hX3 htT).1
  have hB3 : Nat.card ↥B = 3 :=
    (gap17_15_barImage_card (D := D) (X := X) (t := t) hX3 htT).2
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := gap17_15_barImage_commute hC hXL htT htS
  have hdisj : A ⊓ B = ⊥ := gap17_15_barImage_inf hC h7 hXL hX3 htT htS
  have hR9 : Nat.card ↥R = 9 := by
    rw [show R = A ⊔ B from rfl,
      CFSG.card_sup_eq_mul_of_commute _ _ hcomm hdisj, hA3, hB3]
  have hAcyc : IsCyclic ↥A := isCyclic_of_prime_card hA3
  have hBcyc : IsCyclic ↥B := isCyclic_of_prime_card hB3
  have hRcomm : IsMulCommutative ↥R :=
    CFSG.GroupTheory.isMulCommutative_sup_of_elementwise_commute hcomm
      (@IsCyclic.isMulCommutative ↥A _ hAcyc) (@IsCyclic.isMulCommutative ↥B _ hBcyc)
  have hRn : R.Normal :=
    gap17_15_barImage_normal hK hC h7 h7S hXL hX3 hperm hSnorm htT htS hcoset
  obtain ⟨d, hd, hinv⟩ := exists_inverting_of_permutes hK hC h7 hXL hX3 hperm
  have hdH : d ∈ H := (show D.T ⊓ L ≤ H from inf_le_left.trans hTH) hd
  have hinvH : ∀ x ∈ X, d * x * d⁻¹ * x ∈ pCoreOf 2 H := fun x hx =>
    pCoreOf_P1_le_pCoreOf_H hC h7 h7S hXL ⟨hSnorm, t, htT, htS, hcoset⟩ (hinv x hx)
  let dQ : Bar2 H := QuotientGroup.mk ⟨d, hdH⟩
  let tQ : Bar2 H := QuotientGroup.mk ⟨t, hTH htT⟩
  have hdA : ∀ a ∈ A, dQ * a * dQ⁻¹ = a⁻¹ := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hmem : d * (x : G) * d⁻¹ * (x : G) ∈ pCoreOf 2 H := hinvH (x : G) hxX
    have hmem' : (⟨d * (x : G) * d⁻¹ * (x : G), H.mul_mem
        (H.mul_mem (H.mul_mem hdH x.2) (H.inv_mem hdH)) x.2⟩ : ↥H) ∈
        CFSG.pCore 2 ↥H := (CFSG.mem_openPCoreOf_iff _).mp hmem
    have h1 : dQ * (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) x * dQ⁻¹ =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
          ⟨d * (x : G) * d⁻¹, H.mul_mem (H.mul_mem hdH x.2) (H.inv_mem hdH)⟩ := by
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨d, hdH⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) x *
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨d, hdH⟩)⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [h1]
    have h3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
        ⟨d * (x : G) * d⁻¹ * (x : G), H.mul_mem
          (H.mul_mem (H.mul_mem hdH x.2) (H.inv_mem hdH)) x.2⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem'
    have h4 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
        ⟨d * (x : G) * d⁻¹, H.mul_mem (H.mul_mem hdH x.2) (H.inv_mem hdH)⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) x = 1 := by
      rw [← map_mul]
      exact h3
    exact eq_inv_of_mul_eq_one_left h4
  have hdB : ∀ b ∈ B, dQ * b * dQ⁻¹ = b := by
    intro b hb
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    have hyLt : (y : G) ∈ L.map (MulAut.conj t).toMonoidHom :=
      Subgroup.map_mono hXL (Subgroup.mem_subgroupOf.mp hy)
    have hMt : D.M.map (MulAut.conj t).toMonoidHom = D.M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (D.sylowM.le htT))
    have hLtcal : L.map (MulAut.conj t).toMonoidHom ∈ calC D.M :=
      CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map D.M (MulAut.conj t) hMt hC.memL
    have hLt_ne : L ≠ L.map (MulAut.conj t).toMonoidHom := by
      intro h
      exact htS (Subgroup.mem_inf.mpr ⟨htT, Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm⟩)
    have hO2L_O2M : pCoreOf 2 L ≤ pCoreOf 2 D.M :=
      CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hC.memL.1
    have hcommL : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ ≤ pCoreOf 2 D.M :=
      ((calC_commutator_le_of_ne hC.memL hLtcal hLt_ne).trans inf_le_left).trans hO2L_O2M
    have hO2M_le_T : pCoreOf 2 D.M ≤ D.T :=
      CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf
        (CFSG.QuasithinUnique.Setup.Lift.isSylowTwoOf_of_isSylowOf D.sylowM)
    have hO2M_le_H : pCoreOf 2 D.M ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (hO2M_le_T.trans hTH)
        ((sup_le (hXL.trans hC.memL.1.le) (D.sylowM.le)).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
    have hdy : ⁅(d : G), (y : G)⁆ ∈ pCoreOf 2 H :=
      hO2M_le_H (hcommL (Subgroup.commutator_mem_commutator hd.2 hyLt))
    have hmem : d * (y : G) * d⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 H := by
      simpa [commutatorElement_def] using hdy
    have hmem' : (⟨d * (y : G) * d⁻¹ * (y : G)⁻¹, H.mul_mem
        (H.mul_mem (H.mul_mem hdH y.2) (H.inv_mem hdH)) (H.inv_mem y.2)⟩ : ↥H) ∈
        CFSG.pCore 2 ↥H := (CFSG.mem_openPCoreOf_iff _).mp hmem
    have h1 : dQ * (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) y * dQ⁻¹ =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
          ⟨d * (y : G) * d⁻¹, H.mul_mem (H.mul_mem hdH y.2) (H.inv_mem hdH)⟩ := by
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨d, hdH⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) y *
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨d, hdH⟩)⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [h1]
    have h3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
        ⟨d * (y : G) * d⁻¹ * (y : G)⁻¹, H.mul_mem
          (H.mul_mem (H.mul_mem hdH y.2) (H.inv_mem hdH)) (H.inv_mem y.2)⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem'
    have h5 : (⟨d * (y : G) * d⁻¹, H.mul_mem (H.mul_mem hdH y.2) (H.inv_mem hdH)⟩ : ↥H) *
        (⟨y, y.2⟩ : ↥H)⁻¹ =
        ⟨d * (y : G) * d⁻¹ * (y : G)⁻¹, H.mul_mem
          (H.mul_mem (H.mul_mem hdH y.2) (H.inv_mem hdH)) (H.inv_mem y.2)⟩ := by
      ext
      simp [mul_assoc]
    have h4 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
        ⟨d * (y : G) * d⁻¹, H.mul_mem (H.mul_mem hdH y.2) (H.inv_mem hdH)⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) y⁻¹ = 1 := by
      rw [← map_mul, h5]
      exact h3
    rw [map_inv] at h4
    exact mul_inv_eq_one.mp h4
  have htAB : ∀ a ∈ A, tQ * a * tQ⁻¹ ∈ B := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have h1 : tQ * (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) x * tQ⁻¹ =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
          ⟨t * (x : G) * t⁻¹, H.mul_mem (H.mul_mem (hTH htT) x.2)
            (H.inv_mem (hTH htT))⟩ := by
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨t, hTH htT⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) x *
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨t, hTH htT⟩)⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [h1]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hxX))
  have htBA : ∀ b ∈ B, tQ * b * tQ⁻¹ ∈ A := by
    intro b hb
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    have hyXt : (y : G) ∈ X.map (MulAut.conj t).toMonoidHom := Subgroup.mem_subgroupOf.mp hy
    have hty : t * (y : G) * t⁻¹ ∈ X.map (MulAut.conj (t ^ 2)).toMonoidHom := by
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hyXt
      have h2 : t * (y : G) * t⁻¹ = t ^ 2 * x * (t ^ 2)⁻¹ := by
        rw [← hxy]
        change t * (t * x * t⁻¹) * t⁻¹ = t ^ 2 * x * (t ^ 2)⁻¹
        rw [pow_two]
        group
      rw [h2]
      exact Subgroup.mem_map_of_mem _ hx
    have h1 : tQ * (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) y * tQ⁻¹ =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
          ⟨t * (y : G) * t⁻¹, H.mul_mem (H.mul_mem (hTH htT) y.2)
            (H.inv_mem (hTH htT))⟩ := by
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨t, hTH htT⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) y *
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨t, hTH htT⟩)⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [h1]
    have ht2S : t ^ 2 ∈ NTL17 D L := sq_mem_ntl17 htT htS hcoset
    have hle : t * (y : G) * t⁻¹ ∈ X ⊔ pCoreOf 2 H :=
      map_conj_le_sup_pCoreOf_of_mem_NTL17 hK hC h7 h7S hXL hX3 hperm hSnorm htT htS
        hcoset ht2S hty
    have hbar_pcore : barImage H (pCoreOf 2 H) = ⊥ := by
      change Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
        ((pCoreOf 2 H).subgroupOf H) = ⊥
      rw [CFSG.openPCoreOf_subgroupOf, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hbar_sup_X : barImage H (X ⊔ pCoreOf 2 H) = barImage H X := by
      rw [s13_barImage_sup (le_sup_left : X ≤ H) (CFSG.LieType.BorelTits.pCoreOf_le 2 H),
        hbar_pcore, sup_bot_eq]
    rw [show A = barImage H X from rfl, ← hbar_sup_X]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hle)
  intro N hN hNR
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  · right
    by_contra hNtop
    have hN3 : Nat.card ↥N = 3 := by
      have hdvd : Nat.card ↥N ∣ 3 ^ 2 := by
        rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hR9]
        exact Subgroup.card_dvd_of_le hNR
      obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      interval_cases k
      · exact absurd (Subgroup.card_eq_one.mp hk) hNbot
      · exact hk
      · exact absurd (Subgroup.eq_of_le_of_card_ge hNR (le_of_eq (hk.trans hR9.symm).symm)) hNtop
    have hdisj' : A.subgroupOf R ⊓ B.subgroupOf R = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
      have hxG : (x : Bar2 H) ∈ A ⊓ B :=
        ⟨Subgroup.mem_subgroupOf.mp hxA, Subgroup.mem_subgroupOf.mp hxB⟩
      rw [hdisj] at hxG
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxG))
    have hsup' : A.subgroupOf R ⊔ B.subgroupOf R = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (show A ≤ R from le_sup_left) (show B ≤ R from le_sup_right)]
      exact Subgroup.subgroupOf_self (A ⊔ B)
    have hA'3 : Nat.card ↥(A.subgroupOf R) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show A ≤ R from le_sup_left)).toEquiv, hA3]
    have hB'3 : Nat.card ↥(B.subgroupOf R) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show B ≤ R from le_sup_right)).toEquiv, hB3]
    have hN'3 : Nat.card ↥(N.subgroupOf R) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv, hN3]
    let φ : MulAut ↥R := MulAut.conjNormal (H := R) dQ
    have hφA : ∀ a ∈ A.subgroupOf R, φ a = a⁻¹ := by
      intro a ha
      have haA : (a : Bar2 H) ∈ A := Subgroup.mem_subgroupOf.mp ha
      apply Subtype.ext
      exact hdA (a : Bar2 H) haA
    have hφB : ∀ b ∈ B.subgroupOf R, φ b = b := by
      intro b hb
      have hbB : (b : Bar2 H) ∈ B := Subgroup.mem_subgroupOf.mp hb
      apply Subtype.ext
      exact hdB (b : Bar2 H) hbB
    have hφN : ∀ n ∈ N.subgroupOf R, φ n ∈ N.subgroupOf R := by
      intro n hn
      have hnN : (n : Bar2 H) ∈ N := Subgroup.mem_subgroupOf.mp hn
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.Normal.conj_mem hN (n : Bar2 H) hnN dQ
    have hmain := @CFSG.GroupTheory.eq_left_or_right_of_aut_inverts_fixes ↥R
      (@IsMulCommutative.instCommGroup ↥R _ hRcomm) _
      (A.subgroupOf R) (B.subgroupOf R) (N.subgroupOf R) hA'3 hB'3 hN'3 hdisj' hsup'
      φ hφA hφB hφN
    have htN : N.map (MulAut.conj tQ).toMonoidHom = N :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (by
        rw [Subgroup.normalizer_eq_top_iff.mpr hN]
        exact Subgroup.mem_top tQ)
    have hAt : A.map (MulAut.conj tQ).toMonoidHom = B := by
      rw [show A = barImage H X from rfl,
        show B = barImage H (X.map (MulAut.conj t).toMonoidHom) from rfl]
      exact (CFSG.GroupTheory.barImage_map_conj H X le_sup_left (hTH htT)).symm
    have hBt : B.map (MulAut.conj tQ).toMonoidHom = A := by
      rw [show B = barImage H (X.map (MulAut.conj t).toMonoidHom) from rfl]
      erw [← CFSG.GroupTheory.barImage_map_conj H _
        (show X.map (MulAut.conj t).toMonoidHom ≤ H from by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
          exact H.mul_mem (H.mul_mem (hTH htT) (Subgroup.mem_sup_left hx))
            (H.inv_mem (hTH htT)))
        (hTH htT)]
      have h2 : (X.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom =
          X.map (MulAut.conj (t ^ 2)).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, pow_two, mul_assoc]
      rw [h2, show A = barImage H X from rfl]
      have ht2S : t ^ 2 ∈ NTL17 D L := sq_mem_ntl17 htT htS hcoset
      have hbar_pcore : barImage H (pCoreOf 2 H) = ⊥ := by
        change Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
          ((pCoreOf 2 H).subgroupOf H) = ⊥
        rw [CFSG.openPCoreOf_subgroupOf, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      have hbar_sup_X : barImage H (X ⊔ pCoreOf 2 H) = barImage H X := by
        rw [s13_barImage_sup (le_sup_left : X ≤ H) (CFSG.LieType.BorelTits.pCoreOf_le 2 H),
          hbar_pcore, sup_bot_eq]
      have hle : barImage H (X.map (MulAut.conj (t ^ 2)).toMonoidHom) ≤ barImage H X := by
        calc barImage H (X.map (MulAut.conj (t ^ 2)).toMonoidHom)
            ≤ barImage H (X ⊔ pCoreOf 2 H) :=
              barImage_mono (map_conj_le_sup_pCoreOf_of_mem_NTL17 hK hC h7 h7S hXL hX3 hperm
                hSnorm htT htS hcoset ht2S)
          _ = barImage H X := hbar_sup_X
      have hXt2H : X.map (MulAut.conj (t ^ 2)).toMonoidHom ≤ H :=
        (map_conj_le_sup_pCoreOf_of_mem_NTL17 hK hC h7 h7S hXL hX3 hperm hSnorm htT htS
          hcoset ht2S).trans (sup_le le_sup_left (CFSG.LieType.BorelTits.pCoreOf_le 2 H))
      have hXt23 : Nat.card (X.map (MulAut.conj (t ^ 2)).toMonoidHom) = 3 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hX3]
      have hdisjXt2 : X.map (MulAut.conj (t ^ 2)).toMonoidHom ⊓ pCoreOf 2 H = ⊥ :=
        disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num)
          (X.map (MulAut.conj (t ^ 2)).toMonoidHom) (pCoreOf 2 H)
          (IsPGroup.of_card (n := 1) (by rw [hXt23]; norm_num))
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H))
      have hcard : Nat.card ↥(barImage H (X.map (MulAut.conj (t ^ 2)).toMonoidHom)) = 3 :=
        (CFSG.Quasithin.P134.card_modO2Image hXt2H hdisjXt2).trans hXt23
      exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hcard.trans hA3.symm).symm)
    rcases hmain with h | h
    · have hNA : N = A := by
        have h1 := congrArg (Subgroup.map R.subtype) h
        rwa [Subgroup.map_subgroupOf_eq_of_le hNR,
          Subgroup.map_subgroupOf_eq_of_le (show A ≤ R from le_sup_left)] at h1
      rw [hNA, hAt] at htN
      have hbot : A = ⊥ := by
        rw [← hdisj, ← htN, inf_idem]
      rw [hbot] at hA3
      simp at hA3
    · have hNB : N = B := by
        have h1 := congrArg (Subgroup.map R.subtype) h
        rwa [Subgroup.map_subgroupOf_eq_of_le hNR,
          Subgroup.map_subgroupOf_eq_of_le (show B ≤ R from le_sup_right)] at h1
      rw [hNB, hBt] at htN
      have hbot : B = ⊥ := by
        rw [← hdisj, ← htN, inf_idem]
      rw [hbot] at hB3
      simp at hB3

theorem gap17_15_barImage_top :
    barImage (X ⊔ D.T) X ⊔ barImage (X ⊔ D.T) (X.map (MulAut.conj t).toMonoidHom) ⊔
      barImage (X ⊔ D.T) D.T = ⊤ := by
  have hgen : barImage (X ⊔ D.T) X ⊔ barImage (X ⊔ D.T) D.T = ⊤ := by
    rw [barImage, barImage, ← Subgroup.map_sup]
    have hsup : X.subgroupOf (X ⊔ D.T) ⊔ D.T.subgroupOf (X ⊔ D.T) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (A := X) (A' := D.T) (B := X ⊔ D.T)
        le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    rw [hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  calc barImage (X ⊔ D.T) X ⊔ barImage (X ⊔ D.T) (X.map (MulAut.conj t).toMonoidHom) ⊔
        barImage (X ⊔ D.T) D.T
      = barImage (X ⊔ D.T) (X.map (MulAut.conj t).toMonoidHom) ⊔
          (barImage (X ⊔ D.T) X ⊔ barImage (X ⊔ D.T) D.T) := by ac_rfl
    _ = barImage (X ⊔ D.T) (X.map (MulAut.conj t).toMonoidHom) ⊔ ⊤ := by rw [hgen]
    _ = ⊤ := sup_top_eq _

end SwapStep

theorem gap17_15_swapStep1_holds (hK : K_L27PermutesS3) (D : Data G) {V₀ V L : Subgroup G}
    {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q) : Gap17_15_swapStep1 D V₀ V L r q hC := by
  intro h7 h7not h7S hN hthree X hXL hX3 hperm
  classical
  obtain ⟨hSnorm, t, htT, htS, hcoset⟩ :=
    gap17_15_swapOrbit_of (D := D) (L := L) hthree hN
  let H : Subgroup G := X ⊔ D.T
  let A : Subgroup (Bar2 H) := barImage H X
  let B : Subgroup (Bar2 H) := barImage H (X.map (MulAut.conj t).toMonoidHom)
  let R : Subgroup (Bar2 H) := A ⊔ B
  have hA3 : Nat.card ↥A = 3 :=
    (gap17_15_barImage_card (D := D) (X := X) (t := t) hX3 htT).1
  have hB3 : Nat.card ↥B = 3 :=
    (gap17_15_barImage_card (D := D) (X := X) (t := t) hX3 htT).2
  have hcommAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a :=
    gap17_15_barImage_commute hC hXL htT htS
  have hdisj : A ⊓ B = ⊥ := gap17_15_barImage_inf hC h7 hXL hX3 htT htS
  have hRn : R.Normal :=
    gap17_15_barImage_normal hK hC h7 h7S hXL hX3 hperm hSnorm htT htS hcoset
  have hRmin : ∀ N : Subgroup (Bar2 H), N.Normal → N ≤ R → N = ⊥ ∨ N = R :=
    gap17_15_barImage_minimal hK hC h7 h7S hXL hX3 hperm hSnorm htT htS hcoset
  have hRtop : R ⊔ ((D.T.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) = ⊤ :=
    gap17_15_barImage_top (D := D) (X := X) (t := t)
  have hAcyc : IsCyclic ↥A := isCyclic_of_prime_card hA3
  have hBcyc : IsCyclic ↥B := isCyclic_of_prime_card hB3
  have hRcomm : IsMulCommutative ↥R :=
    CFSG.GroupTheory.isMulCommutative_sup_of_elementwise_commute hcommAB
      (@IsCyclic.isMulCommutative ↥A _ hAcyc) (@IsCyclic.isMulCommutative ↥B _ hBcyc)
  have hcommR : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (isMulCommutative_iff.mp hRcomm ⟨a, ha⟩ ⟨b, hb⟩)
  have hR9 : Nat.card ↥R = 9 := by
    rw [show R = A ⊔ B from rfl,
      CFSG.card_sup_eq_mul_of_commute _ _ hcommAB hdisj, hA3, hB3]
  have hRp : IsPGroup 3 R := IsPGroup.of_card (n := 2) (by rw [hR9]; norm_num)
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hle : A ≤ R := le_sup_left
    rw [hbot, le_bot_iff] at hle
    rw [hle] at hA3
    simp at hA3
  exact ⟨R, hRn, hcommR, hRp, hRne, hRmin, hRtop⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
