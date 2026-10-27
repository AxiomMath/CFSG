module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SevenLocal17
public import CFSG.Adapters.StatedPSLTwo
public import CFSG.GroupTheory.PermutingProducts
public import CFSG.Quasithin.H13.NQBlockXTPlacement
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ImageOTwoQuotNormalizer
public import CFSG.GroupTheory.PermutesConjSupNoncyclic
public import CFSG.GroupTheory.PermutesPullback
public import CFSG.Quasithin.H13.L32NLem1444d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section OrbitProduct

open CFSG.GroupTheory

theorem imageOTwoQuot_not_le_center_of_not_le_O2Z {D : Data G} {L X : Subgroup G}
    (hL : L ∈ calC D.M) (hXL : X ≤ L)
    (hXnc : ¬ X ≤ (O2ZIn17 L).map L.subtype) :
    ¬ CFSG.Quasithin.imageOTwoQuot D.M X ≤
      (Subgroup.center ↥(K1Nine D L)).map (K1Nine D L).subtype := by
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hPL : ∀ l : ↥L, ((l : G) ∈ CFSG.Open.pCoreOf 2 L ↔
      (l : G) ∈ CFSG.Open.pCoreOf 2 D.M) := by
    intro l
    constructor
    · intro hl
      exact CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hL.1 hl
    · intro hl
      have hnorm : L ≤ Subgroup.normalizer ((L ⊓ CFSG.Open.pCoreOf 2 D.M : Subgroup G) :
          Set G) := fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx,
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M (hLM hx)⟩
      have hle : L ⊓ CFSG.Open.pCoreOf 2 D.M ≤ CFSG.Open.pCoreOf 2 L :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm
          ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M).to_le inf_le_right)
      exact hle ⟨l.2, hl⟩
  intro hcen
  apply hXnc
  intro x hx
  have hxL : x ∈ L := hXL hx
  have hxM : x ∈ D.M := hLM hxL
  refine Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, ?_, rfl⟩
  rw [O2ZIn17, Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective (s := (CFSG.pCore 2 ↥L)) z
  let aD : ↥D.M := ⟨(y : G), hLM y.2⟩
  let bD : ↥D.M := ⟨x, hxM⟩
  let aL : ↥L := y
  let bL : ↥L := ⟨x, hxL⟩
  have hxA : (QuotientGroup.mk bD : Mbar9 D) ∈ CFSG.Quasithin.imageOTwoQuot D.M X :=
    CFSG.Quasithin.mem_imageOTwoQuot_iff.mpr ⟨x, hxM, hx, rfl⟩
  have hxcenter : (QuotientGroup.mk bD : Mbar9 D) ∈
      (Subgroup.center ↥(K1Nine D L)).map (K1Nine D L).subtype := hcen hxA
  obtain ⟨z₀, hz₀center, hz₀⟩ := Subgroup.mem_map.mp hxcenter
  have hyK : (QuotientGroup.mk aD : Mbar9 D) ∈ K1Nine D L :=
    CFSG.Quasithin.mem_imageOTwoQuot_iff.mpr ⟨(y : G), hLM y.2, y.2, rfl⟩
  have hcomm : (QuotientGroup.mk aD : Mbar9 D) * (QuotientGroup.mk bD : Mbar9 D) =
      (QuotientGroup.mk bD : Mbar9 D) * (QuotientGroup.mk aD : Mbar9 D) := by
    let w : ↥(K1Nine D L) := ⟨(QuotientGroup.mk aD : Mbar9 D), hyK⟩
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz₀center w)
    change (QuotientGroup.mk aD : Mbar9 D) * (K1Nine D L).subtype z₀ =
        (K1Nine D L).subtype z₀ * (QuotientGroup.mk aD : Mbar9 D) at h1
    rw [hz₀] at h1
    exact h1
  have htriv : (QuotientGroup.mk (⁅aD, bD⁆ : ↥D.M) : Mbar9 D) = 1 := by
    change (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)) ⁅aD, bD⁆ = 1
    rw [map_commutatorElement]
    show (QuotientGroup.mk aD : Mbar9 D) * (QuotientGroup.mk bD : Mbar9 D) *
        (QuotientGroup.mk aD : Mbar9 D)⁻¹ * (QuotientGroup.mk bD : Mbar9 D)⁻¹ = 1
    rw [hcomm]
    group
  have hmemM' : ((⁅aD, bD⁆ : ↥D.M) : G) ∈ CFSG.Open.pCoreOf 2 D.M :=
    (CFSG.Quasithin.mk_eq_one_iff_mem_pCoreOf _).mp htriv
  have hmemL : ((⁅aD, bD⁆ : ↥D.M) : G) ∈ L := by
    rw [show ((⁅aD, bD⁆ : ↥D.M) : G) = ⁅(y : G), x⁆ by
      change Subgroup.subtype D.M ⁅aD, bD⁆ = ⁅(y : G), x⁆
      rw [map_commutatorElement]
      rfl]
    exact Subgroup.commutator_le_self L (Subgroup.commutator_mem_commutator y.2 hxL)
  have hmemL' : ((⁅aD, bD⁆ : ↥D.M) : G) ∈ CFSG.Open.pCoreOf 2 L :=
    (hPL ⟨_, hmemL⟩).mpr hmemM'
  have hcommEq : ((⁅aL, bL⁆ : ↥L) : G) = ((⁅aD, bD⁆ : ↥D.M) : G) := by
    change Subgroup.subtype L ⁅aL, bL⁆ = Subgroup.subtype D.M ⁅aD, bD⁆
    rw [map_commutatorElement, map_commutatorElement]
    rfl
  have hmemLL : (⁅aL, bL⁆ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [CFSG.Quasithin.C2Six.mem_pCore_two_iff, hcommEq]
    exact hmemL'
  have hq1 : (QuotientGroup.mk (⁅aL, bL⁆ : ↥L) : Bar2 L) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmemLL
  have hq2 : (QuotientGroup.mk (⁅aL, bL⁆ : ↥L) : Bar2 L) =
      (QuotientGroup.mk aL : Bar2 L) * (QuotientGroup.mk bL : Bar2 L) *
      (QuotientGroup.mk aL : Bar2 L)⁻¹ * (QuotientGroup.mk bL : Bar2 L)⁻¹ := by
    change (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)) ⁅aL, bL⁆ =
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)) aL *
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)) bL *
      ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)) aL)⁻¹ *
      ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)) bL)⁻¹
    rw [map_commutatorElement]
    rfl
  rw [hq2] at hq1
  exact mul_inv_eq_one.mp (by simpa [mul_assoc, mul_inv_rev] using hq1)

theorem exists_permutes_three_of_not_le_normalizer {D : Data G} {L X : Subgroup G}
    (hL : L ∈ calC D.M) (hNT : ¬ D.T ≤ Subgroup.normalizer (L : Set G))
    (hXL : X ≤ L) (hXcard : Nat.card X = 3)
    (hXnc : ¬ X ≤ (O2ZIn17 L).map L.subtype)
    (hperm : Permutes X (D.T ⊓ Subgroup.normalizer (L : Set G))) :
    ∃ X' : Subgroup G, X' ≤ D.M ∧ X' ≠ ⊥ ∧ IsPGroup 3 ↥X' ∧ (∀ x ∈ X', x ^ 3 = 1) ∧
      ¬ IsCyclic ↥X' ∧ Permutes X' D.T := by
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hXM : X ≤ D.M := hXL.trans hLM
  let A : Subgroup (Mbar9 D) := CFSG.Quasithin.imageOTwoQuot D.M X
  have hAK : A ≤ K1Nine D L := by
    exact CFSG.Quasithin.imageOTwoQuot_mono hXL
  have hAcard : Nat.card ↥A = 3 := by
    have h := CFSG.Quasithin.H13.L1444.card_eq_card_imageOTwoQuot_mul D.M X hXM
    have h2 : Nat.card ↥(X ⊓ CFSG.Open.pCoreOf 2 D.M) = 1 := by
      have hdvd : Nat.card ↥(X ⊓ CFSG.Open.pCoreOf 2 D.M) ∣ 3 := by
        rw [← hXcard]
        exact Subgroup.card_dvd_of_le inf_le_left
      have h2p : IsPGroup 2 ↥(X ⊓ CFSG.Open.pCoreOf 2 D.M) :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M).to_le inf_le_right
      obtain ⟨k, hk⟩ := h2p.exists_card_eq
      rw [hk] at hdvd ⊢
      have hk2 : k ≤ 1 := by
        by_contra hkk
        have h4 : 4 ≤ 2 ^ k := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hle : 2 ^ k ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
        omega
      interval_cases k
      · norm_num
      · norm_num at hdvd
    rw [hXcard, h2, mul_one] at h
    exact h.symm
  have hAne : A ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥A = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hAexp : ∀ a ∈ A, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨x, hxM, hxX, rfl⟩ := CFSG.Quasithin.mem_imageOTwoQuot_iff.mp ha
    have hx3 : x ^ 3 = 1 := by
      have hdvd : orderOf x ∣ 3 := by
        rw [← hXcard]
        exact Subgroup.orderOf_dvd_natCard X hxX
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · rw [orderOf_eq_one_iff.mp h1]
        simp
      · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [h3])
    calc (QuotientGroup.mk ⟨x, hxM⟩ : Mbar9 D) ^ 3
        = QuotientGroup.mk ((⟨x, hxM⟩ : ↥D.M) ^ 3) := by
          rw [← QuotientGroup.mk_pow]
      _ = QuotientGroup.mk 1 := by
          rw [show (⟨x, hxM⟩ : ↥D.M) ^ 3 = 1 from Subtype.ext (by simpa using hx3)]
      _ = 1 := by
          change (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)) (1 : ↥D.M) = 1
          exact map_one _
  have hAnc : ¬ A ≤ (Subgroup.center ↥(K1Nine D L)).map (K1Nine D L).subtype :=
    imageOTwoQuot_not_le_center_of_not_le_O2Z hL hXL hXnc
  have hYM : D.T ⊓ Subgroup.normalizer (L : Set G) ≤ D.M :=
    inf_le_left.trans D.sylowM.le
  have hpermM : ((X.subgroupOf D.M : Set ↥D.M) *
      ((D.T ⊓ Subgroup.normalizer (L : Set G)).subgroupOf D.M : Set ↥D.M) =
      ((D.T ⊓ Subgroup.normalizer (L : Set G)).subgroupOf D.M : Set ↥D.M) *
        (X.subgroupOf D.M : Set ↥D.M)) :=
    CFSG.Quasithin.H13.NQBlock.subgroupOf_mul_comm_of_mul_comm hXM hYM hperm
  have hAperm : Permutes A (S1Nine D L) := by
    have h1 := CFSG.GroupTheory.map_permutes_map
      (f := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)) hpermM
    have h2 : ((D.T ⊓ Subgroup.normalizer (L : Set G)).subgroupOf D.M).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)) = S1Nine D L :=
      imageOTwoQuot_inf_normalizer (D := D) (L := L) hL
    rw [show (X.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)) = A from rfl,
      h2] at h1
    exact h1
  have hKne : ∃ t ∈ Tbar9 D,
      (K1Nine D L).map (MulAut.conj t).toMonoidHom ≠ K1Nine D L := by
    by_contra h
    have hnorm : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)) := by
      intro t ht
      by_contra hne
      exact h ⟨t, ht, (Subgroup.mem_normalizer_iff_map_conj_eq).not.mp hne⟩
    exact hNT (le_normalizer_of_le_normalizer_imageOTwoQuot hL hnorm)
  obtain ⟨Xbar, hA_le_Xbar, hXbarT, hXbarExp, hXbarP, hXbarNcyc⟩ :=
    exists_noncyclic_permutes_sup_conj (H := Mbar9 D) (K := K1Nine D L) (T := Tbar9 D) (A := A)
      hAK (commute_of_ne_conj_K1Nine hL) hAperm hKne hAnc hAexp
  have hXbarNe : Xbar ≠ ⊥ := by
    intro hbot
    exact hAne (le_bot_iff.mp (hbot ▸ hA_le_Xbar))
  have hTsub2 : IsPGroup 2 (D.T.subgroupOf D.M) := D.sylowM.isPGroup.comap_subtype (K := D.M)
  have hker : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)).ker ≤ D.T.subgroupOf D.M := by
    rw [show (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)).ker = CFSG.Open.pCore 2 ↥D.M from
      QuotientGroup.ker_mk' _]
    exact Subgroup.map_le_iff_le_comap.mp (s16c7_pCoreOf_le_of_isSylowOf D.sylowM)
  have hSmap : (D.T.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)) =
      Tbar9 D := rfl
  have hAp : IsPGroup 3 ↥A :=
    IsPGroup.of_card (n := 1) (by rw [hAcard]; norm_num)
  obtain ⟨P, hP3, hPmap, ⟨eP⟩, hPperm⟩ :=
    CFSG.GroupTheory.exists_permutes_lift (p := 3)
      (f := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M))
      (QuotientGroup.mk'_surjective _) hTsub2 hker (by norm_num : (3 : ℕ) ≠ 2)
      (hXbarP 3 hAp) (by rw [hSmap]; exact hXbarT)
  refine ⟨P.map D.M.subtype, Subgroup.map_subtype_le P, ?_, hP3.map D.M.subtype, ?_, ?_, ?_⟩
  · intro hbot
    have hPbot : P = ⊥ := by
      refine Subgroup.map_injective (f := D.M.subtype) Subtype.val_injective ?_
      simpa using hbot
    have hcard : Nat.card Xbar = 1 := by
      have h := Nat.card_congr eP.toEquiv
      rw [hPbot, Subgroup.card_bot] at h
      exact h.symm
    exact hXbarNe ((Subgroup.card_eq_one).mp hcard)
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hy3 : (⟨y, hy⟩ : ↥P) ^ 3 = 1 := by
      apply eP.injective
      rw [map_pow, map_one]
      exact Subtype.ext (by simpa using hXbarExp 3 hAexp _ (eP ⟨y, hy⟩).2)
    simpa using congrArg (fun z : ↥P => ((z : ↥D.M) : G)) hy3
  · intro hcyc
    have hPcyc : IsCyclic ↥P := by
      let e := Subgroup.equivMapOfInjective P D.M.subtype Subtype.val_injective
      exact @isCyclic_of_surjective ↥P ↥(P.map D.M.subtype) _ _
        (↥(P.map D.M.subtype) ≃* ↥P) hcyc _ _ e.symm e.symm.surjective
    exact hXbarNcyc (@isCyclic_of_surjective ↥Xbar ↥P _ _ (↥P ≃* ↥Xbar) hPcyc _ _ eP
      eP.surjective)
  · have hDT : ((D.T.subgroupOf D.M).map D.M.subtype : Set G) = (D.T : Set G) :=
      congrArg (fun H : Subgroup G => (H : Set G)) (Subgroup.map_subgroupOf_eq_of_le D.sylowM.le)
    have hXcoe : (P.map D.M.subtype : Set G) = D.M.subtype '' (P : Set ↥D.M) := rfl
    have hScoe : ((D.T.subgroupOf D.M).map D.M.subtype : Set G) =
        D.M.subtype '' (D.T.subgroupOf D.M : Set ↥D.M) := rfl
    show ((P.map D.M.subtype : Subgroup G) : Set G) * (D.T : Set G) =
      (D.T : Set G) * ((P.map D.M.subtype : Subgroup G) : Set G)
    rw [hXcoe, ← hDT, hScoe, ← Set.image_mul, ← Set.image_mul, hPperm]

end OrbitProduct

theorem image_bar2_eq_top_of_formations (D : Data G) {L : Subgroup G} (h7 : IsL2Over17 (Bar2 L) 7)
    (hY : IsL2Over17 (Bar2 (L ⊔ D.T)) 7)
    (hsub : CFSG.Open.IsSubnormal L (L ⊔ D.T)) :
    ((L.subgroupOf (L ⊔ D.T)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ D.T)))) = ⊤ := by
  classical
  obtain ⟨r, f, hr, hr2, hq, hf, hmodel⟩ := hY
  have hsimple : IsSimpleGroup (Bar2 (L ⊔ D.T)) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hmodel
  have hLN : L ≤ L ⊔ D.T := le_sup_left
  have hsub' : (L.subgroupOf (L ⊔ D.T)).IsSubnormal :=
    (CFSG.Quasithin.isSubnormal_iff_subgroupOf hLN).mp hsub
  have hsubTop : CFSG.Open.IsSubnormal (L.subgroupOf (L ⊔ D.T)) ⊤ :=
    CFSG.Quasithin.A3.subnormal_top_iff.mpr hsub'
  have hPsubTop : CFSG.Open.IsSubnormal
      ((L.subgroupOf (L ⊔ D.T)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ D.T)))) ⊤ :=
    CFSG.Quasithin.A3.subnormal_top_map
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(L ⊔ D.T))) hsubTop
  have hPsub : Subgroup.IsSubnormal
      ((L.subgroupOf (L ⊔ D.T)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ D.T)))) :=
    CFSG.Quasithin.A3.subnormal_top_iff.mp hPsubTop
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimple hPsub with hP | hP
  · exfalso
    have hLleQ : L.subgroupOf (L ⊔ D.T) ≤ (QuotientGroup.mk'
        (CFSG.pCore 2 ↥(L ⊔ D.T))).ker := by
      intro x hx
      have hxP : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ D.T)))
          x ∈ ((L.subgroupOf (L ⊔ D.T)).map
            (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ D.T)))) :=
        Subgroup.mem_map_of_mem _ hx
      rw [hP] at hxP
      exact hxP
    have hLle : L.subgroupOf (L ⊔ D.T) ≤ CFSG.pCore 2 ↥(L ⊔ D.T) := by
      intro x hx
      exact (QuotientGroup.eq_one_iff x).mp (hLleQ hx)
    have hL2' : IsPGroup 2 (L.subgroupOf (L ⊔ D.T)) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2).to_le hLle
    have hL2 : IsPGroup 2 L := hL2'.of_equiv (Subgroup.subgroupOfEquivOfLe hLN)
    have hL2odd : IsL2Odd (Bar2 L) 7 := isL2Odd_seven_of_isL2Over17_seven h7
    have hcardBar : Nat.card (Bar2 L) = 168 := card_of_isL2Odd_seven hL2odd
    have h3 : 3 ∣ Nat.card ↥L := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (s := CFSG.pCore 2 ↥L)
      have hbar : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := hcardBar
      rw [hbar] at h
      exact ⟨56 * Nat.card (CFSG.pCore 2 ↥L), by rw [h]; ring⟩
    obtain ⟨k, hk⟩ := hL2.exists_card_eq
    rw [hk] at h3
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3
    norm_num at h32
  · exact hP

theorem exists_pair_of_bar2_l2 (D : Data G) {L : Subgroup G}
    (hL : L ∈ calC D.M) (h7 : IsL2Over17 (Bar2 L) 7)
    (hY : IsL2Over17 (Bar2 (L ⊔ D.T)) 7)
    (hKL0 : K_L27Local) :
    ∃ X₁ X₂ : Subgroup G, X₁ ≤ L ∧ X₂ ≤ L ∧ Nat.card X₁ = 3 ∧ Nat.card X₂ = 3 ∧
      Permutes X₁ D.T ∧ Permutes X₂ D.T ∧ L ≤ X₁ ⊔ X₂ ⊔ D.T := by
  classical
  let N : Subgroup G := L ⊔ D.T
  have hLN : L ≤ N := le_sup_left
  have hTN : D.T ≤ N := le_sup_right
  have hNM : N ≤ D.M := sup_le (CFSG.Quasithin.A3.subnormal_le hL.1) D.sylowM.le
  have hsub : CFSG.Open.IsSubnormal L N :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hL.1 hLN hNM
  have hPtop : ((L.subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N))) = ⊤ :=
    image_bar2_eq_top_of_formations D h7 (by simpa [N] using hY) hsub
  let π : ↥N →* Bar2 N := QuotientGroup.mk' (CFSG.pCore 2 ↥N)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  let S : Subgroup (Bar2 N) := (D.T.subgroupOf N).map π
  have hTsylG : CFSG.ABGLocalTools.IsSylowOf 2 D.T N := D.sylowM.of_le hTN hNM
  have hTsylN : CFSG.ABGLocalTools.IsSylowOf 2 (D.T.subgroupOf N) ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 2) N
      (A := D.T.subgroupOf N) (B := ⊤)).mp (by
      rw [Subgroup.map_subgroupOf_eq_of_le hTN, Subgroup.map_top, Subgroup.range_subtype]
      exact hTsylG)
  have hSin : CFSG.Quasithin.IsSylowIn 2 (D.T.subgroupOf N) ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_iff).mp hTsylN
  have hS : CFSG.Quasithin.IsSylowIn 2 S ⊤ :=
    CFSG.Quasithin.E1.isSylowIn_two_map_top hπsurj hSin
  let Q : Subgroup ↥N := CFSG.pCore 2 ↥N
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hQleT : Q ≤ D.T.subgroupOf N := by
    obtain ⟨Syl, hSyl⟩ := hTsylG.exists_sylow_eq_subgroupOf
    have hEq : (Syl : Subgroup ↥N) = D.T.subgroupOf N := by
      refine Subgroup.map_injective N.subtype_injective ?_
      rw [hSyl, Subgroup.map_subgroupOf_eq_of_le hTN]
    exact hEq ▸ hQ2.le_sylow_of_normal Syl
  have hL2odd : IsL2Odd (Bar2 N) 7 :=
    isL2Odd_seven_of_isL2Over17_seven (by simpa [N] using hY)
  have hKL : ∀ (Y : Type) [Group Y] [Finite Y], IsL2Odd Y 7 →
      ∀ S : Subgroup Y, CFSG.Quasithin.IsSylowIn 2 S ⊤ →
        (∃ X : Subgroup Y, Nat.card X = 3 ∧ Permutes X S ∧
          ¬ X ≤ Subgroup.center Y) ∧
        (∃ X₁ X₂ : Subgroup Y, Nat.card X₁ = 3 ∧ Nat.card X₂ = 3 ∧ X₁ ≠ X₂ ∧
          Permutes X₁ S ∧ Permutes X₂ S ∧ S ⊔ X₁ ⊔ X₂ = ⊤ ∧
          Nonempty (Bar2 (S ⊔ X₁) ≃* Equiv.Perm (Fin 3)) ∧
          Nonempty (Bar2 (S ⊔ X₂) ≃* Equiv.Perm (Fin 3))) := hKL0
  obtain ⟨-, X₁bar, X₂bar, hc1, hc2, hne, hp1, hp2, hsup, hq1, hq2⟩ :=
    hKL (Bar2 N) hL2odd S hS
  let g : ↥(L.subgroupOf N) →* Bar2 N := π.comp (L.subgroupOf N).subtype
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : y ∈ (L.subgroupOf N).map π := by rw [hPtop]; exact Subgroup.mem_top y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, hxy⟩
  have subgroupOf_map_subtype_eq : ∀ A : Subgroup ↥N, (A.map N.subtype).subgroupOf N = A := by
    intro A
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, hwz⟩
      rwa [N.subtype_injective hwz] at hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have lift_one : ∀ (Xbar : Subgroup (Bar2 N)), Nat.card Xbar = 3 → Permutes Xbar S →
      ∃ (XN : Subgroup ↥N) (X : Subgroup G), X = XN.map N.subtype ∧ XN ≤ L.subgroupOf N ∧
        Nat.card X = 3 ∧ Permutes X D.T ∧ XN.map π = Xbar := by
    intro Xbar hXc hperm
    let ψ : ↥(Xbar.comap g) →* ↥Xbar :=
      (g.comp (Xbar.comap g).subtype).codRestrict Xbar (fun x => x.2)
    have hψsurj : Function.Surjective ψ := by
      intro y
      obtain ⟨x, hx⟩ := hgsurj (y : Bar2 N)
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      rw [Subgroup.mem_comap]
      exact hx ▸ y.2
    have h3dvd : 3 ∣ Nat.card ↥(Xbar.comap g) := by
      have h := Subgroup.card_dvd_of_surjective hψsurj
      rwa [hXc] at h
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Xbar.comap g)) 3 h3dvd
    let XN : Subgroup ↥N :=
      (Subgroup.zpowers x).map ((L.subgroupOf N).subtype.comp (Xbar.comap g).subtype)
    let X : Subgroup G := XN.map N.subtype
    have hXNle : XN ≤ L.subgroupOf N := by
      rw [show XN = (Subgroup.zpowers x).map
          ((L.subgroupOf N).subtype.comp (Xbar.comap g).subtype) from rfl]
      refine Subgroup.map_le_iff_le_comap.mpr ?_
      intro y hy
      exact ((Xbar.comap g).subtype y).2
    have hXle : X ≤ L := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_subgroupOf.mp (hXNle hz)
    have hXcard : Nat.card X = 3 := by
      have hinj : Function.Injective
          (N.subtype.comp ((L.subgroupOf N).subtype.comp (Xbar.comap g).subtype)) :=
        N.subtype_injective.comp ((L.subgroupOf N).subtype_injective.comp
          (Xbar.comap g).subtype_injective)
      rw [show X = XN.map N.subtype from rfl,
        show XN = (Subgroup.zpowers x).map
          ((L.subgroupOf N).subtype.comp (Xbar.comap g).subtype) from rfl, Subgroup.map_map]
      rw [Subgroup.card_map_of_injective hinj, Nat.card_zpowers, hxord]
    have hXmap : XN.map π = Xbar := by
      rw [show XN = (Subgroup.zpowers x).map
          ((L.subgroupOf N).subtype.comp (Xbar.comap g).subtype) from rfl, Subgroup.map_map]
      have hcomp : π.comp ((L.subgroupOf N).subtype.comp (Xbar.comap g).subtype) =
          g.comp (Xbar.comap g).subtype := rfl
      rw [hcomp, MonoidHom.map_zpowers]
      change Subgroup.zpowers (g x) = Xbar
      have hgxmem : g (x : ↥(L.subgroupOf N)) ∈ Xbar := x.2
      have hxord' : orderOf (x : ↥(L.subgroupOf N)) = 3 := by
        rw [Subgroup.orderOf_coe, hxord]
      have hord : orderOf (g (x : ↥(L.subgroupOf N))) = 3 := by
        have hdvd : orderOf (g (x : ↥(L.subgroupOf N))) ∣ 3 := by
          rw [← hxord']
          exact orderOf_map_dvd g (x : ↥(L.subgroupOf N))
        have hne1 : orderOf (g (x : ↥(L.subgroupOf N))) ≠ 1 := by
          intro h1
          have hxker : (x : ↥(L.subgroupOf N)) ∈ g.ker := by
            rw [MonoidHom.mem_ker]
            exact orderOf_eq_one_iff.mp h1
          have hker2 : IsPGroup 2 g.ker := by
            let κ : ↥g.ker →* ↥Q :=
              { toFun := fun y => ⟨((y : ↥(L.subgroupOf N)) : ↥N), by
                  have hy : g (y : ↥(L.subgroupOf N)) = 1 := y.2
                  exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥N)
                    (((y : ↥(L.subgroupOf N)) : ↥N))).mp hy⟩
                map_one' := Subtype.ext rfl
                map_mul' := fun a b => Subtype.ext rfl }
            have hκ : Function.Injective κ := by
              intro a b hab
              exact Subtype.ext (Subtype.val_injective (by
                simpa [κ] using congrArg (fun z : ↥Q => (z : ↥N)) hab))
            exact IsPGroup.of_injective hQ2 κ hκ
          have h3ker : 3 ∣ Nat.card ↥g.ker := by
            rw [← hxord']
            exact Subgroup.orderOf_dvd_natCard g.ker hxker
          obtain ⟨k, hk⟩ := hker2.exists_card_eq
          rw [hk] at h3ker
          have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3ker
          norm_num at h32
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · exact absurd h1 hne1
        · exact h3
      have hcardz : Nat.card (Subgroup.zpowers (g (x : ↥(L.subgroupOf N)))) = 3 := by
        rw [Nat.card_zpowers, hord]
      exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgxmem) (by
        rw [hcardz, hXc])
    have hpermN : Permutes XN (D.T.subgroupOf N) := by
      refine CFSG.GroupTheory.permutes_of_map_permutes π (by
        simpa [π, Q, QuotientGroup.ker_mk'] using hQleT) ?_
      rw [hXmap]
      change (Xbar : Set (Bar2 N)) * (S : Set (Bar2 N)) =
        (S : Set (Bar2 N)) * (Xbar : Set (Bar2 N))
      exact hperm
    have hpermG : Permutes X D.T := by
      have h1 := CFSG.GroupTheory.map_permutes_map N.subtype hpermN
      rwa [show XN.map N.subtype = X from rfl,
        Subgroup.map_subgroupOf_eq_of_le hTN] at h1
    exact ⟨XN, X, rfl, hXNle, hXcard, hpermG, hXmap⟩
  obtain ⟨XN₁, X₁, hX₁eq, hXN₁le, hX₁c, hperm₁, hX₁map⟩ := lift_one X₁bar hc1 hp1
  obtain ⟨XN₂, X₂, hX₂eq, hXN₂le, hX₂c, hperm₂, hX₂map⟩ := lift_one X₂bar hc2 hp2
  refine ⟨X₁, X₂, ?_, ?_, hX₁c, hX₂c, hperm₁, hperm₂, ?_⟩
  · intro y hy
    rw [hX₁eq] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_subgroupOf.mp (hXN₁le hz)
  · intro y hy
    rw [hX₂eq] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_subgroupOf.mp (hXN₂le hz)
  · have hX₁N : X₁ ≤ N := by rw [hX₁eq]; exact Subgroup.map_subtype_le _
    have hX₂N : X₂ ≤ N := by rw [hX₂eq]; exact Subgroup.map_subtype_le _
    have hsub₁ : X₁.subgroupOf N = XN₁ := by rw [hX₁eq, subgroupOf_map_subtype_eq]
    have hsub₂ : X₂.subgroupOf N = XN₂ := by rw [hX₂eq, subgroupOf_map_subtype_eq]
    have himageTop : ((X₁ ⊔ X₂ ⊔ D.T).subgroupOf N).map π = ⊤ := by
      rw [Subgroup.subgroupOf_sup (sup_le hX₁N hX₂N) hTN,
        Subgroup.subgroupOf_sup hX₁N hX₂N,
        Subgroup.map_sup, Subgroup.map_sup, hsub₁, hsub₂, hX₁map, hX₂map]
      change X₁bar ⊔ X₂bar ⊔ S = ⊤
      rw [sup_comm (X₁bar ⊔ X₂bar) S, ← sup_assoc]
      exact hsup
    intro l hl
    have hlN : l ∈ N := hLN hl
    have hmem : π ⟨l, hlN⟩ ∈ ((X₁ ⊔ X₂ ⊔ D.T).subgroupOf N).map π := by
      rw [himageTop]
      exact Subgroup.mem_top _
    obtain ⟨h, hh, hq⟩ := Subgroup.mem_map.mp hmem
    have hqker : (⟨l, hlN⟩ : ↥N) * h⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hq, mul_inv_cancel]
    have hqQ : (⟨l, hlN⟩ : ↥N) * h⁻¹ ∈ Q := by
      simpa [Q, π, QuotientGroup.ker_mk'] using hqker
    have hqle : (⟨l, hlN⟩ : ↥N) * h⁻¹ ∈ D.T.subgroupOf N := hQleT hqQ
    have hl_eq : l = ((⟨l, hlN⟩ : ↥N) * h⁻¹ : ↥N) * h := by
      have h1 : (⟨l, hlN⟩ : ↥N) = ((⟨l, hlN⟩ : ↥N) * h⁻¹) * h := by group
      exact congrArg (fun z : ↥N => (z : G)) h1
    rw [hl_eq]
    have hhH : (h : G) ∈ X₁ ⊔ X₂ ⊔ D.T := by
      simpa using (Subgroup.mem_subgroupOf.mp hh)
    have hqH : (((⟨l, hlN⟩ : ↥N) * h⁻¹ : ↥N) : G) ∈ X₁ ⊔ X₂ ⊔ D.T :=
      Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hqle)
    exact Subgroup.mul_mem _ hqH hhH

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
