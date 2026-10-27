module

public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Centres
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42ClassUt

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

theorem mem_centerIn_J_of_fixDimV_eq_zero (h : Tim79a.ParrottHyp z) {σ : ↥(H z)}
    (hdim : fixDimV h σ = 0) {j : G} (hj : j ∈ J z) (hσj : (σ : G) * j * (σ : G)⁻¹ = j) :
    j ∈ centerIn (J z) := by
  have hfix : QuotientV.pi z ⟨j, hj⟩ ∈ autFixedSubgroup (conjV h σ) := by
    rw [mem_autFixedSubgroup, conjV_mk]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    exact hσj
  have hcard : Nat.card (autFixedSubgroup (conjV h σ)) = 1 := by
    rw [card_fix h σ, hdim, pow_zero]
  rw [Subgroup.card_eq_one.mp hcard, Subgroup.mem_bot] at hfix
  exact (pi_eq_one_iff_mem_centerIn hj).mp hfix

section Certified

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "bA" => (⟨beta, beta_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)

private theorem orderOf_uA_mul_tA : orderOf (uA * tA) = 2 := by
  have hA : Nat.card A45 = 51840 := card_QA45
  obtain ⟨hC1, hC2, hC3, hC4⟩ := qa45_involution_centralizers
  have hut1 : uA * tA ≠ 1 :=
    CFSG.GroupTheory.ne_one_of_card_centralizer_ne (by rw [hC2, hA]; omega)
  have hut2 : (uA * tA) * (uA * tA) = 1 := by
    have hcomm : Commute tA uA := Subtype.ext t_commute_u
    have htt : tA * tA = 1 := Subtype.ext t_sq
    have huu : uA * uA = 1 := Subtype.ext u_sq
    rw [Commute.mul_mul_mul_comm hcomm uA tA, huu, htt, one_mul]
  exact orderOf_eq_prime (by rw [pow_two]; exact hut2) hut1

theorem exists_order_four_mem_sylow_d8 :
    ∃ a₀ ∈ Subgroup.closure ({tA, uA, vA * bA} : Set A45), a₀ * a₀ * (a₀ * a₀) = 1 ∧
      a₀ * a₀ = uA * tA ∧
      ∀ x ∈ Subgroup.closure ({tA, uA, vA * bA} : Set A45),
        x * a₀ * x⁻¹ = a₀ ∨ x * a₀ * x⁻¹ = a₀⁻¹ := by
  obtain ⟨-, -, hle3, hcard3, ⟨e⟩, hcen3⟩ := qa45_sigma_centralizer_sylow
  set S : Subgroup A45 := Subgroup.closure ({tA, uA, vA * bA} : Set A45) with hS
  let a₀' : ↥S := e.symm (DihedralGroup.r 1)
  have hsq : ∀ y : DihedralGroup 4, y * DihedralGroup.r 1 * y⁻¹ = DihedralGroup.r 1 ∨
      y * DihedralGroup.r 1 * y⁻¹ = (DihedralGroup.r 1)⁻¹ := by decide +kernel
  have hcentr : ∀ y : DihedralGroup 4,
      y * (DihedralGroup.r 1 * DihedralGroup.r 1) =
        (DihedralGroup.r 1 * DihedralGroup.r 1) * y := by
    decide +kernel
  have hfour : (DihedralGroup.r 1 * DihedralGroup.r 1) *
      (DihedralGroup.r 1 * DihedralGroup.r 1 : DihedralGroup 4) = 1 := by decide +kernel
  have hne : (DihedralGroup.r 1 * DihedralGroup.r 1 : DihedralGroup 4) ≠ 1 := by decide +kernel
  have h4 : a₀' * a₀' * (a₀' * a₀') = 1 := by
    apply e.injective
    simp only [a₀', map_mul, MulEquiv.apply_symm_apply, map_one]
    exact hfour
  have hcen : ((a₀' * a₀' : ↥S) : A45) ∈ (Subgroup.center ↥S).map S.subtype := by
    refine ⟨a₀' * a₀', Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    apply e.injective
    simp only [a₀', map_mul, MulEquiv.apply_symm_apply]
    exact hcentr (e g)
  rw [hcen3] at hcen
  have hsq1 : a₀' * a₀' ≠ 1 := by
    intro h1
    apply hne
    have := congrArg e h1
    simpa [a₀'] using this
  have hut : ((a₀' * a₀' : ↥S) : A45) = uA * tA := by
    rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two orderOf_uA_mul_tA hcen with h1 | h1
    · exact absurd (Subtype.ext h1) hsq1
    · exact h1
  refine ⟨a₀', a₀'.2, congrArg Subtype.val h4, hut, fun x hx => ?_⟩
  have h1 := hsq (e ⟨x, hx⟩)
  rcases h1 with h1 | h1
  · left
    have : (⟨x, hx⟩ : ↥S) * a₀' * (⟨x, hx⟩ : ↥S)⁻¹ = a₀' := by
      apply e.injective
      simp only [a₀', map_mul, map_inv, MulEquiv.apply_symm_apply] at h1 ⊢
      exact h1
    exact congrArg Subtype.val this
  · right
    have : (⟨x, hx⟩ : ↥S) * a₀' * (⟨x, hx⟩ : ↥S)⁻¹ = a₀'⁻¹ := by
      apply e.injective
      simp only [a₀', map_mul, map_inv, MulEquiv.apply_symm_apply] at h1 ⊢
      exact h1
    exact congrArg Subtype.val this

theorem exists_involution_mem_centre_of_involution_ut (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {T : Subgroup G}
    (hT : IsSylowOf 2 T
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G)))
    {y : G} (hy : y ∈ H z) (hyy : y * y = 1) (hyc : IsConj (qH D ⟨y, hy⟩) (uA * tA)) :
    Nat.card ↥(T ⊓ centralizer (T : Set G)) = 8 ∧
      ∃ s ∈ T ⊓ centralizer (T : Set G), s ∉ J z ∧ s * s = 1 ∧
        ∃ hs : s ∈ H z, IsConj (qH D ⟨s, hs⟩) (uA * tA) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set τ : ↥(H z) := sigma1Nine (z := z) D * σ₂ with hτ
  have hτ3 : orderOf τ = 3 := by
    rw [← Subgroup.orderOf_coe τ]
    exact orderOf_sigma1Nine_mul (z := z) D h hσ₂ hq₂ hc₂
  have hqτ : qH D τ = s1A * s2A := by rw [hτ, map_mul, qH_sigma1Nine, hq₂]
  have hE27 := e27LineCountData_of_not_equalityBranch D h hIII hσ₂ hq₂ hc₂
  have hdimτ : fixDimV h τ = 0 :=
    fixDimV_sigma1Nine_mul_sigma2_eq_zero_of_not_equalityBranch D h hIII hσ₂ hq₂ hc₂ hE27
  obtain ⟨P, -, hP⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h D).mp
    (generatorConjugacy_of_not_equalityBranch h D hIII)
  have hP' : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹ := fun a => by
    simpa [rhoA, toQAct] using hP a
  have hV1 := fixDimV_eq_four_of_conj_rep D h rhoA P hP' (fun a ha => spinFixedCard_ut a ha)
  have hTH : T ≤ H z := hT.le.trans inf_le_left
  have hTτ : T ≤ centralizer ({(τ : G)} : Set G) := hT.le.trans inf_le_right
  have hTJ : ∀ j ∈ T, j ∈ J z → j ∈ centerIn (J z) := fun j hjT hjJ =>
    mem_centerIn_J_of_fixDimV_eq_zero h hdimτ hjJ (by
      have h1 : j * (τ : G) = (τ : G) * j := mem_centralizer_singleton_iff.mp (hTτ hjT)
      calc (τ : G) * j * (τ : G)⁻¹ = (j * (τ : G)) * (τ : G)⁻¹ := by rw [h1]
        _ = j := by group)
  have hut2 : (uA * tA) * (uA * tA) = 1 := by
    have h1 := pow_orderOf_eq_one (uA * tA)
    rwa [orderOf_uA_mul_tA, pow_two] at h1
  have hut1 : uA * tA ≠ 1 := fun h1 => by
    have := orderOf_uA_mul_tA
    rw [h1, orderOf_one] at this
    omega
  have hTbar := isSylowOf_map_qH_centralizer D hτ3 hT
  rw [hqτ] at hTbar
  obtain ⟨c, hc, hcx⟩ := isSylowOf_d8_centralizer_sigma1_mul.exists_mem_conj hTbar
  obtain ⟨a₀, ha₀S, ha₀4, ha₀sq, ha₀conj⟩ := exists_order_four_mem_sylow_d8
  have hāmem : c * a₀ * c⁻¹ ∈ (T.subgroupOf (H z)).map (qH D) := by
    rw [hcx]
    have : c⁻¹ * (c * a₀ * c⁻¹) * c = a₀ := by group
    rw [this]
    exact ha₀S
  obtain ⟨ã, hãT, hãq⟩ := hāmem
  have haT : (ã : G) ∈ T := hãT
  have haH : (ã : G) ∈ H z := ã.2
  have hāsq : qH D (ã * ã) = c * (uA * tA) * c⁻¹ := by
    rw [map_mul, hãq, ← ha₀sq]
    group
  have hāfour : qH D (ã * ã * (ã * ã)) = 1 := by
    rw [map_mul, hāsq]
    calc c * (uA * tA) * c⁻¹ * (c * (uA * tA) * c⁻¹) = c * ((uA * tA) * (uA * tA)) * c⁻¹ := by
          group
      _ = 1 := by rw [hut2]; group
  have h4J : (ã : G) * ã * ((ã : G) * ã) ∈ J z := (J_mem_iff D (ã * ã * (ã * ã))).mpr hāfour
  have h4T : (ã : G) * ã * ((ã : G) * ã) ∈ T :=
    T.mul_mem (T.mul_mem haT haT) (T.mul_mem haT haT)
  have h4Z := hTJ _ h4T h4J
  have hycl : IsConj (qH D ⟨y, hy⟩) (qH D (ã * ã)) := by
    rw [hāsq]
    exact hyc.trans (isConj_iff.mpr ⟨c, rfl⟩)
  obtain ⟨d, hd⟩ := isConj_iff.mp hycl
  obtain ⟨g', rfl⟩ := qH_surjective D d
  set y' : G := (g' : G) * y * (g' : G)⁻¹ with hy'
  have hy'H : y' ∈ H z := (H z).mul_mem ((H z).mul_mem g'.2 hy) ((H z).inv_mem g'.2)
  have hy'y' : y' * y' = 1 := by
    calc y' * y' = (g' : G) * (y * y) * (g' : G)⁻¹ := by simp only [hy']; group
      _ = 1 := by rw [hyy]; group
  have hqy' : qH D ⟨y', hy'H⟩ = qH D (ã * ã) := by
    have h1 : (⟨y', hy'H⟩ : ↥(H z)) = g' * ⟨y, hy⟩ * g'⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact hd
  have hcos : ((ã * ã : ↥(H z)) : G)⁻¹ * y' ∈ J z := by
    have h1 : qH D ((ã * ã)⁻¹ * ⟨y', hy'H⟩) = 1 := by
      rw [map_mul, map_inv, hqy', inv_mul_cancel]
    exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr h1)
  have hdim4 : fixDimV h (ã * ã) = 4 := hV1 _ (by
    rw [hāsq]
    exact isConj_iff.mpr ⟨c⁻¹, by group⟩)
  have hmain := mul_self_eq_of_fixDimV_eq_four h hZ (ã * ã).2 hcos hdim4
    (by simpa using h4Z) (hy'y' ▸ (centerIn (J z)).one_mem)
  have hsq1 : (ã : G) * ã * ((ã : G) * ã) = 1 := by
    simpa [hy'y'] using hmain
  have hcentral : ∀ t' ∈ T, t' * ((ã : G) * ã) = ((ã : G) * ã) * t' := by
    intro t' ht'
    have ht'H : t' ∈ H z := hTH ht'
    have hmemT' : qH D ⟨t', ht'H⟩ ∈ (T.subgroupOf (H z)).map (qH D) :=
      ⟨⟨t', ht'H⟩, ht', rfl⟩
    have h1 := ha₀conj (c⁻¹ * qH D ⟨t', ht'H⟩ * c) ((hcx _).mp hmemT')
    have h2 : qH D ⟨t', ht'H⟩ * qH D ã * (qH D ⟨t', ht'H⟩)⁻¹ = qH D ã ∨
        qH D ⟨t', ht'H⟩ * qH D ã * (qH D ⟨t', ht'H⟩)⁻¹ = (qH D ã)⁻¹ := by
      rw [hãq]
      rcases h1 with h1 | h1
      · left
        calc qH D ⟨t', ht'H⟩ * (c * a₀ * c⁻¹) * (qH D ⟨t', ht'H⟩)⁻¹
            = c * ((c⁻¹ * qH D ⟨t', ht'H⟩ * c) * a₀ * (c⁻¹ * qH D ⟨t', ht'H⟩ * c)⁻¹) * c⁻¹ := by
              group
          _ = c * a₀ * c⁻¹ := by rw [h1]
      · right
        calc qH D ⟨t', ht'H⟩ * (c * a₀ * c⁻¹) * (qH D ⟨t', ht'H⟩)⁻¹
            = c * ((c⁻¹ * qH D ⟨t', ht'H⟩ * c) * a₀ * (c⁻¹ * qH D ⟨t', ht'H⟩ * c)⁻¹) * c⁻¹ := by
              group
          _ = c * a₀⁻¹ * c⁻¹ := by rw [h1]
          _ = (c * a₀ * c⁻¹)⁻¹ := by group
    have hcentZ : ∀ e ∈ centerIn (J z), e * (ã : G) = (ã : G) * e := fun e he =>
      (mem_centralizer_iff.mp ((hZ ▸ he : e ∈ centerIn (H z))).2 (ã : G) haH).symm
    have hsqZ : ∀ e ∈ centerIn (J z), e * e = 1 := fun e he => centerIn_J_sq h he
    have ht'a : (t' * (ã : G) * t'⁻¹) ∈ T := T.mul_mem (T.mul_mem ht' haT) (T.inv_mem ht')
    rcases h2 with h2 | h2
    ·
      have hqe : qH D (ã⁻¹ * (⟨t', ht'H⟩ * ã * ⟨t', ht'H⟩⁻¹)) = 1 := by
        simp only [map_mul, map_inv]
        rw [h2]
        group
      have heJ : (ã : G)⁻¹ * (t' * (ã : G) * t'⁻¹) ∈ J z :=
        (J_mem_iff D _).mpr hqe
      have heT : (ã : G)⁻¹ * (t' * (ã : G) * t'⁻¹) ∈ T := T.mul_mem (T.inv_mem haT) ht'a
      have heZ := hTJ _ heT heJ
      set e : G := (ã : G)⁻¹ * (t' * (ã : G) * t'⁻¹) with he
      have hta : t' * (ã : G) * t'⁻¹ = (ã : G) * e := by rw [he]; group
      have : t' * ((ã : G) * ã) * t'⁻¹ = (ã : G) * ã := by
        calc t' * ((ã : G) * ã) * t'⁻¹ = (t' * (ã : G) * t'⁻¹) * (t' * (ã : G) * t'⁻¹) := by group
          _ = ((ã : G) * e) * ((ã : G) * e) := by rw [hta]
          _ = (ã : G) * (e * (ã : G)) * e := by group
          _ = (ã : G) * ((ã : G) * e) * e := by rw [hcentZ e heZ]
          _ = (ã : G) * ã * (e * e) := by group
          _ = (ã : G) * ã := by rw [hsqZ e heZ]; group
      calc t' * ((ã : G) * ã) = (t' * ((ã : G) * ã) * t'⁻¹) * t' := by group
        _ = ((ã : G) * ã) * t' := by rw [this]
    ·
      have hqe : qH D (ã * (⟨t', ht'H⟩ * ã * ⟨t', ht'H⟩⁻¹)) = 1 := by
        simp only [map_mul, map_inv] at h2 ⊢
        rw [h2]
        group
      have heJ : (ã : G) * (t' * (ã : G) * t'⁻¹) ∈ J z := (J_mem_iff D _).mpr hqe
      have heT : (ã : G) * (t' * (ã : G) * t'⁻¹) ∈ T := T.mul_mem haT ht'a
      have heZ := hTJ _ heT heJ
      set e : G := (ã : G) * (t' * (ã : G) * t'⁻¹) with he
      have hta : t' * (ã : G) * t'⁻¹ = (ã : G)⁻¹ * e := by rw [he]; group
      have hcentZ' : e * (ã : G)⁻¹ = (ã : G)⁻¹ * e := by
        have := hcentZ e heZ
        calc e * (ã : G)⁻¹ = (ã : G)⁻¹ * ((ã : G) * e) * (ã : G)⁻¹ := by group
          _ = (ã : G)⁻¹ * (e * (ã : G)) * (ã : G)⁻¹ := by rw [this]
          _ = (ã : G)⁻¹ * e := by group
      have hinv : ((ã : G) * ã)⁻¹ = (ã : G) * ã := inv_eq_of_mul_eq_one_right hsq1
      have : t' * ((ã : G) * ã) * t'⁻¹ = (ã : G) * ã := by
        calc t' * ((ã : G) * ã) * t'⁻¹ = (t' * (ã : G) * t'⁻¹) * (t' * (ã : G) * t'⁻¹) := by group
          _ = ((ã : G)⁻¹ * e) * ((ã : G)⁻¹ * e) := by rw [hta]
          _ = (ã : G)⁻¹ * (e * (ã : G)⁻¹) * e := by group
          _ = (ã : G)⁻¹ * ((ã : G)⁻¹ * e) * e := by rw [hcentZ']
          _ = ((ã : G) * ã)⁻¹ * (e * e) := by group
          _ = (ã : G) * ã := by rw [hsqZ e heZ, hinv]; group
      calc t' * ((ã : G) * ã) = (t' * ((ã : G) * ã) * t'⁻¹) * t' := by group
        _ = ((ã : G) * ã) * t' := by rw [this]
  have hsmem : (ã : G) * ã ∈ T ⊓ centralizer (T : Set G) :=
    mem_inf.mpr ⟨T.mul_mem haT haT, mem_centralizer_iff.mpr fun t' ht' => hcentral t' ht'⟩
  have hsH : (ã : G) * ã ∈ H z := (H z).mul_mem haH haH
  have hsq : qH D (ã * ã) ≠ 1 := by
    rw [hāsq]
    intro h1
    apply hut1
    have : uA * tA = c⁻¹ * (c * (uA * tA) * c⁻¹) * c := by group
    rw [this, h1]
    group
  have hsJ : (ã : G) * ã ∉ J z := fun hJ => hsq ((J_mem_iff D (ã * ã)).mp hJ)
  have hcard := card_centre_sylow_sigma1_mul D h hZ hσ₂ hq₂ hc₂ hT
  have hZW := centerIn_J_le_inf_centralizer_of_isSylowOf h hZ
    (centerIn_J_le_centralizer_of_mem_H hZ τ.2) hT
  refine ⟨?_, (ã : G) * ã, hsmem, hsJ, ?_, hsH, ?_⟩
  · rcases hcard with h4 | h8
    · exfalso
      have heq : centerIn (J z) = T ⊓ centralizer (T : Set G) :=
        Subgroup.eq_of_le_of_card_ge hZW (by rw [h4, card_centerIn_J h])
      exact hsJ (heq ▸ hsmem : (ã : G) * ã ∈ centerIn (J z)).1
    · exact h8
  · have h1 := hsq1
    simpa [mul_assoc] using h1
  · rw [show (⟨(ã : G) * ã, hsH⟩ : ↥(H z)) = ã * ã from rfl, hāsq]
    exact isConj_iff.mpr ⟨c⁻¹, by group⟩

theorem not_isConj_of_class_ut_of_spin (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    (A0 : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) :
    ∀ (y : G) (hy : y ∈ H z), orderOf y = 2 → IsConj (qH D ⟨y, hy⟩) (uA * tA) →
      ¬ IsConj z y := by
  intro y hy hy2 hyc hconj
  have hyy : y * y = 1 := by
    have h1 := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h1
  obtain ⟨σ₂, hσ₂, hq₂, hc₂⟩ := exists_commuting_order_three_lift_sigma2 (z := z) D h
  set τ : ↥(H z) := sigma1Nine (z := z) D * σ₂ with hτ
  have hτ3' : orderOf (τ : G) = 3 := orderOf_sigma1Nine_mul D h hσ₂ hq₂ hc₂
  have hτ3 : orderOf τ = 3 := (Subgroup.orderOf_coe τ).symm.trans hτ3'
  obtain ⟨P, -, hP⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h D).mp
    (generatorConjugacy_of_not_equalityBranch h D hIII)
  have hP' : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹ := fun a => by
    simpa [rhoA, toQAct] using hP a
  have hV1 := fixDimV_eq_four_of_conj_rep D h rhoA P hP' (fun a ha => spinFixedCard_ut a ha)
  have hstar := star_of_card_three_of_spin D h hZ hIII A0
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (H z ⊓ centralizer ({(τ : G)} : Set G))
  obtain ⟨hT8, s, hsW, hsJ, hss, hsH, hsq⟩ :=
    exists_involution_mem_centre_of_involution_ut D h hZ hIII hσ₂ hq₂ hc₂ hT hy hyy hyc
  have hZW := centerIn_J_le_inf_centralizer_of_isSylowOf h hZ
    (centerIn_J_le_centralizer_of_mem_H hZ τ.2) hT
  have hPcard : Nat.card (Subgroup.zpowers (τ : G)) = 3 := by
    rw [Nat.card_zpowers, hτ3']
  have hstarP := hstar _ (Subgroup.zpowers_le.mpr τ.2) hPcard
  obtain ⟨c, hc⟩ := isConj_iff.mp (hyc.trans hsq.symm)
  obtain ⟨g', rfl⟩ := qH_surjective D c
  set y' : G := (g' : G) * y * (g' : G)⁻¹ with hy'
  have hy'H : y' ∈ H z := (H z).mul_mem ((H z).mul_mem g'.2 hy) ((H z).inv_mem g'.2)
  have hy'y' : y' * y' = 1 := by
    calc y' * y' = (g' : G) * (y * y) * (g' : G)⁻¹ := by simp only [hy']; group
      _ = 1 := by rw [hyy]; group
  have hqy' : qH D ⟨y', hy'H⟩ = qH D ⟨s, hsH⟩ := by
    have h1 : (⟨y', hy'H⟩ : ↥(H z)) = g' * ⟨y, hy⟩ * g'⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact hc
  have hcos : s⁻¹ * y' ∈ J z := by
    have h1 : qH D ((⟨s, hsH⟩ : ↥(H z))⁻¹ * ⟨y', hy'H⟩) = 1 := by
      rw [map_mul, map_inv, hqy', inv_mul_cancel]
    exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr h1)
  obtain ⟨k, hkJ, e, he, hke⟩ := exists_conj_mul_centerIn_of_fixDimV_eq_four h hsH hcos
    (hV1 _ hsq) (hss ▸ (centerIn (J z)).one_mem) (hy'y' ▸ (centerIn (J z)).one_mem)
  have hseW : s * e ∈ T ⊓ centralizer (T : Set G) := (T ⊓ centralizer (T : Set G)).mul_mem hsW
    (hZW he)
  have hconjw : IsConj z (s * e) := by
    obtain ⟨c₀, hc₀⟩ := isConj_iff.mp hconj
    refine isConj_iff.mpr ⟨k * ((g' : G) * c₀), ?_⟩
    rw [← hke, hy', ← hc₀]
    group
  have hsez := eq_of_isConj_of_mem_centre_sylowTwo h hZ Nat.prime_three (by norm_num) τ.2 hτ3'
    hstarP hT hT8 A0 hseW hconjw
  apply hsJ
  have hs' : s = z * e⁻¹ := by rw [← hsez]; group
  rw [hs']
  exact Subgroup.mul_mem _ (z_mem_J h) (Subgroup.inv_mem _ (he.1))


end Certified

end CFSG.RankThree.GF2n.Parrott
