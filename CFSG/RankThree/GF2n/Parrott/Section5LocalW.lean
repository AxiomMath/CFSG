module

public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardW
public import CFSG.RankThree.GF2n.Parrott.SpinBridge
public import CFSG.RankThree.GF2n.Parrott.Section5LocalT23
public import CFSG.RankThree.GF2n.Parrott.Section5LocalT
public import CFSG.RankThree.GF2n.Parrott.Lemma16
public import CFSG.RankThree.GF2n.Parrott.OddLiftCentralizer

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def lemma54W (z σ t : G) : Subgroup G :=
  (J z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({t} : Set G)) ⊔ Subgroup.zpowers t

variable {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

@[expose] noncomputable def lemma54T₂ (σ : G) : Subgroup G :=
  H z ⊓ centralizer ({σ} : Set G) ⊓
    ((Subgroup.closure ({tA, uA * vA} : Set A45)).comap (qH (z := z) D)).map (H z).subtype

private theorem lemma54W_pow_two_eq_one_or {τ b : G} (hτ : τ * τ = 1)
    (hb : b ∈ Subgroup.zpowers τ) : b = 1 ∨ b = τ := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have h2 : τ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hτ
  have hper : τ ^ n = τ ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
    rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · rw [hper, h0]; simp
  · rw [hper, h1]; simp

theorem mem_lemma54W_iff_of_mem_J {σ τ : G} (hτ : τ * τ = 1) (hτJ : τ ∉ J z) {x : G}
    (hx : x ∈ J z) :
    x ∈ lemma54W z σ τ ↔ x ∈ centralizer ({σ} : Set G) ∧ x ∈ centralizer ({τ} : Set G) := by
  have hcomm : ∀ a ∈ J z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({τ} : Set G),
      ∀ b ∈ Subgroup.zpowers τ, Commute a b := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (show Commute a τ from Subgroup.mem_centralizer_singleton_iff.mp ha.2).zpow_right k
  rw [lemma54W, CFSG.mem_sup_of_commute hcomm]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨ha₁, haτ⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨haJ, haσ⟩ := Subgroup.mem_inf.mp ha₁
    have hbJ : b ∈ J z := by
      have hb' : b = a⁻¹ * (a * b) := by group
      rw [hb']
      exact (J z).mul_mem ((J z).inv_mem haJ) hx
    rcases lemma54W_pow_two_eq_one_or hτ hb with h | h
    · rw [h, mul_one]
      exact ⟨haσ, haτ⟩
    · rw [h] at hbJ
      exact absurd hbJ hτJ
  · rintro ⟨hσ, hτx⟩
    exact ⟨x, Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hx, hσ⟩, hτx⟩, 1,
      Subgroup.one_mem _, mul_one x⟩

theorem mem_lemma54W_iff {σ τ : G} (hτ : τ * τ = 1) {x : G} :
    x ∈ lemma54W z σ τ ↔
      x ∈ J z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({τ} : Set G) ∨
        τ * x ∈ J z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({τ} : Set G) := by
  have hcomm : ∀ a ∈ J z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({τ} : Set G),
      ∀ b ∈ Subgroup.zpowers τ, Commute a b := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (show Commute a τ from Subgroup.mem_centralizer_singleton_iff.mp ha.2).zpow_right k
  rw [lemma54W, CFSG.mem_sup_of_commute hcomm]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨-, haτ⟩ := Subgroup.mem_inf.mp ha
    rcases lemma54W_pow_two_eq_one_or hτ hb with h | h
    · left
      rw [h, mul_one]
      exact ha
    · right
      rw [h]
      have hgoal : τ * (a * τ) = a := by
        calc τ * (a * τ) = (τ * a) * τ := by rw [mul_assoc]
          _ = (a * τ) * τ := by rw [Subgroup.mem_centralizer_singleton_iff.mp haτ]
          _ = a := by rw [mul_assoc, hτ, mul_one]
      rw [hgoal]
      exact ha
  · rintro (h | h)
    · exact ⟨x, h, 1, Subgroup.one_mem _, mul_one x⟩
    · refine ⟨τ * x, h, τ, Subgroup.mem_zpowers τ, ?_⟩
      have h1 : (τ * x) * τ = τ * (τ * x) :=
        Subgroup.mem_centralizer_singleton_iff.mp h.2
      calc (τ * x) * τ = τ * (τ * x) := h1
        _ = (τ * τ) * x := by group
        _ = x := by rw [hτ, one_mul]

theorem lemma54W_le_lemma54T₂ {σ₂ τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) ≤
      lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) := by
  intro a ha
  have hcomm : ∀ x ∈ J z ⊓ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G), ∀ b ∈ Subgroup.zpowers (τ : G), Commute x b := by
    intro x hx b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (show Commute x (τ : G) from
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2).zpow_right k
  rw [lemma54W, CFSG.mem_sup_of_commute hcomm] at ha
  obtain ⟨x, hx, b, hb, rfl⟩ := ha
  obtain ⟨⟨hxJ, hxσ⟩, -⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hxH : x ∈ H z := J_le_H hxJ
  have hbH : (τ : G) ^ k ∈ H z := Subgroup.zpow_mem (H z) τ.2 k
  have haH : x * (τ : G) ^ k ∈ H z := (H z).mul_mem hxH hbH
  have hτσH : τ * (sigma1Nine (z := z) D * σ₂⁻¹) =
      (sigma1Nine (z := z) D * σ₂⁻¹) * τ := by
    have h2 : τ * σ₂⁻¹ = σ₂⁻¹ * τ := (show Commute τ σ₂ from hτ₂).inv_right.eq
    calc τ * (sigma1Nine (z := z) D * σ₂⁻¹) = (τ * sigma1Nine (z := z) D) * σ₂⁻¹ := by group
      _ = (sigma1Nine (z := z) D * τ) * σ₂⁻¹ := by rw [hτ₁]
      _ = sigma1Nine (z := z) D * (τ * σ₂⁻¹) := by group
      _ = sigma1Nine (z := z) D * (σ₂⁻¹ * τ) := by rw [h2]
      _ = (sigma1Nine (z := z) D * σ₂⁻¹) * τ := by group
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨haH, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : x * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) =
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hxσ
    have h2 : ((τ : G) ^ k) * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) =
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * (τ : G) ^ k := by
      have h3 : (τ : G) * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) =
          ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * (τ : G) := by
        have h := congrArg Subtype.val hτσH
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
      exact (show Commute (τ : G) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) from
        h3).zpow_left k |>.eq
    calc (x * (τ : G) ^ k) * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
        = x * (((τ : G) ^ k) * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) := by group
      _ = x * (((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * (τ : G) ^ k) := by rw [h2]
      _ = (x * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) * (τ : G) ^ k := by
            rw [mul_assoc]
      _ = (((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * x) * (τ : G) ^ k := by rw [h1]
      _ = ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * (x * (τ : G) ^ k) := by
            rw [mul_assoc]
  · refine Subgroup.mem_map.mpr ⟨⟨x * (τ : G) ^ k, haH⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hxq : qH (z := z) D ⟨x, hxH⟩ = 1 :=
      (J_mem_iff D ⟨x, hxH⟩).mp (Subgroup.mem_subgroupOf.mpr hxJ)
    have hbq : qH (z := z) D ⟨(τ : G) ^ k, hbH⟩ = tA ^ k := by
      rw [show (⟨(τ : G) ^ k, hbH⟩ : ↥(H z)) = τ ^ k from Subtype.ext rfl, map_zpow, hqτ]
    rw [show (⟨x * (τ : G) ^ k, haH⟩ : ↥(H z)) =
        ⟨x, hxH⟩ * ⟨(τ : G) ^ k, hbH⟩ from rfl, map_mul, hxq, hbq, one_mul]
    exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) k


private theorem mem_closure_t_uv_iff (x : A45) :
    x ∈ Subgroup.closure ({tA, uA * vA} : Set A45) ↔
      x = 1 ∨ x = tA ∨ x = uA * vA ∨ x = tA * (uA * vA) := by
  constructor
  · intro hx
    let S : Subgroup A45 :=
      { carrier := {y | y = 1 ∨ y = tA ∨ y = uA * vA ∨ y = tA * (uA * vA)}
        one_mem' := Or.inl rfl
        mul_mem' := by
          intro y z hy hz
          simp only [Set.mem_setOf_eq] at hy hz ⊢
          rcases hy with rfl | rfl | rfl | rfl <;>
            rcases hz with rfl | rfl | rfl | rfl <;>
            simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one,
              Subtype.coe_mk] <;>
            decide +kernel
        inv_mem' := by
          intro y hy
          simp only [Set.mem_setOf_eq] at hy ⊢
          rcases hy with rfl | rfl | rfl | rfl <;>
            simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one,
              Subtype.coe_mk] <;>
            decide +kernel }
    have hle : Subgroup.closure ({tA, uA * vA} : Set A45) ≤ S := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    exact hle hx
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

private theorem tA_comm_sigma :
    tA * ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) =
      ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) * tA := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  decide +kernel

private theorem uvA_comm_sigma :
    uA * vA * ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) =
      ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) * (uA * vA) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  decide +kernel

private theorem one_ne_uvA : (1 : A45) ≠ uA * vA := by
  intro h
  exact absurd (congrArg (fun z : A45 => (z : Equiv.Perm (Fin 45))) h) (by
    show (1 : Equiv.Perm (Fin 45)) ≠ u * v
    decide +kernel)

private theorem one_ne_tA_uvA : (1 : A45) ≠ tA * (uA * vA) := by
  intro h
  exact absurd (congrArg (fun z : A45 => (z : Equiv.Perm (Fin 45))) h) (by
    show (1 : Equiv.Perm (Fin 45)) ≠ t * (u * v)
    decide +kernel)

private theorem tA_ne_uvA : tA ≠ uA * vA := by
  intro h
  exact absurd (congrArg (fun z : A45 => (z : Equiv.Perm (Fin 45))) h) (by
    show t ≠ u * v
    decide +kernel)

private theorem tA_ne_tA_uvA : tA ≠ tA * (uA * vA) := by
  intro h
  exact absurd (congrArg (fun z : A45 => (z : Equiv.Perm (Fin 45))) h) (by
    show t ≠ t * (u * v)
    decide +kernel)

private theorem uvA_ne_tA_uvA : uA * vA ≠ tA * (uA * vA) := by
  intro h
  exact absurd (congrArg (fun z : A45 => (z : Equiv.Perm (Fin 45))) h) (by
    show u * v ≠ t * (u * v)
    decide +kernel)

private theorem card_closure_t_uv : Nat.card (Subgroup.closure ({tA, uA * vA} : Set A45)) = 4 := by
  let s : Finset A45 := {1, tA, uA * vA, tA * (uA * vA)}
  have hK : (↑(Subgroup.closure ({tA, uA * vA} : Set A45)) : Set A45) = ↑s := by
    ext x
    rw [SetLike.mem_coe, mem_closure_t_uv_iff, Finset.mem_coe]
    simp [s, Finset.mem_insert, Finset.mem_singleton]
  have hc : s.card = 4 := by
    have h1 : (1 : A45) ∉ ({tA, uA * vA, tA * (uA * vA)} : Finset A45) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h | h)
      · exact absurd (congrArg (fun z : A45 => (z : Equiv.Perm (Fin 45))) h) (by
          show (1 : Equiv.Perm (Fin 45)) ≠ t
          decide +kernel)
      · exact one_ne_uvA h
      · exact one_ne_tA_uvA h
    have h2 : tA ∉ ({uA * vA, tA * (uA * vA)} : Finset A45) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact tA_ne_uvA h
      · exact tA_ne_tA_uvA h
    have h3 : uA * vA ∉ ({tA * (uA * vA)} : Finset A45) := by
      simp only [Finset.mem_singleton]
      exact uvA_ne_tA_uvA
    simp only [s]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have h1 : Nat.card (Subgroup.closure ({tA, uA * vA} : Set A45)) =
      ((Subgroup.closure ({tA, uA * vA} : Set A45) : Subgroup A45) : Set A45).ncard :=
    Nat.card_coe_set_eq _
  rw [h1, hK, Set.ncard_coe_finset, hc]

private theorem card_centralizer_eq_card_centralizerJ_mul_card_centralizer_QA45
    {x : ↥(H z)} (hx3 : orderOf x = 3) {q : A45} (hq : qH (z := z) D x = q) :
    Nat.card (Subgroup.centralizer ({x} : Set ↥(H z))) =
      Nat.card (centralizerJ x) * Nat.card (Subgroup.centralizer ({q} : Set A45)) := by
  have hx3P : IsPGroup 3 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx3]
    norm_num
  have hmain := CFSG.card_centralizer_eq_card_inf_mul_card_quotient
    (G := ↥(H z)) (p := 3) (N := (J z).subgroupOf (H z)) (x := x) hx3P
    (coprime_three_card_J_subgroupOf (z := z))
  rw [hmain, card_centralizer_quotient_eq (D := D) x, hq,
    card_centralizer_inf_J_subgroupOf (z := z) (x := x)]

private theorem card_centralizer_s1s2inv :
    Nat.card (Subgroup.centralizer
      ({(⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹} : Set A45)) = 108 := by
  have hm : sigma1 * sigma2⁻¹ ∈ QA45.originalSubgroup :=
    QA45.originalSubgroup.mul_mem sigma1_mem_A (QA45.originalSubgroup.inv_mem sigma2_mem_A)
  exact (card_centralizer_QA45_eq_filter (sigma1 * sigma2⁻¹) hm).trans
    Certificates.certificate946005.centralizer_sigma1sigma2inv

private theorem lemma54T₂_eq_map (h : Tim79a.ParrottHyp z) (σ : ↥(H z)) :
    lemma54T₂ D (σ : G) = (Subgroup.centralizer ({σ} : Set ↥(H z)) ⊓
      (Subgroup.closure ({tA, uA * vA} : Set A45)).comap (qH (z := z) D)).map (H z).subtype := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨hxH, hxC⟩, hxK⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxK
    have hyH : y = ⟨x, hxH⟩ := Subtype.ext hyx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxC))
    · rw [← hyH]; exact hy
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyC, hyK⟩ := Subgroup.mem_inf.mp hy
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨y.2,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hyC))⟩,
      Subgroup.mem_map.mpr ⟨y, hyK, rfl⟩⟩

theorem card_lemma54T₂ (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    Nat.card (lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) = 2 ^ 8 := by
  let σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  let K : Subgroup A45 := Subgroup.closure ({tA, uA * vA} : Set A45)
  let Y : Subgroup ↥(H z) := Subgroup.centralizer ({σ} : Set ↥(H z))
  let T : Subgroup ↥(H z) := Y ⊓ K.comap (qH (z := z) D)
  let Q : A45 := (⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹
  let C : Subgroup A45 := Subgroup.centralizer ({Q} : Set A45)
  have hqσ : qH (z := z) D σ = Q := by
    show qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) = _
    rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (sigma1Nine (z := z) D) ^ 3 = 1 := by
      rw [← sigma1Nine_order (z := z) D]
      exact pow_orderOf_eq_one _
    have h2 : (σ₂⁻¹) ^ 3 = 1 := by
      have hp : σ₂ ^ 3 = 1 := by rw [← hσ₂]; exact pow_orderOf_eq_one σ₂
      rw [inv_pow, hp, inv_one]
    have hcomm' : Commute (sigma1Nine (z := z) D) σ₂⁻¹ :=
      (show Commute (sigma1Nine (z := z) D) σ₂ from hc₂.symm).inv_right
    show (sigma1Nine (z := z) D * σ₂⁻¹) ^ 3 = 1
    rw [hcomm'.mul_pow, h1, h2, mul_one]
  have hσne : σ ≠ 1 := by
    intro h1
    have h2 : qH (z := z) D σ = 1 := by rw [h1, map_one]
    rw [hqσ] at h2
    exact sigma1_mul_sigma2_inv_ne_one h2
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσne
  have hJcard : Nat.card (centralizerJ σ) = 2 ^ 6 := by
    rw [show Nat.card (centralizerJ σ) =
        Nat.card ↥(J z ⊓ centralizer ({(σ : G)} : Set G)) from ?_]
    · exact card_J_inf_centralizer_sigma1Nine_mul_inv_of_spin (z := z) D h P hP hσ₂ hq₂ hc₂
    · rw [centralizerJ, inf_comm (Subgroup.centralizer ({(σ : G)} : Set G)) (J z)]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (H := J z ⊓ centralizer ({(σ : G)} : Set G)) (K := J z) inf_le_left).toEquiv
  have hYcard : Nat.card ↥Y = 6912 := by
    show Nat.card (Subgroup.centralizer ({σ} : Set ↥(H z))) = 6912
    rw [card_centralizer_eq_card_centralizerJ_mul_card_centralizer_QA45 (z := z) (D := D)
      hσord hqσ, hJcard, card_centralizer_s1s2inv]
    norm_num
  have hYmap : Y.map (qH (z := z) D) = C := by
    ext g
    constructor
    · intro hg
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hyc : y * σ = σ * y := Subgroup.mem_centralizer_singleton_iff.mp hy
      have step1 : qH (z := z) D y * Q = qH (z := z) D y * qH (z := z) D σ := by
        rw [hqσ]
      have step2 : qH (z := z) D y * qH (z := z) D σ = qH (z := z) D (y * σ) :=
        (map_mul (qH (z := z) D) y σ).symm
      have step3 : qH (z := z) D (y * σ) = qH (z := z) D (σ * y) := by rw [hyc]
      have step4 : qH (z := z) D (σ * y) = Q * qH (z := z) D y := by
        rw [map_mul, hqσ]
      exact step1.trans (step2.trans (step3.trans step4))
    · intro hg
      have hgc : g * qH (z := z) D σ = qH (z := z) D σ * g := by
        rw [hqσ]
        exact Subgroup.mem_centralizer_singleton_iff.mp hg
      obtain ⟨s, hqs, hsr⟩ :=
        exists_lift_centralizer (z := z) (D := D) (r := σ) hσord hgc
      exact Subgroup.mem_map.mpr ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr hsr, hqs⟩
  have hKC : K ≤ C := by
    rw [show K = Subgroup.closure ({tA, uA * vA} : Set A45) from rfl, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr tA_comm_sigma
    · exact Subgroup.mem_centralizer_singleton_iff.mpr uvA_comm_sigma
  have hTrel : T.relIndex Y = 27 := by
    have h1 : T.relIndex Y = (K.comap (qH (z := z) D)).relIndex Y := by
      show (Y ⊓ K.comap (qH (z := z) D)).relIndex Y = _
      rw [inf_comm, Subgroup.inf_relIndex_right]
    rw [h1, Subgroup.relIndex_comap, hYmap]
    have hmul := Subgroup.relIndex_mul_card K C
    rw [inf_eq_left.mpr hKC, card_closure_t_uv, card_centralizer_s1s2inv] at hmul
    omega
  have hTcard : Nat.card ↥T = 2 ^ 8 := by
    have hmul := Subgroup.relIndex_mul_card T Y
    rw [inf_eq_left.mpr inf_le_left, hTrel, hYcard] at hmul
    have h256 : Nat.card ↥T = 256 := by
      have h2 := hmul
      rw [show (6912 : ℕ) = 27 * 256 by norm_num] at h2
      exact Nat.mul_left_cancel (by norm_num) h2
    rw [h256]
    norm_num
  rw [lemma54T₂_eq_map (z := z) D h σ, Subgroup.card_map_of_injective (H z).subtype_injective]
  exact hTcard

theorem card_lemma54Y (h : Tim79a.ParrottHyp z)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    Nat.card ↥(H z ⊓ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) = 6912 := by
  let σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  let Q : A45 := (⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹
  have hqσ : qH (z := z) D σ = Q := by
    show qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) = _
    rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (sigma1Nine (z := z) D) ^ 3 = 1 := by
      rw [← sigma1Nine_order (z := z) D]
      exact pow_orderOf_eq_one _
    have h2 : (σ₂⁻¹) ^ 3 = 1 := by
      have hp : σ₂ ^ 3 = 1 := by rw [← hσ₂]; exact pow_orderOf_eq_one σ₂
      rw [inv_pow, hp, inv_one]
    have hcomm' : Commute (sigma1Nine (z := z) D) σ₂⁻¹ :=
      (show Commute (sigma1Nine (z := z) D) σ₂ from hc₂.symm).inv_right
    show (sigma1Nine (z := z) D * σ₂⁻¹) ^ 3 = 1
    rw [hcomm'.mul_pow, h1, h2, mul_one]
  have hσne : σ ≠ 1 := by
    intro h1
    have h2 : qH (z := z) D σ = 1 := by rw [h1, map_one]
    rw [hqσ] at h2
    exact sigma1_mul_sigma2_inv_ne_one h2
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσne
  have hJcard : Nat.card (centralizerJ σ) = 2 ^ 6 := by
    rw [show Nat.card (centralizerJ σ) =
        Nat.card ↥(J z ⊓ centralizer ({(σ : G)} : Set G)) from ?_]
    · exact card_J_inf_centralizer_sigma1Nine_mul_inv_of_spin (z := z) D h P hP hσ₂ hq₂ hc₂
    · rw [centralizerJ, inf_comm (Subgroup.centralizer ({(σ : G)} : Set G)) (J z)]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (H := J z ⊓ centralizer ({(σ : G)} : Set G)) (K := J z) inf_le_left).toEquiv
  have hYcard : Nat.card (Subgroup.centralizer ({σ} : Set ↥(H z))) = 6912 := by
    rw [card_centralizer_eq_card_centralizerJ_mul_card_centralizer_QA45 (z := z) (D := D)
      hσord hqσ, hJcard, card_centralizer_s1s2inv]
    norm_num
  have hEq : H z ⊓ centralizer ({(σ : G)} : Set G) =
      (Subgroup.centralizer ({σ} : Set ↥(H z))).map (H z).subtype := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxC)), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))⟩
  rw [hEq, Subgroup.card_map_of_injective (H z).subtype_injective, hYcard]

private theorem factorization_6912 : Nat.factorization 6912 2 = 8 := by
  have h6912 : 6912 = 2 ^ 8 * 27 := by norm_num
  rw [h6912, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (27 : ℕ)), add_zero]

theorem isSylowOf_lemma54T₂ (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    IsSylowOf 2 (lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) := by
  refine isSylowOf_of_card inf_le_left ?_
  show Nat.card (lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) =
    2 ^ (Nat.card ↥(H z ⊓ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))).factorization 2
  rw [card_lemma54T₂ (z := z) D h P hP hσ₂ hq₂ hc₂,
    card_lemma54Y (z := z) D h P hP hσ₂ hq₂ hc₂, factorization_6912]

private noncomputable def lemma54Cocycle (τ : ↥(H z)) (y : J z) : J z :=
  y⁻¹ * conjJ' z τ y

private theorem conjZ_eq_one_of_qH_eq_tA (h : Tim79a.ParrottHyp z) {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) : conjZ z τ = 1 :=
  conjZ_eq_one_of_qH_mem_QP45 (z := z) D h τ (by rw [hqτ]; exact t_mem_Q)

private theorem mul_comm_of_mem_centerIn {c : J z} (hc : (c : G) ∈ centerIn (J z)) (d : J z) :
    c * d = d * c :=
  Subtype.ext (Subgroup.mem_centralizer_iff.mp hc.2 (d : G) d.2).symm

private theorem lemma54Cocycle_mem_centerIn (h : Tim79a.ParrottHyp z) {τ : ↥(H z)} {y : J z}
    (hy : conjV h τ (QuotientV.pi z y) = QuotientV.pi z y) :
    (lemma54Cocycle τ y : G) ∈ centerIn (J z) := by
  refine (pi_eq_one_iff_mem_centerIn (lemma54Cocycle τ y).2).mp ?_
  change QuotientV.pi z (lemma54Cocycle τ y) = 1
  unfold lemma54Cocycle
  rw [map_mul, map_inv, ← conjV_mk h τ y, hy, inv_mul_cancel]

private theorem lemma54Cocycle_mul {τ : ↥(H z)} {y y' : J z}
    (hy : (lemma54Cocycle τ y : G) ∈ centerIn (J z)) :
    lemma54Cocycle τ (y * y') = lemma54Cocycle τ y * lemma54Cocycle τ y' := by
  have hcomm : y'⁻¹ * (y⁻¹ * conjJ' z τ y) = (y⁻¹ * conjJ' z τ y) * y'⁻¹ :=
    (mul_comm_of_mem_centerIn hy y'⁻¹).symm
  unfold lemma54Cocycle
  rw [map_mul, mul_inv_rev]
  calc y'⁻¹ * y⁻¹ * (conjJ' z τ y * conjJ' z τ y')
      = (y'⁻¹ * (y⁻¹ * conjJ' z τ y)) * conjJ' z τ y' := by group
    _ = ((y⁻¹ * conjJ' z τ y) * y'⁻¹) * conjJ' z τ y' := by rw [hcomm]
    _ = (y⁻¹ * conjJ' z τ y) * (y'⁻¹ * conjJ' z τ y') := by group

private theorem conjJ'_eq_self_of_mem_centerIn {s : ↥(H z)} (hZs : conjZ z s = 1) {c : J z}
    (hc : (c : G) ∈ centerIn (J z)) : conjJ' z s c = c := by
  apply Subtype.ext
  rw [conjJ'_apply_coe]
  have hcent : (c : G) * (s : G) = (s : G) * (c : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (centerIn_le_centralizer_of_conjZ_eq_one hZs hc)
  rw [← hcent]
  group

private theorem lemma54Cocycle_conjJ' {τ s : ↥(H z)} (hs : s * τ = τ * s) (y : J z) :
    lemma54Cocycle τ (conjJ' z s y) = conjJ' z s (lemma54Cocycle τ y) := by
  have h1 : conjJ' z τ (conjJ' z s y) = conjJ' z s (conjJ' z τ y) := by
    calc conjJ' z τ (conjJ' z s y) = (conjJ' z τ * conjJ' z s) y := by rw [MulAut.mul_apply]
      _ = conjJ' z (τ * s) y := by rw [map_mul]
      _ = conjJ' z (s * τ) y := by rw [hs.symm]
      _ = (conjJ' z s * conjJ' z τ) y := by rw [map_mul]
      _ = conjJ' z s (conjJ' z τ y) := by rw [MulAut.mul_apply]
  unfold lemma54Cocycle
  rw [h1, map_mul, map_inv]

private theorem lemma54Cocycle_conjJ'_eq_self {τ s : ↥(H z)} (hs : s * τ = τ * s)
    (hZs : conjZ z s = 1) {y : J z} (hy : (lemma54Cocycle τ y : G) ∈ centerIn (J z)) :
    lemma54Cocycle τ (conjJ' z s y) = lemma54Cocycle τ y := by
  rw [lemma54Cocycle_conjJ' hs]
  exact conjJ'_eq_self_of_mem_centerIn hZs hy

private theorem lemma54Cocycle_eq_one_of_mem_centerIn {τ : ↥(H z)} (hZτ : conjZ z τ = 1)
    {ζ : J z} (hζ : (ζ : G) ∈ centerIn (J z)) : lemma54Cocycle τ ζ = 1 := by
  unfold lemma54Cocycle
  rw [conjJ'_eq_self_of_mem_centerIn hZτ hζ, inv_mul_cancel]

theorem conjV_conjJ'_of_comm (h : Tim79a.ParrottHyp z) {g s : ↥(H z)}
    (hgs : g * s = s * g) {y : J z}
    (hy : conjV h g (QuotientV.pi z y) = QuotientV.pi z y) :
    conjV h g (QuotientV.pi z (conjJ' z s y)) = QuotientV.pi z (conjJ' z s y) := by
  rw [← conjV_mk h s y, ← MulAut.mul_apply, ← map_mul, hgs, map_mul, MulAut.mul_apply, hy]

theorem coord_fixed_of_conjV_fixed (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {y : ↥(H z)} {w : V}
    (hy : conjV h y (spinVecToV h P w) = spinVecToV h P w) :
    ((rhoA (qH (z := z) D y) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
  rw [conjV_spinVecToV D h P hP] at hy
  exact spinVecToV_injective h P hy

theorem coord_fixed_sigma1Nine_mul_inv (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A) {w : V}
    (hx : conjV h (sigma1Nine (z := z) D * σ₂⁻¹) (spinVecToV h P w) = spinVecToV h P w) :
    ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
  have h1 := coord_fixed_of_conjV_fixed (z := z) D h P hP hx
  rwa [map_mul, qH_sigma1Nine, map_inv, hq₂] at h1

theorem coord_fixed_of_qH_eq_tA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) {w : V}
    (hx : conjV h τ (spinVecToV h P w) = spinVecToV h P w) :
    ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
  have h1 := coord_fixed_of_conjV_fixed (z := z) D h P hP hx
  rwa [hqτ] at h1

theorem mem_centralizer_of_conjV_pi_eq (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    (x : J z)
    (hσx : conjV h (sigma1Nine (z := z) D * σ₂⁻¹) (QuotientV.pi z x) = QuotientV.pi z x)
    (hτx : conjV h τ (QuotientV.pi z x) = QuotientV.pi z x) :
    (x : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ∧
      (x : G) ∈ centralizer ({(τ : G)} : Set G) := by
  let s1 : ↥(H z) := sigma1Nine (z := z) D
  let σh : ↥(H z) := s1 * σ₂⁻¹
  have hq1 : qH (z := z) D s1 = (⟨sigma1, sigma1_mem_A⟩ : A45) := qH_sigma1Nine (z := z) D
  have hZσ : conjZ z σh = 1 := by
    show conjZ z (sigma1Nine (z := z) D * σ₂⁻¹) = 1
    have h2 : conjZ z σ₂ = 1 :=
      conjZ_eq_one_of_qH_mem_QP45 (z := z) D h σ₂ (by rw [hq₂]; exact sigma2_mem_Q)
    rw [map_mul, map_inv, conjZ_sigma1Nine (z := z) h D, h2, inv_one, mul_one]
  have hσ3 : σh ^ 3 = 1 := by
    have h1 : s1 ^ 3 = 1 := by
      rw [← sigma1Nine_order (z := z) D]
      exact pow_orderOf_eq_one s1
    have h2 : (σ₂⁻¹) ^ 3 = 1 := by
      have hp : σ₂ ^ 3 = 1 := by rw [← hσ₂]; exact pow_orderOf_eq_one σ₂
      rw [inv_pow, hp, inv_one]
    have hcomm' : Commute s1 σ₂⁻¹ := (show Commute s1 σ₂ from hc₂.symm).inv_right
    show (s1 * σ₂⁻¹) ^ 3 = 1
    rw [hcomm'.mul_pow, h1, h2, mul_one]
  constructor
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact mem_centralizerJ_iff.mp (mem_centralizerJ_of_conjV_pi_eq h hσ3 hZσ hσx)
  · have hZτ : conjZ z τ = 1 := conjZ_eq_one_of_qH_eq_tA (z := z) D h hqτ
    have hs1τ : τ * s1 = s1 * τ := hτ₁
    let x₁ : J z := conjJ' z s1 x
    let x₂ : J z := conjJ' z s1 x₁
    have hτx₁ : conjV h τ (QuotientV.pi z x₁) = QuotientV.pi z x₁ :=
      conjV_conjJ'_of_comm (z := z) h (g := τ) (s := s1) hs1τ (y := x) hτx
    have hτx₂ : conjV h τ (QuotientV.pi z x₂) = QuotientV.pi z x₂ :=
      conjV_conjJ'_of_comm (z := z) h (g := τ) (s := s1) hs1τ (y := x₁) hτx₁
    have hcx : (lemma54Cocycle τ x : G) ∈ centerIn (J z) :=
      lemma54Cocycle_mem_centerIn (z := z) h hτx
    have hcx₁ : (lemma54Cocycle τ x₁ : G) ∈ centerIn (J z) :=
      lemma54Cocycle_mem_centerIn (z := z) h hτx₁
    have hcx₂ : (lemma54Cocycle τ x₂ : G) ∈ centerIn (J z) :=
      lemma54Cocycle_mem_centerIn (z := z) h hτx₂
    have hcx₁eq : lemma54Cocycle τ x₁ = lemma54Cocycle τ x :=
      lemma54Cocycle_conjJ'_eq_self (z := z) (τ := τ) (s := s1) hs1τ.symm
        (conjZ_sigma1Nine (z := z) h D) (y := x) hcx
    have hcx₂eq : lemma54Cocycle τ x₂ = lemma54Cocycle τ x := by
      have h := lemma54Cocycle_conjJ'_eq_self (z := z) (τ := τ) (s := s1) hs1τ.symm
        (conjZ_sigma1Nine (z := z) h D) (y := x₁) hcx₁
      rw [h, hcx₁eq]
    have hcxx₁ : (lemma54Cocycle τ (x * x₁) : G) ∈ centerIn (J z) := by
      rw [lemma54Cocycle_mul (z := z) (τ := τ) (y := x) (y' := x₁) hcx]
      exact Subgroup.mul_mem _ hcx hcx₁
    obtain ⟨w, hw⟩ := spinVecToV_surjective h P (QuotientV.pi z x)
    have hσcoords : ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
        (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
      refine coord_fixed_sigma1Nine_mul_inv (z := z) D h P hP hq₂ ?_
      rw [hw]
      exact hσx
    have htcoords : ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
      refine coord_fixed_of_qH_eq_tA (z := z) D h P hP hqτ ?_
      rw [hw]
      exact hτx
    have htrace := spin_trace_sigma1_of_fixed_sigma_t hσcoords htcoords
    have hπx₁ : QuotientV.pi z x₁ = spinVecToV h P
        (((rhoA (⟨sigma1, sigma1_mem_A⟩ : A45) : GL8) :
          Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) := by
      show QuotientV.pi z (conjJ' z s1 x) = _
      rw [← conjV_mk h s1 x, ← hw, conjV_spinVecToV D h P hP, hq1]
    have hπx₂ : QuotientV.pi z x₂ = spinVecToV h P
        (((rhoA (⟨sigma1, sigma1_mem_A⟩ : A45) : GL8) :
          Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
          (((rhoA (⟨sigma1, sigma1_mem_A⟩ : A45) : GL8) :
            Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w)) := by
      show QuotientV.pi z (conjJ' z s1 x₁) = _
      rw [← conjV_mk h s1 x₁, hπx₁, conjV_spinVecToV D h P hP, hq1]
    have hπall : QuotientV.pi z (x * x₁ * x₂) = 1 := by
      rw [map_mul, map_mul, ← hw, hπx₁, hπx₂, ← spinVecToV_add, ← spinVecToV_add, htrace,
        spinVecToV_zero]
    have hxallZ : ((x * x₁ * x₂ : J z) : G) ∈ centerIn (J z) :=
      (pi_eq_one_iff_mem_centerIn (x * x₁ * x₂).2).mp hπall
    have hc0 : lemma54Cocycle τ (x * x₁ * x₂) = 1 :=
      lemma54Cocycle_eq_one_of_mem_centerIn (z := z) (τ := τ) hZτ hxallZ
    have hc3 : lemma54Cocycle τ x * lemma54Cocycle τ x * lemma54Cocycle τ x = 1 := by
      have h1 := hc0
      rw [lemma54Cocycle_mul (z := z) (τ := τ) (y := x * x₁) (y' := x₂) hcxx₁,
        lemma54Cocycle_mul (z := z) (τ := τ) (y := x) (y' := x₁) hcx, hcx₁eq, hcx₂eq] at h1
      exact h1
    have hc2 : lemma54Cocycle τ x * lemma54Cocycle τ x = 1 := by
      apply Subtype.ext
      simpa using centerIn_J_sq h hcx
    have hc1 : lemma54Cocycle τ x = 1 := by
      have h := hc3
      rw [hc2, one_mul] at h
      exact h
    have hTx : conjJ' z τ x = x := by
      have h := congrArg (fun a : J z => x * a) hc1
      simp only [lemma54Cocycle, mul_one] at h
      rw [← mul_assoc, mul_inv_cancel, one_mul] at h
      exact h
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcoe := congrArg (fun a : J z => (a : G)) hTx
    rw [conjJ'_apply_coe] at hcoe
    calc (x : G) * (τ : G) = ((τ : G) * (x : G) * (τ : G)⁻¹) * (τ : G) := by rw [hcoe]
      _ = (τ : G) * (x : G) := by group


private def lemma54UVec (i : Fin 4) : V := ![0, spinE2, spinW0, spinE2 + spinW0] i

private theorem lemma54UVec_mem_iff (w : V) :
    (∃ i : Fin 4, lemma54UVec i = w) ↔
      ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
      ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;>
      exact (spin_fixed_sigma_t_iff _).mpr (by simp [lemma54UVec])
  · intro hw
    rcases (spin_fixed_sigma_t_iff w).mp hw with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [lemma54UVec]⟩
    · exact ⟨1, by simp [lemma54UVec]⟩
    · exact ⟨2, by simp [lemma54UVec]⟩
    · exact ⟨3, by simp [lemma54UVec]⟩

private theorem lemma54UVec_injective : Function.Injective lemma54UVec := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; exact absurd hij (by decide +kernel))

private theorem card_fixed_subtype :
    Nat.card {w : V // ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
        (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
      ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w} = 4 := by
  let φ : Fin 4 → {w : V // ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
      (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
    ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w} :=
    fun i => ⟨lemma54UVec i, (lemma54UVec_mem_iff (lemma54UVec i)).mp ⟨i, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro i j hij
      exact lemma54UVec_injective (congrArg Subtype.val hij)
    · intro w
      obtain ⟨i, hi⟩ := (lemma54UVec_mem_iff w.1).mpr w.2
      exact ⟨i, Subtype.ext hi⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ)]
  simp

private theorem card_fixed_subgroup (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A) {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) :
    Nat.card ↥(autFixedSubgroup (conjV h (sigma1Nine (z := z) D * σ₂⁻¹)) ⊓
      autFixedSubgroup (conjV h τ)) = 4 := by
  have hqσ : qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) =
      (⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹ := by
    rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
  have himage : spinVecToV h P '' {w : V |
      ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
      ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w} =
      (↑(autFixedSubgroup (conjV h (sigma1Nine (z := z) D * σ₂⁻¹)) ⊓
        autFixedSubgroup (conjV h τ)) : Set (QuotientV.V z)) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_inf, mem_autFixedSubgroup, mem_autFixedSubgroup]
      exact ⟨by rw [conjV_spinVecToV D h P hP, hqσ, hw.1],
        by rw [conjV_spinVecToV D h P hP, hqτ, hw.2]⟩
    · intro hv
      rw [SetLike.mem_coe, Subgroup.mem_inf, mem_autFixedSubgroup, mem_autFixedSubgroup] at hv
      obtain ⟨hσv, hτv⟩ := hv
      obtain ⟨w, rfl⟩ := spinVecToV_surjective h P v
      refine ⟨w, ⟨?_, ?_⟩, rfl⟩
      · have hvv := hσv
        rw [conjV_spinVecToV D h P hP, hqσ] at hvv
        exact spinVecToV_injective h P hvv
      · have hvv := hτv
        rw [conjV_spinVecToV D h P hP, hqτ] at hvv
        exact spinVecToV_injective h P hvv
  have hfin : Nat.card ↥(↑(autFixedSubgroup (conjV h (sigma1Nine (z := z) D * σ₂⁻¹)) ⊓
      autFixedSubgroup (conjV h τ)) : Set (QuotientV.V z)) =
      Nat.card (spinVecToV h P '' {w : V |
        ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
          Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
        ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w}) := by
    rw [himage]
  rw [show Nat.card ↥(autFixedSubgroup (conjV h (sigma1Nine (z := z) D * σ₂⁻¹)) ⊓
      autFixedSubgroup (conjV h τ)) = Nat.card ↥(↑(autFixedSubgroup
        (conjV h (sigma1Nine (z := z) D * σ₂⁻¹)) ⊓ autFixedSubgroup (conjV h τ)) :
        Set (QuotientV.V z)) from rfl]
  rw [hfin, Nat.card_image_of_injective (spinVecToV_injective h P)]
  exact card_fixed_subtype

theorem card_lemma54N (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    Nat.card ↥(J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G)) = 16 := by
  have hZσ : conjZ z (sigma1Nine (z := z) D * σ₂⁻¹) = 1 := by
    rw [map_mul, map_inv, conjZ_sigma1Nine (z := z) h D]
    have h2 : conjZ z σ₂ = 1 :=
      conjZ_eq_one_of_qH_mem_QP45 (z := z) D h σ₂ (by rw [hq₂]; exact sigma2_mem_Q)
    rw [h2, inv_one, mul_one]
  have hZτ : conjZ z τ = 1 := conjZ_eq_one_of_qH_eq_tA (z := z) D h hqτ
  have hAJ : J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G) ≤ J z := fun x hx =>
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
  let g : ↥(J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G)) →* J z :=
    (Subgroup.subtype _).codRestrict (J z) (fun a => hAJ a.2)
  let f : ↥(J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G)) →* QuotientV.V z := (QuotientV.pi z).comp g
  have hcard := Subgroup.card_ker_mul_card_range f
  have hZA : centerIn (J z) ≤ J z ⊓
      centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G) := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
      ⟨(inf_le_left : centerIn (J z) ≤ J z) hx,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp
            (centerIn_le_centralizer_of_conjZ_eq_one hZσ hx))⟩, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp
        (centerIn_le_centralizer_of_conjZ_eq_one hZτ hx))
  have hker : Nat.card ↥f.ker = 4 := by
    have heq : f.ker = (centerIn (J z)).subgroupOf
        (J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
          centralizer ({(τ : G)} : Set G)) := by
      ext a
      constructor
      · intro ha
        rw [MonoidHom.mem_ker] at ha
        exact Subgroup.mem_subgroupOf.mpr ((pi_eq_one_iff_mem_centerIn (hAJ a.2)).mp ha)
      · intro ha
        rw [MonoidHom.mem_ker]
        exact (pi_eq_one_iff_mem_centerIn (hAJ a.2)).mpr (Subgroup.mem_subgroupOf.mp ha)
    rw [heq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZA).toEquiv]
    exact card_centerIn_J h
  have hrange : Nat.card ↥f.range = 4 := by
    have heq : f.range = autFixedSubgroup (conjV h (sigma1Nine (z := z) D * σ₂⁻¹)) ⊓
        autFixedSubgroup (conjV h τ) := by
      ext v
      constructor
      · intro hv
        rw [MonoidHom.mem_range] at hv
        obtain ⟨a, rfl⟩ := hv
        obtain ⟨⟨haJ, haσ⟩, haτ⟩ := Subgroup.mem_inf.mp a.2
        rw [Subgroup.mem_inf, mem_autFixedSubgroup, mem_autFixedSubgroup]
        have hfixσ : conjV h (sigma1Nine (z := z) D * σ₂⁻¹)
            (QuotientV.pi z ⟨(a : G), hAJ a.2⟩) = QuotientV.pi z ⟨(a : G), hAJ a.2⟩ := by
          rw [conjV_mk h _ ⟨(a : G), hAJ a.2⟩]
          congr 1
          apply Subtype.ext
          rw [conjJ'_apply_coe]
          have hc := Subgroup.mem_centralizer_singleton_iff.mp haσ
          rw [← hc]
          group
        have hfixτ : conjV h τ (QuotientV.pi z ⟨(a : G), hAJ a.2⟩) =
            QuotientV.pi z ⟨(a : G), hAJ a.2⟩ := by
          rw [conjV_mk h τ ⟨(a : G), hAJ a.2⟩]
          congr 1
          apply Subtype.ext
          rw [conjJ'_apply_coe]
          have hc := Subgroup.mem_centralizer_singleton_iff.mp haτ
          rw [← hc]
          group
        exact ⟨hfixσ, hfixτ⟩
      · intro hv
        rw [Subgroup.mem_inf, mem_autFixedSubgroup, mem_autFixedSubgroup] at hv
        obtain ⟨hσv, hτv⟩ := hv
        rw [MonoidHom.mem_range]
        obtain ⟨x, rfl⟩ := QuotientV.pi_surjective z v
        obtain ⟨hxσ, hxτ⟩ := mem_centralizer_of_conjV_pi_eq (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ
          hτ₁ hτ₂ x hσv hτv
        refine ⟨⟨(x : G), Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨x.2, hxσ⟩, hxτ⟩⟩, ?_⟩
        rfl
    rw [heq, card_fixed_subgroup (z := z) D h P hP hq₂ hqτ]
  rw [hker, hrange] at hcard
  omega

private theorem coord_of_mem_base (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A) {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    {x : G} (hxJ : x ∈ J z)
    (hxσ : x ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hxτ : x ∈ centralizer ({(τ : G)} : Set G)) :
    ∃ w : V, QuotientV.pi z ⟨x, hxJ⟩ = spinVecToV h P w ∧
      ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
      ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
  obtain ⟨w, hw⟩ := spinVecToV_surjective h P (QuotientV.pi z ⟨x, hxJ⟩)
  have hfixσ : conjV h (sigma1Nine (z := z) D * σ₂⁻¹) (QuotientV.pi z ⟨x, hxJ⟩) =
      QuotientV.pi z ⟨x, hxJ⟩ := by
    rw [conjV_mk h _ ⟨x, hxJ⟩]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hxσ
    rw [← hc]
    group
  have hfixτ : conjV h τ (QuotientV.pi z ⟨x, hxJ⟩) = QuotientV.pi z ⟨x, hxJ⟩ := by
    rw [conjV_mk h τ ⟨x, hxJ⟩]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hxτ
    rw [← hc]
    group
  refine ⟨w, hw.symm, ?_, ?_⟩
  · refine coord_fixed_sigma1Nine_mul_inv (z := z) D h P hP hq₂ ?_
    rw [hw]
    exact hfixσ
  · refine coord_fixed_of_qH_eq_tA (z := z) D h P hP hqτ ?_
    rw [hw]
    exact hfixτ

private theorem commute_of_mem_base (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A) {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    {x : G} (hxJ : x ∈ J z)
    (hxσ : x ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hxτ : x ∈ centralizer ({(τ : G)} : Set G))
    {y : G} (hyJ : y ∈ J z)
    (hyσ : y ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hyτ : y ∈ centralizer ({(τ : G)} : Set G)) : x * y = y * x := by
  obtain ⟨wx, hwx, hσwx, htwx⟩ :=
    coord_of_mem_base (z := z) D h P hP hq₂ hqτ hxJ hxσ hxτ
  obtain ⟨wy, hwy, hσwy, htwy⟩ :=
    coord_of_mem_base (z := z) D h P hP hq₂ hqτ hyJ hyσ hyτ
  have hb : b wx wy = 0 := by
    have h1 : q (wx + wy) = 0 :=
      spin_q_eq_zero_of_fixed_sigma_t (by rw [Matrix.mulVec_add, hσwx, hσwy])
        (by rw [Matrix.mulVec_add, htwx, htwy])
    have h2 : q wx = 0 := spin_q_eq_zero_of_fixed_sigma_t hσwx htwx
    have h3 : q wy = 0 := spin_q_eq_zero_of_fixed_sigma_t hσwy htwy
    unfold b
    rw [h1, h2, h3, add_zero, add_zero]
  have hpolar : polarVZMod h (QuotientV.pi z ⟨x, hxJ⟩) (QuotientV.pi z ⟨y, hyJ⟩) = 0 := by
    rw [hwx, hwy, polarVZMod_spinVecToV_eq_b D h P hP, hb]
  exact (polarVZMod_pi_eq_zero_iff h ⟨x, hxJ⟩ ⟨y, hyJ⟩).mp hpolar

private theorem sq_eq_one_of_mem_base (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A) {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    {x : G} (hxJ : x ∈ J z)
    (hxσ : x ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hxτ : x ∈ centralizer ({(τ : G)} : Set G)) : x * x = 1 := by
  obtain ⟨w, hw, hσw, htw⟩ := coord_of_mem_base (z := z) D h P hP hq₂ hqτ hxJ hxσ hxτ
  have hq : q w = 0 := spin_q_eq_zero_of_fixed_sigma_t hσw htw
  have hqv : qVZMod h (QuotientV.pi z ⟨x, hxJ⟩) = 0 := by
    rw [hw, qVZMod_spinVecToV_eq_q D h P hP, hq]
  have hqV : qV h (QuotientV.pi z ⟨x, hxJ⟩) = 1 := (qVZMod_eq_zero_iff h _).mp hqv
  have hqJ : qJ h ⟨x, hxJ⟩ = 1 := by rwa [qV_pi] at hqV
  have hcoe : (x : G) ^ 2 = 1 := by
    have hone := congrArg (fun a : Subgroup.zpowers z => (a : G)) hqJ
    simpa [qJ_coe] using hone
  rwa [pow_two] at hcoe

private theorem not_mem_J_of_qH_eq_tA {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) :
    (τ : G) ∉ J z := by
  intro hmem
  have hq1 : qH (z := z) D τ = 1 := (J_mem_iff D τ).mp (Subgroup.mem_subgroupOf.mpr hmem)
  rw [hqτ] at hq1
  exact t_ne_one (congrArg Subtype.val hq1)

private theorem mul_tau_mul_tau {τ x y : G} (hτ : τ * τ = 1)
    (hxτ : x * τ = τ * x) : (τ * x) * (τ * y) = x * y := by
  calc (τ * x) * (τ * y) = τ * (x * τ) * y := by group
    _ = τ * (τ * x) * y := by rw [hxτ]
    _ = (τ * τ) * (x * y) := by group
    _ = x * y := by rw [hτ, one_mul]

theorem lemma54W_comm (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    ∀ a ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G),
      ∀ b ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G), a * b = b * a := by
  intro a ha b hb
  have hτG : (τ : G) * (τ : G) = 1 := by simpa using congrArg Subtype.val hτ
  rw [mem_lemma54W_iff (τ := (τ : G)) hτG] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · obtain ⟨⟨haJ, haσ⟩, haτ⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨⟨hbJ, hbσ⟩, hbτ⟩ := Subgroup.mem_inf.mp hb
    exact commute_of_mem_base (z := z) D h P hP hq₂ hqτ haJ haσ haτ hbJ hbσ hbτ
  · obtain ⟨⟨haJ, haσ⟩, haτ⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨⟨hyJ, hyσ⟩, hyτ⟩ := Subgroup.mem_inf.mp hb
    have hycomm : a * ((τ : G) * b) = ((τ : G) * b) * a :=
      commute_of_mem_base (z := z) D h P hP hq₂ hqτ haJ haσ haτ hyJ hyσ hyτ
    have hbeq : b = (τ : G) * ((τ : G) * b) := by rw [← mul_assoc, hτG, one_mul]
    calc a * b = a * ((τ : G) * ((τ : G) * b)) := by conv_lhs => rw [hbeq]
      _ = (a * (τ : G)) * ((τ : G) * b) := by group
      _ = ((τ : G) * a) * ((τ : G) * b) := by
            rw [Subgroup.mem_centralizer_singleton_iff.mp haτ]
      _ = (τ : G) * (a * ((τ : G) * b)) := by group
      _ = (τ : G) * (((τ : G) * b) * a) := by rw [hycomm]
      _ = ((τ : G) * ((τ : G) * b)) * a := by group
      _ = b * a := by rw [← hbeq]
  · obtain ⟨⟨hxJ, hxσ⟩, hxτ⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨⟨hbJ, hbσ⟩, hbτ⟩ := Subgroup.mem_inf.mp hb
    have hxcomm : (τ : G) * a * b = b * ((τ : G) * a) :=
      commute_of_mem_base (z := z) D h P hP hq₂ hqτ hxJ hxσ hxτ hbJ hbσ hbτ
    have haeq : a = (τ : G) * ((τ : G) * a) := by rw [← mul_assoc, hτG, one_mul]
    calc a * b = ((τ : G) * ((τ : G) * a)) * b := by conv_lhs => rw [haeq]
      _ = (τ : G) * (((τ : G) * a) * b) := by group
      _ = (τ : G) * (b * ((τ : G) * a)) := by rw [hxcomm]
      _ = ((τ : G) * b) * ((τ : G) * a) := by group
      _ = (b * (τ : G)) * ((τ : G) * a) := by
            rw [← Subgroup.mem_centralizer_singleton_iff.mp hbτ]
      _ = b * ((τ : G) * ((τ : G) * a)) := by group
      _ = b * a := by rw [← haeq]
  · obtain ⟨⟨hxJ, hxσ⟩, hxτ⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨⟨hyJ, hyσ⟩, hyτ⟩ := Subgroup.mem_inf.mp hb
    have haeq : a = (τ : G) * ((τ : G) * a) := by rw [← mul_assoc, hτG, one_mul]
    have hbeq : b = (τ : G) * ((τ : G) * b) := by rw [← mul_assoc, hτG, one_mul]
    have h1 : ((τ : G) * ((τ : G) * a)) * ((τ : G) * ((τ : G) * b)) =
        ((τ : G) * a) * ((τ : G) * b) :=
      mul_tau_mul_tau hτG (Subgroup.mem_centralizer_singleton_iff.mp hxτ)
    have h2 : ((τ : G) * a) * ((τ : G) * b) = ((τ : G) * b) * ((τ : G) * a) :=
      commute_of_mem_base (z := z) D h P hP hq₂ hqτ hxJ hxσ hxτ hyJ hyσ hyτ
    have h3 : ((τ : G) * ((τ : G) * b)) * ((τ : G) * ((τ : G) * a)) =
        ((τ : G) * b) * ((τ : G) * a) :=
      mul_tau_mul_tau hτG (Subgroup.mem_centralizer_singleton_iff.mp hyτ)
    calc a * b = ((τ : G) * ((τ : G) * a)) * ((τ : G) * ((τ : G) * b)) := by
          conv_lhs => rw [haeq, hbeq]
      _ = ((τ : G) * a) * ((τ : G) * b) := h1
      _ = ((τ : G) * b) * ((τ : G) * a) := h2
      _ = ((τ : G) * ((τ : G) * b)) * ((τ : G) * ((τ : G) * a)) := h3.symm
      _ = b * a := by rw [← hbeq, ← haeq]

theorem lemma54W_mul_self (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    ∀ a ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G), a * a = 1 := by
  intro a ha
  have hτG : (τ : G) * (τ : G) = 1 := by simpa using congrArg Subtype.val hτ
  rw [mem_lemma54W_iff (τ := (τ : G)) hτG] at ha
  rcases ha with ha | ha
  · obtain ⟨⟨haJ, haσ⟩, haτ⟩ := Subgroup.mem_inf.mp ha
    exact sq_eq_one_of_mem_base (z := z) D h P hP hq₂ hqτ haJ haσ haτ
  · obtain ⟨⟨hxJ, hxσ⟩, hxτ⟩ := Subgroup.mem_inf.mp ha
    have hxx : ((τ : G) * a) * ((τ : G) * a) = 1 :=
      sq_eq_one_of_mem_base (z := z) D h P hP hq₂ hqτ hxJ hxσ hxτ
    have haeq : a = (τ : G) * ((τ : G) * a) := by rw [← mul_assoc, hτG, one_mul]
    calc a * a = ((τ : G) * ((τ : G) * a)) * ((τ : G) * ((τ : G) * a)) := by
          conv_lhs => rw [haeq]
      _ = ((τ : G) * a) * ((τ : G) * a) :=
            mul_tau_mul_tau hτG (Subgroup.mem_centralizer_singleton_iff.mp hxτ)
      _ = 1 := hxx

theorem card_lemma54W (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    Nat.card (lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)) = 32 := by
  have hτG : (τ : G) * (τ : G) = 1 := by simpa using congrArg Subtype.val hτ
  have hτJ : (τ : G) ∉ J z := not_mem_J_of_qH_eq_tA (z := z) D hqτ
  have hτne : (τ : G) ≠ 1 := fun h1 => hτJ (h1 ▸ Subgroup.one_mem (J z))
  have hordτ : orderOf (τ : G) = 2 := orderOf_eq_prime (by rwa [pow_two]) hτne
  have hdisj : (J z ⊓ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G)) ⊓ Subgroup.zpowers (τ : G) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyA, hyτ⟩ := Subgroup.mem_inf.mp hy
    have hyJ : y ∈ J z := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hyA).1).1
    rcases lemma54W_pow_two_eq_one_or hτG hyτ with h | h
    · rw [h]; exact Subgroup.one_mem ⊥
    · rw [h] at hyJ
      exact absurd hyJ hτJ
  have hcomm : ∀ a ∈ J z ⊓ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G),
      ∀ b ∈ Subgroup.zpowers (τ : G), Commute a b := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (show Commute a (τ : G) from
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ha).2).zpow_right k
  rw [lemma54W,
    CFSG.card_sup_eq_mul_of_commute _ _ hcomm hdisj,
    card_lemma54N (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂, Nat.card_zpowers, hordτ]

private theorem lemma54T₂_le_H {σ : G} {x : G} (hx : x ∈ lemma54T₂ D σ) : x ∈ H z :=
  (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1

private theorem lemma54T₂_centralizes {σ : G} {x : G} (hx : x ∈ lemma54T₂ D σ) :
    x ∈ centralizer ({σ} : Set G) :=
  (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2

private theorem lemma54T₂_qH_mem {σ : G} {x : G} (hx : x ∈ lemma54T₂ D σ) (hxH : x ∈ H z) :
    qH (z := z) D ⟨x, hxH⟩ ∈ Subgroup.closure ({tA, uA * vA} : Set A45) := by
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hx).2
  rw [Subgroup.mem_comap] at hy
  rw [show (⟨x, hxH⟩ : ↥(H z)) = y from Subtype.ext hyx.symm]
  exact hy

private noncomputable def lemma54MapE (σ : G) (E : Subgroup G) (hE : E ≤ lemma54T₂ D σ) :
    E →* A45 where
  toFun x := qH (z := z) D ⟨(x : G), lemma54T₂_le_H (z := z) D (hE x.2)⟩
  map_one' := by
    rw [show (⟨((1 : E) : G), _⟩ : ↥(H z)) = 1 from Subtype.ext rfl, map_one]
  map_mul' a b := by
    rw [show (⟨((a * b : E) : G), _⟩ : ↥(H z)) =
      (⟨(a : G), _⟩ : ↥(H z)) * ⟨(b : G), _⟩ from Subtype.ext rfl, map_mul]

private theorem lemma54MapE_ker {σ : G} (E : Subgroup G) (hE : E ≤ lemma54T₂ D σ) :
    (lemma54MapE (z := z) D σ E hE).ker = (J z).comap E.subtype := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_comap]
  show qH (z := z) D ⟨(x : G), lemma54T₂_le_H (z := z) D (hE x.2)⟩ = 1 ↔ (x : G) ∈ J z
  rw [← J_mem_iff D ⟨(x : G), lemma54T₂_le_H (z := z) D (hE x.2)⟩, Subgroup.mem_subgroupOf]

private theorem lemma54MapE_range_le {σ : G} (E : Subgroup G) (hE : E ≤ lemma54T₂ D σ) :
    (lemma54MapE (z := z) D σ E hE).range ≤
      Subgroup.closure ({tA, uA * vA} : Set A45) := by
  rintro g ⟨x, rfl⟩
  exact lemma54T₂_qH_mem (z := z) D (hE x.2) (lemma54T₂_le_H (z := z) D (hE x.2))

private theorem card_eq_card_inf_mul_card_range {σ : G} (E : Subgroup G)
    (hE : E ≤ lemma54T₂ D σ) :
    Nat.card E = Nat.card ↥(E ⊓ J z) *
      Nat.card ↥(lemma54MapE (z := z) D σ E hE).range := by
  have h := Subgroup.card_ker_mul_card_range (lemma54MapE (z := z) D σ E hE)
  rw [lemma54MapE_ker] at h
  have hker : Nat.card ↥((J z).comap E.subtype) = Nat.card ↥(E ⊓ J z) := by
    rw [Subgroup.comap_subtype, ← Subgroup.inf_subgroupOf_left (H := J z) (K := E)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hker] at h
  exact h.symm

private noncomputable def lemma54MapJ (E : Subgroup G) : ↥(E ⊓ J z) →* QuotientV.V z where
  toFun x := QuotientV.pi z ⟨(x : G), (Subgroup.mem_inf.mp x.2).2⟩
  map_one' := by
    rw [show (⟨((1 : ↥(E ⊓ J z)) : G), _⟩ : J z) = 1 from Subtype.ext rfl, map_one]
  map_mul' a b := by
    rw [show (⟨((a * b : ↥(E ⊓ J z)) : G), _⟩ : J z) =
      (⟨(a : G), _⟩ : J z) * ⟨(b : G), _⟩ from Subtype.ext rfl, map_mul]

private theorem lemma54MapJ_ker (E : Subgroup G) :
    (lemma54MapJ (z := z) E).ker = (centerIn (J z)).comap (E ⊓ J z).subtype := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_comap]
  exact pi_eq_one_iff_mem_centerIn (Subgroup.mem_inf.mp x.2).2

private theorem card_eq_card_inf_centerIn_mul_card_range (E : Subgroup G) :
    Nat.card ↥(E ⊓ J z) = Nat.card ↥((E ⊓ J z) ⊓ centerIn (J z)) *
      Nat.card ↥(lemma54MapJ (z := z) E).range := by
  have h := Subgroup.card_ker_mul_card_range (lemma54MapJ (z := z) E)
  rw [lemma54MapJ_ker] at h
  have hker : Nat.card ↥((centerIn (J z)).comap (E ⊓ J z).subtype) =
      Nat.card ↥((E ⊓ J z) ⊓ centerIn (J z)) := by
    rw [Subgroup.comap_subtype,
      ← Subgroup.inf_subgroupOf_left (H := centerIn (J z)) (K := E ⊓ J z)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hker] at h
  exact h.symm

private theorem card_range_le_finset (h : Tim79a.ParrottHyp z) (P : GL8) (E : Subgroup G)
    {T : Finset V}
    (hT : ∀ w : V, spinVecToV h P w ∈ (lemma54MapJ (z := z) E).range → w ∈ T) :
    Nat.card ↥(lemma54MapJ (z := z) E).range ≤ T.card := by
  classical
  let f : ↥(lemma54MapJ (z := z) E).range → {w : V // w ∈ T} := fun y =>
    ⟨Classical.choose (spinVecToV_surjective h P y.1), by
      have hspec := Classical.choose_spec (spinVecToV_surjective h P y.1)
      exact hT _ (hspec.symm ▸ y.2)⟩
  have hf : Function.Injective f := by
    intro y₁ y₂ h12
    have h1 := Classical.choose_spec (spinVecToV_surjective h P y₁.1)
    have h2 := Classical.choose_spec (spinVecToV_surjective h P y₂.1)
    refine Subtype.ext ?_
    calc y₁.1 = spinVecToV h P (f y₁).1 := h1.symm
      _ = spinVecToV h P (f y₂).1 := by
            rw [show (f y₁).1 = (f y₂).1 from congrArg Subtype.val h12]
      _ = y₂.1 := h2
  calc Nat.card ↥(lemma54MapJ (z := z) E).range
      ≤ Nat.card {w : V // w ∈ T} := Nat.card_le_card_of_injective f hf
    _ = T.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]

private theorem exists_coord_of_mem_J_of_centralizes (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A)
    {x : G} (hxJ : x ∈ J z)
    (hxσ : x ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) :
    ∃ w : V, QuotientV.pi z ⟨x, hxJ⟩ = spinVecToV h P w ∧
      ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
  obtain ⟨w, hw⟩ := spinVecToV_surjective h P (QuotientV.pi z ⟨x, hxJ⟩)
  have hfixσ : conjV h (sigma1Nine (z := z) D * σ₂⁻¹) (QuotientV.pi z ⟨x, hxJ⟩) =
      QuotientV.pi z ⟨x, hxJ⟩ := by
    rw [conjV_mk h _ ⟨x, hxJ⟩]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hxσ
    rw [← hc]
    group
  refine ⟨w, hw.symm, ?_⟩
  refine coord_fixed_sigma1Nine_mul_inv (z := z) D h P hP hq₂ ?_
  rw [hw]
  exact hfixσ

private theorem q_coord_eq_zero_of_sq_eq_one (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {x : J z} (hx2 : (x : G) * (x : G) = 1) {w : V}
    (hw : QuotientV.pi z x = spinVecToV h P w) : q w = 0 := by
  have hqj : qJ h x = 1 := by
    apply Subtype.ext
    rw [qJ_coe]
    simpa [pow_two] using hx2
  have hqv : qV h (QuotientV.pi z x) = 1 := by
    rw [qV_pi]
    exact hqj
  have hqvz : qVZMod h (QuotientV.pi z x) = 0 := (qVZMod_eq_zero_iff h _).mpr hqv
  rw [← qVZMod_spinVecToV_eq_q D h P hP w, ← hw]
  exact hqvz

private theorem b_coord_eq_zero_of_commute (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {x y : J z} (hxy : (x : G) * (y : G) = (y : G) * (x : G)) {wx wy : V}
    (hwx : QuotientV.pi z x = spinVecToV h P wx)
    (hwy : QuotientV.pi z y = spinVecToV h P wy) : b wx wy = 0 := by
  have hpolar : polarVZMod h (QuotientV.pi z x) (QuotientV.pi z y) = 0 :=
    (polarVZMod_pi_eq_zero_iff h x y).mpr hxy
  rw [hwx, hwy, polarVZMod_spinVecToV_eq_b D h P hP] at hpolar
  exact hpolar

private theorem coord_fixed_of_commute (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {e : G} (heH : e ∈ H z) {x : G} (hxJ : x ∈ J z) (hec : e * x = x * e) {w : V}
    (hw : QuotientV.pi z ⟨x, hxJ⟩ = spinVecToV h P w) :
    ((rhoA (qH (z := z) D ⟨e, heH⟩) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
  have hfix : conjV h ⟨e, heH⟩ (QuotientV.pi z ⟨x, hxJ⟩) = QuotientV.pi z ⟨x, hxJ⟩ := by
    rw [conjV_mk h _ ⟨x, hxJ⟩]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe, hec]
    group
  refine coord_fixed_of_conjV_fixed (z := z) D h P hP (y := ⟨e, heH⟩) ?_
  rw [← hw]
  exact hfix

private theorem exists_mem_N_of_coord (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {u : V}
    (huσ : ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
      (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ u = u)
    (hut : ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ u = u) :
    ∃ j : J z, QuotientV.pi z j = spinVecToV h P u ∧
      (j : G) ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
        centralizer ({(τ : G)} : Set G) := by
  have hqσ : qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) =
      (⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹ := by
    rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
  obtain ⟨j, hj⟩ := QuotientV.pi_surjective z (spinVecToV h P u)
  have hσj : conjV h (sigma1Nine (z := z) D * σ₂⁻¹) (QuotientV.pi z j) =
      QuotientV.pi z j := by
    rw [hj, conjV_spinVecToV D h P hP, hqσ, huσ]
  have hτj : conjV h τ (QuotientV.pi z j) = QuotientV.pi z j := by
    rw [hj, conjV_spinVecToV D h P hP, hqτ, hut]
  have hcj := mem_centralizer_of_conjV_pi_eq (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
    j hσj hτj
  exact ⟨j, hj, Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨j.2, hcj.1⟩, hcj.2⟩⟩

private theorem coord_fixed_of_mapJ_eq (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A) {E : Subgroup G}
    (hE : E ≤ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    {x : ↥(E ⊓ J z)} {w : V}
    (hx : (lemma54MapJ (z := z) E) x = spinVecToV h P w) :
    ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
  have hxE : (x : G) ∈ E := (Subgroup.mem_inf.mp x.2).1
  have hxJ : (x : G) ∈ J z := (Subgroup.mem_inf.mp x.2).2
  obtain ⟨u, hu, huσ⟩ := exists_coord_of_mem_J_of_centralizes (z := z) D h P hP hq₂ hxJ
    (lemma54T₂_centralizes (z := z) D (hE hxE))
  have huw : u = w := spinVecToV_injective h P (hu.symm.trans hx)
  rwa [huw] at huσ

private theorem q_coord_of_mapJ_eq (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {E : Subgroup G}
    {x : ↥(E ⊓ J z)} (hx2 : (x : G) * (x : G) = 1) {w : V}
    (hx : (lemma54MapJ (z := z) E) x = spinVecToV h P w) : q w = 0 := by
  have hxJ : (x : G) ∈ J z := (Subgroup.mem_inf.mp x.2).2
  exact q_coord_eq_zero_of_sq_eq_one (z := z) D h P hP (x := ⟨(x : G), hxJ⟩) hx2 hx

private theorem b_coord_of_mapJ_eq (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {E : Subgroup G} (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    {x y : ↥(E ⊓ J z)} {wx wy : V}
    (hx : (lemma54MapJ (z := z) E) x = spinVecToV h P wx)
    (hy : (lemma54MapJ (z := z) E) y = spinVecToV h P wy) : b wx wy = 0 := by
  have hxE : (x : G) ∈ E := (Subgroup.mem_inf.mp x.2).1
  have hyE : (y : G) ∈ E := (Subgroup.mem_inf.mp y.2).1
  have hxy : (x : G) * (y : G) = (y : G) * (x : G) := hcomm _ hxE _ hyE
  exact b_coord_eq_zero_of_commute (z := z) D h P hP hxy hx hy

private theorem card_range_le_four_of_fixed_uv (h : Tim79a.ParrottHyp z) (P : GL8)
    (E : Subgroup G)
    (hσ : ∀ w : V, spinVecToV h P w ∈ (lemma54MapJ (z := z) E).range →
      ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
        (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w)
    (huv : ∀ w : V, spinVecToV h P w ∈ (lemma54MapJ (z := z) E).range →
      ((rhoA (uA * vA) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w) :
    Nat.card ↥(lemma54MapJ (z := z) E).range ≤ 4 := by
  have h := card_range_le_finset (z := z) h P E (T := Finset.univ.filter fun w : V =>
      ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
      ((rhoA (uA * vA) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w) (by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hσ w hw, huv w hw⟩)
  rwa [spin_card_fixed_sigma_uv] at h

private theorem card_range_le_two_of_fixed_uv_t (h : Tim79a.ParrottHyp z) (P : GL8)
    (E : Subgroup G)
    (hσ : ∀ w : V, spinVecToV h P w ∈ (lemma54MapJ (z := z) E).range →
      ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
        (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w)
    (huv : ∀ w : V, spinVecToV h P w ∈ (lemma54MapJ (z := z) E).range →
      ((rhoA (uA * vA) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w)
    (ht : ∀ w : V, spinVecToV h P w ∈ (lemma54MapJ (z := z) E).range →
      ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w) :
    Nat.card ↥(lemma54MapJ (z := z) E).range ≤ 2 := by
  have h := card_range_le_finset (z := z) h P E (T := Finset.univ.filter fun w : V =>
      ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
      ((rhoA (uA * vA) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
        ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w) (by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hσ w hw, huv w hw, ht w hw⟩)
  rwa [spin_card_fixed_sigma_uv_t] at h

private theorem card_range_le_four_of_singular (h : Tim79a.ParrottHyp z) (P : GL8)
    (E : Subgroup G)
    (hσ : ∀ w : V, spinVecToV h P w ∈ (lemma54MapJ (z := z) E).range →
      ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
        (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w)
    (hq : ∀ w : V, spinVecToV h P w ∈ (lemma54MapJ (z := z) E).range → q w = 0)
    (hb : ∀ v w : V, spinVecToV h P v ∈ (lemma54MapJ (z := z) E).range →
      spinVecToV h P w ∈ (lemma54MapJ (z := z) E).range → b v w = 0)
    (h8 : 8 ≤ Nat.card ↥(lemma54MapJ (z := z) E).range) : False := by
  classical
  haveI : Fintype ↥(lemma54MapJ (z := z) E).range := Fintype.ofFinite _
  have hnt : Nontrivial ↥(lemma54MapJ (z := z) E).range := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  haveI := hnt
  obtain ⟨y₁, hy₁⟩ := exists_ne (1 : ↥(lemma54MapJ (z := z) E).range)
  obtain ⟨y₂, hy₂₁, hy₂₂⟩ :
      ∃ y₂ : ↥(lemma54MapJ (z := z) E).range, y₂ ≠ 1 ∧ y₂ ≠ y₁ := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset ↥(lemma54MapJ (z := z) E).range) ⊆
        ({1, y₁} : Finset ↥(lemma54MapJ (z := z) E).range) := by
      intro y _
      by_cases hy : y = 1
      · simp [hy]
      · simp [hcon y hy]
    have hle := Finset.card_le_card hsub
    have h1 : (Finset.univ : Finset ↥(lemma54MapJ (z := z) E).range).card =
        Nat.card ↥(lemma54MapJ (z := z) E).range := by
      rw [Finset.card_univ, Nat.card_eq_fintype_card]
    have h2 : ({1, y₁} : Finset ↥(lemma54MapJ (z := z) E).range).card ≤ 2 := by
      rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact fun h => hy₁ h.symm),
        Finset.card_singleton]
    omega
  obtain ⟨w₁, hw₁⟩ := spinVecToV_surjective h P y₁.1
  obtain ⟨w₂, hw₂⟩ := spinVecToV_surjective h P y₂.1
  have hmem₁ : spinVecToV h P w₁ ∈ (lemma54MapJ (z := z) E).range := by
    rw [hw₁]; exact y₁.2
  have hmem₂ : spinVecToV h P w₂ ∈ (lemma54MapJ (z := z) E).range := by
    rw [hw₂]; exact y₂.2
  have hw₁0 : w₁ ≠ 0 := by
    intro h0
    exact hy₁ (Subtype.ext (by rw [← hw₁, h0, spinVecToV_zero]; rfl))
  have hw₂0 : w₂ ≠ 0 := by
    intro h0
    exact hy₂₁ (Subtype.ext (by rw [← hw₂, h0, spinVecToV_zero]; rfl))
  have hw₁₂ : w₁ ≠ w₂ := by
    intro h0
    exact hy₂₂ (Subtype.ext (by rw [← hw₁, ← hw₂, h0]))
  have hT : ∀ w : V, spinVecToV h P w ∈ (lemma54MapJ (z := z) E).range →
      w ∈ ({0, w₁, w₂, w₁ + w₂} : Finset V) := by
    intro w hw
    have hres := spin_eq_of_singular_fixed_sigma (hσ w₁ hmem₁) (hσ w₂ hmem₂) (hσ w hw)
      (hq w₁ hmem₁) (hq w₂ hmem₂) (hq w hw)
      (hb w₁ w₂ hmem₁ hmem₂) (hb w₁ w hmem₁ hw) (hb w₂ w hmem₂ hw)
      hw₁0 hw₂0 hw₁₂
    rcases hres with h0 | h0 | h0 | h0 <;> simp [h0]
  have hle := card_range_le_finset (z := z) h P E hT
  have hcard4 : ({0, w₁, w₂, w₁ + w₂} : Finset V).card ≤ 4 := by
    have h1 := Finset.card_insert_le (0 : V) ({w₁, w₂, w₁ + w₂} : Finset V)
    have h2 := Finset.card_insert_le (w₁ : V) ({w₂, w₁ + w₂} : Finset V)
    have h3 := Finset.card_insert_le (w₂ : V) ({w₁ + w₂} : Finset V)
    have h4 : ({w₁ + w₂} : Finset V).card = 1 := Finset.card_singleton _
    simp only [h4] at h3
    omega
  omega

private theorem card_range_le_four_of_fixed_tuv (h : Tim79a.ParrottHyp z) (P : GL8)
    (E : Subgroup G)
    (hσ : ∀ w : V, spinVecToV h P w ∈ (lemma54MapJ (z := z) E).range →
      ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
        (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w)
    (htuv : ∀ w : V, spinVecToV h P w ∈ (lemma54MapJ (z := z) E).range →
      ((rhoA (tA * (uA * vA)) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w) :
    Nat.card ↥(lemma54MapJ (z := z) E).range ≤ 4 := by
  have h := card_range_le_finset (z := z) h P E (T := Finset.univ.filter fun w : V =>
      ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∧
      ((rhoA (tA * (uA * vA)) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w) (by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hσ w hw, htuv w hw⟩)
  rwa [spin_card_fixed_sigma_t_uv] at h

private theorem coord_fixed_of_mem_range_of_mapE_eq (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} {E : Subgroup G}
    (hE : E ≤ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {e : ↥E} {q : A45}
    (hqe : lemma54MapE (z := z) D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE e = q)
    {w : V} (hw : spinVecToV h P w ∈ (lemma54MapJ (z := z) E).range) :
    ((rhoA q : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hw
  have hxE : (x : G) ∈ E := (Subgroup.mem_inf.mp x.2).1
  have hxJ : (x : G) ∈ J z := (Subgroup.mem_inf.mp x.2).2
  have heH : (e : G) ∈ H z := lemma54T₂_le_H (z := z) D (hE e.2)
  have hec : (e : G) * (x : G) = (x : G) * (e : G) := hcomm _ e.2 _ hxE
  have hfix := coord_fixed_of_commute (z := z) D h P hP heH hxJ hec hx
  rw [← hqe]
  exact hfix

private theorem card_inf_centerIn_le_two_of_qH_not_mem_QP45
    (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) {E : Subgroup G}
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {e : G} (heE : e ∈ E) (heH : e ∈ H z)
    (hqe : qH (z := z) D ⟨e, heH⟩ ∉
      QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) :
    Nat.card ↥((E ⊓ J z) ⊓ centerIn (J z)) ≤ 2 := by
  classical
  have hcen_not : e ∉ centralizer ({z₁} : Set G) := fun hc =>
    hqe ((mem_centralizer_z1_iff_qH_mem_QP45 (z := z) D h hZ hz₁ hz₁z hord ⟨e, heH⟩).mp hc)
  have hz1 : z ≠ 1 := by
    intro h1
    have hzord : orderOf z = 2 := h.1
    rw [h1, orderOf_one] at hzord
    omega
  have hz2 : z * z = 1 := by
    have hh := pow_orderOf_eq_one z
    rw [show orderOf z = 2 from h.1] at hh
    simpa [pow_two] using hh
  have hsub : (((E ⊓ J z) ⊓ centerIn (J z) : Subgroup G) : Set G) ⊆
      (({1, z} : Finset G) : Set G) := by
    intro ζ hζ
    obtain ⟨hζE₀, hζZ⟩ := Subgroup.mem_inf.mp hζ
    obtain ⟨hζE, -⟩ := Subgroup.mem_inf.mp hζE₀
    have heζ : e * ζ = ζ * e := hcomm e heE ζ hζE
    rcases (mem_centerIn_J_iff (z := z) h hz₁ hz₁z hord).mp hζZ with h1 | h1 | h1 | h1
    · simp [h1]
    · simp [h1]
    · exfalso
      apply hcen_not
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by rwa [h1] at heζ)
    · exfalso
      apply hcen_not
      have hez : e * z = z * e := Subgroup.mem_centralizer_singleton_iff.mp heH
      have hz₁eq : z₁ = z * ζ := by
        rw [h1]
        calc z₁ = (z * z) * z₁ := by rw [hz2, one_mul]
          _ = z * (z * z₁) := by group
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [hz₁eq]
      calc e * (z * ζ) = (e * z) * ζ := by group
        _ = (z * e) * ζ := by rw [hez]
        _ = z * (e * ζ) := by group
        _ = z * (ζ * e) := by rw [heζ]
        _ = (z * ζ) * e := by group
  change Nat.card ↥(((E ⊓ J z) ⊓ centerIn (J z) : Subgroup G) : Set G) ≤ 2
  rw [Nat.card_coe_set_eq]
  calc (((E ⊓ J z) ⊓ centerIn (J z) : Subgroup G) : Set G).ncard
      ≤ (({1, z} : Finset G) : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = ({1, z} : Finset G).card := Set.ncard_coe_finset _
    _ ≤ 2 := by
        have hc := Finset.card_insert_le (1 : G) ({z} : Finset G)
        simp only [Finset.card_singleton] at hc
        omega

private theorem false_of_range_bot (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A) {E : Subgroup G}
    (hE : E ≤ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsq : ∀ a ∈ E, a * a = 1) (hcard : Nat.card E = 32)
    (hbot : Nat.card ↥(lemma54MapE (z := z) D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range = 1) : False := by
  have hE₀card : Nat.card ↥(E ⊓ J z) = 32 := by
    have h := card_eq_card_inf_mul_card_range (z := z) D
      (σ := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) E hE
    rw [hcard, hbot, mul_one] at h
    exact h.symm
  have hker4 : Nat.card ↥((E ⊓ J z) ⊓ centerIn (J z)) ≤ 4 := by
    calc Nat.card ↥((E ⊓ J z) ⊓ centerIn (J z))
        ≤ Nat.card ↥(centerIn (J z)) := Subgroup.card_le_of_le inf_le_right
      _ = 4 := card_centerIn_J h
  have h8 : 8 ≤ Nat.card ↥(lemma54MapJ (z := z) E).range := by
    have h := card_eq_card_inf_centerIn_mul_card_range (z := z) E
    rw [hE₀card] at h
    have hmul := Nat.mul_le_mul_right (Nat.card ↥(lemma54MapJ (z := z) E).range) hker4
    rw [← h] at hmul
    omega
  refine card_range_le_four_of_singular (z := z) h P E ?_ ?_ ?_ h8
  · intro w hw
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hw
    exact coord_fixed_of_mapJ_eq (z := z) D h P hP hq₂ hE hx
  · intro w hw
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hw
    have hxE : (x : G) ∈ E := (Subgroup.mem_inf.mp x.2).1
    exact q_coord_of_mapJ_eq (z := z) D h P hP (x := x) (hsq _ hxE) hx
  · intro v w hv hw
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hv
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hw
    exact b_coord_of_mapJ_eq (z := z) D h P hP hcomm hx hy

private theorem E_inf_J_le_N_of_range_tA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {E : Subgroup G} (hE : E ≤ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {e' : ↥E}
    (hqe' : lemma54MapE (z := z) D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE e' = tA) :
    E ⊓ J z ≤ J z ⊓ centralizer ({
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G) := by
  intro x hx
  obtain ⟨hxE, hxJ⟩ := Subgroup.mem_inf.mp hx
  have hxσ : x ∈ centralizer ({
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) :=
    lemma54T₂_centralizes (z := z) D (hE hxE)
  have hσx : conjV h (sigma1Nine (z := z) D * σ₂⁻¹) (QuotientV.pi z ⟨x, hxJ⟩) =
      QuotientV.pi z ⟨x, hxJ⟩ := by
    rw [conjV_mk h _ ⟨x, hxJ⟩]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hxσ
    rw [← hc]
    group
  obtain ⟨w, hw, -⟩ := exists_coord_of_mem_J_of_centralizes (z := z) D h P hP hq₂ hxJ hxσ
  have he'H : (e' : G) ∈ H z := lemma54T₂_le_H (z := z) D (hE e'.2)
  have hqe'' : qH (z := z) D ⟨(e' : G), he'H⟩ = tA := hqe'
  have he'x : (e' : G) * x = x * (e' : G) := hcomm _ e'.2 _ hxE
  have hfixe' : conjV h ⟨(e' : G), he'H⟩ (QuotientV.pi z ⟨x, hxJ⟩) =
      QuotientV.pi z ⟨x, hxJ⟩ := by
    rw [conjV_mk h _ ⟨x, hxJ⟩]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe, he'x]
    group
  have htA : ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
    have hfix := coord_fixed_of_conjV_fixed (z := z) D h P hP
      (y := ⟨(e' : G), he'H⟩) (by rw [← hw]; exact hfixe')
    rwa [hqe''] at hfix
  have hτx : conjV h τ (QuotientV.pi z ⟨x, hxJ⟩) = QuotientV.pi z ⟨x, hxJ⟩ := by
    rw [hw, conjV_spinVecToV D h P hP, hqτ, htA]
  have hcx := mem_centralizer_of_conjV_pi_eq (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
    ⟨x, hxJ⟩ hσx hτx
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxJ, hcx.1⟩, hcx.2⟩

private theorem E_inf_J_eq_N_of_range_tA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {E : Subgroup G} (hE : E ≤ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE₀card : Nat.card ↥(E ⊓ J z) = 16) {e' : ↥E}
    (hqe' : lemma54MapE (z := z) D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE e' = tA) :
    E ⊓ J z = J z ⊓ centralizer ({
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G) := by
  refine Subgroup.eq_of_le_of_card_ge
    (E_inf_J_le_N_of_range_tA (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ hE hcomm hqe') ?_
  rw [hE₀card, card_lemma54N (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂]

private theorem tau_mul_mem_N_of_range_tA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {E : Subgroup G} (hE : E ≤ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEN : E ⊓ J z = J z ⊓ centralizer ({
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G)) {e' : ↥E}
    (hqe' : lemma54MapE (z := z) D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE e' = tA) :
    (τ : G) * (e' : G) ∈ J z ⊓ centralizer ({
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G) := by
  let y : G := (τ : G) * (e' : G)
  have he'H : (e' : G) ∈ H z := lemma54T₂_le_H (z := z) D (hE e'.2)
  have hyH : y ∈ H z := (H z).mul_mem τ.2 he'H
  have hqe'' : qH (z := z) D ⟨(e' : G), he'H⟩ = tA := hqe'
  have htt : tA * tA = 1 := Subtype.ext t_sq
  have hyq : qH (z := z) D ⟨y, hyH⟩ = 1 := by
    show qH (z := z) D (⟨(τ : G), τ.2⟩ * ⟨(e' : G), he'H⟩) = 1
    rw [map_mul, hqτ, hqe'', htt]
  have hyJ : y ∈ J z :=
    Subgroup.mem_subgroupOf.mp ((J_mem_iff (z := z) D ⟨y, hyH⟩).mpr hyq)
  have hcommH : τ * (sigma1Nine (z := z) D * σ₂⁻¹) = (sigma1Nine (z := z) D * σ₂⁻¹) * τ := by
    have h2 : τ * σ₂⁻¹ = σ₂⁻¹ * τ := (show Commute τ σ₂ from hτ₂).inv_right.eq
    calc τ * (sigma1Nine (z := z) D * σ₂⁻¹) = (τ * sigma1Nine D) * σ₂⁻¹ := by group
      _ = (sigma1Nine (z := z) D * τ) * σ₂⁻¹ := by rw [hτ₁]
      _ = sigma1Nine (z := z) D * (τ * σ₂⁻¹) := by group
      _ = sigma1Nine (z := z) D * (σ₂⁻¹ * τ) := by rw [h2]
      _ = (sigma1Nine (z := z) D * σ₂⁻¹) * τ := by group
  have hτσ : (τ : G) ∈ centralizer ({
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcommH)
  have hyσ : y ∈ centralizer ({
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) :=
    Subgroup.mul_mem _ hτσ (lemma54T₂_centralizes (z := z) D (hE e'.2))
  obtain ⟨wy, hwy, hwyσ⟩ := exists_coord_of_mem_J_of_centralizes (z := z) D h P hP hq₂ hyJ hyσ
  have hE2 : ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
      (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinE2
        = spinE2 ∧ ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinE2 = spinE2 :=
    (spin_fixed_sigma_t_iff spinE2).mpr (Or.inr (Or.inl rfl))
  obtain ⟨j₂, hj₂, hj₂N⟩ := exists_mem_N_of_coord (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
    hE2.1 hE2.2
  have hW0 : ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
      (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0
        = spinW0 ∧ ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ spinW0 = spinW0 :=
    (spin_fixed_sigma_t_iff spinW0).mpr (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨j₀, hj₀, hj₀N⟩ := exists_mem_N_of_coord (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
    hW0.1 hW0.2
  have hmemN : ∀ {j : J z}, (j : G) ∈ J z ⊓ centralizer ({
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G) → y * (j : G) = (j : G) * y := by
    intro j hj
    have hjE : (j : G) ∈ E := by
      have h : (j : G) ∈ E ⊓ J z := by rw [hEN]; exact hj
      exact (Subgroup.mem_inf.mp h).1
    have hτj : (τ : G) * (j : G) = (j : G) * (τ : G) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hj).2).symm
    have he'j : (e' : G) * (j : G) = (j : G) * (e' : G) := hcomm _ e'.2 _ hjE
    calc y * (j : G) = ((τ : G) * (e' : G)) * (j : G) := rfl
      _ = (τ : G) * ((e' : G) * (j : G)) := by group
      _ = (τ : G) * ((j : G) * (e' : G)) := by rw [he'j]
      _ = ((τ : G) * (j : G)) * (e' : G) := by group
      _ = ((j : G) * (τ : G)) * (e' : G) := by rw [hτj]
      _ = (j : G) * ((τ : G) * (e' : G)) := by group
      _ = (j : G) * y := rfl
  have hb₀ : b spinW0 wy = 0 := by
    have hpolar : polarVZMod h (QuotientV.pi z j₀) (QuotientV.pi z ⟨y, hyJ⟩) = 0 :=
      (polarVZMod_pi_eq_zero_iff h j₀ ⟨y, hyJ⟩).mpr (hmemN hj₀N).symm
    rw [hj₀, hwy, polarVZMod_spinVecToV_eq_b D h P hP] at hpolar
    exact hpolar
  have hb₂ : b spinE2 wy = 0 := by
    have hpolar : polarVZMod h (QuotientV.pi z j₂) (QuotientV.pi z ⟨y, hyJ⟩) = 0 :=
      (polarVZMod_pi_eq_zero_iff h j₂ ⟨y, hyJ⟩).mpr (hmemN hj₂N).symm
    rw [hj₂, hwy, polarVZMod_spinVecToV_eq_b D h P hP] at hpolar
    exact hpolar
  have htwy : ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ wy = wy :=
    spin_fixed_t_of_fixed_sigma_of_b hwyσ hb₂ hb₀
  have hτy : conjV h τ (QuotientV.pi z ⟨y, hyJ⟩) = QuotientV.pi z ⟨y, hyJ⟩ := by
    rw [hwy, conjV_spinVecToV D h P hP, hqτ, htwy]
  have hσy : conjV h (sigma1Nine (z := z) D * σ₂⁻¹) (QuotientV.pi z ⟨y, hyJ⟩) =
      QuotientV.pi z ⟨y, hyJ⟩ := by
    rw [conjV_mk h _ ⟨y, hyJ⟩]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hyσ
    rw [← hc]
    group
  have hcy := mem_centralizer_of_conjV_pi_eq (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
    ⟨y, hyJ⟩ hσy hτy
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hyJ, hcy.1⟩, hcy.2⟩

private theorem false_of_range_meets (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A) {E : Subgroup G}
    (hE : E ≤ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsq : ∀ a ∈ E, a * a = 1) (hcard : Nat.card E = 32)
    (hcase : uA * vA ∈ (lemma54MapE (z := z) D
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range ∨
      tA * (uA * vA) ∈ (lemma54MapE (z := z) D
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range) : False := by
  classical
  have hrangeK := lemma54MapE_range_le (z := z) D E hE
  obtain ⟨e, heq⟩ : ∃ e : ↥E, lemma54MapE (z := z) D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE e = uA * vA ∨
      lemma54MapE (z := z) D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE e =
        tA * (uA * vA) := by
    rcases hcase with h1 | h1
    · obtain ⟨e, he⟩ := MonoidHom.mem_range.mp h1
      exact ⟨e, Or.inl he⟩
    · obtain ⟨e, he⟩ := MonoidHom.mem_range.mp h1
      exact ⟨e, Or.inr he⟩
  have heH : (e : G) ∈ H z := lemma54T₂_le_H (z := z) D (hE e.2)
  have hqe' : qH (z := z) D ⟨(e : G), heH⟩ =
      lemma54MapE (z := z) D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE e := rfl
  have htuv : tA * (uA * vA) = uA * vA * tA := by
    have hc : Commute tA (uA * vA) :=
      (show Commute tA uA from Subtype.ext t_commute_u).mul_right
        (show Commute tA vA from Subtype.ext t_commute_v)
    exact hc.eq
  have hqenot : qH (z := z) D ⟨(e : G), heH⟩ ∉
      QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
    rw [hqe']
    rcases heq with h1 | h1
    · rw [h1]; exact uvA_not_mem_QP45
    · rw [h1, htuv]; exact uvtA_not_mem_QP45
  have hZcard := card_inf_centerIn_le_two_of_qH_not_mem_QP45 (z := z) D h hZ hz₁ hz₁z hord
    hcomm e.2 heH hqenot
  have hσrange : ∀ w : V, spinVecToV h P w ∈ (lemma54MapJ (z := z) E).range →
      ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
        (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
    intro w hw
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hw
    exact coord_fixed_of_mapJ_eq (z := z) D h P hP hq₂ hE hx
  have hrange4 : Nat.card ↥(lemma54MapJ (z := z) E).range ≤ 4 := by
    rcases heq with h1 | h1
    · refine card_range_le_four_of_fixed_uv (z := z) h P E hσrange ?_
      intro w hw
      have h := coord_fixed_of_mem_range_of_mapE_eq (z := z) D h P hP hE hcomm hqe' hw
      rwa [h1] at h
    · refine card_range_le_four_of_fixed_tuv (z := z) h P E hσrange ?_
      intro w hw
      have h := coord_fixed_of_mem_range_of_mapE_eq (z := z) D h P hP hE hcomm hqe' hw
      rwa [h1] at h
  have hE₀le8 : Nat.card ↥(E ⊓ J z) ≤ 8 := by
    have h := card_eq_card_inf_centerIn_mul_card_range (z := z) E
    have hmul := Nat.mul_le_mul hZcard hrange4
    rw [← h] at hmul
    omega
  have hdvd : Nat.card ↥(lemma54MapE (z := z) D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range ∣ 2 ^ 2 := by
    have hd := Subgroup.card_dvd_of_le hrangeK
    rwa [card_closure_t_uv] at hd
  have hne1 : Nat.card ↥(lemma54MapE (z := z) D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range ≠ 1 := by
    intro h1
    have hbot : (lemma54MapE (z := z) D
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ h1
    have hmem : lemma54MapE (z := z) D
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE e ∈
        (lemma54MapE (z := z) D
          ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range := ⟨e, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    rcases heq with h | h
    · exact one_ne_uvA (hmem.symm.trans h)
    · exact one_ne_tA_uvA (hmem.symm.trans h)
  obtain ⟨k, hk, hk2⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases k with _ | _ | _ | k
  · exact hne1 (by simpa using hk2)
  · have h2 : Nat.card ↥(lemma54MapE (z := z) D
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range = 2 := by
      simpa using hk2
    have h16 : Nat.card ↥(E ⊓ J z) = 16 := by
      have h := card_eq_card_inf_mul_card_range (z := z) D
        (σ := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) E hE
      rw [hcard, h2] at h
      omega
    omega
  · have h4 : Nat.card ↥(lemma54MapE (z := z) D
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range = 4 := by
      simpa using hk2
    have h8 : Nat.card ↥(E ⊓ J z) = 8 := by
      have h := card_eq_card_inf_mul_card_range (z := z) D
        (σ := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) E hE
      rw [hcard, h4] at h
      omega
    have hrangeK' : (lemma54MapE (z := z) D
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range =
        Subgroup.closure ({tA, uA * vA} : Set A45) :=
      Subgroup.eq_of_le_of_card_ge hrangeK (by rw [card_closure_t_uv, h4])
    have htAmem : tA ∈ (lemma54MapE (z := z) D
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range := by
      rw [hrangeK']; exact Subgroup.subset_closure (by simp)
    have huvmem : uA * vA ∈ (lemma54MapE (z := z) D
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range := by
      rw [hrangeK']; exact Subgroup.subset_closure (by simp)
    obtain ⟨et, het⟩ := MonoidHom.mem_range.mp htAmem
    obtain ⟨euv, heuv⟩ := MonoidHom.mem_range.mp huvmem
    have hrange2 : Nat.card ↥(lemma54MapJ (z := z) E).range ≤ 2 := by
      refine card_range_le_two_of_fixed_uv_t (z := z) h P E hσrange ?_ ?_
      · intro w hw
        exact coord_fixed_of_mem_range_of_mapE_eq (z := z) D h P hP hE hcomm heuv hw
      · intro w hw
        exact coord_fixed_of_mem_range_of_mapE_eq (z := z) D h P hP hE hcomm het hw
    have hle4 : Nat.card ↥(E ⊓ J z) ≤ 4 := by
      have h := card_eq_card_inf_centerIn_mul_card_range (z := z) E
      have hmul := Nat.mul_le_mul hZcard hrange2
      rw [← h] at hmul
      omega
    omega
  · omega

set_option maxHeartbeats 2000000 in
private theorem E_le_W_of_range_tA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {E : Subgroup G} (hE : E ≤ lemma54T₂ D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsub : ∀ x : E, ∃ hxH : (x : G) ∈ H z,
      qH (z := z) D ⟨(x : G), hxH⟩ = 1 ∨ qH (z := z) D ⟨(x : G), hxH⟩ = tA)
    (hE₀card : Nat.card ↥(E ⊓ J z) = 16)
    {e' : G} (he'E : e' ∈ E) (he'H : e' ∈ H z)
    (hqe' : qH (z := z) D ⟨e', he'H⟩ = tA) :
    E ≤ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) := by
  have hqe'map : lemma54MapE (z := z) D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE
      ⟨e', he'E⟩ = tA := hqe'
  have hEN := E_inf_J_eq_N_of_range_tA (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ hE hcomm
    hE₀card (e' := ⟨e', he'E⟩) hqe'map
  have hyN := tau_mul_mem_N_of_range_tA (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hE hcomm
    hEN (e' := ⟨e', he'E⟩) hqe'map
  have hτ2 : (τ : G) * (τ : G) = 1 := by simpa using congrArg Subtype.val hτ
  have he'W : e' ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) := by
    have hτW : (τ : G) ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hyW : ((τ : G) * e') ∈
        lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) :=
      Subgroup.mem_sup_left hyN
    have hmul := (lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)).mul_mem
      hτW hyW
    rwa [show (τ : G) * ((τ : G) * e') = e' by
      rw [← mul_assoc, hτ2, one_mul]] at hmul
  intro x hx
  obtain ⟨hxH, hqx⟩ := hsub ⟨x, hx⟩
  have hxH' : x ∈ H z := lemma54T₂_le_H (z := z) D (hE hx)
  have hqx' : qH (z := z) D ⟨x, hxH'⟩ = 1 ∨ qH (z := z) D ⟨x, hxH'⟩ = tA := hqx
  rcases hqx' with h1 | h1
  · have hxJ : x ∈ J z :=
      Subgroup.mem_subgroupOf.mp ((J_mem_iff (z := z) D ⟨x, hxH'⟩).mpr h1)
    have hxN : x ∈ J z ⊓ centralizer ({
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
        centralizer ({(τ : G)} : Set G) := by
      rw [← hEN]
      exact Subgroup.mem_inf.mpr ⟨hx, hxJ⟩
    exact Subgroup.mem_sup_left hxN
  · have hxHinv : ((e')⁻¹ * x) ∈ H z := (H z).mul_mem ((H z).inv_mem he'H) hxH'
    have hker : qH (z := z) D ⟨(e')⁻¹ * x, hxHinv⟩ = 1 := by
      have hsplit : (⟨(e')⁻¹ * x, hxHinv⟩ : ↥(H z)) = ⟨e', he'H⟩⁻¹ * ⟨x, hxH'⟩ :=
        Subtype.ext rfl
      rw [hsplit, map_mul, map_inv, h1, hqe']
      exact inv_mul_cancel tA
    have hxJ : (e')⁻¹ * x ∈ J z :=
      Subgroup.mem_subgroupOf.mp ((J_mem_iff (z := z) D ⟨_, hxHinv⟩).mpr hker)
    have hinv : (e')⁻¹ ∈ E := Subgroup.inv_mem E he'E
    have hxE : (e')⁻¹ * x ∈ E := Subgroup.mul_mem E hinv hx
    have hxN : (e')⁻¹ * x ∈ J z ⊓ centralizer ({
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
        centralizer ({(τ : G)} : Set G) := by
      rw [← hEN]
      exact Subgroup.mem_inf.mpr ⟨hxE, hxJ⟩
    have hxeq : x = e' * ((e')⁻¹ * x) := by group
    rw [hxeq]
    exact (lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)).mul_mem
      he'W (Subgroup.mem_sup_left hxN)

private theorem eq_lemma54W_of_range_tA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {E : Subgroup G} (hE : E ≤ lemma54T₂ D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hcard : Nat.card E = 32)
    (hsub : ∀ x : E, ∃ hxH : (x : G) ∈ H z,
      qH (z := z) D ⟨(x : G), hxH⟩ = 1 ∨ qH (z := z) D ⟨(x : G), hxH⟩ = tA)
    (hE₀card : Nat.card ↥(E ⊓ J z) = 16)
    {e' : G} (he'E : e' ∈ E) (he'H : e' ∈ H z)
    (hqe' : qH (z := z) D ⟨e', he'H⟩ = tA) :
    E = lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) := by
  refine Subgroup.eq_of_le_of_card_ge
    (E_le_W_of_range_tA (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hE hcomm hsub hE₀card
      he'E he'H hqe') ?_
  rw [hcard, card_lemma54W (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂]

private theorem conj_mem_lemma54W_of_coord (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {c : ↥(H z)}
    (hcσ : c * (sigma1Nine (z := z) D * σ₂⁻¹) = (sigma1Nine (z := z) D * σ₂⁻¹) * c)
    {j : G} (hjJ : j ∈ J z)
    (hjσ : j ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    {w : V} (hw : QuotientV.pi z ⟨j, hjJ⟩ = spinVecToV h P w)
    (hwσ : ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
      (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w)
    (hwt : ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
        (((rhoA (qH (z := z) D c) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) =
      ((rhoA (qH (z := z) D c) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) :
    (c : G) * j * (c : G)⁻¹ ∈
      lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) := by
  have hqσ : qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) =
      (⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹ := by
    rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
  have hqcomm : qH (z := z) D c * qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) =
      qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) * qH (z := z) D c := by
    rw [← map_mul, ← map_mul, hcσ]
  have hqcomm' : qH (z := z) D c * ((⟨sigma1, sigma1_mem_A⟩ : A45) *
      (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) =
      ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) *
        qH (z := z) D c := by
    rw [← hqσ]
    exact hqcomm
  have hmat : ((rhoA (qH (z := z) D c) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *
      ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *
        ((rhoA (qH (z := z) D c) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
    have h1 : (rhoA (qH (z := z) D c) : GL8) *
        rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) =
        rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) *
          rhoA (qH (z := z) D c) := by
      rw [← map_mul, ← map_mul]
      exact congrArg rhoA hqcomm'
    have h2' := congrArg (fun z : GL8 => (z : Matrix (Fin 8) (Fin 8) (ZMod 2))) h1
    simpa only [Units.val_mul] using h2'
  have hσw' : ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
      (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
      (((rhoA (qH (z := z) D c) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) =
      ((rhoA (qH (z := z) D c) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w := by
    rw [Matrix.mulVec_mulVec, ← hmat, ← Matrix.mulVec_mulVec, hwσ]
  have hPix' : QuotientV.pi z (conjJ' z c ⟨j, hjJ⟩) = spinVecToV h P
      (((rhoA (qH (z := z) D c) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) := by
    rw [← conjV_mk h c ⟨j, hjJ⟩, hw, conjV_spinVecToV D h P hP]
  have hσx' : conjV h (sigma1Nine (z := z) D * σ₂⁻¹)
      (QuotientV.pi z (conjJ' z c ⟨j, hjJ⟩)) =
      QuotientV.pi z (conjJ' z c ⟨j, hjJ⟩) := by
    rw [hPix', conjV_spinVecToV D h P hP, hqσ, hσw']
  have hτx' : conjV h τ (QuotientV.pi z (conjJ' z c ⟨j, hjJ⟩)) =
      QuotientV.pi z (conjJ' z c ⟨j, hjJ⟩) := by
    rw [hPix', conjV_spinVecToV D h P hP, hqτ, hwt]
  have hc' := mem_centralizer_of_conjV_pi_eq (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
    (conjJ' z c ⟨j, hjJ⟩) hσx' hτx'
  have hmem : ((conjJ' z c ⟨j, hjJ⟩ : J z) : G) ∈
      J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
        centralizer ({(τ : G)} : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨(conjJ' z c ⟨j, hjJ⟩).2, hc'.1⟩, hc'.2⟩
  have hcoe : ((conjJ' z c ⟨j, hjJ⟩ : J z) : G) = (c : G) * j * (c : G)⁻¹ := by
    rw [conjJ'_apply_coe]
  rw [← hcoe]
  exact Subgroup.mem_sup_left hmem

private theorem range_subset_tA_of_not_meets
    (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A) {E : Subgroup G}
    (hE : E ≤ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (hcase : ¬ (uA * vA ∈ (lemma54MapE (z := z) D
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range ∨
      tA * (uA * vA) ∈ (lemma54MapE (z := z) D
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range)) :
    (∀ q ∈ (lemma54MapE (z := z) D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range, q = 1 ∨ q = tA) ∧
      Nat.card ↥(lemma54MapE (z := z) D
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range ≤ 2 := by
  classical
  have hsub : ∀ q ∈ (lemma54MapE (z := z) D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range, q = 1 ∨ q = tA := by
    intro q hq
    rcases (mem_closure_t_uv_iff q).mp (lemma54MapE_range_le (z := z) D E hE hq) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (h ▸ hq) (fun hh => hcase (Or.inl hh))
    · exact absurd (h ▸ hq) (fun hh => hcase (Or.inr hh))
  refine ⟨hsub, ?_⟩
  have hsub' : ((lemma54MapE (z := z) D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range : Set A45) ⊆
      (({1, tA} : Finset A45) : Set A45) := by
    intro q hq
    rcases hsub q hq with h | h <;> simp [h]
  change Nat.card ↥(((lemma54MapE (z := z) D
    ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range : Set A45)) ≤ 2
  rw [Nat.card_coe_set_eq]
  calc ((lemma54MapE (z := z) D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range : Set A45).ncard
      ≤ (({1, tA} : Finset A45) : Set A45).ncard := Set.ncard_le_ncard hsub' (Set.toFinite _)
    _ = ({1, tA} : Finset A45).card := Set.ncard_coe_finset _
    _ ≤ 2 := by
        have hc := Finset.card_insert_le (1 : A45) ({tA} : Finset A45)
        simp only [Finset.card_singleton] at hc
        omega

private theorem tA_mem_range_of_card_two {σ₂ : ↥(H z)} (E : Subgroup G)
    (hE : E ≤ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (hsub : ∀ q ∈ (lemma54MapE (z := z) D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range, q = 1 ∨ q = tA)
    (hcard2 : Nat.card ↥(lemma54MapE (z := z) D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range = 2) :
    tA ∈ (lemma54MapE (z := z) D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range := by
  classical
  have hsub' : ((lemma54MapE (z := z) D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range : Set A45) ⊆
      (({1, tA} : Finset A45) : Set A45) := by
    intro q hq
    rcases hsub q hq with h | h <;> simp [h]
  have hset : ((lemma54MapE (z := z) D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range : Set A45) =
      (({1, tA} : Finset A45) : Set A45) := by
    apply Set.eq_of_subset_of_ncard_le hsub'
    rw [Set.ncard_coe_finset]
    have hrn : ((lemma54MapE (z := z) D
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range : Set A45).ncard = 2 := by
      rw [← Nat.card_coe_set_eq]
      exact hcard2
    have hc := Finset.card_insert_le (1 : A45) ({tA} : Finset A45)
    simp only [Finset.card_singleton] at hc
    omega
  change tA ∈ (((lemma54MapE (z := z) D
    ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range : Subgroup A45) : Set A45)
  rw [hset]
  simp

theorem eq_lemma54W_of_le_lemma54T₂
    (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    ∀ E : Subgroup G, E ≤ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) →
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a * a = 1) → Nat.card E = 32 →
        E = lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) := by
  intro E hE hcomm hsq hcard
  classical
  by_cases hcase : uA * vA ∈ (lemma54MapE (z := z) D
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range ∨
      tA * (uA * vA) ∈ (lemma54MapE (z := z) D
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range
  · exact False.elim (false_of_range_meets (z := z) D h hZ hz₁ hz₁z hord P hP hq₂ hE hcomm
      hsq hcard hcase)
  · obtain ⟨hsub, hcard2⟩ := range_subset_tA_of_not_meets (z := z) D h P hP hq₂ hE hcase
    rcases Nat.lt_or_ge (Nat.card ↥(lemma54MapE (z := z) D
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range) 2 with hlt | hge
    · have hrange1 : Nat.card ↥(lemma54MapE (z := z) D
          ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range = 1 := by
        have hpos : 0 < Nat.card ↥(lemma54MapE (z := z) D
            ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range := Nat.card_pos
        omega
      exact False.elim (false_of_range_bot (z := z) D h P hP hq₂ hE hcomm hsq hcard hrange1)
    · have hrange2 : Nat.card ↥(lemma54MapE (z := z) D
          ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) E hE).range = 2 := by omega
      have hE₀card : Nat.card ↥(E ⊓ J z) = 16 := by
        have h := card_eq_card_inf_mul_card_range (z := z) D
          (σ := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) E hE
        rw [hcard, hrange2] at h
        omega
      have htAmem := tA_mem_range_of_card_two (z := z) D E hE hsub hrange2
      obtain ⟨e', he'⟩ := MonoidHom.mem_range.mp htAmem
      have he'H : (e' : G) ∈ H z := lemma54T₂_le_H (z := z) D (hE e'.2)
      have hqe'' : qH (z := z) D ⟨(e' : G), he'H⟩ = tA := he'
      have hsubQ : ∀ x : E, ∃ hxH : (x : G) ∈ H z,
          qH (z := z) D ⟨(x : G), hxH⟩ = 1 ∨ qH (z := z) D ⟨(x : G), hxH⟩ = tA := by
        intro x
        exact ⟨lemma54T₂_le_H (z := z) D (hE x.2), hsub _ ⟨x, rfl⟩⟩
      exact eq_lemma54W_of_range_tA (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hE hcomm
        hcard hsubQ hE₀card e'.2 he'H hqe''

private theorem exists_conj_mem_lemma54W_of_alternatives (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {j : G} (hjJ : j ∈ J z)
    (hjσ : j ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    {w : V} (hw : QuotientV.pi z ⟨j, hjJ⟩ = spinVecToV h P w)
    (hσw : ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
      (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w)
    {γ : ↥(H z)} (hqγ : qH (z := z) D γ = SpinWords.wordElem spinGWord)
    (hγσ : γ * (sigma1Nine (z := z) D * σ₂⁻¹) =
      (sigma1Nine (z := z) D * σ₂⁻¹) * γ)
    (halt : ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w ∨
      ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
        (((rhoA (SpinWords.wordElem spinGWord) : GL8) :
          Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) =
        ((rhoA (SpinWords.wordElem spinGWord) : GL8) :
          Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w ∨
      ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
        (((rhoA (SpinWords.wordElem spinGWord * SpinWords.wordElem spinGWord) : GL8) :
          Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) =
        ((rhoA (SpinWords.wordElem spinGWord * SpinWords.wordElem spinGWord) : GL8) :
          Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) :
    ∃ c ∈ H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G),
      c * j * c⁻¹ ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) := by
  rcases halt with h1 | h2 | h3
  · refine ⟨1, Subgroup.mem_inf.mpr ⟨Subgroup.one_mem _,
      Subgroup.mem_centralizer_singleton_iff.mpr (by simp)⟩, ?_⟩
    have hmain := conj_mem_lemma54W_of_coord (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
      (c := 1) (by simp) hjJ hjσ hw hσw (by simpa using h1)
    simpa using hmain
  · refine ⟨(γ : G), Subgroup.mem_inf.mpr ⟨γ.2,
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hγσ)⟩, ?_⟩
    have hwt : ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
        (((rhoA (qH (z := z) D γ) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) =
        ((rhoA (qH (z := z) D γ) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w := by
      rw [hqγ]
      exact h2
    exact conj_mem_lemma54W_of_coord (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
      (c := γ) hγσ hjJ hjσ hw hσw hwt
  · have hcσ : (γ * γ) * (sigma1Nine (z := z) D * σ₂⁻¹) =
        (sigma1Nine (z := z) D * σ₂⁻¹) * (γ * γ) := by
      rw [mul_assoc, hγσ, ← mul_assoc, hγσ, mul_assoc]
    refine ⟨((γ * γ : ↥(H z)) : G), Subgroup.mem_inf.mpr
      ⟨(H z).mul_mem γ.2 γ.2,
        Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcσ)⟩, ?_⟩
    have hqγγ : qH (z := z) D (γ * γ) =
        SpinWords.wordElem spinGWord * SpinWords.wordElem spinGWord := by
      rw [map_mul, hqγ]
    have hwt : ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
        (((rhoA (qH (z := z) D (γ * γ)) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w) =
        ((rhoA (qH (z := z) D (γ * γ)) : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w := by
      rw [hqγγ]
      exact h3
    exact conj_mem_lemma54W_of_coord (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
      (c := γ * γ) hcσ hjJ hjσ hw hσw hwt

theorem exists_conj_mem_lemma54W
    (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    ∀ j ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G),
      orderOf j = 2 →
        ∃ c ∈ H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G),
          c * j * c⁻¹ ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) := by
  intro j hj hjord
  obtain ⟨hjJ, hjσ⟩ := Subgroup.mem_inf.mp hj
  have hj2 : j * j = 1 := by
    have h := pow_orderOf_eq_one j
    rw [hjord] at h
    simpa [pow_two] using h
  obtain ⟨w, hw'⟩ := spinVecToV_surjective h P (QuotientV.pi z ⟨j, hjJ⟩)
  have hw : QuotientV.pi z ⟨j, hjJ⟩ = spinVecToV h P w := hw'.symm
  have hσw : ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
      (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
    refine coord_fixed_sigma1Nine_mul_inv (z := z) D h P hP hq₂ ?_
    rw [← hw, conjV_mk h _ ⟨j, hjJ⟩]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hjσ
    rw [← hc]
    group
  have hqw : q w = 0 := by
    have hqj : qJ h ⟨j, hjJ⟩ = 1 := by
      apply Subtype.ext
      rw [qJ_coe]
      simpa [pow_two] using hj2
    have hqv : qV h (QuotientV.pi z ⟨j, hjJ⟩) = 1 := by
      rw [qV_pi]
      exact hqj
    have hqvz : qVZMod h (QuotientV.pi z ⟨j, hjJ⟩) = 0 :=
      (qVZMod_eq_zero_iff h _).mpr hqv
    rw [← qVZMod_spinVecToV_eq_q D h P hP w, ← hw]
    exact hqvz
  have hqσ : qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) =
      (⟨sigma1, sigma1_mem_A⟩ : A45) * (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹ := by
    rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
  have hσh3 : orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3 := by
    rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂⁻¹)]
    exact orderOf_sigma1Nine_mul_inv (z := z) D h hσ₂ hq₂ hc₂
  have hcomm_g : SpinWords.wordElem spinGWord * qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) =
      qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) * SpinWords.wordElem spinGWord := by
    rw [hqσ]
    exact wordElem_spinGWord_comm
  obtain ⟨γ, hqγ, hγσ⟩ := exists_lift_centralizer (z := z) (D := D)
    (r := (sigma1Nine (z := z) D * σ₂⁻¹)) (g := SpinWords.wordElem spinGWord) hσh3 hcomm_g
  exact exists_conj_mem_lemma54W_of_alternatives (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
    hjJ hjσ hw hσw hqγ hγσ (spin_fixed_t_or_of_singular_fixed_sigma hσw hqw)

private theorem tA_mul_self : tA * tA = 1 := Subtype.ext t_sq

private theorem tau_mem_centralizer_sigma {σ₂ τ : ↥(H z)}
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    (τ : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) := by
  have h2 : τ * σ₂⁻¹ = σ₂⁻¹ * τ := (show Commute τ σ₂ from hτ₂).inv_right.eq
  have hcomm : τ * (sigma1Nine (z := z) D * σ₂⁻¹) =
      (sigma1Nine (z := z) D * σ₂⁻¹) * τ := by
    calc τ * (sigma1Nine (z := z) D * σ₂⁻¹) = (τ * sigma1Nine D) * σ₂⁻¹ := by group
      _ = (sigma1Nine (z := z) D * τ) * σ₂⁻¹ := by rw [hτ₁]
      _ = sigma1Nine (z := z) D * (τ * σ₂⁻¹) := by group
      _ = sigma1Nine (z := z) D * (σ₂⁻¹ * τ) := by rw [h2]
      _ = (sigma1Nine (z := z) D * σ₂⁻¹) * τ := by group
  exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcomm)

private theorem tau_mul_tau_mul_inv {τ x : ↥(H z)} (hτ : τ * τ = 1) (hx : (x : G) * x = 1) :
    (τ : G) * (((τ * x : ↥(H z)) : G)) * (τ : G)⁻¹ = (((τ * x : ↥(H z)) : G))⁻¹ := by
  have hτG : (τ : G) * (τ : G) = 1 := by simpa using congrArg Subtype.val hτ
  have hxG : (x : G) * (x : G) = 1 := hx
  have hcoe : (((τ * x : ↥(H z)) : G)) = (τ : G) * (x : G) := rfl
  rw [hcoe]
  calc (τ : G) * ((τ : G) * (x : G)) * (τ : G)⁻¹
      = ((τ : G) * (τ : G) * (x : G)) * (τ : G)⁻¹ := by group
    _ = (1 * (x : G)) * (τ : G)⁻¹ := by rw [hτG]
    _ = (x : G) * (τ : G)⁻¹ := by rw [one_mul]
    _ = (x : G) * (τ : G) := by rw [inv_eq_of_mul_eq_one_right hτG]
    _ = ((τ : G) * (x : G))⁻¹ := by
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hxG, inv_eq_of_mul_eq_one_right hτG]

private theorem pi_inv_eq_pi (h : Tim79a.ParrottHyp z) (y : J z) :
    QuotientV.pi z y⁻¹ = QuotientV.pi z y := by
  rw [map_inv]
  have h2 : QuotientV.pi z y * QuotientV.pi z y = 1 := by
    have := QuotientV.pow_two_eq_one_V h (QuotientV.pi z y)
    rwa [pow_two] at this
  exact inv_eq_of_mul_eq_one_right h2

theorem mem_lemma54W_of_qH_eq_tA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    (x : ↥(H z))
    (hxσ : (x : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hx : (x : G) * x = 1) (hqx : qH (z := z) D x = tA) :
    (x : G) ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) := by
  have hτG : (τ : G) * (τ : G) = 1 := by simpa using congrArg Subtype.val hτ
  have hqH : qH (z := z) D (τ * x) = 1 := by
    rw [map_mul, hqτ, hqx, tA_mul_self]
  have hqJ : (((τ * x : ↥(H z)) : G)) ∈ J z :=
    Subgroup.mem_subgroupOf.mp ((J_mem_iff (z := z) D (τ * x)).mpr hqH)
  let qJ : J z := ⟨(((τ * x : ↥(H z)) : G)), hqJ⟩
  have hqσ : (qJ : G) ∈ centralizer ({
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) := by
    have h := Subgroup.mul_mem (Subgroup.centralizer ({
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
      (tau_mem_centralizer_sigma (z := z) D hτ₁ hτ₂) hxσ
    simpa [qJ] using h
  have hconj : conjJ' z τ qJ = qJ⁻¹ := by
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    simpa [qJ] using tau_mul_tau_mul_inv (z := z) (τ := τ) (x := x) hτ hx
  have hτfix : conjV h τ (QuotientV.pi z qJ) = QuotientV.pi z qJ := by
    rw [conjV_mk h τ qJ, hconj, pi_inv_eq_pi (z := z) h qJ]
  have hσfix : conjV h (sigma1Nine (z := z) D * σ₂⁻¹) (QuotientV.pi z qJ) =
      QuotientV.pi z qJ := by
    rw [conjV_mk h _ qJ]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hqσ
    rw [← hc]
    group
  have hqC := mem_centralizer_of_conjV_pi_eq (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
    qJ hσfix hτfix
  rw [mem_lemma54W_iff (z := z) (τ := (τ : G)) hτG]
  right
  have hmem : (qJ : G) ∈ J z ⊓ centralizer ({
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨qJ.2, hqC.1⟩, hqC.2⟩
  simpa [qJ] using hmem

theorem z_mem_lemma54W (h : Tim79a.ParrottHyp z) {σ τ : ↥(H z)} :
    z ∈ lemma54W z (σ : G) (τ : G) := by
  refine Subgroup.mem_sup_left (Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_inf.mpr ⟨z_mem_J h, ?_⟩, ?_⟩)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp σ.2).symm
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp τ.2).symm

end CFSG.RankThree.GF2n.Parrott
