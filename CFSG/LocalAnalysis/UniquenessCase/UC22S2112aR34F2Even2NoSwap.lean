module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2PGL
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul
import CFSG.LinearAlgebra.LinearGroups.PGLTwoPPart

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped MatrixGroups Pointwise

private theorem uc22s2112r34_noswap_images {X : Type*} [Group X]
    [Finite X] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {F : Type*} [Field F] [Finite F] [CharP F p]
    {K P B : Subgroup X}
    (ρ : normalizer (K : Set X) →* PGL(Fin 2, F))
    (hρ : ∀ g, ρ g = 1 ↔ ∀ k ∈ K, (g : X) * k * (g : X)⁻¹ = k)
    (hP : IsPGroup 2 P) (hPN : P ≤ normalizer (K : Set X)) (hBN : B ≤ normalizer (K : Set X))
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBo : Odd (Nat.card B))
    (hpB : 5 ≤ p ∨ ¬ p ∣ Nat.card B) (hBP : (B : Set X) * P = P * B)
    (hQ : ¬ IsCyclic (((P ⊓ K).subgroupOf (normalizer (K : Set X))).map ρ))
    (hout : ∃ w ∈ P, ∀ k ∈ K, ∃ y ∈ K, w * y * w⁻¹ ≠ k * y * k⁻¹) :
    (∀ a ∈ (B.subgroupOf (normalizer (K : Set X))).map ρ,
      ∀ b ∈ (B.subgroupOf (normalizer (K : Set X))).map ρ, a * b = b * a) ∧
    Odd (Nat.card ((B.subgroupOf (normalizer (K : Set X))).map ρ)) ∧
    IsPGroup 2 ((P.subgroupOf (normalizer (K : Set X))).map ρ) ∧
    ¬ IsCyclic ((P.subgroupOf (normalizer (K : Set X))).map ρ) ∧
    8 ≤ Nat.card ((P.subgroupOf (normalizer (K : Set X))).map ρ) ∧
    (((B.subgroupOf (normalizer (K : Set X))).map ρ : Set PGL(Fin 2, F)) *
        ((P.subgroupOf (normalizer (K : Set X))).map ρ : Set PGL(Fin 2, F)) =
      ((P.subgroupOf (normalizer (K : Set X))).map ρ : Set PGL(Fin 2, F)) *
        ((B.subgroupOf (normalizer (K : Set X))).map ρ : Set PGL(Fin 2, F))) ∧
    ¬ p ∣ Nat.card ((B.subgroupOf (normalizer (K : Set X))).map ρ ⊔
      (P.subgroupOf (normalizer (K : Set X))).map ρ : Subgroup PGL(Fin 2, F)) ∧
    ((P ⊓ K).subgroupOf (normalizer (K : Set X))).map ρ ≤
      (P.subgroupOf (normalizer (K : Set X))).map ρ := by
  have : Finite PGL(Fin 2, F) := by
    unfold Matrix.ProjGenLinGroup
    infer_instance
  have hBcard : Nat.card (B.subgroupOf (normalizer (K : Set X))) = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv
  have hP' : IsPGroup 2 (P.subgroupOf (normalizer (K : Set X))) :=
    hP.of_equiv (subgroupOfEquivOfLe hPN).symm
  have hQS : ((P ⊓ K).subgroupOf (normalizer (K : Set X))).map ρ ≤
      (P.subgroupOf (normalizer (K : Set X))).map ρ :=
    map_mono fun y hy => mem_subgroupOf.2 (mem_subgroupOf.1 hy).1
  have hBP' : ((B.subgroupOf (normalizer (K : Set X)) : Subgroup (normalizer (K : Set X))) :
        Set (normalizer (K : Set X))) *
        (P.subgroupOf (normalizer (K : Set X)) : Subgroup (normalizer (K : Set X))) =
      (P.subgroupOf (normalizer (K : Set X)) : Subgroup (normalizer (K : Set X))) *
        (B.subgroupOf (normalizer (K : Set X)) : Subgroup (normalizer (K : Set X))) :=
    CFSG.Quasithin.H23P4.mul_comm_subgroupOf hBN hPN hBP
  have hSc : ¬ IsCyclic ((P.subgroupOf (normalizer (K : Set X))).map ρ) := fun h =>
    hQ (Subgroup.isCyclic_of_le hQS)
  have hYc : ∀ a ∈ (B.subgroupOf (normalizer (K : Set X))).map ρ,
      ∀ b ∈ (B.subgroupOf (normalizer (K : Set X))).map ρ, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc _ (mem_subgroupOf.1 ha) _ (mem_subgroupOf.1 hb))
  have hYo : Odd (Nat.card ((B.subgroupOf (normalizer (K : Set X))).map ρ)) :=
    Odd.of_dvd_nat hBo (hBcard ▸ Subgroup.card_map_dvd _ ρ)
  have hYS : (((B.subgroupOf (normalizer (K : Set X))).map ρ : Set PGL(Fin 2, F)) *
        ((P.subgroupOf (normalizer (K : Set X))).map ρ : Set PGL(Fin 2, F)) =
      ((P.subgroupOf (normalizer (K : Set X))).map ρ : Set PGL(Fin 2, F)) *
        ((B.subgroupOf (normalizer (K : Set X))).map ρ : Set PGL(Fin 2, F))) := by
    rw [coe_map, coe_map, ← Set.image_mul, ← Set.image_mul, hBP']
  have hpY : ¬ p ∣ Nat.card ((B.subgroupOf (normalizer (K : Set X))).map ρ) := by
    rcases hpB with hp5 | hpB
    · exact CFSG.LinearGroups.not_dvd_card_of_comm_permutes_noncyclic_two hp5 hYc hYo
        (hP'.map ρ) hSc hYS
    · exact fun h => hpB (h.trans (hBcard ▸ Subgroup.card_map_dvd _ ρ))
  refine ⟨hYc, hYo, hP'.map ρ, hSc, ?_, hYS, ?_, hQS⟩
  ·
    obtain ⟨w, hwP, hw⟩ := hout
    have hwS : ρ ⟨w, hPN hwP⟩ ∈ (P.subgroupOf (normalizer (K : Set X))).map ρ :=
      mem_map_of_mem _ (mem_subgroupOf.2 hwP)
    have hwQ : ρ ⟨w, hPN hwP⟩ ∉ ((P ⊓ K).subgroupOf (normalizer (K : Set X))).map ρ := by
      rintro ⟨q, hq, hqw⟩
      have hqK : (q : X) ∈ K := (mem_subgroupOf.1 hq).2
      obtain ⟨y, hy, hne⟩ := hw q hqK
      have h1 : ρ (q⁻¹ * ⟨w, hPN hwP⟩) = 1 := by rw [map_mul, map_inv, hqw, inv_mul_cancel]
      have h2 := (hρ _).1 h1 y hy
      apply hne
      simp only [coe_mul, coe_inv] at h2
      calc w * y * w⁻¹ = (q : X) * ((q : X)⁻¹ * w * y * ((q : X)⁻¹ * w)⁻¹) * (q : X)⁻¹ := by
            group
        _ = (q : X) * y * (q : X)⁻¹ := by rw [h2]
    have hlt : ((P ⊓ K).subgroupOf (normalizer (K : Set X))).map ρ ≠
        (P.subgroupOf (normalizer (K : Set X))).map ρ := fun h =>
      hwQ (h ▸ hwS)
    have h4 : 4 ≤ Nat.card (((P ⊓ K).subgroupOf (normalizer (K : Set X))).map ρ) := by
      by_contra h4
      apply hQ
      interval_cases hc : Nat.card (((P ⊓ K).subgroupOf (normalizer (K : Set X))).map ρ)
      · exact absurd hc Nat.card_pos.ne'
      · have := (Nat.card_eq_one_iff_unique.1 hc).1
        infer_instance
      · exact isCyclic_of_prime_card (p := 2) hc
      · exact isCyclic_of_prime_card (p := 3) hc
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hQS
    have hm1 : m ≠ 1 := by
      rintro rfl
      exact hlt (Subgroup.eq_of_le_of_card_ge hQS (by rw [hm, mul_one]))
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact Nat.card_pos.ne' (by rw [hm, mul_zero])
    rw [hm]
    nlinarith [Nat.two_le_iff m |>.2 ⟨hm0, hm1⟩]
  ·
    intro hpd
    obtain ⟨n, hn⟩ := (hP'.map ρ).exists_card_eq
    have hd : Nat.card ((B.subgroupOf (normalizer (K : Set X))).map ρ ⊔
          (P.subgroupOf (normalizer (K : Set X))).map ρ : Subgroup PGL(Fin 2, F)) =
        Nat.card ((B.subgroupOf (normalizer (K : Set X))).map ρ) *
          Nat.card ((P.subgroupOf (normalizer (K : Set X))).map ρ) := by
      refine CFSG.Quasithin.H23P4.card_eq_mul_of_coe_eq_mul
        (CFSG.Quasithin.H23P4.coe_sup_eq_mul_of_mul_comm hYS) ?_
      refine Subgroup.inf_eq_bot_of_coprime ?_
      rw [hn]
      exact Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hYo)
    rw [hd, hn] at hpd
    rcases (Nat.Prime.dvd_mul Fact.out).1 hpd with h | h
    · exact hpY h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1
        ((Nat.Prime.dvd_of_dvd_pow Fact.out h)))

@[expose] def UC22NoSwapInput {X : Type*} [Group X] (p : ℕ) (P K₁ K₂ : Subgroup X) :
    Prop :=
  centralizer (K₁ : Set X) ≤ K₂ ∧ centralizer (K₂ : Set X) ≤ K₁ ∧
    (∀ K ∈ ({K₁, K₂} : Set (Subgroup X)), ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (_ : CharP F p) (ρ : normalizer (K : Set X) →* PGL(Fin 2, F)),
      (∀ g, ρ g = 1 ↔ ∀ k ∈ K, (g : X) * k * (g : X)⁻¹ = k) ∧
      (P ≤ normalizer (K : Set X) →
        ¬ IsCyclic (((P ⊓ K).subgroupOf (normalizer (K : Set X))).map ρ))) ∧
    (P ≤ normalizer (K₁ : Set X) → P ≤ normalizer (K₂ : Set X) →
      ∀ K ∈ ({K₁, K₂} : Set (Subgroup X)), ∃ w ∈ P, ∀ k ∈ K, ∃ y ∈ K,
        w * y * w⁻¹ ≠ k * y * k⁻¹)

theorem UC22NoSwapInput.symm {X : Type*} [Group X] {p : ℕ} {P K₁ K₂ : Subgroup X}
    (h : UC22NoSwapInput p P K₁ K₂) : UC22NoSwapInput p P K₂ K₁ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨h₂, h₁, ?_, fun hP₂ hP₁ => ?_⟩
  · rw [Set.pair_comm]
    exact h₃
  · rw [Set.pair_comm]
    exact h₄ hP₁ hP₂

theorem uc22s2112r34_noswap_outer_of_not_mem {X : Type*} [Group X] {K₁ K₂ : Subgroup X}
    (hC₁ : centralizer (K₁ : Set X) ≤ K₂) (hC₂ : centralizer (K₂ : Set X) ≤ K₁) {w : X}
    (hw : w ∉ K₁ ⊔ K₂) :
    ∀ K ∈ ({K₁, K₂} : Set (Subgroup X)), ∀ k ∈ K, ∃ y ∈ K, w * y * w⁻¹ ≠ k * y * k⁻¹ := by
  have hout : ∀ A B : Subgroup X, centralizer (A : Set X) ≤ B → w ∉ A ⊔ B →
      ∀ k ∈ A, ∃ y ∈ A, w * y * w⁻¹ ≠ k * y * k⁻¹ := by
    intro A B hAB hwAB k hk
    by_contra h
    push Not at h
    apply hwAB
    have hc : k⁻¹ * w ∈ centralizer (A : Set X) := by
      rw [mem_centralizer_iff]
      intro y hy
      calc y * (k⁻¹ * w) = k⁻¹ * (k * y * k⁻¹) * w := by group
        _ = k⁻¹ * (w * y * w⁻¹) * w := by rw [h y hy]
        _ = k⁻¹ * w * y := by group
    have hw' : w = k * (k⁻¹ * w) := by group
    rw [hw']
    exact mul_mem (mem_sup_left hk) (mem_sup_right (hAB hc))
  intro K hK
  obtain rfl | rfl := hK
  · exact hout _ _ hC₁ hw
  · exact hout _ _ hC₂ (by rwa [sup_comm])


theorem uc22s2112r34_noswap_exists_inverter {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {F₁ F₂ : Type*} [Field F₁] [Finite F₁] [CharP F₁ p]
    [Field F₂] [Finite F₂] [CharP F₂ p] {K₁ K₂ P B : Subgroup X}
    (ρ₁ : normalizer (K₁ : Set X) →* PGL(Fin 2, F₁))
    (ρ₂ : normalizer (K₂ : Set X) →* PGL(Fin 2, F₂))
    (hρ₁ : ∀ g, ρ₁ g = 1 ↔ ∀ k ∈ K₁, (g : X) * k * (g : X)⁻¹ = k)
    (hρ₂ : ∀ g, ρ₂ g = 1 ↔ ∀ k ∈ K₂, (g : X) * k * (g : X)⁻¹ = k)
    (hK12 : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hP : IsPGroup 2 P) (hPN₁ : P ≤ normalizer (K₁ : Set X))
    (hPN₂ : P ≤ normalizer (K₂ : Set X)) (hBN₁ : B ≤ normalizer (K₁ : Set X))
    (hBN₂ : B ≤ normalizer (K₂ : Set X)) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBo : Odd (Nat.card B)) (hpB : 5 ≤ p ∨ ¬ p ∣ Nat.card B) (hBP : (B : Set X) * P = P * B)
    (hQ₁ : ¬ IsCyclic (((P ⊓ K₁).subgroupOf (normalizer (K₁ : Set X))).map ρ₁))
    (hQ₂ : ¬ IsCyclic (((P ⊓ K₂).subgroupOf (normalizer (K₂ : Set X))).map ρ₂))
    (hout₁ : ∃ w ∈ P, ∀ k ∈ K₁, ∃ y ∈ K₁, w * y * w⁻¹ ≠ k * y * k⁻¹)
    (hout₂ : ∃ w ∈ P, ∀ k ∈ K₂, ∃ y ∈ K₂, w * y * w⁻¹ ≠ k * y * k⁻¹)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) {x : X} (hxB : x ∈ B) (hxr : orderOf x = r)
    (hx₁ : ∃ k ∈ K₁, x * k * x⁻¹ ≠ k) :
    ∃ u ∈ P, ∀ b ∈ B, ∀ k ∈ K₁ ⊔ K₂,
      (u * b * u⁻¹) * k * (u * b * u⁻¹)⁻¹ = b⁻¹ * k * b := by
  obtain ⟨hY₁c, hY₁o, hS₁2, -, hS₁8, hY₁S₁, hp₁, hQS₁⟩ :=
    uc22s2112r34_noswap_images hp2 ρ₁ hρ₁ hP hPN₁ hBN₁ hBc hBo hpB hBP hQ₁ hout₁
  obtain ⟨hY₂c, hY₂o, hS₂2, hS₂c, hS₂8, hY₂S₂, hp₂, -⟩ :=
    uc22s2112r34_noswap_images hp2 ρ₂ hρ₂ hP hPN₂ hBN₂ hBc hBo hpB hBP hQ₂ hout₂
  have hrY : r ∣ Nat.card ((B.subgroupOf (normalizer (K₁ : Set X))).map ρ₁) := by
    have hmem : ρ₁ ⟨x, hBN₁ hxB⟩ ∈ (B.subgroupOf (normalizer (K₁ : Set X))).map ρ₁ :=
      mem_map_of_mem _ (mem_subgroupOf.2 hxB)
    have hdvd : orderOf (ρ₁ ⟨x, hBN₁ hxB⟩) ∣ r := by
      rw [← hxr]
      exact (orderOf_map_dvd ρ₁ _).trans (by rw [Subgroup.orderOf_mk])
    have hne : orderOf (ρ₁ ⟨x, hBN₁ hxB⟩) ≠ 1 := by
      rw [Ne, orderOf_eq_one_iff, hρ₁]
      obtain ⟨k, hk, hxk⟩ := hx₁
      exact fun h => hxk (h k hk)
    have hord : orderOf (ρ₁ ⟨x, hBN₁ hxB⟩) = r :=
      ((Nat.dvd_prime hr).1 hdvd).resolve_left hne
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ hmem
  obtain ⟨π₂, hπ₂S, hπ₂⟩ :=
    uc22s2112r34_pgl_exists_inv hY₂c hY₂o hS₂2 hS₂c hS₂8 hY₂S₂ hp₂
  obtain ⟨w', hw'P, rfl⟩ := mem_map.1 hπ₂S
  have hwP : (w' : X) ∈ P := mem_subgroupOf.1 hw'P
  obtain ⟨⟨h₁, hh₁S, hh₁⟩, hdich⟩ :=
    uc22s2112r34_pgl_inv_or_comm hY₁o hS₁2 hS₁8 hp₁ hr hr5 hrY hQS₁ hQ₁
  obtain ⟨s', hs'PK, rfl⟩ := mem_map.1 hh₁S
  have hsPK : (s' : X) ∈ P ⊓ K₁ := mem_subgroupOf.1 hs'PK
  set w₁ : normalizer (K₁ : Set X) := ⟨(w' : X), hPN₁ hwP⟩ with hw₁
  have hw₁S : ρ₁ w₁ ∈ (P.subgroupOf (normalizer (K₁ : Set X))).map ρ₁ :=
    mem_map_of_mem _ (mem_subgroupOf.2 hwP)
  have hs₂ : ρ₂ ⟨(s' : X), hPN₂ hsPK.1⟩ = 1 := by
    rw [hρ₂]
    intro k hk
    rw [hK12 _ hsPK.2 k hk, mul_inv_cancel_right]
  obtain ⟨u, huP, hu₁, hu₂⟩ : ∃ u, ∃ huP : u ∈ P,
      (∀ b (hb : b ∈ B), ρ₁ ⟨u, hPN₁ huP⟩ * ρ₁ ⟨b, hBN₁ hb⟩ * (ρ₁ ⟨u, hPN₁ huP⟩)⁻¹ =
        (ρ₁ ⟨b, hBN₁ hb⟩)⁻¹) ∧
      ∀ b (hb : b ∈ B), ρ₂ ⟨u, hPN₂ huP⟩ * ρ₂ ⟨b, hBN₂ hb⟩ * (ρ₂ ⟨u, hPN₂ huP⟩)⁻¹ =
        (ρ₂ ⟨b, hBN₂ hb⟩)⁻¹ := by
    have hY₁mem : ∀ b (hb : b ∈ B),
        ρ₁ ⟨b, hBN₁ hb⟩ ∈ (B.subgroupOf (normalizer (K₁ : Set X))).map ρ₁ :=
      fun b hb => mem_map_of_mem _ (mem_subgroupOf.2 hb)
    have hY₂mem : ∀ b (hb : b ∈ B),
        ρ₂ ⟨b, hBN₂ hb⟩ ∈ (B.subgroupOf (normalizer (K₂ : Set X))).map ρ₂ :=
      fun b hb => mem_map_of_mem _ (mem_subgroupOf.2 hb)
    have hw₂ : (⟨(w' : X), hPN₂ hwP⟩ : normalizer (K₂ : Set X)) = w' := rfl
    rcases hdich _ hw₁S with hinv | hcomm
    · refine ⟨w', hwP, fun b hb => hinv _ (hY₁mem b hb), fun b hb => ?_⟩
      rw [hw₂]
      exact hπ₂ _ (hY₂mem b hb)
    · refine ⟨(s' : X) * w', P.mul_mem hsPK.1 hwP, fun b hb => ?_, fun b hb => ?_⟩
      · have hsplit : (⟨(s' : X) * w', hPN₁ (P.mul_mem hsPK.1 hwP)⟩ :
            normalizer (K₁ : Set X)) = s' * w₁ := rfl
        rw [hsplit, map_mul, mul_inv_rev]
        calc ρ₁ s' * ρ₁ w₁ * ρ₁ ⟨b, hBN₁ hb⟩ * ((ρ₁ w₁)⁻¹ * (ρ₁ s')⁻¹)
            = ρ₁ s' * (ρ₁ w₁ * ρ₁ ⟨b, hBN₁ hb⟩ * (ρ₁ w₁)⁻¹) * (ρ₁ s')⁻¹ := by group
          _ = ρ₁ s' * ρ₁ ⟨b, hBN₁ hb⟩ * (ρ₁ s')⁻¹ := by rw [hcomm _ (hY₁mem b hb)]
          _ = (ρ₁ ⟨b, hBN₁ hb⟩)⁻¹ := hh₁ _ (hY₁mem b hb)
      · have hsplit : (⟨(s' : X) * w', hPN₂ (P.mul_mem hsPK.1 hwP)⟩ :
            normalizer (K₂ : Set X)) = ⟨(s' : X), hPN₂ hsPK.1⟩ * w' := rfl
        rw [hsplit, map_mul, hs₂, one_mul]
        exact hπ₂ _ (hY₂mem b hb)
  refine ⟨u, huP, fun b hb k hk => ?_⟩
  have hc₁ : ∀ y ∈ K₁, (u * b * u⁻¹ * b) * y * (u * b * u⁻¹ * b)⁻¹ = y := by
    have hcN : u * b * u⁻¹ * b ∈ normalizer (K₁ : Set X) :=
      mul_mem (mul_mem (mul_mem (hPN₁ huP) (hBN₁ hb)) (inv_mem (hPN₁ huP))) (hBN₁ hb)
    have h1 : ρ₁ ⟨_, hcN⟩ = 1 := by
      have heq : (⟨_, hcN⟩ : normalizer (K₁ : Set X)) =
          ⟨u, hPN₁ huP⟩ * ⟨b, hBN₁ hb⟩ * (⟨u, hPN₁ huP⟩)⁻¹ * ⟨b, hBN₁ hb⟩ := rfl
      rw [heq, map_mul, map_mul, map_mul, map_inv, hu₁ b hb, inv_mul_cancel]
    exact (hρ₁ _).1 h1
  have hc₂ : ∀ y ∈ K₂, (u * b * u⁻¹ * b) * y * (u * b * u⁻¹ * b)⁻¹ = y := by
    have hcN : u * b * u⁻¹ * b ∈ normalizer (K₂ : Set X) :=
      mul_mem (mul_mem (mul_mem (hPN₂ huP) (hBN₂ hb)) (inv_mem (hPN₂ huP))) (hBN₂ hb)
    have h1 : ρ₂ ⟨_, hcN⟩ = 1 := by
      have heq : (⟨_, hcN⟩ : normalizer (K₂ : Set X)) =
          ⟨u, hPN₂ huP⟩ * ⟨b, hBN₂ hb⟩ * (⟨u, hPN₂ huP⟩)⁻¹ * ⟨b, hBN₂ hb⟩ := rfl
      rw [heq, map_mul, map_mul, map_mul, map_inv, hu₂ b hb, inv_mul_cancel]
    exact (hρ₂ _).1 h1
  have hcK : K₁ ⊔ K₂ ≤ centralizer ({u * b * u⁻¹ * b} : Set X) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [mem_centralizer_singleton_iff]
      have h := hc₁ y hy
      calc y * (u * b * u⁻¹ * b) = (u * b * u⁻¹ * b) * y * (u * b * u⁻¹ * b)⁻¹ *
          (u * b * u⁻¹ * b) := by rw [h]
        _ = (u * b * u⁻¹ * b) * y := by group
    · rw [mem_centralizer_singleton_iff]
      have h := hc₂ y hy
      calc y * (u * b * u⁻¹ * b) = (u * b * u⁻¹ * b) * y * (u * b * u⁻¹ * b)⁻¹ *
          (u * b * u⁻¹ * b) := by rw [h]
        _ = (u * b * u⁻¹ * b) * y := by group
  have hbk : b⁻¹ * k * b ∈ K₁ ⊔ K₂ := by
    have hconj : ∀ {K : Subgroup X}, b ∈ normalizer (K : Set X) → ∀ y ∈ K, b⁻¹ * y * b ∈ K := by
      intro K hbK y hy
      have h := (mem_normalizer_iff.1 (inv_mem hbK) y).1 hy
      rwa [inv_inv] at h
    have hle : K₁ ⊔ K₂ ≤ (K₁ ⊔ K₂).comap (MulAut.conj b⁻¹).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · change (MulAut.conj b⁻¹) y ∈ K₁ ⊔ K₂
        rw [MulAut.conj_apply, inv_inv]
        exact mem_sup_left (hconj (hBN₁ hb) y hy)
      · change (MulAut.conj b⁻¹) y ∈ K₁ ⊔ K₂
        rw [MulAut.conj_apply, inv_inv]
        exact mem_sup_right (hconj (hBN₂ hb) y hy)
    have h := hle hk
    change (MulAut.conj b⁻¹) k ∈ K₁ ⊔ K₂ at h
    rwa [MulAut.conj_apply, inv_inv] at h
  have hcomm := mem_centralizer_singleton_iff.1 (hcK hbk)
  calc (u * b * u⁻¹) * k * (u * b * u⁻¹)⁻¹
      = (u * b * u⁻¹ * b) * (b⁻¹ * k * b) * (u * b * u⁻¹ * b)⁻¹ := by group
    _ = (b⁻¹ * k * b) * (u * b * u⁻¹ * b) * (u * b * u⁻¹ * b)⁻¹ := by rw [← hcomm]
    _ = b⁻¹ * k * b := by group

end CFSG.LocalAnalysis.UniquenessCase.UC22
