module

public import CFSG.Milestones.ASVolI.F48.D43.EPar
public import Certificates.Certificate7811
public import Certificates.Certificate7812
public import Certificates.Certificate7813
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Milestones.ASVolI.F48.Rest.U52Lie

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable CFSG.Quasithin

theorem burnsideF48dE_ev_rep {G : Type*} [Group G] {m : ℕ} (h : Fin m → G) (a : Fin m) (k : ℕ) :
    burnsideF48s_ev h (List.replicate k (a, true)) = h a ^ k := by
  induction k with
  | zero => rw [List.replicate_zero, pow_zero]; rfl
  | succ k ih =>
    rw [List.replicate_succ, burnsideF48s_ev_cons, ih, pow_succ']
    rfl

@[expose] def burnsideF48dE_KW : List (List (Fin 18 × Bool)) :=
  (List.range 3).flatMap fun e => (List.range 2).flatMap fun j => (List.range 26).map fun i =>
    List.replicate i ((3 : Fin 18), true) ++ List.replicate j ((4 : Fin 18), true) ++
      List.replicate e ((2 : Fin 18), true)

theorem burnsideF48dE_mem_KW {w : List (Fin 18 × Bool)} : w ∈ burnsideF48dE_KW ↔
    ∃ e < 3, ∃ j < 2, ∃ i < 26, w = List.replicate i ((3 : Fin 18), true) ++
      List.replicate j ((4 : Fin 18), true) ++ List.replicate e ((2 : Fin 18), true) := by
  simp only [burnsideF48dE_KW, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨e, he, j, hj, i, hi, rfl⟩
    exact ⟨e, he, j, hj, i, hi, rfl⟩
  · rintro ⟨e, he, j, hj, i, hi, rfl⟩
    exact ⟨e, he, j, hj, i, hi, rfl⟩

theorem burnsideF48dE_mem_KWT {w : List (Fin 17 × Bool)} : w ∈ burnsideF48d_KW ↔
    ∃ j < 2, ∃ i < 26, w = List.replicate i ((2 : Fin 17), true) ++
      List.replicate j ((3 : Fin 17), true) := by
  simp only [burnsideF48d_KW, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨j, hj, i, hi, rfl⟩
    exact ⟨j, hj, i, hi, rfl⟩
  · rintro ⟨j, hj, i, hi, rfl⟩
    exact ⟨j, hj, i, hi, rfl⟩

theorem burnsideF48dE_ev_KWT (i j : ℕ) :
    burnsideF48s_ev burnsideF48d_L (List.replicate i ((2 : Fin 17), true) ++
      List.replicate j ((3 : Fin 17), true)) = burnsideF48d_L 2 ^ i * burnsideF48d_L 3 ^ j := by
  rw [burnsideF48s_ev_append, burnsideF48dE_ev_rep, burnsideF48dE_ev_rep]

theorem burnsideF48dE_ev_KW (e j i : ℕ) :
    burnsideF48s_ev burnsideF48dE_L (List.replicate i ((3 : Fin 18), true) ++
      List.replicate j ((4 : Fin 18), true) ++ List.replicate e ((2 : Fin 18), true)) =
      burnsideF48dE_ι (burnsideF48d_L 2 ^ i * burnsideF48d_L 3 ^ j) * burnsideF48dE_F ^ e := by
  rw [burnsideF48s_ev_append, burnsideF48s_ev_append, burnsideF48dE_ev_rep, burnsideF48dE_ev_rep,
    burnsideF48dE_ev_rep, map_mul, map_pow, map_pow, burnsideF48dE_ι_L, burnsideF48dE_ι_L,
    burnsideF48dE_L_two]
  rfl

theorem burnsideF48dE_L_mem_T {i : Fin 17} (h2 : 2 ≤ (i : ℕ)) (h4 : (i : ℕ) ≤ 4) :
    burnsideF48d_L i ∈ burnsideF48d_T :=
  Subgroup.subset_closure ⟨i, ⟨h2, h4⟩, rfl⟩

theorem burnsideF48dE_T_inj (hM : burnsideF48d_ModelFacts) {i j : ℕ} (hi : i < 26) (hj : j < 2)
    (h : burnsideF48d_L 2 ^ i * burnsideF48d_L 3 ^ j = 1) : i = 0 ∧ j = 0 := by
  have h2 : burnsideF48d_L 2 ∈ burnsideF48d_T := burnsideF48dE_L_mem_T (by decide) (by decide)
  have h3 : burnsideF48d_L 3 ∈ burnsideF48d_T := burnsideF48dE_L_mem_T (by decide) (by decide)
  let φ : Fin 26 × Fin 2 → ↥burnsideF48d_T := fun p =>
    ⟨burnsideF48d_L 2 ^ (p.1 : ℕ) * burnsideF48d_L 3 ^ (p.2 : ℕ),
      burnsideF48d_T.mul_mem (burnsideF48d_T.pow_mem h2 _) (burnsideF48d_T.pow_mem h3 _)⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨c, hc⟩
    obtain ⟨w, hw, hwc⟩ := hM.KW_cov c hc
    obtain ⟨j', hj', i', hi', rfl⟩ := burnsideF48dE_mem_KWT.1 hw
    refine ⟨(⟨i', hi'⟩, ⟨j', hj'⟩), Subtype.ext ?_⟩
    show burnsideF48d_L 2 ^ i' * burnsideF48d_L 3 ^ j' = c
    rw [← hwc, burnsideF48dE_ev_KWT]
  have hbij := hsurj.bijective_of_nat_card_le (by
    rw [hM.card_T, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 26),
      Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, Fintype.card_fin])
  have h0 : φ (⟨i, hi⟩, ⟨j, hj⟩) = φ (⟨0, by norm_num⟩, ⟨0, by norm_num⟩) := by
    apply Subtype.ext
    show burnsideF48d_L 2 ^ i * burnsideF48d_L 3 ^ j = burnsideF48d_L 2 ^ 0 * burnsideF48d_L 3 ^ 0
    rw [h, pow_zero, pow_zero, mul_one]
  have := hbij.1 h0
  simp only [Prod.mk.injEq, Fin.mk.injEq] at this
  exact this

section Engine


theorem burnsideF48dE_restrict (c : ℕ) :
    restrictWords (subsetOf 18 burnsideF48dE_S1) (burnsideF48dE_Ws c) = burnsideF48dE_WsP1 := by
  have hmem : ((1 : Fin 18), true) ∈ burnsideF48s_eCandRel 6 [((0 : Fin 18), true)]
      [((1 : Fin 18), true)] (List.replicate c ((2 : Fin 18), true)) := by
    simp only [burnsideF48s_eCandRel, List.mem_append, List.mem_flatten, List.mem_replicate]
    exact Or.inl ⟨_, ⟨by norm_num, rfl⟩, List.mem_append_right _ (List.mem_singleton_self _)⟩
  have hn := burnsideF48t_renumber_none (S := subsetOf 18 burnsideF48dE_S1) hmem
    (show (1 : Fin 18) ∉ subsetOf 18 burnsideF48dE_S1 by decide)
  simp only [burnsideF48dE_Ws, burnsideF48s_eWs, burnsideF48dE_WsP1, restrictWords,
    List.filterMap_append, List.filterMap_cons, hn, List.filterMap_nil, List.append_nil]

theorem burnsideF48dE_card_WsP1 :
    Finite (PG (subsetOf 18 burnsideF48dE_S1).length burnsideF48dE_WsP1) ∧
      Nat.card (PG (subsetOf 18 burnsideF48dE_S1).length burnsideF48dE_WsP1) ≤ 2321334288 := by
  obtain ⟨-, -, h3⟩ := Certificates.certificate7813
  obtain ⟨fP, dP⟩ := CFSG.KC.MiscCoset.card_le_of_index_restrict burnsideF48dE_WsP1 _ h3
    Certificates.certificate7811
  exact ⟨fP, dP.trans (by norm_num)⟩

theorem burnsideF48dE_tc0 :
    Finite (PG 18 (burnsideF48dE_Ws 0)) ∧
      Nat.card (PG 18 (burnsideF48dE_Ws 0)) ≤ 61682494700736 := by
  have hr : Finite (PG (subsetOf 18 burnsideF48dE_S1).length
        (restrictWords (subsetOf 18 burnsideF48dE_S1) (burnsideF48dE_Ws 0))) ∧
      Nat.card (PG (subsetOf 18 burnsideF48dE_S1).length
        (restrictWords (subsetOf 18 burnsideF48dE_S1) (burnsideF48dE_Ws 0))) ≤ 2321334288 := by
    rw [burnsideF48dE_restrict]
    exact burnsideF48dE_card_WsP1
  obtain ⟨f0, d0⟩ := CFSG.KC.MiscCoset.card_le_of_index_restrict (burnsideF48dE_Ws 0) _
    Certificates.certificate7812 hr
  exact ⟨f0, d0.trans (by norm_num)⟩

theorem burnsideF48dE_tc12 {e : ℕ} (he : e = 1 ∨ e = 2) :
    Finite (PG 18 (burnsideF48dE_Ws e)) ∧ Nat.card (PG 18 (burnsideF48dE_Ws e)) ≤ 2321334288 := by
  have hr : Finite (PG (subsetOf 18 burnsideF48dE_S1).length
        (restrictWords (subsetOf 18 burnsideF48dE_S1) (burnsideF48dE_Ws e))) ∧
      Nat.card (PG (subsetOf 18 burnsideF48dE_S1).length
        (restrictWords (subsetOf 18 burnsideF48dE_S1) (burnsideF48dE_Ws e))) ≤ 2321334288 := by
    rw [burnsideF48dE_restrict]
    exact burnsideF48dE_card_WsP1
  obtain ⟨h1, h2, -⟩ := Certificates.certificate7813
  have hi : (genSub {r : FreeGroup (Fin 18) | r ∈ (burnsideF48dE_Ws e).map FreeGroup.mk}
        (subsetOf 18 burnsideF48dE_S1)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 18) | r ∈ (burnsideF48dE_Ws e).map FreeGroup.mk}
        (subsetOf 18 burnsideF48dE_S1)).index ≤ 1 := by
    rcases he with rfl | rfl
    · exact h1
    · exact h2
  obtain ⟨f0, d0⟩ := CFSG.KC.MiscCoset.card_le_of_index_restrict (burnsideF48dE_Ws e) _ hi hr
  exact ⟨f0, d0.trans (by norm_num)⟩

theorem burnsideF48dE_F_comm_xy (hM : burnsideF48d_ModelFacts) :
    burnsideF48dE_F * burnsideF48dE_ι (burnsideF48d_L 0 * burnsideF48d_L 1) =
      burnsideF48dE_ι (burnsideF48d_L 0 * burnsideF48d_L 1) * burnsideF48dE_F := by
  apply Subtype.ext
  show burnsideF48d_frob * (burnsideF48d_σ 0 * burnsideF48d_σ 1) =
    burnsideF48d_σ 0 * burnsideF48d_σ 1 * burnsideF48d_frob
  rw [← mul_assoc, burnsideF48dE_frob_comm_x hM, mul_assoc, burnsideF48dE_frob_comm_y hM,
    mul_assoc]

theorem burnsideF48dE_ev_x :
    burnsideF48s_ev burnsideF48dE_L [((0 : Fin 18), true)] =
      burnsideF48dE_ι (burnsideF48d_L 0) := by
  rw [burnsideF48s_ev_cons, burnsideF48s_ev_nil, mul_one, ← burnsideF48dE_L_zero]
  rfl

theorem burnsideF48dE_ev_y :
    burnsideF48s_ev burnsideF48dE_L [((1 : Fin 18), true)] =
      burnsideF48dE_ι (burnsideF48d_L 1) := by
  rw [burnsideF48s_ev_cons, burnsideF48s_ev_nil, mul_one, ← burnsideF48dE_L_one]
  rfl

theorem burnsideF48dE_comm_cand (hM : burnsideF48d_ModelFacts) {e i j : ℕ} (hi : i < 26)
    (hj : j < 2)
    (h : burnsideF48s_ev burnsideF48dE_L [((0 : Fin 18), true)] *
        burnsideF48s_ev burnsideF48dE_L [((1 : Fin 18), true)] *
        (burnsideF48dE_ι (burnsideF48d_L 2 ^ i * burnsideF48d_L 3 ^ j) * burnsideF48dE_F ^ e) =
      (burnsideF48dE_ι (burnsideF48d_L 2 ^ i * burnsideF48d_L 3 ^ j) * burnsideF48dE_F ^ e) *
        (burnsideF48s_ev burnsideF48dE_L [((0 : Fin 18), true)] *
          burnsideF48s_ev burnsideF48dE_L [((1 : Fin 18), true)])) : i = 0 ∧ j = 0 := by
  rw [burnsideF48dE_ev_x, burnsideF48dE_ev_y, ← map_mul] at h
  set a := burnsideF48dE_ι (burnsideF48d_L 0 * burnsideF48d_L 1) with ha
  set t₀ := burnsideF48d_L 2 ^ i * burnsideF48d_L 3 ^ j with ht₀
  have hfa : burnsideF48dE_F ^ e * a = a * burnsideF48dE_F ^ e :=
    (Commute.pow_left (burnsideF48dE_F_comm_xy hM) e).eq
  have h1 : a * burnsideF48dE_ι t₀ = burnsideF48dE_ι t₀ * a := by
    have h' : a * burnsideF48dE_ι t₀ * burnsideF48dE_F ^ e =
        burnsideF48dE_ι t₀ * a * burnsideF48dE_F ^ e := by
      rw [mul_assoc, h, mul_assoc, hfa, ← mul_assoc]
    exact mul_right_cancel h'
  have h2 : burnsideF48d_L 0 * burnsideF48d_L 1 * t₀ =
      t₀ * (burnsideF48d_L 0 * burnsideF48d_L 1) := by
    apply Subgroup.inclusion_injective burnsideF48dE_X_le
    rw [map_mul, map_mul]
    exact h1
  have hT : t₀ ∈ burnsideF48d_T :=
    burnsideF48d_T.mul_mem
      (burnsideF48d_T.pow_mem (burnsideF48dE_L_mem_T (by decide) (by decide)) _)
      (burnsideF48d_T.pow_mem (burnsideF48dE_L_mem_T (by decide) (by decide)) _)
  exact burnsideF48dE_T_inj hM hi hj (hM.comm_T t₀ hT h2)

theorem burnsideF48dE_xy6_rel (hM : burnsideF48d_ModelFacts) :
    burnsideF48s_ev burnsideF48dE_L (burnsideF48s_eCandRel 6 [((0 : Fin 18), true)]
      [((1 : Fin 18), true)] (List.replicate 0 ((2 : Fin 18), true))) = 1 := by
  rw [burnsideF48s_eCandRel, burnsideF48s_ev_append, burnsideF48s_ev_replicate,
    burnsideF48s_ev_append, burnsideF48dE_ev_x, burnsideF48dE_ev_y, ← map_mul, ← map_pow]
  have h6 : (burnsideF48d_L 0 * burnsideF48d_L 1) ^ 6 = 1 :=
    Subtype.ext (by
      rw [SubgroupClass.coe_pow, Subgroup.coe_mul]
      exact burnsideF48dE_xy_six hM)
  rw [h6, map_one, one_mul]
  rfl

theorem burnsideF48dE_xred (hM : burnsideF48d_ModelFacts) {x : ↥burnsideF48dE_Xh}
    (hx : x ∈ burnsideF48dE_P1) (hx2 : x ∉ burnsideF48dE_P2)
    (hxK : ∀ k ∈ burnsideF48dE_K, x * k * x⁻¹ ∈ burnsideF48dE_K) :
    (burnsideF48dE_ι (burnsideF48d_L 0))⁻¹ * x ∈ burnsideF48dE_K := by
  obtain ⟨e, -, x₀, rfl⟩ := burnsideF48dE_dec hM x
  have hF1 : burnsideF48dE_F ^ e ∈ burnsideF48dE_P1 := Subgroup.pow_mem _ burnsideF48dE_F_mem_P1 e
  have hx₀1 : burnsideF48dE_ι x₀ ∈ burnsideF48dE_P1 := by
    have := burnsideF48dE_P1.mul_mem hx (burnsideF48dE_P1.inv_mem hF1)
    rwa [mul_inv_cancel_right] at this
  have hx₀P1 : x₀ ∈ burnsideF48d_P1 := (hM.mem_P1 x₀).2 ((burnsideF48dE_mem_P1 hM _).1 hx₀1)
  have hx₀P2 : x₀ ∉ burnsideF48d_P2 := fun h => hx2 (burnsideF48dE_P2.mul_mem
    (burnsideF48dE_ι_P2 h) (Subgroup.pow_mem _ burnsideF48dE_F_mem_P2 e))
  have hn : (burnsideF48dE_F ^ e)⁻¹ ∈
      Subgroup.normalizer (burnsideF48dE_Th : Set ↥burnsideF48dE_Xh) :=
    Subgroup.inv_mem _ (Subgroup.pow_mem _ (burnsideF48dE_F_normalizer hM) e)
  have hx₀T : ∀ k ∈ burnsideF48d_T, x₀ * k * x₀⁻¹ ∈ burnsideF48d_T := by
    intro k hk
    have h1 := (Subgroup.mem_normalizer_iff.1 hn (burnsideF48dE_ι k)).1 ⟨k, hk, rfl⟩
    rw [inv_inv] at h1
    have h2 := hxK _ (burnsideF48dE_Th_le_K h1)
    have e2 : burnsideF48dE_ι x₀ * burnsideF48dE_F ^ e *
        ((burnsideF48dE_F ^ e)⁻¹ * burnsideF48dE_ι k * burnsideF48dE_F ^ e) *
        (burnsideF48dE_ι x₀ * burnsideF48dE_F ^ e)⁻¹ = burnsideF48dE_ι (x₀ * k * x₀⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      group
    rw [e2] at h2
    have h3 := burnsideF48dE_K_inf_X hM h2 (x₀ * k * x₀⁻¹).2
    exact (Subgroup.mem_map_iff_mem (Subgroup.inclusion_injective _)).1 h3
  have hred := hM.xred x₀ hx₀P1 hx₀P2 hx₀T
  rw [← mul_assoc, ← map_inv, ← map_mul]
  exact burnsideF48dE_K.mul_mem (burnsideF48dE_Th_le_K ⟨_, hred, rfl⟩)
    (Subgroup.pow_mem _ burnsideF48dE_F_mem_K e)

theorem burnsideF48dE_yred (hM : burnsideF48d_ModelFacts) {y : ↥burnsideF48dE_Xh}
    (hy : y ∈ burnsideF48dE_P2) (hy1 : y ∉ burnsideF48dE_P1)
    (hyK : ∀ k ∈ burnsideF48dE_K, y * k * y⁻¹ ∈ burnsideF48dE_K) :
    (burnsideF48dE_ι (burnsideF48d_L 1))⁻¹ * y ∈ burnsideF48dE_K := by
  obtain ⟨e, -, y₀, rfl⟩ := burnsideF48dE_dec hM y
  have hF2 : burnsideF48dE_F ^ e ∈ burnsideF48dE_P2 := Subgroup.pow_mem _ burnsideF48dE_F_mem_P2 e
  have hy₀2 : burnsideF48dE_ι y₀ ∈ burnsideF48dE_P2 := by
    have := burnsideF48dE_P2.mul_mem hy (burnsideF48dE_P2.inv_mem hF2)
    rwa [mul_inv_cancel_right] at this
  have hy₀P2 : y₀ ∈ burnsideF48d_P2 := (hM.mem_P2 y₀).2 ((burnsideF48dE_mem_P2 hM _).1 hy₀2)
  have hy₀P1 : y₀ ∉ burnsideF48d_P1 := fun h => hy1 (burnsideF48dE_P1.mul_mem
    (burnsideF48dE_ι_P1 h) (Subgroup.pow_mem _ burnsideF48dE_F_mem_P1 e))
  have hn : (burnsideF48dE_F ^ e)⁻¹ ∈
      Subgroup.normalizer (burnsideF48dE_Th : Set ↥burnsideF48dE_Xh) :=
    Subgroup.inv_mem _ (Subgroup.pow_mem _ (burnsideF48dE_F_normalizer hM) e)
  have hy₀T : ∀ k ∈ burnsideF48d_T, y₀ * k * y₀⁻¹ ∈ burnsideF48d_T := by
    intro k hk
    have h1 := (Subgroup.mem_normalizer_iff.1 hn (burnsideF48dE_ι k)).1 ⟨k, hk, rfl⟩
    rw [inv_inv] at h1
    have h2 := hyK _ (burnsideF48dE_Th_le_K h1)
    have e2 : burnsideF48dE_ι y₀ * burnsideF48dE_F ^ e *
        ((burnsideF48dE_F ^ e)⁻¹ * burnsideF48dE_ι k * burnsideF48dE_F ^ e) *
        (burnsideF48dE_ι y₀ * burnsideF48dE_F ^ e)⁻¹ = burnsideF48dE_ι (y₀ * k * y₀⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      group
    rw [e2] at h2
    have h3 := burnsideF48dE_K_inf_X hM h2 (y₀ * k * y₀⁻¹).2
    exact (Subgroup.mem_map_iff_mem (Subgroup.inclusion_injective _)).1 h3
  have hred := hM.yred y₀ hy₀P2 hy₀P1 hy₀T
  rw [← mul_assoc, ← map_inv, ← map_mul]
  exact burnsideF48dE_K.mul_mem (burnsideF48dE_Th_le_K ⟨_, hred, rfl⟩)
    (Subgroup.pow_mem _ burnsideF48dE_F_mem_K e)

theorem burnsideF48dE_facts (hM : burnsideF48d_ModelFacts) :
    burnsideF48t_Facts burnsideF48dE_L burnsideF48dE_P1 burnsideF48dE_P2 burnsideF48dE_LS1
      burnsideF48dE_LS2 burnsideF48dE_K burnsideF48d_R13 burnsideF48d_R23
      [[((0 : Fin 18), true)]] [[((1 : Fin 18), true)]] burnsideF48dE_KW 6 where
  hP1 := rfl
  hP2 := rfl
  rel1 := fun r hr => ⟨by
      have h : ∀ r ∈ burnsideF48d_R13, ∀ l ∈ r, l.1 ≠ 1 := by decide +kernel
      exact h r hr,
    Subtype.ext ((burnsideF48dE_coe_ev r).trans
      (burnsideF48dE_rel hM (List.mem_append_left _ hr)))⟩
  rel2 := fun r hr => ⟨by
      have h : ∀ r ∈ burnsideF48d_R23, ∀ l ∈ r, l.1 ≠ 0 := by decide +kernel
      exact h r hr,
    Subtype.ext ((burnsideF48dE_coe_ev r).trans
      (burnsideF48dE_rel hM (List.mem_append_right _ hr)))⟩
  sup := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨e, -, x, rfl⟩ := burnsideF48dE_dec hM z
    have hx : x ∈ burnsideF48d_P1 ⊔ burnsideF48d_P2 := by
      rw [burnsideF48dE_sup_X hM]
      exact Subgroup.mem_top _
    have hle : (burnsideF48d_P1 ⊔ burnsideF48d_P2).map burnsideF48dE_ι ≤
        burnsideF48dE_P1 ⊔ burnsideF48dE_P2 := by
      rw [Subgroup.map_sup]
      exact sup_le_sup (Subgroup.map_le_iff_le_comap.2 fun y hy => burnsideF48dE_ι_P1 hy)
        (Subgroup.map_le_iff_le_comap.2 fun y hy => burnsideF48dE_ι_P2 hy)
    exact Subgroup.mul_mem _ (hle ⟨x, hx, rfl⟩)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_left burnsideF48dE_F_mem_P1) e)
  K_le := burnsideF48dE_K_le hM
  KW_let := by
    intro w hw l hl
    obtain ⟨e, -, j, -, i, -, rfl⟩ := burnsideF48dE_mem_KW.1 hw
    simp only [List.mem_append, List.mem_replicate] at hl
    rcases hl with (⟨-, rfl⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩
    · exact (by decide : (3 : Fin 18) ≠ 1)
    · exact (by decide : (4 : Fin 18) ≠ 1)
    · exact (by decide : (2 : Fin 18) ≠ 1)
  KW_cov := by
    intro c hc
    obtain ⟨e, he, t, ht, rfl⟩ := (burnsideF48dE_mem_K hM c).1 hc
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    obtain ⟨w, hw, hwc⟩ := hM.KW_cov t₀ ht₀
    obtain ⟨j, hj, i, hi, rfl⟩ := burnsideF48dE_mem_KWT.1 hw
    refine ⟨_, burnsideF48dE_mem_KW.2 ⟨e, he, j, hj, i, hi, rfl⟩, ?_⟩
    rw [burnsideF48dE_ev_KW, ← hwc, burnsideF48dE_ev_KWT]
  XW_let := by
    intro w hw l hl
    rw [List.mem_singleton] at hw
    subst hw
    rw [List.mem_singleton] at hl
    subst hl
    exact (by decide : (0 : Fin 18) ≠ 1)
  YW_let := by
    intro w hw l hl
    rw [List.mem_singleton] at hw
    subst hw
    rw [List.mem_singleton] at hl
    subst hl
    exact (by decide : (1 : Fin 18) ≠ 0)
  xred := fun x hx hx2 hxK _ => ⟨_, List.mem_singleton_self _, by
    rw [burnsideF48dE_ev_x]
    exact burnsideF48dE_xred hM hx hx2 hxK⟩
  yred := fun y hy hy1 hyK _ => ⟨_, List.mem_singleton_self _, by
    rw [burnsideF48dE_ev_y]
    exact burnsideF48dE_yred hM hy hy1 hyK⟩
  cand := fun u hu v hv c hc hcomm => by
    rw [List.mem_singleton] at hu hv
    subst hu hv
    obtain ⟨e, he, j, hj, i, hi, rfl⟩ := burnsideF48dE_mem_KW.1 hc
    rw [burnsideF48dE_ev_KW] at hcomm
    obtain ⟨rfl, rfl⟩ := burnsideF48dE_comm_cand hM hi hj hcomm
    simp only [List.replicate_zero, List.nil_append]
    rw [burnsideF48dE_card_Xh hM]
    rcases (show e = 0 ∨ e = 1 ∨ e = 2 by omega) with rfl | h12
    · obtain ⟨hfin, hcard⟩ := burnsideF48dE_tc0
      exact ⟨hfin, Or.inr ⟨hcard, burnsideF48dE_xy6_rel hM⟩⟩
    · obtain ⟨hfin, hcard⟩ := burnsideF48dE_tc12 h12
      exact ⟨hfin, Or.inl (lt_of_le_of_lt hcard (by norm_num))⟩

end Engine

end CFSG.ASVolI
