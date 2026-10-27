module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V1Basic
public import CFSG.RankThree.PartTwo.Sec11.LaterSteps
public import CFSG.RankThree.PartTwo.Sec11.Steps
import CFSG.RankThree.PartTwo.Sec11.Item1115NotFieldProof
import CFSG.RankThree.PartTwo.Sec11.Item1117ProofBasic
import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
import CFSG.RankThree.PartTwo.Sec11.Item1123Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Item1120V1Proof

section Data


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem exists_r_zpow_mul (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) {y : G}
    (hy : y ∈ R) : ∃ k : ℤ, ∃ b ∈ Subgroup.closure ({s, x} : Set G), y = r ^ k * b := by
  have hrR := (Item1116Proof.mem_R h).1
  refine Item1123Proof.exists_zpow_mul_of_mem_closure (h.R_le_normalizer_V h45 hrR) ?_
  rw [← h.R_eq]
  exact hy

theorem closure_s_x_comm (h : Sec11Data G A c L a R Y d x s r g) :
    ∀ u ∈ Subgroup.closure ({s, x} : Set G), ∀ v ∈ Subgroup.closure ({s, x} : Set G),
      u * v = v * u :=
  fun _ hu _ hv => mul_comm_of_mem_closure_pair h.commute_s_x hu hv

theorem a_mul_x_ne (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) :
    a * x ≠ x * a := by
  intro hax
  apply (Item1119Proof.commutator_x_a_facts h45 h).2
  rw [← hax]
  group

theorem centralizer_x_le_B (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) {y : G}
    (hyR : y ∈ R) (hyx : y * x = x * y) : y ∈ Subgroup.closure ({s, x} : Set G) := by
  have hrR := (Item1116Proof.mem_R h).1
  have haR : a ∈ R := Item1115Proof.A_le_R h.toHyp91 h.a_mem
  exact centralizer_le_B (R := R)
    (Item1116Proof.exists_pow_eq_one_of_mem h hrR) (h.R_le_normalizer_V h45 hrR)
    (h.R_le_normalizer_V h45 haR) (Subgroup.subset_closure (by simp)) (closure_s_x_comm h)
    (h.mem_partTwoF.1.2 a h.a_mem) (a_mul_x_ne h45 h)
    (fun y hy => exists_r_zpow_mul h45 h hy) haR hyR hyx

theorem mem_V_of_pow_three_mem (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    {y : G} (hyR : y ∈ R) (hy3 : y ^ 3 ∈ Subgroup.closure ({s, x} : Set G)) :
    y ∈ Subgroup.closure ({s, x, a} : Set G) := by
  have hrR := (Item1116Proof.mem_R h).1
  have haR : a ∈ R := Item1115Proof.A_le_R h.toHyp91 h.a_mem
  have h1 := mem_sup_of_pow_three_mem_B (R := R)
    (Item1116Proof.exists_pow_eq_one_of_mem h hrR) (h.R_le_normalizer_V h45 hrR)
    h.a_not_mem_V (fun y hy => exists_r_zpow_mul h45 h hy) haR hyR hy3
  have h2 : Subgroup.zpowers a ⊔ Subgroup.closure ({s, x} : Set G) ≤
      Subgroup.closure ({s, x, a} : Set G) := by
    refine sup_le ?_ ?_
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    · exact Subgroup.closure_mono (by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
        tauto)
  exact h2 h1

theorem conj_x_cube_mem (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) {u : G}
    (hu : u ∈ R) : u * x ^ 3 * u⁻¹ ∈ Subgroup.zpowers (x ^ 3) := by
  have huN := Item1115Proof.mem_normalizer_zpowers_x h45 h hu
  rw [← conj_pow]
  obtain ⟨m, hm⟩ :=
    Subgroup.mem_zpowers_iff.mp (Item1119Proof.conj_mem_zpowers_of_mem_normalizer huN)
  have e : (x ^ m) ^ 3 = (x ^ 3) ^ m := by
    rw [← zpow_natCast (x ^ m) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast x 3]
  rw [← hm, e]
  exact Subgroup.zpow_mem_zpowers _ m

theorem R_le_normalizer_V0 (h45 : Sec4.Item4_5) (h113 : Item113)
    (h : Sec11Data G A c L a R Y d x s r g) :
    R ≤ Subgroup.normalizer ((Subgroup.closure ({s, a, x ^ 3} : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hrR, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hsV0 : s ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) := Subgroup.subset_closure (by simp)
  have haV0 : a ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) := Subgroup.subset_closure (by simp)
  have hx3V0 : x ^ 3 ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hx3le : Subgroup.zpowers (x ^ 3) ≤ Subgroup.closure ({s, a, x ^ 3} : Set G) :=
    Subgroup.zpowers_le.mpr hx3V0
  have hdV0 : Subgroup.zpowers d ≤ Subgroup.closure ({s, a, x ^ 3} : Set G) :=
    (Subgroup.zpowers_le.mpr (Item1117Proof.d_mem_zpowers_x_cube h)).trans hx3le
  have hcV0 : c ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) :=
    (Subgroup.zpowers_le.mpr hsV0) h.c_mem_zpowers_s
  have hxz := (Item1119Proof.commutator_x_a_facts h45 h).1
  have hr2 : r ∈ Subgroup.normalizer ((Subgroup.closure {c, a} : Subgroup G) : Set G) :=
    h.closure_rs_le_normalizer h45 h113 (Subgroup.subset_closure (by simp))
  have hle : Subgroup.closure ({c, a} : Set G) ≤ Subgroup.closure ({s, a, x ^ 3} : Set G) := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz <;> rw [hz]
    exacts [hcV0, haV0]
  rw [h.R_eq, Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with hy | hy | hy <;> rw [hy]
  ·
    refine mem_normalizer_closure_of_conj_mem fun w hw => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw | hw <;> rw [hw]
    · exact (Subgroup.zpowers_le.mpr hsV0)
        ((Subgroup.mem_normalizer_iff.mp (Item1115Proof.mem_normalizer_zpowers_s h45 h hrR) s).mp
          (Subgroup.mem_zpowers s))
    · exact hle ((Subgroup.mem_normalizer_iff.mp hr2 a).mp (Subgroup.subset_closure (by simp)))
    · exact hx3le (conj_x_cube_mem h45 h hrR)
  ·
    refine mem_normalizer_closure_of_conj_mem fun w hw => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw | hw <;> rw [hw]
    · have e : x * s * x⁻¹ = s := by
        calc x * s * x⁻¹ = s * x * x⁻¹ := by rw [← h.commute_s_x]
          _ = s := by group
      rw [e]
      exact hsV0
    · have e : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
      rw [e]
      exact Subgroup.mul_mem _ (hdV0 hxz) haV0
    · have e : x * x ^ 3 * x⁻¹ = x ^ 3 := by group
      rw [e]
      exact hx3V0
  · exact Subgroup.le_normalizer hsV0

end Data

section M2

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def M2 (x : G) : Subgroup G := Subgroup.zpowers (x ^ (orderOf x / 9))

theorem M2_le_zpowers (x : G) : M2 x ≤ Subgroup.zpowers x :=
  Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)

theorem pow_nine_eq_one_of_mem_M2 {x z : G} (h9 : 9 ∣ orderOf x) (hz : z ∈ M2 x) : z ^ 9 = 1 := by
  have hm9 : (x ^ (orderOf x / 9)) ^ 9 = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel h9, pow_orderOf_eq_one]
  exact orderOf_dvd_iff_pow_eq_one.mp
    ((orderOf_dvd_of_mem_zpowers hz).trans (orderOf_dvd_iff_pow_eq_one.mpr hm9))

theorem mem_M2_of_pow_nine {x z : G} (h9 : 9 ∣ orderOf x) (hz : z ∈ Subgroup.zpowers x)
    (hz9 : z ^ 9 = 1) : z ∈ M2 x := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  obtain ⟨t, ht⟩ := h9
  have h1 : x ^ (i * 9) = 1 := by
    rw [zpow_mul]
    exact_mod_cast hz9
  have h2 : ((orderOf x : ℕ) : ℤ) ∣ i * 9 := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [ht] at h2
  push_cast at h2
  have h3 : (t : ℤ) ∣ i := by
    rw [mul_comm (9 : ℤ) (t : ℤ)] at h2
    exact (mul_dvd_mul_iff_right (by norm_num : (9 : ℤ) ≠ 0)).mp h2
  obtain ⟨j, hj⟩ := h3
  refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
  have hdiv : orderOf x / 9 = t := by
    rw [ht]
    exact Nat.mul_div_cancel_left t (by norm_num)
  rw [hdiv, ← zpow_natCast, ← zpow_mul, hj]

theorem M2_le_zpowers_cube {x : G} (h27 : 27 ∣ orderOf x) : M2 x ≤ Subgroup.zpowers (x ^ 3) := by
  obtain ⟨w, hw⟩ := h27
  have e : x ^ (orderOf x / 9) = (x ^ 3) ^ w := by
    rw [← pow_mul]
    congr 1
    omega
  rw [M2, e]
  exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)

theorem card_M2 {x : G} (h9 : 9 ∣ orderOf x) : Nat.card (M2 x) = 9 := by
  obtain ⟨t, ht⟩ := h9
  have hpos : 0 < orderOf x := orderOf_pos x
  have ht0 : t ≠ 0 := by
    rintro rfl
    omega
  have hdiv : orderOf x / 9 = t := by
    rw [ht]
    exact Nat.mul_div_cancel_left t (by norm_num)
  rw [M2, Nat.card_zpowers, hdiv, orderOf_pow_of_dvd ht0 ⟨9, by rw [ht]; ring⟩, ht]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero ht0)

theorem M2_le_zpowers_of_pow_three_ne_one {x t : G} (h9 : 9 ∣ orderOf x) (ht : t ∈ M2 x)
    (ht3 : t ^ 3 ≠ 1) : M2 x ≤ Subgroup.zpowers t := by
  have hle : Subgroup.zpowers t ≤ M2 x := Subgroup.zpowers_le.mpr ht
  have hord : orderOf t = 9 := by
    have h1 : orderOf t ∣ 3 ^ 2 := by
      have := orderOf_dvd_iff_pow_eq_one.mpr (pow_nine_eq_one_of_mem_M2 h9 ht)
      simpa using this
    obtain ⟨i, hi, hti⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    interval_cases i
    · exfalso
      apply ht3
      have : orderOf t = 1 := by simpa using hti
      rw [orderOf_eq_one_iff.mp this, one_pow]
    · exfalso
      apply ht3
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hti]; simp)
    · simpa using hti
  have heq : Subgroup.zpowers t = M2 x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_M2 h9, Nat.card_zpowers, hord])
  exact heq.ge

end M2

section Data2


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

noncomputable def V1 (h113 : Item113) (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g) :
    Subgroup G :=
  cenMod (sec11P R g) (Subgroup.closure ({s, a, x ^ 3} : Set G)) (Subgroup.zpowers d)
    (fun _ hq _ hz => Item1119Proof.commute_of_mem_zpowers_d h113 h117 h hz hq)

theorem mem_V1_iff {h113 : Item113} {h117 : Item117} {h : Sec11Data G A c L a R Y d x s r g}
    {y : G} : y ∈ V1 h113 h117 h ↔ y ∈ sec11P R g ∧
      ∀ w ∈ Subgroup.closure ({s, a, x ^ 3} : Set G), y * w * y⁻¹ * w⁻¹ ∈ Subgroup.zpowers d :=
  Iff.rfl

theorem exists_mul_zpow_of_mem_P' (h : Sec11Data G A c L a R Y d x s r g) {y : G}
    (hy : y ∈ sec11P R g) : ∃ u ∈ R, ∃ k : ℤ, y = u * g ^ k := by
  have hle : Subgroup.zpowers g ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr h.g_mem_normalizer
  have hy' : y ∈ ((R ⊔ Subgroup.zpowers g : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at hy'
  obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.mp hy'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ⟨u, hu, k, rfl⟩

theorem V0_le_R (h : Sec11Data G A c L a R Y d x s r g) :
    Subgroup.closure ({s, a, x ^ 3} : Set G) ≤ R := by
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  have haR : a ∈ R := Item1115Proof.A_le_R h.toHyp91 h.a_mem
  rw [Subgroup.closure_le]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with hz | hz | hz <;> rw [hz]
  exacts [hsR, haR, R.pow_mem hxR 3]

theorem mem_zpowers_d_of_commute {u w : G} (huw : u * w = w * u) :
    u * w * u⁻¹ * w⁻¹ ∈ Subgroup.zpowers d := by
  have : u * w * u⁻¹ * w⁻¹ = 1 := by rw [huw]; group
  rw [this]
  exact Subgroup.one_mem _

theorem mem_V1_of_gens (h113 : Item113) (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g)
    {t : G} (htR : t ∈ R)
    (ht : ∀ w ∈ ({s, a, x ^ 3} : Set G), t * w * t⁻¹ * w⁻¹ ∈ Subgroup.zpowers d) :
    t ∈ V1 h113 h117 h := by
  refine ⟨Item1119Proof.R_le_P R g htR, fun w hw => ?_⟩
  have hV0d : Subgroup.closure ({s, a, x ^ 3} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    (V0_le_R h).trans ((Item1119Proof.R_le_P R g).trans
      (Item1119Proof.P_le_normalizer_d h113 h117 h))
  exact Item1119Proof.commutator_mem_of_mem_closure hV0d ht hw

theorem V_le_V1 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) :
    Subgroup.closure ({s, x, a} : Set G) ≤ V1 h113 h117 h := by
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  have haR : a ∈ R := Item1115Proof.A_le_R h.toHyp91 h.a_mem
  have hsa : s * a = a * s := item1115_of_mhoV h45 h113 h117 G A c L a R Y d x s r g h
  have hxz := (Item1119Proof.commutator_x_a_facts h45 h).1
  have hax3 : a * x ^ 3 = x ^ 3 * a := by
    have := (Item1119Proof.a_x_facts h45 h).1
    calc a * x ^ 3 = (a * x ^ 3 * a⁻¹) * a := by group
      _ = x ^ 3 * a := by rw [this]
  have hsx3 : s * x ^ 3 = x ^ 3 * s := (Commute.pow_right (h.commute_s_x : Commute s x) 3).eq
  rw [Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with hy | hy | hy <;> rw [hy]
  · refine mem_V1_of_gens h113 h117 h hsR fun w hw => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw | hw <;> rw [hw]
    · exact mem_zpowers_d_of_commute rfl
    · exact mem_zpowers_d_of_commute hsa
    · exact mem_zpowers_d_of_commute hsx3
  · refine mem_V1_of_gens h113 h117 h hxR fun w hw => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw | hw <;> rw [hw]
    · exact mem_zpowers_d_of_commute h.commute_s_x.symm
    · exact hxz
    · exact mem_zpowers_d_of_commute (Commute.pow_right (Commute.refl x) 3).eq
  · refine mem_V1_of_gens h113 h117 h haR fun w hw => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw | hw <;> rw [hw]
    · exact mem_zpowers_d_of_commute hsa.symm
    · exact mem_zpowers_d_of_commute rfl
    · exact mem_zpowers_d_of_commute hax3

theorem P_le_normalizer_V0 (h45 : Sec4.Item4_5) (h113 : Item113)
    (h : Sec11Data G A c L a R Y d x s r g)
    (hgV0 : g ∈ Subgroup.normalizer
      ((Subgroup.closure ({s, a, x ^ 3} : Set G) : Subgroup G) : Set G)) :
    sec11P R g ≤ Subgroup.normalizer
      ((Subgroup.closure ({s, a, x ^ 3} : Set G) : Subgroup G) : Set G) :=
  sup_le (R_le_normalizer_V0 h45 h113 h) (Subgroup.zpowers_le.mpr hgV0)

theorem conj_mem_V1 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g)
    (hgV0 : g ∈ Subgroup.normalizer
      ((Subgroup.closure ({s, a, x ^ 3} : Set G) : Subgroup G) : Set G))
    {p y : G} (hp : p ∈ sec11P R g) (hy : y ∈ V1 h113 h117 h) : p * y * p⁻¹ ∈ V1 h113 h117 h :=
  conj_mem_cenMod (P_le_normalizer_V0 h45 h113 h hgV0) hp hy

theorem g_pow_three' (hbig : Sec11Big G A c L a R Y d x s r g) : g ^ 3 = 1 :=
  hbig.orderOf_g ▸ pow_orderOf_eq_one g

theorem twentySeven_dvd_orderOf_x (hbig : Sec11Big G A c L a R Y d x s r g) : 27 ∣ orderOf x := by
  have h := hbig.toSec11Data
  have hx : ∃ n : ℕ, x ^ 3 ^ n = 1 := Item1117Proof.x_pow_eq_one h
  have h1 := Item1125Proof.three_pow_succ_dvd_orderOf hx (m := 2)
    (by have := hbig.orderOf_x_gt; omega)
  simpa using h1

theorem d_mem_M2 (h : Sec11Data G A c L a R Y d x s r g) : d ∈ M2 x := by
  refine mem_M2_of_pow_nine (Item1117Proof.nine_dvd_orderOf_x h)
    (Item1115Proof.d_mem_zpowers_x h) ?_
  have hd3 := (Item1115Proof.d_mem h).2.2
  rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hd3, one_pow]

theorem pow_three_eq_one_of_mem_zpowers_d (h : Sec11Data G A c L a R Y d x s r g) {w : G}
    (hw : w ∈ Subgroup.zpowers d) : w ^ 3 = 1 := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hd3 := (Item1115Proof.d_mem h).2.2
  have e : (d ^ i) ^ 3 = (d ^ 3) ^ i := by
    rw [← zpow_natCast (d ^ i) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast d 3]
  rw [e, hd3, one_zpow]

theorem x_cube_pow_three_ne_one (hbig : Sec11Big G A c L a R Y d x s r g) : (x ^ 3) ^ 3 ≠ 1 := by
  intro h1
  rw [← pow_mul] at h1
  have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h1)
  have := hbig.orderOf_x_gt
  omega

theorem V1_le_R (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hbig : Sec11Big G A c L a R Y d x s r g)
    (hCube : ∀ y ∈ Subgroup.zpowers (x ^ 3), y ^ 3 ≠ 1 → d ∈ Subgroup.zpowers y →
      g * y * g⁻¹ ∈ Subgroup.zpowers y → False)
    {y : G} (hy : y ∈ V1 h113 h117 hbig.toSec11Data) : y ∈ R := by
  have h := hbig.toSec11Data
  obtain ⟨hyP, hyV⟩ := hy
  obtain ⟨u, huR, k, rfl⟩ := exists_mul_zpow_of_mem_P' h hyP
  by_cases hk : (3 : ℤ) ∣ k
  · obtain ⟨q, rfl⟩ := hk
    have : g ^ (3 * q) = 1 := by
      rw [zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, g_pow_three' hbig,
        one_zpow]
    rw [this, mul_one]
    exact huR
  · exfalso
    have hx3 : x ^ 3 ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hδ := hyV _ hx3
    have hdx3 : Subgroup.zpowers d ≤ Subgroup.zpowers (x ^ 3) :=
      Subgroup.zpowers_le.mpr (Item1117Proof.d_mem_zpowers_x_cube h)
    have hgk : g ^ k * x ^ 3 * (g ^ k)⁻¹ ∈ Subgroup.zpowers (x ^ 3) := by
      set δ := (u * g ^ k) * x ^ 3 * (u * g ^ k)⁻¹ * (x ^ 3)⁻¹ with hδdef
      have e : g ^ k * x ^ 3 * (g ^ k)⁻¹ = u⁻¹ * (δ * x ^ 3) * u := by
        rw [hδdef]; group
      have hcomm : u⁻¹ * δ = δ * u⁻¹ :=
        Item1119Proof.commute_of_mem_zpowers_d h113 h117 h hδ
          ((sec11P R g).inv_mem (Item1119Proof.R_le_P R g huR))
      have e2 : u⁻¹ * (δ * x ^ 3) * u = δ * (u⁻¹ * x ^ 3 * u) := by
        calc u⁻¹ * (δ * x ^ 3) * u = (u⁻¹ * δ) * x ^ 3 * u := by group
          _ = (δ * u⁻¹) * x ^ 3 * u := by rw [hcomm]
          _ = δ * (u⁻¹ * x ^ 3 * u) := by group
      rw [e, e2]
      refine Subgroup.mul_mem _ (hdx3 hδ) ?_
      have := conj_x_cube_mem h45 h (R.inv_mem huR)
      simpa using this
    have hgkN : g ^ k ∈ Subgroup.normalizer (Subgroup.zpowers (x ^ 3) : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun w hw => ?_
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have e : g ^ k * (x ^ 3) ^ j * (g ^ k)⁻¹ = (g ^ k * x ^ 3 * (g ^ k)⁻¹) ^ j :=
        (conj_zpow).symm
      rw [e]
      exact Subgroup.zpow_mem _ hgk j
    have hgN : g ∈ Subgroup.normalizer (Subgroup.zpowers (x ^ 3) : Set G) :=
      mem_of_zpow_mem_of_pow_three (g_pow_three' hbig) hk hgkN
    have hgx3 : g * x ^ 3 * g⁻¹ ∈ Subgroup.zpowers (x ^ 3) :=
      (Subgroup.mem_normalizer_iff.mp hgN (x ^ 3)).mp (Subgroup.mem_zpowers _)
    exact hCube (x ^ 3) (Subgroup.mem_zpowers _) (x_cube_pow_three_ne_one hbig)
      (Item1117Proof.d_mem_zpowers_x_cube h) hgx3

theorem commutator_x_mem_M2 (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) {u : G}
    (huR : u ∈ R) (hu : u * x ^ 3 * u⁻¹ * (x ^ 3)⁻¹ ∈ Subgroup.zpowers d) :
    u * x * u⁻¹ * x⁻¹ ∈ M2 x := by
  have huN := Item1115Proof.mem_normalizer_zpowers_x h45 h huR
  have hp : u * x * u⁻¹ ∈ Subgroup.zpowers x :=
    Item1119Proof.conj_mem_zpowers_of_mem_normalizer huN
  have hz : u * x * u⁻¹ * x⁻¹ ∈ Subgroup.zpowers x :=
    Subgroup.mul_mem _ hp (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  have hcomm : Commute (u * x * u⁻¹) x⁻¹ := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hp
    rw [← hj]
    exact ((Commute.refl x).inv_right).zpow_left j
  have h3 : (u * x * u⁻¹ * x⁻¹) ^ 3 = u * x ^ 3 * u⁻¹ * (x ^ 3)⁻¹ := by
    rw [hcomm.mul_pow, conj_pow, inv_pow]
  have h3d : (u * x * u⁻¹ * x⁻¹) ^ 3 ∈ Subgroup.zpowers d := by
    rw [h3]
    exact hu
  have h9 : (u * x * u⁻¹ * x⁻¹) ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul]
    exact pow_three_eq_one_of_mem_zpowers_d h h3d
  exact mem_M2_of_pow_nine (Item1117Proof.nine_dvd_orderOf_x h) hz h9

theorem commutator_V1_le_M2 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hbig : Sec11Big G A c L a R Y d x s r g)
    (hCube : ∀ y ∈ Subgroup.zpowers (x ^ 3), y ^ 3 ≠ 1 → d ∈ Subgroup.zpowers y →
      g * y * g⁻¹ ∈ Subgroup.zpowers y → False)
    {u v : G} (hu : u ∈ V1 h113 h117 hbig.toSec11Data) (hv : v ∈ V1 h113 h117 hbig.toSec11Data) :
    u * v * u⁻¹ * v⁻¹ ∈ M2 x := by
  have h := hbig.toSec11Data
  obtain ⟨hrR, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hV1R : ∀ y ∈ V1 h113 h117 h, y ∈ R := fun y hy => V1_le_R h45 h113 h117 hbig hCube hy
  have hBc := closure_s_x_comm h
  have hM2B : M2 x ≤ Subgroup.closure ({s, x} : Set G) :=
    (M2_le_zpowers x).trans (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
  have hBN : Subgroup.closure ({s, x} : Set G) ≤ Subgroup.normalizer (M2 x : Set G) := by
    intro b hb
    refine Subgroup.mem_normalizer_fintype fun m hm => ?_
    have hbm : b * m = m * b := hBc b hb m (hM2B hm)
    have e : b * m * b⁻¹ = m := by
      calc b * m * b⁻¹ = m * b * b⁻¹ := by rw [hbm]
        _ = m := by group
    rw [e]
    exact hm
  have hBV : Subgroup.closure ({s, x} : Set G) ≤ Subgroup.closure ({s, x, a} : Set G) :=
    Subgroup.closure_mono (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto)
  have hAN : ∀ α ∈ Subgroup.zpowers r ⊓ V1 h113 h117 h, ∀ y ∈ Subgroup.closure ({s, x} : Set G),
      α * y * α⁻¹ * y⁻¹ ∈ M2 x := by
    intro α hα y hy
    have hαV1 : α ∈ V1 h113 h117 h := hα.2
    have hαR := hV1R α hαV1
    refine Item1119Proof.commutator_mem_of_mem_closure (S := ({s, x} : Set G)) hBN ?_ hy
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw <;> rw [hw]
    · exact (Subgroup.zpowers_le.mpr (d_mem_M2 h))
        (hαV1.2 s (Subgroup.subset_closure (by simp)))
    · exact commutator_x_mem_M2 h45 h hαR (hαV1.2 _ (Subgroup.subset_closure (by simp)))
  have hAY : Subgroup.zpowers r ⊓ V1 h113 h117 h ≤
      Subgroup.normalizer ((Subgroup.closure ({s, x} : Set G) : Subgroup G) : Set G) :=
    fun α hα => (Subgroup.zpowers_le.mpr (h.R_le_normalizer_V h45 hrR)) hα.1
  have hA : ∀ α ∈ Subgroup.zpowers r ⊓ V1 h113 h117 h, ∀ β ∈ Subgroup.zpowers r ⊓ V1 h113 h117 h,
      α * β = β * α := by
    intro α hα β hβ
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hα.1
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hβ.1
    exact (Commute.zpow_zpow_self r i j).eq
  have hcomm := commutator_sup_le_of_comm' hBc hAY hA hAN
  have hdec : ∀ y ∈ V1 h113 h117 h,
      y ∈ Subgroup.closure ({s, x} : Set G) ⊔ (Subgroup.zpowers r ⊓ V1 h113 h117 h) := by
    intro y hy
    obtain ⟨k, b, hb, hyb⟩ := exists_r_zpow_mul h45 h (hV1R y hy)
    have hbV1 : b ∈ V1 h113 h117 h := V_le_V1 h45 h113 h117 h (hBV hb)
    have hrk : r ^ k ∈ V1 h113 h117 h := by
      have : r ^ k = y * b⁻¹ := by rw [hyb]; group
      rw [this]
      exact Subgroup.mul_mem _ hy (Subgroup.inv_mem _ hbV1)
    have hrkA : r ^ k ∈ Subgroup.zpowers r ⊓ V1 h113 h117 h := ⟨Subgroup.zpow_mem_zpowers r k, hrk⟩
    rw [hyb]
    exact Subgroup.mul_mem _
      ((le_sup_right : Subgroup.zpowers r ⊓ V1 h113 h117 h ≤
        Subgroup.closure ({s, x} : Set G) ⊔ (Subgroup.zpowers r ⊓ V1 h113 h117 h)) hrkA)
      ((le_sup_left : Subgroup.closure ({s, x} : Set G) ≤
        Subgroup.closure ({s, x} : Set G) ⊔ (Subgroup.zpowers r ⊓ V1 h113 h117 h)) hb)
  have h1 := hcomm (Subgroup.commutator_mem_commutator (hdec u hu) (hdec v hv))
  rwa [commutatorElement_def] at h1

theorem commutator_x_mem_zpowers_d (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hbig : Sec11Big G A c L a R Y d x s r g)
    (hgV0 : g ∈ Subgroup.normalizer
      ((Subgroup.closure ({s, a, x ^ 3} : Set G) : Subgroup G) : Set G))
    (hCube : ∀ y ∈ Subgroup.zpowers (x ^ 3), y ^ 3 ≠ 1 → d ∈ Subgroup.zpowers y →
      g * y * g⁻¹ ∈ Subgroup.zpowers y → False)
    {y : G} (hy : y ∈ V1 h113 h117 hbig.toSec11Data) : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers d := by
  have h := hbig.toSec11Data
  by_contra hnot
  have h9 := Item1117Proof.nine_dvd_orderOf_x h
  have h27 := twentySeven_dvd_orderOf_x hbig
  have hxV1 : x ∈ V1 h113 h117 h := V_le_V1 h45 h113 h117 h (Subgroup.subset_closure (by simp))
  have htM2 : x * y * x⁻¹ * y⁻¹ ∈ M2 x :=
    commutator_V1_le_M2 h45 h113 h117 hbig hCube hxV1 hy
  have htx : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers x := M2_le_zpowers x htM2
  have ht3 : (x * y * x⁻¹ * y⁻¹) ^ 3 ≠ 1 := fun h3 =>
    hnot (Item1117Proof.mem_zpowers_of_pow_three_eq_one (Item1115Proof.d_mem_zpowers_x h)
      (Item1117Proof.orderOf_d h) htx h3)
  have hM2t := M2_le_zpowers_of_pow_three_ne_one h9 htM2 ht3
  have hgP : g ∈ sec11P R g := Item1119Proof.g_mem_P R g
  have hgx := conj_mem_V1 h45 h113 h117 h hgV0 hgP hxV1
  have hgy := conj_mem_V1 h45 h113 h117 h hgV0 hgP hy
  have hgt : g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ ∈ M2 x := by
    have e : g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ =
        (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ := by group
    rw [e]
    exact commutator_V1_le_M2 h45 h113 h117 hbig hCube hgx hgy
  exact hCube _ (M2_le_zpowers_cube h27 htM2) ht3 (hM2t (d_mem_M2 h)) (hM2t hgt)

theorem V1_le_V (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hbig : Sec11Big G A c L a R Y d x s r g)
    (hgV0 : g ∈ Subgroup.normalizer
      ((Subgroup.closure ({s, a, x ^ 3} : Set G) : Subgroup G) : Set G))
    (hCube : ∀ y ∈ Subgroup.zpowers (x ^ 3), y ^ 3 ≠ 1 → d ∈ Subgroup.zpowers y →
      g * y * g⁻¹ ∈ Subgroup.zpowers y → False)
    {y : G} (hy : y ∈ V1 h113 h117 hbig.toSec11Data) :
    y ∈ Subgroup.closure ({s, x, a} : Set G) := by
  have h := hbig.toSec11Data
  have hyR := V1_le_R h45 h113 h117 hbig hCube hy
  have hxy := commutator_x_mem_zpowers_d h45 h113 h117 hbig hgV0 hCube hy
  have hδ : (x * y * x⁻¹ * y⁻¹)⁻¹ ∈ Subgroup.zpowers d := Subgroup.inv_mem _ hxy
  have hyx : y * x * y⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ * x := by group
  have hcomm : y * (x * y * x⁻¹ * y⁻¹)⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ * y :=
    Item1119Proof.commute_of_mem_zpowers_d h113 h117 h hδ hy.1
  have h3 := Item1119Proof.zpow_conj_eq_zpow_mul hcomm hyx 3
  have hδ3 : ((x * y * x⁻¹ * y⁻¹)⁻¹) ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact pow_three_eq_one_of_mem_zpowers_d h hδ
  rw [hδ3, one_mul] at h3
  have hy3x : y ^ 3 * x = x * y ^ 3 := by
    have h3' : y ^ (3 : ℤ) * x * (y ^ (3 : ℤ))⁻¹ = x := h3
    rw [zpow_ofNat] at h3'
    calc y ^ 3 * x = (y ^ 3 * x * (y ^ 3)⁻¹) * y ^ 3 := by group
      _ = x * y ^ 3 := by rw [h3']
  have hy3R : y ^ 3 ∈ R := R.pow_mem hyR 3
  exact mem_V_of_pow_three_mem h45 h hyR (centralizer_x_le_B h45 h hy3R hy3x)

end Data2

end Item1120V1Proof

end CFSG.RankThree.PartTwo.Sec11
