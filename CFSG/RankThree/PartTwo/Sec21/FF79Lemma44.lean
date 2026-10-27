module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec4Defs
import CFSG.LocalAnalysis.ComponentClassification.Sol78Maximal
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.Sporadic.Recognition.LyonsAS44Frattini

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped commutatorElement

variable {G : Type} [Group G]

theorem op2_le_cen (t : G) : Op 2 (Cen t) ≤ Cen t := Subgroup.map_subtype_le _

theorem op2_conj_mem {t c y : G} (hc : c ∈ Cen t) (hy : y ∈ Op 2 (Cen t)) :
    c * y * c⁻¹ ∈ Op 2 (Cen t) := by
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨⟨c, hc⟩ * y' * ⟨c, hc⟩⁻¹, ?_, by simp⟩
  exact (inferInstance : (CFSG.pCore 2 ↥(Cen t)).Normal).conj_mem y' hy' ⟨c, hc⟩

theorem op2_isPGroup (t : G) : IsPGroup 2 ↥(Op 2 (Cen t)) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥(Cen t))).map (Cen t).subtype

theorem cen_mul_zpowers {t g : G} (hg : g ∈ Cen t) {c : G} (hc : c ∈ Subgroup.zpowers t) :
    g * c = c * g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hg) k).eq

theorem conj_fix_zpowers {t j : G} (hj : j ∈ Cen t) {c : G} (hc : c ∈ Subgroup.zpowers t) :
    j * c * j⁻¹ = c := by
  rw [cen_mul_zpowers hj hc]; group

theorem sq_eq_one_of_mem_zpowers {t : G} (ht2 : t ^ 2 = 1) {c : G}
    (hc : c ∈ Subgroup.zpowers t) : c ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]

theorem self_mem_op2 {t : G} (ht : orderOf t = 2) : t ∈ Op 2 (Cen t) := by
  have htC : t ∈ Cen t := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hKn : ((Subgroup.zpowers t).subgroupOf (Cen t)).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [conj_fix_zpowers g.2 ha]
    exact ha
  have hKp : IsPGroup 2 ↥((Subgroup.zpowers t).subgroupOf (Cen t)) := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext; apply Subtype.ext
    exact sq_eq_one_of_mem_zpowers ht2 (Subgroup.mem_subgroupOf.mp g.2)
  have hle : (Subgroup.zpowers t).subgroupOf (Cen t) ≤ CFSG.pCore 2 ↥(Cen t) := by
    unfold CFSG.pCore
    exact le_sSup ⟨hKn, hKp⟩
  exact Subgroup.mem_map.mpr ⟨⟨t, htC⟩, hle (Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_zpowers t)), rfl⟩

theorem mem_op2_of_centralizes {t : G} (hchar : IsCharacteristicPType G 2) (ht : orderOf t = 2)
    {c : G} (hc : c ∈ Cen t) (hcT : ∀ y ∈ Op 2 (Cen t), c * y = y * c) :
    c ∈ Op 2 (Cen t) := by
  have hloc := ComponentClassification.Sol78.isPLocal_centralizer_of_orderOf_eq_two ht
  have h := hchar _ hloc
  have hmem : (⟨c, hc⟩ : ↥(Cen t)) ∈ CFSG.pCore 2 ↥(Cen t) := by
    refine h ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (y : G) ∈ Op 2 (Cen t) := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    exact Subtype.ext (hcT y hy').symm
  exact Subgroup.mem_map.mpr ⟨⟨c, hc⟩, hmem, rfl⟩

theorem le_nor_of_conj_mem {J S : Subgroup G} (h : ∀ j ∈ J, ∀ s ∈ S, j * s * j⁻¹ ∈ S) :
    J ≤ Nor S := by
  intro j hj
  rw [Nor, Subgroup.mem_set_normalizer_iff]
  intro x
  simp only [SetLike.mem_coe]
  refine ⟨h j hj x, fun hx => ?_⟩
  have := h j⁻¹ (J.inv_mem hj) _ hx
  rwa [show j⁻¹ * (j * x * j⁻¹) * j⁻¹⁻¹ = x by group] at this

private def sqComm (t : G) (S : Subgroup G) (hS : S ≤ Cen t) : Subgroup G where
  carrier := {y | y ∈ S ∧ y ^ 2 ∈ Subgroup.zpowers t ∧
    ∀ z ∈ S, y * z * y⁻¹ * z⁻¹ ∈ Subgroup.zpowers t}
  one_mem' := ⟨S.one_mem, by simp, fun z _ => by simp⟩
  mul_mem' := by
    rintro y y' ⟨hy, hy2, hyc⟩ ⟨hy', hy'2, hy'c⟩
    refine ⟨S.mul_mem hy hy', ?_, fun z hz => ?_⟩
    · have hc : y' * y * y'⁻¹ * y⁻¹ ∈ Subgroup.zpowers t := hy'c y hy
      have h1 := cen_mul_zpowers (hS hy) hc
      have e1 : (y * y') ^ 2 = (y' * y * y'⁻¹ * y⁻¹) * (y ^ 2 * y' ^ 2) := by
        calc (y * y') ^ 2 = y * (y' * y * y'⁻¹ * y⁻¹) * (y * y' * y') := by simp only [sq]; group
          _ = (y' * y * y'⁻¹ * y⁻¹) * y * (y * y' * y') := by rw [h1]
          _ = _ := by simp only [sq]; group
      rw [e1]
      exact (Subgroup.zpowers t).mul_mem hc ((Subgroup.zpowers t).mul_mem hy2 hy'2)
    · have hd : y' * z * y'⁻¹ * z⁻¹ ∈ Subgroup.zpowers t := hy'c z hz
      have he : y * z * y⁻¹ * z⁻¹ ∈ Subgroup.zpowers t := hyc z hz
      have h1 := cen_mul_zpowers (hS hy) hd
      have e : y * y' * z * (y * y')⁻¹ * z⁻¹
          = (y' * z * y'⁻¹ * z⁻¹) * (y * z * y⁻¹ * z⁻¹) := by
        calc y * y' * z * (y * y')⁻¹ * z⁻¹
            = y * (y' * z * y'⁻¹ * z⁻¹) * z * y⁻¹ * z⁻¹ := by group
          _ = (y' * z * y'⁻¹ * z⁻¹) * y * z * y⁻¹ * z⁻¹ := by rw [h1]
          _ = (y' * z * y'⁻¹ * z⁻¹) * (y * z * y⁻¹ * z⁻¹) := by group
      rw [e]
      exact (Subgroup.zpowers t).mul_mem hd he
  inv_mem' := by
    rintro y ⟨hy, hy2, hyc⟩
    refine ⟨S.inv_mem hy, ?_, fun z hz => ?_⟩
    · rw [inv_pow]; exact (Subgroup.zpowers t).inv_mem hy2
    · have he : (y * z * y⁻¹ * z⁻¹)⁻¹ ∈ Subgroup.zpowers t :=
        (Subgroup.zpowers t).inv_mem (hyc z hz)
      have h1 := cen_mul_zpowers (hS (S.inv_mem hy)) he
      have e : y⁻¹ * z * y⁻¹⁻¹ * z⁻¹ = (y * z * y⁻¹ * z⁻¹)⁻¹ := by
        calc y⁻¹ * z * y⁻¹⁻¹ * z⁻¹
            = y⁻¹ * (y * z * y⁻¹ * z⁻¹)⁻¹ * y := by group
          _ = (y * z * y⁻¹ * z⁻¹)⁻¹ * y⁻¹ * y := by rw [h1]
          _ = (y * z * y⁻¹ * z⁻¹)⁻¹ := by group
      rw [e]
      exact he

private theorem conj_mem_sqComm {t : G} {S : Subgroup G} (hS : S ≤ Cen t)
    (hSn : ∀ c ∈ Cen t, ∀ s ∈ S, c * s * c⁻¹ ∈ S) {j y : G} (hj : j ∈ Cen t)
    (hy : y ∈ sqComm t S hS) : j * y * j⁻¹ ∈ sqComm t S hS := by
  obtain ⟨hyS, hy2, hyc⟩ := hy
  refine ⟨hSn j hj y hyS, ?_, fun z hz => ?_⟩
  · have : (j * y * j⁻¹) ^ 2 = j * y ^ 2 * j⁻¹ := by simp only [sq]; group
    rw [this, conj_fix_zpowers hj hy2]
    exact hy2
  · have hz' : j⁻¹ * z * j ∈ S := by
      have := hSn j⁻¹ ((Cen t).inv_mem hj) z hz
      simpa using this
    have h := hyc _ hz'
    have e : j * y * j⁻¹ * z * (j * y * j⁻¹)⁻¹ * z⁻¹
        = j * (y * (j⁻¹ * z * j) * y⁻¹ * (j⁻¹ * z * j)⁻¹) * j⁻¹ := by group
    rw [e, conj_fix_zpowers hj h]
    exact h

private def commSub (t y : G) : Subgroup G where
  carrier := {z | z ∈ Cen t ∧ y * z * y⁻¹ * z⁻¹ ∈ Subgroup.zpowers t}
  one_mem' := ⟨(Cen t).one_mem, by simp⟩
  mul_mem' := by
    rintro z z' ⟨hz, he⟩ ⟨hz', he'⟩
    refine ⟨(Cen t).mul_mem hz hz', ?_⟩
    have h1 := cen_mul_zpowers hz he'
    have e : y * (z * z') * y⁻¹ * (z * z')⁻¹
        = (y * z * y⁻¹ * z⁻¹) * (y * z' * y⁻¹ * z'⁻¹) := by
      calc y * (z * z') * y⁻¹ * (z * z')⁻¹
          = (y * z * y⁻¹ * z⁻¹) * (z * (y * z' * y⁻¹ * z'⁻¹)) * z⁻¹ := by group
        _ = (y * z * y⁻¹ * z⁻¹) * ((y * z' * y⁻¹ * z'⁻¹) * z) * z⁻¹ := by rw [h1]
        _ = (y * z * y⁻¹ * z⁻¹) * (y * z' * y⁻¹ * z'⁻¹) := by group
    rw [e]
    exact (Subgroup.zpowers t).mul_mem he he'
  inv_mem' := by
    rintro z ⟨hz, he⟩
    refine ⟨(Cen t).inv_mem hz, ?_⟩
    have he' : (y * z * y⁻¹ * z⁻¹)⁻¹ ∈ Subgroup.zpowers t := (Subgroup.zpowers t).inv_mem he
    have h1 := cen_mul_zpowers ((Cen t).inv_mem hz) he'
    have e : y * z⁻¹ * y⁻¹ * z⁻¹⁻¹ = (y * z * y⁻¹ * z⁻¹)⁻¹ := by
      calc y * z⁻¹ * y⁻¹ * z⁻¹⁻¹
          = z⁻¹ * (y * z * y⁻¹ * z⁻¹)⁻¹ * z := by group
        _ = (y * z * y⁻¹ * z⁻¹)⁻¹ * z⁻¹ * z := by rw [h1]
        _ = (y * z * y⁻¹ * z⁻¹)⁻¹ := by group
    rw [e]
    exact he'

theorem pow_pow_eq_self {a : G} (h : a ^ 3 = 1) : (a ^ 2) ^ 2 = a := by
  rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h, one_mul]

theorem rep_closure_pair {b₁ b₂ : G} (h3 : b₁ ^ 3 = 1) (h3' : b₂ ^ 3 = 1)
    (hc : b₁ * b₂ = b₂ * b₁) :
    ∀ x ∈ Subgroup.closure ({b₁, b₂} : Set G), ∃ i j : ℕ, x = b₁ ^ i * b₂ ^ j := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨k, l, rfl⟩ := hy
    refine ⟨i + k, j + l, ?_⟩
    have h := (Commute.pow_pow (show Commute b₁ b₂ from hc) k j).eq
    calc b₁ ^ i * b₂ ^ j * (b₁ ^ k * b₂ ^ l)
        = b₁ ^ i * (b₂ ^ j * b₁ ^ k) * b₂ ^ l := by group
      _ = b₁ ^ i * (b₁ ^ k * b₂ ^ j) * b₂ ^ l := by rw [h]
      _ = b₁ ^ (i + k) * b₂ ^ (j + l) := by rw [pow_add, pow_add]; group
  | inv x _ hx =>
    obtain ⟨i, j, rfl⟩ := hx
    refine ⟨2 * i, 2 * j, ?_⟩
    have e1 : (b₁ ^ i)⁻¹ = b₁ ^ (2 * i) := inv_eq_of_mul_eq_one_right (by
      rw [← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, h3, one_pow])
    have e2 : (b₂ ^ j)⁻¹ = b₂ ^ (2 * j) := inv_eq_of_mul_eq_one_right (by
      rw [← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, h3', one_pow])
    rw [mul_inv_rev, e1, e2]
    exact ((Commute.pow_pow (show Commute b₁ b₂ from hc) (2 * i) (2 * j)).eq).symm

theorem card_closure_pair_le [Finite G] {b₁ b₂ : G} (h3 : b₁ ^ 3 = 1) (h3' : b₂ ^ 3 = 1)
    (hc : b₁ * b₂ = b₂ * b₁) : Nat.card (Subgroup.closure ({b₁, b₂} : Set G)) ≤ 9 := by
  classical
  have hsub : (Subgroup.closure ({b₁, b₂} : Set G) : Set G) ⊆
      ((Finset.univ : Finset (Fin 3 × Fin 3)).image
        fun p => b₁ ^ (p.1 : ℕ) * b₂ ^ (p.2 : ℕ) : Finset G) := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := rep_closure_pair h3 h3' hc x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    simp only
    rw [← pow_eq_pow_mod i h3, ← pow_eq_pow_mod j h3']
  calc Nat.card (Subgroup.closure ({b₁, b₂} : Set G))
      = (Subgroup.closure ({b₁, b₂} : Set G) : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ ((Finset.univ : Finset (Fin 3 × Fin 3)).image
        fun p => b₁ ^ (p.1 : ℕ) * b₂ ^ (p.2 : ℕ) : Finset G).card := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ 9 := Finset.card_image_le.trans (by simp)

theorem sec4_facts [Finite G] {b : G} {J B : Subgroup G} {b₁ b₂ : G}
    (h4 : FF79Sec4 b J B b₁ b₂) :
    b₁ ^ 3 = 1 ∧ b₂ ^ 3 = 1 ∧ b₁ * b₂ = b₂ * b₁ ∧ b₂ ∉ Subgroup.zpowers b₁ ∧
      Nat.card (Subgroup.closure ({b₁, b₂} : Set G)) = 3 ^ 2 ∧
      (∀ x ∈ Subgroup.closure ({b₁, b₂} : Set G), x ^ 3 = 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hEl, hcardB⟩ := h4.mono.1
  haveI := hEl
  have hB3 : ∀ g ∈ B, g ^ 3 = 1 := fun g hg =>
    elemPow_eq_one_of_isElementaryAbelian (A := B) g hg
  have hb₁B : b₁ ∈ B := (Subgroup.mem_inf.mp h4.hb₁).1
  have hb₂B : b₂ ∈ B := (Subgroup.mem_inf.mp h4.hb₂).1
  have hb13 := hB3 b₁ hb₁B
  have hb23 := hB3 b₂ hb₂B
  have hcomm : b₁ * b₂ = b₂ * b₁ :=
    congrArg Subtype.val (hEl.toIsMulCommutative.is_comm.comm ⟨b₁, hb₁B⟩ ⟨b₂, hb₂B⟩)
  have hBeq := h4.mono.2.1
  obtain ⟨c, -, hc1, hc2, hc3⟩ := h4.mono.2.2.2.2.2
  have hK1 : b₂ ∉ Subgroup.zpowers b₁ := by
    intro hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hbm : b = b₁ ^ (m * m) := by
      calc b = c * b₂ * c⁻¹ := hc3.symm
        _ = c * b₁ ^ m * c⁻¹ := by rw [hm]
        _ = (c * b₁ * c⁻¹) ^ m := conj_zpow.symm
        _ = b₂ ^ m := by rw [hc2]
        _ = b₁ ^ (m * m) := by rw [← hm, ← zpow_mul]
    have hle : B ≤ Subgroup.zpowers b₁ := by
      rw [hBeq]
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h
      · rw [h, hbm]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b₁) _
      · rw [h]; exact Subgroup.mem_zpowers b₁
      · rw [h]; exact hmem
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hcardB] at h1
    have h2 : orderOf b₁ ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hb13)
    omega
  have hb1 : b₁ ≠ 1 := by
    intro h
    apply hK1
    rw [← hc2, h]
    simp
  have hAB : Subgroup.closure ({b₁, b₂} : Set G) ≤ B := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h <;> rw [h] <;> assumption
  have hA3 : ∀ x ∈ Subgroup.closure ({b₁, b₂} : Set G), x ^ 3 = 1 := fun x hx => hB3 x (hAB hx)
  have ho : orderOf b₁ = 3 := orderOf_eq_prime hb13 hb1
  have hz : Nat.card (Subgroup.zpowers b₁) = 3 := by rw [Nat.card_zpowers, ho]
  have hzA : Subgroup.zpowers b₁ ≤ Subgroup.closure ({b₁, b₂} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hlt : 3 < Nat.card (Subgroup.closure ({b₁, b₂} : Set G)) := by
    by_contra hcon
    have heq := Subgroup.eq_of_le_of_card_ge hzA (by omega)
    apply hK1
    rw [heq]
    exact Subgroup.subset_closure (by simp)
  have hdvd : Nat.card (Subgroup.closure ({b₁, b₂} : Set G)) ∣ 27 := by
    have := Subgroup.card_dvd_of_le hAB
    rw [hcardB] at this
    simpa using this
  have hle9 := card_closure_pair_le hb13 hb23 hcomm
  refine ⟨hb13, hb23, hcomm, hK1, ?_, hA3⟩
  generalize Nat.card (Subgroup.closure ({b₁, b₂} : Set G)) = n at *
  interval_cases n <;> omega

theorem kcase {b₁ b₂ z : G} (hb13 : b₁ ^ 3 = 1) (hb23 : b₂ ^ 3 = 1) (hcomm : b₁ * b₂ = b₂ * b₁)
    (hP : ∀ x, (x = b₁ * b₂ ∨ x = b₁ ^ 2 * b₂) → z * x = x * z →
      z * b₁ = b₁ * z ∧ z * b₂ = b₂ * z)
    {i j : ℕ} (hx1 : b₁ ^ i * b₂ ^ j ≠ 1) (hz : z * (b₁ ^ i * b₂ ^ j) = (b₁ ^ i * b₂ ^ j) * z) :
    z * b₁ = b₁ * z ∨ z * b₂ = b₂ * z := by
  have hC : Commute b₁ b₂ := hcomm
  rw [pow_eq_pow_mod i hb13, pow_eq_pow_mod j hb23] at hx1 hz
  have hi : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hj : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize i % 3 = i' at *
  generalize j % 3 = j' at *
  have pow2 : ∀ w : G, w ^ 3 = 1 → z * w ^ 2 = w ^ 2 * z → z * w = w * z := by
    intro w hw h
    have := (show Commute z (w ^ 2) from h).pow_right 2
    rw [pow_pow_eq_self hw] at this
    exact this
  interval_cases i' <;> interval_cases j'
  · exact absurd (by simp) hx1
  · simp only [pow_zero, pow_one, one_mul] at hz; exact Or.inr hz
  · simp only [pow_zero, one_mul] at hz; exact Or.inr (pow2 b₂ hb23 hz)
  · simp only [pow_zero, pow_one, mul_one] at hz; exact Or.inl hz
  · simp only [pow_one] at hz; exact Or.inl (hP _ (Or.inl rfl) hz).1
  · simp only [pow_one] at hz
    have h2 := (show Commute z (b₁ * b₂ ^ 2) from hz).pow_right 2
    rw [(hC.pow_right 2).mul_pow, pow_pow_eq_self hb23] at h2
    exact Or.inl (hP _ (Or.inr rfl) h2).1
  · simp only [pow_zero, mul_one] at hz; exact Or.inl (pow2 b₁ hb13 hz)
  · simp only [pow_one] at hz; exact Or.inl (hP _ (Or.inr rfl) hz).1
  · have h2 := (show Commute z (b₁ ^ 2 * b₂ ^ 2) from hz).pow_right 2
    rw [(hC.pow_pow 2 2).mul_pow, pow_pow_eq_self hb13, pow_pow_eq_self hb23] at h2
    exact Or.inl (hP _ (Or.inl rfl) h2).1

theorem gen_by_cent [Finite G] {T : Subgroup G} (hTp : IsPGroup 2 ↥T) {b₁ b₂ : G}
    (hb13 : b₁ ^ 3 = 1) (hb23 : b₂ ^ 3 = 1) (hcomm : b₁ * b₂ = b₂ * b₁)
    (hcard : Nat.card (Subgroup.closure ({b₁, b₂} : Set G)) = 3 ^ 2)
    (hA3 : ∀ x ∈ Subgroup.closure ({b₁, b₂} : Set G), x ^ 3 = 1)
    (hAn : Subgroup.closure ({b₁, b₂} : Set G) ≤ Subgroup.normalizer (T : Set G))
    (hP : ∀ x, (x = b₁ * b₂ ∨ x = b₁ ^ 2 * b₂) → ∀ z ∈ T, z * x = x * z →
      z * b₁ = b₁ * z ∧ z * b₂ = b₂ * z)
    (W : Subgroup G) (hW : ∀ z ∈ T, (z * b₁ = b₁ * z ∨ z * b₂ = b₂ * z) → z ∈ W) : T ≤ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcompl : ¬ 3 ∣ Nat.card ↥T := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hTp
    intro h3
    rw [hn] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    3 Nat.prime_three (Subgroup.closure ({b₁, b₂} : Set G)) T
    (fun m => Subtype.ext (by simpa using hA3 m.1 m.2)) hcard hcompl hAn
  rw [hgen]
  refine iSup_le fun x => iSup_le fun hx1 z hz => ?_
  obtain ⟨hzT, hzx⟩ := Subgroup.mem_inf.mp hz
  have hzx' : z * (x : G) = x * z := Subgroup.mem_centralizer_singleton_iff.mp hzx
  have hxA : (x : G) ∈ Subgroup.closure ({b₁, b₂} : Set G) := x.2
  have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  apply hW z hzT
  obtain ⟨i, j, hij⟩ := rep_closure_pair hb13 hb23 hcomm _ hxA
  rw [hij] at hzx' hx1'
  exact kcase hb13 hb23 hcomm (fun w hw hzw => hP w hw z hzT hzw) hx1' hzx'

theorem extraspecial_aux [Finite G] (h16 : FF79_1_6) {t : G} (ht : orderOf t = 2)
    {J T : Subgroup G} {b₁ b₂ : G}
    (hJL : IsLnq 5 2 1 J) (hJC : J ≤ Cen t) (hβJ : b₁ * b₂ ∈ J)
    (hβo : orderOf (b₁ * b₂) = 3)
    (hTC : T ≤ Cen t) (hTconj : ∀ c ∈ Cen t, ∀ y ∈ T, c * y * c⁻¹ ∈ T) (hTp : IsPGroup 2 ↥T)
    (htT : t ∈ T) (hTcent : ∀ c ∈ Cen t, (∀ y ∈ T, c * y = y * c) → c ∈ T)
    (hgen : ∀ W : Subgroup G, (∀ z ∈ T, (z * b₁ = b₁ * z ∨ z * b₂ = b₂ * z) → z ∈ W) → T ≤ W)
    (hβ' : ∀ x, (x = b₁ * b₂ ∨ x = b₁ ^ 2 * b₂) → ∀ y ∈ T ⊓ Cen x,
      y * b₁ = b₁ * y ∧ y * b₂ = b₂ * y ∧ y ^ 2 ∈ Subgroup.zpowers t)
    (hZ' : ∀ y ∈ T ⊓ Cen (b₁ * b₂), (∀ z ∈ T, y * z = z * y) → y ∈ Subgroup.zpowers t)
    (hb' : ∀ x, (x = b₁ ∨ x = b₂) → ∀ y ∈ T ⊓ Cen x, ∀ z ∈ T ⊓ Cen x,
      y * z * y⁻¹ * z⁻¹ ∈ Subgroup.zpowers t) :
    IsExtraspecialPGroup 2 ↥T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβC : b₁ * b₂ ∈ Cen t := hJC hβJ
  have hJT : J ≤ Nor T := le_nor_of_conj_mem fun j hj s hs => hTconj j (hJC hj) s hs
  have hTcomm : ∀ y ∈ T, y ^ 2 ∈ Subgroup.zpowers t ∧
      ∀ z ∈ T, y * z * y⁻¹ * z⁻¹ ∈ Subgroup.zpowers t := by
    have h5 : sqComm t T hTC = T := by
      refine h16 G J T (sqComm t T hTC) hJL hTp hJT (fun y hy => hy.1)
        (le_nor_of_conj_mem fun j hj s hs => conj_mem_sqComm hTC hTconj (hJC hj) hs)
        (b₁ * b₂) hβJ hβo ?_
      intro y hy
      obtain ⟨hyT, hyβ⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨hy1, hy2, hy3⟩ := hβ' (b₁ * b₂) (Or.inl rfl) y hy
      refine ⟨hyT, hy3, fun z hz => ?_⟩
      have hyb₁ : y ∈ T ⊓ Cen b₁ :=
        Subgroup.mem_inf.mpr ⟨hyT, Subgroup.mem_centralizer_singleton_iff.mpr hy1⟩
      have hyb₂ : y ∈ T ⊓ Cen b₂ :=
        Subgroup.mem_inf.mpr ⟨hyT, Subgroup.mem_centralizer_singleton_iff.mpr hy2⟩
      have hle : T ≤ commSub t y := by
        refine hgen (commSub t y) fun z hzT hzc => ⟨hTC hzT, ?_⟩
        rcases hzc with h | h
        · exact hb' b₁ (Or.inl rfl) y hyb₁ z
            (Subgroup.mem_inf.mpr ⟨hzT, Subgroup.mem_centralizer_singleton_iff.mpr h⟩)
        · exact hb' b₂ (Or.inr rfl) y hyb₂ z
            (Subgroup.mem_inf.mpr ⟨hzT, Subgroup.mem_centralizer_singleton_iff.mpr h⟩)
      exact (hle hz).2
    intro y hy
    have : y ∈ sqComm t T hTC := by rw [h5]; exact hy
    exact ⟨this.2.1, this.2.2⟩
  have hZeq : Subgroup.zpowers t = T ⊓ CenS T := by
    have hzT : Subgroup.zpowers t ≤ T ⊓ CenS T := by
      intro c hc
      refine Subgroup.mem_inf.mpr ⟨Subgroup.zpowers_le.mpr htT hc, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun h hh => cen_mul_zpowers (hTC hh) hc
    have hJZ : J ≤ Nor (T ⊓ CenS T) := by
      refine le_nor_of_conj_mem fun j hj s hs => ?_
      obtain ⟨hsT, hs2⟩ := Subgroup.mem_inf.mp hs
      refine Subgroup.mem_inf.mpr ⟨hTconj j (hJC hj) s hsT, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro h hh
      have hh' : j⁻¹ * h * j ∈ T := by
        simpa using hTconj j⁻¹ ((Cen t).inv_mem (hJC hj)) h hh
      have h1 := Subgroup.mem_centralizer_iff.mp hs2 _ hh'
      calc h * (j * s * j⁻¹) = j * ((j⁻¹ * h * j) * s) * j⁻¹ := by group
        _ = j * (s * (j⁻¹ * h * j)) * j⁻¹ := by rw [h1]
        _ = (j * s * j⁻¹) * h := by group
    have hJzp : J ≤ Nor (Subgroup.zpowers t) :=
      le_nor_of_conj_mem fun j hj s hs => by rw [conj_fix_zpowers (hJC hj) hs]; exact hs
    refine h16 G J (T ⊓ CenS T) (Subgroup.zpowers t) hJL (hTp.to_le inf_le_left) hJZ hzT hJzp
      (b₁ * b₂) hβJ hβo ?_
    intro y hy
    obtain ⟨hyZ, hyβ⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨hyT, hyc⟩ := Subgroup.mem_inf.mp hyZ
    exact hZ' y (Subgroup.mem_inf.mpr ⟨hyT, hyβ⟩)
      (fun z hz => (Subgroup.mem_centralizer_iff.mp hyc z hz).symm)
  have hnab : ¬ ∀ y ∈ T, ∀ z ∈ T, y * z = z * y := by
    intro hab
    have hTz : T ≤ Subgroup.zpowers t := by
      intro y hy
      rw [hZeq]
      exact Subgroup.mem_inf.mpr ⟨hy,
        Subgroup.mem_centralizer_iff.mpr fun z hz => hab z hz y hy⟩
    have hβT : b₁ * b₂ ∈ T := hTcent _ hβC fun y hy => cen_mul_zpowers hβC (hTz hy)
    have hdvd : orderOf (b₁ * b₂) ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers t) (hTz hβT)
      rwa [Nat.card_zpowers, ht] at this
    rw [hβo] at hdvd
    omega
  have hZc : ∀ x : ↥T, x ∈ Subgroup.center ↥T ↔ (x : G) ∈ Subgroup.zpowers t := by
    intro x
    constructor
    · intro hx
      rw [hZeq]
      refine Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hy⟩)
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (cen_mul_zpowers (hTC g.2) hx)
  have hcard : Nat.card ↥(Subgroup.center ↥T) = 2 := by
    have hmap : (Subgroup.center ↥T).map T.subtype = Subgroup.zpowers t := by
      ext c
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hZc x).mp hx
      · intro hc
        have hcT : c ∈ T := Subgroup.zpowers_le.mpr htT hc
        exact ⟨⟨c, hcT⟩, (hZc ⟨c, hcT⟩).mpr hc, rfl⟩
    rw [← Subgroup.card_map_of_injective T.subtype_injective, hmap, Nat.card_zpowers, ht]
  have hpow : ∀ a : ↥T, a ^ 2 ∈ Subgroup.center ↥T := fun a =>
    (hZc _).mpr (by simpa using (hTcomm a.1 a.2).1)
  have hle : ⁅(⊤ : Subgroup ↥T), ⊤⁆ ≤ Subgroup.center ↥T := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    refine (hZc _).mpr ?_
    have := (hTcomm a.1 a.2).2 b.1 b.2
    simpa [commutatorElement_def] using this
  have hcomm : ⁅(⊤ : Subgroup ↥T), ⊤⁆ = Subgroup.center ↥T := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hne : (⁅(⊤ : Subgroup ↥T), (⊤ : Subgroup ↥T)⁆ : Subgroup ↥T) ≠ (⊥ : Subgroup ↥T) := by
      intro hbot
      apply hnab
      intro y hy z hz
      have h1 : ⁅(⟨y, hy⟩ : ↥T), (⟨z, hz⟩ : ↥T)⁆ ∈ ⁅(⊤ : Subgroup ↥T), ⊤⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [hbot, Subgroup.mem_bot, commutatorElement_def] at h1
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h2
      calc y * z = (y * z * y⁻¹ * z⁻¹) * (z * y) := by group
        _ = z * y := by rw [h2, one_mul]
    generalize (⁅(⊤ : Subgroup ↥T), (⊤ : Subgroup ↥T)⁆ : Subgroup ↥T) = K at hne ⊢
    have h1 : Nat.card ↥K ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
    have h0 := Nat.card_pos (α := ↥K)
    omega
  have hfr := CFSG.Sporadic.Recognition.LyonsSims.frattini_eq_of_commutator_eq (p := 2) hTp
    hcomm hpow
  exact ⟨hTp, (_root_.commutator_def ↥T).trans hcomm, hfr, hcard⟩

theorem ff79_4_4X_of (h16 : FF79_1_6) (hJ5 : FF79_JL5) (hJ : FF79_4_4J) (hβ : FF79_4_4Beta)
    (hZ : FF79_4_4Z) (hb : FF79_4_4Bi) : FF79_4_4X := by
  intro G _ _ b J B b₁ b₂ h4 t ht hc1 hc2 hinv
  have hI : FF79Inv b b₁ b₂ t := ⟨ht, hc1, hc2, hinv⟩
  obtain ⟨hb13, hb23, hcomm, hK1, hcardA, hA3⟩ := sec4_facts h4
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJC : J ≤ Cen t := hJ G b J B b₁ b₂ h4 t hI
  have hJL : IsLnq 5 2 1 J := hJ5 G b J h4.hyp
  have hβJ : b₁ * b₂ ∈ J :=
    J.mul_mem (Subgroup.mem_inf.mp h4.hb₁).2 (Subgroup.mem_inf.mp h4.hb₂).2
  have hβ1 : b₁ * b₂ ≠ 1 := by
    intro h
    apply hK1
    rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers b₁)
  have hβ3 : (b₁ * b₂) ^ 3 = 1 := by
    rw [(show Commute b₁ b₂ from hcomm).mul_pow, hb13, hb23, one_mul]
  have hβo : orderOf (b₁ * b₂) = 3 := orderOf_eq_prime hβ3 hβ1
  have hb₁C : b₁ ∈ Cen t := Subgroup.mem_centralizer_singleton_iff.mpr hc1.symm
  have hb₂C : b₂ ∈ Cen t := Subgroup.mem_centralizer_singleton_iff.mpr hc2.symm
  have hAC : Subgroup.closure ({b₁, b₂} : Set G) ≤ Cen t := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h <;> rw [h] <;> assumption
  have hAn : Subgroup.closure ({b₁, b₂} : Set G) ≤ Subgroup.normalizer (Op 2 (Cen t) : Set G) :=
    hAC.trans (le_nor_of_conj_mem fun j hj s hs => op2_conj_mem hj hs)
  have hβ' := hβ G b J B b₁ b₂ h4 t hI
  have hP : ∀ x, (x = b₁ * b₂ ∨ x = b₁ ^ 2 * b₂) → ∀ z ∈ Op 2 (Cen t), z * x = x * z →
      z * b₁ = b₁ * z ∧ z * b₂ = b₂ * z := fun x hx z hz hzx => by
    obtain ⟨h1, h2, -⟩ := hβ' x hx z
      (Subgroup.mem_inf.mpr ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr hzx⟩)
    exact ⟨h1, h2⟩
  have hgen : ∀ W : Subgroup G, (∀ z ∈ Op 2 (Cen t),
      (z * b₁ = b₁ * z ∨ z * b₂ = b₂ * z) → z ∈ W) → Op 2 (Cen t) ≤ W := fun W hW =>
    gen_by_cent (op2_isPGroup t) hb13 hb23 hcomm hcardA hA3 hAn hP W hW
  exact extraspecial_aux h16 ht hJL hJC hβJ hβo (op2_le_cen t)
    (fun c hc y hy => op2_conj_mem hc hy) (op2_isPGroup t) (self_mem_op2 ht)
    (fun c hc h => mem_op2_of_centralizes h4.char2 ht hc h) hgen hβ'
    (hZ G b J B b₁ b₂ h4 t hI) (hb G b J B b₁ b₂ h4 t hI)

end CFSG.RankThree.PartTwo.Sec21.FF79

