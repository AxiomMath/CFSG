module

public import CFSG.RankThree.PartOne.S11b.Sec109SylowTransport

public section

namespace CFSG.RankThree.PartOne

open Subgroup Matrix

namespace Sec109

namespace SylowModel

section Abstract

variable {G : Type} [Group G]

theorem conj_mem_closure_pair {a b y : G}
    (ha : y * a * y⁻¹ ∈ Subgroup.closure ({a, b} : Set G))
    (hb : y * b * y⁻¹ ∈ Subgroup.closure ({a, b} : Set G)) {g : G}
    (hg : g ∈ Subgroup.closure ({a, b} : Set G)) :
    y * g * y⁻¹ ∈ Subgroup.closure ({a, b} : Set G) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hb
  | one => simp [one_mem]
  | mul x z _ _ hx hz =>
    have : y * (x * z) * y⁻¹ = (y * x * y⁻¹) * (y * z * y⁻¹) := by group
    rw [this]
    exact mul_mem hx hz
  | inv x _ hx =>
    have : y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem mem_normalizer_closure_pair {a b y : G}
    (ha : y * a * y⁻¹ ∈ Subgroup.closure ({a, b} : Set G))
    (hb : y * b * y⁻¹ ∈ Subgroup.closure ({a, b} : Set G))
    (ha' : y⁻¹ * a * y ∈ Subgroup.closure ({a, b} : Set G))
    (hb' : y⁻¹ * b * y ∈ Subgroup.closure ({a, b} : Set G)) :
    y ∈ normalizer ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  constructor
  · exact conj_mem_closure_pair ha hb
  · intro h
    have := conj_mem_closure_pair (y := y⁻¹) (by rwa [inv_inv]) (by rwa [inv_inv]) h
    simpa [mul_assoc] using this

theorem closure_pair_eq_sup_zpowers (a b : G) :
    Subgroup.closure ({a, b} : Set G) = zpowers a ⊔ zpowers b := by
  rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure]

def zpowersProdHom {a b : G} (hab : Commute a b) : zpowers a × zpowers b →* G :=
  (zpowers a).subtype.noncommCoprod (zpowers b).subtype (by
    rintro ⟨m, hm⟩ ⟨n, hn⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hm
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hn
    exact hab.zpow_zpow i j)

theorem zpowersProdHom_range {a b : G} (hab : Commute a b) :
    (zpowersProdHom hab).range = zpowers a ⊔ zpowers b := by
  rw [zpowersProdHom, MonoidHom.noncommCoprod_range, Subgroup.range_subtype,
    Subgroup.range_subtype]

theorem exists_zpow_mul_zpow_of_mem_closure_pair {a b : G} (hab : Commute a b) {g : G}
    (hg : g ∈ Subgroup.closure ({a, b} : Set G)) : ∃ i j : ℤ, a ^ i * b ^ j = g := by
  rw [closure_pair_eq_sup_zpowers, ← zpowersProdHom_range hab] at hg
  obtain ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, rfl⟩ := hg
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
  exact ⟨i, j, rfl⟩

theorem card_closure_pair {a b : G} (hab : Commute a b) (ha : orderOf a = 7)
    (hb : orderOf b = 7) (hdisj : Disjoint (zpowers a) (zpowers b)) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) = 49 := by
  have hinj : Function.Injective (zpowersProdHom hab) := by
    rw [zpowersProdHom, MonoidHom.noncommCoprod_injective]
    refine ⟨Subtype.val_injective, Subtype.val_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact hdisj
  have h1 : Nat.card (zpowersProdHom hab).range = Nat.card (zpowers a × zpowers b) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [zpowersProdHom_range, ← closure_pair_eq_sup_zpowers] at h1
  rw [h1, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, ha, hb]

theorem zpowers_eq_closure_inf_centralizer {b₁ b₂ x : G} (hbb : Commute b₁ b₂)
    (hxb : Commute x b₂) (hxa : x * b₁ * x⁻¹ = b₁ ^ 2) :
    zpowers b₂ = Subgroup.closure ({b₁, b₂} : Set G) ⊓ centralizer ({x} : Set G) := by
  have hb₂B : b₂ ∈ Subgroup.closure ({b₁, b₂} : Set G) := subset_closure (by simp)
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hg
    exact ⟨zpow_mem hb₂B j, (hxb.zpow_right j).symm.eq⟩
  · rintro ⟨hgB, hgx⟩
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_closure_pair hbb hgB
    have h3 : b₁ ^ i * x * b₂ ^ j = x * b₁ ^ i * b₂ ^ j := by
      calc b₁ ^ i * x * b₂ ^ j = b₁ ^ i * (x * b₂ ^ j) := by rw [mul_assoc]
        _ = b₁ ^ i * (b₂ ^ j * x) := by rw [(hxb.zpow_right j).eq]
        _ = b₁ ^ i * b₂ ^ j * x := by rw [mul_assoc]
        _ = x * (b₁ ^ i * b₂ ^ j) := hgx
        _ = x * b₁ ^ i * b₂ ^ j := by rw [mul_assoc]
    have h4 : b₁ ^ i * x = x * b₁ ^ i := mul_right_cancel h3
    have h5 : (b₁ ^ 2) ^ i = b₁ ^ i := by
      rw [← hxa, conj_zpow, ← h4, mul_inv_cancel_right]
    have h6 : b₁ ^ i * b₁ ^ i = b₁ ^ i := by
      have h8 : (b₁ ^ 2) ^ i = b₁ ^ i * b₁ ^ i := by
        rw [pow_two, (Commute.refl b₁).mul_zpow]
      rw [← h8, h5]
    have h7 : b₁ ^ i = 1 := mul_left_cancel (h6.trans (mul_one _).symm)
    exact ⟨j, by rw [h7, one_mul]⟩

theorem structureB_closure_pair {b₁ b₂ x₁ x₂ : G}
    (hbb : Commute b₁ b₂) (hxx : Commute x₁ x₂) (h₁₂ : Commute x₁ b₂) (h₂₁ : Commute x₂ b₁)
    (hx₁b₁ : x₁ * b₁ * x₁⁻¹ = b₁ ^ 2) (hx₂b₂ : x₂ * b₂ * x₂⁻¹ = b₂ ^ 2)
    (hb₁7 : b₁ ^ 7 = 1) (hb₂7 : b₂ ^ 7 = 1) (hb₁ : b₁ ≠ 1) (hb₂ : b₂ ≠ 1)
    (hx₁3 : x₁ ^ 3 = 1) (hx₂3 : x₂ ^ 3 = 1) (hx₁ : x₁ ≠ 1) (hx₂ : x₂ ≠ 1)
    (hdisj : ∀ i j : ℤ, b₁ ^ i = b₂ ^ j → b₁ ^ i = 1)
    (hcent : ∀ g : G, g * b₁ = b₁ * g → g * b₂ = b₂ * g →
      g ∈ Subgroup.closure ({b₁, b₂} : Set G)) :
    Nat.card (Subgroup.closure ({b₁, b₂} : Set G)) = 49 ∧
      StructureB (⊤ : Subgroup G) (Subgroup.closure ({b₁, b₂} : Set G)) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hb₁B : b₁ ∈ Subgroup.closure ({b₁, b₂} : Set G) := subset_closure (by simp)
  have hb₂B : b₂ ∈ Subgroup.closure ({b₁, b₂} : Set G) := subset_closure (by simp)
  have hord₁ : orderOf b₁ = 7 := orderOf_eq_prime hb₁7 hb₁
  have hord₂ : orderOf b₂ = 7 := orderOf_eq_prime hb₂7 hb₂
  have hox₁ : orderOf x₁ = 3 := orderOf_eq_prime hx₁3 hx₁
  have hox₂ : orderOf x₂ = 3 := orderOf_eq_prime hx₂3 hx₂
  have hrep : ∀ {g : G}, g ∈ Subgroup.closure ({b₁, b₂} : Set G) →
      ∃ i j : ℤ, b₁ ^ i * b₂ ^ j = g := fun hg =>
    exists_zpow_mul_zpow_of_mem_closure_pair hbb hg
  have hdisj' : Disjoint (zpowers b₁) (zpowers b₂) := by
    rw [Subgroup.disjoint_def]
    intro g hg1 hg2
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg1
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hg2
    exact hdisj i j hj.symm
  have hcard : Nat.card (Subgroup.closure ({b₁, b₂} : Set G)) = 49 :=
    card_closure_pair hbb hord₁ hord₂ hdisj'
  have hx₁b₂ : x₁ * b₂ * x₁⁻¹ = b₂ := by rw [h₁₂.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hx₂b₁ : x₂ * b₁ * x₂⁻¹ = b₁ := by rw [h₂₁.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hx₁b₁' : x₁⁻¹ * b₁ * x₁ = b₁ ^ 4 := by
    have e1 : x₁ * b₁ ^ 4 * x₁⁻¹ = b₁ := by
      rw [← conj_pow, hx₁b₁, ← pow_mul]
      calc b₁ ^ (2 * 4) = b₁ ^ 7 * b₁ := by rw [← pow_succ]
        _ = b₁ := by rw [hb₁7, one_mul]
    calc x₁⁻¹ * b₁ * x₁ = x₁⁻¹ * (x₁ * b₁ ^ 4 * x₁⁻¹) * x₁ := by rw [e1]
      _ = b₁ ^ 4 := by group
  have hx₂b₂' : x₂⁻¹ * b₂ * x₂ = b₂ ^ 4 := by
    have e1 : x₂ * b₂ ^ 4 * x₂⁻¹ = b₂ := by
      rw [← conj_pow, hx₂b₂, ← pow_mul]
      calc b₂ ^ (2 * 4) = b₂ ^ 7 * b₂ := by rw [← pow_succ]
        _ = b₂ := by rw [hb₂7, one_mul]
    calc x₂⁻¹ * b₂ * x₂ = x₂⁻¹ * (x₂ * b₂ ^ 4 * x₂⁻¹) * x₂ := by rw [e1]
      _ = b₂ ^ 4 := by group
  have hx₁b₂' : x₁⁻¹ * b₂ * x₁ = b₂ := by
    calc x₁⁻¹ * b₂ * x₁ = x₁⁻¹ * (x₁ * b₂) := by rw [mul_assoc, ← h₁₂.eq]
      _ = b₂ := inv_mul_cancel_left _ _
  have hx₂b₁' : x₂⁻¹ * b₁ * x₂ = b₁ := by
    calc x₂⁻¹ * b₁ * x₂ = x₂⁻¹ * (x₂ * b₁) := by rw [mul_assoc, ← h₂₁.eq]
      _ = b₁ := inv_mul_cancel_left _ _
  have hn₁ : x₁ ∈ normalizer ((Subgroup.closure ({b₁, b₂} : Set G) : Subgroup G) : Set G) := by
    refine mem_normalizer_closure_pair ?_ ?_ ?_ ?_
    · rw [hx₁b₁]; exact pow_mem hb₁B 2
    · rw [hx₁b₂]; exact hb₂B
    · rw [hx₁b₁']; exact pow_mem hb₁B 4
    · rw [hx₁b₂']; exact hb₂B
  have hn₂ : x₂ ∈ normalizer ((Subgroup.closure ({b₁, b₂} : Set G) : Subgroup G) : Set G) := by
    refine mem_normalizer_closure_pair ?_ ?_ ?_ ?_
    · rw [hx₂b₁]; exact hb₁B
    · rw [hx₂b₂]; exact pow_mem hb₂B 2
    · rw [hx₂b₁']; exact hb₁B
    · rw [hx₂b₂']; exact pow_mem hb₂B 4
  have hz₂ := zpowers_eq_closure_inf_centralizer hbb h₁₂ hx₁b₁
  have hz₁ : zpowers b₁ = Subgroup.closure ({b₁, b₂} : Set G) ⊓ centralizer ({x₂} : Set G) := by
    rw [Set.pair_comm]
    exact zpowers_eq_closure_inf_centralizer hbb.symm h₂₁ hx₂b₂
  have hconjx : ∀ (y u v : G), y * (u * v) * y⁻¹ = (y * u * y⁻¹) * (y * v * y⁻¹) := by
    intro y u v; group
  have hy₁ : x₁ * x₂ * b₁ * (x₁ * x₂)⁻¹ = b₁ ^ 2 := by
    calc x₁ * x₂ * b₁ * (x₁ * x₂)⁻¹ = x₁ * (x₂ * b₁ * x₂⁻¹) * x₁⁻¹ := by group
      _ = b₁ ^ 2 := by rw [hx₂b₁, hx₁b₁]
  have hy₂ : x₁ * x₂ * b₂ * (x₁ * x₂)⁻¹ = b₂ ^ 2 := by
    calc x₁ * x₂ * b₂ * (x₁ * x₂)⁻¹ = x₁ * (x₂ * b₂ * x₂⁻¹) * x₁⁻¹ := by group
      _ = x₁ * b₂ ^ 2 * x₁⁻¹ := by rw [hx₂b₂]
      _ = (x₁ * b₂ * x₁⁻¹) ^ 2 := by rw [conj_pow]
      _ = b₂ ^ 2 := by rw [hx₁b₂]
  have hact : ∀ b ∈ Subgroup.closure ({b₁, b₂} : Set G),
      x₁ * x₂ * b * (x₁ * x₂)⁻¹ = b ^ (2 : ℤ) := by
    intro b hb
    obtain ⟨i, j, rfl⟩ := hrep hb
    have hc : Commute (b₂ ^ j) (b₁ ^ i) := (hbb.symm).zpow_zpow j i
    rw [hconjx, ← conj_zpow, ← conj_zpow, hy₁, hy₂, zpow_two]
    have e1 : (b₁ ^ 2) ^ i = b₁ ^ i * b₁ ^ i := by
      rw [pow_two, (Commute.refl b₁).mul_zpow]
    have e2 : (b₂ ^ 2) ^ j = b₂ ^ j * b₂ ^ j := by
      rw [pow_two, (Commute.refl b₂).mul_zpow]
    rw [e1, e2]
    calc b₁ ^ i * b₁ ^ i * (b₂ ^ j * b₂ ^ j)
        = b₁ ^ i * (b₁ ^ i * b₂ ^ j) * b₂ ^ j := by simp only [mul_assoc]
      _ = b₁ ^ i * (b₂ ^ j * b₁ ^ i) * b₂ ^ j := by rw [hc.eq]
      _ = b₁ ^ i * b₂ ^ j * (b₁ ^ i * b₂ ^ j) := by simp only [mul_assoc]
  have hxne : x₁ * x₂ ≠ 1 := by
    intro h
    have h1 := hact b₁ hb₁B
    rw [h, inv_one, one_mul, mul_one, zpow_two] at h1
    exact hb₁ (mul_left_cancel (a := b₁) (by rw [mul_one]; exact h1.symm))
  have hxmem : x₁ * x₂ ∈ Subgroup.closure ({x₁, x₂} : Set G) :=
    mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have hcentB : centralizer ((Subgroup.closure ({b₁, b₂} : Set G) : Subgroup G) : Set G) ⊓ ⊤ =
      Subgroup.closure ({b₁, b₂} : Set G) := by
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_top, and_true, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg
      exact hcent g (hg b₁ hb₁B).symm (hg b₂ hb₂B).symm
    · intro hg h hh
      obtain ⟨i, j, rfl⟩ := hrep hg
      obtain ⟨k, l, rfl⟩ := hrep hh
      have c1 : Commute (b₁ ^ k) (b₁ ^ i) := Commute.zpow_zpow_self b₁ k i
      have c2 : Commute (b₁ ^ k) (b₂ ^ j) := hbb.zpow_zpow k j
      have c3 : Commute (b₂ ^ l) (b₁ ^ i) := hbb.symm.zpow_zpow l i
      have c4 : Commute (b₂ ^ l) (b₂ ^ j) := Commute.zpow_zpow_self b₂ l j
      exact ((c1.mul_right c2).mul_left (c3.mul_right c4)).eq
  exact ⟨hcard, b₁, b₂, x₁, x₂, x₁ * x₂, hb₁B, hb₂B, rfl, hord₁, hord₂, mem_top _, mem_top _,
    hn₁, hn₂, hox₁, hox₂, hxx.eq, hz₂, hz₁, hxmem, hxne, ⟨2, by norm_num, hact⟩, hcentB⟩

end Abstract

abbrev Idx (κ : Type) : Type := Fin 3 ⊕ (Fin 3 ⊕ κ)

abbrev compMat : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

abbrev frobMat : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 1]

section Blocks

variable {κ : Type} [Fintype κ] [DecidableEq κ]

def embFst (U : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Idx κ) (Idx κ) (ZMod 2) :=
  fromBlocks U 0 0 1

def embSnd (U : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Idx κ) (Idx κ) (ZMod 2) :=
  fromBlocks 1 0 0 (fromBlocks U 0 0 1)

theorem embFst_mul (U V : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (embFst (U * V) : Matrix (Idx κ) (Idx κ) (ZMod 2)) = embFst U * embFst V := by
  simp [embFst, fromBlocks_multiply]

theorem embSnd_mul (U V : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (embSnd (U * V) : Matrix (Idx κ) (Idx κ) (ZMod 2)) = embSnd U * embSnd V := by
  simp [embSnd, fromBlocks_multiply]

omit [Fintype κ] in
theorem embFst_one : (embFst 1 : Matrix (Idx κ) (Idx κ) (ZMod 2)) = 1 := by
  simp [embFst, fromBlocks_one]

omit [Fintype κ] in
theorem embSnd_one : (embSnd 1 : Matrix (Idx κ) (Idx κ) (ZMod 2)) = 1 := by
  simp [embSnd, fromBlocks_one]

theorem embFst_det (U : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (embFst U : Matrix (Idx κ) (Idx κ) (ZMod 2)).det = U.det := by
  rw [embFst, det_fromBlocks_zero₂₁]
  simp only [det_one, mul_one]

theorem embSnd_det (U : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (embSnd U : Matrix (Idx κ) (Idx κ) (ZMod 2)).det = U.det := by
  rw [embSnd, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁]
  simp only [det_one, one_mul, mul_one]

theorem embFst_embSnd (U V : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (embFst U : Matrix (Idx κ) (Idx κ) (ZMod 2)) * embSnd V = embSnd V * embFst U := by
  simp [embFst, embSnd, fromBlocks_multiply]

omit [Fintype κ] in
theorem embFst_inj {U V : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : (embFst U : Matrix (Idx κ) (Idx κ) (ZMod 2)) = embFst V) : U = V := by
  simpa [embFst, fromBlocks_inj] using h

theorem eq_zero_of_compMat_mul {m : Type} [Fintype m] (Q : Matrix (Fin 3) m (ZMod 2))
    (h : compMat * Q = Q) : Q = 0 := by
  obtain ⟨M, hM, -⟩ : ∃ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
      M * (compMat - 1) = 1 ∧ (compMat - 1) * M = 1 := by decide +kernel
  have h1 : (compMat - 1) * Q = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h, sub_self]
  calc Q = (M * (compMat - 1)) * Q := by rw [hM, Matrix.one_mul]
    _ = M * ((compMat - 1) * Q) := Matrix.mul_assoc _ _ _
    _ = 0 := by rw [h1, Matrix.mul_zero]

theorem eq_zero_of_mul_compMat {m : Type} [Fintype m] (R : Matrix m (Fin 3) (ZMod 2))
    (h : R * compMat = R) : R = 0 := by
  obtain ⟨M, -, hM⟩ : ∃ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
      M * (compMat - 1) = 1 ∧ (compMat - 1) * M = 1 := by decide +kernel
  have h1 : R * (compMat - 1) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]
  calc R = R * ((compMat - 1) * M) := by rw [hM, Matrix.mul_one]
    _ = (R * (compMat - 1)) * M := (Matrix.mul_assoc _ _ _).symm
    _ = 0 := by rw [h1, Matrix.zero_mul]

theorem eq_zero_or_pow_of_commute_compMat (P : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (h : P * compMat = compMat * P) : P = 0 ∨ ∃ i : ℕ, P = compMat ^ i := by
  have key : ∀ P : Matrix (Fin 3) (Fin 3) (ZMod 2), P * compMat = compMat * P →
      P = 0 ∨ ∃ i : Fin 7, P = compMat ^ (i : ℕ) := by decide +kernel
  rcases key P h with h0 | ⟨i, hi⟩
  · exact Or.inl h0
  · exact Or.inr ⟨i, hi⟩

theorem blocks_commute_fst {m : Type} [Fintype m] [DecidableEq m]
    (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) (Q : Matrix (Fin 3) m (ZMod 2))
    (R : Matrix m (Fin 3) (ZMod 2)) (S : Matrix m m (ZMod 2))
    (h : fromBlocks P Q R S * fromBlocks compMat 0 0 1 =
      fromBlocks compMat 0 0 1 * fromBlocks P Q R S) :
    P * compMat = compMat * P ∧ Q = 0 ∧ R = 0 := by
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.one_mul, fromBlocks_inj] at h
  obtain ⟨hP, hQ, hR, -⟩ := h
  exact ⟨hP, eq_zero_of_compMat_mul Q hQ.symm, eq_zero_of_mul_compMat R hR⟩

theorem centralizer_matrix (A : Matrix (Idx κ) (Idx κ) (ZMod 2))
    (h1 : A * embFst compMat = embFst compMat * A)
    (h2 : A * embSnd compMat = embSnd compMat * A)
    (hdet : A.det = 1) (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1) :
    ∃ i j : ℕ, A = embFst (compMat ^ i) * embSnd (compMat ^ j) := by
  obtain ⟨P, Q, R, S, rfl⟩ : ∃ (P : Matrix (Fin 3) (Fin 3) (ZMod 2))
      (Q : Matrix (Fin 3) (Fin 3 ⊕ κ) (ZMod 2)) (R : Matrix (Fin 3 ⊕ κ) (Fin 3) (ZMod 2))
      (S : Matrix (Fin 3 ⊕ κ) (Fin 3 ⊕ κ) (ZMod 2)), A = fromBlocks P Q R S :=
    ⟨_, _, _, _, (fromBlocks_toBlocks A).symm⟩
  obtain ⟨hP, hQ, hR⟩ := blocks_commute_fst P Q R S h1
  subst hQ hR
  have h2' : S * fromBlocks compMat 0 0 1 = fromBlocks compMat 0 0 1 * S := by
    simp only [embSnd, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, Matrix.mul_one, Matrix.one_mul, fromBlocks_inj] at h2
    exact h2.2.2.2
  obtain ⟨S₁, S₂, S₃, T, rfl⟩ : ∃ (S₁ : Matrix (Fin 3) (Fin 3) (ZMod 2))
      (S₂ : Matrix (Fin 3) κ (ZMod 2)) (S₃ : Matrix κ (Fin 3) (ZMod 2))
      (T : Matrix κ κ (ZMod 2)), S = fromBlocks S₁ S₂ S₃ T :=
    ⟨_, _, _, _, (fromBlocks_toBlocks S).symm⟩
  obtain ⟨hS₁, hS₂, hS₃⟩ := blocks_commute_fst S₁ S₂ S₃ T h2'
  subst hS₂ hS₃
  rw [det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁] at hdet
  have key : ∀ a b c : ZMod 2, a * (b * c) = 1 → a = 1 ∧ b = 1 ∧ c = 1 := by decide
  obtain ⟨hdP, hdS, hdT⟩ := key _ _ _ hdet
  have hTone := hκ T hdT
  have hne : ∀ U : Matrix (Fin 3) (Fin 3) (ZMod 2), U.det = 1 → U ≠ 0 := by
    rintro U hU rfl
    rw [Matrix.det_zero] at hU
    exact zero_ne_one hU
  rcases eq_zero_or_pow_of_commute_compMat P hP with h0 | ⟨i, hi⟩
  · exact absurd h0 (hne P hdP)
  rcases eq_zero_or_pow_of_commute_compMat S₁ hS₁ with h0 | ⟨j, hj⟩
  · exact absurd h0 (hne S₁ hdS)
  refine ⟨i, j, ?_⟩
  subst hi hj hTone
  simp [embFst, embSnd, fromBlocks_multiply]

end Blocks

section ModelSL

variable {κ : Type} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
theorem embSnd_inj {U V : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : (embSnd U : Matrix (Idx κ) (Idx κ) (ZMod 2)) = embSnd V) : U = V := by
  simpa [embSnd, fromBlocks_inj] using h

def slEmbFst : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →*
    Matrix.SpecialLinearGroup (Idx κ) (ZMod 2) where
  toFun g := ⟨embFst (g : Matrix (Fin 3) (Fin 3) (ZMod 2)), by rw [embFst_det]; exact g.2⟩
  map_one' := Subtype.ext (by simpa using embFst_one)
  map_mul' g h := by
    refine Subtype.ext ?_
    show embFst (↑(g * h) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = embFst ↑g * embFst ↑h
    rw [Matrix.SpecialLinearGroup.coe_mul, embFst_mul]

def slEmbSnd : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →*
    Matrix.SpecialLinearGroup (Idx κ) (ZMod 2) where
  toFun g := ⟨embSnd (g : Matrix (Fin 3) (Fin 3) (ZMod 2)), by rw [embSnd_det]; exact g.2⟩
  map_one' := Subtype.ext (by simpa using embSnd_one)
  map_mul' g h := by
    refine Subtype.ext ?_
    show embSnd (↑(g * h) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = embSnd ↑g * embSnd ↑h
    rw [Matrix.SpecialLinearGroup.coe_mul, embSnd_mul]

theorem slEmbFst_injective : Function.Injective (slEmbFst (κ := κ)) := fun _ _ hgh =>
  Subtype.ext (embFst_inj (congrArg Subtype.val hgh))

theorem slEmbSnd_injective : Function.Injective (slEmbSnd (κ := κ)) := fun _ _ hgh =>
  Subtype.ext (embSnd_inj (congrArg Subtype.val hgh))

theorem slEmbFst_comm (g h : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    Commute (slEmbFst (κ := κ) g) (slEmbSnd h) :=
  Subtype.ext (embFst_embSnd _ _)

def cSL : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨compMat, by decide⟩

def fSL : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨frobMat, by decide⟩

theorem cSL_pow_seven : cSL ^ 7 = 1 := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_pow]
  exact (by decide : compMat ^ 7 = 1)

theorem cSL_ne_one : cSL ≠ 1 := by
  intro h
  have h' : compMat = 1 := congrArg Subtype.val h
  exact absurd h' (by decide)

theorem fSL_pow_three : fSL ^ 3 = 1 := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_pow]
  exact (by decide : frobMat ^ 3 = 1)

theorem fSL_ne_one : fSL ≠ 1 := by
  intro h
  have h' : frobMat = 1 := congrArg Subtype.val h
  exact absurd h' (by decide)

theorem fSL_mul_cSL : fSL * cSL = cSL ^ 2 * fSL := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_pow]
  exact (by decide : frobMat * compMat = compMat ^ 2 * frobMat)

theorem model_idx (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1) :
    ∃ B₀ : Subgroup (Matrix.SpecialLinearGroup (Idx κ) (ZMod 2)),
      Nat.card B₀ = 49 ∧ StructureB (⊤ : Subgroup (Matrix.SpecialLinearGroup (Idx κ) (ZMod 2)))
        B₀ := by
  refine ⟨Subgroup.closure {slEmbFst cSL, slEmbSnd cSL}, ?_⟩
  refine structureB_closure_pair (b₁ := slEmbFst cSL) (b₂ := slEmbSnd cSL)
    (x₁ := slEmbFst fSL) (x₂ := slEmbSnd fSL) (slEmbFst_comm _ _) (slEmbFst_comm _ _)
    (slEmbFst_comm _ _) (slEmbFst_comm _ _).symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_pow, ← map_mul, fSL_mul_cSL]
  · rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_pow, ← map_mul, fSL_mul_cSL]
  · rw [← map_pow, cSL_pow_seven, map_one]
  · rw [← map_pow, cSL_pow_seven, map_one]
  · exact fun h => cSL_ne_one (slEmbFst_injective (h.trans (map_one _).symm))
  · exact fun h => cSL_ne_one (slEmbSnd_injective (h.trans (map_one _).symm))
  · rw [← map_pow, fSL_pow_three, map_one]
  · rw [← map_pow, fSL_pow_three, map_one]
  · exact fun h => fSL_ne_one (slEmbFst_injective (h.trans (map_one _).symm))
  · exact fun h => fSL_ne_one (slEmbSnd_injective (h.trans (map_one _).symm))
  · intro i j h
    rw [← map_zpow, ← map_zpow] at h
    have h' : embFst (↑(cSL ^ i) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        (embSnd (↑(cSL ^ j) : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Idx κ) (Idx κ) (ZMod 2)) :=
      congrArg Subtype.val h
    simp only [embFst, embSnd, fromBlocks_inj] at h'
    rw [← map_zpow, show cSL ^ i = 1 from Subtype.ext h'.1, map_one]
  · intro g h1 h2
    obtain ⟨i, j, hij⟩ := centralizer_matrix (g : Matrix (Idx κ) (Idx κ) (ZMod 2))
      (congrArg Subtype.val h1) (congrArg Subtype.val h2) g.2 hκ
    have hg : g = slEmbFst (cSL ^ i) * slEmbSnd (cSL ^ j) := by
      refine Subtype.ext ?_
      rw [hij, Matrix.SpecialLinearGroup.coe_mul]
      show _ = embFst (↑(cSL ^ i) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        embSnd (↑(cSL ^ j) : Matrix (Fin 3) (Fin 3) (ZMod 2))
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow]
      rfl
    rw [hg, map_pow, map_pow]
    exact mul_mem (pow_mem (subset_closure (by simp)) i) (pow_mem (subset_closure (by simp)) j)

end ModelSL

def slReindex {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) :
    Matrix.SpecialLinearGroup ι (ZMod 2) →* Matrix.SpecialLinearGroup κ (ZMod 2) where
  toFun g := ⟨Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e (g : Matrix ι ι (ZMod 2)), by
    rw [Matrix.det_reindexAlgEquiv]; exact g.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := by
    refine Subtype.ext ?_
    show Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e (↑(g * h) : Matrix ι ι (ZMod 2)) =
      Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e ↑g * Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e ↑h
    rw [Matrix.SpecialLinearGroup.coe_mul, map_mul]

theorem slReindex_injective {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) : Function.Injective (slReindex e) := fun _ _ hgh =>
  Subtype.ext ((Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e).injective (congrArg Subtype.val hgh))

theorem slReindex_surjective {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) : Function.Surjective (slReindex e) := fun h =>
  ⟨⟨(Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e).symm (h : Matrix κ κ (ZMod 2)), by
    rw [Matrix.symm_reindexAlgEquiv, Matrix.det_reindexAlgEquiv]; exact h.2⟩,
    Subtype.ext (AlgEquiv.apply_symm_apply _ _)⟩

theorem model_of_equiv {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ)
    (h : ∃ B₀ : Subgroup (Matrix.SpecialLinearGroup ι (ZMod 2)),
      Nat.card B₀ = 49 ∧ StructureB (⊤ : Subgroup (Matrix.SpecialLinearGroup ι (ZMod 2))) B₀) :
    ∃ B₀ : Subgroup (Matrix.SpecialLinearGroup κ (ZMod 2)),
      Nat.card B₀ = 49 ∧ StructureB (⊤ : Subgroup (Matrix.SpecialLinearGroup κ (ZMod 2))) B₀ := by
  obtain ⟨B₀, hc, hS⟩ := h
  refine ⟨B₀.map (slReindex e), ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (slReindex_injective e), hc]
  · have h1 := StructureB.map (slReindex e) (slReindex_injective e) hS
    rwa [map_top_of_surjective' _ (slReindex_surjective e)] at h1

theorem rigid_det_fin_zero (T : Matrix (Fin 0) (Fin 0) (ZMod 2)) (_ : T.det = 1) : T = 1 :=
  Subsingleton.elim T 1

theorem rigid_det_fin_one (T : Matrix (Fin 1) (Fin 1) (ZMod 2)) (hT : T.det = 1) : T = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simpa [Matrix.det_unique] using hT

end SylowModel

theorem lnTwoSylowSevenModel : LnTwoSylowSevenModel := by
  intro n hn
  rcases hn with rfl | rfl
  · exact SylowModel.model_of_equiv (Fintype.equivOfCardEq (by simp))
      (SylowModel.model_idx (κ := Fin 0) SylowModel.rigid_det_fin_zero)
  · exact SylowModel.model_of_equiv (Fintype.equivOfCardEq (by simp))
      (SylowModel.model_idx (κ := Fin 1) SylowModel.rigid_det_fin_one)

end Sec109

end CFSG.RankThree.PartOne
