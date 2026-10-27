module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B4
public import CFSG.RankThree.PartOne.K159.AutTits
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Plane

variable {X : Type*} [Group X] {a b : X}

theorem plane_mul_uc6 (hab : a * b = b * a) (i j k l : ℕ) :
    (a ^ i * b ^ j) * (a ^ k * b ^ l) = a ^ (i + k) * b ^ (j + l) := by
  have h : b ^ j * a ^ k = a ^ k * b ^ j := ((Commute.pow_pow (show Commute a b from hab).symm j k)).eq
  calc (a ^ i * b ^ j) * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by
        simp only [mul_assoc]
    _ = a ^ (i + k) * b ^ (j + l) := by
        rw [h]; simp only [pow_add, mul_assoc]

theorem plane_pow_uc6 (hab : a * b = b * a) (i j k : ℕ) :
    (a ^ i * b ^ j) ^ k = a ^ (i * k) * b ^ (j * k) := by
  rw [(Commute.pow_pow (show Commute a b from hab) i j).mul_pow, pow_mul, pow_mul]

@[expose] def planeSub_uc6 (hab : a * b = b * a) (ha : a ^ 5 = 1) (hb : b ^ 5 = 1) : Subgroup X where
  carrier := {x | ∃ i j : ℕ, x = a ^ i * b ^ j}
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    exact ⟨i + k, j + l, plane_mul_uc6 hab i j k l⟩
  one_mem' := ⟨0, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    refine ⟨4 * i, 4 * j, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [plane_mul_uc6 hab, show i + 4 * i = 5 * i by ring, show j + 4 * j = 5 * j by ring,
      pow_mul, pow_mul, ha, hb, one_pow, one_pow, one_mul]

theorem plane_exp_inj_uc6 (ha : a ^ 5 = 1) (hb : b ^ 5 = 1)
    (hinj : ∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
      a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j') {i j k l : ℕ}
    (h : a ^ i * b ^ j = a ^ k * b ^ l) : i % 5 = k % 5 ∧ j % 5 = l % 5 := by
  rw [pow_eq_pow_mod i ha, pow_eq_pow_mod j hb, pow_eq_pow_mod k ha, pow_eq_pow_mod l hb] at h
  exact hinj _ _ _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h

theorem card_planeSub_uc6 (hab : a * b = b * a) (ha : a ^ 5 = 1) (hb : b ^ 5 = 1)
    (hinj : ∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
      a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j') :
    Nat.card (planeSub_uc6 hab ha hb) = 25 := by
  let φ : Fin 5 × Fin 5 → planeSub_uc6 hab ha hb := fun p =>
    ⟨a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ), p.1, p.2, rfl⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro p q h
      have := plane_exp_inj_uc6 ha hb hinj (congrArg Subtype.val h)
      rw [Nat.mod_eq_of_lt p.1.2, Nat.mod_eq_of_lt q.1.2, Nat.mod_eq_of_lt p.2.2,
        Nat.mod_eq_of_lt q.2.2] at this
      exact Prod.ext (Fin.ext this.1) (Fin.ext this.2)
    · rintro ⟨x, i, j, rfl⟩
      refine ⟨(⟨i % 5, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩),
        Subtype.ext ?_⟩
      show a ^ (i % 5) * b ^ (j % 5) = a ^ i * b ^ j
      rw [← pow_eq_pow_mod i ha, ← pow_eq_pow_mod j hb]
  rw [← Nat.card_eq_of_bijective φ hφ]
  simp

variable {g : X}

theorem conj_plane_uc6 (i j : ℕ) :
    g * (a ^ i * b ^ j) * g⁻¹ = (g * a * g⁻¹) ^ i * (g * b * g⁻¹) ^ j := by
  rw [conj_pow, conj_pow]
  group

theorem conj_plane_tits_uc6 (hab : a * b = b * a) (ha : a ^ 5 = 1) (hb : b ^ 5 = 1)
    (hga : g * a * g⁻¹ = a ^ 3 * b ^ 4) (hgb : g * b * g⁻¹ = a ^ 2 * b ^ 4) (i j : ℕ) :
    g * (a ^ i * b ^ j) * g⁻¹ = a ^ ((3 * i + 2 * j) % 5) * b ^ ((4 * i + 4 * j) % 5) := by
  rw [conj_plane_uc6, hga, hgb, plane_pow_uc6 hab, plane_pow_uc6 hab, plane_mul_uc6 hab,
    ← pow_eq_pow_mod _ ha, ← pow_eq_pow_mod _ hb]

theorem conj_cube_tits_uc6 (hab : a * b = b * a) (ha : a ^ 5 = 1) (hb : b ^ 5 = 1)
    (hga : g * a * g⁻¹ = a ^ 3 * b ^ 4) (hgb : g * b * g⁻¹ = a ^ 2 * b ^ 4) (i j : ℕ) :
    g ^ 3 * (a ^ i * b ^ j) * (g ^ 3)⁻¹ = (a ^ i * b ^ j) ^ 2 := by
  have h3 : ∀ x : X, g ^ 3 * x * (g ^ 3)⁻¹ = g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ := by
    intro x
    simp only [pow_three, mul_inv_rev, mul_assoc]
  have ha3 : g ^ 3 * a * (g ^ 3)⁻¹ = a ^ 2 := by
    have h := h3 (a ^ 1 * b ^ 0)
    rw [conj_plane_tits_uc6 hab ha hb hga hgb, conj_plane_tits_uc6 hab ha hb hga hgb,
      conj_plane_tits_uc6 hab ha hb hga hgb] at h
    norm_num at h
    exact h
  have hb3 : g ^ 3 * b * (g ^ 3)⁻¹ = b ^ 2 := by
    have h := h3 (a ^ 0 * b ^ 1)
    rw [conj_plane_tits_uc6 hab ha hb hga hgb, conj_plane_tits_uc6 hab ha hb hga hgb,
      conj_plane_tits_uc6 hab ha hb hga hgb] at h
    norm_num at h
    exact h
  rw [conj_plane_uc6, ha3, hb3, plane_pow_uc6 hab, ← pow_mul, ← pow_mul, mul_comm i 2,
    mul_comm j 2]

theorem tits_sq_noEigen_check : ∀ i j k : Fin 5, (i ≠ 0 ∨ j ≠ 0) →
    ¬ ((i : ℕ) * k % 5 = (2 * (i : ℕ) + 4 * j) % 5 % 5 ∧
      (j : ℕ) * k % 5 = (3 * (i : ℕ) + 4 * j) % 5 % 5) := by
  decide

theorem tits_sq_not_normalizes_uc6 (hab : a * b = b * a) (ha : a ^ 5 = 1) (hb : b ^ 5 = 1)
    (hinj : ∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
      a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j')
    (hga : g * a * g⁻¹ = a ^ 3 * b ^ 4) (hgb : g * b * g⁻¹ = a ^ 2 * b ^ 4)
    {Y : Subgroup X} (hY : Y ≤ planeSub_uc6 hab ha hb) (hY5 : Nat.card Y = 5)
    (hgY : ∀ y ∈ Y, g ^ 2 * y * (g ^ 2)⁻¹ ∈ Y) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by rw [hY5]; norm_num)
  haveI : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.1 (by rw [hY5]; norm_num)
  obtain ⟨⟨x, hxY⟩, hx1⟩ := exists_ne (1 : Y)
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨i, j, rfl⟩ := hY hxY
  have hord : orderOf (a ^ i * b ^ j) = 5 := by
    have h5 : (a ^ i * b ^ j) ^ 5 = 1 := by
      rw [plane_pow_uc6 hab, pow_mul', pow_mul', ha, hb, one_pow, one_pow, one_mul]
    rcases (Nat.dvd_prime Nat.prime_five).1 (orderOf_dvd_of_pow_eq_one h5) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1'
    · exact h
  have hYeq : Y = zpowers (a ^ i * b ^ j) :=
    (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hxY)
      (by rw [hY5, Nat.card_zpowers, hord])).symm
  have hmem := hgY _ hxY
  rw [hYeq] at hmem
  have hfin : IsOfFinOrder (a ^ i * b ^ j) := orderOf_pos_iff.1 (by rw [hord]; norm_num)
  obtain ⟨k, hk⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hfin.mem_powers_iff_mem_zpowers.2 hmem)
  have hg2 : g ^ 2 * (a ^ i * b ^ j) * (g ^ 2)⁻¹ =
      a ^ ((2 * i + 4 * j) % 5) * b ^ ((3 * i + 4 * j) % 5) := by
    have h2 : g ^ 2 * (a ^ i * b ^ j) * (g ^ 2)⁻¹ = g * (g * (a ^ i * b ^ j) * g⁻¹) * g⁻¹ := by
      simp only [sq, mul_inv_rev, mul_assoc]
    rw [h2, conj_plane_tits_uc6 hab ha hb hga hgb, conj_plane_tits_uc6 hab ha hb hga hgb,
      ← pow_eq_pow_mod _ ha, ← pow_eq_pow_mod _ hb, pow_eq_pow_mod _ ha, pow_eq_pow_mod _ hb]
    congr 2 <;> omega
  rw [plane_pow_uc6 hab, hg2] at hk
  have h := plane_exp_inj_uc6 ha hb hinj hk
  have hij : i % 5 ≠ 0 ∨ j % 5 ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hx1'
    rw [pow_eq_pow_mod i ha, pow_eq_pow_mod j hb, hc.1, hc.2, pow_zero, pow_zero, one_mul]
  apply tits_sq_noEigen_check ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩ ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩
    ⟨k % 5, Nat.mod_lt _ (by norm_num)⟩
    (by simpa [Fin.ext_iff] using hij)
  refine ⟨?_, ?_⟩
  · show i % 5 * (k % 5) % 5 = (2 * (i % 5) + 4 * (j % 5)) % 5 % 5
    rw [← Nat.mul_mod, h.1]
    omega
  · show j % 5 * (k % 5) % 5 = (3 * (i % 5) + 4 * (j % 5)) % 5 % 5
    rw [← Nat.mul_mod, h.2]
    omega

end Plane

open scoped Pointwise in
theorem exists_mulEquiv_sylow_eq_uc6 {K Y : Type} [Group K] [Group Y] [Finite K] [Finite Y]
    (e : K ≃* Y) {p : ℕ} [Fact p.Prime] (S₀ : Subgroup Y)
    (hS₀ : Nat.card S₀ = p ^ (Nat.card Y).factorization p) (S : Sylow p K) :
    ∃ ψ : K ≃* Y, ∀ x : K, x ∈ (S : Subgroup K) ↔ ψ x ∈ S₀ := by
  let S' : Sylow p Y := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let Q : Sylow p Y := Sylow.ofCard S₀ hS₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q S'
  refine ⟨e.trans (MulAut.conj g⁻¹), fun x => ?_⟩
  have h1 : x ∈ (S : Subgroup K) ↔ e x ∈ (S' : Subgroup Y) := by
    show x ∈ (S : Subgroup K) ↔ e x ∈ (S : Subgroup K).map e.toMonoidHom
    rw [Subgroup.mem_map_equiv]
    simp
  have h2 : (S' : Subgroup Y) = MulAut.conj g • (Q : Subgroup Y) := by
    rw [← hg]
    rfl
  rw [h1, h2, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [Q]

section TitsModel

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CFSG.RankThree.PartOne.K159

theorem tits_plane_uc6 :
    ∃ a b g : ↥titsD, a ^ 5 = 1 ∧ b ^ 5 = 1 ∧ a * b = b * a ∧
      (∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
        a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j') ∧
      g * a * g⁻¹ = a ^ 3 * b ^ 4 ∧ g * b * g⁻¹ = a ^ 2 * b ^ 4 := by
  obtain ⟨hlA, hlB, hlG, hA5, hB5, hAB, hdist, hga, hgb, -⟩ :=
    Certificates.certificate14973
  have rA := rep_wordArr_titsT hlA
  have rB := rep_wordArr_titsT hlB
  have rG := rep_wordArr_titsT hlG
  set a := wordIn 13 titsT titsAWord with ha_def
  set b := wordIn 13 titsT titsBWord with hb_def
  set g := wordIn 13 titsT titsGWord with hg_def
  have hpa : ∀ k, Rep 1755 (powArr titsAArr k) (a ^ k) := rep_powArr rA
  have hpb : ∀ k, Rep 1755 (powArr titsBArr k) (b ^ k) := rep_powArr rB
  have ha5 : a ^ 5 = 1 := eq_of_eqA (hpa 5) rep_idA hA5
  have hb5 : b ^ 5 = 1 := eq_of_eqA (hpb 5) rep_idA hB5
  have hab : a * b = b * a := eq_of_eqA (rep_compA rA rB) (rep_compA rB rA) hAB
  have hinj : ∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
      a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j' := by
    intro i j i' j' hi hj hi' hj' h
    have h1 := allLt_spec (allLt_spec (allLt_spec (allLt_spec hdist hi) hj) hi') hj'
    have heq : eqA 1755 (pairArr i j) (pairArr i' j') = true :=
      (eqA_iff (rep_compA (hpa i) (hpb j)) (rep_compA (hpa i') (hpb j'))).2 h
    simp only [heq, Bool.not_true, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at h1
    exact h1
  have hga3 : g * a * g⁻¹ = a ^ 3 * b ^ 4 :=
    mul_inv_eq_iff_eq_mul.2
      (eq_of_eqA (rep_compA rG rA) (rep_compA (rep_compA (hpa 3) (hpb 4)) rG) hga)
  have hgb2 : g * b * g⁻¹ = a ^ 2 * b ^ 4 :=
    mul_inv_eq_iff_eq_mul.2
      (eq_of_eqA (rep_compA rG rB) (rep_compA (rep_compA (hpa 2) (hpb 4)) rG) hgb)
  refine ⟨⟨a, wordIn_titsT_mem_titsD titsAWord⟩, ⟨b, wordIn_titsT_mem_titsD titsBWord⟩,
    ⟨g, wordIn_titsT_mem_titsD titsGWord⟩, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, ?_,
    Subtype.ext ?_, Subtype.ext ?_⟩
  · simpa using ha5
  · simpa using hb5
  · simpa using hab
  · intro i j i' j' hi hj hi' hj' h
    exact hinj i j i' j' hi hj hi' hj' (by simpa using congrArg Subtype.val h)
  · simpa using hga3
  · simpa using hgb2

theorem factorization_card_titsD_uc6 :
    (Nat.card titsD).factorization 5 = 2 := by
  rw [card_titsD, show (17971200 : ℕ) = 5 ^ 2 * 718848 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

end TitsModel

namespace Mz614

open CFSG.Sporadic.Schreier.Tits

variable {G : Type} [Group G] [Finite G]

structure TitsSetup (m : Mz614 G) where
  a : ↥titsD
  b : ↥titsD
  g : ↥titsD
  ha : a ^ 5 = 1
  hb : b ^ 5 = 1
  hab : a * b = b * a
  hinj : ∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
    a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j'
  hga : g * a * g⁻¹ = a ^ 3 * b ^ 4
  hgb : g * b * g⁻¹ = a ^ 2 * b ^ 4
  ψ : ↥m.L ≃* ↥titsD
  mem_iff : ∀ x : ↥m.L, x ∈ (m.A ⊓ m.L).subgroupOf m.L ↔ ψ x ∈ planeSub_uc6 hab ha hb

namespace TitsSetup

variable {m : Mz614 G} (T : TitsSetup m)

@[expose] def plane : Subgroup ↥titsD := planeSub_uc6 T.hab T.ha T.hb

@[expose] noncomputable def n : G := ((T.ψ.symm T.g : ↥m.L) : G)

@[expose] noncomputable def y : G := ((T.ψ.symm (T.g ^ 3) : ↥m.L) : G)

theorem exists_exp {x : G} (hx : x ∈ m.A ⊓ m.L) :
    ∃ i j : ℕ, T.ψ ⟨x, hx.2⟩ = T.a ^ i * T.b ^ j := by
  obtain ⟨i, j, hij⟩ := (T.mem_iff ⟨x, hx.2⟩).1 hx
  exact ⟨i, j, hij⟩

theorem psi_conj (h : ↥titsD) {x : G} (hx : x ∈ m.L) :
    T.ψ ⟨((T.ψ.symm h : ↥m.L) : G) * x * ((T.ψ.symm h : ↥m.L) : G)⁻¹,
      m.L.mul_mem (m.L.mul_mem (T.ψ.symm h).2 hx) (m.L.inv_mem (T.ψ.symm h).2)⟩ =
      h * T.ψ ⟨x, hx⟩ * h⁻¹ := by
  have e1 : (⟨((T.ψ.symm h : ↥m.L) : G) * x * ((T.ψ.symm h : ↥m.L) : G)⁻¹,
      m.L.mul_mem (m.L.mul_mem (T.ψ.symm h).2 hx) (m.L.inv_mem (T.ψ.symm h).2)⟩ : ↥m.L) =
      T.ψ.symm h * ⟨x, hx⟩ * (T.ψ.symm h)⁻¹ := Subtype.ext (by simp)
  rw [e1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem conj_mem_of_normalizes (h : ↥titsD)
    (hh : ∀ i j : ℕ, h * (T.a ^ i * T.b ^ j) * h⁻¹ ∈ T.plane) :
    ∀ x ∈ m.A ⊓ m.L,
      ((T.ψ.symm h : ↥m.L) : G) * x * ((T.ψ.symm h : ↥m.L) : G)⁻¹ ∈ m.A ⊓ m.L := by
  intro x hx
  obtain ⟨i, j, hij⟩ := T.exists_exp hx
  have h1 := T.psi_conj h hx.2
  rw [hij] at h1
  have h2 : T.ψ ⟨_, m.L.mul_mem (m.L.mul_mem (T.ψ.symm h).2 hx.2)
      (m.L.inv_mem (T.ψ.symm h).2)⟩ ∈ T.plane := h1 ▸ hh i j
  exact (T.mem_iff _).2 h2

theorem g_mem (i j : ℕ) : T.g * (T.a ^ i * T.b ^ j) * T.g⁻¹ ∈ T.plane :=
  ⟨_, _, conj_plane_tits_uc6 T.hab T.ha T.hb T.hga T.hgb i j⟩

theorem g_cube_mem (i j : ℕ) : T.g ^ 3 * (T.a ^ i * T.b ^ j) * (T.g ^ 3)⁻¹ ∈ T.plane := by
  rw [conj_cube_tits_uc6 T.hab T.ha T.hb T.hga T.hgb, plane_pow_uc6 T.hab]
  exact ⟨_, _, rfl⟩

theorem n_mem (h620 : m.C620) : T.n ∈ m.L ⊓ m.W :=
  ⟨(T.ψ.symm T.g).2, mem_W_of_mem_L h620 (T.ψ.symm T.g).2 (T.conj_mem_of_normalizes T.g T.g_mem)⟩

theorem y_mem (h620 : m.C620) : T.y ∈ m.L ⊓ m.W :=
  ⟨(T.ψ.symm (T.g ^ 3)).2, mem_W_of_mem_L h620 (T.ψ.symm (T.g ^ 3)).2
    (T.conj_mem_of_normalizes (T.g ^ 3) T.g_cube_mem)⟩

theorem y_conj : ∀ x ∈ m.A ⊓ m.L, T.y * x * T.y⁻¹ = x ^ 2 := by
  intro x hx
  obtain ⟨i, j, hij⟩ := T.exists_exp hx
  have h1 := T.psi_conj (T.g ^ 3) hx.2
  rw [hij, conj_cube_tits_uc6 T.hab T.ha T.hb T.hga T.hgb, ← hij, ← map_pow] at h1
  have h2 := congrArg Subtype.val (T.ψ.injective h1)
  simpa [y] using h2

theorem map_le_plane {X : Subgroup G} (hX : X ≤ m.A ⊓ m.L) :
    (X.subgroupOf m.L).map T.ψ.toMonoidHom ≤ T.plane ∧
      Nat.card ((X.subgroupOf m.L).map T.ψ.toMonoidHom) = Nat.card X := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (T.mem_iff x).1 (hX hx)
  · rw [Subgroup.card_map_of_injective T.ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hX.trans inf_le_right)).toEquiv]

theorem map_normalized {X : Subgroup G} (hX : X ≤ m.A ⊓ m.L)
    (hXn : X.map (MulAut.conj (T.n ^ 2)).toMonoidHom = X) :
    ∀ u ∈ (X.subgroupOf m.L).map T.ψ.toMonoidHom, T.g ^ 2 * u * (T.g ^ 2)⁻¹ ∈
      (X.subgroupOf m.L).map T.ψ.toMonoidHom := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (T.n ^ 2) * (x : G) * (T.n ^ 2)⁻¹ ∈ X := by
    rw [← hXn]
    exact ⟨x, hx, rfl⟩
  refine ⟨⟨(T.n ^ 2) * (x : G) * (T.n ^ 2)⁻¹, m.L.mul_mem (m.L.mul_mem
    (m.L.pow_mem (T.ψ.symm T.g).2 2) x.2) (m.L.inv_mem (m.L.pow_mem (T.ψ.symm T.g).2 2))⟩, hx',
    ?_⟩
  have h1 := T.psi_conj (T.g ^ 2) x.2
  simp only [map_pow, Subgroup.coe_pow] at h1
  simpa [n] using h1

theorem not_normalizes {Y : Subgroup ↥titsD} (hY : Y ≤ T.plane) (hY5 : Nat.card Y = 5)
    (hgY : ∀ y ∈ Y, T.g ^ 2 * y * (T.g ^ 2)⁻¹ ∈ Y) : False :=
  tits_sq_not_normalizes_uc6 T.hab T.ha T.hb T.hinj T.hga T.hgb hY hY5 hgY

end TitsSetup

theorem c621_of_titsSetup {m : Mz614 G} (T : TitsSetup m) (h620 : m.C620) (hr : m.r = 5) :
    m.C621 := by
  intro W' hW'B hW'N
  by_contra hcon
  push Not at hcon
  have hdvd : Nat.card W' ∣ 5 ^ 2 := by
    rw [← hr, ← m.card_A_inf_L h620]
    exact Subgroup.card_dvd_of_le hW'B
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hdvd
  interval_cases k
  · exact hcon.1 (Subgroup.eq_bot_of_card_eq W' (by simpa using hk'))
  · obtain ⟨hY1, hY2⟩ := T.map_le_plane hW'B
    have hn2 : W'.map (MulAut.conj (T.n ^ 2)).toMonoidHom = W' := by
      apply le_antisymm
      · rintro _ ⟨w, hw, rfl⟩
        exact (mem_normalizer_iff.1 (hW'N ((m.L ⊓ m.W).pow_mem (T.n_mem h620) 2)) w).1 hw
      · intro w hw
        refine ⟨(T.n ^ 2)⁻¹ * w * (T.n ^ 2), ?_, ?_⟩
        swap
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        have := (mem_normalizer_iff.1 (hW'N ((m.L ⊓ m.W).inv_mem
          ((m.L ⊓ m.W).pow_mem (T.n_mem h620) 2))) w).1 hw
        simpa using this
    exact T.not_normalizes hY1 (by rw [hY2, hk', pow_one]) (T.map_normalized hW'B hn2)
  · exact hcon.2 (Subgroup.eq_of_le_of_card_ge hW'B (by
      rw [hk', m.card_A_inf_L h620, hr]))


theorem exists_titsSetup (m : Mz614 G) (h620 : m.C620) (hr : m.r = 5)
    (hL : IsoLie ↥m.L .tits) : Nonempty (TitsSetup m) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := titsModelEquiv ↥m.L 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits hL)
  obtain ⟨a, b, g, ha, hb, hab, hinj, hga, hgb⟩ := tits_plane_uc6
  set S₀ := planeSub_uc6 hab ha hb with hS₀def
  have hS₀ : Nat.card S₀ = 5 ^ (Nat.card ↥titsD).factorization 5 := by
    rw [card_planeSub_uc6 hab ha hb hinj, factorization_card_titsD_uc6]
    norm_num
  set S0 : Subgroup ↥m.L := (m.A ⊓ m.L).subgroupOf m.L with hS0
  have hS0card : Nat.card S0 = 5 ^ (Nat.card ↥m.L).factorization 5 := by
    rw [hS0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
      m.card_A_inf_L h620, hr, Nat.card_congr e.toEquiv, factorization_card_titsD_uc6]
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_sylow_eq_uc6 e S₀ hS₀ (Sylow.ofCard S0 hS0card)
  exact ⟨⟨a, b, g, ha, hb, hab, hinj, hga, hgb, ψ, fun x => hψ x⟩⟩

theorem c621_of_tits (m : Mz614 G) (h620 : m.C620) (hr : m.r = 5) (hL : IsoLie ↥m.L .tits) :
    m.C621 := by
  obtain ⟨T⟩ := exists_titsSetup m h620 hr hL
  exact c621_of_titsSetup T h620 hr

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
