module

public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace HSRuLoc

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G]

theorem c134Ex_card_field {n : ℕ} {F : Type} [Field F] [Fintype F] (h : Fintype.card F = 2 ^ n) :
    1 ≤ n ∧ (2 : F) = 0 := by
  have hn : n ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := F)
    omega
  refine ⟨Nat.one_le_iff_ne_zero.2 hn, ?_⟩
  have h0 := FiniteField.cast_card_eq_zero F
  rw [h, Nat.cast_pow, Nat.cast_ofNat] at h0
  exact (pow_eq_zero_iff hn).1 h0

theorem c134Ex_two_nsmul {F M : Type*} [Field F] [AddCommGroup M] [Module F M] (h2 : (2 : F) = 0)
    (m : M) : (2 : ℕ) • m = 0 := by
  rw [← Nat.cast_smul_eq_nsmul F, Nat.cast_ofNat, h2, zero_smul]

theorem c134Ex_sq_eq_one {V : Subgroup G} {M : Type*} [AddCommGroup M]
    (hM : ∀ m : M, (2 : ℕ) • m = 0) (β : ↥V →* Multiplicative M)
    (hk : β.ker = (⊥ : Subgroup G).subgroupOf V) {x : G} (hx : x ∈ V) : x ^ 2 = 1 := by
  have h2 : ∀ y : Multiplicative M, y ^ 2 = 1 := fun y => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    exact hM _
  have h : (⟨x, hx⟩ : ↥V) ^ 2 ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact h2 _
  rw [hk, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at h
  simpa using h

theorem c134Ex_card_section {V Z : Subgroup G} (hZ : Z ≤ V) {M : Type*} [AddCommGroup M]
    (β : ↥V →* Multiplicative M) (hs : Function.Surjective β) (hk : β.ker = Z.subgroupOf V) :
    Nat.card ↥V = Nat.card ↥Z * Nat.card M := by
  rw [← Subgroup.card_ker_mul_card_of_surjective hs, hk,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ).toEquiv, Nat.card_congr Multiplicative.toAdd]

theorem c134Ex_card_of_sum {A V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] [Fintype F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥A →* ↥Γ} {dual : Bool}
    {k : ℕ} (h : IsSumOfNaturalModulesVia A V Z α dual k) :
    Nat.card ↥V = Nat.card ↥Z * Nat.card F ^ (Nat.card ι * k) := by
  obtain ⟨-, hZ, β, hs, hk, -⟩ := h
  rw [c134Ex_card_section hZ β hs hk, Nat.card_fun, Nat.card_fun, ← pow_mul]
  simp [Nat.card_eq_fintype_card]

theorem c134Ex_fixed_zero {F : Type} [Field F] (w : Fin 3 → F)
    (h : ∀ g : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F),
      ((g : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w = w) :
    w = 0 := by
  have key : ∀ A : Matrix (Fin 3) (Fin 3) F, A.det = 1 → A.mulVec w = w := by
    intro A hA
    have hg : Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hA]; exact one_ne_zero) ∈
        CFSG.Assembly.LowTwoRank.StatedSL 3 F :=
      Subgroup.subset_closure (by simpa using hA)
    exact h ⟨_, hg⟩
  have e1 := congrFun (key !![1, 1, 0; 0, 1, 0; 0, 0, 1] (by simp [Matrix.det_fin_three])) 0
  have e2 := congrFun (key !![1, 0, 0; 1, 1, 0; 0, 0, 1] (by simp [Matrix.det_fin_three])) 1
  have e3 := congrFun (key !![1, 0, 1; 0, 1, 0; 0, 0, 1] (by simp [Matrix.det_fin_three])) 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e1 e2 e3
  funext i
  fin_cases i <;> simp [*]

theorem c134Ex_case12 {Q : Subgroup G} {n : ℕ} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ n) {M : Type} [AddCommGroup M] [Module F M]
    (β : ↥Q →* Multiplicative M) (hk : β.ker = (⊥ : Subgroup G).subgroupOf Q) {x : G} (hx : x ∈ Q)
    (hx2 : x ^ 2 ≠ 1) : False :=
  hx2 (c134Ex_sq_eq_one (c134Ex_two_nsmul (c134Ex_card_field hF).2) β hk hx)

theorem c134Ex_case3 {K Q Z T : Subgroup G} {e n : ℕ} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ n)
    {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : Function.Surjective α)
    (hTK : ∀ t ∈ T, ∀ a ∈ K, a * t = t * a) (hTZ : T ≤ Z)
    (h1 : IsSumOfNaturalModulesVia K Z ⊥ α false 1) (h2 : IsSumOfNaturalModulesVia K Q Z α true 2)
    (hcard : Nat.card ↥Q = 2 ^ e * Nat.card ↥T) : 9 ∣ e := by
  have c1 := c134Ex_card_of_sum h1
  have c2 := c134Ex_card_of_sum h2
  obtain ⟨-, -, β, -, hβk, hβe⟩ := h1
  have hT1 : T = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    set u : ↥Z := ⟨t, hTZ ht⟩ with hu
    have hfix : ∀ g : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F),
        ((g : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (β u) 0) = Multiplicative.toAdd (β u) 0 := by
      intro g
      obtain ⟨a, rfl⟩ := hα g
      have hcomm : (u : G) = (a : G) * (u : G) * (a : G)⁻¹ := by
        show t = (a : G) * t * (a : G)⁻¹
        rw [hTK t ht a a.2]
        group
      have := hβe a u u hcomm 0
      simpa [moduleAct] using this.symm
    have hw := c134Ex_fixed_zero _ hfix
    have hu1 : β u = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simpa using hw
    have hmem : u ∈ β.ker := hu1
    rw [hβk, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hmem
    exact hmem
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  subst hT1
  rw [Subgroup.card_bot] at hcard c1
  have h3 : Nat.card (Fin 3) = 3 := by simp
  rw [h3, hq] at c1 c2
  rw [c2, c1] at hcard
  have hpow : 2 ^ e = 2 ^ (9 * n) :=
    calc 2 ^ e = 2 ^ e * 1 := (mul_one _).symm
      _ = 1 * (2 ^ n) ^ (3 * 1) * (2 ^ n) ^ (3 * 2) := hcard.symm
      _ = 2 ^ (9 * n) := by ring
  have := Nat.pow_right_injective (le_refl 2) hpow
  exact ⟨n, by omega⟩

theorem c134Ex_case5 [Finite G] {K Q CQ T : Subgroup G} {e : ℕ}
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))} {α : ↥K →* ↥Γ}
    (hCQ : Nat.card ↥CQ = 2) (h1 : IsSumOfNaturalModulesVia K Q CQ α false 1) (he : 5 ≤ e)
    (hcard : Nat.card ↥Q = 2 ^ e * Nat.card ↥T) : False := by
  have c1 := c134Ex_card_of_sum h1
  have h3 : Nat.card (Fin 3) = 3 := by simp
  rw [h3, hCQ, Nat.card_zmod] at c1
  have hT : 0 < Nat.card ↥T := Nat.card_pos
  have h5 : 2 ^ 5 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have : 2 ^ e ≤ Nat.card ↥Q := by
    rw [hcard]
    exact Nat.le_mul_of_pos_right _ hT
  norm_num at c1
  omega

end HSRuLoc

end CFSG.Quasithin
