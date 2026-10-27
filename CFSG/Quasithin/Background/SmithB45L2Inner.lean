module

public import CFSG.Quasithin.Background.SmithB45L2Field
public import CFSG.Quasithin.Background.SmithB45L2Pair
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInternal
public import Mathlib.Data.Int.Star

public section

namespace CFSG.Quasithin.B45L2

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups

section Helpers

theorem two_mul_lt_two_pow {r : ℕ} (hr : 5 ≤ r) : 2 * r < 2 ^ (r - 1) := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    have h1 : r + 1 - 1 = (r - 1) + 1 := by omega
    rw [h1, pow_succ]
    omega

theorem exp_le_of_pow_le {a b c : ℕ} (h : 2 ^ a ≤ 2 ^ b * 2 ^ c) : a ≤ b + c := by
  rw [← pow_add] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem frob_pow_injective {K : Type*} [Field K] [CharP K 2] (m : ℕ) {x y : K}
    (h : x ^ (2 ^ m) = y ^ (2 ^ m)) : x = y := by
  have h1 : (x - y) ^ (2 ^ m) = 0 := by rw [sub_pow_char_pow, h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h1)

theorem pow_two_pow_mod {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (hK : Fintype.card K = 2 ^ n) (x : K) (m : ℕ) : x ^ (2 ^ (m % n)) = x ^ (2 ^ m) := by
  have h : ∀ q : ℕ, x ^ (2 ^ (m % n + n * q)) = x ^ (2 ^ (m % n)) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, ← add_assoc, pow_add, pow_mul, ← hK, FiniteField.pow_card, ih]
  rw [← h (m / n), Nat.mod_add_div]

theorem card_le_of_frob_fixed {K : Type*} [Field K] {d : ℕ} (hd : 1 ≤ d) (s : Finset K)
    (hs : ∀ u ∈ s, u ^ (2 ^ d) = u) : s.card ≤ 2 ^ d := by
  classical
  have hq : 1 < 2 ^ d := Nat.one_lt_two_pow (by omega)
  by_contra hlt
  push Not at hlt
  have h := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (Polynomial.X ^ 2 ^ d - Polynomial.X : Polynomial K) s (fun u hu => by
      simp [hs u hu]) (by rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hq]; exact hlt)
  exact FiniteField.X_pow_card_sub_X_ne_zero K hq h

end Helpers

section Fixed

variable {k : Type*} [Field k] {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module k W]

theorem natCard_fixed_two_conj (ρ : Representation k G W) (x g₁ g₂ : G) :
    Nat.card {w : W // ρ (x * g₁ * x⁻¹) w = w ∧ ρ (x * g₂ * x⁻¹) w = w} =
      Nat.card {w : W // ρ g₁ w = w ∧ ρ g₂ w = w} := by
  have hx : ∀ v, ρ x (ρ x⁻¹ v) = v := fun v => by
    rw [← rep_mul_apply, mul_inv_cancel, rep_one_apply]
  have hx' : ∀ v, ρ x⁻¹ (ρ x v) = v := fun v => by
    rw [← rep_mul_apply, inv_mul_cancel, rep_one_apply]
  have key : ∀ (g : G) (w : W), ρ (x * g * x⁻¹) w = w ↔ ρ g (ρ x⁻¹ w) = ρ x⁻¹ w := by
    intro g w
    rw [rep_mul_apply, rep_mul_apply]
    constructor
    · intro h
      have h2 := congrArg (ρ x⁻¹) h
      rwa [hx'] at h2
    · intro h
      rw [h, hx]
  refine Nat.card_congr
    { toFun := fun w => ⟨ρ x⁻¹ w.1, (key g₁ w.1).mp w.2.1, (key g₂ w.1).mp w.2.2⟩
      invFun := fun w => ⟨ρ x w.1, by rw [key, hx']; exact w.2.1, by rw [key, hx']; exact w.2.2⟩
      left_inv := fun w => Subtype.ext (hx w.1)
      right_inv := fun w => Subtype.ext (hx' w.1) }

end Fixed

section Root

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]

theorem card_fixed_eq_of_card {n : ℕ} (hF : Fintype.card F = 2 ^ n) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type*} [Field E] [Finite E] [CharP E 2]
    (ιF : F →+* E) (ιD : EndRing ρ →+* E) (J : Finset ℕ) (hJn : ∀ i ∈ J, i < n)
    (Φ : (letI := ιF.toAlgebra; (matRepE b ιD).Equiv (frobTensor F E J)))
    (A : Subgroup SL(2, F)) (hA2 : ∀ a ∈ A, a * a = 1) (hcard : Nat.card A = 2 ^ n) :
    Nat.card {w : W // ∀ a ∈ A, ρ a w = w} = Nat.card (EndRing ρ) := by
  have hcardF : Nat.card A = Nat.card F := by rw [hcard, Nat.card_eq_fintype_card, hF]
  obtain ⟨x, hx⟩ := eq_conj_rootGroup A hA2 hcardF
  rw [natCard_fixed_conj ρ A _ x hx, ← natCard_fixW_rootGroup ρ hF b ιF ιD J hJn Φ]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  constructor
  · intro h t
    exact h _ ((mem_rootGroup_iff _).mpr ⟨t, rfl⟩)
  · intro h u hu
    obtain ⟨t, rfl⟩ := (mem_rootGroup_iff _).mp hu
    exact h t

end Root

section Class

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem dvd_two_mul_of_card_two {n d : ℕ} {J : Finset ℕ} (hJ : J.card = 2)
    (hJn : ∀ i ∈ J, i < n) (hshift : J.image (fun i => (i + d) % n) = J) (hnd : ¬ n ∣ d) :
    n ∣ 2 * d := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hJ
  have hx : x < n := hJn x (by simp)
  have hy : y < n := hJn y (by simp)
  have hmem : ∀ i ∈ ({x, y} : Finset ℕ), (i + d) % n ∈ ({x, y} : Finset ℕ) := fun i hi => by
    rw [← hshift]
    exact Finset.mem_image_of_mem _ hi
  have hne : ∀ i, i < n → (i + d) % n ≠ i := by
    intro i hi h
    apply hnd
    have h1 : (i + d) % n = (i + 0) % n := by rw [h, add_zero, Nat.mod_eq_of_lt hi]
    have h2 := Nat.ModEq.add_left_cancel' i h1
    exact (Nat.modEq_zero_iff_dvd.mp h2)
  have h1 := hmem x (by simp)
  have h2 := hmem y (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  have hxy' : (x + d) % n = y := h1.resolve_left (hne x hx)
  have hyx' : (y + d) % n = x := h2.resolve_right (hne y hy)
  have h3 : (x + 2 * d) % n = x % n :=
    calc (x + 2 * d) % n = ((x + d) % n + d) % n := by rw [Nat.mod_add_mod]; ring_nf
      _ = (y + d) % n := by rw [hxy']
      _ = x := hyx'
      _ = x % n := (Nat.mod_eq_of_lt hx).symm
  have h4 : (x + 2 * d) % n = (x + 0) % n := by rw [h3, add_zero]
  exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' x h4)

theorem inner_class {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1)
    (A : Subgroup SL(2, F)) (hA1 : A ≠ ⊥) (hA2 : ∀ a ∈ A, a * a = 1)
    (hoff : Nat.card W ≤ Nat.card A ^ 2 * Nat.card {w : W // ∀ a ∈ A, ρ a w = w}) :
    (Nat.card (EndRing ρ) = 2 ^ n ∧ Module.finrank (EndRing ρ) W = 2) ∨
      ∃ s, n = 2 * s ∧ Nat.card (EndRing ρ) = 2 ^ s ∧ Module.finrank (EndRing ρ) W = 4 := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := binary_SL2_irreducible_Frobenius_descent hn hF ρ hnt
  have hfinD : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  let b := Module.finBasis (EndRing ρ) W
  obtain ⟨E, hEF, hEfin, hEchar, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ := hdesc b
  obtain ⟨r, hr⟩ : ∃ r, J.card = r := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := hr ▸ Finset.card_pos.mpr hJne
  set C := Nat.card {w : W // ∀ a ∈ A, ρ a w = w} with hCdef
  obtain ⟨⟨a, haA⟩, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have ha1 : a ≠ 1 := fun h => ha (Subtype.ext h)
  have hfixa : Nat.card {w : W // ρ a w = w} = 2 ^ (d * 2 ^ (r - 1)) := by
    have h1 := natCard_fixW_involution ρ b ιF ιD J hJne Φ a ha1 (hA2 a haA)
    rw [hDcard, ← pow_mul, hr] at h1
    exact h1
  have hW : Nat.card W = 2 ^ (d * 2 ^ r) := by
    have h1 := natCard_eq_pow_finrank (ρ := ρ)
    rw [hDcard, hdim, ← pow_mul, hr] at h1
    exact h1
  have hCa : C ≤ 2 ^ (d * 2 ^ (r - 1)) := by
    rw [← hfixa]
    exact Nat.card_le_card_of_injective (fun w => ⟨w.1, w.2 a haA⟩) (by
      intro x y h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext h)
  have hAp : IsPGroup 2 A := fun g => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using hA2 g g.2⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAp
  have hkn : k ≤ n := by
    have := card_le_of_involutions A hA2
    rw [hk, Nat.card_eq_fintype_card (α := F), hF] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hoff' : 2 ^ (d * 2 ^ r) ≤ 2 ^ (2 * k) * C := by
    rw [← hW]
    calc Nat.card W ≤ Nat.card A ^ 2 * C := hoff
      _ = 2 ^ (2 * k) * C := by rw [hk, ← pow_mul, mul_comm k 2]
  have hroot : k = n → C = 2 ^ d := by
    intro hkn'
    rw [hCdef, card_fixed_eq_of_card ρ hF b ιF ιD J hJn Φ A hA2 (by rw [hk, hkn']), hDcard]
  have h2r : 2 ^ r = 2 * 2 ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hdn : d * 2 ^ (r - 1) ≤ 2 * n := by
    have h1 := exp_le_of_pow_le (hoff'.trans (Nat.mul_le_mul_left _ hCa))
    have h3 : d * 2 ^ r = 2 * (d * 2 ^ (r - 1)) := by rw [h2r]; ring
    omega
  have horb : n ≤ r * d := hr ▸ n_le_card_mul (by omega) (by omega) hJn hJne hshift
  have hr4 : r ≤ 4 := by
    by_contra h
    push Not at h
    have h1 := two_mul_lt_two_pow (show 5 ≤ r by omega)
    have h2 : d * 2 ^ (r - 1) ≤ 2 * (r * d) := hdn.trans (by omega)
    have h3 : d * 2 ^ (r - 1) ≤ d * (2 * r) := by
      calc d * 2 ^ (r - 1) ≤ 2 * (r * d) := h2
        _ = d * (2 * r) := by ring
    have h4 := Nat.le_of_mul_le_mul_left h3 (by omega)
    omega
  have hlt : k < n → 2 ^ (d * 2 ^ r) ≤ 2 ^ (2 * (n - 1)) * C := by
    intro hkn'
    refine hoff'.trans (Nat.mul_le_mul_right _ ?_)
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  interval_cases r
  ·
    left
    have hdim2 : Module.finrank (EndRing ρ) W = 2 := by rw [hdim, hr]; rfl
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hr
    have hj : j < n := hJn j (Finset.mem_singleton_self j)
    have hjd : (j + d) % n = j := by
      have h := hshift
      rw [Finset.image_singleton, Finset.singleton_inj] at h
      exact h
    have hnd : n ∣ d := by
      have h1 : (j + d) % n = (j + 0) % n := by rw [hjd, add_zero, Nat.mod_eq_of_lt hj]
      exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' j h1)
    have hdn' := eq_of_finrank_eq_two hn hF ρ hnt hDcard hdim2 hnd
    exact ⟨hdn' ▸ hDcard, hdim2⟩
  ·
    have hdim4 : Module.finrank (EndRing ρ) W = 4 := by rw [hdim, hr]; rfl
    have hdle : d ≤ n := by simp at hdn; omega
    rcases Nat.lt_or_ge d n with hdlt | hdge
    · right
      have hnd : ¬ n ∣ d := fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
      have h2d := dvd_two_mul_of_card_two hr hJn hshift hnd
      obtain ⟨c, hc⟩ := h2d
      have hc1 : c = 1 := by
        rcases Nat.lt_or_ge c 2 with h | h
        · interval_cases c
          · omega
          · rfl
        · nlinarith
      subst hc1
      exact ⟨d, by omega, hDcard, hdim4⟩
    · exfalso
      have hdn' : d = n := le_antisymm hdle hdge
      subst hdn'
      rcases Nat.lt_or_ge k d with hkn' | hkn'
      · have h1 := exp_le_of_pow_le ((hlt hkn').trans (Nat.mul_le_mul_left _ hCa))
        simp at h1
        omega
      · have hkd : k = d := le_antisymm hkn hkn'
        have h1 := hoff'
        rw [hroot hkd, hkd] at h1
        have h2 := exp_le_of_pow_le h1
        simp at h2
        omega
  ·
    exfalso
    simp at hdn horb
    have hnd : ¬ n ∣ d := fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
    rcases Nat.lt_or_ge k n with hkn' | hkn'
    · rcases Nat.lt_or_ge d k with hdk | hdk
      ·
        obtain ⟨x, hx⟩ := exists_conj_le_rootGroup A hA2
        have hxa := hx a haA
        obtain ⟨t₁, ht₁⟩ := (mem_rootGroup_iff _).mp hxa
        have ha' : a = x * uElt t₁ * x⁻¹ := by rw [← ht₁]; group
        have ht₁0 : t₁ ≠ 0 := by
          rintro rfl
          apply ha1
          rw [ha', uElt_zero, mul_one, mul_inv_cancel]
        let S : Finset F := Finset.univ.filter fun t => x * uElt t * x⁻¹ ∈ A
        have hAS : Nat.card A ≤ S.card := by
          rw [← Fintype.card_coe S, ← Nat.card_eq_fintype_card]
          refine Nat.card_le_card_of_injective
            (fun g => ⟨(mem_rootGroup_iff _).mp (hx g g.2) |>.choose, ?_⟩) ?_
          · have h := ((mem_rootGroup_iff _).mp (hx g g.2)).choose_spec
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [← h]
            simp [mul_assoc]
          · intro g g' h
            have h1 := congrArg Subtype.val h
            simp only at h1
            have e1 := ((mem_rootGroup_iff _).mp (hx g g.2)).choose_spec
            have e2 := ((mem_rootGroup_iff _).mp (hx g' g'.2)).choose_spec
            rw [h1] at e1
            have : (g : SL(2, F)) = g' := by
              have h2 : x⁻¹ * g * x = x⁻¹ * g' * x := e1.trans e2.symm
              simpa using h2
            exact Subtype.ext this
        obtain ⟨t₂, ht₂S, ht₂⟩ : ∃ t₂ ∈ S, (t₂ / t₁) ^ (2 ^ d) ≠ t₂ / t₁ := by
          by_contra hall
          push Not at hall
          have h1 : (S.image fun t => t / t₁).card ≤ 2 ^ d :=
            card_le_of_frob_fixed hd1 _ (fun u hu => by
              obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
              exact hall t ht)
          rw [Finset.card_image_of_injective _ (fun t t' h => by
            simpa [div_left_inj' ht₁0] using h)] at h1
          have h2 : 2 ^ k ≤ 2 ^ d := hk ▸ hAS.trans h1
          have h3 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
          omega
        have ht₂A : x * uElt t₂ * x⁻¹ ∈ A := (Finset.mem_filter.mp ht₂S).2
        obtain ⟨j, hjJ⟩ := hJne
        have hj : j < n := hJn j hjJ
        have hj' : (j + d) % n ∈ J := by
          rw [← hshift]
          exact Finset.mem_image_of_mem _ hjJ
        have hjne : j ≠ (j + d) % n := by
          intro h
          apply hnd
          have h1 : (j + d) % n = (j + 0) % n := by rw [← h, add_zero, Nat.mod_eq_of_lt hj]
          exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' j h1)
        have hdet : (ιF t₁) ^ (2 ^ j) * (ιF t₂) ^ (2 ^ ((j + d) % n)) ≠
            (ιF t₂) ^ (2 ^ j) * (ιF t₁) ^ (2 ^ ((j + d) % n)) := by
          intro h
          apply ht₂
          set u := t₂ / t₁ with hu
          have ht₂u : t₂ = u * t₁ := by rw [hu, div_mul_cancel₀ _ ht₁0]
          rw [ht₂u, map_mul, mul_pow, mul_pow] at h
          have hι : (ιF t₁) ^ (2 ^ j) * (ιF t₁) ^ (2 ^ ((j + d) % n)) ≠ 0 :=
            mul_ne_zero (pow_ne_zero _ ((map_ne_zero ιF).mpr ht₁0))
              (pow_ne_zero _ ((map_ne_zero ιF).mpr ht₁0))
          have h1 : (ιF u) ^ (2 ^ ((j + d) % n)) = (ιF u) ^ (2 ^ j) := by
            have h2 : ((ιF u) ^ (2 ^ ((j + d) % n)) - (ιF u) ^ (2 ^ j)) *
                ((ιF t₁) ^ (2 ^ j) * (ιF t₁) ^ (2 ^ ((j + d) % n))) = 0 := by
              linear_combination h
            exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hι)
          rw [← map_pow, ← map_pow] at h1
          have h2 : u ^ (2 ^ ((j + d) % n)) = u ^ (2 ^ j) := ιF.injective h1
          rw [pow_two_pow_mod hF, pow_add, pow_mul, ← pow_mul, mul_comm, pow_mul] at h2
          exact frob_pow_injective j h2
        have hpair := natCard_fixW_pair_le ρ b ιF ιD J hr Φ hjJ hj' hjne ht₁0 hdet
        have hCpair : C ≤ Nat.card (EndRing ρ) ^ 2 := by
          refine le_trans ?_ (natCard_fixed_two_conj ρ x (uElt t₁) (uElt t₂) ▸ hpair)
          refine Nat.card_le_card_of_injective
            (fun w => ⟨w.1, w.2 _ (ha' ▸ haA), w.2 _ ht₂A⟩) (fun w w' h => ?_)
          have h' := congrArg Subtype.val h
          exact Subtype.ext h'
        rw [hDcard, ← pow_mul] at hCpair
        have h1 := exp_le_of_pow_le ((hlt hkn').trans (Nat.mul_le_mul_left _ hCpair))
        simp at h1
        omega
      · have h1 := exp_le_of_pow_le (hoff'.trans (Nat.mul_le_mul_left _ hCa))
        simp at h1
        omega
    · have hkd : k = n := le_antisymm hkn hkn'
      have h1 := hoff'
      rw [hroot hkd, hkd] at h1
      have h2 := exp_le_of_pow_le h1
      simp at h2
      omega
  ·
    exfalso
    simp at hdn horb
    rcases Nat.lt_or_ge k n with hkn' | hkn'
    · have h1 := exp_le_of_pow_le ((hlt hkn').trans (Nat.mul_le_mul_left _ hCa))
      simp at h1
      omega
    · have hkd : k = n := le_antisymm hkn hkn'
      have h1 := hoff'
      rw [hroot hkd, hkd] at h1
      have h2 := exp_le_of_pow_le h1
      simp at h2
      omega

end Class

end CFSG.Quasithin.B45L2
