module

public import CFSG.RankThree.SubgroupLists.SymplecticReducible
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import CFSG.CharacterTheory.Wreathed.OddLinearThreeCentralizerCore
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups
public import Certificates.Certificate43

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open Matrix CFSG CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

open CFSG.Wreathed.OddLinearThreeCentralizerCore in
theorem finrank_eigenspace_eq_two {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {t : GL (Fin 4) K}
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (hdet : (t : Matrix (Fin 4) (Fin 4) K).det = 1) :
    Module.finrank K
        (Module.End.eigenspace (Matrix.toLin' (t : Matrix (Fin 4) (Fin 4) K)) 1) = 2 ∧
      Module.finrank K
        (Module.End.eigenspace (Matrix.toLin' (t : Matrix (Fin 4) (Fin 4) K)) (-1)) = 2 := by
  set a : Module.End K (Fin 4 → K) := Matrix.toLin' (t : Matrix (Fin 4) (Fin 4) K) with ha
  have htt : (t : Matrix (Fin 4) (Fin 4) K) * (t : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, ht2, Units.val_one]
  have hinv : Function.Involutive a := by
    intro v
    rw [ha, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, htt,
      Matrix.one_mulVec]
  have hsum := involution_finrank_sum h2 a hinv
  rw [Module.finrank_fin_fun] at hsum
  have hpow : (-1 : K) ^ Module.finrank K (minusSpace a) = 1 := by
    rw [← involution_det_eq h2 a hinv, ha, LinearMap.det_toLin', hdet]
  have hneq : (-1 : K) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  obtain ⟨r, hr⟩ := (neg_one_pow_eq_one_iff_even hneq).mp hpow
  have hm0 : Module.finrank K (minusSpace a) ≠ 0 := by
    intro hz
    apply ht1
    have hid := involution_eq_id_of_minus_bot h2 a hinv (Submodule.finrank_eq_zero.mp hz)
    apply Units.ext
    apply Matrix.toLin'.injective
    rw [Units.val_one, Matrix.toLin'_one, ← ha]
    exact hid
  have hp0 : Module.finrank K (plusSpace a) ≠ 0 := by
    intro hz
    apply htm
    have hminus : minusSpace a = ⊤ := by
      have hsup := (involution_spaces_isCompl h2 a hinv).sup_eq_top
      rwa [Submodule.finrank_eq_zero.mp hz, sup_bot_eq] at hsup
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ minusSpace a := hminus ▸ Submodule.mem_top
    rw [← ha, Module.End.mem_eigenspace_iff.mp hv, Units.val_neg, Units.val_one,
      Matrix.toLin'_apply, Matrix.neg_mulVec, Matrix.one_mulVec, neg_one_smul]
  change Module.finrank K (plusSpace a) = 2 ∧ Module.finrank K (minusSpace a) = 2
  omega

theorem isQuasisimple_and_card_center_of_isPerfect_gl2 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (J : Subgroup (GL (Fin 2) (ZMod p))) [Group.IsPerfect J] (hJ : J ≠ ⊥) :
    IsQuasisimple J ∧ Nat.card (Subgroup.center J) = 2 := by
  rcases perfect_gl2_mulEquiv (by omega) J hJ with h | h
  · obtain ⟨e⟩ := h
    exact ⟨LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_SL2 hp5),
      (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans (card_center_SL2 (by omega))⟩
  · obtain ⟨e⟩ := h
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact ⟨LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_SL2 le_rfl),
      (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans (card_center_SL2 (by norm_num))⟩

theorem le_center_of_isPGroup_two_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) {M : Subgroup Q} (hM : M.Normal) (h2 : IsPGroup 2 M) :
    M ≤ Subgroup.center Q := by
  rcases LocalCores.quasisimple_normal_subgroups hQ hM with h | h
  · have : Nontrivial Q := LocalCores.isQuasisimple_nontrivial hQ
    have : Group.IsPerfect Q := hQ.1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQ2 : IsPGroup 2 Q := fun g => by
      obtain ⟨k, hk⟩ := h2 ⟨g, h ▸ Subgroup.mem_top g⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    exact absurd hQ2.isNilpotent (Group.IsPerfect.not_isNilpotent Q)
  · exact h

theorem eq_bot_of_odd_card_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) (hZ : Nat.card (Subgroup.center Q) = 2) {M : Subgroup Q}
    (hM : M.Normal) (hodd : Odd (Nat.card M)) : M = ⊥ := by
  rcases LocalCores.quasisimple_normal_subgroups hQ hM with h | h
  · rw [h, Subgroup.card_top] at hodd
    have h2 : 2 ∣ Nat.card Q := hZ ▸ Subgroup.card_subgroup_dvd_card (Subgroup.center Q)
    exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hodd)
  · have hdvd : Nat.card M ∣ 2 := hZ ▸ Subgroup.card_dvd_of_le h
    apply Subgroup.eq_bot_of_card_eq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact h1
    · rw [h1] at hodd
      exact absurd hodd (Nat.not_odd_iff_even.mpr even_two)

theorem gl2Rep_normal_two_odd {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {G : Type*} [Group G]
    [Finite G] [Group.IsPerfect G] (ρ : G →* GL (Fin 2) (ZMod p)) {N : Subgroup G}
    (hN : N.Normal) :
    (IsPGroup 2 N → ∀ n ∈ N, ∀ g, ρ (g * n) = ρ (n * g)) ∧
      (Odd (Nat.card N) → ∀ n ∈ N, ρ n = 1) := by
  by_cases hbot : ρ.range = ⊥
  · have h1 : ∀ g, ρ g = 1 := fun g => by
      have hg : ρ g ∈ ρ.range := ⟨g, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at hg
    exact ⟨fun _ n _ g => by rw [h1, h1], fun _ n _ => h1 n⟩
  have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  obtain ⟨hQ, hZ⟩ := isQuasisimple_and_card_center_of_isPerfect_gl2 hp5 ρ.range hbot
  have hM : (N.map ρ.rangeRestrict).Normal := hN.map ρ.rangeRestrict ρ.rangeRestrict_surjective
  refine ⟨fun h2N n hn g => ?_, fun hodd n hn => ?_⟩
  · have hMc := le_center_of_isPGroup_two_of_isQuasisimple hQ hM (h2N.map ρ.rangeRestrict)
    have hc := Subgroup.mem_center_iff.mp (hMc ⟨n, hn, rfl⟩) (ρ.rangeRestrict g)
    have hc' := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul, MonoidHom.coe_rangeRestrict] at hc'
    rw [map_mul, map_mul, hc']
  · have hMbot := eq_bot_of_odd_card_of_isQuasisimple hQ hZ hM
      (hodd.of_dvd_nat (Subgroup.card_map_dvd N _))
    have hn' : ρ.rangeRestrict n ∈ N.map ρ.rangeRestrict := ⟨n, hn, rfl⟩
    rw [hMbot, Subgroup.mem_bot] at hn'
    exact congrArg Subtype.val hn'

theorem normal_of_two_gl2_reps {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {G : Type*} [Group G]
    [Finite G] [Group.IsPerfect G] (ρ₁ ρ₂ : G →* GL (Fin 2) (ZMod p))
    (hjoint : ∀ g, ρ₁ g = 1 → ρ₂ g = 1 → g = 1) :
    (∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N ≤ Subgroup.center G) ∧
      (∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥) := by
  refine ⟨fun N hN h2N n hn => Subgroup.mem_center_iff.mpr fun g => ?_, fun N hN hodd => ?_⟩
  · have e₁ := (gl2Rep_normal_two_odd hp5 ρ₁ hN).1 h2N n hn g
    have e₂ := (gl2Rep_normal_two_odd hp5 ρ₂ hN).1 h2N n hn g
    exact mul_inv_eq_one.mp (hjoint _ (by rw [map_mul, map_inv, e₁, mul_inv_cancel])
      (by rw [map_mul, map_inv, e₂, mul_inv_cancel]))
  · refine eq_bot_iff.mpr fun n hn => Subgroup.mem_bot.mpr ?_
    exact hjoint n ((gl2Rep_normal_two_odd hp5 ρ₁ hN).2 hodd n hn)
      ((gl2Rep_normal_two_odd hp5 ρ₂ hN).2 hodd n hn)

theorem normal_of_commute_involution {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {H : Subgroup (GL (Fin 4) (ZMod p))} (hH : Group.IsPerfect H) {t : GL (Fin 4) (ZMod p)}
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htm : t ≠ -1)
    (hdet : (t : Matrix (Fin 4) (Fin 4) (ZMod p)).det = 1) (htH : ∀ h ∈ H, h * t = t * h) :
    (∀ N : Subgroup H, N.Normal → IsPGroup 2 N → N ≤ Subgroup.center H) ∧
      (∀ N : Subgroup H, N.Normal → Odd (Nat.card N) → N = ⊥) := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := by
    have h := (ZMod.natCast_eq_zero_iff 2 p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
    exact_mod_cast h
  obtain ⟨hd₁, hd₂⟩ := finrank_eigenspace_eq_two h2 ht2 ht1 htm hdet
  set a : Module.End (ZMod p) (Fin 4 → ZMod p) :=
    Matrix.toLin' (t : Matrix (Fin 4) (Fin 4) (ZMod p)) with ha
  have htt : (t : Matrix (Fin 4) (Fin 4) (ZMod p)) * t = 1 := by
    rw [← Units.val_mul, ht2, Units.val_one]
  have hinv : Function.Involutive a := by
    intro v
    rw [ha, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, htt,
      Matrix.one_mulVec]
  have hsup : a.eigenspace 1 ⊔ a.eigenspace (-1) = ⊤ := by
    rw [sup_comm]
    exact (CFSG.Wreathed.OddLinearThreeCentralizerCore.involution_spaces_isCompl h2 a
      hinv).sup_eq_top
  have hW : ∀ μ : ZMod p, SubgroupLists.IsInvariant H (a.eigenspace μ) := by
    intro μ x hx v hv
    rw [Module.End.mem_eigenspace_iff, ha, Matrix.toLin'_apply] at hv ⊢
    have hxt : (x : Matrix (Fin 4) (Fin 4) (ZMod p)) * t = t * x := by
      rw [← Units.val_mul, ← Units.val_mul, htH x hx]
    rw [Matrix.mulVec_mulVec, ← hxt, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  let b₁ := Module.finBasisOfFinrankEq (ZMod p) _
    ((finrank_section_bot (a.eigenspace 1)).trans hd₁)
  let b₂ := Module.finBasisOfFinrankEq (ZMod p) _
    ((finrank_section_bot (a.eigenspace (-1))).trans hd₂)
  have hρ₁ := sectionRep_bot_eq_one_iff H (hW 1) b₁
  have hρ₂ := sectionRep_bot_eq_one_iff H (hW (-1)) b₂
  refine normal_of_two_gl2_reps hp5 (sectionRep H (isInvariant_bot H) (hW 1) b₁)
    (sectionRep H (isInvariant_bot H) (hW (-1)) b₂) fun g h1 h2 => ?_
  apply Subtype.ext
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  have hv : v ∈ a.eigenspace 1 ⊔ a.eigenspace (-1) := hsup ▸ Submodule.mem_top
  obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
  rw [Matrix.mulVec_add, (hρ₁ g).mp h1 w hw, (hρ₂ g).mp h2 w' hw', OneMemClass.coe_one,
    Units.val_one, Matrix.one_mulVec]

theorem mulVec_mulVec_of_commute {n R : Type*} [Fintype n] [CommRing R] {A B : Matrix n n R}
    (h : A * B = B * A) (w : n → R) : A *ᵥ (B *ᵥ w) = B *ᵥ (A *ᵥ w) := by
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec]

theorem mulVec_mulVec_of_anticommute {n R : Type*} [Fintype n] [CommRing R]
    {A B : Matrix n n R} (h : A * B = -(B * A)) (w : n → R) :
    A *ᵥ (B *ᵥ w) = -(B *ᵥ (A *ᵥ w)) := by
  rw [Matrix.mulVec_mulVec, h, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]

theorem mulVec_ne_zero_of_mul_self_eq_one {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] {A : Matrix n n R} (h : A * A = 1) {w : n → R} (hw : w ≠ 0) :
    A *ᵥ w ≠ 0 := by
  intro h0
  apply hw
  rw [← Matrix.one_mulVec w, ← h, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

theorem conj_mul_eq_of_mul_eq {R : Type*} [Ring R] {v a a' b b' : R} (hv : v * v = 1)
    (ha : v * a = a' * v) (hb : v * b = b' * v) : v * (a * b) * v = a' * b' := by
  rw [← mul_assoc, ha, mul_assoc a', hb, mul_assoc, mul_assoc, hv, mul_one]

theorem one_add_mul_one_add_ne_zero {R : Type*} [Ring R] (h4 : (4 : R) ≠ 0) {u₁ v₁ u₂ v₂ : R}
    (hv₁ : v₁ * v₁ = 1) (hv₂ : v₂ * v₂ = 1) (h₁ : u₁ * v₁ = -(v₁ * u₁))
    (h₂ : u₂ * v₂ = -(v₂ * u₂)) (huv : u₁ * v₂ = v₂ * u₁) (hvu : v₁ * u₂ = u₂ * v₁) :
    (1 + u₁) * (1 + u₂) ≠ 0 := by
  intro h0
  have hv₁a : v₁ * (1 + u₁) = (1 - u₁) * v₁ := by
    rw [mul_add, mul_one, sub_mul, one_mul, h₁, sub_neg_eq_add]
  have hv₁b : v₁ * (1 + u₂) = (1 + u₂) * v₁ := by
    rw [mul_add, add_mul, mul_one, one_mul, hvu]
  have hv₂a : v₂ * (1 + u₁) = (1 + u₁) * v₂ := by
    rw [mul_add, add_mul, mul_one, one_mul, huv]
  have hv₂a' : v₂ * (1 - u₁) = (1 - u₁) * v₂ := by
    rw [mul_sub, sub_mul, mul_one, one_mul, huv]
  have hv₂b : v₂ * (1 + u₂) = (1 - u₂) * v₂ := by
    rw [mul_add, mul_one, sub_mul, one_mul, h₂, sub_neg_eq_add]
  have k₁ : (1 - u₁) * (1 + u₂) = 0 := by
    rw [← conj_mul_eq_of_mul_eq hv₁ hv₁a hv₁b, h0, mul_zero, zero_mul]
  have k₂ : (1 + u₁) * (1 - u₂) = 0 := by
    rw [← conj_mul_eq_of_mul_eq hv₂ hv₂a hv₂b, h0, mul_zero, zero_mul]
  have k₃ : (1 - u₁) * (1 - u₂) = 0 := by
    rw [← conj_mul_eq_of_mul_eq hv₂ hv₂a' hv₂b, k₁, mul_zero, zero_mul]
  have hsum : (1 + u₁) * (1 + u₂) + (1 - u₁) * (1 + u₂) + (1 + u₁) * (1 - u₂) +
      (1 - u₁) * (1 - u₂) = 4 := by
    noncomm_ring
    simp
  rw [h0, k₁, k₂, k₃, add_zero, add_zero, add_zero] at hsum
  exact h4 hsum.symm

theorem eq_scalar_of_commute_d8d8 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {u₁ v₁ u₂ v₂ : Matrix (Fin 4) (Fin 4) (ZMod p)} (hu₁ : u₁ * u₁ = 1) (hv₁ : v₁ * v₁ = 1)
    (hu₂ : u₂ * u₂ = 1) (hv₂ : v₂ * v₂ = 1) (h₁ : u₁ * v₁ = -(v₁ * u₁))
    (h₂ : u₂ * v₂ = -(v₂ * u₂)) (huu : u₁ * u₂ = u₂ * u₁) (huv : u₁ * v₂ = v₂ * u₁)
    (hvu : v₁ * u₂ = u₂ * v₁) (hvv : v₁ * v₂ = v₂ * v₁) {c : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hc₁ : c * u₁ = u₁ * c) (hc₂ : c * v₁ = v₁ * c) (hc₃ : c * u₂ = u₂ * c)
    (hc₄ : c * v₂ = v₂ * c) : ∃ μ : ZMod p, c = Matrix.scalar (Fin 4) μ := by
  classical
  have hn : ∀ n : ℕ, 0 < n → n < p → (n : ZMod p) ≠ 0 := fun n h0 hnp =>
    (ZMod.natCast_eq_zero_iff n p).not.mpr (Nat.not_dvd_of_pos_of_lt h0 hnp)
  have h2 : (2 : ZMod p) ≠ 0 := by exact_mod_cast hn 2 (by norm_num) (by omega)
  have h4 : (4 : Matrix (Fin 4) (Fin 4) (ZMod p)) ≠ 0 := by
    intro h
    have h00 := congrFun (congrFun h 0) 0
    rw [Matrix.zero_apply, Matrix.ofNat_apply, ite_eq_left rfl] at h00
    exact hn 4 (by norm_num) (by omega) h00
  obtain ⟨x, hx0, hux₁, hux₂⟩ : ∃ x : Fin 4 → ZMod p, x ≠ 0 ∧ u₁ *ᵥ x = x ∧ u₂ *ᵥ x = x := by
    obtain ⟨y, hy⟩ : ∃ y, ((1 + u₁) * (1 + u₂)) *ᵥ y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact one_add_mul_one_add_ne_zero h4 hv₁ hv₂ h₁ h₂ huv hvu
        (Matrix.ext_iff_mulVec.mpr fun v => by rw [hcon v, Matrix.zero_mulVec])
    have hu₁a : u₁ * (1 + u₁) = 1 + u₁ := by rw [mul_add, mul_one, hu₁, add_comm]
    have hu₂a : u₂ * (1 + u₁) = (1 + u₁) * u₂ := by
      rw [mul_add, add_mul, mul_one, one_mul, huu]
    have hu₂b : u₂ * (1 + u₂) = 1 + u₂ := by rw [mul_add, mul_one, hu₂, add_comm]
    refine ⟨_, hy, ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, ← mul_assoc, hu₁a]
    · rw [Matrix.mulVec_mulVec, ← mul_assoc, hu₂a, mul_assoc, hu₂b]
  obtain ⟨F, hF⟩ : ∃ F : Matrix (Fin 4) (Fin 4) (ZMod p), F = u₁ + (2 : ZMod p) • u₂ := ⟨_, rfl⟩
  have hFw : ∀ w, F *ᵥ w = u₁ *ᵥ w + (2 : ZMod p) • (u₂ *ᵥ w) := fun w => by
    rw [hF, Matrix.add_mulVec, Matrix.smul_mulVec]
  have hFc : F * c = c * F := by
    rw [hF, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hc₁, hc₃]
  have e₀ : F *ᵥ x = (3 : ZMod p) • x := by
    rw [hFw, hux₁, hux₂]
    module
  have e₁ : F *ᵥ (v₁ *ᵥ x) = (1 : ZMod p) • (v₁ *ᵥ x) := by
    rw [hFw, mulVec_mulVec_of_anticommute h₁, hux₁, mulVec_mulVec_of_commute hvu.symm, hux₂]
    module
  have e₂ : F *ᵥ (v₂ *ᵥ x) = (-1 : ZMod p) • (v₂ *ᵥ x) := by
    rw [hFw, mulVec_mulVec_of_commute huv, hux₁, mulVec_mulVec_of_anticommute h₂, hux₂]
    module
  have e₃ : F *ᵥ (v₁ *ᵥ (v₂ *ᵥ x)) = (-3 : ZMod p) • (v₁ *ᵥ (v₂ *ᵥ x)) := by
    rw [hFw, mulVec_mulVec_of_anticommute h₁, mulVec_mulVec_of_commute huv, hux₁,
      mulVec_mulVec_of_commute hvu.symm, mulVec_mulVec_of_anticommute h₂, hux₂,
      Matrix.mulVec_neg]
    module
  have hx₁ : v₁ *ᵥ x ≠ 0 := mulVec_ne_zero_of_mul_self_eq_one hv₁ hx0
  have hx₂ : v₂ *ᵥ x ≠ 0 := mulVec_ne_zero_of_mul_self_eq_one hv₂ hx0
  have hx₃ : v₁ *ᵥ (v₂ *ᵥ x) ≠ 0 := by
    rw [Matrix.mulVec_mulVec]
    refine mulVec_ne_zero_of_mul_self_eq_one ?_ hx0
    rw [mul_assoc, ← mul_assoc v₂, ← hvv, mul_assoc, hv₂, mul_one, hv₁]
  set xs : Fin 4 → Fin 4 → ZMod p := ![x, v₁ *ᵥ x, v₂ *ᵥ x, v₁ *ᵥ (v₂ *ᵥ x)] with hxs
  set μs : Fin 4 → ZMod p := ![3, 1, -1, -3] with hμs
  have heig : ∀ i, F *ᵥ xs i = μs i • xs i := by
    intro i
    fin_cases i
    · exact e₀
    · exact e₁
    · exact e₂
    · exact e₃
  have hne : ∀ i, xs i ≠ 0 := by
    intro i
    fin_cases i
    · exact hx0
    · exact hx₁
    · exact hx₂
    · exact hx₃
  have hμ : ∀ i : Fin 4, μs i = 3 - 2 * ((i : ℕ) : ZMod p) := by
    intro i
    fin_cases i <;> simp [hμs] <;> ring
  have hinj : Function.Injective μs := by
    intro i j hij
    rw [hμ, hμ] at hij
    have hij' : ((i : ℕ) : ZMod p) = ((j : ℕ) : ZMod p) := by
      have h0 : (2 : ZMod p) * (((i : ℕ) : ZMod p) - ((j : ℕ) : ZMod p)) = 0 := by
        linear_combination -hij
      exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left h2)
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by have := i.isLt; omega),
      Nat.mod_eq_of_lt (by have := j.isLt; omega)] at hij'
    exact Fin.ext hij'
  have hli : LinearIndependent (ZMod p) xs := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' F) μs hinj xs fun i => ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact ⟨heig i, hne i⟩
  have hcard : Fintype.card (Fin 4) = Module.finrank (ZMod p) (Fin 4 → ZMod p) := by simp
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp
    (by rw [hli.span_eq_top_of_card_eq_finrank hcard]; exact Submodule.mem_top :
      c *ᵥ x ∈ Submodule.span (ZMod p) (Set.range xs))
  have hcx : F *ᵥ (c *ᵥ x) = (3 : ZMod p) • (c *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, hFc, ← Matrix.mulVec_mulVec, e₀, Matrix.mulVec_smul]
  have hzero : ∑ i, (a i * (μs i - 3)) • xs i = 0 := by
    have hFs : F *ᵥ (∑ i, a i • xs i) = ∑ i, (a i * μs i) • xs i := by
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_smul, heig i, smul_smul]
    calc ∑ i, (a i * (μs i - 3)) • xs i =
          ∑ i, (a i * μs i) • xs i - (3 : ZMod p) • ∑ i, a i • xs i := by
          rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          module
      _ = 0 := by rw [← hFs, ha, hcx, sub_self]
  have hcoef := Fintype.linearIndependent_iff.mp hli _ hzero
  have ha0 : ∀ i, i ≠ 0 → a i = 0 := by
    intro i hi
    have hne3 : μs i - 3 ≠ 0 := sub_ne_zero.mpr (by simpa [hμs] using hinj.ne hi)
    exact (mul_eq_zero.mp (hcoef i)).resolve_right hne3
  have hcx' : c *ᵥ x = a 0 • x := by
    rw [← ha, Fintype.sum_eq_single 0 (fun i hi => by rw [ha0 i hi, zero_smul])]
    rfl
  have hcb : ∀ i, c *ᵥ xs i = a 0 • xs i := by
    intro i
    fin_cases i
    · exact hcx'
    · change c *ᵥ (v₁ *ᵥ x) = a 0 • (v₁ *ᵥ x)
      rw [mulVec_mulVec_of_commute hc₂, hcx', Matrix.mulVec_smul]
    · change c *ᵥ (v₂ *ᵥ x) = a 0 • (v₂ *ᵥ x)
      rw [mulVec_mulVec_of_commute hc₄, hcx', Matrix.mulVec_smul]
    · change c *ᵥ (v₁ *ᵥ (v₂ *ᵥ x)) = a 0 • (v₁ *ᵥ (v₂ *ᵥ x))
      rw [mulVec_mulVec_of_commute hc₂, mulVec_mulVec_of_commute hc₄, hcx', Matrix.mulVec_smul,
        Matrix.mulVec_smul]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨a 0, Matrix.toLin'.injective (b.ext fun i => ?_)⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.toLin'_apply, Matrix.toLin'_apply,
    hcb i]
  funext j
  rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]

end CFSG.RankThree.PartTwo.Sec4.Census
