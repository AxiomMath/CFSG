module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieCartanAux

public section

namespace CFSG.StandardType

open Finset Module
open scoped BigOperators

lemma ggNSLiePI2_ext_row {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {n : ℕ} (hn : 0 < n) (x : ℕ → V) (f : ℕ → Module.Dual K V) (c : Fin n → K)
    (c' : ℕ → K) (hc' : ∀ k (h : k < n), c' k = c ⟨k, h⟩)
    (hc'ge : ∀ k, n ≤ k → c' k = 0)
    (hdiag : ∀ i, i < n → f i (x i) = 2)
    (hoff : ∀ i j, i < n → j < n → j ≠ i → j ≠ i + 1 → i ≠ j + 1 → f i (x j) = 0)
    (hc : ∀ i : Fin n, ∑ j : Fin n, f i.val (x j.val) * c j = 0) :
    2 * c' 0 + f 0 (x 1) * c' 1 = 0 ∧
    (∀ i, 1 ≤ i → i < n →
      f i (x (i - 1)) * c' (i - 1) + 2 * c' i + f i (x (i + 1)) * c' (i + 1) = 0) := by
  have hsum : ∀ i : Fin n, ∑ j : Fin n, f i.val (x j.val) * c' j.val = 0 := by
    intro i
    rw [← hc i]
    apply Finset.sum_congr rfl
    intro j _
    rw [hc' j.val j.isLt]
  constructor
  · have hband := ggNSLiePI2_sum_band (fun j : Fin n => f 0 (x j.val) * c' j.val) ⟨0, hn⟩ (by
      intro j hji hj1 hi1
      rw [hoff 0 j.val hn j.isLt (fun hv => hji (Fin.ext hv)) hj1 (by omega), zero_mul])
    rw [hsum ⟨0, hn⟩] at hband
    simp only [dif_neg (Nat.lt_irrefl 0), add_zero] at hband
    have hg0 : f 0 (x (⟨0, hn⟩ : Fin n).val) * c' (⟨0, hn⟩ : Fin n).val = 2 * c' 0 := by
      rw [hdiag 0 hn]
    by_cases h1n : 1 < n
    · rw [dif_pos h1n] at hband
      rw [hg0] at hband
      exact hband.symm
    · rw [dif_neg h1n] at hband
      have hc1 : c' 1 = 0 := hc'ge 1 (by omega)
      rw [hg0, add_zero] at hband
      rw [hc1, mul_zero, add_zero]
      exact hband.symm
  · intro i hi1 hin
    have hband := ggNSLiePI2_sum_band (fun j : Fin n => f i (x j.val) * c' j.val) ⟨i, hin⟩ (by
      intro j hji hj1 hi1'
      rw [hoff i j.val hin j.isLt (fun hv => hji (Fin.ext hv)) hj1 (by simpa using hi1'), zero_mul])
    rw [hsum ⟨i, hin⟩] at hband
    have hg0 : f i (x (⟨i, hin⟩ : Fin n).val) * c' (⟨i, hin⟩ : Fin n).val = 2 * c' i := by
      rw [hdiag i hin]
    have hpred : (⟨i, hin⟩ : Fin n).val - 1 = i - 1 := rfl
    have hgpred : f i (x ((⟨i, hin⟩ : Fin n).val - 1)) * c' ((⟨i, hin⟩ : Fin n).val - 1)
        = f i (x (i - 1)) * c' (i - 1) := by rw [hpred]
    rw [dif_pos (show 0 < (⟨i, hin⟩ : Fin n).val from by simp only [Fin.val_mk]; omega), hg0] at hband
    by_cases h1n : i + 1 < n
    · rw [dif_pos h1n] at hband
      have hgs : f i (x (⟨i + 1, h1n⟩ : Fin n).val) * c' (⟨i + 1, h1n⟩ : Fin n).val
          = f i (x (i + 1)) * c' (i + 1) := by
        rw [hc' (i + 1) h1n]
      rw [hgs, hgpred] at hband
      rw [show f i (x (i - 1)) * c' (i - 1) + 2 * c' i + f i (x (i + 1)) * c' (i + 1)
          = 2 * c' i + f i (x (i + 1)) * c' (i + 1) + f i (x (i - 1)) * c' (i - 1)
          from by ring, ← hband]
    · rw [dif_neg h1n] at hband
      have hc1 : c' (i + 1) = 0 := hc'ge (i + 1) (by omega)
      rw [hgpred, add_zero] at hband
      rw [hc1, mul_zero, add_zero]
      rw [show f i (x (i - 1)) * c' (i - 1) + 2 * c' i
          = 2 * c' i + f i (x (i - 1)) * c' (i - 1) from by ring]
      exact hband.symm

theorem ggNSLiePI2_rank_bound {K : Type*} [Field K] [DecidableEq K] {V : Type*} [AddCommGroup V]
    [Module K V] [Module.Finite K V]
    (n : ℕ) (x : ℕ → V) (f : ℕ → Module.Dual K V)
    (hdiag : ∀ i, i < n → f i (x i) = 2)
    (hoff : ∀ i j, i < n → j < n → j ≠ i → j ≠ i + 1 → i ≠ j + 1 → f i (x j) = 0)
    (hadj : ∀ i, i + 1 < n → f i (x (i + 1)) * f (i + 1) (x i) = 1) :
    n - (if (n + 1 : K) = 0 then 1 else 0) ≤ Module.finrank K V := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hp1 : (1 : K) ≠ 0 := one_ne_zero
    simp [hp1]
  let F : V →ₗ[K] (Fin n → K) :=
    { toFun := fun v i => f i.val v
      map_add' := by intro u v; ext i; simp
      map_smul' := by intro a v; ext i; simp }
  let X : (Fin n → K) →ₗ[K] V :=
    { toFun := fun c => ∑ j : Fin n, c j • x j.val
      map_add' := by
        intro c d
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        simp only [Pi.smul_apply, smul_assoc, Finset.smul_sum]
        rfl }
  let A : (Fin n → K) →ₗ[K] (Fin n → K) := F.comp X
  have hAapply : ∀ (c : Fin n → K) (i : Fin n),
      (A c) i = ∑ j : Fin n, f i.val (x j.val) * c j := by
    intro c i
    change f i.val (∑ j : Fin n, c j • x j.val) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, smul_eq_mul]
    ring
  have hle : Module.finrank K (LinearMap.range A) ≤ Module.finrank (K) V := by
    have h1 : LinearMap.range A ≤ LinearMap.range F := by
      rw [show A = F.comp X from rfl, LinearMap.range_comp]
      rintro v ⟨w, -, rfl⟩
      exact ⟨w, rfl⟩
    haveI : Module.Finite (K) ↥(LinearMap.range F) := by infer_instance
    exact le_trans (Submodule.finrank_mono h1) (LinearMap.finrank_range_le F)
  have hrank' : Module.finrank K (LinearMap.range A) + Module.finrank K (LinearMap.ker A)
      = Module.finrank K (Fin n → K) := by
    haveI : Module.Finite K (Fin n → K) := Module.Finite.pi
    exact LinearMap.finrank_range_add_finrank_ker A
  have hrank : Module.finrank K (LinearMap.range A) + Module.finrank K (LinearMap.ker A)
      = n := by
    rw [hrank', Module.finrank_fintype_fun_eq_card (K) (η := Fin n), Fintype.card_fin]
  have hzero_of_coord : ∀ c : Fin n → K, A c = 0 → c ⟨0, hn⟩ = 0 → c = 0 := by
    intro c hAc hc0
    let c' : ℕ → K := fun k => if h : k < n then c ⟨k, h⟩ else 0
    have hc' : ∀ k (h : k < n), c' k = c ⟨k, h⟩ := fun k h => dif_pos h
    have hc'ge' : ∀ k, n ≤ k → c' k = 0 := fun k h => dif_neg (by omega)
    have hcA : ∀ i : Fin n, ∑ j : Fin n, f i.val (x j.val) * c j = 0 := by
      intro i; rw [← hAapply c i, hAc]; rfl
    obtain ⟨hrow0, hrowi⟩ := ggNSLiePI2_ext_row hn x f c c' hc' hc'ge' hdiag hoff hcA
    have ha0 : ∀ k, k + 1 < n → f k (x (k + 1)) ≠ 0 := by
      intro k hk
      have h := hadj k hk
      intro h0; rw [h0, zero_mul] at h; exact one_ne_zero h.symm
    have hmain : ∀ k, k ≤ n - 1 → c' k = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        rcases k with _ | k'
        · rw [hc' 0 hn]; exact hc0
        · rcases k' with _ | k''
          · have hlt : 1 < n := by omega
            have hf : f 0 (x 1) ≠ 0 := ha0 0 hlt
            have h0' := hrow0
            rw [hc' 0 hn, hc0, mul_zero, zero_add] at h0'
            have hthis : c' 1 = 0 := by
              rcases mul_eq_zero.mp h0' with h | h
              · exact absurd h hf
              · exact h
            exact hthis
          · have hlt : k'' + 1 < n := by omega
            have hle : 1 ≤ k'' + 1 := by omega
            have hrow := hrowi (k'' + 1) hle hlt
            have h1 : c' (k'' + 1 - 1) = 0 := by
              rw [show k'' + 1 - 1 = k'' by omega]
              exact ih k'' (by omega) (by omega)
            have h2 : c' (k'' + 1) = 0 := ih (k'' + 1) (by omega) (by omega)
            rw [h1, h2, mul_zero, mul_zero, add_zero, zero_add] at hrow
            have hf : f (k'' + 1) (x (k'' + 1 + 1)) ≠ 0 := ha0 (k'' + 1) (by omega)
            have hthis : c' (k'' + 2) = 0 := by
              rcases mul_eq_zero.mp hrow with h | h
              · exact absurd h hf
              · exact h
            exact hthis
    funext i
    have h := hmain i.val (by omega)
    rwa [hc' i.val i.isLt] at h
  have hseq : ∀ c : Fin n → K, A c = 0 → (n + 1 : K) * c ⟨0, hn⟩ = 0 := by
    intro c hAc
    let c' : ℕ → K := fun k => if h : k < n then c ⟨k, h⟩ else 0
    have hc' : ∀ k (h : k < n), c' k = c ⟨k, h⟩ := fun k h => dif_pos h
    have hc'ge' : ∀ k, n ≤ k → c' k = 0 := fun k h => dif_neg (by omega)
    have hcA : ∀ i : Fin n, ∑ j : Fin n, f i.val (x j.val) * c j = 0 := by
      intro i; rw [← hAapply c i, hAc]; rfl
    obtain ⟨hrow0, hrowi⟩ := ggNSLiePI2_ext_row hn x f c c' hc' hc'ge' hdiag hoff hcA
    have ha : ∀ i, i < n - 1 → f i (x (i + 1)) ≠ 0 := by
      intro i hi
      have h := hadj i (by omega)
      intro h0; rw [h0, zero_mul] at h; exact one_ne_zero h.symm
    have hab : ∀ i, i < n - 1 → f i (x (i + 1)) * f (i + 1) (x i) = 1 := by
      intro i hi; exact hadj i (by omega)
    have h0' : 2 * c' 0 + f 0 (x (0 + 1)) * c' (0 + 1) = 0 := by simpa using hrow0
    have hrow'' : ∀ i, 1 ≤ i → i < n →
        f (i - 1 + 1) (x (i - 1)) * c' (i - 1) + 2 * c' i + f i (x (i + 1)) * c' (i + 1) = 0 := by
      intro i hi1 hin
      have h := hrowi i hi1 hin
      simpa only [show i - 1 + 1 = i by omega] using h
    have hthis := ggNSLiePI2_seq_bound n (fun i => f i (x (i + 1))) (fun i => f (i + 1) (x i)) c'
      hc'ge' ha hab h0' hrow''
    rwa [hc' 0 hn] at hthis
  have hker : Module.finrank K (LinearMap.ker A) ≤ (if (n + 1 : K) = 0 then 1 else 0) := by
    by_cases hp : (n + 1 : K) = 0
    · rw [if_pos hp]
      let ev0 : (LinearMap.ker A) →ₗ[K] K :=
        { toFun := fun c => c.1 ⟨0, hn⟩
          map_add' := by intro a b; rfl
          map_smul' := by intro a b; rfl }
      have hinj : Function.Injective ev0 := by
        intro a b hab
        have h1 : a.1 ⟨0, hn⟩ = b.1 ⟨0, hn⟩ := hab
        have hz : (a.1 - b.1) ⟨0, hn⟩ = 0 := by
          rw [Pi.sub_apply]; exact sub_eq_zero.mpr h1
        have hmem : A (a.1 - b.1) = 0 := by
          rw [map_sub, LinearMap.mem_ker.mp a.2, LinearMap.mem_ker.mp b.2]
          exact sub_self 0
        have hz' : a.1 - b.1 = 0 := hzero_of_coord (a.1 - b.1) hmem hz
        exact Subtype.ext (sub_eq_zero.mp hz')
      have h1 := LinearMap.finrank_le_finrank_of_injective hinj
      simpa using h1
    · rw [if_neg hp]
      have hne : (n : K) + 1 ≠ 0 := hp
      have hkerbot : LinearMap.ker A = ⊥ :=
        LinearMap.ker_eq_bot.mpr (fun a b hab => by
          have hsub : A (a - b) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hab
          have h0 : ((n : K) + 1) * (a - b) ⟨0, hn⟩ = 0 := hseq (a - b) hsub
          have hz : (a - b) ⟨0, hn⟩ = 0 := by
            rcases mul_eq_zero.mp h0 with h | h
            · exact absurd h hne
            · exact h
          have hzb : a - b = 0 := hzero_of_coord (a - b) hsub hz
          exact sub_eq_zero.mp hzb)
      rw [hkerbot]; simp
  have hrange : n - (if (n + 1 : K) = 0 then 1 else 0) ≤
      Module.finrank K (LinearMap.range A) := by
    have h1 := Nat.sub_le_sub_left hker n
    have h2 : n - Module.finrank K (LinearMap.ker A) =
        Module.finrank K (LinearMap.range A) := by omega
    rwa [h2] at h1
  exact le_trans hrange hle

lemma ggNSLiePI2_braid {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {r t : V ≃ₗ[K] V} {x y : V} {f g : Module.Dual K V}
    (hr : ∀ v, r v = v - f v • x) (ht : ∀ v, t v = v - g v • y)
    (hfx : f x = 2) (hgy : g y = 2)
    (hbraid : r * t * r = t * r * t) :
    (1 - f y * g x) • (f y • x - 2 • y) = 0 := by
  have h := congrArg (fun T : V ≃ₗ[K] V => T y) hbraid
  simp only [LinearEquiv.mul_apply] at h
  have hL : r (t (r y)) = (f y * (2 - f y * g x)) • x + (f y * g x - 1) • y := by
    simp only [hr, ht, hfx, hgy, map_sub, map_smul, map_neg, map_add, smul_sub, smul_smul,
      smul_neg, sub_eq_add_neg, neg_add_rev, neg_neg]
    module
  have hR : t (r (t y)) = f y • x + (1 - f y * g x) • y := by
    simp only [ht, hr, hfx, hgy, map_sub, map_smul, map_neg, map_add, smul_sub, smul_smul,
      smul_neg, sub_eq_add_neg, neg_add_rev, neg_neg]
    module
  rw [hL, hR] at h
  have hAB : (f y * (2 - f y * g x)) • x + (f y * g x - 1) • y
      - (f y • x + (1 - f y * g x) • y) = 0 := sub_eq_zero.mpr h
  rw [← hAB]
  module

end CFSG.StandardType
