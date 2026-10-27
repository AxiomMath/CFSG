module

public import CFSG.RankThree.PartOne.S12.Sec153Defs
public import CFSG.RankThree.PartOne.S12.Sec1322Reflect
import CFSG.LieType.Simplicity.Classical
public import CFSG.RankThree.PartOne.S12.PhanAssembly

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace Sec153

theorem exists_perm_two (a b i j : Fin 5) (hab : a ≠ b) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 5), σ a = i ∧ σ b = j := by
  refine ⟨Equiv.swap (Equiv.swap a i b) j * Equiv.swap a i, ?_, ?_⟩
  · revert a b i j; decide +kernel
  · revert a b i j; decide +kernel

theorem exists_third (i j : Fin 5) : ∃ k : Fin 5, k ≠ i ∧ k ≠ j := by
  revert i j; decide +kernel

@[expose] def GoodPair5 (t d : Equiv.Perm (Fin 5)) : Prop :=
  t * t = 1 ∧ t ≠ 1 ∧ d ^ 5 = 1 ∧ d ≠ 1 ∧ (t * d) ^ 4 = 1 ∧ (t * d) ^ 2 ≠ 1

instance (t d : Equiv.Perm (Fin 5)) : Decidable (GoodPair5 t d) := by
  unfold GoodPair5
  infer_instance

theorem closure_s5 :
    Subgroup.closure ({finRotate 5, Equiv.swap 0 1} : Set (Equiv.Perm (Fin 5))) = ⊤ := by
  have := Equiv.Perm.closure_cycle_adjacent_swap (σ := finRotate 5) isCycle_finRotate
    support_finRotate 0
  have h : Equiv.swap (0 : Fin 5) (finRotate 5 0) = Equiv.swap 0 1 := by decide
  rw [h] at this
  exact this

theorem pairs_conj5 : ∀ t d : Equiv.Perm (Fin 5), GoodPair5 t d →
    ∃ g : Equiv.Perm (Fin 5), g * Equiv.swap 0 1 * g⁻¹ = t ∧ g * finRotate 5 * g⁻¹ = d := by
  decide +kernel

theorem center5 : ∀ g : Equiv.Perm (Fin 5), g * Equiv.swap 0 1 = Equiv.swap 0 1 * g →
    g * finRotate 5 = finRotate 5 * g → g = 1 := by
  decide +kernel

theorem good5 : GoodPair5 (Equiv.swap 0 1) (finRotate 5) := by decide +kernel

theorem sym5_conj_surjective :
    Function.Surjective (MulAut.conj : Equiv.Perm (Fin 5) →* MulAut (Equiv.Perm (Fin 5))) := by
  intro φ
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := good5
  have hgood : GoodPair5 (φ (Equiv.swap 0 1)) (φ (finRotate 5)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← map_mul, h1, map_one]
    · intro h
      exact h2 (φ.injective (h.trans (map_one φ).symm))
    · rw [← map_pow, h3, map_one]
    · intro h
      exact h4 (φ.injective (h.trans (map_one φ).symm))
    · rw [← map_mul, ← map_pow, h5, map_one]
    · intro h
      exact h6 (φ.injective (by rw [map_pow, map_mul, h, map_one]))
  obtain ⟨g, hgs, hgc⟩ := pairs_conj5 _ _ hgood
  refine ⟨g, ?_⟩
  have e : (MulAut.conj g).toMonoidHom = φ.toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense closure_s5 ?_
    rintro x (rfl | rfl)
    · exact hgc
    · exact hgs
  exact MulEquiv.ext fun x => DFunLike.congr_fun e x

theorem sym5_center : ∀ σ : Equiv.Perm (Fin 5), (∀ τ, σ * τ = τ * σ) → σ = 1 :=
  fun σ h => center5 σ (h _) (h _)

section Module

variable {M : Type*} [CommGroup M]

theorem exists_const_of_fixed_perm {p : ℕ} (v : Fin 5 → M)
    (hrel : ∀ a : Fin 5 → ℤ, ∏ i, v i ^ a i = 1 ↔ ∃ m : ℤ, ∀ i, (p : ℤ) ∣ a i - m)
    (a : Fin 5 → ℤ) (π : Equiv.Perm (Fin 5)) (t : M ≃* M) (ht : ∀ k, t (v k) = v (π k))
    (hfx : t (∏ k, v k ^ a k) = ∏ k, v k ^ a k) :
    ∃ m : ℤ, ∀ j, (p : ℤ) ∣ a (π.symm j) - a j - m := by
  have h1 : t (∏ k, v k ^ a k) = ∏ k, v k ^ a (π.symm k) := by
    rw [map_prod]
    simp only [map_zpow, ht]
    exact Fintype.prod_equiv π _ _ (fun k => by simp)
  have h2 : ∏ k, v k ^ (a (π.symm k) - a k) = 1 := by
    simp only [zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    rw [← h1, hfx, mul_inv_cancel]
  exact (hrel _).1 h2

theorem dvd_of_fixed_swap {p : ℕ} (v : Fin 5 → M)
    (hrel : ∀ a : Fin 5 → ℤ, ∏ i, v i ^ a i = 1 ↔ ∃ m : ℤ, ∀ i, (p : ℤ) ∣ a i - m)
    (a : Fin 5 → ℤ) {i j : Fin 5} (t : M ≃* M) (ht : ∀ k, t (v k) = v (Equiv.swap i j k))
    (hfx : t (∏ k, v k ^ a k) = ∏ k, v k ^ a k) : (p : ℤ) ∣ a j - a i := by
  obtain ⟨m, hm⟩ := exists_const_of_fixed_perm v hrel a (Equiv.swap i j) t ht hfx
  obtain ⟨k₀, hk₀i, hk₀j⟩ := exists_third i j
  have h3 := hm k₀
  rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hk₀i hk₀j, sub_self, zero_sub] at h3
  have hpm : (p : ℤ) ∣ m := (dvd_neg.1 h3)
  have h4 := hm i
  rw [Equiv.symm_swap, Equiv.swap_apply_left] at h4
  have := dvd_add h4 hpm
  simpa using this

theorem card_fixed_le {p : ℕ} [NeZero p] (v : Fin 5 → M)
    (hrel : ∀ a : Fin 5 → ℤ, ∏ i, v i ^ a i = 1 ↔ ∃ m : ℤ, ∀ i, (p : ℤ) ∣ a i - m)
    (hgen : ∀ x : M, ∃ a : Fin 5 → ℤ, x = ∏ i, v i ^ a i)
    (π : Equiv.Perm (Fin 5)) (hπ : ∀ i j : Fin 5, ∃ k : ℕ, (π ^ k) i = j)
    (t : M ≃* M) (ht : ∀ k, t (v k) = v (π k)) :
    Nat.card {u : M // t u = u} ≤ p := by
  classical
  choose a ha using hgen
  let D : {u : M // t u = u} → ZMod p := fun u => ((a u.1 (π.symm 0) - a u.1 0 : ℤ) : ZMod p)
  have hD : Function.Injective D := by
    rintro ⟨u, hu⟩ ⟨w, hw⟩ huw
    simp only [D] at huw
    set d : Fin 5 → ℤ := fun i => a u i - a w i with hd
    have hq : u * w⁻¹ = ∏ i, v i ^ d i := by
      calc u * w⁻¹ = (∏ i, v i ^ a u i) * (∏ i, v i ^ a w i)⁻¹ := by rw [← ha u, ← ha w]
        _ = ∏ i, v i ^ d i := by
          simp only [hd, zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    have hfixq : t (∏ i, v i ^ d i) = ∏ i, v i ^ d i := by
      rw [← hq, map_mul, map_inv, hu, hw]
    obtain ⟨m, hm⟩ := exists_const_of_fixed_perm v hrel d π t ht hfixq
    have h0 : (p : ℤ) ∣ d (π.symm 0) - d 0 := by
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 huw
      have h' : d (π.symm 0) - d 0 = -((a w (π.symm 0) - a w 0) - (a u (π.symm 0) - a u 0)) := by
        simp only [hd]; ring
      rw [h']
      exact dvd_neg.2 this
    have hpm : (p : ℤ) ∣ m := by
      have := dvd_sub h0 (hm 0)
      simpa using this
    have hstep : ∀ j, (p : ℤ) ∣ d (π j) - d j := by
      intro j
      have h1 := dvd_add (hm (π j)) hpm
      rw [Equiv.symm_apply_apply] at h1
      rw [sub_add_cancel] at h1
      have := dvd_neg.2 h1
      simpa using this
    have hall : ∀ k : ℕ, (p : ℤ) ∣ d ((π ^ k) 0) - d 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h1 := hstep ((π ^ k) 0)
        have h2 := dvd_add h1 ih
        have h3 : (π ^ (k + 1)) 0 = π ((π ^ k) 0) := by rw [pow_succ']; rfl
        rw [h3]
        simpa using h2
    have hq1 : ∏ i, v i ^ d i = 1 := by
      refine (hrel d).2 ⟨d 0, fun j => ?_⟩
      obtain ⟨k, hk⟩ := hπ 0 j
      rw [← hk]
      exact hall k
    exact Subtype.ext (mul_inv_eq_one.1 (hq.trans hq1))
  calc Nat.card {u : M // t u = u} ≤ Nat.card (ZMod p) := Nat.card_le_card_of_injective D hD
    _ = p := Nat.card_zmod p

theorem eq_one_of_fixed_swaps {p : ℕ} (v : Fin 5 → M)
    (hrel : ∀ a : Fin 5 → ℤ, ∏ i, v i ^ a i = 1 ↔ ∃ m : ℤ, ∀ i, (p : ℤ) ∣ a i - m)
    (a : Fin 5 → ℤ)
    (hfix : ∀ i j : Fin 5, i ≠ j → ∃ t : M ≃* M, (∀ k, t (v k) = v (Equiv.swap i j k)) ∧
      t (∏ k, v k ^ a k) = ∏ k, v k ^ a k) : ∏ k, v k ^ a k = 1 := by
  refine (hrel a).2 ⟨a 0, fun i => ?_⟩
  by_cases hi : i = 0
  · subst hi; simp
  · obtain ⟨t, ht, hfx⟩ := hfix 0 i (Ne.symm hi)
    exact dvd_of_fixed_swap v hrel a t ht hfx

theorem power_of_commute {p : ℕ} (v : Fin 5 → M)
    (hrel : ∀ a : Fin 5 → ℤ, ∏ i, v i ^ a i = 1 ↔ ∃ m : ℤ, ∀ i, (p : ℤ) ∣ a i - m)
    (hgen : ∀ x : M, ∃ a : Fin 5 → ℤ, x = ∏ i, v i ^ a i) (z : M ≃* M)
    (hz : ∀ σ : Equiv.Perm (Fin 5), ∃ w : M ≃* M, (∀ i, w (v i) = v (σ i)) ∧
      ∀ y, z (w y) = w (z y)) : ∃ k : ℤ, ∀ x : M, z x = x ^ k := by
  classical
  obtain ⟨a, ha⟩ := hgen (z (v 0))
  have hdvd : ∀ i : Fin 5, i ≠ 0 → (p : ℤ) ∣ a i - a 1 := by
    intro i hi
    by_cases h1 : i = 1
    · subst h1; simp
    · obtain ⟨w, hw, hcomm⟩ := hz (Equiv.swap 1 i)
      refine dvd_of_fixed_swap v hrel a w hw ?_
      rw [← ha, ← hcomm, hw, Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 5) ≠ 1 by decide)
        (Ne.symm hi)]
  set d : Fin 5 → ℤ := fun i => if i = 0 then a 0 - a 1 else 0 with hd
  have hprod : ∏ i, v i ^ d i = v 0 ^ (a 0 - a 1) := by
    rw [Finset.prod_eq_single (0 : Fin 5)]
    · simp [hd]
    · intro b _ hb; simp [hd, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hk : z (v 0) = v 0 ^ (a 0 - a 1) := by
    rw [← hprod]
    have h1 : ∏ i, v i ^ (a i - d i) = 1 := by
      refine (hrel _).2 ⟨a 1, fun i => ?_⟩
      by_cases hi : i = 0
      · subst hi; simp [hd]
      · simpa [hd, hi] using hdvd i hi
    simp only [zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib] at h1
    rw [ha]
    exact mul_inv_eq_one.1 h1
  refine ⟨a 0 - a 1, fun x => ?_⟩
  have hv : ∀ i, z (v i) = v i ^ (a 0 - a 1) := by
    intro i
    obtain ⟨w, hw, hcomm⟩ := hz (Equiv.swap 0 i)
    have h1 : w (v 0) = v i := by rw [hw, Equiv.swap_apply_left]
    rw [← h1, hcomm, hk, map_zpow]
  obtain ⟨b, hb⟩ := hgen x
  rw [hb, map_prod]
  simp only [map_zpow, hv]
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← zpow_mul, ← zpow_mul, mul_comm]

end Module

section Refl

variable {G : Type} [Group G] [Finite G]

theorem exists_reflection_swap {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (θ : ↥(reflectionGroup p E) ≃* Equiv.Perm (Fin 5))
    (h4 : ∀ (t : MulAut ↥E) (ht : t ∈ reflectionSet p E),
      ∃ a b : Fin 5, a ≠ b ∧ θ ⟨t, Subgroup.subset_closure ht⟩ = Equiv.swap a b)
    (i j : Fin 5) (hij : i ≠ j) :
    ∃ (t : MulAut ↥E) (ht : t ∈ reflectionSet p E),
      θ ⟨t, Subgroup.subset_closure ht⟩ = Equiv.swap i j := by
  classical
  obtain ⟨t₀, ht₀⟩ : (reflectionSet p E).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hbot : reflectionGroup p E = ⊥ := by
      unfold reflectionGroup
      rw [hne, Subgroup.closure_empty]
    have h2 : ((θ.symm (Equiv.swap 0 1) : ↥(reflectionGroup p E)) : MulAut ↥E) ∈
        (⊥ : Subgroup (MulAut ↥E)) := hbot ▸ (θ.symm (Equiv.swap 0 1)).2
    have h3 : ((θ.symm 1 : ↥(reflectionGroup p E)) : MulAut ↥E) ∈
        (⊥ : Subgroup (MulAut ↥E)) := hbot ▸ (θ.symm 1).2
    rw [Subgroup.mem_bot] at h2 h3
    have h1 : θ.symm (Equiv.swap 0 1) = θ.symm 1 := Subtype.ext (h2.trans h3.symm)
    have := θ.symm.injective h1
    revert this
    decide +kernel
  obtain ⟨a, b, hab, hθ⟩ := h4 t₀ ht₀
  obtain ⟨σ, hσa, hσb⟩ := exists_perm_two a b i j hab hij
  obtain ⟨w, hw, hwg⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E (θ.symm σ).2)
  have hmem : ((θ.symm σ : ↥(reflectionGroup p E)) : MulAut ↥E) * t₀ *
      ((θ.symm σ : ↥(reflectionGroup p E)) : MulAut ↥E)⁻¹ ∈ reflectionSet p E := by
    rw [← hwg]
    exact conj_mem_reflectionSet hp ht₀ hw
  refine ⟨_, hmem, ?_⟩
  have h5 : (⟨((θ.symm σ : ↥(reflectionGroup p E)) : MulAut ↥E) * t₀ *
      ((θ.symm σ : ↥(reflectionGroup p E)) : MulAut ↥E)⁻¹, Subgroup.subset_closure hmem⟩ :
      ↥(reflectionGroup p E)) =
      θ.symm σ * ⟨t₀, Subgroup.subset_closure ht₀⟩ * (θ.symm σ)⁻¹ := rfl
  rw [h5, map_mul, map_mul, map_inv, hθ, MulEquiv.apply_symm_apply, ← Equiv.swap_apply_apply, hσa,
    hσb]

omit [Finite G] in
theorem exists_moved {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G}
    (hexp : ∀ e : ↥E, e ^ p = 1) {t : MulAut ↥E} (ht : orderOf t = 2) :
    ∃ e : ↥E, t (t e * e⁻¹) ≠ t e * e⁻¹ := by
  by_contra hcon
  push Not at hcon
  have ht2 : ∀ e : ↥E, t (t e) = e := fun e => by
    have h1 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    have := congrArg (fun s : MulAut ↥E => s e) h1
    simpa [pow_two] using this
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h1 : ∀ e : ↥E, t e = e := by
    intro e
    have h2 := hcon e
    rw [map_mul, map_inv, ht2] at h2
    have hy1 : (t e * e⁻¹)⁻¹ = t e * e⁻¹ := by rw [mul_inv_rev, inv_inv]; exact h2
    have hy2 : (t e * e⁻¹) ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.2 hy1.symm
    obtain ⟨n, hn⟩ := hodd
    have hy3 : (t e * e⁻¹) = 1 := by
      have h4 := hexp (t e * e⁻¹)
      rw [hn, pow_succ, pow_mul, hy2, one_pow, one_mul] at h4
      exact h4
    exact mul_inv_eq_one.1 hy3
  have : t = 1 := MulEquiv.ext h1
  rw [this, orderOf_one] at ht
  omega

end Refl

section Fix

variable {I : Type*} [Group I]

theorem comm_mul_central {g₁ g₂ z₁ z₂ : I} (h1 : ∀ g, g * z₁ = z₁ * g) (h2 : ∀ g, g * z₂ = z₂ * g) :
    (g₁ * z₁) * (g₂ * z₂) * (g₁ * z₁)⁻¹ * (g₂ * z₂)⁻¹ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by
  have a1 : z₁ * g₂ = g₂ * z₁ := (h1 g₂).symm
  have a2 : z₂ * z₁⁻¹ = z₁⁻¹ * z₂ := (h2 z₁⁻¹).symm
  have a3 : z₂ * g₁⁻¹ = g₁⁻¹ * z₂ := (h2 g₁⁻¹).symm
  calc (g₁ * z₁) * (g₂ * z₂) * (g₁ * z₁)⁻¹ * (g₂ * z₂)⁻¹
      = g₁ * (z₁ * g₂) * (z₂ * z₁⁻¹) * g₁⁻¹ * z₂⁻¹ * g₂⁻¹ := by group
    _ = g₁ * (g₂ * z₁) * (z₁⁻¹ * z₂) * g₁⁻¹ * z₂⁻¹ * g₂⁻¹ := by rw [a1, a2]
    _ = g₁ * g₂ * z₂ * g₁⁻¹ * z₂⁻¹ * g₂⁻¹ := by group
    _ = g₁ * g₂ * (z₂ * g₁⁻¹) * z₂⁻¹ * g₂⁻¹ := by group
    _ = g₁ * g₂ * (g₁⁻¹ * z₂) * z₂⁻¹ * g₂⁻¹ := by rw [a3]
    _ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by group

theorem fixes_of_simple (α : MulAut I) (hα : ∀ k : I, k⁻¹ * α k ∈ Subgroup.center I)
    (K : Subgroup I) (hK : IsSimpleGroup ↥K) (hnc : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a) :
    ∀ k ∈ K, α k = k := by
  classical
  have hc : ∀ k g : I, g * (k⁻¹ * α k) = (k⁻¹ * α k) * g := fun k g =>
    Subgroup.mem_center_iff.1 (hα k) g
  let F : Subgroup I := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id I)
  have hF : ∀ g, g ∈ F ↔ α g = g := fun g => Iff.rfl
  have hcomm : ∀ a b : I, a * b * a⁻¹ * b⁻¹ ∈ F := by
    intro a b
    rw [hF, map_mul, map_mul, map_mul, map_inv, map_inv]
    obtain ⟨ca, hca, hαa⟩ : ∃ ca : I, (∀ g, g * ca = ca * g) ∧ α a = a * ca :=
      ⟨a⁻¹ * α a, hc a, by group⟩
    obtain ⟨cb, hcb, hαb⟩ : ∃ cb : I, (∀ g, g * cb = cb * g) ∧ α b = b * cb :=
      ⟨b⁻¹ * α b, hc b, by group⟩
    rw [hαa, hαb]
    exact comm_mul_central hca hcb
  have hN : (F.subgroupOf K).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf, hF] at hn ⊢
    obtain ⟨ck, hck, hαk⟩ : ∃ ck : I, (∀ g, g * ck = ck * g) ∧ α (k : I) = (k : I) * ck :=
      ⟨(k : I)⁻¹ * α (k : I), hc k, by group⟩
    have hn' : α (n : I) = (n : I) := hn
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hαk, hn']
    calc (k : I) * ck * (n : I) * ((k : I) * ck)⁻¹
        = (k : I) * (ck * (n : I)) * ck⁻¹ * (k : I)⁻¹ := by group
      _ = (k : I) * ((n : I) * ck) * ck⁻¹ * (k : I)⁻¹ := by rw [← hck (n : I)]
      _ = (k : I) * (n : I) * (k : I)⁻¹ := by group
  rcases hK.eq_bot_or_eq_top_of_normal (F.subgroupOf K) with h | h
  · exfalso
    obtain ⟨a, haK, b, hbK, hab⟩ := hnc
    have h1 : (⟨a * b * a⁻¹ * b⁻¹, K.mul_mem (K.mul_mem (K.mul_mem haK hbK) (K.inv_mem haK))
        (K.inv_mem hbK)⟩ : ↥K) ∈ F.subgroupOf K := Subgroup.mem_subgroupOf.2 (hcomm a b)
    rw [h, Subgroup.mem_bot] at h1
    apply hab
    have h2 : a * b * a⁻¹ * b⁻¹ = 1 := congrArg Subtype.val h1
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h2, one_mul]
  · intro k hk
    have h1 : (⟨k, hk⟩ : ↥K) ∈ F.subgroupOf K := by rw [h]; trivial
    exact (hF k).1 (Subgroup.mem_subgroupOf.1 h1)

end Fix

section Faithful

variable {G : Type} [Group G]

theorem act_trivial_aux {I : Subgroup G} {P : Type*} [Group P]
    (e : ↥I ⧸ Subgroup.center ↥I ≃* P) {x : G} (hx : x ∈ Subgroup.normalizer (I : Set G))
    (h : U5K.U5Act I e ⟨x, hx⟩ = 1) :
    ∀ k : ↥I, k⁻¹ * I.normalizerMonoidHom ⟨x, hx⟩ k ∈ Subgroup.center ↥I := by
  intro k
  have h1 := U5K.U5Act_apply I e ⟨x, hx⟩ k
  rw [h, MulAut.one_apply] at h1
  exact QuotientGroup.eq.1 (e.injective h1)

end Faithful

section Main

variable {G : Type} [Group G] [Finite G]

theorem u5_faithful_of (hMod : KFU5Mod) (hAt : KFU5At) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec15Hyp G p A c L E → Sec12Facts G p A c L E →
      Outcome152Five p E A (lieGenerated p E) →
      ∀ (f : ℕ) (e : ↥(lieGenerated p E) ⧸ Subgroup.center ↥(lieGenerated p E) ≃* projSU 5 2 f)
        (x : G) (hx : x ∈ lieNormalizer p E), x ∈ E →
          U5K.U5Act (lieGenerated p E) e ⟨x, hx⟩ = 1 → x = 1 := by
  intro G _ _ p A c L E h15 hF hout f e x hx hxE hact
  classical
  have h := h15.h12
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := h.three_lt; omega
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => hEel.is_comm.comm a b
  have hexp : ∀ e : ↥E, e ^ p = 1 := fun e =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p ↥E) e
  let _ : CommGroup ↥E := { (inferInstance : Group ↥E) with mul_comm := hEc }
  obtain ⟨θ, v, hperm, hgen, hrel, hrefl⟩ := hMod G p A c L E h15 hF hout
  obtain ⟨f₀, hf₀, hpf₀, ⟨e₀⟩, -⟩ := id hout
  have hx' : x ∈ Subgroup.normalizer (lieGenerated p E : Set G) := hx
  have hα := act_trivial_aux e hx' hact
  have hfixt : ∀ t ∈ reflectionSet p E, t ⟨x, hxE⟩ = ⟨x, hxE⟩ := by
    intro t ht
    obtain ⟨hne, hmod, hcent, hmoved, k, hk, hkK, hkt⟩ :=
      hAt G p A c L E f₀ h15 hF hout hf₀ hpf₀ ⟨e₀⟩ t ht
    have hKI : kZero p E t ≤ lieGenerated p E :=
      le_sSup ⟨t, ht, (isKt_iff_of_nonexceptional hne).2 rfl⟩
    have hKs : IsSimpleGroup ↥(kZero p E t) :=
      (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 f₀ hmod).2
    obtain ⟨e', he'⟩ := exists_moved hp hp2 hexp ht.1.1
    have hyK : ((t e' * e'⁻¹ : ↥E) : G) ∈ kZero p E t :=
      hmoved ⟨t e' * e'⁻¹, Subgroup.subset_closure ⟨e', rfl⟩, rfl⟩
    have hkmove : k * ((t e' * e'⁻¹ : ↥E) : G) * k⁻¹ ≠ ((t e' * e'⁻¹ : ↥E) : G) := by
      have h1 := Equivariance.coe_conjAut hk (t e' * e'⁻¹)
      have h2 : conjAut E k hk = t := hkt
      rw [h2] at h1
      rw [← h1]
      exact fun h => he' (Subtype.ext h)
    have hnc : ∃ a ∈ (kZero p E t).subgroupOf (lieGenerated p E),
        ∃ b ∈ (kZero p E t).subgroupOf (lieGenerated p E), a * b ≠ b * a := by
      refine ⟨⟨k, hKI hkK⟩, Subgroup.mem_subgroupOf.2 hkK,
        ⟨((t e' * e'⁻¹ : ↥E) : G), hKI hyK⟩, Subgroup.mem_subgroupOf.2 hyK, fun hcomm => ?_⟩
      have h1 : k * ((t e' * e'⁻¹ : ↥E) : G) = ((t e' * e'⁻¹ : ↥E) : G) * k :=
        congrArg Subtype.val hcomm
      exact hkmove (by rw [h1]; group)
    have hKs' : IsSimpleGroup ↥((kZero p E t).subgroupOf (lieGenerated p E)) :=
      (Subgroup.subgroupOfEquivOfLe hKI).isSimpleGroup
    have hfix := fixes_of_simple ((lieGenerated p E).normalizerMonoidHom ⟨x, hx'⟩) hα
      ((kZero p E t).subgroupOf (lieGenerated p E)) hKs' hnc
    have hcentr : ∀ k₁ ∈ kZero p E t, x * k₁ * x⁻¹ = k₁ := by
      intro k₁ hk₁
      have h1 := hfix ⟨k₁, hKI hk₁⟩ (Subgroup.mem_subgroupOf.2 hk₁)
      have h2 := congrArg Subtype.val h1
      rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
    have hxc : x ∈ E ⊓ Subgroup.centralizer (kZero p E t : Set G) := by
      refine ⟨hxE, Subgroup.mem_centralizer_iff.2 fun k₁ hk₁ => ?_⟩
      calc k₁ * x = (x * k₁ * x⁻¹) * x := by rw [hcentr k₁ hk₁]
        _ = x * k₁ := by group
    rw [hcent] at hxc
    obtain ⟨y', hy', hyx⟩ := hxc
    have hy'eq : y' = ⟨x, hxE⟩ := Subtype.ext hyx
    rw [hy'eq] at hy'
    exact hy'
  obtain ⟨a, ha₀⟩ := hgen ⟨x, hxE⟩
  have ha : (⟨x, hxE⟩ : ↥E) = ∏ i, v i ^ a i := by rw [Fin.prod_univ_five]; exact ha₀
  have hrel' : ∀ a : Fin 5 → ℤ, ∏ i, v i ^ a i = 1 ↔ ∃ m : ℤ, ∀ i, (p : ℤ) ∣ a i - m :=
    fun a => by rw [Fin.prod_univ_five]; exact hrel a
  have h1 : ∏ k, v k ^ a k = 1 := by
    refine eq_one_of_fixed_swaps v hrel' a (fun i j hij => ?_)
    obtain ⟨t, ht, hθ⟩ := exists_reflection_swap hp θ hrefl i j hij
    refine ⟨t, fun k => ?_, ?_⟩
    · have := hperm ⟨t, Subgroup.subset_closure ht⟩ k
      rw [hθ] at this
      exact this
    · rw [← ha]
      exact hfixt t ht
  rw [← ha] at h1
  exact congrArg Subtype.val h1

end Main

end Sec153

end CFSG.RankThree.PartOne
