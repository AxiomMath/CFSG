module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113NA5K

public section

namespace CFSG.Quasithin.H13.D7Pos

open Equiv Equiv.Perm CFSG.Quasithin.G6

@[expose] def w0 (j : Fin 7) : PermMod 7 := Multiplicative.ofAdd (Pi.single 0 1 + Pi.single j 1)

theorem w0_apply : ∀ j i : Fin 7, j ≠ 0 →
    (Multiplicative.toAdd (w0 j) i = 1 ↔ i = 0 ∨ i = j) := by
  decide +kernel

theorem w0_mem (j : Fin 7) : w0 j ∈ coreMod 7 := by
  rw [mem_coreMod]
  revert j
  decide +kernel

@[expose] def v0 (j : Fin 7) : ↥(coreMod 7) := ⟨w0 j, w0_mem j⟩

theorem eq_one_of_forall_coreAct {ρ : Perm (Fin 7)} (h : ∀ v, coreAct 7 ρ v = v) : ρ = 1 := by
  have key : ∀ j : Fin 7, j ≠ 0 → ∀ y : Fin 7,
      (Multiplicative.toAdd (w0 j) (ρ⁻¹ y) = Multiplicative.toAdd (w0 j) y) := by
    intro j _ y
    have h1 := congrArg (fun v : ↥(coreMod 7) => Multiplicative.toAdd (v : PermMod 7) y) (h (v0 j))
    exact h1
  have hmem : ∀ j : Fin 7, j ≠ 0 → ∀ y : Fin 7, (y = 0 ∨ y = j) → (ρ⁻¹ y = 0 ∨ ρ⁻¹ y = j) := by
    intro j hj y hy
    rw [← w0_apply j _ hj, key j hj y, w0_apply j _ hj]
    exact hy
  have h0 : ρ⁻¹ 0 = 0 := by
    rcases hmem 1 (by decide) 0 (Or.inl rfl) with h1 | h1
    · exact h1
    · rcases hmem 2 (by decide) 0 (Or.inl rfl) with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) (by decide)
  have hinv : ρ⁻¹ = 1 := by
    refine Equiv.ext fun j => ?_
    rw [Perm.one_apply]
    by_cases hj : j = 0
    · rw [hj, h0]
    · rcases hmem j hj j (Or.inr rfl) with h1 | h1
      · exact absurd (ρ⁻¹.injective (h1.trans h0.symm)) hj
      · exact h1
  rw [← inv_inv ρ, hinv, inv_one]

theorem coreAct_injective : Function.Injective (coreAct 7) := by
  intro σ τ h
  have h1 : ∀ v, coreAct 7 (σ⁻¹ * τ) v = v := by
    intro v
    rw [map_mul, MulAut.mul_apply, ← h, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      MulAut.one_apply]
  exact inv_mul_eq_one.mp (eq_one_of_forall_coreAct h1)

@[expose] def stabL : List (Perm (Fin 7)) :=
  [swap 2 3 * swap 3 4, swap 2 3 * swap 3 4 * swap 4 5 * swap 5 6, swap 0 1 * swap 2 3]

@[expose] def tauL : Fin 7 → Perm (Fin 7) :=
  ![1, 1, swap 1 2 * swap 2 3, swap 1 3 * swap 3 4, swap 1 4 * swap 4 5, swap 1 5 * swap 5 6,
    swap 1 6 * swap 6 2]

theorem schur_check :
    stabL.all (fun σ => decide (sign σ = 1 ∧ ∀ i, Multiplicative.toAdd (w0 1) (σ⁻¹ i) =
      Multiplicative.toAdd (w0 1) i)) &&
    (List.finRange 7).all (fun j => decide (sign (tauL j) = 1 ∧ (j ≠ 0 → ∀ i,
      Multiplicative.toAdd (w0 1) ((tauL j)⁻¹ i) = Multiplicative.toAdd (w0 j) i))) = true := by
  decide +kernel

theorem fixed_stab_check : ∀ x : Fin 7 → ZMod 2, ∑ i, x i = 0 →
    (stabL.all fun σ => (List.finRange 7).all fun i => decide (x (σ⁻¹ i) = x i)) = true →
      x = 0 ∨ x = Pi.single 0 1 + Pi.single 1 1 := by
  decide +kernel

theorem val_nsmul_eq (a : ZMod 2) (w : Fin 7 → ZMod 2) : a.val • w = a • w := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]

theorem decomp_check : ∀ x : Fin 7 → ZMod 2, ∑ i, x i = 0 →
    x = x 1 • (Pi.single 0 1 + Pi.single 1 1) + x 2 • (Pi.single 0 1 + Pi.single 2 1) +
      x 3 • (Pi.single 0 1 + Pi.single 3 1) + x 4 • (Pi.single 0 1 + Pi.single 4 1) +
      x 5 • (Pi.single 0 1 + Pi.single 5 1) + x 6 • (Pi.single 0 1 + Pi.single 6 1) := by
  decide +kernel

theorem eq_of_commute_coreAct (f : ↥(coreMod 7) →* ↥(coreMod 7)) (hf : Function.Injective f)
    (hc : ∀ σ ∈ alternatingGroup (Fin 7), ∀ v, f (coreAct 7 σ v) = coreAct 7 σ (f v)) :
    ∀ v, f v = v := by
  have hck := schur_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq] at hck
  obtain ⟨hstab, htau⟩ := hck
  have hfix : ∀ σ ∈ stabL, coreAct 7 σ (v0 1) = v0 1 := by
    intro σ hσ
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    exact (hstab σ hσ).2 i
  have hf1 : f (v0 1) = v0 1 := by
    have h1 : ∀ σ ∈ stabL, ∀ i, Multiplicative.toAdd ((f (v0 1) : ↥(coreMod 7)) : PermMod 7)
        (σ⁻¹ i) = Multiplicative.toAdd ((f (v0 1) : ↥(coreMod 7)) : PermMod 7) i := by
      intro σ hσ i
      have h2 : coreAct 7 σ (f (v0 1)) = f (v0 1) := by
        rw [← hc σ (Equiv.Perm.mem_alternatingGroup.mpr (hstab σ hσ).1), hfix σ hσ]
      exact congrArg (fun v : ↥(coreMod 7) => Multiplicative.toAdd (v : PermMod 7) i) h2
    have h1' : (stabL.all fun σ => (List.finRange 7).all fun i =>
        decide (Multiplicative.toAdd ((f (v0 1) : ↥(coreMod 7)) : PermMod 7) (σ⁻¹ i) =
          Multiplicative.toAdd ((f (v0 1) : ↥(coreMod 7)) : PermMod 7) i)) = true := by
      simp only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]
      exact h1
    rcases fixed_stab_check _ (f (v0 1)).2 h1' with h0 | h0
    · exfalso
      have h3 : f (v0 1) = 1 := Subtype.ext (Multiplicative.toAdd.injective (by rw [h0]; rfl))
      rw [← map_one f] at h3
      have h4 := hf h3
      have h5 := congrArg (fun v : ↥(coreMod 7) => Multiplicative.toAdd (v : PermMod 7) 0) h4
      revert h5
      decide +kernel
    · exact Subtype.ext (Multiplicative.toAdd.injective h0)
  have hfj : ∀ j : Fin 7, j ≠ 0 → f (v0 j) = v0 j := by
    intro j hj
    have hτ : coreAct 7 (tauL j) (v0 1) = v0 j := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      funext i
      exact (htau j).2 hj i
    rw [← hτ, hc _ (Equiv.Perm.mem_alternatingGroup.mpr (htau j).1), hf1]
  intro v
  have hd : v = v0 1 ^ (Multiplicative.toAdd (v : PermMod 7) 1).val *
      v0 2 ^ (Multiplicative.toAdd (v : PermMod 7) 2).val *
      v0 3 ^ (Multiplicative.toAdd (v : PermMod 7) 3).val *
      v0 4 ^ (Multiplicative.toAdd (v : PermMod 7) 4).val *
      v0 5 ^ (Multiplicative.toAdd (v : PermMod 7) 5).val *
      v0 6 ^ (Multiplicative.toAdd (v : PermMod 7) 6).val := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow, toAdd_mul, toAdd_pow, v0, w0,
      toAdd_ofAdd, val_nsmul_eq]
    exact decomp_check _ (mem_coreMod.mp v.2)
  rw [hd]
  simp only [map_mul, map_pow, hf1, hfj 2 (by decide), hfj 3 (by decide), hfj 4 (by decide),
    hfj 5 (by decide), hfj 6 (by decide)]

theorem p0L_fix_check : A7Std.p0L.all (fun q => decide (q * q = 1) ||
    (List.finRange 7).all fun i => !decide (q i = i) || decide (i = 0)) = true := by
  decide +kernel

theorem zero_of_normalizes {π : Perm (Fin 7)}
    (hN : ∀ p ∈ A7Std.p0L, π * p * π⁻¹ ∈ A7Std.p0L) : π 0 = 0 := by
  have ha : A7Std.p0a ∈ A7Std.p0L := by simp [A7Std.p0L]
  have h1 := List.all_eq_true.mp p0L_fix_check _ (hN _ ha)
  rw [Bool.or_eq_true, decide_eq_true_eq] at h1
  rcases h1 with h1 | h1
  · exfalso
    have h2 : A7Std.p0a * A7Std.p0a = 1 := by
      apply (MulAut.conj π).injective
      rw [map_one, MulAut.conj_apply]
      calc π * (A7Std.p0a * A7Std.p0a) * π⁻¹ =
          π * A7Std.p0a * π⁻¹ * (π * A7Std.p0a * π⁻¹) := by group
        _ = 1 := h1
    revert h2
    decide +kernel
  · have h2 := List.all_eq_true.mp h1 (π 0) (List.mem_finRange _)
    rw [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at h2
    rcases h2 with h2 | h2
    · exfalso
      apply h2
      rw [Perm.mul_apply, Perm.mul_apply, ← Perm.mul_apply π⁻¹, inv_mul_cancel, Perm.one_apply,
        A7Std.p0L_zero ha]
    · exact h2

@[expose] def invL : List (Perm (Fin 7)) :=
  [1, swap 1 3, swap 2 4, swap 1 3 * swap 2 4, swap 1 2 * swap 3 4, swap 1 4 * swap 2 3]

@[expose] def l4 : List (Fin 7) := [1, 2, 3, 4]

theorem invL_check : ∀ a ∈ l4, ∀ b ∈ l4, ∀ c ∈ l4, ∀ d ∈ l4,
    ![0, a, b, c, d, 5, 6] a = 1 → ![0, a, b, c, d, 5, 6] b = 2 →
    ![0, a, b, c, d, 5, 6] c = 3 → ![0, a, b, c, d, 5, 6] d = 4 →
    swap a b * swap b c * swap c d * swap 5 6 ∈ A7Std.p0L → swap a c * swap 5 6 ∈ A7Std.p0L →
    invL.any (fun τ => (List.finRange 7).all fun i => decide (τ i = ![0, a, b, c, d, 5, 6] i)) =
      true := by
  decide +kernel

theorem mem_invL {σ : Perm (Fin 7)} (h0 : σ 0 = 0) (h5 : σ 5 = 5) (h6 : σ 6 = 6)
    (hsq : σ * σ = 1) (hN : ∀ p ∈ A7Std.p0L, σ * p * σ⁻¹ ∈ A7Std.p0L) : σ ∈ invL := by
  have hinj : ∀ i j : Fin 7, i ≠ j → σ i ≠ σ j := fun i j hij h => hij (σ.injective h)
  have h14 : ∀ i ∈ l4, σ i ∈ l4 := by
    intro i hi
    have hi' : i ≠ 0 ∧ i ≠ 5 ∧ i ≠ 6 := by
      simp only [l4, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide
    have e0 := hinj i 0 hi'.1
    have e5 := hinj i 5 hi'.2.1
    have e6 := hinj i 6 hi'.2.2
    rw [h0] at e0
    rw [h5] at e5
    rw [h6] at e6
    revert e0 e5 e6
    generalize σ i = a
    revert a
    decide
  have hf : ∀ i, σ i = ![0, σ 1, σ 2, σ 3, σ 4, 5, 6] i := by
    intro i
    fin_cases i <;> simp [h0, h5, h6]
  have hinv : ∀ i, σ (σ i) = i := fun i => by rw [← Perm.mul_apply, hsq, Perm.one_apply]
  have hc : ∀ x y : Fin 7, σ * swap x y * σ⁻¹ = swap (σ x) (σ y) :=
    fun x y => (swap_apply_apply σ x y).symm
  have hpa : σ * A7Std.p0a * σ⁻¹ =
      swap (σ 1) (σ 2) * swap (σ 2) (σ 3) * swap (σ 3) (σ 4) * swap (σ 5) (σ 6) := by
    rw [← hc, ← hc, ← hc, ← hc, A7Std.p0a]
    group
  have hpb : σ * A7Std.p0b * σ⁻¹ = swap (σ 1) (σ 3) * swap (σ 5) (σ 6) := by
    rw [← hc, ← hc, A7Std.p0b]
    group
  rw [h5, h6] at hpa hpb
  have ha := hN _ (show A7Std.p0a ∈ A7Std.p0L by simp [A7Std.p0L])
  have hb := hN _ (show A7Std.p0b ∈ A7Std.p0L by simp [A7Std.p0L])
  rw [hpa] at ha
  rw [hpb] at hb
  have hv : ∀ i, ![0, σ 1, σ 2, σ 3, σ 4, 5, 6] (σ i) = i := fun i => by rw [← hf, hinv]
  have hck := invL_check _ (h14 1 (by decide)) _ (h14 2 (by decide)) _ (h14 3 (by decide)) _
    (h14 4 (by decide)) (hv 1) (hv 2) (hv 3) (hv 4) ha hb
  obtain ⟨τ, hτ, hτi⟩ := List.any_eq_true.mp hck
  have hστ : σ = τ := by
    refine Equiv.ext fun i => ?_
    have h1 := List.all_eq_true.mp hτi i (List.mem_finRange i)
    rw [decide_eq_true_eq] at h1
    rw [hf i, h1]
  rw [hστ]
  exact hτ

theorem mem_eL_or_of_mem_invL {σ : Perm (Fin 7)} (hσ : σ ∈ invL) :
    σ ∈ A7Four.eL ∨ σ = swap 1 3 ∨ σ = swap 2 4 := by
  simp only [invL, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

@[expose] def gam13 : Perm (Fin 7) := swap 1 5 * swap 3 6

@[expose] def gam24 : Perm (Fin 7) := swap 2 5 * swap 4 6

theorem exists_gam {s : Perm (Fin 7)} (hs : s = swap 1 3 ∨ s = swap 2 4) :
    ∃ γ : Perm (Fin 7), sign γ = 1 ∧ γ * s * γ⁻¹ = swap 5 6 ∧
      ∀ σ ∈ invL, σ * s = s * σ →
        γ * σ * γ⁻¹ ∈ A7Std.p0L ∨ s * (γ * σ * γ⁻¹) ∈ A7Std.p0L := by
  rcases hs with rfl | rfl
  · refine ⟨gam13, by decide +kernel, by decide +kernel, fun σ hσ hcomm => ?_⟩
    simp only [invL, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | (exfalso; revert hcomm; decide +kernel)
        | decide +kernel
  · refine ⟨gam24, by decide +kernel, by decide +kernel, fun σ hσ hcomm => ?_⟩
    simp only [invL, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | (exfalso; revert hcomm; decide +kernel)
        | decide +kernel

theorem card_orbits_le_five {P : Subgroup (Perm (Fin 7))} (hP : IsPGroup 2 P)
    (hPA : P ≤ alternatingGroup (Fin 7)) (h2 : 2 ≤ Nat.card P) :
    Nat.card (Quotient (MulAction.orbitRel P (Fin 7))) ≤ 5 := by
  classical
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group P (Fin 7)
  have hle : ∀ g : P, Fintype.card (MulAction.fixedBy (Fin 7) g) ≤
      3 + if g = 1 then 4 else 0 := by
    intro g
    rw [← Nat.card_eq_fintype_card, Vol2.Ch10.SecB.C11AmS.K8.card_fixedBy_eq]
    split_ifs with hg
    · subst hg
      simp
    · obtain ⟨k, hk⟩ := hP g
      have hk' : (g : Perm (Fin 7)) ^ 2 ^ k = 1 := by
        rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]
      have hne : (g : Perm (Fin 7)) ≠ 1 := fun h => hg (Subtype.ext h)
      have := Vol2.Ch10.SecB.C11AmS.K8.card_compl_support_le (hPA g.2) hne hk'
      omega
  have hsum : ∑ g : P, Fintype.card (MulAction.fixedBy (Fin 7) g) ≤
      3 * Fintype.card P + 4 := by
    calc ∑ g : P, Fintype.card (MulAction.fixedBy (Fin 7) g)
        ≤ ∑ g : P, (3 + if g = 1 then 4 else 0) := Finset.sum_le_sum fun g _ => hle g
      _ = 3 * Fintype.card P + 4 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
          Finset.sum_ite_eq']
        simp [mul_comm]
  rw [hB] at hsum
  rw [Nat.card_eq_fintype_card] at h2 ⊢
  by_contra hlt
  have h6 : 6 * Fintype.card P ≤
      Fintype.card (Quotient (MulAction.orbitRel P (Fin 7))) * Fintype.card P :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem card_fixVec_le_thirtyTwo {P : Subgroup (Perm (Fin 7))} (hP : IsPGroup 2 P)
    (hPA : P ≤ alternatingGroup (Fin 7)) (h2 : 2 ≤ Nat.card P) :
    Nat.card {x : Fin 7 → ZMod 2 // ∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i} ≤ 32 := by
  have hΩ := card_orbits_le_five hP hPA h2
  let f : {x : Fin 7 → ZMod 2 // ∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i} →
      (Quotient (MulAction.orbitRel P (Fin 7)) → ZMod 2) := fun x q => x.1 q.out
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hq : (Quotient.mk (MulAction.orbitRel P (Fin 7)) i).out ∈ MulAction.orbit P i :=
      MulAction.orbitRel_apply.1 (Quotient.exact (Quotient.out_eq _))
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hq
    have key : ∀ z : {x : Fin 7 → ZMod 2 // ∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i},
        f z (Quotient.mk _ i) = z.1 i := by
      intro z
      show z.1 (Quotient.mk (MulAction.orbitRel P (Fin 7)) i).out = z.1 i
      rw [← hg, Subgroup.smul_def, Perm.smul_def]
      have := z.2 (g : Perm (Fin 7))⁻¹ (P.inv_mem g.2) i
      rwa [inv_inv] at this
    rw [← key x, ← key y, hxy]
  calc Nat.card {x : Fin 7 → ZMod 2 // ∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i}
      ≤ Nat.card (Quotient (MulAction.orbitRel P (Fin 7)) → ZMod 2) :=
        Nat.card_le_card_of_injective f hf
    _ = 2 ^ Nat.card (Quotient (MulAction.orbitRel P (Fin 7))) := by
        rw [Nat.card_fun, Nat.card_zmod]
    _ ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hΩ
    _ = 32 := by norm_num

theorem card_fixVec_even_le_sixteen {P : Subgroup (Perm (Fin 7))} (hP : IsPGroup 2 P)
    (hPA : P ≤ alternatingGroup (Fin 7)) (h2 : 2 ≤ Nat.card P) :
    Nat.card {x : Fin 7 → ZMod 2 // (∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i) ∧ ∑ i, x i = 0} ≤ 16 := by
  have hF := card_fixVec_le_thirtyTwo hP hPA h2
  let E := {x : Fin 7 → ZMod 2 // (∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i) ∧ ∑ i, x i = 0}
  let F := {x : Fin 7 → ZMod 2 // ∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i}
  have hodd : ∀ y : E, ∑ i, (y.1 + 1) i = 1 := by
    intro y
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, y.2.2]
    simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    decide
  let g : E ⊕ E → F := Sum.elim (fun x => ⟨x.1, x.2.1⟩)
    (fun x => ⟨x.1 + 1, fun σ hσ i => by
      simp only [Pi.add_apply, Pi.one_apply]
      rw [x.2.1 σ hσ i]⟩)
  have hg : Function.Injective g := by
    rintro (x | x) (y | y) h
    · have h1 := congrArg Subtype.val h
      exact congrArg Sum.inl (Subtype.ext h1)
    · exfalso
      have h1 : x.1 = y.1 + 1 := congrArg Subtype.val h
      have h2 := hodd y
      rw [← h1, x.2.2] at h2
      exact absurd h2 (by decide)
    · exfalso
      have h1 : x.1 + 1 = y.1 := congrArg Subtype.val h
      have h2 := hodd x
      rw [h1, y.2.2] at h2
      exact absurd h2 (by decide)
    · have h1 : x.1 + 1 = y.1 + 1 := congrArg Subtype.val h
      exact congrArg Sum.inr (Subtype.ext (add_right_cancel h1))
  have h := Nat.card_le_card_of_injective g hg
  rw [Nat.card_sum] at h
  change Nat.card F ≤ 32 at hF
  change Nat.card E ≤ 16
  omega

theorem card_mul_card_fixVec_le {P : Subgroup (Perm (Fin 7))}
    (hPE : ∀ σ ∈ P, σ ∈ A7Four.eL) (hP1 : P ≠ ⊥) :
    Nat.card P * Nat.card {x : Fin 7 → ZMod 2 // (∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i) ∧
      ∑ i, x i = 0} ≤ 32 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 P := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_one, pow_two, Subgroup.coe_one]
    exact A7Four.eL_sq (hPE g g.2)
  have hPA : P ≤ alternatingGroup (Fin 7) := fun σ hσ =>
    Equiv.Perm.mem_alternatingGroup.mpr (A7Std.p0L_sign (A7Four.eL_p0L (hPE σ hσ)))
  have hP4 : Nat.card P ≤ 4 := by
    have h1 : (P : Set (Perm (Fin 7))) ⊆ (A7Four.eL.toFinset : Set (Perm (Fin 7))) :=
      fun σ hσ => by
        rw [Finset.mem_coe, List.mem_toFinset]
        exact hPE σ hσ
    have h2 := Nat.card_mono (Finset.finite_toSet _) h1
    rw [Nat.card_coe_set_eq ((A7Four.eL.toFinset : Finset (Perm (Fin 7))) : Set (Perm (Fin 7))),
      Set.ncard_coe_finset] at h2
    have hnd : A7Four.eL.Nodup := by decide +kernel
    rw [List.toFinset_card_of_nodup hnd] at h2
    exact h2
  have h2 : 2 ≤ Nat.card P := by
    have := (Subgroup.one_lt_card_iff_ne_bot P).mpr hP1
    omega
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  have hk3 : k < 3 := by
    by_contra hc
    have h8 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 3 ≤ k by omega)
    omega
  interval_cases k
  · omega
  · rw [hk]
    have := card_fixVec_even_le_sixteen hP2 hPA h2
    omega
  · rw [hk]
    have := Vol2.Ch10.SecB.C11AmS.K8.card_fixVec_even_le hP2 hPA (by omega)
    omega

end CFSG.Quasithin.H13.D7Pos

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

section Acts

variable {G : Type} [Group G] {Y U : Subgroup G} (hYU : Y ≤ Subgroup.normalizer (U : Set G))
  (β : ↥U ≃* ↥(G6.coreMod 7))

theorem acts_mul {y z : ↥Y} {σ τ : Perm (Fin 7)}
    (hy : ∀ u, β (A7ZK.conjAut hYU y u) = G6.coreAct 7 σ (β u))
    (hz : ∀ u, β (A7ZK.conjAut hYU z u) = G6.coreAct 7 τ (β u)) (u : ↥U) :
    β (A7ZK.conjAut hYU (y * z) u) = G6.coreAct 7 (σ * τ) (β u) := by
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hy, hz]

theorem acts_inv {y : ↥Y} {σ : Perm (Fin 7)}
    (hy : ∀ u, β (A7ZK.conjAut hYU y u) = G6.coreAct 7 σ (β u)) (u : ↥U) :
    β (A7ZK.conjAut hYU y⁻¹ u) = G6.coreAct 7 σ⁻¹ (β u) := by
  have h := hy (A7ZK.conjAut hYU y⁻¹ u)
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h
  rw [h, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem acts_of_coe_eq {y y' : ↥Y} (h : (y : G) = y') {σ : Perm (Fin 7)}
    (hy : ∀ u, β (A7ZK.conjAut hYU y u) = G6.coreAct 7 σ (β u)) :
    ∀ u, β (A7ZK.conjAut hYU y' u) = G6.coreAct 7 σ (β u) := by
  obtain rfl : y = y' := Subtype.ext h
  exact hy

theorem acts_unique {y : ↥Y} {σ τ : Perm (Fin 7)}
    (hσ : ∀ u, β (A7ZK.conjAut hYU y u) = G6.coreAct 7 σ (β u))
    (hτ : ∀ u, β (A7ZK.conjAut hYU y u) = G6.coreAct 7 τ (β u)) : σ = τ := by
  apply D7Pos.coreAct_injective
  refine MulEquiv.ext fun v => ?_
  obtain ⟨u, rfl⟩ := β.surjective v
  rw [← hσ, ← hτ]

theorem mem_centralizer_of_acts_one {y : ↥Y}
    (hy : ∀ u, β (A7ZK.conjAut hYU y u) = G6.coreAct 7 1 (β u)) :
    (y : G) ∈ Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have h := hy ⟨u, hu⟩
  rw [map_one, MulAut.one_apply] at h
  have h2 : (y : G) * u * (y : G)⁻¹ = u := congrArg Subtype.val (β.injective h)
  calc u * (y : G) = ((y : G) * u * (y : G)⁻¹) * y := by rw [h2]
    _ = y * u := by group

end Acts

section SixSide

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem A7Pack.exists_perm_of_mem {T K Kh W : Subgroup G}
    {e : O2Q Kh ≃* alternatingGroup (Fin 7)} (pk : A7Pack T K Kh W e)
    {β : ↥⁅W, Kh⁆ ≃* ↥(G6.coreMod 7)}
    (hβ : ∀ (y : ↥Kh) (u : ↥⁅W, Kh⁆), (β (A7ZK.conjAut pk.le_normalizer y u) : G6.PermMod 7) =
      G6.permAct 7 ((e (QuotientGroup.mk y) : alternatingGroup (Fin 7)) : Perm (Fin 7)) (β u))
    {t : G} (ht : t ∈ T) :
    ∃ π : Perm (Fin 7), (∀ u : ↥⁅W, Kh⁆,
        β (A7ZK.conjAut pk.T_le_normalizer ⟨t, ht⟩ u) = G6.coreAct 7 π (β u)) ∧
      ∀ p ∈ A7Std.p0L, π * p * π⁻¹ ∈ A7Std.p0L := by
  set tN : ↥(Subgroup.normalizer (Kh : Set G)) := ⟨t, pk.T_le ht⟩ with htN
  set φ : alternatingGroup (Fin 7) ≃* alternatingGroup (Fin 7) :=
    e.symm.trans ((quotConjAut Kh tN).trans e) with hφ
  obtain ⟨π, hπ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).2 φ
  have hconj : ∀ k : ↥Kh, ((e (QuotientGroup.mk ⟨t * k * t⁻¹,
      (Subgroup.mem_normalizer_iff.mp (pk.T_le ht) k).mp k.2⟩) : alternatingGroup (Fin 7)) :
        Perm (Fin 7)) = π * (e (QuotientGroup.mk k) : Perm (Fin 7)) * π⁻¹ := by
    intro k
    have h1 : φ (e (QuotientGroup.mk k)) = e (QuotientGroup.mk ⟨t * k * t⁻¹,
        (Subgroup.mem_normalizer_iff.mp (pk.T_le ht) k).mp k.2⟩) := by
      rw [hφ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]
      rfl
    rw [← h1, ← hπ, MulAut.conjNormal_apply]
  set f : ↥(G6.coreMod 7) →* ↥(G6.coreMod 7) :=
    (G6.coreAct 7 π⁻¹).toMonoidHom.comp ((β.toMonoidHom.comp
      (A7ZK.conjAut pk.T_le_normalizer ⟨t, ht⟩).toMonoidHom).comp β.symm.toMonoidHom) with hf
  have hfi : Function.Injective f := by
    intro v w h
    simp only [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
    exact β.symm.injective ((A7ZK.conjAut pk.T_le_normalizer ⟨t, ht⟩).injective
      (β.injective ((G6.coreAct 7 π⁻¹).injective h)))
  have hcomm : ∀ σ ∈ alternatingGroup (Fin 7), ∀ v,
      f (G6.coreAct 7 σ v) = G6.coreAct 7 σ (f v) := by
    intro σ hσ v
    obtain ⟨q, hq⟩ := e.surjective ⟨σ, hσ⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    set u := β.symm v with hu
    have hv : v = β u := by rw [hu, MulEquiv.apply_symm_apply]
    have h1 : G6.coreAct 7 σ v = β (A7ZK.conjAut pk.le_normalizer k u) := by
      apply Subtype.ext
      rw [hβ, hq, hv]
      rfl
    have hk' : t * k * t⁻¹ ∈ Kh := (Subgroup.mem_normalizer_iff.mp (pk.T_le ht) k).mp k.2
    have h2 : A7ZK.conjAut pk.T_le_normalizer ⟨t, ht⟩ (A7ZK.conjAut pk.le_normalizer k u) =
        A7ZK.conjAut pk.le_normalizer ⟨t * k * t⁻¹, hk'⟩
          (A7ZK.conjAut pk.T_le_normalizer ⟨t, ht⟩ u) := by
      apply Subtype.ext
      simp only [A7ZK.coe_conjAut]
      group
    have h3 : β (A7ZK.conjAut pk.le_normalizer ⟨t * k * t⁻¹, hk'⟩
        (A7ZK.conjAut pk.T_le_normalizer ⟨t, ht⟩ u)) =
        G6.coreAct 7 (π * σ * π⁻¹) (β (A7ZK.conjAut pk.T_le_normalizer ⟨t, ht⟩ u)) := by
      apply Subtype.ext
      rw [hβ, hconj, hq]
      rfl
    simp only [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [h1, MulEquiv.symm_apply_apply, h2, h3, hv, MulEquiv.symm_apply_apply,
      ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    group
  have hid := D7Pos.eq_of_commute_coreAct f hfi hcomm
  refine ⟨π, fun u => ?_, fun p hp => ?_⟩
  · have h1 := hid (β u)
    simp only [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      at h1
    rw [← h1, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  · obtain ⟨g, hg, hgp⟩ := A7Std.exists_mem_p0 hp
    rw [← pk.p0] at hg
    obtain ⟨q, ⟨k, hk, rfl⟩, hqe⟩ := hg
    have hkT : (k : G) ∈ T := (Subgroup.mem_subgroupOf.mp hk).1
    have hk' : t * k * t⁻¹ ∈ Kh := (Subgroup.mem_normalizer_iff.mp (pk.T_le ht) k).mp k.2
    have h1 := hconj k
    have h2 : e (QuotientGroup.mk ⟨t * k * t⁻¹, hk'⟩) ∈ A7Std.p0 := by
      rw [← pk.p0]
      exact ⟨_, ⟨⟨t * k * t⁻¹, hk'⟩,
        Subgroup.mem_subgroupOf.mpr ⟨T.mul_mem (T.mul_mem ht hkT) (T.inv_mem ht), hk'⟩, rfl⟩,
        rfl⟩
    rw [← hgp, ← hqe]
    rw [A7Std.mem_p0, h1] at h2
    exact h2

theorem not_le_normalizer_thompsonJ_of_six {T K Kh W : Subgroup G}
    {e : O2Q Kh ≃* alternatingGroup (Fin 7)} (pk : A7Pack T K Kh W e)
    (h64 : Nat.card ↥⁅W, Kh⁆ = 2 ^ 6)
    (hJU : ¬ thompsonJ T ≤ Subgroup.centralizer ((⁅W, Kh⁆ : Subgroup G) : Set G))
    {D₃ : Subgroup G} (h3 : Nat.card D₃ = 3)
    (hpos : ∀ d : ↥Kh, (d : G) ∈ D₃ → ∀ i : Fin 7, (i = 0 ∨ i = 5 ∨ i = 6) →
      ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 0 ∨
        ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 5 ∨
        ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = 6)
    (hmove : ∃ d : ↥Kh, (d : G) ∈ D₃ ∧
      ((e (QuotientGroup.mk d) : alternatingGroup (Fin 7)) : Perm (Fin 7)) 0 ≠ 0) :
    ¬ D₃ ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
  intro hDJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsElemAbelian 2 ⁅W, Kh⁆ := pk.elemAbelian
  have hKhU : Kh ≤ Subgroup.normalizer ((⁅W, Kh⁆ : Subgroup G) : Set G) := pk.le_normalizer
  have hTU : T ≤ Subgroup.normalizer ((⁅W, Kh⁆ : Subgroup G) : Set G) := pk.T_le_normalizer
  have hYU : Kh ⊔ T ≤ Subgroup.normalizer ((⁅W, Kh⁆ : Subgroup G) : Set G) := sup_le hKhU hTU
  have hT2 : IsPGroup 2 T := pk.sylow.2.1
  have hUT : ⁅W, Kh⁆ ≤ T := pk.U_le.trans pk.le_T
  let _ : CommGroup ↥⁅W, Kh⁆ := commGroupOfElemAbelian hU
  obtain ⟨β, hβ⟩ := A7ZK.exists_coreMod_equiv e hKhU hU pk.pCoreOf_le pk.irr
    pk.not_le_centralizer h64
  set φ : ↥Kh →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥Kh))) with hφ
  have hφe : ∀ k : ↥Kh,
      φ k = ((e (QuotientGroup.mk k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) := fun _ => rfl
  have hactK : ∀ (k : ↥Kh) u, β (A7ZK.conjAut hYU ⟨k, Subgroup.mem_sup_left k.2⟩ u) =
      G6.coreAct 7 (φ k) (β u) := by
    intro k u
    have e1 : A7ZK.conjAut hYU ⟨k, Subgroup.mem_sup_left k.2⟩ u = A7ZK.conjAut hKhU k u :=
      Subtype.ext rfl
    rw [e1]
    exact Subtype.ext (hβ k u)
  have hactT : ∀ t (ht : t ∈ T), ∃ π : Perm (Fin 7),
      (∀ u, β (A7ZK.conjAut hYU ⟨t, Subgroup.mem_sup_right ht⟩ u) = G6.coreAct 7 π (β u)) ∧
      ∀ p ∈ A7Std.p0L, π * p * π⁻¹ ∈ A7Std.p0L := by
    intro t ht
    obtain ⟨π, hπ, hπN⟩ := pk.exists_perm_of_mem hβ ht
    refine ⟨π, fun u => ?_, hπN⟩
    have e1 : A7ZK.conjAut hYU ⟨t, Subgroup.mem_sup_right ht⟩ u =
        A7ZK.conjAut pk.T_le_normalizer ⟨t, ht⟩ u := Subtype.ext rfl
    rw [e1]
    exact hπ u
  have hzero : ∀ t (ht : t ∈ T) (π : Perm (Fin 7)),
      (∀ u, β (A7ZK.conjAut hYU ⟨t, Subgroup.mem_sup_right ht⟩ u) = G6.coreAct 7 π (β u)) →
      π 0 = 0 ∧ ∀ p ∈ A7Std.p0L, π * p * π⁻¹ ∈ A7Std.p0L := by
    intro t ht π hπ
    obtain ⟨π', hπ', hN⟩ := hactT t ht
    obtain rfl : π = π' := acts_unique hYU β hπ hπ'
    exact ⟨D7Pos.zero_of_normalizes hN, hN⟩
  have hJT : thompsonJ T ≤ T := B6.thompsonJ_le T
  obtain ⟨d₀, hd₀, hmv⟩ := hmove
  have hd₀3 : φ d₀ * φ d₀ * φ d₀ = 1 := by
    have h1 : (⟨(d₀ : G), hd₀⟩ : ↥D₃) ^ 3 = 1 := by
      rw [← h3]
      exact pow_card_eq_one'
    have h2 : (d₀ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val h1
    have h4 : d₀ ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h2, Subgroup.coe_one])
    rw [← map_mul, ← map_mul, ← pow_three', h4, map_one]
  have hfix : ∀ z (hz : z ∈ thompsonJ T) (ω : Perm (Fin 7)),
      (∀ u, β (A7ZK.conjAut hYU ⟨z, Subgroup.mem_sup_right (hJT hz)⟩ u) =
        G6.coreAct 7 ω (β u)) →
      ω 0 = 0 ∧ ω 5 = 5 ∧ ω 6 = 6 := by
    intro z hz ω hω
    have key : ∀ d : ↥Kh, (d : G) ∈ D₃ → ω ((φ d)⁻¹ 0) = (φ d)⁻¹ 0 := by
      intro d hd
      have hdz : (d : G) * z * (d : G)⁻¹ ∈ thompsonJ T :=
        (Subgroup.mem_normalizer_iff.mp (hDJ hd) z).mp hz
      have h1 := acts_of_coe_eq hYU β
        (y' := ⟨(d : G) * z * (d : G)⁻¹, Subgroup.mem_sup_right (hJT hdz)⟩) rfl
        (acts_mul hYU β (acts_mul hYU β (hactK d) hω) (acts_inv hYU β (hactK d)))
      have h2 := (hzero _ (hJT hdz) _ h1).1
      rw [Perm.mul_apply, Perm.mul_apply] at h2
      have h3 := congrArg (fun i => (φ d)⁻¹ i) h2
      rwa [← Perm.mul_apply (φ d)⁻¹, inv_mul_cancel, Perm.one_apply] at h3
    have h0 : ω 0 = 0 := (hzero z (hJT hz) ω hω).1
    have hq := key d₀ hd₀
    have hr := key d₀⁻¹ (D₃.inv_mem hd₀)
    rw [map_inv, inv_inv] at hr
    have hp0 : (0 : Fin 7) = 0 ∨ (0 : Fin 7) = 5 ∨ (0 : Fin 7) = 6 := Or.inl rfl
    have hq0 := hpos d₀ hd₀ 0 hp0
    have hr0 := hpos d₀⁻¹ (D₃.inv_mem hd₀) 0 hp0
    rw [← hφe] at hq0 hr0 hmv
    rw [map_inv] at hr0
    have hpq : (0 : Fin 7) ≠ φ d₀ 0 := fun h => hmv h.symm
    have hpr : (0 : Fin 7) ≠ (φ d₀)⁻¹ 0 := by
      intro h
      apply hmv
      conv_lhs => rw [h]
      rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
    have hqr : φ d₀ 0 ≠ (φ d₀)⁻¹ 0 := by
      intro h
      have h1 : φ d₀ (φ d₀ 0) = 0 := by rw [h, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
      have h2 := congrArg (fun f : Perm (Fin 7) => f 0) hd₀3
      simp only [Perm.mul_apply, Perm.one_apply] at h2
      rw [h1] at h2
      exact hmv h2
    have hj : ∀ j : Fin 7, (j = 0 ∨ j = 5 ∨ j = 6) → ω j = j := by
      intro j hj
      rcases A7Four.eq_of_three _ _ _ _ hp0 hq0 hr0 hpq hpr hqr hj with rfl | rfl | rfl
      · exact h0
      · exact hr
      · exact hq
    exact ⟨h0, hj 5 (Or.inr (Or.inl rfl)), hj 6 (Or.inr (Or.inr rfl))⟩
  have hCT : (Kh ⊔ T) ⊓ Subgroup.centralizer ((⁅W, Kh⁆ : Subgroup G) : Set G) ≤ T := by
    have hC2 := isPGroup_sup_inf_centralizer pk.perf pk.simple hT2 pk.T_le hYU
      pk.not_le_centralizer
    have hCY : Kh ⊔ T ≤ Subgroup.normalizer
        (((Kh ⊔ T) ⊓ Subgroup.centralizer ((⁅W, Kh⁆ : Subgroup G) : Set G) : Subgroup G) :
          Set G) := fun y hy =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hy, B6.le_normalizer_centralizer hYU hy⟩
    exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCY hC2).trans
      (F7.isSylowTwoOf_pCoreOf_le pk.sylow)
  have hex : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      ¬ A ≤ Subgroup.centralizer ((⁅W, Kh⁆ : Subgroup G) : Set G) := by
    by_contra hcon
    exact hJU (iSup₂_le fun A hA => by_contra fun hn => hcon ⟨A, hA, hn⟩)
  obtain ⟨A, hA, hAU⟩ := hex
  have hAT : A ≤ T := hA.1
  have hAJ : A ≤ thompsonJ T := B6.le_thompsonJ hA
  have hAY : A ≤ Kh ⊔ T := hAT.trans le_sup_right
  have hAN : A ≤ Subgroup.normalizer ((⁅W, Kh⁆ : Subgroup G) : Set G) := hAT.trans hTU
  set P : Subgroup (Perm (Fin 7)) :=
    ((autOn A ⁅W, Kh⁆).map (MulAut.congr β).toMonoidHom).comap (G6.coreAct 7) with hP
  have hPmem : ∀ σ ∈ P, ∃ a, ∃ ha : a ∈ A,
      ∀ u, β (A7ZK.conjAut hYU ⟨a, hAY ha⟩ u) = G6.coreAct 7 σ (β u) := by
    intro σ hσ
    obtain ⟨x, hx, hxσ⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hσ)
    obtain ⟨⟨a, ha⟩, rfl⟩ := (A4.mem_autOn_iff hAN).mp hx
    refine ⟨a, ha, fun u => ?_⟩
    rw [← hxσ, MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  have hmemP : ∀ a (ha : a ∈ A) (π : Perm (Fin 7)),
      (∀ u, β (A7ZK.conjAut hYU ⟨a, hAY ha⟩ u) = G6.coreAct 7 π (β u)) →
      (MulAut.congr β).toMonoidHom (A4.actionOn ⁅W, Kh⁆ A hAN ⟨a, ha⟩) = G6.coreAct 7 π := by
    intro a ha π hπ
    refine MulEquiv.ext fun v => ?_
    obtain ⟨u, rfl⟩ := β.surjective v
    rw [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply, ← hπ u]
    rfl
  by_cases hcase : ∀ σ ∈ P, σ ∈ A7Four.eL
  ·
    have hP1 : P ≠ ⊥ := by
      intro hbot
      apply hAU
      intro a ha
      obtain ⟨π, hπ, -⟩ := hactT a (hAT ha)
      have hπP : π ∈ P := by
        show G6.coreAct 7 π ∈ (autOn A ⁅W, Kh⁆).map (MulAut.congr β).toMonoidHom
        exact ⟨_, (A4.mem_autOn_iff hAN).mpr ⟨⟨a, ha⟩, rfl⟩, hmemP a ha π hπ⟩
      rw [hbot, Subgroup.mem_bot] at hπP
      subst hπP
      exact mem_centralizer_of_acts_one hYU β hπ
    have hff := (offender_core hU hUT hTU hA (B := ⊥) bot_le).1
    rw [B1.card_bot_mul_card_fixV] at hff
    have h1 : Nat.card (IntMod ⁅W, Kh⁆ hU) = 64 := by
      show Nat.card ↥⁅W, Kh⁆ = 64
      rw [h64]
      norm_num
    rw [h1] at hff
    have hff' : 64 ≤ Nat.card (autOn A ⁅W, Kh⁆) * Nat.card (fixV (autOn A ⁅W, Kh⁆)) := hff
    have hle : (autOn A ⁅W, Kh⁆).map (MulAut.congr β).toMonoidHom ≤ P.map (G6.coreAct 7) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨⟨a, ha⟩, rfl⟩ := (A4.mem_autOn_iff hAN).mp hx
      obtain ⟨π, hπ, -⟩ := hactT a (hAT ha)
      have hcπ := hmemP a ha π hπ
      refine ⟨π, ?_, hcπ.symm⟩
      show G6.coreAct 7 π ∈ (autOn A ⁅W, Kh⁆).map (MulAut.congr β).toMonoidHom
      exact ⟨_, hx, hcπ⟩
    have hc1 : Nat.card (autOn A ⁅W, Kh⁆) ≤ Nat.card P := by
      have h2 := Subgroup.card_le_of_le hle
      rwa [Subgroup.card_map_of_injective (MulAut.congr β).injective,
        Subgroup.card_map_of_injective D7Pos.coreAct_injective] at h2
    have hc2 : Nat.card (fixV (autOn A ⁅W, Kh⁆)) ≤ Nat.card {x : Fin 7 → ZMod 2 //
        (∀ σ ∈ P, ∀ i, x (σ⁻¹ i) = x i) ∧ ∑ i, x i = 0} := by
      refine Nat.card_le_card_of_injective (fun u => ⟨Multiplicative.toAdd
        ((β u.1 : ↥(G6.coreMod 7)) : G6.PermMod 7), fun σ hσ i => ?_,
          G6.mem_coreMod.mp (β u.1).2⟩) fun u v huv => ?_
      · obtain ⟨x, hx, hxσ⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hσ)
        have hfx : x u.1 = u.1 := (mem_fixV.mp u.2) x hx
        have h2 : G6.coreAct 7 σ (β u.1) = β u.1 := by
          rw [← hxσ, MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
            MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hfx]
        exact congrArg (fun w : ↥(G6.coreMod 7) => Multiplicative.toAdd (w : G6.PermMod 7) i) h2
      · have h2 := Subtype.ext_iff.mp huv
        exact Subtype.ext (β.injective (Subtype.ext (Multiplicative.toAdd.injective h2)))
    have hc3 := D7Pos.card_mul_card_fixVec_le hcase hP1
    have h4 : Nat.card (autOn A ⁅W, Kh⁆) * Nat.card (fixV (autOn A ⁅W, Kh⁆)) ≤ 32 :=
      (Nat.mul_le_mul hc1 hc2).trans hc3
    omega
  ·
    obtain ⟨σ, hσP, hσE⟩ : ∃ σ ∈ P, σ ∉ A7Four.eL := by
      by_contra hc
      exact hcase fun σ hσ => by_contra fun hn => hc ⟨σ, hσ, hn⟩
    obtain ⟨a, ha, hσa⟩ := hPmem σ hσP
    have hsq : ∀ y (hy : y ∈ A) (τ : Perm (Fin 7)),
        (∀ u, β (A7ZK.conjAut hYU ⟨y, hAY hy⟩ u) = G6.coreAct 7 τ (β u)) → τ * τ = 1 := by
      intro y hy τ hτ
      have h1 := acts_of_coe_eq hYU β (y' := 1) (by
        show y * y = 1
        rw [← sq]
        exact hA.2.1.2 y hy) (acts_mul hYU β hτ hτ)
      have h2 : ∀ u, β (A7ZK.conjAut hYU 1 u) = G6.coreAct 7 1 (β u) := fun u => by
        rw [map_one, map_one, MulAut.one_apply, MulAut.one_apply]
      exact acts_unique hYU β h1 h2
    obtain ⟨h0a, h5a, h6a⟩ := hfix a (hAJ ha) σ hσa
    have hσinv := D7Pos.mem_invL h0a h5a h6a (hsq a ha σ hσa) (hzero a (hAT ha) σ hσa).2
    have hs : σ = swap 1 3 ∨ σ = swap 2 4 :=
      (D7Pos.mem_eL_or_of_mem_invL hσinv).resolve_left hσE
    obtain ⟨γ, hγ1, hγs, hγP⟩ := D7Pos.exists_gam hs
    obtain ⟨q, hq⟩ := e.surjective ⟨γ, Equiv.Perm.mem_alternatingGroup.mpr hγ1⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hφg : φ g = γ := by rw [hφe, hq]
    have hgY : (g : G) ∈ Kh ⊔ T := Subgroup.mem_sup_left g.2
    have hA'Y : IsMaxElemAbelian (Kh ⊔ T) (cjSub (g : G) A) :=
      isMaxElemAbelian_cjSub (Subgroup.le_normalizer hgY)
        (isMaxElemAbelian_of_isSylowTwoOf pk.sylow hA)
    have hp0 : ∀ ω ∈ A7Std.p0L, ∃ k : ↥Kh, (k : G) ∈ T ∧ φ k = ω := by
      intro ω hω
      obtain ⟨w, hw, hwe⟩ := A7Std.exists_mem_p0 hω
      rw [← pk.p0] at hw
      obtain ⟨q', ⟨k, hk, rfl⟩, hq'⟩ := hw
      refine ⟨k, (Subgroup.mem_subgroupOf.mp hk).1, ?_⟩
      rw [hφe, ← hwe, ← hq']
      rfl
    have hA'T : cjSub (g : G) A ≤ T := by
      intro x hx
      have hy : (g : G)⁻¹ * x * g ∈ A := mem_cjSub.mp hx
      obtain ⟨τ, hτ, hτN⟩ := hactT _ (hAT hy)
      obtain ⟨h0y, h5y, h6y⟩ := hfix _ (hAJ hy) τ hτ
      have hτσ : τ * σ = σ * τ := by
        have hya : (g : G)⁻¹ * x * g * a = a * ((g : G)⁻¹ * x * g) :=
          B2F.isElemAbelian_comm hA.2.1 hy ha
        have h1 := acts_of_coe_eq hYU β
          (y := ⟨_, Subgroup.mem_sup_right (hAT hy)⟩ * ⟨a, hAY ha⟩)
          (y' := ⟨a, hAY ha⟩ * ⟨_, Subgroup.mem_sup_right (hAT hy)⟩) hya (acts_mul hYU β hτ hσa)
        exact acts_unique hYU β h1 (acts_mul hYU β hσa hτ)
      have hτinv := D7Pos.mem_invL h0y h5y h6y (hsq _ hy τ hτ) hτN
      have hx' : ∀ u, β (A7ZK.conjAut hYU ⟨x, hA'Y.1 hx⟩ u) =
          G6.coreAct 7 (γ * τ * γ⁻¹) (β u) := by
        have h1 := acts_mul hYU β (acts_mul hYU β (hactK g) hτ) (acts_inv hYU β (hactK g))
        rw [hφg] at h1
        exact acts_of_coe_eq hYU β (by show (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ = x; group)
          h1
      have hxY : x ∈ Kh ⊔ T := hA'Y.1 hx
      rcases hγP τ hτinv hτσ with hP0 | hP0
      · obtain ⟨k, hkT, hφk⟩ := hp0 _ hP0
        have h1 := acts_mul hYU β (acts_inv hYU β (hactK k)) hx'
        rw [hφk, inv_mul_cancel] at h1
        have hc := mem_centralizer_of_acts_one hYU β h1
        have hmem : (k : G)⁻¹ * x ∈ (Kh ⊔ T) ⊓
            Subgroup.centralizer ((⁅W, Kh⁆ : Subgroup G) : Set G) :=
          ⟨(Kh ⊔ T).mul_mem ((Kh ⊔ T).inv_mem (Subgroup.mem_sup_left k.2)) hxY, hc⟩
        have e1 : x = (k : G) * ((k : G)⁻¹ * x) := by group
        rw [e1]
        exact T.mul_mem hkT (hCT hmem)
      · obtain ⟨k, hkT, hφk⟩ := hp0 _ hP0
        have h1 := acts_mul hYU β (acts_inv hYU β (acts_mul hYU β hσa (hactK k))) hx'
        have e2 : (σ * φ k)⁻¹ * (γ * τ * γ⁻¹) = 1 := by
          rw [hφk, ← mul_assoc σ σ, hsq a ha σ hσa, one_mul, inv_mul_cancel]
        rw [e2] at h1
        have hc := mem_centralizer_of_acts_one hYU β h1
        have hak : a * k ∈ T := T.mul_mem (hAT ha) hkT
        have hmem : (a * k : G)⁻¹ * x ∈ (Kh ⊔ T) ⊓
            Subgroup.centralizer ((⁅W, Kh⁆ : Subgroup G) : Set G) :=
          ⟨(Kh ⊔ T).mul_mem ((Kh ⊔ T).inv_mem (Subgroup.mem_sup_right hak)) hxY, hc⟩
        have e1 : x = (a * k : G) * ((a * k : G)⁻¹ * x) := by group
        rw [e1]
        exact T.mul_mem hak (hCT hmem)
    have hA'T' : IsMaxElemAbelian T (cjSub (g : G) A) :=
      ⟨hA'T, hA'Y.2.1, fun B hBT hB => hA'Y.2.2 B (hBT.trans le_sup_right) hB⟩
    have hA'J : cjSub (g : G) A ≤ thompsonJ T := B6.le_thompsonJ hA'T'
    have hx0 : (g : G) * a * (g : G)⁻¹ ∈ cjSub (g : G) A := by
      rw [mem_cjSub]
      simpa [mul_assoc] using ha
    have h1 := acts_mul hYU β (acts_mul hYU β (hactK g) hσa) (acts_inv hYU β (hactK g))
    rw [hφg, hγs] at h1
    have h2 := acts_of_coe_eq hYU β
      (y' := ⟨(g : G) * a * (g : G)⁻¹, Subgroup.mem_sup_right (hJT (hA'J hx0))⟩) rfl h1
    have h56 := (hfix _ (hA'J hx0) _ h2).2.1
    exact absurd h56 (by decide)

end SixSide

end CFSG.Quasithin.H13
