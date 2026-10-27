module

public import CFSG.Timmesfeld.ARS.CaseERootSys

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType.RootSystem

variable {I : Type} [Fintype I] [DecidableEq I]

@[expose] def cartanPair (A : Matrix I I ℤ) (u v : I → ℤ) : ℤ := ∑ k, v k * coroot A k u

section Pair

variable {A : Matrix I I ℤ}

theorem cartanPair_single (u : I → ℤ) (k : I) : cartanPair A u (Pi.single k 1) = coroot A k u := by
  rw [cartanPair, Finset.sum_eq_single k (fun m _ hm => by simp [Pi.single_eq_of_ne hm])
    (fun h => absurd (Finset.mem_univ k) h)]
  simp

omit [DecidableEq I] in
theorem cartanPair_self (u : I → ℤ) : cartanPair A u u = cartanForm A u := rfl

omit [DecidableEq I] in
theorem cartanPair_comm (hsymm : ∀ i j, A i j = A j i) (u v : I → ℤ) :
    cartanPair A u v = cartanPair A v u := by
  simp only [cartanPair, coroot_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    rw [hsymm a b]
    ring

omit [DecidableEq I] in
theorem cartanForm_add (hsymm : ∀ i j, A i j = A j i) (u v : I → ℤ) :
    cartanForm A (u + v) = cartanForm A u + cartanForm A v + 2 * cartanPair A u v := by
  have e : cartanForm A (u + v) =
      cartanForm A u + cartanForm A v + cartanPair A v u + cartanPair A u v := by
    simp only [cartanForm, cartanPair, map_add, Pi.add_apply, add_mul, mul_add,
      Finset.sum_add_distrib]
    ring
  rw [e, cartanPair_comm hsymm v u]
  ring

variable (hA : TauCeti.IsFiniteType A)

include hA in
theorem cartanPair_weylAction (hsymm : ∀ i j, A i j = A j i) (w : (coxeterMatrix hA).Group)
    (u v : I → ℤ) :
    cartanPair A (weylAction hA w u) (weylAction hA w v) = cartanPair A u v := by
  have h := cartanForm_weylAction hA hsymm w (u + v)
  rw [map_add, cartanForm_add hsymm, cartanForm_add hsymm, cartanForm_weylAction hA hsymm,
    cartanForm_weylAction hA hsymm] at h
  linarith

end Pair

section Level

variable {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

include hA in
theorem weylAction_apply_self_of_mem_parabolic {j : I} {z : (coxeterMatrix hA).Group}
    (hz : z ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {k | k ≠ j}) (v : I → ℤ) :
    weylAction hA z v j = v j :=
  weylAction_apply_of_mem_parabolic hA hz v (fun h => h rfl)

include hA in
theorem exists_mem_parabolic_eq_of_level_one (hpd : (A.map (Int.cast : ℤ → ℚ)).PosDef) (j : I)
    {β : I → ℤ} (hβ : β ∈ roots hA ∅) (hβj : β j = 1) :
    ∃ u ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {k | k ≠ j},
      weylAction hA u (Pi.single j 1) = β := by
  have hsymm := cartan_symm_of_posDef hpd
  set cs := (coxeterMatrix hA).toCoxeterSystem
  have hpos : 0 ≤ β := by
    rcases nonneg_or_nonpos hA ∅ hβ with h | h
    · exact h
    · have := h j
      simp only [Pi.zero_apply] at this
      omega
  induction hn : (∑ m, β m).toNat using Nat.strong_induction_on generalizing β with
  | _ N ih =>
    by_cases hβα : β = Pi.single j 1
    · exact ⟨1, one_mem _, by rw [hβα, map_one, Module.End.one_apply]⟩
    have hpos' : ∀ m, 0 ≤ β m := fun m => by simpa using hpos m
    have hq := cartanForm_eq_two hA hsymm hβ
    have hcj : coroot A j β ≤ 1 := coroot_le_one hA hpd hβ hβα
    obtain ⟨k, hkj, hβk, hck⟩ : ∃ k, k ≠ j ∧ 0 < β k ∧ 0 < coroot A k β := by
      by_contra hcon
      push Not at hcon
      have hle : ∀ m, m ≠ j → β m * coroot A m β ≤ 0 := fun m hm => by
        rcases (hpos' m).lt_or_eq with hlt | heq
        · nlinarith [hcon m hm hlt]
        · rw [← heq, zero_mul]
      have hsplit : cartanForm A β = β j * coroot A j β +
          ∑ m ∈ Finset.univ.erase j, β m * coroot A m β := by
        rw [cartanForm, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      have hrest : ∑ m ∈ Finset.univ.erase j, β m * coroot A m β ≤ 0 :=
        Finset.sum_nonpos fun m hm => hle m (Finset.ne_of_mem_erase hm)
      rw [hβj, one_mul] at hsplit
      omega
    have hβαk : β ≠ Pi.single k 1 := fun e => by
      have := congrFun e j
      rw [hβj, Pi.single_eq_of_ne (Ne.symm hkj)] at this
      omega
    have hck1 : coroot A k β = 1 := le_antisymm (coroot_le_one hA hpd hβ hβαk) hck
    set β' : I → ℤ := β - Pi.single k 1 with hβ'def
    have hs : weylAction hA (cs.simple k) β = β' := by
      rw [weylAction_simple, reflection_apply_coroot, hck1, one_smul]
    have hβ' : β' ∈ roots hA ∅ := hs ▸ weylAction_mem_roots hA _ hβ
    have hβ'j : β' j = 1 := by
      rw [hβ'def, Pi.sub_apply, hβj, Pi.single_eq_of_ne (Ne.symm hkj), sub_zero]
    have hβ'pos : 0 ≤ β' := by
      rcases nonneg_or_nonpos hA ∅ hβ' with h | h
      · exact h
      · have := h j
        rw [hβ'j] at this
        simp at this
    have hht : (∑ m, β' m).toNat < N := by
      have hsum : ∑ m, β' m = ∑ m, β m - 1 := by
        simp [hβ'def, Finset.sum_sub_distrib]
      have hge : β k ≤ ∑ m, β m :=
        Finset.single_le_sum (fun m _ => hpos' m) (Finset.mem_univ k)
      rw [← hn, hsum]
      exact Int.toNat_lt_toNat (by omega) |>.2 (by omega)
    obtain ⟨u, hu, hue⟩ := ih _ hht hβ' hβ'j hβ'pos rfl
    refine ⟨cs.simple k * u, mul_mem (cs.simple_mem_parabolic hkj) hu, ?_⟩
    rw [weylAction_mul_apply, hue, ← hs, ← weylAction_mul_apply,
      CoxeterSystem.simple_mul_simple_self, map_one, Module.End.one_apply]

@[expose] def levelInv (j : I) (x : (coxeterMatrix hA).Group) : Set (I → ℤ) :=
  {β | β ∈ roots hA ∅ ∧ β j = 1 ∧ weylAction hA x⁻¹ β j = 1}

include hA in
theorem levelInv_mul_left {j : I} {u : (coxeterMatrix hA).Group}
    (hu : u ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {k | k ≠ j})
    (x : (coxeterMatrix hA).Group) {β : I → ℤ} (hβ : β ∈ levelInv hA j x) :
    weylAction hA u β ∈ levelInv hA j (u * x) := by
  obtain ⟨h1, h2, h3⟩ := hβ
  refine ⟨weylAction_mem_roots hA _ h1, ?_, ?_⟩
  · rw [weylAction_apply_self_of_mem_parabolic hA hu, h2]
  · rw [mul_inv_rev, weylAction_mul_apply, weylAction_inv_apply_apply]
    exact h3

include hA in
theorem levelInv_mul_right {j : I} {v : (coxeterMatrix hA).Group}
    (hv : v ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {k | k ≠ j})
    (x : (coxeterMatrix hA).Group) {β : I → ℤ} (hβ : β ∈ levelInv hA j x) :
    β ∈ levelInv hA j (x * v) := by
  obtain ⟨h1, h2, h3⟩ := hβ
  refine ⟨h1, h2, ?_⟩
  rw [mul_inv_rev, weylAction_mul_apply, weylAction_apply_self_of_mem_parabolic hA (inv_mem hv),
    h3]

include hA in
theorem exists_two_mem_levelInv (hpd : (A.map (Int.cast : ℤ → ℚ)).PosDef) {j : I}
    (hstar : ∀ γ ∈ roots hA ∅, γ j = 1 → ∃ β₁ β₂ : I → ℤ, β₁ ≠ β₂ ∧
      ∀ β ∈ ({β₁, β₂} : Set (I → ℤ)), β ∈ roots hA ∅ ∧ β j = 1 ∧ coroot A j β = 0 ∧
        cartanPair A β γ = 0)
    {u v y : (coxeterMatrix hA).Group}
    (hu : u ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {k | k ≠ j})
    (hv : v ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {k | k ≠ j})
    (hy : y = 1 ∨ y = (coxeterMatrix hA).toCoxeterSystem.simple j ∨
      ∃ z ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {k | k ≠ j},
        y = (coxeterMatrix hA).toCoxeterSystem.simple j * z *
        (coxeterMatrix hA).toCoxeterSystem.simple j) :
    ∃ β₁ β₂ : I → ℤ, β₁ ≠ β₂ ∧ β₁ ∈ levelInv hA j (u * y * v) ∧
      β₂ ∈ levelInv hA j (u * y * v) := by
  have hsymm := cartan_symm_of_posDef hpd
  set cs := (coxeterMatrix hA).toCoxeterSystem
  have hαj : (Pi.single j 1 : I → ℤ) ∈ roots hA ∅ := Or.inl ⟨1, j, by simp⟩
  have hsj : ∀ β : I → ℤ, coroot A j β = 0 → weylAction hA (cs.simple j) β = β := fun β h => by
    rw [weylAction_simple, reflection_apply_coroot, h, zero_smul, sub_zero]
  have hy2 : ∃ β₁ β₂ : I → ℤ, β₁ ≠ β₂ ∧ β₁ ∈ levelInv hA j y ∧ β₂ ∈ levelInv hA j y := by
    rcases hy with rfl | rfl | ⟨z, hz, rfl⟩
    · obtain ⟨β₁, β₂, hne, hβ⟩ := hstar _ hαj (by simp)
      have key : ∀ β ∈ ({β₁, β₂} : Set (I → ℤ)), β ∈ levelInv hA j 1 := fun β hmem => by
        obtain ⟨h1, h2, -, -⟩ := hβ β hmem
        exact ⟨h1, h2, by rw [inv_one, map_one, Module.End.one_apply, h2]⟩
      exact ⟨β₁, β₂, hne, key _ (by simp), key _ (by simp)⟩
    · obtain ⟨β₁, β₂, hne, hβ⟩ := hstar _ hαj (by simp)
      have key : ∀ β ∈ ({β₁, β₂} : Set (I → ℤ)), β ∈ levelInv hA j (cs.simple j) :=
        fun β hmem => by
          obtain ⟨h1, h2, h3, -⟩ := hβ β hmem
          exact ⟨h1, h2, by rw [CoxeterSystem.inv_simple, hsj _ h3, h2]⟩
      exact ⟨β₁, β₂, hne, key _ (by simp), key _ (by simp)⟩
    · set γ := weylAction hA z (Pi.single j 1) with hγ
      have hγr : γ ∈ roots hA ∅ := weylAction_mem_roots hA _ hαj
      have hγj : γ j = 1 := by
        rw [hγ, weylAction_apply_self_of_mem_parabolic hA hz]
        simp
      obtain ⟨β₁, β₂, hne, hβ⟩ := hstar γ hγr hγj
      have key : ∀ β ∈ ({β₁, β₂} : Set (I → ℤ)),
          β ∈ levelInv hA j (cs.simple j * z * cs.simple j) := fun β hmem => by
        obtain ⟨h1, h2, h3, h4⟩ := hβ β hmem
        refine ⟨h1, h2, ?_⟩
        have hz1 : weylAction hA z⁻¹ β j = 1 := by
          rw [weylAction_apply_self_of_mem_parabolic hA (inv_mem hz), h2]
        have hz2 : coroot A j (weylAction hA z⁻¹ β) = 0 := by
          rw [← cartanPair_single, ← cartanPair_weylAction hA hsymm z,
            weylAction_apply_inv_apply, h4]
        rw [mul_inv_rev, mul_inv_rev, CoxeterSystem.inv_simple, weylAction_mul_apply,
          weylAction_mul_apply, hsj _ h3, hsj _ hz2, hz1]
      exact ⟨β₁, β₂, hne, key _ (by simp), key _ (by simp)⟩
  obtain ⟨β₁, β₂, hne, h1, h2⟩ := hy2
  refine ⟨weylAction hA u β₁, weylAction hA u β₂, fun e => hne ?_, ?_, ?_⟩
  · exact weylAction_apply_injective hA u e
  · exact levelInv_mul_right hA hv _ (levelInv_mul_left hA hu _ h1)
  · exact levelInv_mul_right hA hv _ (levelInv_mul_left hA hu _ h2)

include hA in
theorem weylAction_inv_apply_self_of_neg {w₀ : (coxeterMatrix hA).Group} {σ : I → I}
    (hσ : ∀ k, weylAction hA w₀ (Pi.single k 1) = -Pi.single (σ k) 1) (hσinj : Function.Injective σ)
    {j : I} (hσj : σ j = j) (γ : I → ℤ) : weylAction hA w₀⁻¹ γ j = -γ j := by
  set δ := weylAction hA w₀⁻¹ γ with hδ
  have hγ : γ = weylAction hA w₀ δ := by rw [hδ, weylAction_apply_inv_apply]
  have hsum : weylAction hA w₀ δ = ∑ k, δ k • weylAction hA w₀ (Pi.single k 1) := by
    conv_lhs => rw [← sum_smul_single δ]
    simp only [map_sum, map_zsmul]
  rw [hγ, hsum, Finset.sum_apply, Finset.sum_eq_single j]
  · rw [Pi.smul_apply, hσ, hσj]
    simp
  · intro k _ hkj
    rw [Pi.smul_apply, hσ, Pi.neg_apply,
      Pi.single_eq_of_ne (fun e => hkj (hσinj (e.symm.trans hσj.symm)))]
    simp
  · intro h
    exact absurd (Finset.mem_univ j) h

include hA in
theorem levelInv_simple_mul_subset (hpd : (A.map (Int.cast : ℤ → ℚ)).PosDef)
    {w₀ : (coxeterMatrix hA).Group} {σ : I → I}
    (hσ : ∀ k, weylAction hA w₀ (Pi.single k 1) = -Pi.single (σ k) 1) (hσinj : Function.Injective σ)
    {j : I} (hσj : σ j = j) {β : I → ℤ}
    (hβ : β ∈ levelInv hA j ((coxeterMatrix hA).toCoxeterSystem.simple j * w₀)) :
    β = Pi.single j 1 := by
  obtain ⟨h1, h2, h3⟩ := hβ
  by_contra hne
  have hc := coroot_le_one hA hpd h1 hne
  rw [mul_inv_rev, CoxeterSystem.inv_simple, weylAction_mul_apply,
    weylAction_inv_apply_self_of_neg hA hσ hσinj hσj, weylAction_simple, reflection_apply_coroot,
    Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, h2] at h3
  omega

end Level

end CFSG.Timmesfeld.ARS
