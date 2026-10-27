module

public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs

public section

namespace CFSG.StandardType.S2MathFi1451

open CFSG.LieType.RootSystem

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

theorem weylAction_comp_linearCombination {κ : Type} [Fintype κ] [DecidableEq κ]
    {A' : Matrix κ κ ℤ} (hA' : TauCeti.IsFiniteType A')
    (h : (coxeterMatrix hA').Group →* (coxeterMatrix hA).Group) (π : κ → I → ℤ)
    (πc : κ → (I → ℤ) →ₗ[ℤ] ℤ)
    (hrefl : ∀ k v, weylAction hA (h ((coxeterMatrix hA').toCoxeterSystem.simple k)) v =
      v - πc k v • π k)
    (hcart : ∀ k l, πc k (π l) = A' k l) (g : (coxeterMatrix hA').Group) (x : κ → ℤ) :
    weylAction hA (h g) (Fintype.linearCombination ℤ π x) =
      Fintype.linearCombination ℤ π (weylAction hA' g x) := by
  have hπc : ∀ k y, πc k (Fintype.linearCombination ℤ π y) = coroot A' k y := by
    intro k y
    rw [Fintype.linearCombination_apply, map_sum, coroot_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, hcart, smul_eq_mul, mul_comm]
  induction g using (coxeterMatrix hA').toCoxeterSystem.simple_induction_left generalizing x with
  | one => simp
  | mul_simple_left g k ih =>
    rw [map_mul, weylAction_mul_apply, ih, hrefl, hπc, weylAction_mul_apply, weylAction_simple,
      reflection_apply_coroot, map_sub, map_zsmul, Fintype.linearCombination_apply_single,
      one_smul]

theorem transported_nonneg_or_nonpos {κ : Type} [Fintype κ] [DecidableEq κ]
    {A' : Matrix κ κ ℤ} (hA' : TauCeti.IsFiniteType A')
    (h : (coxeterMatrix hA').Group →* (coxeterMatrix hA).Group) (π : κ → I → ℤ)
    (πc : κ → (I → ℤ) →ₗ[ℤ] ℤ)
    (hrefl : ∀ k v, weylAction hA (h ((coxeterMatrix hA').toCoxeterSystem.simple k)) v =
      v - πc k v • π k)
    (hcart : ∀ k l, πc k (π l) = A' k l) (g : (coxeterMatrix hA').Group) (k : κ) :
    ∃ x : κ → ℤ, (0 ≤ x ∨ x ≤ 0) ∧
      weylAction hA (h g) (π k) = Fintype.linearCombination ℤ π x := by
  refine ⟨weylAction hA' g (Pi.single k 1), weylAction_single_nonneg_or_nonpos hA' g k, ?_⟩
  rw [← weylAction_comp_linearCombination hA hA' h π πc hrefl hcart,
    Fintype.linearCombination_apply_single, one_smul]

end CFSG.StandardType.S2MathFi1451

namespace CFSG.StandardType.S2MathFi1451

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg.OfCartan

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

section Cone

variable {κ : Type} [Fintype κ] (π : κ → I → ℤ)

@[expose] def ConePos (v : I → ℤ) : Prop :=
  ∃ y : κ → ℤ, 0 ≤ y ∧ v = Fintype.linearCombination ℤ π y

@[expose] def ConeNeg (v : I → ℤ) : Prop :=
  ∃ y : κ → ℤ, y ≤ 0 ∧ v = Fintype.linearCombination ℤ π y

variable {π}

theorem coneNeg_neg_iff {v : I → ℤ} : ConeNeg π (-v) ↔ ConePos π v := by
  constructor
  · rintro ⟨y, hy, hv⟩
    exact ⟨-y, neg_nonneg.mpr hy, by rw [map_neg, ← hv, neg_neg]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨-y, neg_nonpos.mpr hy, by rw [map_neg]⟩

theorem not_conePos_and_coneNeg (hind : LinearIndependent ℤ π) {v : I → ℤ} (hv : v ≠ 0)
    (hp : ConePos π v) (hn : ConeNeg π v) : False := by
  obtain ⟨y, hy, rfl⟩ := hp
  obtain ⟨y', hy', hyy⟩ := hn
  have he : y = y' := (linearIndependent_iff_injective_fintypeLinearCombination.mp hind) hyy
  subst he
  have : y = 0 := le_antisymm hy' hy
  exact hv (by rw [this, map_zero])

end Cone

theorem weylAction_simple_nonneg {w : (coxeterMatrix hA).Group} {i j : I}
    (hγ : 0 ≤ weylAction hA w (Pi.single j 1))
    (hne : weylAction hA w (Pi.single j 1) ≠ Pi.single i 1) :
    0 ≤ weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple i)
      (weylAction hA w (Pi.single j 1)) := by
  set cs := (coxeterMatrix hA).toCoxeterSystem
  rw [← weylAction_mul_apply]
  rcases weylAction_single_nonneg_or_nonpos hA (cs.simple i * w) j with h | h
  · exact h
  exfalso
  rw [weylAction_mul_apply] at h
  set γ := weylAction hA w (Pi.single j 1) with hγdef
  have hk : ∀ k, k ≠ i → γ k = 0 := fun k hk => by
    have h1 := h k
    rw [weylAction_simple_apply_of_ne hA i γ hk] at h1
    exact le_antisymm h1 (hγ k)
  have hsm : γ = γ i • Pi.single i 1 := by
    funext k
    by_cases hki : k = i
    · subst hki; simp
    · simp [hk k hki, hki]
  rcases eq_one_or_eq_neg_one_of_weylAction_eq_smul hA (hγdef ▸ hsm) with hc | hc
  · rw [← hγdef] at hc
    exact hne (by rw [hsm, hc, one_smul])
  · rw [← hγdef] at hc
    have := hγ i
    rw [Pi.zero_apply, hc] at this
    exact absurd this (by norm_num)

section Descent

variable {κ : Type} [Fintype κ] {π : κ → I → ℤ}

@[expose] def descSet (π : κ → I → ℤ) (x : (coxeterMatrix hA).Group) : Set (I → ℤ) :=
  {γ | (∃ (w : (coxeterMatrix hA).Group) (j : I), γ = weylAction hA w (Pi.single j 1)) ∧
    0 ≤ γ ∧ ConeNeg π (weylAction hA x γ)}

theorem descSet_finite (x : (coxeterMatrix hA).Group) : (descSet hA π x).Finite :=
  (finite_roots hA ∅).subset fun _ hγ => Or.inl hγ.1

theorem ncard_descSet_mul_lt (hind : LinearIndependent ℤ π) {x : (coxeterMatrix hA).Group}
    {i : I} (hi : ConeNeg π (weylAction hA x (Pi.single i 1))) :
    (descSet hA π (x * (coxeterMatrix hA).toCoxeterSystem.simple i)).ncard <
      (descSet hA π x).ncard := by
  set cs := (coxeterMatrix hA).toCoxeterSystem
  have hmem : (Pi.single i 1 : I → ℤ) ∈ descSet hA π x :=
    ⟨⟨1, i, by rw [map_one, Module.End.one_apply]⟩, by
      intro k; by_cases hk : k = i <;> simp [hk, Pi.single_apply], hi⟩
  have hsub : descSet hA π (x * cs.simple i) ⊆
      (weylAction hA (cs.simple i)) '' (descSet hA π x \ {Pi.single i 1}) := by
    rintro γ ⟨⟨w, j, rfl⟩, hγ, hneg⟩
    have hne : weylAction hA w (Pi.single j 1) ≠ Pi.single i 1 := by
      intro heq
      rw [heq, weylAction_mul_apply, weylAction_simple_single, map_neg, coneNeg_neg_iff] at hneg
      exact not_conePos_and_coneNeg hind (weylAction_single_ne_zero hA x i) hneg hi
    refine ⟨weylAction hA (cs.simple i) (weylAction hA w (Pi.single j 1)),
      ⟨⟨⟨cs.simple i * w, j, by rw [weylAction_mul_apply]⟩,
        weylAction_simple_nonneg hA hγ hne, by rwa [← weylAction_mul_apply]⟩, ?_⟩, ?_⟩
    · intro heq
      rw [Set.mem_singleton_iff] at heq
      have h2 := congrArg (weylAction hA (cs.simple i)) heq
      rw [← weylAction_mul_apply, cs.simple_mul_simple_self, map_one, Module.End.one_apply,
        weylAction_simple_single] at h2
      have := hγ i
      rw [h2] at this
      exact absurd this (by simp)
    · rw [← weylAction_mul_apply, cs.simple_mul_simple_self, map_one, Module.End.one_apply]
  calc (descSet hA π (x * cs.simple i)).ncard
      ≤ ((weylAction hA (cs.simple i)) '' (descSet hA π x \ {Pi.single i 1})).ncard :=
        Set.ncard_le_ncard hsub (((descSet_finite hA x).diff).image _)
    _ ≤ (descSet hA π x \ {Pi.single i 1}).ncard :=
        Set.ncard_image_le (descSet_finite hA x).diff
    _ < (descSet hA π x).ncard := Set.ncard_diff_singleton_lt_of_mem hmem (descSet_finite hA x)

theorem exists_forall_not_coneNeg (hind : LinearIndependent ℤ π) :
    ∃ x : (coxeterMatrix hA).Group, ∀ i, ¬ ConeNeg π (weylAction hA x (Pi.single i 1)) := by
  suffices h : ∀ n, ∀ x : (coxeterMatrix hA).Group, (descSet hA π x).ncard = n →
      ∃ x : (coxeterMatrix hA).Group, ∀ i, ¬ ConeNeg π (weylAction hA x (Pi.single i 1)) from
    h _ 1 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx
    by_cases H : ∀ i, ¬ ConeNeg π (weylAction hA x (Pi.single i 1))
    · exact ⟨x, H⟩
    push Not at H
    obtain ⟨i, hi⟩ := H
    exact ih _ (hx ▸ ncard_descSet_mul_lt hA hind hi) _ rfl

end Descent

theorem weylAction_eq_linearCombination_sum {κ : Type} [Fintype κ] {π : κ → I → ℤ}
    (x : (coxeterMatrix hA).Group) (d : I → κ → ℤ)
    (hd : ∀ i, weylAction hA x (Pi.single i 1) = Fintype.linearCombination ℤ π (d i))
    (γ : I → ℤ) :
    weylAction hA x γ = Fintype.linearCombination ℤ π (∑ i, γ i • d i) := by
  have hγ : γ = ∑ i, γ i • (Pi.single i 1 : I → ℤ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hγ]
  simp only [map_sum, map_zsmul, hd]

theorem exists_weylAction_eq_of_cone {κ : Type} [Fintype κ] (π : κ → I → ℤ)
    (hπ : ∀ k, ∃ (w : (coxeterMatrix hA).Group) (i : I), π k = weylAction hA w (Pi.single i 1))
    (hind : LinearIndependent ℤ π)
    (hcone : ∀ (w : (coxeterMatrix hA).Group) (i : I), ∃ x : κ → ℤ, (0 ≤ x ∨ x ≤ 0) ∧
      weylAction hA w (Pi.single i 1) = Fintype.linearCombination ℤ π x) :
    ∃ (u : (coxeterMatrix hA).Group) (σ : I ≃ κ),
      ∀ i, weylAction hA u (Pi.single i 1) = π (σ i) := by
  classical
  set φ := Fintype.linearCombination ℤ π with hφ
  have hinj : Function.Injective φ :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp hind
  have hcone' : ∀ (w : (coxeterMatrix hA).Group) (i : I),
      ConePos π (weylAction hA w (Pi.single i 1)) ∨
        ConeNeg π (weylAction hA w (Pi.single i 1)) := by
    intro w i
    obtain ⟨y, hy | hy, he⟩ := hcone w i
    · exact Or.inl ⟨y, hy, he⟩
    · exact Or.inr ⟨y, hy, he⟩
  obtain ⟨x, hx⟩ := exists_forall_not_coneNeg hA hind
  have hpos : ∀ i, ConePos π (weylAction hA x (Pi.single i 1)) := fun i =>
    (hcone' x i).resolve_right (hx i)
  choose d hd0 hd using hpos
  have hπk : ∀ k, φ (Pi.single k 1) = π k := fun k => by
    rw [hφ, Fintype.linearCombination_apply_single, one_smul]
  have hc0 : ∀ k, 0 ≤ weylAction hA x⁻¹ (π k) := by
    intro k
    obtain ⟨w, i, hwi⟩ := hπ k
    rcases weylAction_single_nonneg_or_nonpos hA (x⁻¹ * w) i with h | h
    · rwa [weylAction_mul_apply, ← hwi] at h
    exfalso
    rw [weylAction_mul_apply, ← hwi] at h
    set c := weylAction hA x⁻¹ (π k) with hc
    have hcn : 0 ≤ -c := neg_nonneg.mpr h
    have hxc : weylAction hA x (-c) = -π k := by
      rw [map_neg, hc, weylAction_apply_inv_apply]
    have hP : ConePos π (-π k) := by
      rw [← hxc, weylAction_eq_linearCombination_sum hA x d hd]
      refine ⟨_, fun l => ?_, rfl⟩
      rw [Finset.sum_apply]
      exact Finset.sum_nonneg fun i _ => by
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (hcn i) (hd0 i l)
    have hπ0 : π k ≠ 0 := by
      rw [hwi]; exact weylAction_single_ne_zero hA w i
    exact not_conePos_and_coneNeg hind hπ0
      ⟨Pi.single k 1, fun l => by by_cases hl : l = k <;> simp [hl, Pi.single_apply], (hπk k).symm⟩
      (coneNeg_neg_iff.mpr hP |> fun h => by rwa [neg_neg] at h)
  have hcd : ∀ k, ∑ i, weylAction hA x⁻¹ (π k) i • d i = Pi.single k 1 := by
    intro k
    apply hinj
    rw [← weylAction_eq_linearCombination_sum hA x d hd, weylAction_apply_inv_apply, hπk]
  have hτ : ∀ k, ∃ i, d i = Pi.single k 1 := by
    intro k
    obtain ⟨c, hcdef⟩ : ∃ c, c = weylAction hA x⁻¹ (π k) := ⟨_, rfl⟩
    have hc0' : ∀ i, 0 ≤ c i := fun i => by rw [hcdef]; exact hc0 k i
    have hd0' : ∀ i l, 0 ≤ d i l := fun i l => hd0 i l
    have hsum : ∀ l, ∑ i, c i * d i l = (Pi.single k 1 : κ → ℤ) l := fun l => by
      rw [← hcd k, Finset.sum_apply, hcdef]
      simp [smul_eq_mul]
    have hnn : ∀ l i, 0 ≤ c i * d i l := fun l i => mul_nonneg (hc0' i) (hd0' i l)
    have h1 : ∑ i, c i * d i k ≠ 0 := by rw [hsum k]; simp
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    refine ⟨i, funext fun l => ?_⟩
    have hle : c i * d i l ≤ (Pi.single k 1 : κ → ℤ) l := by
      rw [← hsum l]
      exact Finset.single_le_sum (fun j _ => hnn l j) (Finset.mem_univ i)
    have hci : 1 ≤ c i := by
      rcases eq_or_lt_of_le (hc0' i) with h | h
      · exact absurd (by rw [← h, zero_mul]) hi
      · omega
    have hdik : 1 ≤ d i k := by
      rcases eq_or_lt_of_le (hd0' i k) with h | h
      · exact absurd (by rw [← h, mul_zero]) hi
      · omega
    have hdl := hd0' i l
    by_cases hl : l = k
    · subst hl
      simp only [Pi.single_eq_same] at hle ⊢
      nlinarith
    · simp only [Pi.single_eq_of_ne hl] at hle ⊢
      nlinarith
  choose τ hτd using hτ
  have hxτ : ∀ k, weylAction hA x (Pi.single (τ k) 1) = π k := fun k => by
    rw [hd, hτd, hπk]
  have hτinj : Function.Injective τ := fun k l hkl =>
    hind.injective (by rw [← hxτ k, ← hxτ l, hkl])
  have hτsurj : Function.Surjective τ := by
    intro i
    by_contra hni
    push Not at hni
    have hαi : (Pi.single i 1 : I → ℤ) = ∑ l, d i l • Pi.single (τ l) 1 := by
      have := weylAction_inv_apply_apply hA x (Pi.single i 1)
      rw [hd, Fintype.linearCombination_apply, map_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_zsmul, ← hxτ l, weylAction_inv_apply_apply]
    have := congrFun hαi i
    simp [Finset.sum_apply, Pi.single_apply, Ne.symm (hni _)] at this
  refine ⟨x, (Equiv.ofBijective τ ⟨hτinj, hτsurj⟩).symm, fun i => ?_⟩
  have := hxτ ((Equiv.ofBijective τ ⟨hτinj, hτsurj⟩).symm i)
  rwa [show τ ((Equiv.ofBijective τ ⟨hτinj, hτsurj⟩).symm i) = i from
    Equiv.ofBijective_apply_symm_apply τ _ i] at this

end CFSG.StandardType.S2MathFi1451
