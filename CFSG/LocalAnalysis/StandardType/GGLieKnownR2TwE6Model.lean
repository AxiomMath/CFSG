module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Data

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.StandardType

@[expose] def twE6ShiftMap {k : Type} [AddCommMonoid k] (j : Fin 12) (m : Fin 8 → k) :
    Fin 8 → k :=
  fun i' => ∑ i ∈ Finset.univ.filter (fun i => twE6Shift j i = some i'), m i

@[expose] def twE6TorusMap {k : Type} [Field k] (θ : k →+* k) (t : k) (m : Fin 8 → k) :
    Fin 8 → k :=
  fun i => t ^ twE6Exp2 i * θ t ^ twE6Exp4 i * m i

@[expose] def twE6PermMap {k : Type} (m : Fin 8 → k) : Fin 8 → k :=
  fun i => m (twE6Perm i)

private def twE6ShiftSucc (j : Fin 12) (i : Fin 8) : Fin 8 :=
  (twE6Shift j i).getD i

private def twE6ReachStep (s : Finset (Fin 8)) : Finset (Fin 8) :=
  s ∪ s.image twE6Perm ∪
    (Finset.univ : Finset (Fin 12)).biUnion
      (fun j => (s.filter (fun i => (twE6Shift j i).isSome)).image (twE6ShiftSucc j))

private theorem twE6_shift_sep :
    ∀ i i' : Fin 8, i ≠ i' → ∃ j : Fin 12,
      (∃ i₀, twE6Shift j i = some i₀ ∧ twE6Shift j i' = none) ∨
      (∃ i₀, twE6Shift j i' = some i₀ ∧ twE6Shift j i = none) := by
  decide +kernel

private theorem twE6_shift_inj :
    ∀ j : Fin 12, ∀ i i' i'' : Fin 8,
      twE6Shift j i = some i'' → twE6Shift j i' = some i'' → i = i' := by
  decide +kernel

private theorem twE6_perm_involutive : ∀ i : Fin 8, twE6Perm (twE6Perm i) = i := by
  decide +kernel

private theorem twE6_reach_univ : ∀ i : Fin 8, (twE6ReachStep^[8]) {i} = Finset.univ := by
  decide +kernel

private lemma twE6_shift_filter_eq_singleton {j : Fin 12} {i i'' : Fin 8}
    (h : twE6Shift j i = some i'') :
    (Finset.univ.filter fun k => twE6Shift j k = some i'') = {i} := by
  apply Finset.eq_singleton_iff_unique_mem.2
  refine ⟨Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩, ?_⟩
  intro k hk
  exact twE6_shift_inj j k i i'' (Finset.mem_filter.1 hk).2 h

private lemma twE6ShiftMap_apply_of_shift {k : Type} [Field k]
    (j : Fin 12) (m : Fin 8 → k) {i i'' : Fin 8} (h : twE6Shift j i = some i'') :
    twE6ShiftMap j m i'' = m i := by
  rw [twE6ShiftMap, twE6_shift_filter_eq_singleton h, Finset.sum_singleton]

private lemma exists_shift_of_shiftMap_ne_zero {k : Type} [Field k]
    (j : Fin 12) (m : Fin 8 → k) {i'' : Fin 8}
    (h : twE6ShiftMap j m i'' ≠ 0) : ∃ i, twE6Shift j i = some i'' := by
  by_contra hc
  push Not at hc
  apply h
  rw [twE6ShiftMap]
  apply Finset.sum_eq_zero
  intro i hi
  exact absurd (Finset.mem_filter.1 hi).2 (hc i)

private lemma twE6ShiftMap_single_of_shift {k : Type} [Field k]
    (j : Fin 12) (i i' : Fin 8) (x : k) (h : twE6Shift j i = some i') :
    twE6ShiftMap j (Pi.single i x) = Pi.single i' x := by
  funext i''
  by_cases hii : i'' = i'
  · subst hii
    rw [twE6ShiftMap_apply_of_shift j (Pi.single i x) h]
    simp
  · have hz : twE6ShiftMap j (Pi.single i x) i'' = 0 := by
      rw [twE6ShiftMap]
      apply Finset.sum_eq_zero
      intro k hk
      have hk' : twE6Shift j k = some i'' := (Finset.mem_filter.1 hk).2
      have hki : k ≠ i := by
        intro hki
        subst hki
        rw [h] at hk'
        exact hii (Option.some.inj hk').symm
      rw [Pi.single_eq_of_ne hki]
    rw [hz, Pi.single_eq_of_ne hii]

private lemma twE6_shiftSucc_injOn (j : Fin 12) (s : Finset (Fin 8))
    (hs : ∀ i ∈ s, (twE6Shift j i).isSome = true) :
    Set.InjOn (twE6ShiftSucc j) (↑s : Set (Fin 8)) := by
  intro a ha b hb hab
  have ha' := hs a ha
  have hb' := hs b hb
  unfold twE6ShiftSucc at hab
  cases hao : twE6Shift j a with
  | none => rw [hao] at ha'; simp at ha'
  | some a' =>
    cases hbo : twE6Shift j b with
    | none => rw [hbo] at hb'; simp at hb'
    | some b' =>
      have hab' : a' = b' := by rw [hao, hbo] at hab; simpa using hab
      subst hab'
      exact twE6_shift_inj j a b a' hao hbo

private lemma twE6_support_shiftMap {k : Type} [Field k] [DecidableEq k]
    (j : Fin 12) (m : Fin 8 → k) :
    (Finset.univ.filter fun i'' => twE6ShiftMap j m i'' ≠ 0) =
      ((Finset.univ.filter fun i => m i ≠ 0).filter fun i =>
        (twE6Shift j i).isSome).image (twE6ShiftSucc j) := by
  classical
  ext i''
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_shift_of_shiftMap_ne_zero j m h
    exact ⟨i, ⟨by rwa [twE6ShiftMap_apply_of_shift j m hi] at h, by rw [hi]; rfl⟩,
      by simp [twE6ShiftSucc, hi]⟩
  · rintro ⟨i, ⟨hmi, his⟩, hsucc⟩
    subst hsucc
    unfold twE6ShiftSucc
    cases hsh : twE6Shift j i with
    | none => rw [hsh] at his; simp at his
    | some i' =>
      change twE6ShiftMap j m i' ≠ 0
      rw [twE6ShiftMap_apply_of_shift j m hsh]
      exact hmi

private lemma twE6_support_shiftMap_card_lt {k : Type} [Field k] [DecidableEq k]
    (j : Fin 12) (m : Fin 8 → k)
    {i' : Fin 8} (hmi' : m i' ≠ 0)
    (hi' : twE6Shift j i' = none) :
    (Finset.univ.filter fun i'' => twE6ShiftMap j m i'' ≠ 0).card <
      (Finset.univ.filter fun i => m i ≠ 0).card := by
  classical
  set A : Finset (Fin 8) := Finset.univ.filter fun i => m i ≠ 0 with hA
  set B : Finset (Fin 8) := A.filter fun i => (twE6Shift j i).isSome with hB
  have hsupp : (Finset.univ.filter fun i'' => twE6ShiftMap j m i'' ≠ 0) =
      B.image (twE6ShiftSucc j) := by
    rw [twE6_support_shiftMap j m]
  rw [hsupp]
  have hinj : Set.InjOn (twE6ShiftSucc j) (↑B : Set (Fin 8)) := by
    apply twE6_shiftSucc_injOn
    intro i hi
    rw [hB] at hi
    exact (Finset.mem_filter.1 hi).2
  rw [Finset.card_image_of_injOn hinj]
  have hne : B ≠ A := by
    intro hEq
    have : i' ∈ B := by
      rw [hEq]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ i', hmi'⟩
    rw [hB, Finset.mem_filter] at this
    obtain ⟨-, his⟩ := this
    rw [hi'] at his
    simp at his
  have hssub : B ⊂ A := Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, hne⟩
  exact Finset.card_lt_card hssub

private lemma twE6ShiftMap_mem {k : Type} [Field k] (j : Fin 12) (m : Fin 8 → k)
    (W : AddSubgroup (Fin 8 → k))
    (hshift : ∀ j : Fin 12, ∀ m ∈ W, m + twE6ShiftMap j m ∈ W) (hm : m ∈ W) :
    twE6ShiftMap j m ∈ W := by
  have h := W.sub_mem (hshift j m hm) hm
  simpa using h

private lemma twE6PermMap_single {k : Type} [Zero k] (i : Fin 8) (x : k) :
    twE6PermMap (Pi.single i x) = Pi.single (twE6Perm i) x := by
  funext j
  simp only [twE6PermMap, Pi.single_apply]
  by_cases hj : twE6Perm j = i
  · rw [if_pos hj]
    have : j = twE6Perm i := by
      have := congrArg twE6Perm hj
      simpa [twE6_perm_involutive] using this
    rw [if_pos this]
  · rw [if_neg hj]
    have : j ≠ twE6Perm i := fun h => hj (by rw [h, twE6_perm_involutive])
    rw [if_neg this]

private lemma twE6TorusMap_single {k : Type} [Field k] (θ : k →+* k) (t : k)
    (i : Fin 8) (x : k) :
    twE6TorusMap θ t (Pi.single i x) =
      Pi.single i (t ^ twE6Exp2 i * θ t ^ twE6Exp4 i * x) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [twE6TorusMap]
  · simp [twE6TorusMap, Pi.single_eq_of_ne hj]

private def twE6ScalarMap {k : Type} [Field k] (i : Fin 8) (c : k) : k →+ (Fin 8 → k) where
  toFun x := Pi.single i (c * x)
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Pi.single_add]

private lemma twE6ScalarMap_apply {k : Type} [Field k] (i : Fin 8) (c : k) (x : k) :
    twE6ScalarMap i c x = Pi.single i (c * x) := rfl

private lemma twE6TorusMu_mem {k : Type} [Field k] (θ : k →+* k) (t : k) (i : Fin 8) :
    t ^ twE6Exp2 i * θ t ^ twE6Exp4 i = t ∨
    t ^ twE6Exp2 i * θ t ^ twE6Exp4 i = t⁻¹ ∨
    t ^ twE6Exp2 i * θ t ^ twE6Exp4 i = θ t ∨
    t ^ twE6Exp2 i * θ t ^ twE6Exp4 i = (θ t)⁻¹ := by
  fin_cases i <;> simp [twE6Exp2, twE6Exp4]

private lemma mul_inv_closure {k : Type} [Field k] [Finite k]
    (S : AddSubgroup k) (μ : k) (hμ : μ ≠ 0)
    (h : ∀ x ∈ S, μ * x ∈ S) : ∀ x ∈ S, μ⁻¹ * x ∈ S := by
  haveI : Finite ↥S := inferInstance
  set φ : ↥S → ↥S := fun x => ⟨μ * x.1, h x.1 x.2⟩ with hφ
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hxy' : μ * x.1 = μ * y.1 := congrArg Subtype.val hxy
    exact Subtype.ext (mul_left_cancel₀ hμ hxy')
  have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.1 hφinj
  intro x hx
  obtain ⟨y, hy⟩ := hφsurj ⟨x, hx⟩
  have hyv : μ * y.1 = x := congrArg Subtype.val hy
  have : y.1 = μ⁻¹ * x := by
    rw [← hyv, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul]
  rw [← this]
  exact y.2

private lemma comap_theta_eq_top {k : Type} [Field k]
    (θ : k →+* k) (hθ : Function.Surjective θ) {t : k}
    (ht : ∀ S : AddSubgroup k, (1 : k) ∈ S → (∀ x ∈ S, t * x ∈ S) → S = ⊤)
    (S : AddSubgroup k) (h1 : 1 ∈ S) (h : ∀ x ∈ S, θ t * x ∈ S) : S = ⊤ := by
  let S' : AddSubgroup k := S.comap θ.toAddMonoidHom
  have h1' : (1 : k) ∈ S' := by
    rw [AddSubgroup.mem_comap]
    simpa using h1
  have hcl : ∀ x ∈ S', t * x ∈ S' := by
    intro x hx
    rw [AddSubgroup.mem_comap] at hx ⊢
    change θ (t * x) ∈ S
    rw [map_mul]
    exact h (θ x) hx
  have htop : S' = ⊤ := ht S' h1' hcl
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hθ y
  have : x ∈ S' := by rw [htop]; trivial
  rwa [AddSubgroup.mem_comap] at this

private lemma scalar_eq_top_of_mu {k : Type} [Field k] [Finite k]
    (θ : k →+* k) (hθ : Function.Surjective θ) {t : k}
    (ht : ∀ S : AddSubgroup k, (1 : k) ∈ S → (∀ x ∈ S, t * x ∈ S) → S = ⊤)
    (S : AddSubgroup k) (h1 : 1 ∈ S) (μ : k)
    (hμ : μ = t ∨ μ = t⁻¹ ∨ μ = θ t ∨ μ = (θ t)⁻¹)
    (hμS : ∀ x ∈ S, μ * x ∈ S) : S = ⊤ := by
  by_cases ht0 : t = 0
  · apply ht S h1
    intro x _
    rw [ht0, zero_mul]
    exact S.zero_mem
  · have hθt0 : θ t ≠ 0 := by
      intro h
      exact ht0 (RingHom.injective θ (by rw [h, map_zero]))
    rcases hμ with rfl | rfl | rfl | rfl
    · exact ht S h1 hμS
    · have hcl : ∀ x ∈ S, t * x ∈ S := by
        have := mul_inv_closure S t⁻¹ (inv_ne_zero ht0) hμS
        simpa using this
      exact ht S h1 hcl
    · exact comap_theta_eq_top θ hθ ht S h1 hμS
    · have hcl : ∀ x ∈ S, θ t * x ∈ S := by
        have := mul_inv_closure S (θ t)⁻¹ (inv_ne_zero hθt0) hμS
        simpa using this
      exact comap_theta_eq_top θ hθ ht S h1 hcl

private lemma single_mem_of_single_mul_mem {k : Type} [Field k] [Finite k]
    (θ : k →+* k) (hθ : Function.Surjective θ) {t : k}
    (ht : ∀ S : AddSubgroup k, (1 : k) ∈ S → (∀ x ∈ S, t * x ∈ S) → S = ⊤)
    (W : AddSubgroup (Fin 8 → k))
    (htorus : ∀ m ∈ W, twE6TorusMap θ t m ∈ W)
    {i : Fin 8} {c : k} (hc : c ≠ 0) (h : Pi.single i c ∈ W) :
    ∀ x : k, Pi.single i x ∈ W := by
  have htop : W.comap (twE6ScalarMap i c) = ⊤ := by
    refine scalar_eq_top_of_mu θ hθ ht (W.comap (twE6ScalarMap i c)) ?_
      (t ^ twE6Exp2 i * θ t ^ twE6Exp4 i) ?_ ?_
    · rw [AddSubgroup.mem_comap, twE6ScalarMap_apply]
      simpa using h
    · exact twE6TorusMu_mem θ t i
    · intro z hz
      rw [AddSubgroup.mem_comap] at hz ⊢
      have hmem : twE6TorusMap θ t (twE6ScalarMap i c z) ∈ W := htorus _ hz
      have hEq : twE6TorusMap θ t (twE6ScalarMap i c z) =
          twE6ScalarMap i c (t ^ twE6Exp2 i * θ t ^ twE6Exp4 i * z) := by
        rw [twE6ScalarMap_apply, twE6TorusMap_single, twE6ScalarMap_apply, Pi.single_inj]
        ac_rfl
      rwa [hEq] at hmem
  intro x
  have hS : c⁻¹ * x ∈ W.comap (twE6ScalarMap i c) := by rw [htop]; trivial
  rw [AddSubgroup.mem_comap] at hS
  have hmul : c * (c⁻¹ * x) = x := by
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [twE6ScalarMap_apply] at hS
  simpa [hmul] using hS

private lemma exists_single_mem {k : Type} [Field k] [DecidableEq k]
    (W : AddSubgroup (Fin 8 → k))
    (hshift : ∀ j : Fin 12, ∀ m ∈ W, m + twE6ShiftMap j m ∈ W) :
    ∀ m ∈ W, m ≠ 0 → ∃ (c : k) (i : Fin 8), c ≠ 0 ∧ Pi.single i c ∈ W := by
  suffices h : ∀ n, ∀ m ∈ W, m ≠ 0 →
      (Finset.univ.filter fun i => m i ≠ 0).card = n →
      ∃ (c : k) (i : Fin 8), c ≠ 0 ∧ Pi.single i c ∈ W by
    intro m hmW hm0
    exact h _ m hmW hm0 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hmW hm0 hcard
    by_cases hcard1 : (Finset.univ.filter fun i => m i ≠ 0).card = 1
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.1 hcard1
      have hmi : m i ≠ 0 := by
        have hmem : i ∈ Finset.univ.filter fun i => m i ≠ 0 := by rw [hi]; simp
        exact (Finset.mem_filter.1 hmem).2
      refine ⟨m i, i, hmi, ?_⟩
      have hs : Pi.single i (m i) = m := by
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · have hjn : j ∉ Finset.univ.filter fun i => m i ≠ 0 := by rw [hi]; simp [hj]
          rw [Finset.mem_filter] at hjn
          simp only [Finset.mem_univ, true_and, not_not] at hjn
          rw [hjn, Pi.single_eq_of_ne hj]
      rw [hs]; exact hmW
    · have hne0 : (Finset.univ.filter fun i => m i ≠ 0).card ≠ 0 := by
        intro h0
        apply hm0
        funext i
        have hmem : i ∉ Finset.univ.filter fun i => m i ≠ 0 := by
          rw [Finset.card_eq_zero.1 h0]; simp
        rw [Finset.mem_filter] at hmem
        simpa using hmem
      have h2 : 1 < (Finset.univ.filter fun i => m i ≠ 0).card := by omega
      obtain ⟨i, hiA, i', hi'A, hne⟩ := Finset.one_lt_card.1 h2
      have hmi : m i ≠ 0 := (Finset.mem_filter.1 hiA).2
      have hmi' : m i' ≠ 0 := (Finset.mem_filter.1 hi'A).2
      obtain ⟨j, hcase | hcase⟩ := twE6_shift_sep i i' hne
      · obtain ⟨i₀, hii₀, hi'none⟩ := hcase
        have hmem : twE6ShiftMap j m ∈ W := twE6ShiftMap_mem j m W hshift hmW
        have hnz : twE6ShiftMap j m ≠ 0 := by
          intro h0
          have h1 := twE6ShiftMap_apply_of_shift j m hii₀
          rw [h0] at h1
          exact hmi h1.symm
        have hcardlt : (Finset.univ.filter fun i'' => twE6ShiftMap j m i'' ≠ 0).card < n := by
          rw [← hcard]
          exact twE6_support_shiftMap_card_lt j m hmi' hi'none
        exact ih _ hcardlt (twE6ShiftMap j m) hmem hnz rfl
      · obtain ⟨i₀, hi'i₀, hinone⟩ := hcase
        have hmem : twE6ShiftMap j m ∈ W := twE6ShiftMap_mem j m W hshift hmW
        have hnz : twE6ShiftMap j m ≠ 0 := by
          intro h0
          have h1 := twE6ShiftMap_apply_of_shift j m hi'i₀
          rw [h0] at h1
          exact hmi' h1.symm
        have hcardlt : (Finset.univ.filter fun i'' => twE6ShiftMap j m i'' ≠ 0).card < n := by
          rw [← hcard]
          exact twE6_support_shiftMap_card_lt j m hmi hinone
        exact ih _ hcardlt (twE6ShiftMap j m) hmem hnz rfl

private lemma single_mem_reachStep {k : Type} [Field k]
    (W : AddSubgroup (Fin 8 → k)) (x : k)
    (hshift : ∀ j : Fin 12, ∀ m ∈ W, m + twE6ShiftMap j m ∈ W)
    (hperm : ∀ m ∈ W, twE6PermMap m ∈ W)
    {s : Finset (Fin 8)} (hs : ∀ i ∈ s, Pi.single i x ∈ W) :
    ∀ i ∈ twE6ReachStep s, Pi.single i x ∈ W := by
  intro i hi
  rw [twE6ReachStep] at hi
  simp only [Finset.mem_union] at hi
  rcases hi with (hi | hi) | hi
  · exact hs i hi
  · rw [Finset.mem_image] at hi
    obtain ⟨i₀, hi₀, rfl⟩ := hi
    have := hperm (Pi.single i₀ x) (hs i₀ hi₀)
    rwa [twE6PermMap_single] at this
  · rw [Finset.mem_biUnion] at hi
    obtain ⟨j, -, hi⟩ := hi
    rw [Finset.mem_image] at hi
    obtain ⟨i₀, hi₀, rfl⟩ := hi
    rw [Finset.mem_filter] at hi₀
    obtain ⟨hi₀s, hisome⟩ := hi₀
    obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.1 hisome
    have hbase := hs i₀ hi₀s
    have hmem : twE6ShiftMap j (Pi.single i₀ x) ∈ W := twE6ShiftMap_mem j _ W hshift hbase
    have hSucc : twE6ShiftSucc j i₀ = i' := by simp [twE6ShiftSucc, hi']
    rw [hSucc]
    rw [twE6ShiftMap_single_of_shift j i₀ i' x hi'] at hmem
    exact hmem

private lemma single_mem_reachStep_iter {k : Type} [Field k]
    (W : AddSubgroup (Fin 8 → k)) (x : k)
    (hshift : ∀ j : Fin 12, ∀ m ∈ W, m + twE6ShiftMap j m ∈ W)
    (hperm : ∀ m ∈ W, twE6PermMap m ∈ W) :
    ∀ n : ℕ, ∀ s : Finset (Fin 8),
      (∀ i ∈ s, Pi.single i x ∈ W) →
      ∀ i ∈ (twE6ReachStep^[n]) s, Pi.single i x ∈ W := by
  intro n
  induction n with
  | zero => intro s hs i hi; simpa using hs i hi
  | succ n ih =>
    intro s hs i hi
    rw [Function.iterate_succ_apply] at hi
    exact ih (twE6ReachStep s) (single_mem_reachStep W x hshift hperm hs) i hi

theorem twE6_model_irreducible
    {k : Type} [Field k] [Finite k] (θ : k →+* k) (hθ : Function.Surjective θ) {t : k}
    (ht : ∀ S : AddSubgroup k, (1 : k) ∈ S → (∀ x ∈ S, t * x ∈ S) → S = ⊤)
    (W : AddSubgroup (Fin 8 → k))
    (hshift : ∀ (j : Fin 12), ∀ m ∈ W, m + twE6ShiftMap j m ∈ W)
    (htorus : ∀ m ∈ W, twE6TorusMap θ t m ∈ W)
    (hperm : ∀ m ∈ W, twE6PermMap m ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · refine Or.inr ?_
    have hex : ∃ m ∈ W, m ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hbot (by rw [eq_bot_iff]; intro m hm; exact hc m hm)
    obtain ⟨m0, hm0W, hm00⟩ := hex
    obtain ⟨c0, i0, hc0, hsingle0⟩ := exists_single_mem W hshift m0 hm0W hm00
    have hscalar : ∀ x : k, Pi.single i0 x ∈ W :=
      single_mem_of_single_mul_mem θ hθ ht W htorus hc0 hsingle0
    have hall : ∀ (i : Fin 8) (x : k), Pi.single i x ∈ W := by
      intro i x
      have hgood0 : ∀ j ∈ ({i0} : Finset (Fin 8)), Pi.single j x ∈ W := by
        intro j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact hscalar x
      have hmem : ∀ j ∈ (twE6ReachStep^[8]) {i0}, Pi.single j x ∈ W :=
        single_mem_reachStep_iter W x hshift hperm 8 {i0} hgood0
      rw [twE6_reach_univ i0] at hmem
      exact hmem i (Finset.mem_univ i)
    apply le_antisymm le_top
    intro m _
    rw [← Finset.univ_sum_single m]
    exact W.sum_mem fun i _ => hall i (m i)

end CFSG.StandardType.LieKnownR2.Short
