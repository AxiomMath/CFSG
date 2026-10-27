module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Algebra.CharP.Two
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.CentralCover

variable {X : Type*} [Group X]

@[expose] def IsCocycle₂ (d : X × X → ZMod 2) : Prop :=
  ∀ g h k, d (g * h, k) + d (g, h) = d (h, k) + d (g, h * k)

@[expose] def IsCoboundary₂ (d : X × X → ZMod 2) : Prop :=
  ∃ s : X → ZMod 2, ∀ g h, d (g, h) = s h - s (g * h) + s g

structure Cocycle₂ (X : Type*) [Group X] where
  f : X × X → ZMod 2
  cond : IsCocycle₂ f

@[ext] structure CExt (c : Cocycle₂ X) where
  fst : ZMod 2
  snd : X

namespace CExt

variable (c : Cocycle₂ X)

theorem f_one_left (g : X) : c.f (1, g) = c.f (1, 1) := by
  have h := c.cond 1 1 g
  rw [one_mul, one_mul] at h
  exact (add_left_cancel h).symm

theorem f_one_right (g : X) : c.f (g, 1) = c.f (1, 1) := by
  have h := c.cond g 1 1
  rw [mul_one, mul_one] at h
  exact add_right_cancel h

instance : Mul (CExt c) := ⟨fun x y => ⟨x.fst + y.fst + c.f (x.snd, y.snd), x.snd * y.snd⟩⟩

instance : One (CExt c) := ⟨⟨-c.f (1, 1), 1⟩⟩

instance : Inv (CExt c) := ⟨fun x => ⟨-c.f (1, 1) - x.fst - c.f (x.snd⁻¹, x.snd), x.snd⁻¹⟩⟩

theorem mul_fst (x y : CExt c) : (x * y).fst = x.fst + y.fst + c.f (x.snd, y.snd) := rfl

theorem mul_snd (x y : CExt c) : (x * y).snd = x.snd * y.snd := rfl

theorem one_snd : (1 : CExt c).snd = 1 := rfl

theorem inv_snd (x : CExt c) : x⁻¹.snd = x.snd⁻¹ := rfl

instance : Group (CExt c) :=
  Group.ofLeftAxioms
    (fun x y z => by
      refine CExt.ext ?_ (mul_assoc x.snd y.snd z.snd)
      change x.fst + y.fst + c.f (x.snd, y.snd) + z.fst + c.f (x.snd * y.snd, z.snd) =
        x.fst + (y.fst + z.fst + c.f (y.snd, z.snd)) + c.f (x.snd, y.snd * z.snd)
      linear_combination c.cond x.snd y.snd z.snd)
    (fun x => by
      refine CExt.ext ?_ (one_mul x.snd)
      change -c.f (1, 1) + x.fst + c.f (1, x.snd) = x.fst
      rw [f_one_left c x.snd]
      ring)
    (fun x => by
      refine CExt.ext ?_ (inv_mul_cancel x.snd)
      change -c.f (1, 1) - x.fst - c.f (x.snd⁻¹, x.snd) + x.fst + c.f (x.snd⁻¹, x.snd) =
        -c.f (1, 1)
      ring)

@[expose] def snd' : CExt c →* X where
  toFun x := x.snd
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def ι (a : ZMod 2) : CExt c := ⟨a - c.f (1, 1), 1⟩

theorem ι_snd (a : ZMod 2) : (ι c a).snd = 1 := rfl

theorem ι_fst (a : ZMod 2) : (ι c a).fst = a - c.f (1, 1) := rfl

theorem ι_add (a b : ZMod 2) : ι c (a + b) = ι c a * ι c b := by
  refine CExt.ext ?_ (mul_one (1 : X)).symm
  change a + b - c.f (1, 1) = a - c.f (1, 1) + (b - c.f (1, 1)) + c.f (1, 1)
  ring

theorem ι_central (x : CExt c) (a : ZMod 2) : x * ι c a = ι c a * x := by
  refine CExt.ext ?_ ((mul_one x.snd).trans (one_mul x.snd).symm)
  change x.fst + (a - c.f (1, 1)) + c.f (x.snd, 1) = a - c.f (1, 1) + x.fst + c.f (1, x.snd)
  rw [f_one_left c x.snd, f_one_right c x.snd]
  ring

theorem ι_zero : ι c 0 = 1 := by
  have h := ι_add c 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem ι_inv (a : ZMod 2) : (ι c a)⁻¹ = ι c a := by
  apply inv_eq_of_mul_eq_one_left
  rw [← ι_add, CharTwo.add_self_eq_zero, ι_zero]

theorem eq_ι_of_snd {x : CExt c} (hx : x.snd = 1) : x = ι c (x.fst + c.f (1, 1)) :=
  CExt.ext (add_sub_cancel_right _ _).symm hx

theorem ι_one_ne_one : ι c 1 ≠ 1 := by
  intro h
  have h1 : (1 : ZMod 2) - c.f (1, 1) = -c.f (1, 1) := congrArg CExt.fst h
  exact one_ne_zero (sub_eq_neg_self.mp h1)

theorem eq_one_or_eq_ι_one {x : CExt c} (hx : x.snd = 1) : x = 1 ∨ x = ι c 1 := by
  rw [eq_ι_of_snd c hx]
  generalize x.fst + c.f (1, 1) = b
  fin_cases b
  · exact Or.inl (ι_zero c)
  · exact Or.inr rfl

theorem card_eq [Finite X] : Nat.card (CExt c) = 2 * Nat.card X := by
  have e : CExt c ≃ ZMod 2 × X :=
    ⟨fun x => (x.fst, x.snd), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod]

instance [Finite X] : Finite (CExt c) :=
  Finite.of_injective (fun x : CExt c => (x.fst, x.snd)) fun _ _ h =>
    CExt.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem sec_mul_sec (x y : X) :
    (⟨0, x⟩ : CExt c) * ⟨0, y⟩ = ι c (c.f (x, y)) * ⟨0, x * y⟩ := by
  refine CExt.ext ?_ (one_mul (x * y)).symm
  change 0 + 0 + c.f (x, y) = c.f (x, y) - c.f (1, 1) + 0 + c.f (1, x * y)
  rw [f_one_left c (x * y)]
  ring

end CExt

open CExt

section Words

variable (c : Cocycle₂ X) {m : ℕ}

theorem sum_map_fst (a : Fin m → ZMod 2) (w : List (Fin m × Bool)) :
    (w.map fun l => a l.1).sum = ∑ j, ((w.countP fun l => l.1 = j : ℕ) : ZMod 2) * a j := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [List.countP_cons, decide_eq_true_eq, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring

theorem lift_adjust (e₀ : Fin m → CExt c) (a : Fin m → ZMod 2) (w : List (Fin m × Bool)) :
    FreeGroup.lift (fun i => e₀ i * ι c (a i)) (FreeGroup.mk w) =
      FreeGroup.lift e₀ (FreeGroup.mk w) * ι c (w.map fun l => a l.1).sum := by
  induction w with
  | nil =>
    simp only [FreeGroup.lift_mk, List.map_nil, List.prod_nil, List.sum_nil, ι_zero, mul_one]
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    have hmk : FreeGroup.mk ((i, b) :: w) = FreeGroup.mk [(i, b)] * FreeGroup.mk w := by
      rw [FreeGroup.mul_mk, List.singleton_append]
    rw [hmk, map_mul, map_mul, ih, List.map_cons, List.sum_cons, ι_add]
    set P := FreeGroup.lift e₀ (FreeGroup.mk w)
    cases b
    · have h1 : FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ := by
        rw [FreeGroup.of, FreeGroup.inv_mk]
        rfl
      rw [h1, map_inv, map_inv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of,
        _root_.mul_inv_rev, ι_inv, ← ι_central c (e₀ i)⁻¹]
      simp only [mul_assoc]
      rw [← mul_assoc (ι c (a i)) P, ← ι_central c P (a i), mul_assoc]
    · have h1 : FreeGroup.mk [(i, true)] = FreeGroup.of i := rfl
      rw [h1, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      simp only [mul_assoc]
      rw [← mul_assoc (ι c (a i)) P, ← ι_central c P (a i), mul_assoc]

theorem snd_lift (e : Fin m → CExt c) (w : FreeGroup (Fin m)) :
    (FreeGroup.lift e w).snd = FreeGroup.lift (fun i => (e i).snd) w := by
  change snd' c (FreeGroup.lift e w) = _
  rw [← MonoidHom.comp_apply]
  congr 1
  exact FreeGroup.ext_hom _ _ fun i => by
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    rfl

end Words

variable {m : ℕ}

@[expose] def commW (i : Fin m) (r : List (Fin m × Bool)) : List (Fin m × Bool) :=
  (i, true) :: r ++ (i, false) :: FreeGroup.invRev r

@[expose] def coverW (R : List (List (Fin m × Bool))) (n : Fin m → List (Fin m × Bool)) :
    List (List (Fin m × Bool)) :=
  (List.finRange m).flatMap (fun i => R.map (commW i)) ++ R.map (fun r => r ++ r) ++
    (List.finRange m).map n

abbrev coverRels (R : List (List (Fin m × Bool))) (n : Fin m → List (Fin m × Bool)) :
    Set (FreeGroup (Fin m)) :=
  {r | r ∈ (coverW R n).map FreeGroup.mk}

theorem mk_commW (i : Fin m) (r : List (Fin m × Bool)) :
    FreeGroup.mk (commW i r) =
      FreeGroup.of i * FreeGroup.mk r * (FreeGroup.of i)⁻¹ * (FreeGroup.mk r)⁻¹ := by
  rw [FreeGroup.inv_mk, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.mul_mk,
    FreeGroup.mul_mk, commW]
  simp [FreeGroup.invRev]

theorem mem_coverW {R : List (List (Fin m × Bool))} {n : Fin m → List (Fin m × Bool)}
    {w : List (Fin m × Bool)} (hw : w ∈ coverW R n) :
    (∃ i, ∃ r ∈ R, w = commW i r) ∨ (∃ r ∈ R, w = r ++ r) ∨ ∃ i, w = n i := by
  simp only [coverW, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_map] at hw
  rcases hw with (⟨i, r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨i, rfl⟩
  · exact Or.inl ⟨i, r, hr, rfl⟩
  · exact Or.inr (Or.inl ⟨r, hr, rfl⟩)
  · exact Or.inr (Or.inr ⟨i, rfl⟩)

section Hom

variable {g : Fin m → X} {R : List (List (Fin m × Bool))} {n : Fin m → List (Fin m × Bool)}
  (hR : ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1) (hnR : ∀ i, n i ∈ R)
  (hn : ∀ i j, (((n i).countP fun l => l.1 = j : ℕ) : ZMod 2) = if i = j then 1 else 0)
  (c : Cocycle₂ X)

@[expose] def lift₀ (g : Fin m → X) (c : Cocycle₂ X) (i : Fin m) : CExt c := ⟨0, g i⟩

@[expose] def corr (g : Fin m → X) (n : Fin m → List (Fin m × Bool)) (c : Cocycle₂ X)
    (i : Fin m) : ZMod 2 :=
  (FreeGroup.lift (lift₀ g c) (FreeGroup.mk (n i))).fst + c.f (1, 1)

@[expose] def liftC (g : Fin m → X) (n : Fin m → List (Fin m × Bool)) (c : Cocycle₂ X)
    (i : Fin m) : CExt c :=
  lift₀ g c i * ι c (corr g n c i)

theorem snd_liftC (i : Fin m) : (liftC g n c i).snd = g i := mul_one (g i)

include hR in
theorem liftC_rel_snd {r : List (Fin m × Bool)} (hr : r ∈ R) :
    (FreeGroup.lift (liftC g n c) (FreeGroup.mk r)).snd = 1 := by
  rw [snd_lift]
  simp only [snd_liftC]
  exact hR r hr

include hR hnR hn in
theorem liftC_n (j : Fin m) : FreeGroup.lift (liftC g n c) (FreeGroup.mk (n j)) = 1 := by
  have h0 : (FreeGroup.lift (lift₀ g c) (FreeGroup.mk (n j))).snd = 1 := by
    rw [snd_lift]
    exact hR _ (hnR j)
  have h1 := eq_ι_of_snd c h0
  unfold liftC
  rw [lift_adjust, sum_map_fst]
  simp only [hn j, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [h1, ← ι_add]
  change ι c (corr g n c j + corr g n c j) = 1
  rw [CharTwo.add_self_eq_zero, ι_zero]

include hR hnR hn in
theorem liftC_cover : ∀ r ∈ coverRels R n, FreeGroup.lift (liftC g n c) r = 1 := by
  intro r' hr'
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr'
  rcases mem_coverW hw with ⟨i, r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨i, rfl⟩
  · rw [mk_commW]
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rcases eq_one_or_eq_ι_one c (liftC_rel_snd hR c hr) with h | h <;> rw [h]
    · simp
    · rw [ι_central c (liftC g n c i) 1, mul_inv_cancel_right, mul_inv_cancel]
  · rw [← FreeGroup.mul_mk, map_mul]
    rcases eq_one_or_eq_ι_one c (liftC_rel_snd hR c hr) with h | h <;> rw [h]
    · exact mul_one 1
    · rw [← ι_add, CharTwo.add_self_eq_zero, ι_zero]
  · exact liftC_n hR hnR hn c i

@[expose] def coverHom : PresentedGroup (coverRels R n) →* CExt c :=
  PresentedGroup.toGroup (liftC_cover hR hnR hn c)

theorem coverHom_of (i : Fin m) :
    coverHom hR hnR hn c (PresentedGroup.of i) = liftC g n c i :=
  PresentedGroup.toGroup.of _

include hR hnR in
theorem cover_lift_g : ∀ r ∈ coverRels R n, FreeGroup.lift g r = 1 := by
  intro r' hr'
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr'
  rcases mem_coverW hw with ⟨i, r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨i, rfl⟩
  · rw [mk_commW]
    simp only [map_mul, map_inv, hR r hr, mul_one, inv_one, mul_inv_cancel]
  · rw [← FreeGroup.mul_mk, map_mul, hR r hr, mul_one]
  · exact hR _ (hnR i)

@[expose] def coverπ : PresentedGroup (coverRels R n) →* X :=
  PresentedGroup.toGroup (cover_lift_g hR hnR)

theorem snd_coverHom (p : PresentedGroup (coverRels R n)) :
    (coverHom hR hnR hn c p).snd = coverπ hR hnR p := by
  change snd' c (coverHom hR hnR hn c p) = _
  rw [← MonoidHom.comp_apply]
  congr 1
  exact PresentedGroup.ext fun i => by
    rw [MonoidHom.comp_apply, coverHom_of, coverπ, PresentedGroup.toGroup.of]
    exact snd_liftC c i

end Hom

section Main

variable [Finite X] {g : Fin m → X} (hg : Subgroup.closure (Set.range g) = ⊤)
  {R : List (List (Fin m × Bool))} {n : Fin m → List (Fin m × Bool)}
  (hR : ∀ r ∈ R, FreeGroup.lift g (FreeGroup.mk r) = 1) (hnR : ∀ i, n i ∈ R)
  (hn : ∀ i j, (((n i).countP fun l => l.1 = j : ℕ) : ZMod 2) = if i = j then 1 else 0)

omit [Finite X] in
include hg in
theorem coverπ_surjective : Function.Surjective (coverπ hR hnR) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hg, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of _⟩

include hg in
theorem isCoboundary₂_or_bijective [Finite (PresentedGroup (coverRels R n))]
    (hcard : Nat.card (PresentedGroup (coverRels R n)) ≤ 2 * Nat.card X) (c : Cocycle₂ X) :
    IsCoboundary₂ c.f ∨ Function.Bijective (coverHom hR hnR hn c) := by
  set φ := coverHom hR hnR hn c
  by_cases hz : ι c 1 ∈ φ.range
  · right
    have hsurj : Function.Surjective φ := by
      intro x
      obtain ⟨p, hp⟩ := coverπ_surjective hg hR hnR x.snd
      have hx : (x * (φ p)⁻¹).snd = 1 := by
        rw [mul_snd, inv_snd, snd_coverHom, hp, mul_inv_cancel]
      rcases eq_one_or_eq_ι_one c hx with h | h
      · exact ⟨p, (mul_inv_eq_one.mp h).symm⟩
      · obtain ⟨q, hq⟩ := hz
        refine ⟨q * p, ?_⟩
        rw [map_mul, hq, ← h, inv_mul_cancel_right]
    exact hsurj.bijective_of_nat_card_le (by rw [card_eq]; exact hcard)
  · left
    have huniq : ∀ p q : PresentedGroup (coverRels R n),
        coverπ hR hnR p = coverπ hR hnR q → φ p = φ q := by
      intro p q hpq
      have hx : ((φ p)⁻¹ * φ q).snd = 1 := by
        rw [mul_snd, inv_snd, snd_coverHom, snd_coverHom, hpq, inv_mul_cancel]
      rcases eq_one_or_eq_ι_one c hx with h | h
      · exact inv_mul_eq_one.mp h
      · exact absurd ⟨p⁻¹ * q, by rw [map_mul, map_inv, h]⟩ hz
    choose sec hsec using coverπ_surjective hg hR hnR
    refine ⟨fun x => -(φ (sec x)).fst, fun x y => ?_⟩
    have h1 : φ (sec x) * φ (sec y) = φ (sec (x * y)) := by
      rw [← map_mul]
      exact huniq _ _ (by rw [map_mul, hsec, hsec, hsec])
    have h2 := congrArg CExt.fst h1
    rw [mul_fst, snd_coverHom, snd_coverHom, hsec, hsec] at h2
    linear_combination h2

include hg hR hnR hn in
theorem isCoboundary₂_sub_of_card_le [Finite (PresentedGroup (coverRels R n))]
    (hcard : Nat.card (PresentedGroup (coverRels R n)) ≤ 2 * Nat.card X)
    {d₁ d₂ : X × X → ZMod 2} (h₁ : IsCocycle₂ d₁) (h₂ : IsCocycle₂ d₂)
    (hn₁ : ¬ IsCoboundary₂ d₁) (hn₂ : ¬ IsCoboundary₂ d₂) : IsCoboundary₂ (d₁ - d₂) := by
  set c₁ : Cocycle₂ X := ⟨d₁, h₁⟩
  set c₂ : Cocycle₂ X := ⟨d₂, h₂⟩
  have hb₁ := (isCoboundary₂_or_bijective hg hR hnR hn hcard c₁).resolve_left hn₁
  have hb₂ := (isCoboundary₂_or_bijective hg hR hnR hn hcard c₂).resolve_left hn₂
  let φ₁ := MulEquiv.ofBijective _ hb₁
  let φ₂ := MulEquiv.ofBijective _ hb₂
  let θ : CExt c₁ ≃* CExt c₂ := φ₁.symm.trans φ₂
  have hθ : ∀ p, θ (coverHom hR hnR hn c₁ p) = coverHom hR hnR hn c₂ p := by
    intro p
    change φ₂ (φ₁.symm (φ₁ p)) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hθsnd : ∀ x, (θ x).snd = x.snd := by
    intro x
    obtain ⟨p, rfl⟩ := hb₁.2 x
    rw [hθ, snd_coverHom, snd_coverHom]
  have hθι : ∀ a, θ (ι c₁ a) = ι c₂ a := by
    intro a
    fin_cases a
    · change θ (ι c₁ 0) = ι c₂ 0
      rw [ι_zero, ι_zero, map_one]
    · change θ (ι c₁ 1) = ι c₂ 1
      have hs : (θ (ι c₁ 1)).snd = 1 := by
        rw [hθsnd]
        rfl
      rcases eq_one_or_eq_ι_one c₂ hs with h | h
      · exact absurd (θ.injective (h.trans θ.map_one.symm)) (ι_one_ne_one c₁)
      · exact h
  refine ⟨fun x => (θ ⟨0, x⟩).fst, fun x y => ?_⟩
  have h := congrArg (fun z => (θ z).fst) (sec_mul_sec c₁ x y)
  simp only [map_mul, hθι, mul_fst, hθsnd, ι_fst, ι_snd] at h
  rw [f_one_left c₂ (x * y)] at h
  change (θ ⟨0, x⟩).fst + (θ ⟨0, y⟩).fst + d₂ (x, y) =
    d₁ (x, y) - d₂ (1, 1) + (θ ⟨0, x * y⟩).fst + d₂ (1, 1) at h
  change d₁ (x, y) - d₂ (x, y) = _
  linear_combination -h

end Main

end CFSG.LocalAnalysis.CentralCover
