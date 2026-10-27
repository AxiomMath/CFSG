module

public import CFSG.Monster.GMS.Facts.Co1Local
public import CFSG.Sporadic.Co1.Module.Forms

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS.Leech

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act
open scoped Matrix

theorem bil₀_add_left (u u' v : Fin 24 → ZMod 2) : bil₀ (u + u') v = bil₀ u v + bil₀ u' v := by
  unfold bil₀
  rw [add_dotProduct]

theorem bil₀_add_right (u v v' : Fin 24 → ZMod 2) : bil₀ u (v + v') = bil₀ u v + bil₀ u v' := by
  unfold bil₀
  rw [Matrix.mulVec_add, dotProduct_add]

theorem bil₀_co1Act
    (g : Co1) (u v : Fin 24 → ZMod 2) :
    bil₀ (co1Act g u) (co1Act g v) = bil₀ u v := by
  have h1 := q₀_add (co1Act g u) (co1Act g v)
  have h2 := q₀_add u v
  have h3 : q₀ (co1Act g (u + v)) = q₀ (u + v) :=
    CFSG.Sporadic.Co1.Module.q₀_co1Act g (u + v)
  rw [map_add] at h3
  have h4 : q₀ (co1Act g u) = q₀ u := CFSG.Sporadic.Co1.Module.q₀_co1Act g u
  have h5 : q₀ (co1Act g v) = q₀ v := CFSG.Sporadic.Co1.Module.q₀_co1Act g v
  linear_combination -h1 + h3 - h4 - h5 + h2

theorem exists_bil₀_eq_of_additive {f : (Fin 24 → ZMod 2) → ZMod 2}
    (hf : ∀ u v, f (u + v) = f u + f v) :
    ∃ a : Fin 24 → ZMod 2, ∀ x, f x = bil₀ a x := by
  refine ⟨(fun j => f (Pi.single j 1)) ᵥ* F₀inv, fun x => ?_⟩
  rw [additive_expand hf x]
  unfold bil₀
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, F₀inv_mul, Matrix.vecMul_one, dotProduct,
    Finset.sum_congr rfl fun j _ => mul_comm (x j) (f (Pi.single j 1))]

theorem eq_zero_of_forall_bil₀_eq_zero
    {u : Fin 24 → ZMod 2} (h : ∀ v, bil₀ u v = 0) : u = 0 := by
  have h1 : u ᵥ* F₀ = 0 := by
    funext j
    have := h (Pi.single j 1)
    unfold bil₀ at this
    rw [Matrix.dotProduct_mulVec] at this
    simpa using this
  have h2 : u = (u ᵥ* F₀) ᵥ* F₀inv := by
    rw [Matrix.vecMul_vecMul, F₀_mul_inv, Matrix.vecMul_one]
  rw [h2, h1]
  simp

theorem exists_bil₀_eq_one
    {u : Fin 24 → ZMod 2} (hu : u ≠ 0) : ∃ v, bil₀ u v = 1 := by
  by_contra hne
  push Not at hne
  exact hu (eq_zero_of_forall_bil₀_eq_zero fun v => (zmod2_cases _).resolve_right (hne v))

theorem exists_bil₀_eq
    {ι : Type*} [Fintype ι] {v : ι → Fin 24 → ZMod 2}
    (hv : LinearIndependent (ZMod 2) v) (ε : ι → ZMod 2) :
    ∃ w : Fin 24 → ZMod 2, ∀ i, bil₀ w (v i) = ε i := by
  classical
  have hker : LinearMap.ker (Matrix.mulVecLin F₀) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h : F₀inv *ᵥ (F₀ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, F₀inv_mul, Matrix.one_mulVec]
    rw [← h]
    change F₀ *ᵥ x = 0 at hx
    rw [hx, Matrix.mulVec_zero]
  have hu : LinearIndependent (ZMod 2) (fun i => F₀ *ᵥ v i) := hv.map' (Matrix.mulVecLin F₀) hker
  have hT : LinearMap.ker (Fintype.linearCombination (ZMod 2) (fun i => F₀ *ᵥ v i)) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (linearIndependent_iff_injective_fintypeLinearCombination.mp hu)
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective _ hT
  have hLu : ∀ i j, L (F₀ *ᵥ v i) j = if j = i then 1 else 0 := by
    intro i j
    have h1 : Fintype.linearCombination (ZMod 2) (fun i => F₀ *ᵥ v i) (Pi.single i 1) =
        F₀ *ᵥ v i := by
      rw [Fintype.linearCombination_apply, Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    have h2 := congrArg (fun f => f (Pi.single i (1 : ZMod 2))) hL
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
    rw [h1] at h2
    rw [h2]
    simp [Pi.single_apply]
  let f : (Fin 24 → ZMod 2) → ZMod 2 := fun x => ∑ j, ε j * L x j
  have hf : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    simp only [f, map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  refine ⟨fun j => f (Pi.single j 1), fun i => ?_⟩
  have h3 : f (F₀ *ᵥ v i) = ε i := by
    simp only [f, hLu]
    simp
  rw [← h3, additive_expand hf (F₀ *ᵥ v i)]
  unfold bil₀
  rw [dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem neg_eq_self (w : Fin 24 → ZMod 2) : -w = w := neg_eq_of_add_eq_zero_right (vec_add_self w)

theorem sub_eq_add (a b : Fin 24 → ZMod 2) : a - b = a + b := by
  rw [sub_eq_add_neg, neg_eq_self]

theorem co1Act_co1Act_of_mul_self_eq_one {g : Co1} (hg : g * g = 1) (v : Fin 24 → ZMod 2) :
    co1Act g (co1Act g v) = v := by
  have h := congrArg (fun m : Module.End (ZMod 2) (Fin 24 → ZMod 2) => m v) (map_mul co1Act g g)
  simp only [Module.End.mul_apply, hg, map_one, Module.End.one_apply] at h
  exact h.symm

theorem exists_add_eq_of_forall_bil₀_eq_zero
    {g : Co1} (hg : g * g = 1) {u : Fin 24 → ZMod 2}
    (hu : ∀ v, co1Act g v = v → bil₀ u v = 0) : ∃ w, co1Act g w + w = u := by
  by_contra hne
  push Not at hne
  let T : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) := co1Act g - LinearMap.id
  have hT : ∀ x, T x = co1Act g x + x := fun x => by
    simp only [T, LinearMap.sub_apply, LinearMap.id_apply]
    exact sub_eq_add _ _
  have hnot : u ∉ LinearMap.range T := by
    rintro ⟨w, hw⟩
    exact hne w (by rw [← hw, hT])
  obtain ⟨f, hfu, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hfT : ∀ x, f (co1Act g x) = f x := by
    intro x
    have hmem : f (T x) ∈ (LinearMap.range T).map f := ⟨T x, ⟨x, rfl⟩, rfl⟩
    rw [hf, Submodule.mem_bot, hT, map_add] at hmem
    exact (eq_neg_of_add_eq_zero_left hmem).trans (CharTwo.neg_eq _)
  obtain ⟨a, ha⟩ := exists_bil₀_eq_of_additive (f := fun x => f x) (fun u v => map_add f u v)
  have hga : co1Act g a = a := by
    have h1 : ∀ y, bil₀ (co1Act g a + a) y = 0 := by
      intro y
      have e1 : bil₀ (co1Act g a) y = bil₀ a (co1Act g y) := by
        have := bil₀_co1Act g a (co1Act g y)
        rw [co1Act_co1Act_of_mul_self_eq_one hg] at this
        exact this
      have e2 : bil₀ a (co1Act g y) = bil₀ a y := by
        rw [← ha, ← ha]
        exact hfT y
      rw [bil₀_add_left, e1, e2]
      exact CharTwo.add_self_eq_zero _
    have h2 := eq_zero_of_forall_bil₀_eq_zero h1
    exact (eq_neg_of_add_eq_zero_left h2).trans (neg_eq_self a)
  apply hfu
  rw [ha, bil₀_comm]
  exact hu a hga

theorem linearIndependent_fin_one {x : Fin 24 → ZMod 2} (hx : x ≠ 0) :
    LinearIndependent (ZMod 2) ![x] := by
  rw [linearIndependent_unique_iff]
  exact hx

theorem linearIndependent_fin_two {x y : Fin 24 → ZMod 2} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    LinearIndependent (ZMod 2) ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp only [zero_smul, one_smul, zero_add] at h
    exact absurd h hy
  · simp only [zero_smul, one_smul, add_zero] at h
    exact absurd h hx
  · simp only [one_smul] at h
    exact absurd (eq_neg_of_add_eq_zero_left h |>.trans (neg_eq_self y)) hxy

theorem linearIndependent_fin_three {x y w : Fin 24 → ZMod 2} (hx : x ≠ 0) (hy : y ≠ 0)
    (hw : w ≠ 0) (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w) (h : x + y ≠ w) :
    LinearIndependent (ZMod 2) ![x, y, w] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hg
  have hsub : ∀ a b : Fin 24 → ZMod 2, a + b = 0 → a = b := fun a b hab =>
    (eq_neg_of_add_eq_zero_left hab).trans (neg_eq_self b)
  have h0 : g 0 = 0 ∧ g 1 = 0 ∧ g 2 = 0 := by
    rcases zmod2_cases (g 0) with h0 | h0 <;> rcases zmod2_cases (g 1) with h1 | h1 <;>
      rcases zmod2_cases (g 2) with h2 | h2 <;> rw [h0, h1, h2] at hg <;>
      simp only [zero_smul, one_smul, zero_add, add_zero] at hg
    · exact ⟨h0, h1, h2⟩
    · exact absurd hg hw
    · exact absurd hg hy
    · exact absurd (hsub _ _ hg) hyw
    · exact absurd hg hx
    · exact absurd (hsub _ _ hg) hxw
    · exact absurd (hsub _ _ hg) hxy
    · exact absurd (hsub _ _ hg) h
  intro i
  fin_cases i
  · exact h0.1
  · exact h0.2.1
  · exact h0.2.2

@[instance_reducible]
private noncomputable def co1MulAction : MulAction Co1 (Fin 24 → ZMod 2) where
  smul g v := co1Act g v
  one_smul v := by
    show co1Act 1 v = v
    rw [map_one]
    rfl
  mul_smul g h v := by
    show co1Act (g * h) v = co1Act g (co1Act h v)
    rw [map_mul]
    rfl

attribute [local instance] co1MulAction

theorem card_co1Stab_mul_ncard_range (v : Fin 24 → ZMod 2) :
    Nat.card (co1Stab v) * (Set.range fun g : Co1 => co1Act g v).ncard = Nat.card Co1 := by
  have h3 := Subgroup.card_mul_index (MulAction.stabilizer Co1 v)
  rw [MulAction.index_stabilizer Co1 v] at h3
  exact h3

theorem range_co1Act_eq_co1Orbit {i : Fin 3} {v : Fin 24 → ZMod 2} (hv : v ∈ co1Orbit i) :
    (Set.range fun g : Co1 => co1Act g v) = co1Orbit i := by
  obtain ⟨a, rfl⟩ := hv
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g * a, by simp⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by simp [← Module.End.mul_apply, ← map_mul]⟩

theorem card_co1Stab_mul_ncard_co1Orbit {i : Fin 3} {v : Fin 24 → ZMod 2} (hv : v ∈ co1Orbit i) :
    Nat.card (co1Stab v) * (co1Orbit i).ncard = Nat.card Co1 := by
  rw [← range_co1Act_eq_co1Orbit hv]
  exact card_co1Stab_mul_ncard_range v

theorem ncard_co1Orbit_zero :
    (co1Orbit 0).ncard = 98280 :=
  CFSG.Sporadic.Co1.Module.co1_orbit_ncard_v₂

theorem ncard_co1Orbit_one :
    (co1Orbit 1).ncard = 8386560 :=
  CFSG.Sporadic.Co1.Module.co1_orbit_ncard_v₃

theorem ncard_co1Orbit_two :
    (co1Orbit 2).ncard = 8292375 :=
  CFSG.Sporadic.Co1.Module.co1_orbit_ncard_v₄

theorem co1Act_mem_co1Orbit {i : Fin 3} {v : Fin 24 → ZMod 2} (hv : v ∈ co1Orbit i) (g : Co1) :
    co1Act g v ∈ co1Orbit i := by
  obtain ⟨a, rfl⟩ := hv
  exact ⟨g * a, by simp⟩

theorem exists_co1Act_eq {i : Fin 3} {v w : Fin 24 → ZMod 2} (hv : v ∈ co1Orbit i)
    (hw : w ∈ co1Orbit i) : ∃ g : Co1, co1Act g v = w := by
  obtain ⟨a, rfl⟩ := hv
  obtain ⟨b, rfl⟩ := hw
  exact ⟨b * a⁻¹, by simp [← Module.End.mul_apply, ← map_mul]⟩

theorem ne_zero_of_mem_co1Orbit {i : Fin 3} {v : Fin 24 → ZMod 2} (hv : v ∈ co1Orbit i) :
    v ≠ 0 := by
  obtain ⟨a, rfl⟩ := hv
  intro h
  have hr : CFSG.Sporadic.Co1.Module.reps i = 0 := by
    have h' := congrArg (co1Act a⁻¹) h
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      map_zero] at h'
    exact h'
  fin_cases i
  · exact CFSG.Sporadic.Co1.Module.v₂_ne_zero hr
  · exact CFSG.Sporadic.Co1.Module.v₃_ne_zero hr
  · exact CFSG.Sporadic.Co1.Module.v₄_ne_zero hr

theorem existsUnique_co1Orbit
    {v : Fin 24 → ZMod 2} (hv : v ≠ 0) : ∃! i : Fin 3, v ∈ co1Orbit i :=
  CFSG.Sporadic.Co1.Module.co1_exists_unique_orbit hv

theorem eq_of_mem_co1Orbit
    {i j : Fin 3} {v : Fin 24 → ZMod 2} (hi : v ∈ co1Orbit i)
    (hj : v ∈ co1Orbit j) : i = j := by
  obtain ⟨k, -, huniq⟩ := existsUnique_co1Orbit (ne_zero_of_mem_co1Orbit hi)
  exact (huniq i hi).trans (huniq j hj).symm

theorem linearIndependent_pair_of_add_mem {i : Fin 3} {x y : Fin 24 → ZMod 2} (hx : x ≠ 0)
    (hy : y ≠ 0) (hxy : x + y ∈ co1Orbit i) : LinearIndependent (ZMod 2) ![x, y] := by
  refine linearIndependent_fin_two hx hy fun h => ?_
  rw [h, vec_add_self] at hxy
  exact ne_zero_of_mem_co1Orbit hxy rfl

theorem q₀_eq_zero_of_mem_co1Orbit_zero
    {v : Fin 24 → ZMod 2} (hv : v ∈ co1Orbit 0) : q₀ v = 0 := by
  obtain ⟨a, rfl⟩ := hv
  exact (CFSG.Sporadic.Co1.Module.q₀_co1Act a _).trans CFSG.Sporadic.Co1.Module.q₀_v₂

theorem q₀_eq_one_of_mem_co1Orbit_one
    {v : Fin 24 → ZMod 2} (hv : v ∈ co1Orbit 1) : q₀ v = 1 := by
  obtain ⟨a, rfl⟩ := hv
  exact (CFSG.Sporadic.Co1.Module.q₀_co1Act a _).trans CFSG.Sporadic.Co1.Module.q₀_v₃

theorem q₀_eq_zero_of_mem_co1Orbit_two
    {v : Fin 24 → ZMod 2} (hv : v ∈ co1Orbit 2) : q₀ v = 0 := by
  obtain ⟨a, rfl⟩ := hv
  exact (CFSG.Sporadic.Co1.Module.q₀_co1Act a _).trans CFSG.Sporadic.Co1.Module.q₀_v₄

theorem mem_co1Orbit_one_of_q₀_eq_one
    {v : Fin 24 → ZMod 2} (hv : q₀ v = 1) : v ∈ co1Orbit 1 :=
  (CFSG.Sporadic.Co1.Module.co1_q₀_eq_one_iff v).1 hv

end CFSG.Monster.GMS.Leech
