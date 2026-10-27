module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.Quasithin.H13.P31Sz

section Odd

variable {Y W : Type*} [Group Y] [CommGroup W]

@[expose] def commW (ρ : Y →* MulAut W) (E : Subgroup Y) : Subgroup W :=
  Subgroup.closure {u | ∃ e ∈ E, ∃ v : W, u = ρ e v * v⁻¹}

@[expose] def commU (ρ : Y →* MulAut W) (E : Subgroup Y) (U : Subgroup W) : Subgroup W :=
  Subgroup.closure {u | ∃ e ∈ E, ∃ v ∈ U, u = ρ e v * v⁻¹}

theorem fixed_inf_commutator_eq_bot [Finite W] (hW : ∀ w : W, w * w = 1) (ρ : Y →* MulAut W)
    (E : Subgroup Y) [Finite E] (hodd : Odd (Nat.card E)) {w : W} (hw : ∀ e ∈ E, ρ e w = w)
    (hD : w ∈ commW ρ E) : w = 1 := by
  haveI : Fintype E := Fintype.ofFinite E
  let Nm : W →* W :=
    { toFun := fun x => ∏ e : E, ρ e x
      map_one' := by simp
      map_mul' := fun a b => by simp [Finset.prod_mul_distrib] }
  have hNm : ∀ x : W, ∀ e : E, Nm (ρ e x) = Nm x := by
    intro x e
    show ∏ e' : E, ρ e' (ρ e x) = ∏ e' : E, ρ e' x
    have : ∀ e' : E, ρ e' (ρ e x) = ρ (e' * e) x := fun e' => by simp [map_mul]
    simp_rw [this]
    exact Fintype.prod_equiv (Equiv.mulRight e) _ _ (fun e' => rfl)
  have hker : commW ρ E ≤ Nm.ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨e, he, v, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hNm v ⟨e, he⟩, mul_inv_cancel]
  have h1 : Nm w = 1 := hker hD
  have h2 : Nm w = w := by
    show ∏ e : E, ρ e w = w
    have : ∀ e : E, ρ e w = w := fun e => hw e e.2
    simp_rw [this]
    rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, sq, hW, one_pow, one_mul]
  rw [← h2, h1]

end Odd

section Skeleton

variable {Y W : Type*} [Group Y] [CommGroup W]

theorem commW_invariant (ρ : Y →* MulAut W) (E : Subgroup Y) [E.Normal] (y : Y) {w : W}
    (hw : w ∈ commW ρ E) : ρ y w ∈ commW ρ E := by
  induction hw using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨e, he, v, rfl⟩ := hu
    refine Subgroup.subset_closure ⟨y * e * y⁻¹, (inferInstance : E.Normal).conj_mem e he y, ρ y v, ?_⟩
    simp [map_mul]
  | one => simpa using (commW ρ E).one_mem
  | mul a b _ _ ha hb =>
    rw [map_mul]
    exact (commW ρ E).mul_mem ha hb
  | inv a _ ha =>
    rw [map_inv]
    exact (commW ρ E).inv_mem ha

theorem commU_le_commW (ρ : Y →* MulAut W) (E : Subgroup Y) (U : Subgroup W) :
    commU ρ E U ≤ commW ρ E :=
  Subgroup.closure_mono fun _ ⟨e, he, v, _, hu⟩ => ⟨e, he, v, hu⟩

@[expose] def fixedW (ρ : Y →* MulAut W) (E : Subgroup Y) : Subgroup W where
  carrier := {w | ∀ e ∈ E, ρ e w = w}
  one_mem' := fun e _ => map_one _
  mul_mem' := fun {a b} ha hb e he => by rw [map_mul, ha e he, hb e he]
  inv_mem' := fun {a} ha e he => by rw [map_inv, ha e he]

theorem fixedW_invariant (ρ : Y →* MulAut W) (E : Subgroup Y) [E.Normal] (y : Y) {w : W}
    (hw : w ∈ fixedW ρ E) : ρ y w ∈ fixedW ρ E := by
  intro e he
  have hmem : y⁻¹ * e * y ∈ E := by
    have := (inferInstance : E.Normal).conj_mem e he y⁻¹
    simpa using this
  have h1 : ρ e (ρ y w) = ρ y (ρ (y⁻¹ * e * y) w) := by
    rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    group
  rw [h1, hw _ hmem]

theorem fixed_eq_one_of_normal_odd [Finite W] (hW : ∀ w : W, w * w = 1) (ρ : Y →* MulAut W)
    (hρ : Function.Injective ρ) (E : Subgroup Y) [E.Normal] [Finite E] (hodd : Odd (Nat.card E))
    (hE1 : ∃ e ∈ E, e ≠ 1) (S : Subgroup Y) (hES : E ≤ S)
    (U : Subgroup W) (hSU : ∀ s ∈ S, ∀ u ∈ U, ρ s u ∈ U)
    (hirr : ∀ U' : Subgroup W, U' ≤ U → (∀ s ∈ S, ∀ u ∈ U', ρ s u ∈ U') → U' = ⊥ ∨ U' = U)
    (hgen : ∀ D : Subgroup W, U ≤ D → (∀ y : Y, ∀ d ∈ D, ρ y d ∈ D) → D = ⊤) {w : W}
    (hw : ∀ e ∈ E, ρ e w = w) : w = 1 := by
  have hnt : ∃ e ∈ E, ∃ u ∈ U, ρ e u ≠ u := by
    by_contra hcon
    push Not at hcon
    have hD : fixedW ρ E = ⊤ := hgen _ (fun u hu e he => hcon e he u hu)
      (fun y d hd => fixedW_invariant ρ E y hd)
    obtain ⟨e, he, he1⟩ := hE1
    apply he1
    apply hρ
    ext v
    have : v ∈ fixedW ρ E := by rw [hD]; exact Subgroup.mem_top v
    simpa using this e he
  have hle : commU ρ E U ≤ U := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨e, he, v, hv, rfl⟩
    exact U.mul_mem (hSU e (hES he) v hv) (U.inv_mem hv)
  have hinv : ∀ s ∈ S, ∀ u ∈ commU ρ E U, ρ s u ∈ commU ρ E U := by
    intro s hs u hu
    induction hu using Subgroup.closure_induction with
    | mem u hu =>
      obtain ⟨e, he, v, hv, rfl⟩ := hu
      refine Subgroup.subset_closure ⟨s * e * s⁻¹, (inferInstance : E.Normal).conj_mem e he s, ρ s v,
        hSU s hs v hv, ?_⟩
      simp [map_mul]
    | one => simpa using (commU ρ E U).one_mem
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact (commU ρ E U).mul_mem ha hb
    | inv a _ ha =>
      rw [map_inv]
      exact (commU ρ E U).inv_mem ha
  have hne : commU ρ E U ≠ ⊥ := by
    obtain ⟨e, he, u, hu, hne⟩ := hnt
    intro hbot
    apply hne
    have hmem : ρ e u * u⁻¹ ∈ commU ρ E U := Subgroup.subset_closure ⟨e, he, u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  have hU : commU ρ E U = U := by
    rcases hirr _ hle hinv with h | h
    · exact absurd h hne
    · exact h
  have hUD : ∀ u ∈ U, u ∈ commW ρ E := fun u hu =>
    commU_le_commW ρ E U (by rw [hU]; exact hu)
  have hD : commW ρ E = ⊤ :=
    hgen _ hUD (fun y d hd => commW_invariant ρ E y hd)
  exact fixed_inf_commutator_eq_bot hW ρ E hodd hw (by rw [hD]; exact Subgroup.mem_top w)

end Skeleton

section Head

variable {Y W : Type*} [Group Y] [CommGroup W]

theorem trivial_of_head (ρ : Y →* MulAut W) (K : Subgroup Y) (x : Y)
    (hxK : ∀ k ∈ K, x * k = k * x) (M C : Subgroup W)
    (hMK : ∀ k ∈ K, ∀ m ∈ M, ρ k m ∈ M)
    (hMgen : M ≤ commU ρ K M) (hCfix : ∀ k ∈ K, ∀ c ∈ C, ρ k c = c)
    (hxC : ∀ m ∈ M, ρ x m * m⁻¹ ∈ C) : ∀ m ∈ M, ρ x m = m := by
  have hφ : ∀ m ∈ commU ρ K M, ρ x m * m⁻¹ = 1 := by
    intro m hm
    induction hm using Subgroup.closure_induction with
    | mem u hu =>
      obtain ⟨k, hk, v, hv, rfl⟩ := hu
      have hc := hxC v hv
      have hkc : ρ k (ρ x v * v⁻¹) = ρ x v * v⁻¹ := hCfix k hk _ hc
      have h2 : ρ x (ρ k v) = ρ k (ρ x v) := by
        have := congrArg (fun z => ρ z v) (hxK k hk)
        simpa [map_mul] using this
      have h3 : ρ k (ρ x v) = (ρ x v * v⁻¹) * ρ k v := by
        have h4 : ρ x v = (ρ x v * v⁻¹) * v := (inv_mul_cancel_right _ _).symm
        calc ρ k (ρ x v) = ρ k ((ρ x v * v⁻¹) * v) := by rw [← h4]
          _ = ρ k (ρ x v * v⁻¹) * ρ k v := map_mul _ _ _
          _ = (ρ x v * v⁻¹) * ρ k v := by rw [hkc]
      have h5 : ρ x (ρ k v * v⁻¹) = ρ k v * v⁻¹ := by
        rw [map_mul, map_inv, h2, h3]
        calc ρ x v * v⁻¹ * ρ k v * (ρ x v)⁻¹ = (ρ x v * (ρ x v)⁻¹) * (ρ k v * v⁻¹) := by ac_rfl
          _ = ρ k v * v⁻¹ := by simp
      rw [h5, mul_inv_cancel]
    | one => simp
    | mul a b _ _ ha hb =>
      rw [map_mul]
      calc ρ x a * ρ x b * (a * b)⁻¹ = (ρ x a * a⁻¹) * (ρ x b * b⁻¹) := by
            rw [mul_inv_rev]; ac_rfl
        _ = 1 := by rw [ha, hb, one_mul]
    | inv a _ ha =>
      rw [map_inv]
      calc (ρ x a)⁻¹ * a⁻¹⁻¹ = (ρ x a * a⁻¹)⁻¹ := by rw [mul_inv_rev, mul_comm]
        _ = 1 := by rw [ha, inv_one]
  intro m hm
  have := hφ m (hMgen hm)
  rwa [mul_inv_eq_one] at this

end Head

end CFSG.Quasithin.H13.P31Sz
