module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmNsComm
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusNorm

public section

namespace CFSG.StandardType

namespace WitOmNs

open Module QuadraticMap TableBOrth

section Blocks

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {L : Type} [Field L] [Algebra K L] {s : ℕ} {κ : Type}
  {Φ : ((Fin s → L) × (κ → K)) ≃ₗ[K] V} {β : LinearMap.BilinForm K L}

@[expose] noncomputable def blk (Φ : ((Fin s → L) × (κ → K)) ≃ₗ[K] V) (l : Fin s) (a : L) : V :=
  Φ (Pi.single l a, 0)

@[expose] noncomputable def two (Φ : ((Fin s → L) × (κ → K)) ≃ₗ[K] V) (i j : Fin s) (a a' : L) :
    V :=
  blk Φ i a + blk Φ j a'

theorem blk_add (l : Fin s) (a b : L) : blk Φ l (a + b) = blk Φ l a + blk Φ l b := by
  rw [blk, blk, blk, ← map_add, Prod.mk_add_mk, Pi.single_add, add_zero]

theorem blk_smul (l : Fin s) (c : K) (a : L) : blk Φ l (c • a) = c • blk Φ l a := by
  rw [blk, blk, ← map_smul, Prod.smul_mk, Pi.single_smul, smul_zero]

theorem blk_neg (l : Fin s) (a : L) : blk Φ l (-a) = -blk Φ l a := by
  rw [blk, blk, ← map_neg, Prod.neg_mk, Pi.single_neg, neg_zero]

theorem blk_sub (l : Fin s) (a b : L) : blk Φ l (a - b) = blk Φ l a - blk Φ l b := by
  rw [sub_eq_add_neg, blk_add, blk_neg, ← sub_eq_add_neg]

theorem polar_frame_zero
    (hdec : ∀ d d' w w', polar Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + polar Q (Φ (0, w)) (Φ (0, w'))) (d d' : Fin s → L) :
    polar Q (Φ (d, 0)) (Φ (d', 0)) = ∑ i, β (d i) (d' i) := by
  rw [hdec, Prod.mk_zero_zero, map_zero, polar_zero_left, add_zero]

theorem polar_blk
    (hdec : ∀ d d' w w', polar Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + polar Q (Φ (0, w)) (Φ (0, w'))) (l m : Fin s) (a b : L) :
    polar Q (blk Φ l a) (blk Φ m b) = if l = m then β a b else 0 := by
  classical
  rw [blk, blk, polar_frame_zero hdec, Finset.sum_eq_single l]
  · rw [Pi.single_eq_same]
    split_ifs with h
    · subst h
      rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, map_zero]
  · intro c _ hc
    rw [Pi.single_eq_of_ne hc, LinearMap.map_zero₂]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem polar_frame_blk
    (hdec : ∀ d d' w w', polar Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + polar Q (Φ (0, w)) (Φ (0, w'))) (d : Fin s → L) (w : κ → K)
    (l : Fin s) (a : L) :
    polar Q (Φ (d, w)) (blk Φ l a) = β (d l) a := by
  classical
  rw [blk, hdec, Prod.mk_zero_zero, map_zero, polar_zero_right, add_zero,
    Finset.sum_eq_single l]
  · rw [Pi.single_eq_same]
  · intro c _ hc
    rw [Pi.single_eq_of_ne hc, map_zero]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem quad_two
    (hdec : ∀ d d' w w', polar Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + polar Q (Φ (0, w)) (Φ (0, w'))) {i j : Fin s} (hij : i ≠ j)
    (a a' : L) : Q (two Φ i j a a') = Q (blk Φ i a) + Q (blk Φ j a') := by
  rw [two, QuadraticMap.map_add (Q : V → K), polar_blk hdec]
  simp [hij]

theorem polar_two
    (hdec : ∀ d d' w w', polar Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + polar Q (Φ (0, w)) (Φ (0, w'))) {i j : Fin s} (hij : i ≠ j)
    (a a' b b' : L) : polar Q (two Φ i j a a') (two Φ i j b b') = β a b + β a' b' := by
  rw [two, two, polar_add_left, polar_add_right, polar_add_right, polar_blk hdec,
    polar_blk hdec, polar_blk hdec, polar_blk hdec]
  simp [hij, Ne.symm hij]

theorem frame_decomp {i j : Fin s} (hij : i ≠ j) (d : Fin s → L) (w : κ → K) :
    Φ (d, w) = two Φ i j (d i) (d j) +
      Φ (fun l => if l = i ∨ l = j then 0 else d l, w) := by
  classical
  rw [two, blk, blk, ← map_add, ← map_add]
  congr 1
  refine Prod.ext (funext fun l => ?_) (by simp)
  by_cases hi : l = i
  · subst hi
    simp [hij]
  · by_cases hj : l = j
    · subst hj
      simp [hi]
    · simp [hi, hj]

end Blocks

section Invariant

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {L : Type} [Field L] [Algebra K L] {s : ℕ} {κ : Type}
  {Φ : ((Fin s → L) × (κ → K)) ≃ₗ[K] V} {β : LinearMap.BilinForm K L}

theorem diag_blk {ζ : L} {x : V →ₗ[K] V} {k : Fin s → ℕ}
    (hx : ∀ d w, x (Φ (d, w)) = Φ (fun l => ζ ^ k l * d l, w)) (l : Fin s) (a : L) :
    x (blk Φ l a) = blk Φ l (ζ ^ k l * a) := by
  classical
  rw [blk, hx, blk]
  congr 2
  funext m
  by_cases h : m = l
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem eq_of_pow_invariant {α : Type*} {p : ℕ} (hp : p.Prime) {ζ : L} (hζp : ζ ^ p = 1)
    {k : ℕ} (hk : ¬ p ∣ k) {F : L → α} (hF : ∀ a, F (ζ ^ k * a) = F a) (a : L) :
    F (ζ * a) = F a := by
  have hcop : Nat.Coprime k p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hk)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hiter : ∀ j : ℕ, ∀ a, F (ζ ^ (k * j) * a) = F a := by
    intro j
    induction j with
    | zero => intro a; rw [Nat.mul_zero, pow_zero, one_mul]
    | succ j ih =>
      intro a
      rw [Nat.mul_succ, pow_add, mul_assoc, ih, hF]
  have h1 : ζ ^ (k * m) = ζ := by rw [pow_eq_pow_mod _ hζp, hm, pow_one]
  rw [← h1]
  exact hiter m a

theorem quad_blk_mul_eq {p : ℕ} (hp : p.Prime) {ζ : L} (hζp : ζ ^ p = 1) {x : V →ₗ[K] V}
    (hxQ : ∀ v, Q (x v) = Q v) {k : Fin s → ℕ}
    (hx : ∀ d w, x (Φ (d, w)) = Φ (fun l => ζ ^ k l * d l, w)) {l : Fin s} (hk : ¬ p ∣ k l)
    (a : L) : Q (blk Φ l (ζ * a)) = Q (blk Φ l a) :=
  eq_of_pow_invariant hp hζp hk (F := fun a => Q (blk Φ l a))
    (fun a => by rw [← diag_blk hx, hxQ]) a

theorem beta_mul_eq
    (hdec : ∀ d d' w w', polar Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + polar Q (Φ (0, w)) (Φ (0, w'))) {ζ : L} {l : Fin s}
    (hQl : ∀ a, Q (blk Φ l (ζ * a)) = Q (blk Φ l a)) (a b : L) :
    β (ζ * a) (ζ * b) = β a b := by
  have hβ : ∀ a b, β a b = polar Q (blk Φ l a) (blk Φ l b) := fun a b => by
    rw [polar_blk hdec, ite_eq_left rfl]
  rw [hβ, hβ, polar, polar, ← blk_add, ← blk_add, ← mul_add, hQl, hQl, hQl]

theorem quad_blk_eq_of_inv [CharP K 2]
    (hdec : ∀ d d' w w', polar Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + polar Q (Φ (0, w)) (Φ (0, w'))) {ζ : L} (hζ1 : ζ ≠ 1) {i j : Fin s}
    (hQi : ∀ a, Q (blk Φ i (ζ * a)) = Q (blk Φ i a))
    (hQj : ∀ a, Q (blk Φ j (ζ * a)) = Q (blk Φ j a)) (a : L) :
    Q (blk Φ i a) = Q (blk Φ j a) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set D : L → K := fun a => Q (blk Φ i a) - Q (blk Φ j a) with hD
  have hadd : ∀ a b, D (a + b) = D a + D b := by
    intro a b
    simp only [hD, blk_add, QuadraticMap.map_add (Q : V → K), polar_blk hdec]
    ring
  have hζD : ∀ a, D (ζ * a) = D a := fun a => by simp only [hD, hQi, hQj]
  have hneg : ∀ a, D (-a) = D a := fun a => by
    simp only [hD, blk_neg, QuadraticMap.map_neg]
  have hz : ∀ b, D ((ζ + 1) * b) = 0 := by
    intro b
    rw [add_mul, one_mul, hadd, hζD]
    have h1 : D b + D b = 2 * D b := by ring
    rw [h1, show (2 : K) = 0 from h2, zero_mul]
  have hζ1' : ζ + 1 ≠ 0 := by
    intro h
    apply hζ1
    have hc : (2 : L) = 0 := by
      have h3 := congrArg (algebraMap K L) h2
      rwa [map_ofNat, map_zero] at h3
    linear_combination h - hc
  have h3 := hz ((ζ + 1)⁻¹ * a)
  rw [← mul_assoc, mul_inv_cancel₀ hζ1', one_mul] at h3
  exact sub_eq_zero.mp h3

end Invariant

section TwoPlane

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {L : Type} [Field L] [Algebra K L] {s : ℕ} {κ : Type}
  {Φ : ((Fin s → L) × (κ → K)) ≃ₗ[K] V} {β : LinearMap.BilinForm K L}

@[expose] noncomputable def tpScal (ζ : L) (i j l : Fin s) : L :=
  if l = i ∨ l = j then ζ else 1

theorem tpScal_ne_zero {ζ : L} (hζ : ζ ≠ 0) (i j l : Fin s) : tpScal ζ i j l ≠ 0 := by
  unfold tpScal
  split_ifs
  · exact hζ
  · exact one_ne_zero

@[expose] noncomputable def twoPlane (Φ : ((Fin s → L) × (κ → K)) ≃ₗ[K] V) {ζ : L} (hζ : ζ ≠ 0)
    (i j : Fin s) : V ≃ₗ[K] V :=
  Φ.symm.trans ((SpNS.scaleEquiv (κ := κ) (K := K) (tpScal ζ i j) (tpScal_ne_zero hζ i j)).trans Φ)

variable {ζ : L} (hζ : ζ ≠ 0) {i j : Fin s}

theorem twoPlane_apply (d : Fin s → L) (w : κ → K) :
    twoPlane Φ hζ i j (Φ (d, w)) = Φ (fun l => tpScal ζ i j l * d l, w) := by
  rw [twoPlane, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    SpNS.scaleEquiv_apply]

theorem twoPlane_pow_apply (m : ℕ) (d : Fin s → L) (w : κ → K) :
    (twoPlane Φ hζ i j ^ m) (Φ (d, w)) = Φ (fun l => tpScal ζ i j l ^ m * d l, w) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, twoPlane_apply]
    congr 2
    funext l
    ring

theorem twoPlane_blk_left (hij : i ≠ j) (a : L) :
    twoPlane Φ hζ i j (blk Φ i a) = blk Φ i (ζ * a) := by
  classical
  rw [blk, twoPlane_apply, blk]
  congr 2
  funext l
  by_cases h : l = i
  · subst h
    simp [tpScal]
  · simp [Pi.single_eq_of_ne h]

theorem twoPlane_blk_right (hij : i ≠ j) (a : L) :
    twoPlane Φ hζ i j (blk Φ j a) = blk Φ j (ζ * a) := by
  classical
  rw [blk, twoPlane_apply, blk]
  congr 2
  funext l
  by_cases h : l = j
  · subst h
    simp [tpScal]
  · simp [Pi.single_eq_of_ne h]

theorem twoPlane_two (hij : i ≠ j) (a a' : L) :
    twoPlane Φ hζ i j (two Φ i j a a') = two Φ i j (ζ * a) (ζ * a') := by
  rw [two, two, map_add, twoPlane_blk_left hζ hij, twoPlane_blk_right hζ hij]

theorem twoPlane_fix {d : Fin s → L} (hi : d i = 0) (hj : d j = 0) (w : κ → K) :
    twoPlane Φ hζ i j (Φ (d, w)) = Φ (d, w) := by
  rw [twoPlane_apply]
  congr 2
  funext l
  unfold tpScal
  split_ifs with h
  · rcases h with rfl | rfl
    · rw [hi, mul_zero]
    · rw [hj, mul_zero]
  · rw [one_mul]

theorem twoPlane_pow_eq_one {p : ℕ} (hζp : ζ ^ p = 1) : twoPlane Φ hζ i j ^ p = 1 := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  rw [twoPlane_pow_apply, LinearEquiv.coe_one, id_eq]
  congr 2
  funext l
  unfold tpScal
  split_ifs <;> simp [hζp]

theorem twoPlane_ne_one (hζ1 : ζ ≠ 1) : twoPlane Φ hζ i j ≠ 1 := by
  classical
  intro h
  have h1 := congrArg (fun g : V ≃ₗ[K] V => Φ.symm (g (blk Φ i 1))) h
  simp only [blk, twoPlane_apply, LinearEquiv.coe_one, id_eq, LinearEquiv.symm_apply_apply] at h1
  have h2 := congrFun (congrArg Prod.fst h1) i
  simp only [Pi.single_eq_same, mul_one, tpScal, true_or, ite_true] at h2
  exact hζ1 h2

theorem twoPlane_commute {x : V →ₗ[K] V} {k : Fin s → ℕ}
    (hx : ∀ d w, x (Φ (d, w)) = Φ (fun l => ζ ^ k l * d l, w)) (v : V) :
    x (twoPlane Φ hζ i j v) = twoPlane Φ hζ i j (x v) := by
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  rw [twoPlane_apply, hx, hx, twoPlane_apply]
  congr 2
  funext l
  ring

theorem quad_twoPlane
    (hdec : ∀ d d' w w', polar Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + polar Q (Φ (0, w)) (Φ (0, w'))) (hij : i ≠ j)
    (hQi : ∀ a, Q (blk Φ i (ζ * a)) = Q (blk Φ i a))
    (hQj : ∀ a, Q (blk Φ j (ζ * a)) = Q (blk Φ j a)) (v : V) :
    Q (twoPlane Φ hζ i j v) = Q v := by
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  set r : Fin s → L := fun l => if l = i ∨ l = j then 0 else d l with hr
  have hri : r i = 0 := by simp [hr]
  have hrj : r j = 0 := by simp [hr]
  have hpol : ∀ a a', polar Q (two Φ i j a a') (Φ (r, w)) = 0 := by
    intro a a'
    rw [polar_comm, two, polar_add_right, polar_frame_blk hdec, polar_frame_blk hdec, hri, hrj,
      LinearMap.map_zero₂, LinearMap.map_zero₂, add_zero]
  have hdecomp : Φ (d, w) = two Φ i j (d i) (d j) + Φ (r, w) := frame_decomp hij d w
  rw [hdecomp, map_add, twoPlane_fix hζ hri hrj, twoPlane_two hζ hij,
    QuadraticMap.map_add (Q : V → K) (two Φ i j _ _), QuadraticMap.map_add (Q : V → K)
      (two Φ i j (d i) (d j)), hpol, hpol, quad_two hdec hij, quad_two hdec hij, hQi, hQj]

section Hyp

variable [CharP K 2]

omit [CharP K 2] in
theorem beta_eq_zero_of_span (hspan : ∀ a : L, ∃ y w : K, a = y • 1 + w • ζ)
    (hβnd : ∀ u, (∀ v, β u v = 0) → u = 0) {x : L} (h1 : β x 1 = 0) (hz : β x ζ = 0) :
    x = 0 := by
  refine hβnd x fun v => ?_
  obtain ⟨y, w, rfl⟩ := hspan v
  rw [map_add, map_smul, map_smul, h1, hz, smul_zero, smul_zero, add_zero]

omit [CharP K 2] in
theorem polar_fix_two
    (hdec : ∀ d d' w w', polar Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + polar Q (Φ (0, w)) (Φ (0, w'))) (hij : i ≠ j) (hζ1 : ζ ≠ 1)
    (hQi : ∀ a, Q (blk Φ i (ζ * a)) = Q (blk Φ i a))
    (hQj : ∀ a, Q (blk Φ j (ζ * a)) = Q (blk Φ j a)) {u : V}
    (hu : twoPlane Φ hζ i j u = u) (a a' : L) : polar Q u (two Φ i j a a') = 0 := by
  have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
  set x := two Φ i j ((ζ - 1)⁻¹ * a) ((ζ - 1)⁻¹ * a') with hx
  have hsub : ∀ b : L, ζ * ((ζ - 1)⁻¹ * b) - (ζ - 1)⁻¹ * b = b := fun b => by
    rw [← sub_one_mul, ← mul_assoc, mul_inv_cancel₀ hζ1', one_mul]
  have htwo : two Φ i j a a' = twoPlane Φ hζ i j x - x := by
    rw [hx, twoPlane_two hζ hij, two, two, two]
    conv_lhs => rw [← hsub a, ← hsub a']
    rw [blk_sub, blk_sub]
    abel
  have hiso : ∀ v w, polar Q (twoPlane Φ hζ i j v) (twoPlane Φ hζ i j w) = polar Q v w := by
    intro v w
    rw [polar, polar, ← map_add, quad_twoPlane hζ hdec hij hQi hQj,
      quad_twoPlane hζ hdec hij hQi hQj, quad_twoPlane hζ hdec hij hQi hQj]
  rw [htwo, polar_sub_right, ← hiso u x, hu, sub_self]

theorem exists_hyp_twoPlane
    (hdec : ∀ d d' w w', polar Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + polar Q (Φ (0, w)) (Φ (0, w'))) (hij : i ≠ j) (hζ1 : ζ ≠ 1)
    (hβalt : β.IsAlt) (hβnd : ∀ u, (∀ v, β u v = 0) → u = 0)
    (hspan : ∀ a : L, ∃ y w : K, a = y • 1 + w • ζ)
    (hQi : ∀ a, Q (blk Φ i (ζ * a)) = Q (blk Φ i a))
    (hQj : ∀ a, Q (blk Φ j (ζ * a)) = Q (blk Φ j a)) :
    ∃ (e f : Fin 2 → V) (y w : K), IsHypFamily Q e f ∧
      twoPlane Φ hζ i j (e 0) = (0 : K) • e 0 + (1 : K) • f 1 ∧
      twoPlane Φ hζ i j (e 1) = (0 : K) • e 1 + (1 : K) • f 0 ∧
      twoPlane Φ hζ i j (f 0) = y • e 1 + w • f 0 ∧
      twoPlane Φ hζ i j (f 1) = y • e 0 + w • f 1 ∧
      (∀ u, (∀ a, polar Q u (e a) = 0) → (∀ a, polar Q u (f a) = 0) →
        twoPlane Φ hζ i j u = u) ∧
      ∀ u, twoPlane Φ hζ i j u = u → ∀ a, polar Q u (e a) = 0 ∧ polar Q u (f a) = 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hβζ := beta_mul_eq hdec hQi
  have hQij := quad_blk_eq_of_inv hdec hζ1 hQi hQj
  have hc : β 1 ζ ≠ 0 := by
    intro h0
    have h1 : (1 : L) = 0 := beta_eq_zero_of_span hspan hβnd (hβalt 1) h0
    exact one_ne_zero h1
  set c := β 1 ζ with hcdef
  have hζ1' : ζ + 1 ≠ 0 := by
    intro h
    apply hζ1
    have hc2 : (2 : L) = 0 := by
      have h3 := congrArg (algebraMap K L) h2
      rwa [map_ofNat, map_zero] at h3
    linear_combination h - hc2
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  set b₀ : L := c⁻¹ • (ζ + 1)⁻¹ with hb₀
  have hsum : b₀ + ζ * b₀ = c⁻¹ • (1 : L) := by
    calc b₀ + ζ * b₀ = (ζ + 1) * b₀ := by ring
      _ = c⁻¹ • ((ζ + 1) * (ζ + 1)⁻¹) := by rw [hb₀, mul_smul_comm]
      _ = c⁻¹ • 1 := by rw [mul_inv_cancel₀ hζ1']
  have hsumζ : ζ * b₀ + ζ * (ζ * b₀) = c⁻¹ • ζ := by
    rw [← mul_add, hsum, mul_smul_comm, mul_one]
  have hcc : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  obtain ⟨y, w, hyw⟩ := hspan (ζ * ζ)
  have two_comb : ∀ (a b a' b' : L), two Φ i j (y • a + w • b) (y • a' + w • b') =
      y • two Φ i j a a' + w • two Φ i j b b' := by
    intro a b a' b'
    simp only [two, blk_add, blk_smul]
    module
  have hz2 : ∀ x : L, ζ * (ζ * x) = y • x + w • (ζ * x) := fun x => by
    rw [← mul_assoc, hyw, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  refine ⟨![two Φ i j 1 1, two Φ i j b₀ (ζ * b₀)],
    ![two Φ i j (ζ * b₀) (ζ * (ζ * b₀)), two Φ i j ζ ζ], y, w, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · show Q (two Φ i j 1 1) = 0
      rw [quad_two hdec hij, ← hQij, CharTwo.add_self_eq_zero]
    · show Q (two Φ i j b₀ (ζ * b₀)) = 0
      rw [quad_two hdec hij, hQj, ← hQij, CharTwo.add_self_eq_zero]
  · intro k
    fin_cases k
    · show Q (two Φ i j (ζ * b₀) (ζ * (ζ * b₀))) = 0
      rw [quad_two hdec hij, hQi, hQj, hQj, ← hQij, CharTwo.add_self_eq_zero]
    · show Q (two Φ i j ζ ζ) = 0
      rw [quad_two hdec hij, ← mul_one ζ, hQi, hQj, ← hQij, CharTwo.add_self_eq_zero]
  · intro a b
    fin_cases a <;> fin_cases b
    · show polar Q (two Φ i j 1 1) (two Φ i j 1 1) = 0
      rw [polar_two hdec hij, hβalt, add_zero]
    · show polar Q (two Φ i j 1 1) (two Φ i j b₀ (ζ * b₀)) = 0
      rw [polar_two hdec hij, ← map_add, hsum, map_smul, hβalt, smul_zero]
    · show polar Q (two Φ i j b₀ (ζ * b₀)) (two Φ i j 1 1) = 0
      rw [polar_two hdec hij, ← LinearMap.add_apply, ← map_add, hsum, map_smul,
        LinearMap.smul_apply, hβalt, smul_zero]
    · show polar Q (two Φ i j b₀ (ζ * b₀)) (two Φ i j b₀ (ζ * b₀)) = 0
      rw [polar_two hdec hij, hβalt, hβalt, add_zero]
  · intro a b
    fin_cases a <;> fin_cases b
    · show polar Q (two Φ i j (ζ * b₀) (ζ * (ζ * b₀))) (two Φ i j (ζ * b₀) (ζ * (ζ * b₀))) = 0
      rw [polar_two hdec hij, hβalt, hβalt, add_zero]
    · show polar Q (two Φ i j (ζ * b₀) (ζ * (ζ * b₀))) (two Φ i j ζ ζ) = 0
      rw [polar_two hdec hij, ← LinearMap.add_apply, ← map_add, hsumζ, map_smul,
        LinearMap.smul_apply, hβalt, smul_zero]
    · show polar Q (two Φ i j ζ ζ) (two Φ i j (ζ * b₀) (ζ * (ζ * b₀))) = 0
      rw [polar_two hdec hij, ← map_add, hsumζ, map_smul, hβalt, smul_zero]
    · show polar Q (two Φ i j ζ ζ) (two Φ i j ζ ζ) = 0
      rw [polar_two hdec hij, hβalt, add_zero]
  · intro a b
    fin_cases a <;> fin_cases b
    · show polar Q (two Φ i j 1 1) (two Φ i j (ζ * b₀) (ζ * (ζ * b₀))) = 1
      rw [polar_two hdec hij, ← map_add, hsumζ, map_smul, ← hcdef, smul_eq_mul, hcc]
    · show polar Q (two Φ i j 1 1) (two Φ i j ζ ζ) = 0
      rw [polar_two hdec hij, CharTwo.add_self_eq_zero]
    · show polar Q (two Φ i j b₀ (ζ * b₀)) (two Φ i j (ζ * b₀) (ζ * (ζ * b₀))) = 0
      rw [polar_two hdec hij, hβζ, CharTwo.add_self_eq_zero]
    · show polar Q (two Φ i j b₀ (ζ * b₀)) (two Φ i j ζ ζ) = 1
      rw [polar_two hdec hij, ← LinearMap.add_apply, ← map_add, hsum, map_smul,
        LinearMap.smul_apply, ← hcdef, smul_eq_mul, hcc]
  · show twoPlane Φ hζ i j (two Φ i j 1 1) = (0 : K) • two Φ i j 1 1 + (1 : K) • two Φ i j ζ ζ
    rw [twoPlane_two hζ hij, zero_smul, one_smul, zero_add, mul_one]
  · show twoPlane Φ hζ i j (two Φ i j b₀ (ζ * b₀)) =
      (0 : K) • two Φ i j b₀ (ζ * b₀) + (1 : K) • two Φ i j (ζ * b₀) (ζ * (ζ * b₀))
    rw [twoPlane_two hζ hij, zero_smul, one_smul, zero_add]
  · show twoPlane Φ hζ i j (two Φ i j (ζ * b₀) (ζ * (ζ * b₀))) =
      y • two Φ i j b₀ (ζ * b₀) + w • two Φ i j (ζ * b₀) (ζ * (ζ * b₀))
    rw [twoPlane_two hζ hij, ← two_comb, ← hz2 b₀, ← hz2 (ζ * b₀)]
  · show twoPlane Φ hζ i j (two Φ i j ζ ζ) = y • two Φ i j 1 1 + w • two Φ i j ζ ζ
    rw [twoPlane_two hζ hij, ← two_comb, ← hyw]
  · intro u he hf
    obtain ⟨⟨d', w'⟩, rfl⟩ := Φ.surjective u
    have hp2 : ∀ a a', polar Q (Φ (d', w')) (two Φ i j a a') = β (d' i) a + β (d' j) a' :=
      fun a a' => by rw [two, polar_add_right, polar_frame_blk hdec, polar_frame_blk hdec]
    have h0 := he 0
    have h1 := he 1
    have h2' := hf 0
    have h3 := hf 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hp2] at h0 h1 h2' h3
    have hsumij : d' i + d' j = 0 := by
      refine beta_eq_zero_of_span hspan hβnd ?_ ?_
      · rw [map_add, LinearMap.add_apply, h0]
      · rw [map_add, LinearMap.add_apply, h3]
    have hji : d' j = d' i := by
      rw [← CharTwo.neg_eq (d' i)]
      exact eq_neg_of_add_eq_zero_right hsumij
    rw [hji] at h1 h2'
    have hi0 : d' i = 0 := by
      refine beta_eq_zero_of_span hspan hβnd ?_ ?_
      · have h4 : β (d' i) (b₀ + ζ * b₀) = 0 := by rw [map_add, h1]
        rw [hsum, map_smul, smul_eq_mul] at h4
        exact (mul_eq_zero.mp h4).resolve_left (inv_ne_zero hc)
      · have h4 : β (d' i) (ζ * b₀ + ζ * (ζ * b₀)) = 0 := by rw [map_add, h2']
        rw [hsumζ, map_smul, smul_eq_mul] at h4
        exact (mul_eq_zero.mp h4).resolve_left (inv_ne_zero hc)
    exact twoPlane_fix hζ hi0 (hji.trans hi0) w'
  · intro u hu a
    have hfx := polar_fix_two hζ hdec hij hζ1 hQi hQj hu
    fin_cases a
    · exact ⟨hfx _ _, hfx _ _⟩
    · exact ⟨hfx _ _, hfx _ _⟩

end Hyp

end TwoPlane

end WitOmNs

end CFSG.StandardType
