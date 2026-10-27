module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolModel

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

structure FourFrame {W : Type} [CommGroup W] (a b : W) : Prop where
  sq : ∀ w : W, w * w = 1
  ne_a : a ≠ 1
  ne_b : b ≠ 1
  ne_ab : a ≠ b
  span : ∀ w : W, w = 1 ∨ w = a ∨ w = b ∨ w = a * b

namespace FourFrame

variable {W : Type} [CommGroup W] {a b : W}

theorem pow_two_eq_one (h : FourFrame a b) (w : W) : w ^ 2 = 1 := by
  rw [pow_two]
  exact h.sq w

theorem mul_ne_one (h : FourFrame a b) : a * b ≠ 1 := fun h1 =>
  h.ne_ab (by
    have h2 : a = b⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2]
    exact inv_eq_of_mul_eq_one_right (h.sq b))

theorem zmod_two_cases : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide

theorem val_zero_zmod_two : (0 : ZMod 2).val = 0 := rfl

theorem val_one_zmod_two : (1 : ZMod 2).val = 1 := rfl

@[expose] def psi (h : FourFrame a b) : Multiplicative (ZMod 2 × ZMod 2) →* W where
  toFun x := a ^ (Multiplicative.toAdd x).1.val * b ^ (Multiplicative.toAdd x).2.val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
    rw [← pow_eq_pow_mod _ (h.pow_two_eq_one a), ← pow_eq_pow_mod _ (h.pow_two_eq_one b),
      pow_add, pow_add]
    exact mul_mul_mul_comm _ _ _ _

theorem psi_apply (h : FourFrame a b) (i j : ZMod 2) :
    h.psi (Multiplicative.ofAdd (i, j)) = a ^ i.val * b ^ j.val := rfl

theorem psi_injective (h : FourFrame a b) : Function.Injective h.psi := by
  rw [injective_iff_map_eq_one]
  have hij : ∀ i j : ZMod 2, a ^ i.val * b ^ j.val = 1 → i = 0 ∧ j = 0 := by
    intro i j hx
    rcases zmod_two_cases i with rfl | rfl <;> rcases zmod_two_cases j with rfl | rfl <;>
      simp only [val_zero_zmod_two, val_one_zmod_two, pow_zero, pow_one, mul_one, one_mul]
        at hx ⊢
    all_goals first
      | exact ⟨trivial, trivial⟩
      | exact absurd hx h.ne_b
      | exact absurd hx h.ne_a
      | exact absurd hx h.mul_ne_one
  intro x hx
  have hx' : x = Multiplicative.ofAdd (Multiplicative.toAdd x) := rfl
  obtain ⟨h1, h2⟩ := hij _ _ hx
  rw [hx']
  apply Multiplicative.toAdd.injective
  exact Prod.ext h1 h2

theorem psi_surjective (h : FourFrame a b) : Function.Surjective h.psi := by
  intro w
  rcases h.span w with rfl | rfl | rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨Multiplicative.ofAdd (1, 0), by simp [psi_apply, val_one_zmod_two]⟩
  · exact ⟨Multiplicative.ofAdd (0, 1), by simp [psi_apply, val_one_zmod_two]⟩
  · exact ⟨Multiplicative.ofAdd (1, 1), by simp [psi_apply, val_one_zmod_two]⟩

noncomputable def equiv (h : FourFrame a b) : Multiplicative (ZMod 2 × ZMod 2) ≃* W :=
  MulEquiv.ofBijective h.psi ⟨h.psi_injective, h.psi_surjective⟩

theorem exists_mulEquiv {W' : Type} [CommGroup W'] {a' b' : W'} (h : FourFrame a b)
    (h' : FourFrame a' b') : ∃ e : W ≃* W', e a = a' ∧ e b = b' := by
  refine ⟨h.equiv.symm.trans h'.equiv, ?_, ?_⟩
  · have e1 : h.equiv (Multiplicative.ofAdd (1, 0)) = a := by
      show h.psi _ = a
      simp [psi_apply, val_one_zmod_two]
    have e2 : h'.equiv (Multiplicative.ofAdd (1, 0)) = a' := by
      show h'.psi _ = a'
      simp [psi_apply, val_one_zmod_two]
    have e3 : h.equiv.symm a = Multiplicative.ofAdd (1, 0) := by
      rw [MulEquiv.symm_apply_eq]
      exact e1.symm
    rw [MulEquiv.trans_apply, e3, e2]
  · have e1 : h.equiv (Multiplicative.ofAdd (0, 1)) = b := by
      show h.psi _ = b
      simp [psi_apply, val_one_zmod_two]
    have e2 : h'.equiv (Multiplicative.ofAdd (0, 1)) = b' := by
      show h'.psi _ = b'
      simp [psi_apply, val_one_zmod_two]
    have e3 : h.equiv.symm b = Multiplicative.ofAdd (0, 1) := by
      rw [MulEquiv.symm_apply_eq]
      exact e1.symm
    rw [MulEquiv.trans_apply, e3, e2]

theorem hom_ext {W' : Type} [CommGroup W'] (h : FourFrame a b) (f g : W →* W') (ha : f a = g a)
    (hb : f b = g b) : f = g := by
  ext w
  rcases h.span w with rfl | rfl | rfl | rfl
  · rw [map_one, map_one]
  · exact ha
  · exact hb
  · rw [map_mul, map_mul, ha, hb]

end FourFrame

@[expose] def s3d : Perm (Fin 3) := finRotate 3

@[expose] def s3t : Perm (Fin 3) := swap 0 1

theorem s3d_pow_three : s3d ^ 3 = 1 := by decide +kernel

theorem s3d_ne_one : s3d ≠ 1 := by decide +kernel

theorem s3t_mul_self : s3t * s3t = 1 := by decide +kernel

theorem s3t_mul_s3d : s3t * s3d = s3d * s3d * s3t := by decide +kernel

theorem s3d_mul_s3t : s3d * s3t = s3t * s3d * s3d := by decide +kernel

theorem s3_gen : ∀ σ : Perm (Fin 3), ∃ i < 3, ∃ j < 2, σ = s3d ^ i * s3t ^ j := by decide +kernel

theorem s3_sign_eq_one_iff : ∀ σ : Perm (Fin 3), Perm.sign σ = 1 ↔ ∃ i < 3, σ = s3d ^ i := by
  decide +kernel

theorem S3Syl_eq : S3Syl = Subgroup.zpowers s3t := rfl

theorem alternatingGroup_three : alternatingGroup (Fin 3) = Subgroup.zpowers s3d := by
  ext σ
  rw [Perm.mem_alternatingGroup, s3_sign_eq_one_iff,
    mem_zpowers_iff_of_pow_eq_one s3d_pow_three (by norm_num)]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

section Gens

variable (M : Model 3)

theorem s3_act_d_three (w : M.W) : M.act s3d (M.act s3d (M.act s3d w)) = w := by
  rw [← act_mul_apply, ← act_mul_apply, ← pow_two, ← pow_succ]
  rw [s3d_pow_three]
  simp

theorem s3_act_t_t (w : M.W) : M.act s3t (M.act s3t w) = w := by
  rw [← act_mul_apply, s3t_mul_self]
  simp

theorem s3_act_t_d (w : M.W) :
    M.act s3t (M.act s3d w) = M.act s3d (M.act s3d (M.act s3t w)) := by
  rw [← act_mul_apply, s3t_mul_s3d, act_mul_apply, act_mul_apply]

theorem s3_act_d_t (w : M.W) :
    M.act s3d (M.act s3t w) = M.act s3t (M.act s3d (M.act s3d w)) := by
  rw [← act_mul_apply, s3d_mul_s3t, act_mul_apply, act_mul_apply]

variable {M}

theorem isInvSub_top_of_gens {U : Subgroup M.W} (hd : ∀ u ∈ U, M.act s3d u ∈ U)
    (ht : ∀ u ∈ U, M.act s3t u ∈ U) : IsInvSub M ⊤ U := by
  have hd' := (isInvSub_zpowers_iff M s3d U).mpr hd
  have ht' := (isInvSub_zpowers_iff M s3t U).mpr ht
  intro b _ u hu
  obtain ⟨i, -, j, -, rfl⟩ := s3_gen b
  rw [act_mul_apply]
  exact hd' _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers s3d) i) _
    (ht' _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers s3t) j) _ hu)

theorem act_eq_of_gens {N : Model 3} (f : M.W → N.W)
    (hd : ∀ w, f (M.act s3d w) = N.act s3d (f w))
    (ht : ∀ w, f (M.act s3t w) = N.act s3t (f w)) (σ : Perm (Fin 3)) (w : M.W) :
    f (M.act σ w) = N.act σ (f w) := by
  have hpow : ∀ (g : Perm (Fin 3)), (∀ w, f (M.act g w) = N.act g (f w)) →
      ∀ k : ℕ, ∀ w, f (M.act (g ^ k) w) = N.act (g ^ k) (f w) := by
    intro g hg k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ', act_mul_apply, act_mul_apply, hg, ih]
  obtain ⟨i, -, j, -, rfl⟩ := s3_gen σ
  rw [act_mul_apply, act_mul_apply, hpow s3d hd i, hpow s3t ht j]

end Gens

@[expose] def Model.restrict {n : ℕ} (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U) :
    Model n where
  W := U
  grp := Subgroup.toCommGroup U
  fin := inferInstance
  act :=
    { toFun := fun σ =>
        { toFun := fun u => ⟨M.act σ (u : M.W), hU σ (Subgroup.mem_top σ) u u.2⟩
          invFun := fun u => ⟨M.act σ⁻¹ (u : M.W), hU σ⁻¹ (Subgroup.mem_top _) u u.2⟩
          left_inv := fun u => Subtype.ext (act_inv_act M σ (u : M.W))
          right_inv := fun u => Subtype.ext (act_act_inv M σ (u : M.W))
          map_mul' := fun u v => Subtype.ext (map_mul (M.act σ) (u : M.W) (v : M.W)) }
      map_one' := MulEquiv.ext fun u => Subtype.ext (by simp)
      map_mul' := fun σ τ => MulEquiv.ext fun u => Subtype.ext (act_mul_apply M σ τ (u : M.W)) }
  sq := fun u => Subtype.ext (M.sq u)

theorem Model.restrict_act {n : ℕ} (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U)
    (σ : Perm (Fin n)) (u : (M.restrict U hU).W) :
    Subtype.val ((M.restrict U hU).act σ u) = M.act σ (Subtype.val u) := rfl

end CFSG.Quasithin.F53Mod
