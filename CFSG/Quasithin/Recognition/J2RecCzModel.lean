module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.Quasithin.J2Cz

open Equiv

inductive F2 : Type
  | o : F2
  | i : F2
  deriving DecidableEq

namespace F2

instance : Fintype F2 := ⟨{o, i}, by intro x; cases x <;> decide⟩

@[expose] def add : F2 → F2 → F2
  | o, y => y
  | i, o => i
  | i, i => o

@[expose] def mul : F2 → F2 → F2
  | o, _ => o
  | i, y => y

@[expose] def toZ : F2 → ZMod 2
  | o => 0
  | i => 1

theorem toZ_add (a b : F2) : toZ (add a b) = toZ a + toZ b := by cases a <;> cases b <;> rfl

theorem toZ_mul (a b : F2) : toZ (mul a b) = toZ a * toZ b := by cases a <;> cases b <;> rfl

theorem toZ_o : toZ o = 0 := rfl

theorem toZ_injective : Function.Injective toZ := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem add_self (t : ZMod 2) : t + t = 0 := by
  fin_cases t <;> rfl

end F2

open F2

@[ext] structure QM where
  e : F2
  a : F2
  b : F2
  c : F2
  d : F2

namespace QM

instance : DecidableEq QM := fun p q =>
  decidable_of_iff (p.e = q.e ∧ p.a = q.a ∧ p.b = q.b ∧ p.c = q.c ∧ p.d = q.d) (by
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact QM.ext h1 h2 h3 h4 h5
    · rintro rfl
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

@[expose] def equivProd : QM ≃ F2 × F2 × F2 × F2 × F2 where
  toFun p := (p.e, p.a, p.b, p.c, p.d)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype QM := Fintype.ofEquiv _ equivProd.symm

@[expose] def cocyc (p q : QM) : F2 :=
  add (add (mul q.a (add (add p.b p.c) p.d)) (mul q.b (add p.c p.d))) (mul q.c p.d)

instance : Mul QM :=
  ⟨fun p q => ⟨add (add p.e q.e) (cocyc p q), add p.a q.a, add p.b q.b, add p.c q.c, add p.d q.d⟩⟩

instance : One QM := ⟨⟨o, o, o, o, o⟩⟩

instance : Inv QM := ⟨fun p => ⟨add p.e (cocyc p p), p.a, p.b, p.c, p.d⟩⟩

theorem mul_def (p q : QM) : p * q =
    ⟨add (add p.e q.e) (cocyc p q), add p.a q.a, add p.b q.b, add p.c q.c, add p.d q.d⟩ := rfl

theorem one_def : (1 : QM) = ⟨o, o, o, o, o⟩ := rfl

theorem inv_def (p : QM) : p⁻¹ = ⟨add p.e (cocyc p p), p.a, p.b, p.c, p.d⟩ := rfl

instance : Group QM where
  mul_assoc p q r := by
    ext <;> apply toZ_injective <;> simp only [mul_def, cocyc, toZ_add, toZ_mul] <;> ring
  one_mul p := by
    ext <;> apply toZ_injective <;> simp only [mul_def, one_def, cocyc, toZ_add, toZ_mul, toZ_o] <;>
      ring
  mul_one p := by
    ext <;> apply toZ_injective <;> simp only [mul_def, one_def, cocyc, toZ_add, toZ_mul, toZ_o] <;>
      ring
  inv_mul_cancel p := by
    ext <;> apply toZ_injective <;>
      simp only [mul_def, inv_def, one_def, cocyc, toZ_add, toZ_mul, toZ_o]
    · rw [show ∀ s t : ZMod 2, s + t + s + t = (s + s) + (t + t) from fun s t => by ring,
        add_self, add_self, add_zero]
    all_goals exact add_self _

@[expose] def z : QM := ⟨i, o, o, o, o⟩

@[expose] def x : Fin 5 → QM
  | 0 => ⟨o, i, i, i, i⟩
  | 1 => ⟨o, i, o, o, o⟩
  | 2 => ⟨o, o, i, o, o⟩
  | 3 => ⟨o, o, o, i, o⟩
  | 4 => ⟨o, o, o, o, i⟩

theorem z_sq : z * z = 1 := by decide

theorem z_ne_one : z ≠ 1 := by decide

theorem z_comm : ∀ p : QM, z * p = p * z := by decide +kernel

theorem x_sq : ∀ j, x j * x j = 1 := by decide +kernel

theorem x_anti : ∀ j k, j ≠ k → x k * x j = z * (x j * x k) := by decide +kernel

theorem x_prod : x 0 * x 1 * x 2 * x 3 * x 4 = 1 := by decide +kernel

theorem x_ne : ∀ j k, x j ≠ z * x k := by decide +kernel

theorem x_ne_one : ∀ j, x j ≠ 1 := by decide +kernel

theorem x_ne_z : ∀ j, x j ≠ z := by decide +kernel

theorem x_inj : ∀ j k, x j = x k → j = k := by decide +kernel

theorem zx_inj : ∀ j k, z * x j = z * x k → j = k := by decide +kernel

theorem eq_of_comm_x : ∀ p : QM, (∀ j, p * x j = x j * p) → p = 1 ∨ p = z := by
  decide +kernel

theorem eq_x_of_sq : ∀ p : QM, p * p = 1 → p ≠ 1 → p ≠ z → ∃ j, p = x j ∨ p = z * x j := by
  decide +kernel

theorem conj_x : ∀ h : QM, ∀ j, h * x j * h⁻¹ = x j ∨ h * x j * h⁻¹ = z * x j := by
  decide +kernel

theorem x_prod_perm : ∀ π : Perm (Fin 5),
    x (π 0) * x (π 1) * x (π 2) * x (π 3) * x (π 4) = 1 → Perm.sign π = 1 := by
  decide +kernel

end QM

open QM

section Lift

variable {G : Type*} [Group G]

@[expose] def pw (y : G) : F2 → G
  | o => 1
  | i => y

@[simp] theorem pw_o (y : G) : pw y o = 1 := rfl

@[simp] theorem pw_i (y : G) : pw y i = y := rfl

theorem pw_mul_pw {y : G} (hy : y * y = 1) (s t : F2) (g : G) :
    pw y s * (pw y t * g) = pw y (add s t) * g := by
  cases s <;> cases t <;> simp [add, ← mul_assoc, hy]

theorem pw_comm {w y : G} (h : w * y = y * w) (s t : F2) (g : G) :
    pw y t * (pw w s * g) = pw w s * (pw y t * g) := by
  cases s <;> cases t <;> simp [← mul_assoc, h]

theorem pw_swap {w y y' : G} (h : y' * y = w * (y * y')) (s t : F2) (g : G) :
    pw y' t * (pw y s * g) = pw w (F2.mul s t) * (pw y s * (pw y' t * g)) := by
  cases s <;> cases t <;> simp [F2.mul, ← mul_assoc, h]

theorem map_pw {H : Type*} [Group H] (f : G →* H) (y : G) (t : F2) : f (pw y t) = pw (f y) t := by
  cases t <;> simp

@[expose] def liftT (w : G) (y : Fin 4 → G) (p : QM) (g : G) : G :=
  pw w p.e * (pw (y 0) p.a * (pw (y 1) p.b * (pw (y 2) p.c * (pw (y 3) p.d * g))))

theorem liftT_eq_mul (w : G) (y : Fin 4 → G) (p : QM) (g : G) :
    liftT w y p g = liftT w y p 1 * g := by
  simp only [liftT, mul_one, mul_assoc]

theorem map_liftT {H : Type*} [Group H] (f : G →* H) (w : G) (y : Fin 4 → G) (p : QM) (g : G) :
    f (liftT w y p g) = liftT (f w) (fun j => f (y j)) p (f g) := by
  simp only [liftT, map_mul, map_pw]

structure LiftRel (w : G) (y : Fin 4 → G) : Prop where
  w_sq : w * w = 1
  w_comm : ∀ j, w * y j = y j * w
  y_sq : ∀ j, y j * y j = 1
  anti : ∀ i j, i < j → y j * y i = w * (y i * y j)

theorem LiftRel.liftT_mul {w : G} {y : Fin 4 → G} (h : LiftRel w y) (p q : QM) (g : G) :
    liftT w y p (liftT w y q g) = liftT w y (p * q) g := by
  have hc : ∀ j (s t : F2) (g : G), pw (y j) t * (pw w s * g) = pw w s * (pw (y j) t * g) :=
    fun j s t g => pw_comm (h.w_comm j) s t g
  have sw : ∀ i j, i < j → ∀ (s t : F2) (g : G),
      pw (y j) t * (pw (y i) s * g) = pw w (F2.mul s t) * (pw (y i) s * (pw (y j) t * g)) :=
    fun i j hij s t g => pw_swap (h.anti i j hij) s t g
  have m : ∀ j (s t : F2) (g : G), pw (y j) s * (pw (y j) t * g) = pw (y j) (add s t) * g :=
    fun j => pw_mul_pw (h.y_sq j)
  have mw : ∀ (s t : F2) (g : G), pw w s * (pw w t * g) = pw w (add s t) * g := pw_mul_pw h.w_sq
  simp only [liftT, QM.mul_def]
  rw [hc 3 q.e p.d, hc 2 q.e p.c, hc 1 q.e p.b, hc 0 q.e p.a, mw p.e q.e]
  rw [sw 0 3 (by decide) q.a p.d, hc 2 _ p.c, hc 1 _ p.b, hc 0 _ p.a, mw]
  rw [sw 0 2 (by decide) q.a p.c, hc 1 _ p.b, hc 0 _ p.a, mw]
  rw [sw 0 1 (by decide) q.a p.b, hc 0 _ p.a, mw, m 0 p.a q.a]
  rw [sw 1 3 (by decide) q.b p.d, hc 2 _ p.c, hc 1 _ p.b, hc 0 _ (add p.a q.a), mw]
  rw [sw 1 2 (by decide) q.b p.c, hc 1 _ p.b, hc 0 _ (add p.a q.a), mw, m 1 p.b q.b]
  rw [sw 2 3 (by decide) q.c p.d, hc 2 _ p.c, hc 1 _ (add p.b q.b), hc 0 _ (add p.a q.a), mw,
    m 2 p.c q.c, m 3 p.d q.d]
  congr 2
  apply toZ_injective
  simp only [QM.cocyc, toZ_add, toZ_mul]
  ring

@[expose] def LiftRel.liftHom {w : G} {y : Fin 4 → G} (h : LiftRel w y) : QM →* G where
  toFun p := liftT w y p 1
  map_one' := by simp [liftT, QM.one_def]
  map_mul' p q := by rw [← h.liftT_mul, liftT_eq_mul w y p]

theorem LiftRel.liftHom_apply {w : G} {y : Fin 4 → G} (h : LiftRel w y) (p : QM) :
    h.liftHom p = liftT w y p 1 := rfl

theorem liftT_x : ∀ p : QM, liftT z (fun j => x j.succ) p 1 = p := by
  decide +kernel

theorem eq_liftT (f : QM →* G) (p : QM) :
    f p = liftT (f z) (fun j => f (x j.succ)) p 1 := by
  conv_lhs => rw [← liftT_x p]
  rw [map_liftT, map_one]

theorem hom_ext {f g : QM →* G} (hz : f z = g z) (hx : ∀ j : Fin 4, f (x j.succ) = g (x j.succ)) :
    f = g := by
  ext p
  rw [eq_liftT f, eq_liftT g, hz]
  simp only [hx]

end Lift


theorem aut_z (α : MulAut QM) : α z = z := by
  have hc : ∀ j, α z * x j = x j * α z := by
    intro j
    calc α z * x j = α z * α (α.symm (x j)) := by rw [MulEquiv.apply_symm_apply]
      _ = α (z * α.symm (x j)) := (map_mul α _ _).symm
      _ = α (α.symm (x j) * z) := by rw [z_comm]
      _ = x j * α z := by rw [map_mul, MulEquiv.apply_symm_apply]
  rcases eq_of_comm_x (α z) hc with h | h
  · exact absurd (α.injective (h.trans (map_one α).symm)) z_ne_one
  · exact h

theorem aut_x (α : MulAut QM) (j : Fin 5) : ∃ k, α (x j) = x k ∨ α (x j) = z * x k := by
  refine eq_x_of_sq _ ?_ (fun h => x_ne_one j (α.injective (h.trans (map_one α).symm)))
    (fun h => x_ne_z j (α.injective (h.trans (aut_z α).symm)))
  rw [← map_mul, x_sq, map_one]

theorem eq_of_signed {k k' : Fin 5} {p : QM} (h : p = x k ∨ p = z * x k)
    (h' : p = x k' ∨ p = z * x k') : k = k' := by
  rcases h with rfl | rfl <;> rcases h' with h' | h'
  · exact x_inj _ _ h'
  · exact absurd h' (x_ne _ _)
  · exact absurd h'.symm (x_ne _ _)
  · exact zx_inj _ _ h'

@[expose] noncomputable def lineFun (α : MulAut QM) (j : Fin 5) : Fin 5 := (aut_x α j).choose

theorem lineFun_spec (α : MulAut QM) (j : Fin 5) :
    α (x j) = x (lineFun α j) ∨ α (x j) = z * x (lineFun α j) :=
  (aut_x α j).choose_spec

theorem lineFun_injective (α : MulAut QM) : Function.Injective (lineFun α) := by
  intro j j' hjj
  have h1 := lineFun_spec α j
  have h2 := lineFun_spec α j'
  rw [← hjj] at h2
  have hz : α z = z := aut_z α
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact x_inj _ _ (α.injective (h1.trans h2.symm))
  · exact absurd (α.injective (show α (x j') = α (z * x j) by rw [map_mul, hz, h1, h2]))
      (x_ne j' j)
  · exact absurd (α.injective (show α (x j) = α (z * x j') by rw [map_mul, hz, h1, h2]))
      (x_ne j j')
  · exact x_inj _ _ (α.injective (h1.trans h2.symm))

@[expose] noncomputable def linePerm (α : MulAut QM) : Perm (Fin 5) :=
  Equiv.ofBijective (lineFun α) (Finite.injective_iff_bijective.mp (lineFun_injective α))

theorem linePerm_spec (α : MulAut QM) (j : Fin 5) :
    α (x j) = x (linePerm α j) ∨ α (x j) = z * x (linePerm α j) :=
  lineFun_spec α j

theorem linePerm_eq {α : MulAut QM} {j k : Fin 5} (h : α (x j) = x k ∨ α (x j) = z * x k) :
    linePerm α j = k :=
  eq_of_signed (linePerm_spec α j).symm.symm h |>.symm.symm

theorem signed_map (α : MulAut QM) {p : QM} {k : Fin 5} (h : p = x k ∨ p = z * x k) :
    α p = x (linePerm α k) ∨ α p = z * x (linePerm α k) := by
  rcases h with rfl | rfl
  · exact linePerm_spec α k
  · rw [map_mul, aut_z]
    rcases linePerm_spec α k with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl (by rw [← mul_assoc, z_sq, one_mul])

@[expose] noncomputable def linePermHom : MulAut QM →* Perm (Fin 5) where
  toFun := linePerm
  map_one' := Equiv.ext fun _ => linePerm_eq (Or.inl rfl)
  map_mul' α β := Equiv.ext fun j => linePerm_eq (signed_map α (linePerm_spec β j))

theorem linePermHom_apply (α : MulAut QM) : linePermHom α = linePerm α := rfl

@[expose] noncomputable def L0 : Subgroup (MulAut QM) where
  carrier := {α | ∀ j, α (x j) = x (linePerm α j)}
  mul_mem' {α β} hα hβ j := by
    show α (β (x j)) = x (linePermHom (α * β) j)
    rw [hβ j, hα, map_mul]
    rfl
  one_mem' j := by
    show x j = x (linePermHom 1 j)
    rw [map_one]
    rfl
  inv_mem' {α} hα j := by
    have hk := linePerm_spec α⁻¹ j
    rcases hk with hk | hk
    · exact hk
    · exfalso
      have h1 : α (α⁻¹ (x j)) = x j := by simp
      rw [hk, map_mul, aut_z, hα] at h1
      have h2 : linePerm α (linePerm α⁻¹ j) = j := by
        have h3 := DFunLike.congr_fun (map_mul linePermHom α α⁻¹) j
        rw [mul_inv_cancel, map_one, Perm.mul_apply] at h3
        exact h3.symm
      rw [h2] at h1
      exact z_ne_one (by
        calc z = z * x j * (x j)⁻¹ := by group
          _ = 1 := by rw [h1, mul_inv_cancel])

theorem mem_L0 {α : MulAut QM} : α ∈ L0 ↔ ∀ j, α (x j) = x (linePerm α j) := Iff.rfl

theorem aut_ext {α β : MulAut QM} (h : ∀ j : Fin 4, α (x j.succ) = β (x j.succ)) : α = β := by
  have := hom_ext (f := α.toMonoidHom) (g := β.toMonoidHom) (by simp [aut_z]) (by simpa using h)
  exact MulEquiv.ext fun p => DFunLike.congr_fun this p

theorem linePerm_mem_alternatingGroup {α : MulAut QM} (hα : α ∈ L0) :
    linePerm α ∈ alternatingGroup (Fin 5) := by
  apply x_prod_perm
  rw [← hα 0, ← hα 1, ← hα 2, ← hα 3, ← hα 4, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
    x_prod, map_one]

theorem card_L0_le : Nat.card L0 ≤ 60 := by
  have hinj : Function.Injective fun α : L0 =>
      (⟨linePerm α, linePerm_mem_alternatingGroup α.2⟩ : alternatingGroup (Fin 5)) := by
    intro α β h
    have h' : linePerm (α : MulAut QM) = linePerm β := congrArg Subtype.val h
    refine Subtype.ext (aut_ext fun j => ?_)
    rw [α.2, β.2, h']
  have := Nat.card_le_card_of_injective _ hinj
  rwa [nat_card_alternatingGroup, Nat.card_fin, show Nat.factorial 5 / 2 = 60 from rfl] at this


@[expose] def pa : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def pb : Perm (Fin 5) := swap 0 4 * swap 0 2

theorem liftRel_perm (σ : Perm (Fin 5)) : LiftRel z (fun j : Fin 4 => x (σ j.succ)) :=
  ⟨z_sq, fun _ => z_comm _, fun _ => x_sq _, fun _ _ hij =>
    x_anti _ _ fun h => hij.ne (Fin.succ_injective _ (σ.injective h))⟩

@[expose] def phiAHom : QM →* QM := (liftRel_perm pa).liftHom

@[expose] def phiBHom : QM →* QM := (liftRel_perm pb).liftHom

theorem phiAHom_x : ∀ j, phiAHom (x j) = x (pa j) := by decide +kernel

theorem phiBHom_x : ∀ j, phiBHom (x j) = x (pb j) := by decide +kernel

theorem phiAHom_phiAHom (p : QM) : phiAHom (phiAHom p) = p := by
  have h : phiAHom.comp phiAHom = MonoidHom.id QM :=
    hom_ext (by decide +kernel) (by decide +kernel)
  exact DFunLike.congr_fun h p

theorem phiBHom_three (p : QM) : phiBHom (phiBHom (phiBHom p)) = p := by
  have h : phiBHom.comp (phiBHom.comp phiBHom) = MonoidHom.id QM :=
    hom_ext (by decide +kernel) (by decide +kernel)
  exact DFunLike.congr_fun h p

@[expose] def phiA : MulAut QM where
  toFun := phiAHom
  invFun := phiAHom
  left_inv := phiAHom_phiAHom
  right_inv := phiAHom_phiAHom
  map_mul' := map_mul phiAHom

@[expose] def phiB : MulAut QM where
  toFun := phiBHom
  invFun p := phiBHom (phiBHom p)
  left_inv := phiBHom_three
  right_inv := phiBHom_three
  map_mul' := map_mul phiBHom

theorem phiA_x (j : Fin 5) : phiA (x j) = x (pa j) := phiAHom_x j

theorem phiB_x (j : Fin 5) : phiB (x j) = x (pb j) := phiBHom_x j

theorem linePerm_phiA : linePerm phiA = pa := Equiv.ext fun j => linePerm_eq (Or.inl (phiA_x j))

theorem linePerm_phiB : linePerm phiB = pb := Equiv.ext fun j => linePerm_eq (Or.inl (phiB_x j))

theorem phiA_mem : phiA ∈ L0 := fun j => by rw [linePerm_phiA, phiA_x]

theorem phiB_mem : phiB ∈ L0 := fun j => by rw [linePerm_phiB, phiB_x]

@[expose] def sgn4 (s₀ s₁ s₂ s₃ : F2) : Fin 4 → F2
  | 0 => s₀
  | 1 => s₁
  | 2 => s₂
  | 3 => s₃

@[expose] def autS (σ : Perm (Fin 5)) (s : Fin 4 → F2) (p : QM) : QM :=
  liftT z (fun j => pw z (s j) * x (σ j.succ)) p 1

theorem check_sign_a : ∀ s₀ s₁ s₂ s₃ : F2,
    (∀ j : Fin 4, autS pa (sgn4 s₀ s₁ s₂ s₃) (autS pa (sgn4 s₀ s₁ s₂ s₃) (x j.succ)) = x j.succ) →
    ∀ j : Fin 4, (⟨o, s₀, o, s₁, o⟩ : QM) *
      autS pa (sgn4 s₀ s₁ s₂ s₃) ((⟨o, s₀, o, s₁, o⟩ : QM)⁻¹ * x j.succ * ⟨o, s₀, o, s₁, o⟩) *
        (⟨o, s₀, o, s₁, o⟩ : QM)⁻¹ = x (pa j.succ) := by
  decide +kernel

theorem check_sign_b : ∀ s₀ s₁ s₂ s₃ : F2,
    (∀ j : Fin 4, autS pb (sgn4 s₀ s₁ s₂ s₃) (autS pb (sgn4 s₀ s₁ s₂ s₃)
      (autS pb (sgn4 s₀ s₁ s₂ s₃) (x j.succ))) = x j.succ) →
    ∀ j : Fin 4, (⟨o, o, add s₁ s₃, add s₁ s₃, s₃⟩ : QM) * autS pb (sgn4 s₀ s₁ s₂ s₃)
        ((⟨o, o, add s₁ s₃, add s₁ s₃, s₃⟩ : QM)⁻¹ * x j.succ * ⟨o, o, add s₁ s₃, add s₁ s₃, s₃⟩) *
          (⟨o, o, add s₁ s₃, add s₁ s₃, s₃⟩ : QM)⁻¹ = x (pb j.succ) ∧
      (⟨o, o, add s₁ s₃, add s₁ s₃, s₃⟩ : QM) * phiAHom
        ((⟨o, o, add s₁ s₃, add s₁ s₃, s₃⟩ : QM)⁻¹ * x j.succ * ⟨o, o, add s₁ s₃, add s₁ s₃, s₃⟩) *
          (⟨o, o, add s₁ s₃, add s₁ s₃, s₃⟩ : QM)⁻¹ = x (pa j.succ) := by
  decide +kernel


theorem signed_conj (h : QM) {p : QM} {k : Fin 5} (hp : p = x k ∨ p = z * x k) :
    h * p * h⁻¹ = x k ∨ h * p * h⁻¹ = z * x k := by
  rcases hp with rfl | rfl
  · exact conj_x h k
  · rw [show h * (z * x k) * h⁻¹ = z * (h * x k * h⁻¹) by rw [← mul_assoc h z, ← z_comm h]; group]
    rcases conj_x h k with h1 | h1 <;> rw [h1]
    · exact Or.inr rfl
    · exact Or.inl (by rw [← mul_assoc, z_sq, one_mul])

theorem signed_aut {B : MulAut QM} {σ : Perm (Fin 5)}
    (hB : ∀ j, B (x j) = x (σ j) ∨ B (x j) = z * x (σ j))
    {p : QM} {k : Fin 5} (hp : p = x k ∨ p = z * x k) : B p = x (σ k) ∨ B p = z * x (σ k) := by
  rcases hp with rfl | rfl
  · exact hB k
  · rw [map_mul, aut_z]
    rcases hB k with h1 | h1 <;> rw [h1]
    · exact Or.inr rfl
    · exact Or.inl (by rw [← mul_assoc, z_sq, one_mul])

theorem eq_autS {A : MulAut QM} {σ : Perm (Fin 5)}
    (hA : ∀ j, A (x j) = x (σ j) ∨ A (x j) = z * x (σ j)) :
    ∃ s₀ s₁ s₂ s₃ : F2, ∀ p, A p = autS σ (sgn4 s₀ s₁ s₂ s₃) p := by
  have hs : ∀ j : Fin 4, ∃ t : F2, A (x j.succ) = pw z t * x (σ j.succ) := fun j => by
    rcases hA j.succ with h | h
    · exact ⟨o, by rw [h, pw_o, one_mul]⟩
    · exact ⟨i, by rw [h, pw_i]⟩
  choose t ht using hs
  refine ⟨t 0, t 1, t 2, t 3, fun p => ?_⟩
  have hsg : sgn4 (t 0) (t 1) (t 2) (t 3) = t := funext fun j => by fin_cases j <;> rfl
  rw [hsg]
  have := eq_liftT A.toMonoidHom p
  simp only [MulEquiv.coe_toMonoidHom] at this
  rw [this, aut_z]
  simp only [ht, autS]

theorem exists_conj_eq_phi {A B : MulAut QM}
    (hA : ∀ j, A (x j) = x (pa j) ∨ A (x j) = z * x (pa j))
    (hB : ∀ j, B (x j) = x (pb j) ∨ B (x j) = z * x (pb j)) (hA2 : A * A = 1)
    (hB3 : B * B * B = 1) : ∃ g : MulAut QM, g * A * g⁻¹ = phiA ∧ g * B * g⁻¹ = phiB := by
  obtain ⟨s₀, s₁, s₂, s₃, hAs⟩ := eq_autS hA
  set h₁ : QM := ⟨o, s₀, o, s₁, o⟩ with hh₁
  have hA' : MulAut.conj h₁ * A * (MulAut.conj h₁)⁻¹ = phiA := by
    refine aut_ext fun j => ?_
    have hc := check_sign_a s₀ s₁ s₂ s₃ (fun j => by
      rw [← hAs, ← hAs]
      exact DFunLike.congr_fun hA2 (x j.succ)) j
    rw [phiA_x, ← hc, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply,
      MulAut.conj_inv_apply, hAs]
  set B' := MulAut.conj h₁ * B * (MulAut.conj h₁)⁻¹ with hB'def
  have hB' : ∀ j, B' (x j) = x (pb j) ∨ B' (x j) = z * x (pb j) := fun j => by
    have h1 : B' (x j) = h₁ * B (h₁⁻¹ * x j * h₁⁻¹⁻¹) * h₁⁻¹ := by
      rw [hB'def, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply,
        inv_inv]
    rw [h1]
    exact signed_conj h₁ (signed_aut hB (signed_conj h₁⁻¹ (Or.inl rfl)))
  have hB'3 : B' * B' * B' = 1 := by
    calc B' * B' * B' = MulAut.conj h₁ * (B * B * B) * (MulAut.conj h₁)⁻¹ := by
          rw [hB'def]; group
      _ = 1 := by rw [hB3, mul_one, mul_inv_cancel]
  obtain ⟨t₀, t₁, t₂, t₃, hBs⟩ := eq_autS hB'
  set h₂ : QM := ⟨o, o, add t₁ t₃, add t₁ t₃, t₃⟩ with hh₂
  have hc2 := check_sign_b t₀ t₁ t₂ t₃ (fun j => by
    rw [← hBs, ← hBs, ← hBs]
    exact DFunLike.congr_fun hB'3 (x j.succ))
  refine ⟨MulAut.conj h₂ * MulAut.conj h₁, ?_, ?_⟩
  · rw [mul_inv_rev, show MulAut.conj h₂ * MulAut.conj h₁ * A * ((MulAut.conj h₁)⁻¹ *
      (MulAut.conj h₂)⁻¹) = MulAut.conj h₂ * (MulAut.conj h₁ * A * (MulAut.conj h₁)⁻¹) *
        (MulAut.conj h₂)⁻¹ by group, hA']
    refine aut_ext fun j => ?_
    rw [phiA_x, ← (hc2 j).2, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply,
      MulAut.conj_inv_apply]
    rfl
  · rw [mul_inv_rev, show MulAut.conj h₂ * MulAut.conj h₁ * B * ((MulAut.conj h₁)⁻¹ *
      (MulAut.conj h₂)⁻¹) = MulAut.conj h₂ * B' * (MulAut.conj h₂)⁻¹ by rw [hB'def]; group]
    refine aut_ext fun j => ?_
    rw [phiB_x, ← (hc2 j).1, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply,
      MulAut.conj_inv_apply, hBs]

@[expose] def innerOf (s₀ s₁ s₂ s₃ : F2) : QM :=
  ⟨o, add (add (add (add s₀ s₁) s₂) s₃) s₀, add (add (add (add s₀ s₁) s₂) s₃) s₁,
    add (add (add (add s₀ s₁) s₂) s₃) s₂, add (add (add (add s₀ s₁) s₂) s₃) s₃⟩

theorem check_inner : ∀ s₀ s₁ s₂ s₃ : F2, ∀ j : Fin 4,
    innerOf s₀ s₁ s₂ s₃ * x j.succ * (innerOf s₀ s₁ s₂ s₃)⁻¹ =
      pw z (sgn4 s₀ s₁ s₂ s₃ j) * x j.succ := by
  decide +kernel

theorem eq_conj_of_linePerm_eq_one {α : MulAut QM} (hα : linePerm α = 1) :
    ∃ h : QM, α = MulAut.conj h := by
  obtain ⟨s₀, s₁, s₂, s₃, hs⟩ := eq_autS (σ := 1) fun j => by
    have := linePerm_spec α j
    rwa [hα] at this
  refine ⟨innerOf s₀ s₁ s₂ s₃, aut_ext fun j => ?_⟩
  rw [hs, MulAut.conj_apply, check_inner]
  simp only [autS, liftT, Perm.one_apply]
  fin_cases j <;> simp [x, sgn4, pw]

theorem pa_sq : pa * pa = 1 := by decide

theorem pb_cube : pb * pb * pb = 1 := by decide

theorem pa_ne_one : pa ≠ 1 := by decide

theorem pb_ne_one : pb ≠ 1 := by decide

theorem papb_pow_five : (pa * pb) ^ 5 = 1 := by decide

theorem papb_ne_one : pa * pb ≠ 1 := by decide

theorem pa_mem : pa ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem pb_mem : pb ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup]
  decide

abbrev Model : Type := QM ⋊[L0.subtype] L0

end CFSG.Quasithin.J2Cz
