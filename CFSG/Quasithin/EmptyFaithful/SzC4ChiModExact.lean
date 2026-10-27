module

public import CFSG.Quasithin.EmptyFaithful.SzC4ChiModDef
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Quasithin.SzC4.ChiMod

section Count

variable {A M B : Type} [Group A] [Group M] [Group B]

theorem card_eq_mul_of_exact (ι : A →* M) (π : M →* B) (hι : Function.Injective ι)
    (hex : ι.range = π.ker) (S : Subgroup M) (SA : Set A) (SB : Set B)
    (hA : ∀ a, ι a ∈ S ↔ a ∈ SA) (hB1 : ∀ m ∈ S, π m ∈ SB)
    (hB2 : ∀ b ∈ SB, ∃ m ∈ S, π m = b) : Nat.card S = Nat.card SA * Nat.card SB := by
  let f : S →* B := π.comp S.subtype
  have hker1 : ∀ a : A, π (ι a) = 1 := fun a =>
    MonoidHom.mem_ker.1 (hex ▸ (⟨a, rfl⟩ : ι a ∈ ι.range))
  have hker : Nat.card f.ker = Nat.card SA := by
    symm
    refine Nat.card_eq_of_bijective
      (fun a : SA => (⟨⟨ι a, (hA a).2 a.2⟩, MonoidHom.mem_ker.2 (hker1 a)⟩ : f.ker)) ⟨?_, ?_⟩
    · intro a a' h
      exact Subtype.ext (hι (congrArg (fun x : f.ker => (x.1 : M)) h))
    · rintro ⟨⟨m, hmS⟩, hmk⟩
      have hm1 : π m = 1 := MonoidHom.mem_ker.1 hmk
      obtain ⟨a, ha⟩ : m ∈ ι.range := hex ▸ MonoidHom.mem_ker.2 hm1
      exact ⟨⟨a, (hA a).1 (ha ▸ hmS)⟩, Subtype.ext (Subtype.ext ha)⟩
  have hrange : Nat.card f.range = Nat.card SB := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ?_)
    constructor
    · rintro ⟨⟨m, hm⟩, rfl⟩
      exact hB1 m hm
    · intro hb
      obtain ⟨m, hm, rfl⟩ := hB2 b hb
      exact ⟨⟨m, hm⟩, rfl⟩
  rw [← Subgroup.card_ker_mul_card_range f, hker, hrange]

end Count

section Idempotent

variable {M : Type} [Group M]

@[expose] def eP (φ : MulAut M) (x : M) : M :=
  φ (φ (φ (φ (φ (φ x))))) * φ (φ (φ (φ (φ x)))) * φ (φ (φ x)) * x

@[expose] def eT (φ : MulAut M) (x : M) : M :=
  φ (φ (φ (φ x))) * φ (φ x) * φ x * x

theorem eP_eq_of_mem (φ : MulAut M) {x : M} (hx : x ∈ Kp φ) : eP φ x = x := by
  have h := congrArg (fun y => φ (φ (φ y))) hx
  simp only [map_mul, map_one] at h
  rw [eP, h, one_mul]

theorem eT_eq_of_mem (φ : MulAut M) {x : M} (hx : x ∈ Kt φ) : eT φ x = x := by
  have h := congrArg (fun y => φ y) hx
  simp only [map_mul, map_one] at h
  rw [eT, h, one_mul]

theorem pow7_apply {φ : MulAut M} (h7 : φ ^ 7 = 1) (z : M) :
    φ (φ (φ (φ (φ (φ (φ z)))))) = z := by
  have := congrArg (fun f : MulAut M => f z) h7
  simpa [pow_succ, MulAut.mul_apply] using this

end Idempotent

section Commutative

variable {M : Type} [CommGroup M]

@[expose] def KpSub (φ : MulAut M) : Subgroup M where
  carrier := Kp φ
  mul_mem' {x y} hx hy := by
    have hx' : φ (φ (φ x)) * φ (φ x) * x = 1 := hx
    have hy' : φ (φ (φ y)) * φ (φ y) * y = 1 := hy
    show φ (φ (φ (x * y))) * φ (φ (x * y)) * (x * y) = 1
    simp only [map_mul]
    calc _ = (φ (φ (φ x)) * φ (φ x) * x) * (φ (φ (φ y)) * φ (φ y) * y) := by
          simp only [mul_comm, mul_left_comm, mul_assoc]
      _ = 1 := by rw [hx', hy', mul_one]
  one_mem' := by simp [Kp]
  inv_mem' {x} hx := by
    have hx' : φ (φ (φ x)) * φ (φ x) * x = 1 := hx
    show φ (φ (φ x⁻¹)) * φ (φ x⁻¹) * x⁻¹ = 1
    simp only [map_inv]
    rw [← mul_inv, ← mul_inv, hx', inv_one]

@[expose] def KtSub (φ : MulAut M) : Subgroup M where
  carrier := Kt φ
  mul_mem' {x y} hx hy := by
    have hx' : φ (φ (φ x)) * φ x * x = 1 := hx
    have hy' : φ (φ (φ y)) * φ y * y = 1 := hy
    show φ (φ (φ (x * y))) * φ (x * y) * (x * y) = 1
    simp only [map_mul]
    calc _ = (φ (φ (φ x)) * φ x * x) * (φ (φ (φ y)) * φ y * y) := by
          simp only [mul_comm, mul_left_comm, mul_assoc]
      _ = 1 := by rw [hx', hy', mul_one]
  one_mem' := by simp [Kt]
  inv_mem' {x} hx := by
    have hx' : φ (φ (φ x)) * φ x * x = 1 := hx
    show φ (φ (φ x⁻¹)) * φ x⁻¹ * x⁻¹ = 1
    simp only [map_inv]
    rw [← mul_inv, ← mul_inv, hx', inv_one]

theorem eP_mem (hM : ∀ x : M, x * x = 1) {φ : MulAut M} (h7 : φ ^ 7 = 1) (x : M) :
    eP φ x ∈ Kp φ := by
  have hxx : ∀ y z : M, y * (y * z) = z := fun y z => by rw [← mul_assoc, hM, one_mul]
  show φ (φ (φ (eP φ x))) * φ (φ (eP φ x)) * eP φ x = 1
  simp only [eP, map_mul, pow7_apply h7]
  simp only [mul_comm, mul_left_comm, hxx, hM]

theorem eT_mem (hM : ∀ x : M, x * x = 1) {φ : MulAut M} (h7 : φ ^ 7 = 1) (x : M) :
    eT φ x ∈ Kt φ := by
  have hxx : ∀ y z : M, y * (y * z) = z := fun y z => by rw [← mul_assoc, hM, one_mul]
  show φ (φ (φ (eT φ x))) * φ (eT φ x) * eT φ x = 1
  simp only [eT, map_mul, pow7_apply h7]
  simp only [mul_comm, mul_left_comm, hxx, hM]

end Commutative

section Exact

variable {A M B : Type} [Group A] [CommGroup M] [Group B]

theorem card_Kp_exact (hM : ∀ x : M, x * x = 1) (ι : A →* M) (π : M →* B)
    (hι : Function.Injective ι) (hπ : Function.Surjective π) (hex : ι.range = π.ker)
    (φA : MulAut A) (φM : MulAut M) (φB : MulAut B) (h7 : φM ^ 7 = 1)
    (h1 : ∀ a : A, φM (ι a) = ι (φA a)) (h2 : ∀ m : M, π (φM m) = φB (π m)) :
    Nat.card (Kp φM) = Nat.card (Kp φA) * Nat.card (Kp φB) := by
  refine card_eq_mul_of_exact ι π hι hex (KpSub φM) (Kp φA) (Kp φB) ?_ ?_ ?_
  · intro a
    have h : ι (φA (φA (φA a)) * φA (φA a) * a) = φM (φM (φM (ι a))) * φM (φM (ι a)) * ι a := by
      simp only [map_mul, h1]
    show φM (φM (φM (ι a))) * φM (φM (ι a)) * ι a = 1 ↔ φA (φA (φA a)) * φA (φA a) * a = 1
    rw [← h]
    exact map_eq_one_iff ι hι
  · intro m hm
    have hm' : φM (φM (φM m)) * φM (φM m) * m = 1 := hm
    have h : π (φM (φM (φM m)) * φM (φM m) * m) = φB (φB (φB (π m))) * φB (φB (π m)) * π m := by
      simp only [map_mul, h2]
    show φB (φB (φB (π m))) * φB (φB (π m)) * π m = 1
    rw [← h, hm', map_one]
  · intro b hb
    obtain ⟨m, rfl⟩ := hπ b
    refine ⟨eP φM m, eP_mem hM h7 m, ?_⟩
    simp only [eP, map_mul, h2]
    exact eP_eq_of_mem φB hb

theorem card_Kt_exact (hM : ∀ x : M, x * x = 1) (ι : A →* M) (π : M →* B)
    (hι : Function.Injective ι) (hπ : Function.Surjective π) (hex : ι.range = π.ker)
    (φA : MulAut A) (φM : MulAut M) (φB : MulAut B) (h7 : φM ^ 7 = 1)
    (h1 : ∀ a : A, φM (ι a) = ι (φA a)) (h2 : ∀ m : M, π (φM m) = φB (π m)) :
    Nat.card (Kt φM) = Nat.card (Kt φA) * Nat.card (Kt φB) := by
  refine card_eq_mul_of_exact ι π hι hex (KtSub φM) (Kt φA) (Kt φB) ?_ ?_ ?_
  · intro a
    have h : ι (φA (φA (φA a)) * φA a * a) = φM (φM (φM (ι a))) * φM (ι a) * ι a := by
      simp only [map_mul, h1]
    show φM (φM (φM (ι a))) * φM (ι a) * ι a = 1 ↔ φA (φA (φA a)) * φA a * a = 1
    rw [← h]
    exact map_eq_one_iff ι hι
  · intro m hm
    have hm' : φM (φM (φM m)) * φM m * m = 1 := hm
    have h : π (φM (φM (φM m)) * φM m * m) = φB (φB (φB (π m))) * φB (π m) * π m := by
      simp only [map_mul, h2]
    show φB (φB (φB (π m))) * φB (π m) * π m = 1
    rw [← h, hm', map_one]
  · intro b hb
    obtain ⟨m, rfl⟩ := hπ b
    refine ⟨eT φM m, eT_mem hM h7 m, ?_⟩
    simp only [eT, map_mul, h2]
    exact eT_eq_of_mem φB hb

end Exact

section Delta

theorem card_Kp_pos {X : Type} [Group X] [Finite X] (φ : MulAut X) : 0 < Nat.card (Kp φ) :=
  have : Nonempty (Kp φ) := ⟨⟨1, by simp [Kp]⟩⟩
  Nat.card_pos

theorem card_Kt_pos {X : Type} [Group X] [Finite X] (φ : MulAut X) : 0 < Nat.card (Kt φ) :=
  have : Nonempty (Kt φ) := ⟨⟨1, by simp [Kt]⟩⟩
  Nat.card_pos

theorem mul_comm_of_sq {M : Type} [Group M] (hM : ∀ x : M, x * x = 1) (x y : M) :
    x * y = y * x := by
  have hinv : ∀ z : M, z⁻¹ = z := fun z => inv_eq_of_mul_eq_one_right (hM z)
  calc x * y = (x * y)⁻¹ := (hinv _).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hinv, hinv]

theorem delta_exact {A M B : Type} [Group A] [Group M] [Group B] [Finite A] [Finite M] [Finite B]
    (hM : ∀ x : M, x * x = 1) (ι : A →* M) (π : M →* B) (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hex : ι.range = π.ker) (φA : MulAut A) (φM : MulAut M)
    (φB : MulAut B) (h7 : φM ^ 7 = 1) (h1 : ∀ a : A, φM (ι a) = ι (φA a))
    (h2 : ∀ m : M, π (φM m) = φB (π m)) : delta M φM = delta A φA + delta B φB := by
  let _ : CommGroup M := { ‹Group M› with mul_comm := mul_comm_of_sq hM }
  have hP := card_Kp_exact hM ι π hι hπ hex φA φM φB h7 h1 h2
  have hT := card_Kt_exact hM ι π hι hπ hex φA φM φB h7 h1 h2
  rw [delta, delta, delta, hP, hT, padicValNat.mul (card_Kp_pos φA).ne' (card_Kp_pos φB).ne',
    padicValNat.mul (card_Kt_pos φA).ne' (card_Kt_pos φB).ne']
  push_cast
  ring

end Delta

end CFSG.Quasithin.SzC4.ChiMod
