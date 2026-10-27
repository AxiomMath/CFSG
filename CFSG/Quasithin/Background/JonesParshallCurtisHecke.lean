module

public import CFSG.Quasithin.Background.JonesParshallCurtisWeyl
public import Certificates.Certificate17022


public section

namespace CFSG.Quasithin.JonesParshall.Curtis

open Matrix

@[expose] def rootE : Bool × Fin 4 → G5
  | (true, s) => xE s
  | (false, s) => yE s

@[expose] def rootProd (l : List (Bool × Fin 4)) : G5 := l.foldr (fun a g => rootE a * g) 1

theorem rootE_mul_self
    (a : Bool × Fin 4) : rootE a * rootE a = 1 := by
  obtain ⟨b, s⟩ := a
  cases b
  · exact yE_mul_self s
  · exact xE_mul_self s

theorem rootE_coe (a : Bool × Fin 4) :
    (rootE a : Matrix (Fin 5) (Fin 5) (ZMod 2)) = toMat (rootB a) := by
  obtain ⟨b, s⟩ := a
  cases b
  · exact yM_eq_toMat s
  · exact xM_eq_toMat s

theorem rootProd_cons (a : Bool × Fin 4) (l : List (Bool × Fin 4)) :
    rootProd (a :: l) = rootE a * rootProd l := rfl

theorem rootProd_append (l l' : List (Bool × Fin 4)) :
    rootProd (l ++ l') = rootProd l * rootProd l' := by
  induction l with
  | nil => simp [rootProd]
  | cons a l ih => rw [List.cons_append, rootProd_cons, rootProd_cons, ih, mul_assoc]

theorem rootProd_coe (l : List (Bool × Fin 4)) :
    (rootProd l : Matrix (Fin 5) (Fin 5) (ZMod 2)) = toMat (rootBM l) := by
  induction l with
  | nil => exact toMat_bone.symm
  | cons a l ih =>
    change (rootE a : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (rootProd l : Matrix (Fin 5) (Fin 5) _) =
      toMat (bmul (rootB a) (rootBM l))
    rw [ih, toMat_bmul, rootE_coe]

theorem rootProd_reverse_mul
    (l : List (Bool × Fin 4)) : rootProd l.reverse * rootProd l = 1 := by
  induction l with
  | nil => simp [rootProd]
  | cons a l ih =>
    rw [List.reverse_cons, rootProd_append, rootProd_cons a l]
    have e : rootProd [a] = rootE a := by simp [rootProd]
    rw [e, mul_assoc, ← mul_assoc (rootE a), rootE_mul_self, one_mul, ih]

theorem rootProd_mem_Ugrp
    {l : List (Bool × Fin 4)} (h : IsUpU (toMat (rootBM l))) :
    rootProd l ∈ Ugrp := by
  rw [mem_Ugrp, rootProd_coe]
  exact h

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G5 V)

@[expose] def fixU : Submodule (ZMod 2) V where
  carrier := {x | ∀ u ∈ Ugrp, ρ u x = x}
  add_mem' {a b} ha hb u hu := by rw [map_add, ha u hu, hb u hu]
  zero_mem' _ _ := map_zero _
  smul_mem' c x hx u hu := by rw [map_smul, hx u hu]

theorem mem_fixU {x : V} : x ∈ fixU ρ ↔ ∀ u ∈ Ugrp, ρ u x = x := Iff.rfl

theorem act_act (g h : G5) (x : V) : ρ g (ρ h x) = ρ (g * h) x := by
  rw [map_mul, Module.End.mul_apply]

theorem act_rootProd (l l' : List (Bool × Fin 4)) (x : V) :
    ρ (rootProd l) (ρ (rootProd l') x) = ρ (rootProd (l ++ l')) x := by
  rw [act_act, rootProd_append]

theorem act_eq_of_mem {g h : G5} (hgh : h⁻¹ * g ∈ Ugrp) {x : V} (hx : x ∈ fixU ρ) :
    ρ g x = ρ h x := by
  have e : g = h * (h⁻¹ * g) := by group
  rw [e, ← act_act, hx _ hgh]

theorem act_eq_of_words
    {l₁ l₂ : List (Bool × Fin 4)}
    (h : IsUpU (toMat (rootBM (l₂.reverse ++ l₁)))) {x : V} (hx : x ∈ fixU ρ) :
    ρ (rootProd l₁) x = ρ (rootProd l₂) x := by
  refine act_eq_of_mem ρ ?_ hx
  have e : (rootProd l₂)⁻¹ = rootProd l₂.reverse :=
    (eq_inv_of_mul_eq_one_left (rootProd_reverse_mul l₂)).symm
  rw [e, ← rootProd_append]
  exact rootProd_mem_Ugrp h

theorem add_self_zmod2 (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

@[expose] def Th (s : Fin 4) : V →ₗ[ZMod 2] V := ρ (yE s) + ρ (xE s * yE s)

theorem Th_apply (s : Fin 4) (x : V) : Th ρ s x = ρ (yE s) x + ρ (xE s * yE s) x := rfl

theorem sE_def (s : Fin 4) : sE s = xE s * yE s * xE s := rfl

theorem Th_words (s : Fin 4) (x : V) :
    Th ρ s x = ρ (rootProd [(false, s)]) x + ρ (rootProd [(true, s), (false, s)]) x := by
  rw [Th_apply]
  simp only [rootProd, List.foldr_cons, List.foldr_nil, rootE, mul_one]

theorem Th_rootProd (s : Fin 4) (l : List (Bool × Fin 4)) (x : V) :
    Th ρ s (ρ (rootProd l) x) =
      ρ (rootProd ((false, s) :: l)) x + ρ (rootProd ((true, s) :: (false, s) :: l)) x := by
  rw [Th_words, act_rootProd, act_rootProd]
  rfl

theorem fix_of_Qs {s : Fin 4} {x : V} (hx : x ∈ fixU ρ) {q : G5}
    (hq : IsQs s (q : Matrix (Fin 5) (Fin 5) (ZMod 2))) : ρ q (Th ρ s x) = Th ρ s x := by
  change ρ q (ρ (yE s) x + ρ (xE s * yE s) x) = ρ (yE s) x + ρ (xE s * yE s) x
  rw [map_add, act_act, act_act]
  congr 1
  · refine act_eq_of_mem ρ ?_ hx
    rw [yE_inv, mem_Ugrp]
    change IsUpU ((yE s : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
      ((q : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (yE s : Matrix (Fin 5) (Fin 5) (ZMod 2))))
    rw [← mul_assoc]
    exact (Qs_conj_y hq).1
  · refine act_eq_of_mem ρ ?_ hx
    rw [_root_.mul_inv_rev, yE_inv, xE_inv, mem_Ugrp]
    have h1 := Qs_conj_y (Qs_conj_x hq)
    change IsUpU ((yE s : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
      (xE s : Matrix (Fin 5) (Fin 5) (ZMod 2)) * ((q : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
        ((xE s : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (yE s : Matrix (Fin 5) (Fin 5) (ZMod 2)))))
    simpa only [mul_assoc] using h1.1

theorem Th_mem_fixU
    (s : Fin 4) {x : V} (hx : x ∈ fixU ρ) : Th ρ s x ∈ fixU ρ := by
  intro u hu
  rcases decomp_up (s := s) (show IsUpU (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) from hu) with h | h
  · exact fix_of_Qs ρ hx h
  · have hq := fix_of_Qs ρ hx (q := xE s * u) h
    have e : u = xE s * (xE s * u) := by rw [← mul_assoc, xE_mul_self, one_mul]
    rw [e, ← act_act, hq]
    change ρ (xE s) (ρ (yE s) x + ρ (xE s * yE s) x) = ρ (yE s) x + ρ (xE s * yE s) x
    rw [map_add, act_act, act_act, ← mul_assoc, xE_mul_self, one_mul, add_comm]

theorem Th_Th_checks : ∀ s : Fin 4,
    IsUpU (toMat (rootBM ([(true, s), (false, s)].reverse ++
      [(false, s), (true, s), (false, s)]))) ∧
    IsUpU (toMat (rootBM ([(false, s)].reverse ++ [(true, s), (false, s), (true, s), (false, s)])))
    ∧ IsUpU (toMat (rootBM (([] : List (Bool × Fin 4)).reverse ++ [(false, s), (false, s)]))) ∧
    IsUpU (toMat (rootBM (([] : List (Bool × Fin 4)).reverse ++
      [(true, s), (false, s), (false, s)]))) :=
  Certificates.certificate17022.1

theorem Th_Th
    (s : Fin 4) {x : V} (hx : x ∈ fixU ρ) : Th ρ s (Th ρ s x) = Th ρ s x := by
  obtain ⟨h1, h2, h3, h4⟩ := Th_Th_checks s
  have hx0 : ρ (rootProd []) x = x := by
    rw [show rootProd [] = (1 : G5) from rfl, map_one]
    rfl
  have e : Th ρ s x = Th ρ s (ρ (rootProd []) x) := by rw [hx0]
  rw [e, Th_rootProd, map_add, Th_rootProd, Th_rootProd, act_eq_of_words ρ h1 hx,
    act_eq_of_words ρ h2 hx, act_eq_of_words ρ h3 hx, act_eq_of_words ρ h4 hx, hx0,
    add_self_zmod2, zero_add, add_comm]

theorem rootProd_eq_of_bits {l l' : List (Bool × Fin 4)}
    (h : rootBM l = rootBM l') :
    rootProd l = rootProd l' :=
  Subtype.ext (by rw [rootProd_coe, rootProd_coe, h])

theorem comm_checks : ∀ s t : Fin 4, (s.val + 2 ≤ t.val ∨ t.val + 2 ≤ s.val) →
    rootBM [(false, s), (false, t)] = rootBM [(false, t), (false, s)] ∧
    rootBM [(true, s), (false, s), (false, t)] = rootBM [(false, t), (true, s), (false, s)] ∧
    rootBM [(false, s), (true, t), (false, t)] = rootBM [(true, t), (false, t), (false, s)] ∧
    rootBM [(true, s), (false, s), (true, t), (false, t)] =
      rootBM [(true, t), (false, t), (true, s), (false, s)] :=
  Certificates.certificate17022.2.1

theorem Th_comm
    {s t : Fin 4} (hst : s.val + 2 ≤ t.val ∨ t.val + 2 ≤ s.val) (x : V) :
    Th ρ s (Th ρ t x) = Th ρ t (Th ρ s x) := by
  obtain ⟨h1, h2, h3, h4⟩ := comm_checks s t hst
  have hx0 : ρ (rootProd []) x = x := by
    rw [show rootProd [] = (1 : G5) from rfl, map_one]
    rfl
  rw [← hx0, Th_rootProd, Th_rootProd, map_add, map_add, Th_rootProd, Th_rootProd, Th_rootProd,
    Th_rootProd, rootProd_eq_of_bits h1, rootProd_eq_of_bits h2, rootProd_eq_of_bits h3,
    rootProd_eq_of_bits h4]
  abel

theorem braid_checks : ∀ s : Fin 3,
    IsUpU (toMat (rootBM (
      [(true, s.succ), (false, s.succ), (false, s.castSucc), (true, s.succ),
        (false, s.succ)].reverse ++
      [(false, s.castSucc), (false, s.succ), (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(false, s.succ), (true, s.castSucc), (false, s.castSucc), (false, s.succ)].reverse ++
      [(false, s.castSucc), (false, s.succ), (true, s.castSucc),
        (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(false, s.succ), (false, s.castSucc), (true, s.succ), (false, s.succ)].reverse ++
      [(false, s.castSucc), (true, s.succ), (false, s.succ), (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(true, s.succ), (false, s.succ), (true, s.castSucc), (false, s.castSucc),
        (false, s.succ)].reverse ++
      [(false, s.castSucc), (true, s.succ), (false, s.succ), (true, s.castSucc),
        (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(true, s.succ), (false, s.succ), (false, s.castSucc), (false, s.succ)].reverse ++
      [(true, s.castSucc), (false, s.castSucc), (false, s.succ),
        (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(false, s.succ), (false, s.castSucc), (false, s.succ)].reverse ++
      [(true, s.castSucc), (false, s.castSucc), (false, s.succ),
        (true, s.castSucc), (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(false, s.succ), (true, s.castSucc), (false, s.castSucc), (true, s.succ),
        (false, s.succ)].reverse ++
      [(true, s.castSucc), (false, s.castSucc), (true, s.succ), (false, s.succ),
        (false, s.castSucc)]))) ∧
    IsUpU (toMat (rootBM (
      [(true, s.succ), (false, s.succ), (true, s.castSucc), (false, s.castSucc),
        (true, s.succ), (false, s.succ)].reverse ++
      [(true, s.castSucc), (false, s.castSucc), (true, s.succ), (false, s.succ),
        (true, s.castSucc), (false, s.castSucc)]))) :=
  Certificates.certificate17022.2.2.1

theorem Th_braid
    (s : Fin 3) {x : V} (hx : x ∈ fixU ρ) :
    Th ρ s.castSucc (Th ρ s.succ (Th ρ s.castSucc x)) =
      Th ρ s.succ (Th ρ s.castSucc (Th ρ s.succ x)) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := braid_checks s
  have hx0 : ρ (rootProd []) x = x := by
    rw [show rootProd [] = (1 : G5) from rfl, map_one]
    rfl
  rw [← hx0]
  simp only [Th_rootProd, map_add]
  rw [act_eq_of_words ρ c1 hx, act_eq_of_words ρ c2 hx, act_eq_of_words ρ c3 hx,
    act_eq_of_words ρ c4 hx, act_eq_of_words ρ c5 hx, act_eq_of_words ρ c6 hx,
    act_eq_of_words ρ c7 hx, act_eq_of_words ρ c8 hx]
  abel

theorem order_three_checks : ∀ s : Fin 4,
    (xE s * yE s) * (xE s * yE s) * (xE s * yE s) = 1 ∧ yE s = xE s * sE s * xE s ∧
      xE s * yE s = sE s * xE s :=
  Certificates.certificate17022.2.2.2

theorem Th_eq_zero_iff
    (s : Fin 4) {x : V} (hx : x ∈ fixU ρ) :
    Th ρ s x = 0 ↔ ρ (sE s) x = x := by
  obtain ⟨h3, hy, hxy⟩ := order_three_checks s
  have hxx : ρ (xE s) x = x := hx _ (xE_mem s)
  change ρ (yE s) x + ρ (xE s * yE s) x = 0 ↔ _
  constructor
  · intro h
    have e1 : ρ (xE s * yE s) x = ρ (yE s) x := by
      have := congrArg (fun z => z + ρ (xE s * yE s) x) h
      simp only [add_assoc, add_self_zmod2, add_zero, zero_add] at this
      exact this.symm
    have e2 : ρ (xE s * yE s) (ρ (yE s) x) = x := by
      rw [act_act, mul_assoc, yE_mul_self, mul_one, hxx]
    have e4 : ρ (xE s * yE s) (ρ (xE s * yE s) x) = x := by rw [e1, e2]
    have e5 : ρ (xE s * yE s) x = x := by
      have h' := congrArg (ρ (xE s * yE s)) e4
      rw [act_act, act_act, h3, map_one, Module.End.one_apply] at h'
      exact h'.symm
    rw [sE_def, ← act_act, hxx, e5]
  · intro h
    have e1 : ρ (yE s) x = x := by rw [hy, ← act_act, ← act_act, hxx, h, hxx]
    have e2 : ρ (xE s * yE s) x = x := by rw [hxy, ← act_act, hxx, h]
    rw [e1, e2, add_self_zmod2]

end CFSG.Quasithin.JonesParshall.Curtis
