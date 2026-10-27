module

public import CFSG.Permutation.FinPackPow
public import CFSG.Quasithin.Vol2.Ch3Sec3A6Act
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.H13.A6S13826bK

open Equiv Equiv.Perm CFSG.Permutation.FinPack

theorem h16 : 6 ≤ 16 := by norm_num

@[expose] noncomputable def cjB (r x t : ℕ) : Bool := evenK 6 t && Nat.beq (mulK 6 t r) (mulK 6 x t)

@[expose] noncomputable def exB (r x : ℕ) : Bool := !walkK 6 (fun t => !cjB r x t) 6 0 0 0

@[expose] noncomputable def q3 (x : ℕ) : Bool :=
  !evenK 6 x || !Nat.beq (powK 6 5517840 x 3) 5517840 || Nat.beq x 5517840 ||
    exB 5517345 x || exB 3489825 x

theorem q3_walk : walkK 6 q3 6 0 0 0 = true := by decide +kernel

@[expose] noncomputable def qN (g : ℕ) : Bool := !Nat.beq (mulK 6 g 5517345) (mulK 6 3489825 g)

theorem qN_walk : walkK 6 qN 6 0 0 0 = true := by decide +kernel

@[expose] noncomputable def qI (x : ℕ) : Bool :=
  !evenK 6 x || !Nat.beq (powK 6 5517840 x 3) 5517840 || exB x (invPK 6 x)

theorem qI_walk : walkK 6 qI 6 0 0 0 = true := by decide +kernel

theorem exB_sound {r x : Perm (Fin 6)} (h : exB (enc r) (enc x) = true) :
    ∃ g : Perm (Fin 6), sign g = 1 ∧ g * r * g⁻¹ = x := by
  rw [exB.eq_1, Bool.not_eq_true'] at h
  obtain ⟨g, hg⟩ := exists_of_walkK (P := cjB (enc r) (enc x)) h
  rw [cjB.eq_1, Bool.and_eq_true, ← enc_mul h16, ← enc_mul h16, beq_enc_iff h16] at hg
  exact ⟨g, (sign_eq_one_iff_evenK h16 g).2 hg.1, by rw [mul_inv_eq_iff_eq_mul]; exact hg.2⟩

theorem pow3_iff {x : Perm (Fin 6)} (he : enc (1 : Perm (Fin 6)) = 5517840) :
    x ^ 3 = 1 ↔ Nat.beq (powK 6 5517840 (enc x) 3) 5517840 = true := by
  rw [← enc_pow h16 he, ← he, beq_enc_iff h16]

theorem three_cases_K (a d : Perm (Fin 6)) (ha : enc a = 5517345) (hd : enc d = 3489825)
    (he : enc (1 : Perm (Fin 6)) = 5517840) : ∀ x : Perm (Fin 6), sign x = 1 → x ^ 3 = 1 →
    x ≠ 1 → (∃ g : Perm (Fin 6), sign g = 1 ∧ g * a * g⁻¹ = x) ∨
      (∃ g : Perm (Fin 6), sign g = 1 ∧ g * d * g⁻¹ = x) := by
  intro x h1 h2 h3
  have h := walkK_sound q3_walk x
  have e3 : Nat.beq (enc x) 5517840 = false := by
    rw [← he]
    exact beq_enc_false h16 h3
  rw [q3.eq_1, (sign_eq_one_iff_evenK h16 x).1 h1, (pow3_iff he).1 h2, e3, ← ha, ← hd] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
  rcases h with e | e
  · exact Or.inl (exB_sound e)
  · exact Or.inr (exB_sound e)

theorem not_conj_K (a d : Perm (Fin 6)) (ha : enc a = 5517345) (hd : enc d = 3489825) :
    ∀ g : Perm (Fin 6), g * a * g⁻¹ ≠ d := by
  intro g e
  have h := walkK_sound qN_walk g
  rw [qN.eq_1, ← ha, ← hd, ← enc_mul h16, ← enc_mul h16, Bool.not_eq_true'] at h
  rw [mul_inv_eq_iff_eq_mul] at e
  rw [e, Nat.beq_refl] at h
  cases h

theorem conj_inv_K (he : enc (1 : Perm (Fin 6)) = 5517840) : ∀ x : Perm (Fin 6), sign x = 1 →
    x ^ 3 = 1 → ∃ g : Perm (Fin 6), sign g = 1 ∧ g * x * g⁻¹ = x⁻¹ := by
  intro x h1 h2
  have h := walkK_sound qI_walk x
  rw [qI.eq_1, (sign_eq_one_iff_evenK h16 x).1 h1, (pow3_iff he).1 h2, ← enc_inv h16] at h
  simp only [Bool.not_true, Bool.false_or] at h
  exact exB_sound h

open CFSG.Quasithin.H13.A6Coc in
theorem fixCount_conj (g a : Perm (Fin 6)) : fixCount (g * a * g⁻¹) = fixCount a := by
  unfold fixCount
  refine Finset.card_bij' (fun v _ => act g⁻¹ v) (fun w _ => act g w) ?_ ?_ ?_ ?_
  · intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    calc act a (act g⁻¹ v) = act (a * g⁻¹) v := (act_mul a g⁻¹ v).symm
      _ = act (g⁻¹ * (g * a * g⁻¹)) v := by
        congr 1
        group
      _ = act g⁻¹ (act (g * a * g⁻¹) v) := act_mul _ _ v
      _ = act g⁻¹ v := by rw [hv.2]
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    calc act (g * a * g⁻¹) (act g w) = act (g * a * g⁻¹ * g) w := (act_mul _ _ w).symm
      _ = act (g * a) w := by
        congr 1
        group
      _ = act g (act a w) := act_mul _ _ w
      _ = act g w := by rw [hw.2]
  · intro v _
    rw [← act_mul, mul_inv_cancel, act_one]
  · intro w _
    rw [← act_mul, inv_mul_cancel, act_one]

end CFSG.Quasithin.H13.A6S13826bK
