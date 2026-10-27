module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGPDDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

private def pdo_fin81 (n : ℕ) : Fin 81 := ⟨n % 81, Nat.mod_lt _ (by norm_num)⟩

private def pdo_fin4 (n : ℕ) : Fin 4 := ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩

private def pdo_enc (v : Fin 4 → ZMod 3) : Fin 81 :=
  pdo_fin81 ((v 0).val * 27 + (v 1).val * 9 + (v 2).val * 3 + (v 3).val)

private def pdo_digitNat (c : Fin 81) (j : Fin 4) : ℕ :=
  c.val / 3 ^ (3 - j.val) % 3

private def pdo_dec (c : Fin 81) : Fin 4 → ZMod 3 := fun j => (pdo_digitNat c j : ZMod 3)

private def pdo_F (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (i : Fin 4) (c : Fin 81) : Fin 81 :=
  pdo_enc ((ggPDRefl M i).transpose.mulVec (pdo_dec c))

private def pdo_walk (f : Fin 4 → Fin 81 → Fin 81) : List (Fin 4) → Fin 81 → Fin 81
  | [], x => x
  | i :: w, x => pdo_walk f w (f i x)

private theorem pdo_enc_dec : ∀ c : Fin 81, pdo_enc (pdo_dec c) = c := by
  decide +kernel

private theorem pdo_dec_enc : ∀ (v : Fin 4 → ZMod 3) (j : Fin 4), pdo_dec (pdo_enc v) j = v j := by
  decide +kernel

private theorem pdo_dec_enc' (v : Fin 4 → ZMod 3) : pdo_dec (pdo_enc v) = v :=
  funext (pdo_dec_enc v)

private theorem pdo_enc_eq_zero : ∀ (u : Fin 4 → ZMod 3) (j : Fin 4),
    pdo_enc u = 0 → u j = 0 := by
  decide +kernel

private def pdo_wordsC : List (List ℕ) := [
  [], [], [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3], [], [3, 2, 1, 0, 2, 1, 2, 3], [3],
  [2, 1, 0, 2, 1, 2], [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2], [3, 2, 1, 0, 2, 1, 2],
  [2, 1, 2, 3, 2, 1, 0, 2, 1], [], [2, 3], [1, 0, 2, 1, 0, 2, 1, 3, 2], [3, 2, 1, 0, 2, 1, 3, 2],
  [3], [3, 2], [2], [3, 2, 1, 0, 2, 1, 2, 3, 2], [2, 1, 0, 3, 2, 1, 0, 2, 1], [2, 1, 0, 2, 1, 3],
  [1, 0, 2, 1, 0, 2, 1], [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1], [3, 2, 1, 0, 2, 1],
  [2, 1, 0, 2, 1], [3, 2], [1, 0, 2, 1, 0, 2, 1, 3], [3, 2, 1, 0, 2, 1, 3], [3, 2, 1, 0],
  [1, 0, 2, 1, 2, 3], [3, 2, 1, 2, 3], [2, 1, 0, 3, 2, 1, 2], [2, 1, 2, 3], [1, 0, 2, 1, 2],
  [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 2], [3, 2, 1, 2], [2, 1, 2], [1, 2, 1, 0], [2, 1, 3, 2, 1, 0],
  [2, 1, 0, 2, 3, 2, 1], [1, 2], [2, 1, 3, 2], [2, 1, 2, 3, 2, 1, 0], [1, 0, 2, 1],
  [2, 1, 0, 3, 2, 1], [2, 1, 2, 3, 2], [1, 0, 2, 1, 0, 2, 1, 3, 2, 1],
  [3, 2, 1, 0, 2, 1, 3, 2, 1], [1, 3], [3, 2, 1], [2, 1], [3, 2, 1, 0, 2, 1, 2, 3, 2, 1],
  [2, 1, 2, 3, 2, 1, 0, 2], [1], [2, 1, 3], [1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0],
  [3, 2, 1, 0, 2, 1, 3, 2, 1, 0], [1, 0, 3], [3, 2, 1, 0], [2, 1, 0],
  [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0], [2, 1, 2, 3, 2, 1, 2], [1, 0], [2, 1, 0, 3], [3, 2, 1],
  [1, 0, 2, 1, 0, 2, 3], [3, 2, 1, 0, 2, 3], [2, 1, 0, 3, 2, 1, 0, 2], [2, 1, 0, 2, 3],
  [1, 0, 2, 1, 0, 2], [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2], [3, 2, 1, 0, 2], [2, 1, 0, 2],
  [1, 2, 1], [2, 1, 3, 2, 1], [2, 1, 0, 2, 3, 2, 1, 0], [1, 0, 2], [2, 1, 0, 3, 2],
  [2, 1, 2, 3, 2, 1], [1, 0, 2, 1, 0], [2, 1, 0, 3, 2, 1, 0], [2, 1, 0, 2, 3, 2],
]

private def pdo_repLC : List ℕ := [
  0, 1, 1, 3, 1, 1, 3, 1, 1, 3, 10, 3, 10, 1, 10, 1, 3, 1, 3, 3, 10, 1, 1, 3, 10, 10, 1, 10, 10,
  1, 3, 3, 10, 1, 1, 3, 10, 3, 3, 10, 3, 3, 10, 3, 3, 10, 1, 10, 1, 3, 1, 3, 10, 3, 10, 1, 10, 1,
  3, 1, 3, 10, 3, 10, 10, 1, 3, 3, 10, 1, 1, 3, 10, 3, 3, 10, 3, 3, 10, 3, 3,
]

private def pdo_wordsCT : List (List ℕ) := [
  [], [], [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3], [], [3, 2, 1, 0, 2, 1, 2, 3], [3],
  [2, 1, 0, 2, 1, 2], [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2], [3, 2, 1, 0, 2, 1, 2],
  [2, 1, 0, 3, 2, 1, 0, 2, 1], [2, 1, 0, 2, 1, 3], [], [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1],
  [3, 2, 1, 0, 2, 1], [2, 1, 0, 2, 1], [1, 0, 2, 1, 0, 2, 1, 3, 2], [3], [3, 2, 1, 0, 2, 1, 3],
  [2, 1, 2, 3, 2, 1, 0, 2, 1], [1, 0, 2, 1, 0, 2, 1], [2, 3], [3, 2], [3, 2, 1, 0, 2, 1, 3, 2],
  [1, 0, 2, 1, 0, 2, 1, 3], [3, 2], [2], [3, 2, 1, 0, 2, 1, 2, 3, 2], [3, 2, 1, 0],
  [3, 2, 1, 0, 2, 1, 3, 2, 1, 0], [1, 0, 2, 1, 2, 3], [3, 2, 1, 0], [2, 1, 0],
  [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0], [2, 1, 2, 3, 2, 1, 2], [1, 0, 2, 1, 2], [2, 1, 0, 3],
  [1, 2, 1, 0], [2, 1, 3, 2, 1], [2, 1, 0, 2, 3, 2, 1, 0], [1, 0, 2, 1], [2, 1, 0, 3, 2],
  [2, 1, 2, 3, 2, 1], [1, 2], [2, 1, 0, 3, 2, 1, 0], [2, 1, 0, 2, 3, 2],
  [1, 0, 2, 1, 0, 2, 1, 3, 2, 1], [1, 3], [3, 2, 1, 0, 2, 3], [2, 1, 0, 3, 2, 1, 0, 2],
  [2, 1, 0, 2, 3], [1], [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2], [3, 2, 1, 0, 2], [2, 1, 0, 2],
  [1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0], [1, 0, 3], [3, 2, 1, 2, 3], [2, 1, 0, 3, 2, 1, 2],
  [2, 1, 2, 3], [1, 0], [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 2], [3, 2, 1, 2], [2, 1, 2], [3, 2, 1],
  [3, 2, 1, 0, 2, 1, 3, 2, 1], [1, 0, 2, 1, 0, 2, 3], [3, 2, 1], [2, 1],
  [3, 2, 1, 0, 2, 1, 2, 3, 2, 1], [2, 1, 2, 3, 2, 1, 0, 2], [1, 0, 2, 1, 0, 2], [2, 1, 3],
  [1, 2, 1], [2, 1, 3, 2, 1, 0], [2, 1, 0, 2, 3, 2, 1], [1, 0, 2, 1, 0], [2, 1, 3, 2],
  [2, 1, 2, 3, 2, 1, 0], [1, 0, 2], [2, 1, 0, 3, 2, 1], [2, 1, 2, 3, 2],
]

private def pdo_repLCT : List ℕ := [
  0, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 11, 1, 1, 3, 11, 11, 1, 3, 11, 3, 11, 1, 11, 1, 3, 1, 11, 1,
  11, 1, 3, 1, 3, 11, 3, 11, 3, 3, 11, 3, 3, 11, 3, 3, 11, 11, 1, 3, 3, 11, 1, 1, 3, 11, 11, 1, 3,
  3, 11, 1, 1, 3, 11, 1, 11, 1, 3, 1, 3, 11, 3, 11, 3, 3, 11, 3, 3, 11, 3, 3,
]

private def pdo_wordsOf (L : List (List ℕ)) (c : Fin 81) : List (Fin 4) :=
  (L.getD c.val []).map pdo_fin4

private def pdo_repOf (L : List ℕ) (c : Fin 81) : Fin 81 :=
  pdo_fin81 (L.getD c.val 0)

private theorem pdo_wordsC_correct :
    ∀ c : Fin 81, c ≠ 0 →
      pdo_walk (pdo_F ggPDC3) (pdo_wordsOf pdo_wordsC c) (pdo_repOf pdo_repLC c) = c := by
  decide +kernel

private theorem pdo_repC_card :
    ∀ c : Fin 81, c ≠ 0 → 24 ≤ ((Finset.univ.erase 0).filter
      (fun d : Fin 81 => pdo_repOf pdo_repLC d = pdo_repOf pdo_repLC c)).card := by
  decide +kernel

private theorem pdo_wordsCT_correct :
    ∀ c : Fin 81, c ≠ 0 →
      pdo_walk (pdo_F ggPDC3.transpose) (pdo_wordsOf pdo_wordsCT c)
        (pdo_repOf pdo_repLCT c) = c := by
  decide +kernel

private theorem pdo_repCT_card :
    ∀ c : Fin 81, c ≠ 0 → 24 ≤ ((Finset.univ.erase 0).filter
      (fun d : Fin 81 => pdo_repOf pdo_repLCT d = pdo_repOf pdo_repLCT c)).card := by
  decide +kernel

private theorem pdo_mat_invol (M : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hM : M = ggPDC3 ∨ M = ggPDC3.transpose) (i : Fin 4) :
    ggPDRefl M i * ggPDRefl M i = 1 := by
  rcases hM with rfl | rfl <;> fin_cases i <;> decide +kernel

private theorem pdo_T_invol (M : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hM : M = ggPDC3 ∨ M = ggPDC3.transpose) (i : Fin 4) (v : Fin 4 → ZMod 3) :
    (ggPDRefl M i).transpose.mulVec ((ggPDRefl M i).transpose.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, pdo_mat_invol M hM i,
      Matrix.transpose_one, Matrix.one_mulVec]

private theorem pdo_F_invol (M : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hM : M = ggPDC3 ∨ M = ggPDC3.transpose) (i : Fin 4) (c : Fin 81) :
    pdo_F M i (pdo_F M i c) = c := by
  simp only [pdo_F]
  rw [pdo_dec_enc', pdo_T_invol M hM i, pdo_enc_dec]

private theorem pdo_closed (M : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (S : Set (Fin 4 → ZMod 3))
    (hS : ∀ i, ∀ u ∈ S, (ggPDRefl M i).transpose.mulVec u ∈ S) :
    ∀ i c, pdo_dec c ∈ S → pdo_dec (pdo_F M i c) ∈ S := by
  intro i c hc
  have h := hS i (pdo_dec c) hc
  rw [show pdo_dec (pdo_F M i c) =
      (ggPDRefl M i).transpose.mulVec (pdo_dec c) from pdo_dec_enc' _]
  exact h

private theorem pdo_walk_forward {f : Fin 4 → Fin 81 → Fin 81} {P : Fin 81 → Prop}
    (hstep : ∀ i c, P c → P (f i c)) :
    ∀ (w : List (Fin 4)) (x : Fin 81), P x → P (pdo_walk f w x) := by
  intro w
  induction w with
  | nil => intro x hx; exact hx
  | cons i w ih => intro x hx; exact ih (f i x) (hstep i x hx)

private theorem pdo_walk_backward {f : Fin 4 → Fin 81 → Fin 81} {P : Fin 81 → Prop}
    (hback : ∀ i c, P (f i c) → P c) :
    ∀ (w : List (Fin 4)) (x : Fin 81), P (pdo_walk f w x) → P x := by
  intro w
  induction w with
  | nil => intro x hx; exact hx
  | cons i w ih => intro x hx; exact hback i x (ih (f i x) hx)

private theorem pdo_dec_injective : Function.Injective pdo_dec := by
  intro a b h
  have h2 := congrArg pdo_enc h
  rwa [pdo_enc_dec a, pdo_enc_dec b] at h2

private theorem pdo_orbit_aux (f : Fin 4 → Fin 81 → Fin 81) (S : Set (Fin 4 → ZMod 3))
    (hclosed : ∀ i c, pdo_dec c ∈ S → pdo_dec (f i c) ∈ S)
    (hinvol : ∀ i c, f i (f i c) = c)
    (u : Fin 4 → ZMod 3) (hu : u ∈ S) (hu0 : u ≠ 0)
    (words : List (List ℕ)) (reps : List ℕ)
    (hwords : ∀ c, c ≠ 0 → pdo_walk f (pdo_wordsOf words c) (pdo_repOf reps c) = c)
    (hcard : ∀ c, c ≠ 0 → 24 ≤ ((Finset.univ.erase 0).filter
      (fun d : Fin 81 => pdo_repOf reps d = pdo_repOf reps c)).card) :
    24 ≤ S.ncard := by
  set c₀ := pdo_enc u with hc₀
  have hc₀0 : c₀ ≠ 0 := by
    intro h
    rw [hc₀] at h
    exact hu0 (funext fun j => pdo_enc_eq_zero u j h)
  have hPc : pdo_dec c₀ ∈ S := by
    rw [hc₀, pdo_dec_enc']
    exact hu
  set r := pdo_repOf reps c₀ with hr
  have hback : ∀ i x, pdo_dec (f i x) ∈ S → pdo_dec x ∈ S := by
    intro i x hx
    have h := hclosed i (f i x) hx
    rwa [hinvol i x] at h
  have hr_mem : pdo_dec r ∈ S := by
    have hw := hwords c₀ hc₀0
    refine pdo_walk_backward (f := f) (P := fun x => pdo_dec x ∈ S) hback
      (pdo_wordsOf words c₀) r ?_
    rw [hr, hw]
    exact hPc
  set O : Finset (Fin 81) := (Finset.univ.erase 0).filter
    (fun d => pdo_repOf reps d = r) with hO
  have hOcard : 24 ≤ O.card := by
    have h := hcard c₀ hc₀0
    rw [← hr, ← hO] at h
    exact h
  have hOsub : ∀ d ∈ O, pdo_dec d ∈ S := by
    intro d hd
    have hd0 : d ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hd).1).1
    have hrd : pdo_repOf reps d = r := (Finset.mem_filter.mp hd).2
    have hw := hwords d hd0
    have hP : pdo_dec (pdo_walk f (pdo_wordsOf words d) r) ∈ S :=
      pdo_walk_forward (f := f) (P := fun x => pdo_dec x ∈ S) hclosed
        (pdo_wordsOf words d) r hr_mem
    rw [← hrd, hw] at hP
    exact hP
  have hsub : ((O.image pdo_dec : Finset (Fin 4 → ZMod 3)) : Set _) ⊆ S := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact hOsub d hd
  calc
    24 ≤ O.card := hOcard
    _ = (O.image pdo_dec).card :=
        (Finset.card_image_of_injective O pdo_dec_injective).symm
    _ = ((O.image pdo_dec : Finset (Fin 4 → ZMod 3)) : Set _).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ S.ncard := Set.ncard_le_ncard hsub

theorem ggPD_orbit_finite (M : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hM : M = ggPDC3 ∨ M = ggPDC3.transpose) (S : Set (Fin 4 → ZMod 3))
    (hS : ∀ i, ∀ u ∈ S, (ggPDRefl M i).transpose.mulVec u ∈ S)
    (u : Fin 4 → ZMod 3) (hu : u ∈ S) (hu0 : u ≠ 0) : 24 ≤ S.ncard := by
  rcases hM with rfl | rfl
  · exact pdo_orbit_aux (pdo_F ggPDC3) S (pdo_closed ggPDC3 S hS)
      (pdo_F_invol ggPDC3 (Or.inl rfl)) u hu hu0 pdo_wordsC pdo_repLC
      pdo_wordsC_correct pdo_repC_card
  · exact pdo_orbit_aux (pdo_F ggPDC3.transpose) S (pdo_closed ggPDC3.transpose S hS)
      (pdo_F_invol ggPDC3.transpose (Or.inr rfl)) u hu hu0 pdo_wordsCT pdo_repLCT
      pdo_wordsCT_correct pdo_repCT_card

end CFSG.StandardType

end
