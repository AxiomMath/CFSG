module

public import CFSG.OddTranspositions.PartThree.Eleven.Five.FiveFormAux

public section

namespace CFSG.OddTranspositions.PartThree

private theorem zero_ne_last (k : ℕ) : (0 : Fin (k + 2)) ≠ Fin.last (k + 1) := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_last] at this
  omega

private theorem fiveForm_single_self (n : ℕ) (ε : Bool) (i : Fin (n + 1))
    (hi : i ≠ Fin.last n) :
    fiveForm n ε (Pi.single i 1) (Pi.single i 1) = 1 := by
  rw [fiveForm_single n ε (Pi.single i 1) i, if_neg hi, Pi.single_eq_same, one_mul]

private theorem fiveForm_single_last (n : ℕ) (ε : Bool) :
    fiveForm n ε (Pi.single (Fin.last n) 1) (Pi.single (Fin.last n) 1) =
      -(if ε then 1 else 2) := by
  rw [fiveForm_single n ε (Pi.single (Fin.last n) 1) (Fin.last n), if_pos rfl,
    Pi.single_eq_same, mul_one]

private theorem fiveForm_single_zero (n : ℕ) (ε : Bool) {i j : Fin (n + 1)} (hij : i ≠ j) :
    fiveForm n ε (Pi.single i 1) (Pi.single j 1) = 0 := by
  rw [fiveForm_single n ε (Pi.single i 1) j]
  simp [hij]

private def shiftCoord (k : ℕ) : Fin (k + 2) → (Fin (k + 1) → ZMod 5) →ₗ[ZMod 5] ZMod 5 :=
  Fin.cases 0 (fun i : Fin (k + 1) =>
    LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5) i)

private def shiftMap (k : ℕ) :
    (Fin (k + 1) → ZMod 5) →ₗ[ZMod 5] (Fin (k + 2) → ZMod 5) :=
  LinearMap.pi (shiftCoord k)

private theorem shiftMap_apply_zero (k : ℕ) (z : Fin (k + 1) → ZMod 5) :
    shiftMap k z 0 = 0 := by
  simp [shiftMap, shiftCoord, LinearMap.pi_apply]

private theorem shiftMap_apply_succ (k : ℕ) (z : Fin (k + 1) → ZMod 5) (i : Fin (k + 1)) :
    shiftMap k z i.succ = z i := by
  simp [shiftMap, shiftCoord, LinearMap.pi_apply]

private theorem shiftMap_apply_zero' (k : ℕ) (z : Fin (k + 1) → ZMod 5) :
    shiftMap k z (Fin.castSucc (0 : Fin (k + 1))) = 0 := by
  rw [show (Fin.castSucc (0 : Fin (k + 1)) : Fin (k + 2)) = 0 from rfl]
  exact shiftMap_apply_zero k z

private theorem shiftMap_injective (k : ℕ) : Function.Injective (shiftMap k) := by
  intro x y h
  funext i
  have := congrFun h i.succ
  rwa [shiftMap_apply_succ, shiftMap_apply_succ] at this

private theorem shiftMap_isom (k : ℕ) (ε : Bool) (x y : Fin (k + 1) → ZMod 5) :
    fiveForm (k + 1) ε (shiftMap k x) (shiftMap k y) = fiveForm k ε x y := by
  rw [fiveForm, fiveForm, Fin.sum_univ_succ]
  rw [show shiftMap k x (Fin.castSucc (0 : Fin (k + 1))) = 0 from shiftMap_apply_zero' k x,
    show shiftMap k y (Fin.castSucc (0 : Fin (k + 1))) = 0 from shiftMap_apply_zero' k y]
  rw [Finset.sum_congr rfl (fun i _ => by
        rw [show shiftMap k x ((i.succ).castSucc) = x i.castSucc from
              shiftMap_apply_succ k x i.castSucc,
            show shiftMap k y ((i.succ).castSucc) = y i.castSucc from
              shiftMap_apply_succ k y i.castSucc]),
    show shiftMap k x (Fin.last (k + 1)) = x (Fin.last k) from
      shiftMap_apply_succ k x (Fin.last k),
    show shiftMap k y (Fin.last (k + 1)) = y (Fin.last k) from
      shiftMap_apply_succ k y (Fin.last k)]
  ring

private def case2Coord (k : ℕ) : Fin (k + 2) → (Fin (k + 1) → ZMod 5) →ₗ[ZMod 5] ZMod 5 :=
  Fin.cons ((2 : ZMod 5) • LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5) (Fin.last k))
    (Fin.snoc (fun i : Fin k =>
        LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5) i.castSucc)
      (LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5) (Fin.last k)))

private def case2Map (k : ℕ) :
    (Fin (k + 1) → ZMod 5) →ₗ[ZMod 5] (Fin (k + 2) → ZMod 5) :=
  LinearMap.pi (case2Coord k)

private theorem case2Map_apply_zero (k : ℕ) (z : Fin (k + 1) → ZMod 5) :
    case2Map k z 0 = 2 * z (Fin.last k) := by
  simp [case2Map, case2Coord, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul]

private theorem case2Map_apply_succ (k : ℕ) (z : Fin (k + 1) → ZMod 5) (i : Fin k) :
    case2Map k z (i.castSucc.succ) = z i.castSucc := by
  simp [case2Map, case2Coord, LinearMap.pi_apply, LinearMap.proj_apply, Fin.snoc_castSucc]

private theorem case2Map_apply_zero' (k : ℕ) (z : Fin (k + 1) → ZMod 5) :
    case2Map k z (Fin.castSucc (0 : Fin (k + 1))) = 2 * z (Fin.last k) := by
  rw [show (Fin.castSucc (0 : Fin (k + 1)) : Fin (k + 2)) = 0 from rfl]
  exact case2Map_apply_zero k z

private theorem case2Map_apply_last (k : ℕ) (z : Fin (k + 1) → ZMod 5) :
    case2Map k z (Fin.last (k + 1)) = z (Fin.last k) := by
  change case2Map k z ((Fin.last k).succ) = z (Fin.last k)
  simp [case2Map, case2Coord, LinearMap.pi_apply, LinearMap.proj_apply, Fin.snoc_last]

private theorem case2Map_injective (k : ℕ) : Function.Injective (case2Map k) := by
  intro x y h
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · have h1 := congrFun h (j.castSucc.succ)
    rwa [case2Map_apply_succ, case2Map_apply_succ] at h1
  · have h1 := congrFun h (Fin.last (k + 1))
    rwa [case2Map_apply_last, case2Map_apply_last] at h1

private theorem case2Map_isom (k : ℕ) (x y : Fin (k + 1) → ZMod 5) :
    fiveForm (k + 1) true (case2Map k x) (case2Map k y) = fiveForm k false x y := by
  rw [fiveForm, fiveForm, Fin.sum_univ_succ]
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [show case2Map k x (Fin.castSucc (0 : Fin (k + 1))) = 2 * x (Fin.last k) from
        case2Map_apply_zero' k x,
      show case2Map k y (Fin.castSucc (0 : Fin (k + 1))) = 2 * y (Fin.last k) from
        case2Map_apply_zero' k y]
  rw [Finset.sum_congr rfl (fun i _ => by
        rw [show case2Map k x ((i.succ).castSucc) = x i.castSucc from
              case2Map_apply_succ k x i,
            show case2Map k y ((i.succ).castSucc) = y i.castSucc from
              case2Map_apply_succ k y i]),
    show case2Map k x (Fin.last (k + 1)) = x (Fin.last k) from case2Map_apply_last k x,
    show case2Map k y (Fin.last (k + 1)) = y (Fin.last k) from case2Map_apply_last k y]
  ring_nf
  rw [show (3 : ZMod 5) = -2 by decide]
  ring

private def case3Coord (k : ℕ) : Fin (k + 2) → (Fin (k + 1) → ZMod 5) →ₗ[ZMod 5] ZMod 5 :=
  Fin.snoc (Fin.snoc (fun i : Fin k =>
      LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5) i.castSucc)
    ((2 : ZMod 5) • LinearMap.proj (R := ZMod 5) (φ := fun _ => ZMod 5) (Fin.last k))) 0

private def case3Map (k : ℕ) :
    (Fin (k + 1) → ZMod 5) →ₗ[ZMod 5] (Fin (k + 2) → ZMod 5) :=
  LinearMap.pi (case3Coord k)

private theorem case3Map_apply_mid (k : ℕ) (z : Fin (k + 1) → ZMod 5) (i : Fin k) :
    case3Map k z (i.castSucc.castSucc) = z i.castSucc := by
  simp [case3Map, case3Coord, LinearMap.pi_apply, LinearMap.proj_apply, Fin.snoc_castSucc]

private theorem case3Map_apply_lastk (k : ℕ) (z : Fin (k + 1) → ZMod 5) :
    case3Map k z ((Fin.last k).castSucc) = 2 * z (Fin.last k) := by
  simp [case3Map, case3Coord, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul, Fin.snoc_castSucc, Fin.snoc_last]

private theorem case3Map_apply_last (k : ℕ) (z : Fin (k + 1) → ZMod 5) :
    case3Map k z (Fin.last (k + 1)) = 0 := by
  simp [case3Map, case3Coord, LinearMap.pi_apply, Fin.snoc_last]

private theorem case3Map_injective (k : ℕ) : Function.Injective (case3Map k) := by
  intro x y h
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · have h1 := congrFun h (j.castSucc.castSucc)
    rwa [case3Map_apply_mid, case3Map_apply_mid] at h1
  · have h1 := congrFun h ((Fin.last k).castSucc)
    rw [case3Map_apply_lastk, case3Map_apply_lastk] at h1
    have h2 := congrArg (fun t => (3 : ZMod 5) * t) h1
    rw [← mul_assoc, ← mul_assoc, show (3 : ZMod 5) * 2 = 1 by decide, one_mul, one_mul] at h2
    exact h2

private theorem case3Map_isom (k : ℕ) (x y : Fin (k + 1) → ZMod 5) :
    fiveForm (k + 1) false (case3Map k x) (case3Map k y) = fiveForm k true x y := by
  rw [fiveForm, fiveForm, Fin.sum_univ_castSucc]
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [show case3Map k x ((Fin.last k).castSucc) = 2 * x (Fin.last k) from
        case3Map_apply_lastk k x,
      show case3Map k y ((Fin.last k).castSucc) = 2 * y (Fin.last k) from
        case3Map_apply_lastk k y,
      show case3Map k x (Fin.last (k + 1)) = 0 from case3Map_apply_last k x,
      show case3Map k y (Fin.last (k + 1)) = 0 from case3Map_apply_last k y]
  rw [Finset.sum_congr rfl (fun i _ => by
        rw [show case3Map k x (i.castSucc.castSucc) = x i.castSucc from
              case3Map_apply_mid k x i,
            show case3Map k y (i.castSucc.castSucc) = y i.castSucc from
              case3Map_apply_mid k y i])]
  ring_nf
  rw [show (4 : ZMod 5) = -1 by decide]
  ring

structure FiveAdjoin (k : ℕ) (ε π : Bool) where
  a : Fin (k + 2) → ZMod 5
  j : (Fin (k + 1) → ZMod 5) →ₗ[ZMod 5] (Fin (k + 2) → ZMod 5)
  sign_a : fiveForm (k + 1) (ε == π) a a ≠ 0 ∧
    (IsSquare (fiveForm (k + 1) (ε == π) a a) ↔ π = true)
  inj : Function.Injective j
  isom : ∀ x y, fiveForm (k + 1) (ε == π) (j x) (j y) = fiveForm k ε x y
  perp : ∀ x, fiveForm (k + 1) (ε == π) (j x) a = 0

theorem nonempty_fiveAdjoin (k : ℕ) (ε π : Bool) : Nonempty (FiveAdjoin k ε π) := by
  cases π with
  | true =>
    have hε' : (ε == true) = ε := by cases ε <;> rfl
    refine ⟨Pi.single (0 : Fin (k + 2)) 1, shiftMap k, ?_, ?_, ?_, ?_⟩
    · rw [hε']
      refine ⟨?_, ?_⟩
      · rw [fiveForm_single_self (k + 1) ε 0 (zero_ne_last k)]
        decide
      · rw [fiveForm_single_self (k + 1) ε 0 (zero_ne_last k)]
        decide
    · exact shiftMap_injective k
    · intro x y
      rw [hε']
      exact shiftMap_isom k ε x y
    · intro x
      rw [hε', fiveForm_single (k + 1) ε (shiftMap k x) 0, if_neg (zero_ne_last k),
        shiftMap_apply_zero]
      ring
  | false =>
    have hε' : (false == false) = true := rfl
    cases ε with
    | false =>
      refine ⟨Pi.single (0 : Fin (k + 2)) 1 +
          (2 : ZMod 5) • Pi.single (Fin.last (k + 1)) 1, case2Map k, ?_, ?_, ?_, ?_⟩
      · rw [hε']
        refine ⟨?_, ?_⟩
        · have hnorm : fiveForm (k + 1) true
              (Pi.single (0 : Fin (k + 2)) 1 +
                (2 : ZMod 5) • Pi.single (Fin.last (k + 1)) 1)
              (Pi.single (0 : Fin (k + 2)) 1 +
                (2 : ZMod 5) • Pi.single (Fin.last (k + 1)) 1) = 2 := by
            rw [fiveForm_add_left, fiveForm_smul_left, fiveForm_add_right, fiveForm_smul_right,
              fiveForm_add_right, fiveForm_smul_right,
              fiveForm_single_self (k + 1) true 0 (zero_ne_last k),
              fiveForm_single_zero (k + 1) true (zero_ne_last k).symm,
              fiveForm_single_zero (k + 1) true (zero_ne_last k),
              fiveForm_single_last (k + 1) true]
            decide
          rw [hnorm]
          decide
        · have hnorm : fiveForm (k + 1) true
              (Pi.single (0 : Fin (k + 2)) 1 +
                (2 : ZMod 5) • Pi.single (Fin.last (k + 1)) 1)
              (Pi.single (0 : Fin (k + 2)) 1 +
                (2 : ZMod 5) • Pi.single (Fin.last (k + 1)) 1) = 2 := by
            rw [fiveForm_add_left, fiveForm_smul_left, fiveForm_add_right, fiveForm_smul_right,
              fiveForm_add_right, fiveForm_smul_right,
              fiveForm_single_self (k + 1) true 0 (zero_ne_last k),
              fiveForm_single_zero (k + 1) true (zero_ne_last k).symm,
              fiveForm_single_zero (k + 1) true (zero_ne_last k),
              fiveForm_single_last (k + 1) true]
            decide
          rw [hnorm]
          decide
      · exact case2Map_injective k
      · intro x y
        rw [hε']
        exact case2Map_isom k x y
      · intro x
        rw [hε', fiveForm_add_right, fiveForm_smul_right,
          fiveForm_single (k + 1) true (case2Map k x) 0,
          if_neg (zero_ne_last k),
          fiveForm_single (k + 1) true (case2Map k x) (Fin.last (k + 1)), if_pos rfl,
          case2Map_apply_zero, case2Map_apply_last]
        simp only [↓reduceIte]
        ring
    | true =>
      have hε'' : (true == false) = false := rfl
      refine ⟨Pi.single (Fin.last (k + 1)) 1, case3Map k, ?_, ?_, ?_, ?_⟩
      · rw [hε'']
        refine ⟨?_, ?_⟩
        · rw [fiveForm_single_last (k + 1) false]
          decide
        · rw [fiveForm_single_last (k + 1) false]
          decide
      · exact case3Map_injective k
      · intro x y
        rw [hε'']
        exact case3Map_isom k x y
      · intro x
        rw [hε'', fiveForm_single (k + 1) false (case3Map k x) (Fin.last (k + 1)),
          if_pos rfl, case3Map_apply_last]
        ring

end CFSG.OddTranspositions.PartThree

end
