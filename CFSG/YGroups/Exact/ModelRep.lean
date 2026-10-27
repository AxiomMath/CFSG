module

public import CFSG.YGroups.Exact.Model

public section

namespace CFSG.YGroups

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.YGroups.ModelNative
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

theorem rep_letterOf_of_rep {n : ℕ} {O : Array (Array ℕ)}
    (hO : ∀ c < O.size, Rep n O[c]! (arrGen n O c)) (c : ℕ) :
    Rep n (letterOf n O c) (arrGen n O c) := by
  unfold letterOf
  by_cases hc : c < O.size
  · rw [ite_eq_left hc]
    exact hO c hc
  · rw [ite_eq_right hc, arrGen_of_le (Nat.not_lt.mp hc)]
    exact rep_idA

theorem rep_evalW_of_rep {n : ℕ} {O : Array (Array ℕ)}
    (hO : ∀ c < O.size, Rep n O[c]! (arrGen n O c)) :
    ∀ w : List ℕ, Rep n (evalW n O w) (evalWord (arrGen n O) w)
  | [] => by
    rw [evalW, evalWord_nil]
    exact rep_idA
  | c :: w => by
    rw [evalW, evalWord_cons]
    exact rep_compA (rep_letterOf_of_rep hO c) (rep_evalW_of_rep hO w)

theorem yModelHom_injective_and_card_of_le {p q r n : ℕ} {O : Array (Array ℕ)} {B : ℕ}
    (hcard : Finite (YGroup p q r) ∧ Nat.card (YGroup p q r) ≤ B)
    (hsize : O.size = ngen p q r) (hrel : ∀ w ∈ yRels p q r, evalWord (arrGen n O) w = 1)
    (hlow : B ≤ Nat.card (arrClosure n O)) :
    Function.Injective (yModelHom (arrGen n O) hrel) ∧ Nat.card (YGroup p q r) = B := by
  have := hcard.1
  refine injective_and_card_of_model _ hcard.2 ?_
  rw [range_yModelHom, ← hsize, arrGen_image_eq]
  exact hlow

theorem evalWord_yGen_eq_iff_of_rep {p q r n : ℕ} {O : Array (Array ℕ)}
    (hsize : O.size = ngen p q r) (hO : ∀ c < O.size, Rep n O[c]! (arrGen n O c))
    (hrel : ∀ w ∈ yRels p q r, evalWord (arrGen n O) w = 1)
    (hinj : Function.Injective (yModelHom (arrGen n O) hrel)) (u v : List ℕ) :
    evalWord (yGen p q r) u = evalWord (yGen p q r) v ↔
      eqA n (evalW n O u) (evalW n O v) = true := by
  have hgen : ∀ c, yModelHom (arrGen n O) hrel (yGen p q r c) = arrGen n O c := by
    intro c
    by_cases hc : c < ngen p q r
    · exact yModelHom_yGen hc
    · rw [yGen_of_le (Nat.not_lt.mp hc), map_one, arrGen_of_le (by omega)]
  have hmap : ∀ w : List ℕ, yModelHom (arrGen n O) hrel (evalWord (yGen p q r) w) =
      evalWord (arrGen n O) w := by
    intro w
    induction w with
    | nil => simp
    | cons c w ih => rw [evalWord_cons, map_mul, ih, hgen, evalWord_cons]
  rw [eqA_iff (rep_evalW_of_rep hO u) (rep_evalW_of_rep hO v), ← hmap u, ← hmap v]
  exact hinj.eq_iff.symm

theorem evalWord_yGen_eq_one_iff_of_rep {p q r n : ℕ} {O : Array (Array ℕ)}
    (hsize : O.size = ngen p q r) (hO : ∀ c < O.size, Rep n O[c]! (arrGen n O c))
    (hrel : ∀ w ∈ yRels p q r, evalWord (arrGen n O) w = 1)
    (hinj : Function.Injective (yModelHom (arrGen n O) hrel)) (w : List ℕ) :
    evalWord (yGen p q r) w = 1 ↔ eqA n (evalW n O w) (idA n) = true := by
  have := evalWord_yGen_eq_iff_of_rep hsize hO hrel hinj w []
  simpa [evalWord_nil, evalW] using this

end CFSG.YGroups
