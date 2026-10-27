module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2m
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Blueprint

@[expose] def BadConc (X : Type) [Group X] : Prop :=
  IsPSL 2 5 2 X ∨ IsPSL 2 7 2 X ∨ (∃ s : Bool, IsPSLEps3 s 5 1 X ∨ IsSLEps3 s 5 X) ∨
    (∃ s : Bool, IsPSLEps3 s 7 1 X ∨ IsSLEps3 s 7 X) ∨ IsSporadic .M22 X ∨
    IsHat X (NativeSporadic.Carrier .M22) ∨ IsSporadic .M23 X ∨ IsSporadic .M24 X ∨
    IsSporadic .J1 X ∨ IsSporadic .J2 X ∨ IsSporadic .J4 X ∨ IsSporadic .HS X ∨
    IsSporadic .He X ∨ IsSporadic .Ru X

variable {X : Type} [Group X] {M : ℕ}

omit [Group X] in
theorem false_of_card (hJ : B56Card M) (hc : Nat.card X = M ∨ Nat.card X = 3 * M) {N : ℕ}
    (hX : Nat.card X = N) (v u v' u' : ℕ) (hN : N = 2 ^ v * u) (hu : Odd u)
    (h1 : ¬ B56Cond N v u) (hN3 : N = 3 * (2 ^ v' * u')) (hu' : Odd u')
    (h3 : ¬ B56Cond (2 ^ v' * u') v' u') : False :=
  false_of_b56_three hJ (by rwa [hX] at hc) hN hu h1 hN3 hu' h3

theorem false_of_badConc (hJ : B56Card M) (hc : Nat.card X = M ∨ Nat.card X = 3 * M)
    (h : BadConc X) : False := by
  have hsp : ∀ {s : TauCeti.SporadicName} {N : ℕ}, Nat.card (NativeSporadic.Carrier s) = N →
      IsSporadic s X → Nat.card X = N := fun hN ⟨e⟩ => (Nat.card_congr e.toEquiv).trans hN
  rcases h with h | h | ⟨s, h | h⟩ | ⟨s, h | h⟩ | h | h | h | h | h | h | h | h | h | h
  · exact false_of_card hJ hc (card_L225 h) 3 975 3 325 (by norm_num) (by decide) (by decide)
      (by norm_num) (by decide) (by decide)
  · exact false_of_card hJ hc (card_L249 h) 4 3675 4 1225 (by norm_num) (by decide)
      (by decide) (by norm_num) (by decide) (by decide)
  · cases s
    · exact false_of_card hJ hc (card_U35 h) 4 7875 4 2625 (by norm_num) (by decide)
        (by decide) (by norm_num) (by decide) (by decide)
    · exact false_of_card hJ hc (card_L35 h) 5 11625 5 3875 (by norm_num) (by decide)
        (by decide) (by norm_num) (by decide) (by decide)
  · cases s
    · exact false_of_card hJ hc (card_SU35 h) 4 23625 4 7875 (by norm_num) (by decide)
        (by decide) (by norm_num) (by decide) (by decide)
    · exact false_of_card hJ hc (card_SL35 h) 5 11625 5 3875 (by norm_num) (by decide)
        (by decide) (by norm_num) (by decide) (by decide)
  · cases s
    · exact false_of_card hJ hc (card_U37 h) 7 44247 7 14749 (by norm_num) (by decide)
        (by decide) (by norm_num) (by decide) (by decide)
    · exact false_of_card hJ hc (card_L37 h) 5 58653 5 19551 (by norm_num) (by decide)
        (by decide) (by norm_num) (by decide) (by decide)
  · cases s
    · exact false_of_card hJ hc (card_SU37 h) 7 44247 7 14749 (by norm_num) (by decide)
        (by decide) (by norm_num) (by decide) (by decide)
    · exact false_of_card hJ hc (card_SL37 h) 5 175959 5 58653 (by norm_num) (by decide)
        (by decide) (by norm_num) (by decide) (by decide)
  · have hN := hsp (s := .M22) (N := 443520) CFSG.Sporadic.Mathieu.card_M22 h
    exact false_of_card hJ hc hN 7 3465 7 1155
      (by norm_num) (by decide) (by decide) (by norm_num) (by decide) (by decide)
  · have hN : Nat.card X = 1330560 := by
      rw [card_of_isHat h]
      exact (congrArg (· * 3) CFSG.Sporadic.Mathieu.card_M22).trans (by norm_num)
    exact false_of_card hJ hc hN 7 10395 7 3465 (by norm_num) (by decide) (by decide)
      (by norm_num) (by decide) (by decide)
  · have hM23 : Nat.card (NativeSporadic.Carrier .M23) = 10200960 := by
      show Nat.card NativeSporadic.M23 = 10200960
      rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
      exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans
        CFSG.M23.M23Group.card_M23
    have hN := hsp (s := .M23) (N := 10200960) hM23 h
    exact false_of_card hJ hc hN 7 79695 7 26565 (by norm_num) (by decide)
      (by decide) (by norm_num) (by decide) (by decide)
  · have hN := hsp (s := .M24) (N := 244823040) CFSG.Sporadic.Mathieu.card_M24 h
    exact false_of_card hJ hc hN 10 239085 10 79695
      (by norm_num) (by decide) (by decide) (by norm_num) (by decide) (by decide)
  · have hN := hsp (s := .J1) (N := 175560) CFSG.Sporadic.J1.card_J1 h
    exact false_of_card hJ hc hN 3 21945 3 7315
      (by norm_num) (by decide) (by decide) (by norm_num) (by decide) (by decide)
  · have hN := hsp (s := .J2) (N := 604800) CFSG.Sporadic.J2.card_J2 h
    exact false_of_card hJ hc hN 7 4725 7 1575
      (by norm_num) (by decide) (by decide) (by norm_num) (by decide) (by decide)
  · have hN := hsp (s := .J4) (N := 86775571046077562880) CFSG.Sporadic.J4.card_J4 h
    exact false_of_card hJ hc hN 21 41377816699065 21
      13792605566355 (by norm_num) (by decide) (by decide) (by norm_num) (by decide) (by decide)
  · have hN := hsp (s := .HS) (N := 44352000) CFSG.Sporadic.HS.card_HS h
    exact false_of_card hJ hc hN 9 86625 9 28875
      (by norm_num) (by decide) (by decide) (by norm_num) (by decide) (by decide)
  · have hN := hsp (s := .He) (N := 4030387200) CFSG.Sporadic.He.card_He h
    exact false_of_card hJ hc hN 10 3935925 10 1311975
      (by norm_num) (by decide) (by decide) (by norm_num) (by decide) (by decide)
  · have hN := hsp (s := .Ru) (N := 145926144000) CFSG.Sporadic.Ru.card_Ru h
    exact false_of_card hJ hc hN 14 8906625 14 2968875
      (by norm_num) (by decide) (by decide) (by norm_num) (by decide) (by decide)

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
