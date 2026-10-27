module

public import CFSG.RankThree.PartOne.KS.ONPlane
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneKit
public import CFSG.RankThree.PartOne.S11c.OuterInner

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.Native
open CFSG.ONSchreier (Pv onEquivPv)
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem on_two_part_le :
    ∀ y ∈ Pv, orderOf y = 7 → ∀ R2 : Subgroup (Equiv.Perm (Fin CFSG.ONSchreier.N)),
      IsPGroup 2 R2 → R2 ≤ Pv ⊓ centralizer ({y} : Set (Equiv.Perm (Fin CFSG.ONSchreier.N))) →
        Nat.card R2 ≤ 4 := by
  obtain ⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, hC, hlow, hhigh, htrans, hcov⟩ :=
    R3E_ON_full_seven_centralizer_structures
  refine twoPart_le_of_lines_cent (by norm_num) le_rfl hQsyl hlines (fun j => ?_)
  obtain ⟨r, t, ht, htj⟩ := hcov j
  obtain ⟨hhP, he1, he6, hjlt, hconj⟩ := htrans r t ht
  have hjj : (⟨t.line, hjlt⟩ : Fin 57) = j := Fin.ext htj
  rw [hjj] at hconj
  refine ⟨onSevenRep r, ⟨onSevenTransporterPerm t, hhP, ?_⟩, fun R2 hR2 hle => ?_⟩
  · set h := onSevenTransporterPerm t with hh
    set y := h * onSevenLine (onSevenRep r) * h⁻¹ with hy
    have hord : orderOf y = 7 := by
      have : y = MulAut.conj h (onSevenLine (onSevenRep r)) := rfl
      rw [this, MulEquiv.orderOf_eq, orderOf_onSevenLine]
    have hcop : Nat.Coprime t.power (orderOf y) := by
      rw [hord]
      exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).2 fun hd =>
        absurd (Nat.le_of_dvd (by omega) hd) (by omega)).symm
    rw [← hconj]
    exact centralizer_singleton_pow_eq hcop
  · have hCr := hC r
    have hle' : R2 ≤ onSevenC r := by rwa [hCr, inf_comm]
    by_cases hr : r.val < 3
    · obtain ⟨r', rfl⟩ : ∃ r' : Fin 3, r = Fin.castLE (by norm_num) r' :=
        ⟨⟨r.val, hr⟩, Fin.ext rfl⟩
      obtain ⟨hcard, -⟩ := hlow r'
      have h4 := card_le_of_isPGroup_two_of_le (a := 2) (m := 343) (by rw [hcard]; norm_num)
        (by norm_num) hR2 hle'
      omega
    · have hcard := hhigh r (by omega)
      have h1 := card_le_of_isPGroup_two_of_le (a := 0) (m := 49) (by rw [hcard]; norm_num)
        (by norm_num) hR2 hle'
      omega

theorem not_sq_dvd_card_mulAut_ONan
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) (e : T ≃* CFSG.Blueprint.NativeSporadic.ON) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hp7 : p ≠ 7) : ¬ p ^ 2 ∣ Nat.card (MulAut T) := by
  have hc : center T = ⊥ := center_eq_bot_of_simple hnab
  rw [card_mulAut_eq_mul_card_outer hc]
  have hT : Nat.card T = 460815505920 := (Nat.card_congr e.toEquiv).trans card_ON_eq_card_Pv
  have hout : ¬ p ∣ Nat.card (Outer T) := by
    intro hd
    let e' : Outer T ≃* Outer CFSG.Blueprint.NativeSporadic.ON :=
      CFSG.ComponentClassification.OuterAutomorphisms.equivalence e
    rw [Nat.card_congr e'.toEquiv] at hd
    rcases CFSG.Quasithin.SteinbergCB.ON_large_prime_outer_automorphisms_absent p hp hd with
      h | h <;> omega
  have hcop : Nat.Coprime (p ^ 2) (Nat.card (Outer T)) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hout)
  intro hdvd
  rw [hT] at hdvd
  exact not_sq_dvd_card_ON hp hp3 hp7 (hcop.dvd_of_dvd_mul_right hdvd)

theorem sporadicPlanesCentralize_ONan :
    SporadicPlanesCentralize (Carrier .ONan) := by
  refine sporadicPlanesCentralize_of_data (P := Pv) (R := Pv) le_rfl onEquivPv (S := {7})
    (fun T _ _ hs hnab ⟨eT⟩ p hp hp3 => ?_) (fun p hp T _ _ eT α hα => ?_) (fun p hp => ?_)
  · by_cases hp7 : p = 7
    · exact Or.inl (by simp [hp7])
    · exact Or.inr (not_sq_dvd_card_mulAut_ONan hnab eT hp hp3 hp7)
  · rw [Finset.mem_singleton] at hp
    subst hp
    refine exists_inner_of_pow_eq_one_of_not_dvd_card_outer (by norm_num) ?_ α hα
    intro hd
    let e' : Outer T ≃* Outer CFSG.Blueprint.NativeSporadic.ON :=
      CFSG.ComponentClassification.OuterAutomorphisms.equivalence eT
    rw [Nat.card_congr e'.toEquiv] at hd
    rcases CFSG.Quasithin.SteinbergCB.ON_large_prime_outer_automorphisms_absent 7 (by norm_num) hd
      with h | h <;> omega
  · rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨4, Or.inr ⟨rfl, by norm_num⟩, moveBound_of_plain on_two_part_le⟩

end CFSG.RankThree.PartOne
