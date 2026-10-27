module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.RankThree.PartOne.K1214

variable {p e r : ℕ}

theorem card_torsion_zmod [Fact p.Prime] (he : 1 ≤ e) :
    Nat.card {x : Multiplicative (ZMod (p ^ e)) // x ^ p = 1} = p := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have h := IsCyclic.card_powMonoidHom_ker (G := Multiplicative (ZMod (p ^ e))) p
  have hc : Nat.card (Multiplicative (ZMod (p ^ e))) = p ^ e := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
    exact ZMod.card _
  rw [hc, Nat.gcd_eq_right (dvd_pow_self p (by omega : e ≠ 0))] at h
  have h2 : Nat.card {x : Multiplicative (ZMod (p ^ e)) // x ^ p = 1} =
      Nat.card (powMonoidHom p : Multiplicative (ZMod (p ^ e)) →* _).ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
      rw [MonoidHom.mem_ker, powMonoidHom_apply]))
  rw [h2, h]

theorem card_torsion_pi [Fact p.Prime] (he : 1 ≤ e) :
    Nat.card {v : Fin r → Multiplicative (ZMod (p ^ e)) // v ^ p = 1} = p ^ r := by
  have h1 : {v : Fin r → Multiplicative (ZMod (p ^ e)) // v ^ p = 1} ≃
      {v : Fin r → Multiplicative (ZMod (p ^ e)) // ∀ i, v i ^ p = 1} :=
    Equiv.subtypeEquivRight (fun v => by
      constructor
      · intro h i
        exact congrFun h i
      · intro h
        funext i
        exact h i)
  rw [Nat.card_congr (h1.trans (Equiv.subtypePiEquivPi (p := fun _ x => x ^ p = 1)))]
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    card_torsion_zmod he]

theorem pow_card_eq_one (v : Fin r → Multiplicative (ZMod (p ^ e))) : v ^ (p ^ e) = 1 := by
  funext i
  show (v i) ^ (p ^ e) = 1
  have : Multiplicative.toAdd (v i ^ (p ^ e)) = 0 := by
    rw [toAdd_pow]
    simp
  exact Multiplicative.toAdd.injective (by simp)

theorem exists_pow_ne_one [Fact p.Prime] (he : 1 ≤ e) (hr : 1 ≤ r) :
    ∃ v : Fin r → Multiplicative (ZMod (p ^ e)), v ^ (p ^ (e - 1)) ≠ 1 := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  refine ⟨Pi.mulSingle ⟨0, hr⟩ (Multiplicative.ofAdd 1), fun h => ?_⟩
  have h1 := congrFun h ⟨0, hr⟩
  simp only [Pi.pow_apply, Pi.mulSingle_eq_same, Pi.one_apply] at h1
  have h2 : Multiplicative.toAdd ((Multiplicative.ofAdd (1 : ZMod (p ^ e))) ^ (p ^ (e - 1))) = 0 := by
    rw [h1]
    rfl
  rw [toAdd_pow] at h2
  simp only [toAdd_ofAdd, nsmul_eq_mul, mul_one] at h2
  have h3 : ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)) = 0 := by simp [h2]
  have h4 := (ZMod.natCast_eq_zero_iff _ _).1 h3
  have h5 : p ^ e ≤ p ^ (e - 1) := Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos _) h4
  have := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 h5
  omega

theorem exponent_pi_eq [Fact p.Prime] (he : 1 ≤ e) (hr : 1 ≤ r) :
    Monoid.exponent (Fin r → Multiplicative (ZMod (p ^ e))) = p ^ e := by
  have h1 : Monoid.exponent (Fin r → Multiplicative (ZMod (p ^ e))) ∣ p ^ e :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun v => pow_card_eq_one v
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 h1
  by_cases hie : i = e
  · rw [hi', hie]
  · exfalso
    obtain ⟨v, hv⟩ := exists_pow_ne_one (p := p) he hr
    apply hv
    have h2 : Monoid.exponent (Fin r → Multiplicative (ZMod (p ^ e))) ∣ p ^ (e - 1) := by
      rw [hi']
      exact pow_dvd_pow p (by omega)
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1 h2 v

end CFSG.RankThree.PartOne.K1214
