module

public import CFSG.Quasithin.H13.NQCatT513Lat
public import CFSG.Quasithin.Background.A312SporJ1
public import CFSG.Sporadic.Schreier.J1Faithful
public import CFSG.Sporadic.Schreier.J1Order
public import CFSG.Sporadic.Schreier.ImagePairs
public import CFSG.Sporadic.Schreier.J1Tables
public import CFSG.Sporadic.Schreier.J1CountCheckInputs
public import Certificates.Certificate7193
import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.H13.NQCat.T513P

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.A312S
  CFSG.Quasithin.E2P.SporB CFSG.Sporadic.Schreier

theorem j1P_no_order_21
    (x : ↥j1P) :
    orderOf x ≠ 21 := by
  obtain ⟨Q, hrec, hQ, -, -, -, hP, -, -⟩ := fam_j1_order
  have hord : orderTables Q 21 = j1OrderTables 21 := by
    rw [orderTables, j1_levelTables hrec]
    rfl
  have h := card_orderOf_eq (by norm_num) Q hQ (m := 21) (by norm_num)
  rw [hord, Certificates.certificate7193, hP] at h
  intro hx
  have hpos : 0 < Nat.card {y : ↥j1P // orderOf y = 21} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨x, hx⟩⟩, inferInstance⟩
  omega

theorem j1J_no_order_21
    (g : ↥CFSG.Sporadic.J1.J) :
    orderOf g ≠ 21 := by
  rw [← MulEquiv.orderOf_eq CFSG.Sporadic.J1.nativeEquiv.symm g,
    ← MulEquiv.orderOf_eq j1PermEquiv]
  exact j1P_no_order_21 _

theorem cycOddPerm_j1Grp :
    CycOddPerm ↥CFSG.Sporadic.J1.J fun n => n = 7 := by
  refine cycOddPerm_of_sylow j1_sylow fun Dc hcyc hodd hperm => ?_
  have hS : Nat.card ↥j1S = 2 ^ 3 :=
    card_of_isSylowTwoOf_top j1_sylow (m := 21945)
      (by rw [CFSG.Sporadic.J1.card_J]; norm_num) (by decide)
  have hall := j1_all
  have hcard : ∀ j < (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] :
      Array ℕ).size, Nat.card ↥(j1Y j) =
        (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ)[j]! *
          Nat.card ↥j1S := fun j hj => by
    rw [hS]
    exact j1_Y_card hj
  have hpos : 0 < Nat.card ↥j1S := Nat.card_pos
  have hΓ : Nat.card ↥CFSG.Sporadic.J1.J = 21945 * Nat.card ↥j1S := by
    rw [CFSG.Sporadic.J1.card_J, hS]
    norm_num
  have hidx : ∀ Z : Subgroup ↥CFSG.Sporadic.J1.J, j1S ≤ Z → ∀ m : ℕ,
      Nat.card ↥Z = m * Nat.card ↥j1S → m = 1 ∨ 3 ∣ m ∨ m = 7 := by
    intro Z hZ m hm
    have hL : ∀ j < (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ).size,
        (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ)[j]! = 1 ∨
          3 ∣ (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ)[j]! ∨
            (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ)[j]! = 7 := by
      decide
    rcases index_of_list hall hcard hZ hm with ⟨j, hj, rfl⟩ | h
    · exact hL j hj
    · rw [hΓ] at h
      rw [← Nat.eq_of_mul_eq_mul_right hpos h]
      exact Or.inr (Or.inl (by norm_num))
  have h7 : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥Dc → p = 3 ∨ p = 7 := by
    intro p hp hpD
    by_cases hp3 : p = 3
    · exact Or.inl hp3
    obtain ⟨a, ha⟩ := pPart_of_overgroups (E := fun m => m = 7) j1_sylow hidx hcyc hodd hperm
      hp hp3 hpD
    have hpa : p ∣ 7 := ha ▸ dvd_pow_self p a.succ_ne_zero
    exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hpa)
  have hcop : Nat.Coprime (Nat.card ↥Dc) (Nat.card ↥j1S) := by
    rw [hS]
    exact Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd)
  have hY := card_sup_of_perm hperm hcop
  obtain ⟨g, -, hg⟩ := exists_orderOf_eq_card hcyc
  have h21 : Nat.card ↥Dc ≠ 21 := fun h => j1J_no_order_21 (g : ↥CFSG.Sporadic.J1.J) (hg.trans h)
  have h5 : ¬ 5 ∣ Nat.card ↥Dc := fun h => by
    rcases h7 5 (by norm_num) h with h | h <;> norm_num at h
  rcases index_of_list hall hcard le_sup_right hY with ⟨j, hj, hDj⟩ | h
  · have hcases : ∀ j < (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] :
        Array ℕ).size, (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] :
          Array ℕ)[j]! ∈ ({1, 3, 7, 15, 21} : Finset ℕ) := by decide
    have hm := hcases j hj
    rw [← hDj] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm | hm | hm
    · exact Or.inl ⟨0, by rw [hm, pow_zero]⟩
    · exact Or.inl ⟨1, by rw [hm, pow_one]⟩
    · exact Or.inr hm
    · exact absurd (by rw [hm]; norm_num) h5
    · exact absurd hm h21
  · rw [hΓ] at h
    have hD : Nat.card ↥Dc = 21945 := (Nat.eq_of_mul_eq_mul_right hpos h).symm
    exact absurd (by rw [hD]; norm_num) h5

theorem cycOddPerm_j1 :
    CycOddPerm (CFSG.Blueprint.NativeSporadic.Carrier .J1) fun n => n = 7 := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .J1 ≃* ↥CFSG.Sporadic.J1.J :=
    CFSG.Sporadic.J1.nativeEquiv
  exact @CycOddPerm.of_equiv ↥CFSG.Sporadic.J1.J (CFSG.Blueprint.NativeSporadic.Carrier .J1) _ _
    _ _ e.symm cycOddPerm_j1Grp

end CFSG.Quasithin.H13.NQCat.T513P
