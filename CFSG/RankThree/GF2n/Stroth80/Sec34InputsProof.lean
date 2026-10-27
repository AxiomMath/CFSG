module

public import CFSG.RankThree.GF2n.Stroth80.SL2KDescent
public import CFSG.RankThree.GF2n.Stroth80.Sec34Inputs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.QuasithinUnique.Setup.SL2Modules SL2Descent
open scoped MatrixGroups

theorem two_le_card_of_shift {k : ℕ} (hk : 0 < k) {J : Finset ℕ} (hne : J.Nonempty)
    (hJ : ∀ i ∈ J, i < 2 * k) (hshift : J.image (fun i => (i + k * 1) % (2 * k)) = J) :
    2 ≤ J.card := by
  obtain ⟨i, hi⟩ := hne
  have hj : (i + k * 1) % (2 * k) ∈ J := by
    rw [← hshift]
    exact Finset.mem_image_of_mem _ hi
  have hiJ := hJ i hi
  have hne : (i + k * 1) % (2 * k) ≠ i := by
    by_cases h : i + k * 1 < 2 * k
    · rw [Nat.mod_eq_of_lt h]
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  exact Finset.one_lt_card.mpr ⟨i, hi, _, hj, hne.symm⟩

theorem sl2ModuleDimStatement_holds : SL2ModuleDimStatement := by
  intro k hk V _ _ _ _ ρ hirr hnt
  have hk0 : k ≠ 0 := by omega
  have hk2 : 2 * k ≠ 0 := by omega
  letI : Fintype (GaloisField 2 k) := Fintype.ofFinite _
  letI : Fintype (GaloisField 2 (2 * k)) := Fintype.ofFinite _
  haveI : Finite V := Module.finite_of_finite (GaloisField 2 k)
  have hK : Fintype.card (GaloisField 2 k) = 2 ^ k := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 k hk0]
  have hF : Fintype.card (GaloisField 2 (2 * k)) = 2 ^ (2 * k) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (2 * k) hk2]
  obtain ⟨κ'⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2)
    (K := GaloisField 2 k) (L := GaloisField 2 (2 * k))
    (by rw [GaloisField.finrank 2 hk0, GaloisField.finrank 2 hk2]; exact dvd_mul_left k 2)
  let ρ' : Representation (GaloisField 2 k) SL(2, GaloisField 2 (2 * k)) V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ
  have hirr' : ρ'.IsIrreducible := by
    refine (isIrreducible_iff ρ').mpr ⟨inferInstance, fun W hW => hirr W fun g v hv => hW g v hv⟩
  haveI : Fact ρ'.IsIrreducible := ⟨hirr'⟩
  have hnt' : ∃ g, ρ' g ≠ 1 := by
    obtain ⟨g, hg⟩ := hnt
    refine ⟨g, fun h => hg ?_⟩
    apply LinearEquiv.toLinearMap_injective
    exact h
  obtain ⟨f, J, hf1, -, hfn, hJne, hJn, hshift, hdim⟩ :=
    kDescent (ρ := ρ') hK (by omega) hF κ'.toRingHom hnt'
  have hf2 : f ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hk0) (by
    rw [mul_comm 2 k] at hfn; exact hfn)
  have hcard : 1 ≤ J.card := Finset.card_pos.mpr hJne
  rcases (Nat.dvd_prime Nat.prime_two).mp hf2 with h1 | h2
  · subst h1
    have h2 := two_le_card_of_shift (Nat.pos_of_ne_zero hk0) hJne hJn (by
      simpa using hshift)
    exact ⟨J.card, h2, by rw [hdim, one_mul]⟩
  · subst h2
    exact ⟨J.card + 1, by omega, by rw [hdim, pow_succ, mul_comm]⟩

end CFSG.RankThree.GF2n.Stroth80
