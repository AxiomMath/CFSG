module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg.Assembly
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg.Coprime
import CFSG.CharacterTheory.Burnside

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

open UnitaryHeisenberg

theorem UnitaryHeisenberg.isSolvable_of_card_dvd_seventy_two {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ∣ 72) : Group.IsSolvable G := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.mp (show Nat.card G ∣ 2 ^ 3 * 3 ^ 2 by
    simpa using h)
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hz
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hyz.symm)

theorem psu3_centralizer_eq_of_card_nine {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (P : Subgroup (PSU3 2 p)) (hPe : IsElemAbelian 3 P) (hPc : Nat.card P = 9) :
    Subgroup.centralizer (P : Set (PSU3 2 p)) = P := by
  obtain ⟨a, b, ζ, h, hker, hCP, hMU, rfl⟩ := exists_pair_of_card_nine hp h5 P hPc
  rw [← h.E_eq_closure]
  exact h.centralizer_map_E _ (projSU3_surjective _) hker hCP

theorem psu3_card_normalizer_dvd {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (P : Subgroup (PSU3 2 p))
    (hPe : IsElemAbelian 3 P) (hPc : Nat.card P = 9) :
    Nat.card (Subgroup.normalizer (P : Set (PSU3 2 p))) ∣ 72 := by
  obtain ⟨a, b, ζ, h, hker, hCP, hMU, hPeq⟩ := exists_pair_of_card_nine hp h5 P hPc
  subst hPeq
  set P := (Subgroup.closure {a, b}).map (projSU3 hp.one_le) with hPdef
  have h216 : Nat.card (Subgroup.normalizer (P : Set (PSU3 2 p))) ∣ 216 := by
    rw [hPdef, ← h.E_eq_closure]
    exact h.card_normalizer_dvd _ (projSU3_surjective _) hker hCP
  obtain ⟨T, hT, hT3⟩ := exists_card_psu3 hp h5
  have h9 : 9 ∣ Nat.card (Subgroup.normalizer (P : Set (PSU3 2 p))) := by
    rw [← hPc]
    exact Subgroup.card_dvd_of_le Subgroup.le_normalizer
  have h27 : ¬ 27 ∣ Nat.card (Subgroup.normalizer (P : Set (PSU3 2 p))) := by
    intro h27
    have := h27.trans (Subgroup.card_subgroup_dvd_card _)
    rw [hT] at this
    omega
  have key : ∀ n ∈ Nat.divisors 216, 9 ∣ n → ¬ 27 ∣ n → n ∣ 72 := by decide
  exact key _ (Nat.mem_divisors.mpr ⟨h216, by norm_num⟩) h9 h27

theorem psu3_not_normalizes_coprime_six {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (P C : Subgroup (PSU3 2 p)) (hPe : IsElemAbelian 3 P) (hPc : Nat.card P = 9) (hPC : P ≤ C)
    (hCP : C ≤ Subgroup.normalizer (P : Set (PSU3 2 p)))
    (htrans : ∀ x ∈ P, x ≠ 1 → ∀ y ∈ P, y ≠ 1 → ∃ c ∈ C, c * x * c⁻¹ = y)
    (N : Subgroup (PSU3 2 p)) (hN : N ≠ ⊥) (hN6 : Nat.Coprime (Nat.card N) 6) :
    ¬ C ≤ Subgroup.normalizer (N : Set (PSU3 2 p)) := by
  intro hCN
  have hC72 : Nat.card C ∣ 72 :=
    (Subgroup.card_dvd_of_le hCP).trans (psu3_card_normalizer_dvd hp h5 P hPe hPc)
  have hN72 : Nat.Coprime (Nat.card N) 72 := by
    have h2 : Nat.Coprime (Nat.card N) 2 := hN6.coprime_dvd_right (by norm_num)
    have h36 : Nat.Coprime (Nat.card N) (6 ^ 2) := hN6.pow_right 2
    simpa using h36.mul_right h2
  have hcop : Nat.Coprime (Nat.card C) (Nat.card N) := (hN72.symm).coprime_dvd_left hC72
  have hN3 : Nat.Coprime 3 (Nat.card N) := (hN6.symm).coprime_dvd_left (by norm_num)
  have hsolv : Group.IsSolvable C := isSolvable_of_card_dvd_seventy_two hC72
  obtain ⟨a, b, ζ, h, hker, -, hMU, hPeq⟩ := exists_pair_of_card_nine hp h5 P hPc
  have hmem : ∀ g : SU3 hp.one_le, g ∈ h.E → projSU3 hp.one_le g ∈ P := fun g hg => by
    rw [hPeq, ← h.E_eq_closure]
    exact Subgroup.mem_map_of_mem _ hg
  have hne : ∀ g : SU3 hp.one_le, g ∉ Subgroup.zpowers ζ → projSU3 hp.one_le g ≠ 1 :=
    fun g hg h1 => hg ((hker g).mp h1)
  obtain ⟨x, y, hxN, hyN, hx1, hy1, hxa, hyb, hxy⟩ := exists_commuting_pair hPe (by omega) hPC
    htrans hN hN3 hCN hsolv hcop (hmem a h.a_mem_E) (hne a h.a_not_mem_zpowers)
    (hmem b h.b_mem_E) (hne b h.b_not_mem_zpowers)
  have h3 : ∀ z ∈ N, ¬ 3 ∣ orderOf z := fun z hz h3 => by
    have := h3.trans (Subgroup.orderOf_dvd_natCard N hz)
    have := Nat.eq_one_of_dvd_coprimes hN3 (dvd_refl 3) this
    omega
  exact h.no_commuting_pair (projSU3 hp.one_le) (projSU3_surjective _) hker hMU hx1 hy1
    (h3 x hxN) (h3 y hyN) hxa hyb hxy

end CFSG.SignalizerFunctorTheorem.McBride
