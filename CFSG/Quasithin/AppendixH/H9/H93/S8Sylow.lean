module

public import CFSG.Quasithin.AppendixH.H9.H93.S8Unique
public import CFSG.Quasithin.AppendixH.H9.H93.S8Sylow.SylowConjLe
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.ASVolI.ChH

open Equiv

private theorem isElemAb2_map_hom {G H : Type*} [Group G] [Group H] {E : Subgroup G}
    (hE : IsElemAb2 E) (f : G →* H) : IsElemAb2 (E.map f) := by
  obtain ⟨hcomm, hsq⟩ := hE
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hsq a ha, map_one]

theorem exists_unique_e16_of_card_sixtyfour {P : Subgroup (Perm (Fin 8))}
    (hPA : P ≤ alternatingGroup (Fin 8)) (hc : Nat.card P = 64) :
    ∃ E₀ : Subgroup (Perm (Fin 8)), E₀ ≤ P ∧ IsElemAb2 E₀ ∧ Nat.card E₀ = 16 ∧
      ∀ E : Subgroup (Perm (Fin 8)), E ≤ P → IsElemAb2 E →
        Nat.card E ≤ 16 ∧ (Nat.card E = 16 → E = E₀) := by
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 6) (by rw [hc]; norm_num)
  obtain ⟨Es, hEs, hEsc, hEso⟩ := exists_e16_with_orbitSizes (s := {4, 4}) (Or.inl rfl)
  have hEsA : Es ≤ alternatingGroup (Fin 8) := (e16_le_alternatingGroup_iff hEs hEsc).2 hEso
  have hEs2 : IsPGroup 2 Es := IsPGroup.of_card (n := 4) (by rw [hEsc]; norm_num)
  have hfac : (Nat.card (alternatingGroup (Fin 8))).factorization 2 = 6 := by
    have hK : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
      rw [nat_card_alternatingGroup]
      simp [Nat.factorial]
    have h : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
    rw [hK, h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  obtain ⟨g, -, hg⟩ := exists_mem_map_conj_le_of_card_eq (p := 2) hPA hEsA
    (by rw [hc, hfac]; norm_num) hEs2
  have hE₀ : IsElemAb2 (Es.map (MulAut.conj g).toMonoidHom) := isElemAb2_map_hom hEs _
  have hE₀c : Nat.card (Es.map (MulAut.conj g).toMonoidHom) = 16 :=
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).trans hEsc
  have hE₀A : Es.map (MulAut.conj g).toMonoidHom ≤ alternatingGroup (Fin 8) := hg.trans hPA
  refine ⟨_, hg, hE₀, hE₀c, fun E hEP hE => ⟨card_le_sixteen_of_isElemAb2 hE, fun hEc => ?_⟩⟩
  exact e16_eq_of_le_twoGroup hE hEc hE₀ hE₀c (hEP.trans hPA) hE₀A hP2 hEP hg

end CFSG.ASVolI.ChH
