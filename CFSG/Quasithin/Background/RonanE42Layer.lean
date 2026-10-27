module

import CFSG.Quasithin.Background.B1MoreTenA
import CFSG.Quasithin.Background.B1MoreElevenD
import CFSG.Quasithin.Background.B6Sections
import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.RonanE42

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem exists_normal_two_subgroup_of_central (L : Subgroup G) (hLn : L.Normal) :
    ∃ P : Subgroup G, P.Normal ∧ IsPGroup 2 P ∧
      ∀ z : G, z ∈ L → (∀ l ∈ L, z * l = l * z) → (∃ n : ℕ, z ^ 2 ^ n = 1) → z ∈ P := by
  refine ⟨{ carrier := {z : G | z ∈ L ∧ (∀ l ∈ L, z * l = l * z) ∧ ∃ n : ℕ, z ^ 2 ^ n = 1}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, ?_, ?_, ?_⟩
  · rintro a b ⟨ha, hac, n, hn⟩ ⟨hb, hbc, m, hm⟩
    refine ⟨L.mul_mem ha hb, fun l hl => ?_, n + m, ?_⟩
    · exact ((show Commute a l from hac l hl).mul_left (show Commute b l from hbc l hl)).eq
    · have hab : Commute a b := hac b hb
      rw [hab.mul_pow, pow_add, pow_mul, pow_mul', hn, hm, one_pow, one_pow, mul_one]
  · exact ⟨L.one_mem, fun l _ => by rw [one_mul, mul_one], 0, by rw [one_pow]⟩
  · rintro a ⟨ha, hac, n, hn⟩
    refine ⟨L.inv_mem ha, fun l hl => ?_, n, ?_⟩
    · exact (show Commute a l from hac l hl).inv_left
    · rw [inv_pow, hn, inv_one]
  · refine ⟨fun z hz g => ?_⟩
    obtain ⟨hzL, hzc, n, hn⟩ := hz
    refine ⟨hLn.conj_mem z hzL g, fun l hl => ?_, n, ?_⟩
    · have hl' : g⁻¹ * l * g ∈ L := by
        have h := hLn.conj_mem l hl g⁻¹
        rwa [inv_inv] at h
      calc g * z * g⁻¹ * l = g * (z * (g⁻¹ * l * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * l * g) * z) * g⁻¹ := by rw [hzc _ hl']
        _ = l * (g * z * g⁻¹) := by group
    · rw [conj_pow, hn]
      simp
  · intro g
    obtain ⟨z, hz⟩ := g
    have hex : ∃ n : ℕ, z ^ 2 ^ n = 1 := by
      obtain ⟨-, -, n, hn⟩ := hz
      exact ⟨n, hn⟩
    obtain ⟨n, hn⟩ := hex
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  · intro z hzL hzc hzn
    obtain ⟨n, hn⟩ := hzn
    exact ⟨hzL, hzc, n, hn⟩

theorem commutator_eq_of_quasisimple_fitting {L W : Subgroup G}
    (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) (hW2 : IsPGroup 2 W) (hW : W ≠ ⊥) : ⁅L, W⁆ = L := by
  have hLn : L.Normal := by
    rw [hLF]
    exact (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  have hWL : ∀ b ∈ W, ∀ k ∈ L, b * k * b⁻¹ ∈ L := fun b _ k hk => hLn.conj_mem k hk b
  rcases CFSG.Quasithin.B1Red.commutator_eq_or_commute (K := L) (B := W)
      (Or.inl (CFSG.Quasithin.B1Red.isQuasisimple_to_open hLq)) hWL with h | hcomm
  · exact h
  exfalso
  have hWn : ∀ b ∈ W, ∃ n : ℕ, b ^ 2 ^ n = 1 := by
    intro b hb
    obtain ⟨n, hn⟩ := hW2 ⟨b, hb⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hWL' : ∀ b ∈ W, b ∈ L := by
    intro b hb
    have hc : b ∈ Subgroup.centralizer (CFSG.generalizedFitting G : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [← hLF] at hh
      exact (hcomm b hb h hh).symm
    rw [hLF]
    exact CFSG.centralizer_generalizedFitting_le G hc
  obtain ⟨P, hPn, hPp, hPmem⟩ := exists_normal_two_subgroup_of_central L hLn
  have hWP : ∀ b ∈ W, b ∈ P := fun b hb => hPmem b (hWL' b hb) (hcomm b hb) (hWn b hb)
  have hPle : P ≤ CFSG.pCore 2 G :=
    le_sSup (s := {K : Subgroup G | K.Normal ∧ IsPGroup 2 K}) ⟨hPn, hPp⟩
  have hcore : CFSG.pCore 2 G = ⊥ := (CFSG.Quasithin.B6.pCoreOf_top 2 G).symm.trans hO2
  rw [hcore] at hPle
  exact hW (eq_bot_iff.mpr fun b hb => hPle (hWP b hb))

end CFSG.Quasithin.RonanE42
