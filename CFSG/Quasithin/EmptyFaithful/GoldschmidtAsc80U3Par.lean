module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Inv
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Hat

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin CFSG.Quasithin.A312U3 CFSG.Assembly.LowTwoRank

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

theorem odd_index_of_leviU_le (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) {Y : Subgroup (SU3F p F)}
    (hB : leviU hF ≤ Y) : Odd Y.index :=
  Odd.of_dvd_nat (odd_index_leviU hp2 hF) (Subgroup.index_dvd_of_le hB)

theorem le_leviU_of_ne_top (hirr : SU3OddIrr) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    (h3 : p = 3 → ∀ {Y : Subgroup (SU3F p F)}, leviU hF ≤ Y → Odd Y.index →
      IsIrrIn (StatedSU 3 (p ^ 1) F) Y → ¬ Group.IsSolvable ↥Y)
    {Y : Subgroup (SU3F p F)} (hB : leviU hF ≤ Y) (hY : Y ≠ ⊤) : Y ≤ leviU hF := by
  by_cases hirr' : IsIrrIn (StatedSU 3 (p ^ 1) F) Y
  · exfalso
    have hodd := odd_index_of_leviU_le hp2 hF hB
    rcases hirr p hp2 F hF Y hodd hirr' with htop | hsolv | ⟨hp5, hHat, -⟩
    · exact hY htop
    · by_cases hp3 : p = 3
      · exact h3 hp3 hB hodd hirr' hsolv
      · exact not_isSolvable_of_leviU_le hp2 hp3 hF hB hsolv
    · exact false_of_hat_a6 hp5 hF hB hHat
  · exact le_leviU_of_not_irr hp2 hF hB hirr'

omit [Finite F] in
theorem comap_leviCU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) :
    (leviCU hF).comap (piU p F) = leviU hF :=
  Subgroup.comap_map_eq_self (ker_piU_le_leviU hp2 hF)

omit [Finite F] in
theorem leviCU_ne_top (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) : leviCU hF ≠ ⊤ := fun h => by
  have := congrArg (Subgroup.comap (piU p F)) h
  rw [comap_leviCU hp2 hF, Subgroup.comap_top] at this
  exact flipU_not_mem_leviU hp2 hF (this ▸ Subgroup.mem_top _)

theorem le_leviCU_of_ne_top (hirr : SU3OddIrr) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    (h3 : p = 3 → ∀ {Y : Subgroup (SU3F p F)}, leviU hF ≤ Y → Odd Y.index →
      IsIrrIn (StatedSU 3 (p ^ 1) F) Y → ¬ Group.IsSolvable ↥Y)
    {Y : Subgroup (PSU3F p F)} (hB : leviCU hF ≤ Y) (hY : Y ≠ ⊤) : Y ≤ leviCU hF := by
  have hmc : (Y.comap (piU p F)).map (piU p F) = Y :=
    Subgroup.map_comap_eq_self_of_surjective piU_surjective Y
  have hBt : leviU hF ≤ Y.comap (piU p F) := fun x hx => hB ⟨x, hx, rfl⟩
  have hYt : Y.comap (piU p F) ≠ ⊤ := fun h => hY (by
    rw [← hmc, h]
    exact Subgroup.map_top_of_surjective _ piU_surjective)
  rw [← hmc]
  exact Subgroup.map_mono (le_leviU_of_ne_top hirr hp2 hF h3 hBt hYt)

end CFSG.Quasithin.E2P.Asc80
