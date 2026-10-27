module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixIndex
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem center_dihedral_three_eq_bot :
    Subgroup.center (DihedralGroup 3) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall (Subgroup.center (DihedralGroup 3))).2
  intro z hz
  rcases dihedralGroup_cases z with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · have hcomm := Subgroup.mem_center_iff.mp hz (DihedralGroup.sr 0)
    have hi : i = -i := by simpa using hcomm
    have h2i : (2 : ZMod 3) * i = 0 := by
      linear_combination hi
    have h2ne : (2 : ZMod 3) ≠ 0 := by decide
    have hi0 : i = 0 := (mul_eq_zero.mp h2i).resolve_left h2ne
    simp [hi0]
  · exfalso
    have hcomm := Subgroup.mem_center_iff.mp hz (DihedralGroup.r 1)
    have hi : i - 1 = i + 1 := by simpa using hcomm
    have h2zero : (2 : ZMod 3) = 0 := by
      calc
        (2 : ZMod 3) = (i + 1) - (i - 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [hi]
        _ = 0 := by abel
    exact (by decide : (2 : ZMod 3) ≠ 0) h2zero

/-- The order-six dihedral group has trivial normal `2`-core. -/
public theorem pCore_two_dihedral_three_eq_bot :
    pCore 2 (DihedralGroup 3) = ⊥ := by
  classical
  let P : Subgroup (DihedralGroup 3) := pCore 2 (DihedralGroup 3)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPnormal : P.Normal := by
    dsimp [P]
    infer_instance
  have hPp : IsPGroup 2 P := by
    dsimp [P]
    exact pCore_isPGroup
  have hPcarddvd : Nat.card P ∣ 6 := by
    have htop : P ≤ (⊤ : Subgroup (DihedralGroup 3)) := le_top
    have h := Subgroup.card_dvd_of_le htop
    have hDcard : Fintype.card (DihedralGroup 3) = 6 := by
      rw [← Nat.card_eq_fintype_card, DihedralGroup.nat_card]
    simpa [Nat.card_eq_fintype_card, hDcard] using h
  obtain ⟨n, hn⟩ := hPp.exists_card_eq
  have hnle : n ≤ 2 := by
    have hPcarddvd' := hPcarddvd
    rw [hn] at hPcarddvd'
    have hpowdvd : 2 ^ n ∣ 6 := by simpa using hPcarddvd'
    have hpowle : 2 ^ n ≤ 6 := Nat.le_of_dvd (by norm_num) hpowdvd
    by_contra h
    have hn3 : 3 ≤ n := by omega
    have hpow8 : 8 ≤ 2 ^ n := by
      have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn3
      norm_num at hpow ⊢
      exact hpow
    omega
  have hcases : Nat.card P = 1 ∨ Nat.card P = 2 := by
    have hn' : Fintype.card P = 2 ^ n := by
      simpa [Nat.card_eq_fintype_card] using hn
    interval_cases n
    · left
      simpa [hn']
    · right
      simpa [hn']
    · exfalso
      have hbad : (4 : ℕ) ∣ 6 := by
        have h := hPcarddvd
        rw [hn] at h
        simpa [Nat.card_eq_fintype_card] using h
      norm_num at hbad
  rcases hcases with h1 | h2
  · exact (Subgroup.eq_bot_iff_card P).2 h1
  · apply (Subgroup.eq_bot_iff_forall P).2
    intro x hx
    by_cases hx1 : x = 1
    · exact hx1
    have hxuniq : ∀ y : P, y ≠ 1 → y = ⟨x, hx⟩ := by
      intro y hy1
      have htwo := (Nat.card_eq_two_iff' (1 : P)).mp h2
      obtain ⟨z, hz1, hzuniq⟩ := htwo
      exact (hzuniq y hy1).trans (hzuniq ⟨x, hx⟩ (by simpa [hx1])).symm
    have hcenter : x ∈ Subgroup.center (DihedralGroup 3) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hconj : g * x * g⁻¹ ∈ P := hPnormal.conj_mem x hx g
      have hne : g * x * g⁻¹ ≠ 1 := by
        intro hh
        apply hx1
        calc
          x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = 1 := by rw [hh]; simp
      have hne' : (⟨g * x * g⁻¹, hconj⟩ : P) ≠ 1 := by
        intro hh
        exact hne (congrArg Subtype.val hh)
      have heq : (⟨g * x * g⁻¹, hconj⟩ : P) = ⟨x, hx⟩ :=
        hxuniq _ hne'
      have hfix : g * x * g⁻¹ = x := congrArg Subtype.val heq
      calc
        g * x = (g * x * g⁻¹) * g := by group
        _ = x * g := by rw [hfix]
    have h := (center_dihedral_three_eq_bot ▸ hcenter)
    exact Subgroup.mem_bot.mp h

end CFSG.GorensteinWalter
