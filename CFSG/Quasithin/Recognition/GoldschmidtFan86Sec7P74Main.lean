module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74H
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P75C2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

namespace P74

theorem card_calpha_le (h40 : Fan40 F) (hΞ : ∃ T : Track Γ G, InXi T) (h62 : Fan62 F)
    (h64 : Fan64 F) (h65 : Fan65 F) (h71a : Fan71a F L) (h71c : Fan71c F L)
    (h72b : Fan72b F L) (h73b : Fan73b F L) {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5) :
    Nat.card ↥(L.calpha P) ≤ 4 := by
  have hle := ballStab_three_le_calpha h40 h64 h71a h71c h72b h73b h5
  have hidx := relIndex_le_two h40 h64 h65 h71a h71c h72b h73b h5
  have hN := ballStab_three_eq h40 hΞ h62 h64 h65 h71a h71c h72b h73b h5
  have hcard := Subgroup.card_mul_index
    ((ballStab Γ G 3 (P.vert 4)).subgroupOf (L.calpha P))
  have hK : Nat.card ↥((ballStab Γ G 3 (P.vert 4)).subgroupOf (L.calpha P)) =
      Nat.card ↥(ballStab Γ G 3 (P.vert 4)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h2 : Nat.card ↥(ballStab Γ G 3 (P.vert 4)) = 2 := by
    rw [hN, Nat.card_zpowers]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by simpa [pow_two] using L.z_mul_self h5) (L.z_ne_one h5)
  have hidx' : ((ballStab Γ G 3 (P.vert 4)).subgroupOf (L.calpha P)).index ≤ 2 := hidx
  rw [hK, h2] at hcard
  omega

end P74

theorem fan_7_4 (h40 : Fan40 F) (hΞ : ∃ T : Track Γ G, InXi T) (h62 : Fan62 F) (h64 : Fan64 F)
    (h65 : Fan65 F) (h71a : Fan71a F L) (h71c : Fan71c F L) (h72b : Fan72b F L)
    (h73b : Fan73b F L) : Fan74 F L := fun _ h5 =>
  ⟨P74.ballStab_three_le_calpha h40 h64 h71a h71c h72b h73b h5,
    P74.relIndex_le_two h40 h64 h65 h71a h71c h72b h73b h5,
    P74.ballStab_five_eq_bot F h40 hΞ h62 h65 h5,
    fun _ hβ => P74.ballStab_four_nbr_eq_bot h40 hΞ h62 h64 h65 h71a h71c h72b h73b h5 hβ⟩

theorem fan_7_5 (h40 : Fan40 F) (hΞ : ∃ T : Track Γ G, InXi T) (h62 : Fan62 F) (h64 : Fan64 F)
    (h65 : Fan65 F) (h71a : Fan71a F L) (h71c : Fan71c F L) (h72b : Fan72b F L)
    (h73b : Fan73b F L) : Fan75 F L := fun _ h5 =>
  ⟨P74.ballStab_three_eq h40 hΞ h62 h64 h65 h71a h71c h72b h73b h5,
    P74.ballStab_four_eq h40 hΞ h62 h64 h65 h71a h71c h72b h73b h5,
    P74.card_calpha_le h40 hΞ h62 h64 h65 h71a h71c h72b h73b h5⟩

end CFSG.Quasithin.Fan86
