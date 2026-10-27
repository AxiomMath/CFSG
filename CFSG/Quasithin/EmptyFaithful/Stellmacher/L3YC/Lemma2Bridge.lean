module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace Stellmacher.L3YC

section Bridge

theorem le_nine_of_pRank_le {K : Type*} [Group K] [Finite K] (h : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 2)
    (E : Subgroup K) (hE : IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 ↥E := by
    intro x
    exact ⟨1, by
      apply Subtype.ext
      simpa using hE.2 x x.2⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hk2 : k ≤ 2 := (CFSG.SectionRank.le_pRank (by norm_num) le_top hE hk).trans h
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

theorem le_nine_quotient_of_pRank_le {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN : IsPGroup 2 ↥N) (h : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 2) :
    ∀ E : Subgroup (H ⧸ N), IsElemAbelian 3 E → Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN3 : ¬ 3 ∣ Nat.card ↥N := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (hk ▸ h3)
    omega
  have h' : CFSG.Open.pRank 3 (⊤ : Subgroup (H ⧸ N)) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_quotient_eq N hN3]
    exact h
  exact fun E hE => le_nine_of_pRank_le h' E hE

theorem le_nine_modO2_of_pRank_le {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (h : CFSG.Open.pRank 3 H ≤ 2) :
    ∀ E : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), IsElemAbelian 3 E → Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_nine_quotient_of_pRank_le (CFSG.pCore 2 ↥H) (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ?_
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]

end Bridge

end Stellmacher.L3YC

end CFSG.Quasithin
