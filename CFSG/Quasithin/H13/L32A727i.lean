module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.L32ASetting

public section

namespace CFSG.Quasithin.H13.L32A.R727

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem pRank_star_le (S : Setting147 G T L V H) :
    Open.pRank 3 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := S.hyp.fsu.simple
  have hsqtk : CFSG.SectionRank.IsSQTKCat ↥H :=
    (QuasithinUnique.qtkeCore_of_cat S.hyp.fsu.nonabelian S.hyp.fsu.qtke).1 _ S.hz.1.2
  have h1 := hsqtk.1 3 Nat.prime_three (by norm_num)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h1
  have hN : ¬ 3 ∣ Nat.card ↥(CFSG.pCore 2 ↥H) := by
    have hP2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  rw [CFSG.SectionRank.pRank_quotient_eq _ hN]
  exact h1

theorem pRank_pCore_three_le (S : Setting147 G T L V H) :
    Open.pRank 3 (⊤ : Subgroup ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))) ≤ 2 :=
  (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) _ (Subgroup.subtype_injective _)).trans
    (pRank_star_le S)

end CFSG.Quasithin.H13.L32A.R727
