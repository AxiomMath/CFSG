module

public import CFSG.Quasithin.Vol2.GoldschmidtF431q2G2Amal

public section

namespace CFSG.Quasithin.H13.F431.G2Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

section


theorem f431_clause_G2 :
    ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ (H₁ H₂ : Subgroup G) (z : G),
      IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂) (IsG2Over 1) →
      IsL2Quot 1 (oTwoQuot ↥H₁) → IsSpecialPow 2 2 2 ↥(pCoreOf 2 H₁) → z ∈ H₁ → z ≠ 1 →
      z ^ 2 = 1 → H₁ ≤ Subgroup.centralizer ({z} : Set G) →
      Subgroup.centralizer ({z} : Set G) ≤ H₁ →
      Nonempty (G ≃* MulAut (PSU3 3 1)) := by
  intro G _ _ hG H₁ H₂ z hA _ hsp _ hz1 hz2 hle1 hle2
  exfalso
  obtain ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨I⟩⟩ := hA
  rcases hY with ⟨-, ⟨e₀⟩⟩ | ⟨h, -⟩
  · have hk : Nat.card (ZMod 2) = 2 := by simp [Nat.card_eq_fintype_card]
    obtain ⟨f⟩ := g2Group_mulEquiv_aut (ZMod 2) hk
    exact Model.false_of_amalgam (k := ZMod 2) (by decide) (by decide) (e₀.trans f.symm) hpair I
      hsp hz1 (by rw [← sq]; exact hz2) hle1 hle2
  · exact absurd h (by norm_num)

end

end CFSG.Quasithin.H13.F431.G2Two
