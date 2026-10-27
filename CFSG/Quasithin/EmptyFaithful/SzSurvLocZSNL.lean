module

public import CFSG.Quasithin.EmptyFaithful.SzSurvLocZSNFam
public import CFSG.Quasithin.EmptyFaithful.S1421QNSSurv
public import CFSG.Quasithin.Background.Harris.R1.Fam

public section

namespace CFSG.Quasithin.SzSurvLoc

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

theorem hZS_of_nonab_L {G : Type} [Group G] [Finite G]
    {K1 L2 S Zs : Subgroup G} (h : R1SettingLegacyBare K1 L2 S Zs)
    (hL : IsL2Quot 2 (OTwoQuot K1) ∨ IsL2Quot 3 (OTwoQuot K1))
    (hKZ : K1 ≤ Subgroup.centralizer (omegaOneCenterOf S : Set G))
    (hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥) :
    ∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs := by
  classical
  obtain ⟨n, hn2, hLn⟩ : ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (OTwoQuot K1) := by
    rcases hL with h2 | h3
    · exact ⟨2, le_rfl, h2⟩
    · exact ⟨3, by norm_num, h3⟩
  obtain ⟨Ω, _, C, hodd, hcard, -⟩ :=
    Background.Harris.R1.famStmt_holds G K1 L2 S Zs h n hn2 (Or.inl hLn) hna
  have hc : Fintype.card Ω = 2 ^ n + 1 := hcard hLn
  have h4n : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hsimple : IsSimpleGroup (OTwoQuot K1) := S1421NS.isSimpleGroup_of_isL2Quot hn2 hLn
  exact hZS_of_famCtx C (by omega) (act_ker_le_pCore C hodd (by omega) hsimple) hKZ

end CFSG.Quasithin.SzSurvLoc
