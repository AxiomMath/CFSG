module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParGen
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYam

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.Sec53F.Yam

variable {Y : Type} [Group Y] [Finite Y] {U : Subgroup Y} {P : Fin 2 → Subgroup Y}

theorem Rank2Pkg.twoLocal (h : Rank2Pkg Y U P)
    (hno : ∀ R : Subgroup Y, R.Normal → IsPGroup 2 ↥R → R = ⊥) (j : Fin 2) :
    IsTwoLocal (P j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRne : pCoreOf 2 (perfectCore (P j)) ≠ ⊥ := by
    intro hbot
    apply h.perfectCore_ne_bot j
    rw [eq_bot_iff]
    intro x hx
    have hc : x ∈ Subgroup.centralizer (pCoreOf 2 (perfectCore (P j)) : Set Y) := by
      rw [hbot]
      exact Subgroup.mem_centralizer_iff.mpr (by simp)
    have := h.charTwo j ⟨hx, hc⟩
    rwa [hbot] at this
  have hPN : P j ≤ Subgroup.normalizer (pCoreOf 2 (perfectCore (P j)) : Set Y) :=
    Subgroup.le_normalizer.trans ((normalizer_le_normalizer_perfectCore (P j)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
  have hRp : IsPGroup 2 ↥(pCoreOf 2 (perfectCore (P j))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  refine ⟨_, hRne, hRp, ?_⟩
  rcases (covBy_top_iff.mp (h.covBy j)).le_iff.mp hPN with hN | hN
  · exact absurd (hno _ (Subgroup.normalizer_eq_top_iff.mp hN) hRp) hRne
  · exact hN.symm

theorem Rank2Pkg.yamStd (h : Rank2Pkg Y U P) (hU : IsSylowTwoOf U ⊤)
    (hno : ∀ R : Subgroup Y, R.Normal → IsPGroup 2 ↥R → R = ⊥) : YamStd Y U (P 0) (P 1) where
  sylow := hU
  no_normal := hno
  ne := h.res.1
  le₀ := h.norm 0
  le₁ := h.norm 1
  coatom₀ := covBy_top_iff.mp (h.covBy 0)
  coatom₁ := covBy_top_iff.mp (h.covBy 1)
  above := fun A hNA hAt => by
    obtain ⟨A', hA', hAA'⟩ := (IsCoatomic.eq_top_or_exists_le_coatom A).resolve_left hAt
    have hUA : U ≤ A' := Subgroup.le_normalizer.trans (hNA.trans hAA')
    obtain ⟨j, rfl⟩ := (h.res.2.2.1 A' hUA).mp (covBy_top_iff.mpr hA')
    fin_cases j
    · exact Or.inl hAA'
    · exact Or.inr hAA'
  twoLoc₀ := h.twoLocal hno 0
  twoLoc₁ := h.twoLocal hno 1

end CFSG.Quasithin.Rk2
