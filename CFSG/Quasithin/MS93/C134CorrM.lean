module

public import CFSG.Quasithin.MS93.Burnside.Mag568Main
public import CFSG.Quasithin.MS93.C134L32CorrMHolds

public section

namespace CFSG.Quasithin.MS93

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped Pointwise

@[expose] def AS_C_1_34_corrM : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) →
    (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α) →
      ∃ i : ℕ, IsC134CaseM i G₀ R L

theorem AS_C_1_34_corrM_of (hM : C134L32CorrM) (hb : burnsideC134w_AS_C_1_34_corrBig) :
    AS_C_1_34_corrM := by
  intro G _ _ G₀ R L hMS hL hG ⟨n, F, iF, fF, α, hcard, hα⟩
  by_cases hn : n = 1
  · subst hn
    exact hM G G₀ R L hMS hL hG ⟨F, iF, fF, α, by simpa using hcard, hα⟩
  · have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with h | h
      · have h0 : n = 0 := by omega
        subst h0
        have h1 : Fintype.card F = 1 := by simpa using hcard
        have h2 : 1 < Fintype.card F := Fintype.one_lt_card
        omega
      · exact h
    obtain ⟨i, hi⟩ := hb G G₀ R L hMS hL hG ⟨n, F, iF, fF, α, hn2, hcard, hα⟩
    exact ⟨i, IsC134CaseM.of_corr hi⟩

structure C134Weak : Prop where
  small : C134L32CorrM
  big : burnsideC134w_AS_C_1_34_corrBig

theorem C134Weak.toM (h : C134Weak) : AS_C_1_34_corrM :=
  AS_C_1_34_corrM_of h.small h.big

theorem c134Weak_holds
    : C134Weak :=
  ⟨c134L32CorrM_holds, burnsideC134w_corrBig S4L.burnsideMag568_noNonlinSLGt4⟩

end CFSG.Quasithin.MS93
