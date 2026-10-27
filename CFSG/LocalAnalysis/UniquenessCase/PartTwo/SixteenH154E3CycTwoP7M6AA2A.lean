module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6AA2AA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_CycTwoP7M6A_isCharacteristicP_of_normalSylow
    {X : Type} [Group X] [Finite X] {H P : Subgroup X} (hPle : P ≤ H)
    (hPnorm : H ≤ Subgroup.normalizer (P : Set X)) (hPgrp : IsPGroup 7 P)
    (hPcent : Subgroup.centralizer (P : Set X) ⊓ H ≤ P) :
    CFSG.IsCharacteristicP 7 ↥H := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hN : (P.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mpr hPnorm
  have hsub : P.subgroupOf H ≤ CFSG.pCore 7 ↥H :=
    le_sSup ⟨hN, hPgrp.of_equiv (Subgroup.subgroupOfEquivOfLe hPle).symm⟩
  intro x hx
  refine hsub (Subgroup.mem_subgroupOf.mpr ?_)
  have hxcent : (x : X) ∈ Subgroup.centralizer (P : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hnH : n ∈ H := hPle hn
    have hncore : (⟨n, hnH⟩ : ↥H) ∈ CFSG.pCore 7 ↥H :=
      hsub (Subgroup.mem_subgroupOf.mpr hn)
    have h1 := Subgroup.mem_centralizer_iff.mp hx ⟨n, hnH⟩ hncore
    exact congrArg Subtype.val h1
  exact hPcent (Subgroup.mem_inf.mpr ⟨hxcent, x.2⟩)

theorem s16h_e3_CycTwoP7M6A_isCharacteristicP
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n)
    (hs2 : s15 D.M V₀ V hV L = 2)
    (hres : ∀ q ∈ D.sig, q = p ∨
      (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6 ∧ q = 3))
    (hp7 : p = 7) (hm : rk ↥(wTil V₀ V hV L) = 6)
    (hbad : ¬ ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    CFSG.IsCharacteristicP 7 ↥(Mbar D.M V₀ V hV) := by
  obtain ⟨P, hPle, hPnorm, -, hPgrp, -, hPcent⟩ :=
    s16h_e3_CycTwoP7M6A_normSylow_selfCent D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp7 hm hbad
  exact s16h_e3_CycTwoP7M6A_isCharacteristicP_of_normalSylow hPle hPnorm hPgrp hPcent

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
