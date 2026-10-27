module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4AA2AAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4AA2AACAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_CycTwoP3M4AA2AACA_isCharacteristicP_of_normalSylow
    {X : Type} [Group X] [Finite X] {H P : Subgroup X} (hPle : P ≤ H)
    (hPnorm : H ≤ Subgroup.normalizer (P : Set X)) (hPgrp : IsPGroup 3 P)
    (hPcent : Subgroup.centralizer (P : Set X) ⊓ H ≤ P) :
    CFSG.IsCharacteristicP 3 ↥H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : (P.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mpr hPnorm
  have hsub : P.subgroupOf H ≤ CFSG.pCore 3 ↥H :=
    le_sSup ⟨hN, hPgrp.of_equiv (Subgroup.subgroupOfEquivOfLe hPle).symm⟩
  intro x hx
  refine hsub (Subgroup.mem_subgroupOf.mpr ?_)
  have hxcent : (x : X) ∈ Subgroup.centralizer (P : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hnH : n ∈ H := hPle hn
    have hncore : (⟨n, hnH⟩ : ↥H) ∈ CFSG.pCore 3 ↥H :=
      hsub (Subgroup.mem_subgroupOf.mpr hn)
    have h1 := Subgroup.mem_centralizer_iff.mp hx ⟨n, hnH⟩ hncore
    exact congrArg Subtype.val h1
  exact hPcent (Subgroup.mem_inf.mpr ⟨hxcent, x.2⟩)

theorem s16h_e3_CycTwoP3M4AA2AACA_characteristicP
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
    (hp3 : p = 3) (hm : rk ↥(wTil V₀ V hV L) = 4)
    (hW : ¬ ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    CFSG.IsCharacteristicP 3 ↥(Mbar D.M V₀ V hV) := by
  have h3 : D.sig = {3} :=
    (s16h_e3_CycTwoP3M4AA2AAA_sigma_eq_three D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp3 hm hW).1
  obtain ⟨P, hPle, hPnorm, -, hPgrp, -, hPcent⟩ :=
    s16h_e3_CycTwoP3M4AA2AACAA_normal_sylow_selfCentralizing
      D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp3 hm hW h3
  exact s16h_e3_CycTwoP3M4AA2AACA_isCharacteristicP_of_normalSylow hPle hPnorm hPgrp hPcent

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
