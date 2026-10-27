module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4AA2AACA
public import CFSG.GroupTheory.PCore.PCoreOfIndex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_inf_centralizer_pCoreOf_le {Ω : Type*} [Group Ω] {p : ℕ}
    {Y X : Subgroup Ω} (hY : CFSG.IsCharacteristicP p ↥Y) (hXY : X ≤ Y)
    (hXC : X ≤ Subgroup.centralizer (pCoreOf p Y : Set Ω)) :
    X ≤ pCoreOf p Y := by
  intro x hx
  have hxc : (⟨x, hXY hx⟩ : ↥Y) ∈
      Subgroup.centralizer (CFSG.pCore p ↥Y : Set ↥Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqY : (q : Ω) ∈ pCoreOf p Y := Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hXC hx)) (q : Ω) hqY)
  exact Subgroup.mem_map.mpr ⟨⟨x, hXY hx⟩, hY hxc, rfl⟩

theorem s16h_e3_CycTwoP3M4AA2AAC_selfCentralizing
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
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)))
    (P : Subgroup (MulAut (Vtil V₀ V hV)))
    (hPle : P ≤ Mbar D.M V₀ V hV)
    (hPn : Mbar D.M V₀ V hV ≤ Subgroup.normalizer (P : Set (MulAut (Vtil V₀ V hV))))
    (hPrel : ¬ 3 ∣ P.relIndex (Mbar D.M V₀ V hV))
    (hPgrp : IsPGroup 3 P) :
    Subgroup.centralizer (P : Set (MulAut (Vtil V₀ V hV))) ⊓ Mbar D.M V₀ V hV ≤ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CFSG.IsCharacteristicP 3 ↥(Mbar D.M V₀ V hV) :=
    s16h_e3_CycTwoP3M4AA2AACA_characteristicP D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp3 hm hW
  have hle : P ≤ pCoreOf 3 (Mbar D.M V₀ V hV) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 3 hPle hPn hPgrp
  have hge : pCoreOf 3 (Mbar D.M V₀ V hV) ≤ P :=
    CFSG.GroupTheory.pCoreOf_le_of_not_dvd_relIndex hPle hPn hPrel
  have hcore : pCoreOf 3 (Mbar D.M V₀ V hV) = P := le_antisymm hge hle
  have hmem : Subgroup.centralizer (pCoreOf 3 (Mbar D.M V₀ V hV) :
        Set (MulAut (Vtil V₀ V hV))) ⊓ Mbar D.M V₀ V hV ≤
      pCoreOf 3 (Mbar D.M V₀ V hV) :=
    s16h_inf_centralizer_pCoreOf_le hchar inf_le_right inf_le_left
  rw [hcore] at hmem
  exact hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
