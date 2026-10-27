module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6AA2AA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP7M6A_exists_normal_sylow_seven
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
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)))
    (hLle : lBar V₀ V hV L ≤ pCoreOf 7 (Mbar D.M V₀ V hV)) :
    ∃ P : Subgroup (MulAut (Vtil V₀ V hV)),
      P ≤ Mbar D.M V₀ V hV ∧ (P.subgroupOf (Mbar D.M V₀ V hV)).Normal ∧
        IsElemAbelianOfRank 7 3 ↥P ∧
        ∀ Q : Subgroup (MulAut (Vtil V₀ V hV)), Q ≤ Mbar D.M V₀ V hV →
          IsPGroup 7 ↥Q → Q ≤ P := by
  obtain ⟨P, hPM, hnorm, hrel, hP7, hrk, -⟩ :=
    s16h_e3_CycTwoP7M6A_normSylow_selfCent D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp7 hm hbad
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hnormal : (P.subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).2 hnorm
  refine ⟨P, hPM, hnormal, hrk, fun Q hQM hQ7 => ?_⟩
  have hP' : IsPGroup 7 (P.subgroupOf (Mbar D.M V₀ V hV)) := hP7.comap_subtype
  have hrel' : ¬ 7 ∣ (P.subgroupOf (Mbar D.M V₀ V hV)).index := hrel
  let S7 : Sylow 7 ↥(Mbar D.M V₀ V hV) := hP'.toSylow hrel'
  haveI : (S7 : Subgroup ↥(Mbar D.M V₀ V hV)).Normal := hnormal
  obtain ⟨R, hR⟩ := (hQ7.comap_subtype (K := Mbar D.M V₀ V hV)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(Mbar D.M V₀ V hV) S7 R
  have hRS : R = S7 := by rw [← hg, Sylow.smul_eq_of_normal]
  intro x hx
  have hx' : (⟨x, hQM hx⟩ : ↥(Mbar D.M V₀ V hV)) ∈ R := hR hx
  rw [hRS] at hx'
  exact hx'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
