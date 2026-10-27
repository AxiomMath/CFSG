module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6AA2AAA2BA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP7M6AA2AAA2B_centralizer_le_of_normal_sylow
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
    (P : Subgroup (MulAut (Vtil V₀ V hV))) (hPM : P ≤ Mbar D.M V₀ V hV)
    (hnorm : (P.subgroupOf (Mbar D.M V₀ V hV)).Normal)
    (hrk : IsElemAbelianOfRank 7 3 ↥P)
    (hmax : ∀ Q : Subgroup (MulAut (Vtil V₀ V hV)), Q ≤ Mbar D.M V₀ V hV →
      IsPGroup 7 ↥Q → Q ≤ P) :
    Subgroup.centralizer (P : Set (MulAut (Vtil V₀ V hV))) ⊓
      Mbar D.M V₀ V hV ≤ P := by
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxc, hxM⟩ := hx
  have hLP : lBar V₀ V hV L ≤ P := by
    refine hmax (lBar V₀ V hV L) (barSub_mono V₀ V hV h.hyp151.le) ?_
    exact IsPGroup.of_card (n := 1) (by rw [hLp.2, hp7, pow_one])
  have hxcL : x ∈ Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    Subgroup.centralizer_le (show (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) ⊆
      (P : Set (MulAut (Vtil V₀ V hV))) from hLP) hxc
  have hxn : x ∈ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    Subgroup.centralizer_le_normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) hxcL
  exact s16h_e3_CycTwoP7M6AA2AAA2BA_centralizer_aux D S hr3 hσ hV h hc hp hLp hχ hs2 hres
    hp7 hm hbad P hPM hnorm hrk hmax hxM hxn hxc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
