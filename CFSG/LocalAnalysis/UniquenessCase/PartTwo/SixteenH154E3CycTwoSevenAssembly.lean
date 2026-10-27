module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoSetFrame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoSevenA1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoMasterG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoGoodG

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoSevenAssembly_exists
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
    ∃ P : Subgroup (MulAut (Vtil V₀ V hV)),
      P ≤ Mbar D.M V₀ V hV ∧
      Mbar D.M V₀ V hV ≤ Subgroup.normalizer (P : Set (MulAut (Vtil V₀ V hV))) ∧
      ¬ 7 ∣ P.relIndex (Mbar D.M V₀ V hV) ∧
      IsPGroup 7 ↥P ∧
      IsElemAbelianOfRank 7 3 ↥P ∧
      Subgroup.centralizer (P : Set (MulAut (Vtil V₀ V hV))) ⊓ Mbar D.M V₀ V hV ≤ P := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hsig : D.sig = {7} :=
    s16h_e3_CycTwoP7M6A_sig_eq D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp7 hm hbad
  have h7mem : 7 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 7
  obtain ⟨l, ψ, hLl, F⟩ :=
    s16h_e3_CycTwoSetFrame_exists (q := 7) (n := 6) D hV h hc (by norm_num) (by norm_num)
      (hp7 ▸ hLp) hs2 hm
  obtain ⟨T, hTA, hTab, hzT, hSyl, hcent⟩ :=
    s16h_e3_CycTwoSevenA1_structure D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp7 hm hbad hLl F
  obtain ⟨u₀, hu₀, hu₁, hK⟩ :=
    s16h_e3_CycTwoGoodG_vector (q := 7) (by norm_num) D S hr3 hV h h7mem hbad
  have hTe : IsElemAbelian 7 T := by
    obtain ⟨e⟩ := hTab
    refine ⟨IsMulCommutative.of_comm (fun a b => e.injective ?_), fun x hx => ?_⟩
    · rw [map_mul, map_mul, mul_comm]
    · have hpow : ∀ a : ↥T, a ^ 7 = 1 := by
        intro a
        apply e.injective
        rw [map_pow, map_one]
        ext i
        have h7 : (7 : ZMod 7) = 0 := by decide +revert
        simp [h7]
      simpa using congrArg Subtype.val (hpow ⟨x, hx⟩)
  have hCoreEl : IsElemAbelian 7 (F.core T) := s16h_e3_CycTwoCoreAG_isElemAbelian F hTe
  have hker : Nat.card ↥(F.core T ⊓ centSub (wTil V₀ V hV L)) ≤ 7 :=
    hK (F.core T ⊓ centSub (wTil V₀ V hV L)) (inf_le_left.trans (F.core_le T))
      (IsElemAbelian.mono hCoreEl inf_le_left) (fun r hr => mem_centSub.1 hr.2 u₀ hu₀)
  exact s16h_e3_CycTwoMasterG (q := 7) (m := 6) (by norm_num) (by norm_num) F hTA hTab hzT
    hSyl hcent hker

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
