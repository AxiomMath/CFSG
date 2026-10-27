module

import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229NSE
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22r8100b_dvd_of_modEq {p m : ℕ} (h : (2 : ℤ) ^ m ≡ -1 [ZMOD (p : ℤ)]) :
    p ∣ 2 ^ m + 1 := by
  have h1 : (p : ℤ) ∣ -1 - 2 ^ m := Int.modEq_iff_dvd.1 h
  have h2 : (p : ℤ) ∣ ((2 ^ m + 1 : ℕ) : ℤ) := by
    push_cast
    have := dvd_neg.2 h1
    rwa [show -(-1 - (2 : ℤ) ^ m) = 2 ^ m + 1 by ring] at this
  exact Int.natCast_dvd_natCast.1 h2

theorem uc22s21r8100_hNS {D : Data G} {Ch : Choice2011 G}
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) (L : Subgroup G) (n s q : ℕ)
    (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) (hL2 : IsL2 (Bar2 L) n) (hs : Odd s)
    (hsn : s ∣ n) (hq : q.Prime) (hqs : q ∣ 2 ^ s - 1) : ¬ IsStronglyPEmbedded q D.M := by
  have hq2 := uc22ine229_ne_two hs hqs
  obtain ⟨x, -, hxo, hxT⟩ : ∃ x ∈ conjClosure D.M L, orderOf x = q ∧
      x ∈ normalizer (D.T : Set G) :=
    uc22ine229_exists_mem_conjClosure_normalizer_of_isL2 D.sylowM hL hc2.le hL2 hs hsn hq hqs
  exact uc22ine229_not_sp_of_mem_normalizer h211 h1930 c hq hq2 hxT hxo

end CFSG.LocalAnalysis.UniquenessCase.UC22
