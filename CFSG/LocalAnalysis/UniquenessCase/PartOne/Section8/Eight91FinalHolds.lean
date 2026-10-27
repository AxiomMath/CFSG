module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Final
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91SevenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91AutThirteenSeventyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91List2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91GammaHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

theorem r891_final_holds
    {G : Type} [Group G] [Finite G] {D : Data G} (hSg : SigmaStd D)
    {L S R A : Subgroup G} {n : ℕ} (hst : R891State D L S R A n) (h895 : R891Facts895 D L S n R)
    {Ys : Subgroup (R891Star (R891H L S) (R891Z L S))} (hY : R891YSet D L S n R Ys)
    (h897 : R891List897 (R891Ybar (R891H L S) (R891Z L S) Ys)) : False :=
  r891_final_of_primes hSg r891SevenCore_holds
    (fun _ _ _ hY' => mulAut_eq_one_of_list897_of_prime_ne hY') hst h895 hY h897

theorem r891_final_of_list896
    {G : Type} [Group G] [Finite G] {D : Data G} (hSg : SigmaStd D)
    {L S R A : Subgroup G} {n : ℕ} (hst : R891State D L S R A n) (h895 : R891Facts895 D L S n R)
    {Ys : Subgroup (R891Star (R891H L S) (R891Z L S))} (hY : R891YSet D L S n R Ys)
    (h896 : R891List896 (R891Ybar (R891H L S) (R891Z L S) Ys)) : False :=
  r891_final_holds hSg hst h895 hY
    (s891_list897_of_list D r891GammaList_holds L S R A n hst h895 Ys hY h896)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
