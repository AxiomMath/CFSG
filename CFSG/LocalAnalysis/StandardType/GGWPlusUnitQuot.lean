module

public import CFSG.LocalAnalysis.StandardType.GGWPlusUnitAut
public import CFSG.LocalAnalysis.StandardType.GGWPlusPerm
public import CFSG.LocalAnalysis.StandardType.GGWPlusDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggSolvQuotLeTwo_PSU
    {d n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 5 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d)
    (hperf : commutator (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊤)
    {Eb : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hA : IsElemAbelian p Eb)
    (hI : (Eb : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))) (LargeEvenGUSet (Fin d) K (2 ^ n)))
    (hr : p ^ (d - 2) ≤ Nat.card Eb) (hsc : GGTorusSelfCent p Eb) :
    GGSolvQuotLeTwo
      ((MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))).range ⊓ Subgroup.normalizer (Eb : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))))
      (Subgroup.centralizer (Eb : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))))) := by
  obtain ⟨ρ, hρs, hρk⟩ := exists_automizer_hom_PSU hK hn hd hp hpq hpd hperf hA hI hr hsc
  exact ggSolvQuotLeTwo_of_surj
    (fun Q _ f hf hQ => perm_solvable_quotient_card_le_two hd f hf hQ) ρ hρs hρk

end CFSG.StandardType
