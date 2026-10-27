module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Two
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvCore
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTv

public section

namespace CFSG.StandardType.UnitTvQ2

open CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly

theorem noTransvection_odd {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hcov : Line63.UnitaryCoverOddAt 1 6 K)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 1 K 6)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hodd : Odd (Nat.card ψ.ker))
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)), ∀ l : L', x (ψ l) = ψ (a l))
    (hr : 3 ^ 4 ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A)
    (α : Subgroup.normalizer (A : Set (MulAut L'))) :
    ¬ GGIsTransvection 3 (A.normalizerMonoidHom α) := by
  have hcard : 3 ^ (6 / 3 + 2) ≤ Nat.card A := by simpa using hr
  obtain ⟨φ, hφs, hφker, hdiag⟩ := Line63.exists_diagModel_of hK le_rfl (by norm_num)
    Nat.prime_three (by norm_num) (by norm_num) hcov.1 hψ hker hperf hA hAI hcard
    (fun ψ'' hs hk => hcov.2 L' ψ'' hs (hk ▸ hker) hperf (hk ▸ hodd))
  have hM : UnitTB.Model φ := ⟨TableBU.unitaryFieldData_of_card hK le_rfl, hφs, hφker⟩
  exact UnitTv.not_transvection_of_model hM hK Nat.prime_three (by norm_num) (by norm_num)
    (by norm_num) hA hsc hdiag α

end CFSG.StandardType.UnitTvQ2

end
