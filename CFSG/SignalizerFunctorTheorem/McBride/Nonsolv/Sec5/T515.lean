module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515.PartA
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515.PartB

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem theorem_5_15_a
    {p : ℕ} {A G X : Subgroup Γ} (h : KSetting p A G)
    (hX : IsDAInvariant A G X) (hsolv : Group.IsSolvable (X ⊓ Subgroup.centralizer (A : Set Γ) :
      Subgroup Γ)) : X ≤ kDown G A :=
  T515ab.le_kDown_of_isSolvable_inf_centralizer h hX hsolv

theorem theorem_5_15_b
    {p : ℕ} {A G X J : Subgroup Γ} (h : KSetting p A G)
    (hX : IsDAInvariant A G X) (hJ : J ∈ mcalA G A) (hK : khat X = X) :
    X ≤ Subgroup.normalizer (J : Set Γ) :=
  T515ab.normalizer_of_mem_mcalA h hX hJ hK

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
