module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T516.PartA
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T516.PartB

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem theorem_5_16_a
    {p : ℕ} {A G : Subgroup Γ} (h : KSetting p A G) :
    nsOf p A G ∈ nsSet p A G :=
  T516.nsOf_mem_nsSet h

theorem theorem_5_16_b
    {p : ℕ} {A G X : Subgroup Γ} (h : KSetting p A G)
    (hX : IsDAInvariant A G X) (hK : kOf X = X) : X ≤ Subgroup.normalizer (nsOf p A G : Set Γ) :=
  T516.normalizer_nsOf h hX hK

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
