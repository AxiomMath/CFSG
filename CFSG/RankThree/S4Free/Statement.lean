module

public import CFSG.RankThree.S4Free.Basic

public section

universe u v

namespace CFSG.RankThree.S4Free

open Subgroup

theorem isAdmissibleHost_of_not_three_dvd {S : Type*} [Group S] {X : Type*} [Group X] [Finite X]
    {ι : S →* X} (h3 : ¬ 3 ∣ Nat.card X) (hinj : Function.Injective ι)
    (hsyl : ∃ P : Sylow 2 X, (P : Subgroup X) = ι.range)
    (hC : centralizer (oTwo X : Set X) ≤ oTwo X) : IsAdmissibleHost ι :=
  ⟨inferInstance, isSym4Free_of_not_three_dvd h3, hinj, hsyl, hC⟩

variable {S : Type u} [Group S]

end CFSG.RankThree.S4Free
