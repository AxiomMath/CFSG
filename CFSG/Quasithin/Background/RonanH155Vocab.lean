module

public import CFSG.Quasithin.Background.RonanH143Sext
public import CFSG.Quasithin.Background.RonanH163Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH155

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143
  CFSG.Quasithin.RonanH163 CFSG.Quasithin.H.Mathieu

open scoped Classical in
@[expose] noncomputable def fixedSetR (z : P24) : Finset (Fin 24) :=
  Finset.univ.filter fun i => z i = i

@[expose] def Alt3Struct (Γ A : Subgroup P24) (a b : Fin 24) : Prop :=
  ∃ i ∈ A, i ∉ M22g a b ∧
    (∃ O' : Finset (Fin 24), IsOctR O' ∧ ¬ (a ∈ O' ∧ b ∈ O') ∧ fixedSetR i = O') ∧
    A = pCoreOf 2 (Γ ⊓ Subgroup.centralizer ({i} : Set P24)) ∧
    ∃ π : ↥(Γ ⊓ Subgroup.centralizer ({i} : Set P24)) →* GL (Fin 3) (ZMod 2),
      Function.Surjective π ∧ π.ker = A.subgroupOf (Γ ⊓ Subgroup.centralizer ({i} : Set P24))

@[expose] def Concl155 {V : Type*} [CommGroup V] {Γ : Subgroup P24} (ρ : ↥Γ →* MulAut V)
    (a b : Fin 24) (O : Finset (Fin 24)) (S : Finset (Finset (Fin 24))) (B : Finset (Fin 24))
    (T₀ : Subgroup P24) : Prop :=
  ∀ A : Subgroup P24, A ≤ T₀ ⊓ Γ → IsE2k 4 A →
    (A = KY Γ ((O.erase a).erase b) ∧ rk ↥(fixV (rImg ρ A)) = 5 ∧
        rkIdx (xiV (rImg ρ A)) = 1) ∨
      ((∃ g ∈ Γ, conjSubg g A ≤ KY Γ (S.erase B)) ∧ rk ↥(fixV (rImg ρ A)) = 2 ∧
        xiV (rImg ρ A) = ⊤) ∨
      (Alt3Struct Γ A a b ∧ rk ↥(fixV (rImg ρ A)) = 3 ∧ xiV (rImg ρ A) = ⊤) ∨
      (rk ↥(A ⊓ KY Γ ((O.erase a).erase b)) = 3 ∧ rk ↥(fixV (rImg ρ A)) = 3 ∧
        rkIdx (xiV (rImg ρ A)) ≤ 1)

end CFSG.Quasithin.RonanH155
