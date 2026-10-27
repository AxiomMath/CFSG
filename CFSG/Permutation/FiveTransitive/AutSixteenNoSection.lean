module

public import CFSG.Permutation.FiveTransitive.AutSixteenCoordinates
public import CFSG.Permutation.FiveTransitive.AutSixteenSection

public section

namespace CFSG

namespace FiveTransitive.AutSixteenNoSection

theorem no_surjection
    (Q : Type*) [Group Q] [Finite Q] (hcard : Nat.card Q = 16)
    (hcomm : IsMulCommutative Q) (hp : ∀ q : Q, q ^ 2 = 1)
    {F : Type*} [Finite F] (hF : Nat.card F = 7)
    (B : Subgroup (MulAut Q)) (f : B →* Equiv.Perm F) :
    ¬ Function.Surjective f := by
  classical
  obtain ⟨hperfect, hAutcard⟩ := AutSixteenCoordinates.perfect_and_card Q hcard hcomm hp
  let _ := hperfect
  let e : F ≃ Fin 7 := Finite.equivFinOfCardEq hF
  intro hf
  exact AutSixteenSection.no_surjection hAutcard B
    (e.permCongrHom.toMonoidHom.comp f) (e.permCongrHom.surjective.comp hf)

end FiveTransitive.AutSixteenNoSection

end CFSG
