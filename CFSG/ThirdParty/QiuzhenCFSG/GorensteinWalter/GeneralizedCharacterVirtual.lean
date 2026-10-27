module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.CharacterValues
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5

namespace CFSG
end CFSG
open CFSG

/-!
# Generalized characters as virtual characters

The Bender--Glauberman class-function library represents a generalized
character as a difference of two ordinary characters.  Suzuki's transfer
API uses the equivalent finite integral-combination representation.
-/

namespace CFSG.Theory.Character

universe u

/-- A generalized character in the class-function API is a virtual character
in the integral-combination API. -/
public theorem generalizedCharacter_isVirtualCharacter
    {G : Type u} [Group G] {phi : ClassFunction G}
    (hphi : IsGeneralizedCharacter phi) : IsVirtualCharacter phi := by
  classical
  rcases hphi with ⟨chi, psi, hchi, hpsi, rfl⟩
  have toVirtual {theta : ClassFunction G} (htheta : IsCharacter theta) :
      IsVirtualCharacter theta := by
    rcases htheta with ⟨n, rho, rfl⟩
    refine ⟨1, (fun _ : Fin 1 => (1 : ℤ)), (fun _ : Fin 1 => n),
      (fun _ : Fin 1 => rho), ?_⟩
    ext g
    simp [virtualCharacterOfRepresentations]
  exact Section3.isVirtualCharacter_sub (toVirtual hchi) (toVirtual hpsi)

end CFSG.Theory.Character
