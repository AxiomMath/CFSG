module

public import CFSG.Walter.Ree.Thompson2.BaseFin.HatData
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Walter.Ree.T2.BaseFin.HatData

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 1512 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 0 3000 =
      true := by
  decide +kernel

theorem facts_1 :
    factsOK 1512 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 3000 3000 =
      true := by
  decide +kernel

theorem facts_2 :
    factsOK 1512 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 6000 48 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 1512 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 0 6048 =
      true := by
  rw [show (6048 : ℕ) = 3000 + 3048 from rfl, factsOK_add, facts_0,
    Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  rw [show (3048 : ℕ) = 3000 + 48 from rfl, factsOK_add, facts_1,
    Bool.true_and, show (3000 : ℕ) + 3000 = 6000 from rfl]
  exact facts_2

theorem cover_0 : coverOK 1512 8 6048 fx fc fy (invLetter 4) ffi live 0 12096 = true := by
  decide +kernel

theorem cover_all : coverOK 1512 8 6048 fx fc fy (invLetter 4) ffi live 0 12096 = true := by
  exact cover_0

theorem liveCount_eq : liveCount live 1512 = 1512 := by
  decide +kernel

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Walter.Ree.T2.BaseFin.HatData
