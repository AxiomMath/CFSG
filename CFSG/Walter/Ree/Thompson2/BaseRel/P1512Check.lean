module

public import CFSG.Walter.Ree.Thompson2.BaseRel.P1512Data
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Walter.Ree.T2.BaseRel.P1512Data

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 1898 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 0 3000 =
      true := by
  decide +kernel

theorem facts_1 :
    factsOK 1898 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 3000 3000 =
      true := by
  decide +kernel

theorem facts_2 :
    factsOK 1898 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 6000 1728 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 1898 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 0 7728 =
      true := by
  rw [show (7728 : ℕ) = 3000 + 4728 from rfl, factsOK_add, facts_0,
    Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  rw [show (4728 : ℕ) = 3000 + 1728 from rfl, factsOK_add, facts_1,
    Bool.true_and, show (3000 : ℕ) + 3000 = 6000 from rfl]
  exact facts_2

theorem cover_0 : coverOK 1898 8 7728 fx fc fy (invLetter 4) ffi live 0 15184 = true := by
  decide +kernel

theorem cover_all : coverOK 1898 8 7728 fx fc fy (invLetter 4) ffi live 0 15184 = true := by
  exact cover_0

theorem liveCount_eq : liveCount live 1898 = 1512 := by
  decide +kernel

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Walter.Ree.T2.BaseRel.P1512Data
