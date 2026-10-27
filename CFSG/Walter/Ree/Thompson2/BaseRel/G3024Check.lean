module

public import CFSG.Walter.Ree.Thompson2.BaseRel.G3024Data
public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Walter.Ree.T2.BaseRel.G3024Data

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 4124 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 0 3000 =
      true := by
  decide +kernel

theorem facts_1 :
    factsOK 4124 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 3000 3000 =
      true := by
  decide +kernel

theorem facts_2 :
    factsOK 4124 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 6000 3000 =
      true := by
  decide +kernel

theorem facts_3 :
    factsOK 4124 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 9000 3000 =
      true := by
  decide +kernel

theorem facts_4 :
    factsOK 4124 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 12000 3000 =
      true := by
  decide +kernel

theorem facts_5 :
    factsOK 4124 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 15000 1885 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 4124 9 fx fc fy kind wi fs ft fo refs pl (invLetter 4)
      words [] 0 16885 =
      true := by
  rw [show (16885 : ℕ) = 3000 + 13885 from rfl, factsOK_add, facts_0,
    Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  rw [show (13885 : ℕ) = 3000 + 10885 from rfl, factsOK_add, facts_1,
    Bool.true_and, show (3000 : ℕ) + 3000 = 6000 from rfl]
  rw [show (10885 : ℕ) = 3000 + 7885 from rfl, factsOK_add, facts_2,
    Bool.true_and, show (6000 : ℕ) + 3000 = 9000 from rfl]
  rw [show (7885 : ℕ) = 3000 + 4885 from rfl, factsOK_add, facts_3,
    Bool.true_and, show (9000 : ℕ) + 3000 = 12000 from rfl]
  rw [show (4885 : ℕ) = 3000 + 1885 from rfl, factsOK_add, facts_4,
    Bool.true_and, show (12000 : ℕ) + 3000 = 15000 from rfl]
  exact facts_5

theorem cover_0 : coverOK 4124 8 16885 fx fc fy (invLetter 4) ffi live 0 20000 = true := by
  decide +kernel

theorem cover_1 : coverOK 4124 8 16885 fx fc fy (invLetter 4) ffi live 20000 12992 = true := by
  decide +kernel

theorem cover_all : coverOK 4124 8 16885 fx fc fy (invLetter 4) ffi live 0 32992 = true := by
  rw [show (32992 : ℕ) = 20000 + 12992 from rfl, coverOK_add, cover_0,
    Bool.true_and, show (0 : ℕ) + 20000 = 20000 from rfl]
  exact cover_1

theorem liveCount_eq : liveCount live 4124 = 3024 := by
  decide +kernel

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Walter.Ree.T2.BaseRel.G3024Data
