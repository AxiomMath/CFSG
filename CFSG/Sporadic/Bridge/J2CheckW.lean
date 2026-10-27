module

public import CFSG.Sporadic.Bridge.J2DataW
public import CFSG.Sporadic.Bridge.J2Weighted

public section

namespace CFSG.Sporadic.Bridge.J2Data

open CFSG.Certificates.CosetEnumeration CFSG.Sporadic.Bridge.J2

@[expose] def tgtG (j : ℕ) : ℕ := cond (Nat.beq j 0) 1 0

@[expose] def tgtZ (j : ℕ) : ℕ := cond (Nat.beq j 1) 1 0

theorem factsB_0 :
    factsOK 40382 5 fxB fcB fyB kindB wiB fsB ftB foB refsB pl (invLetter 2)
      wordsB [[0, 3], [0, 2, 0, 0, 2, 0]] 0 3000 = true := by
  decide +kernel

theorem factsB_1 :
    factsOK 40382 5 fxB fcB fyB kindB wiB fsB ftB foB refsB pl (invLetter 2)
      wordsB [[0, 3], [0, 2, 0, 0, 2, 0]] 3000 3000 = true := by
  decide +kernel

theorem factsB_2 :
    factsOK 40382 5 fxB fcB fyB kindB wiB fsB ftB foB refsB pl (invLetter 2)
      wordsB [[0, 3], [0, 2, 0, 0, 2, 0]] 6000 3000 = true := by
  decide +kernel

theorem factsB_3 :
    factsOK 40382 5 fxB fcB fyB kindB wiB fsB ftB foB refsB pl (invLetter 2)
      wordsB [[0, 3], [0, 2, 0, 0, 2, 0]] 9000 3000 = true := by
  decide +kernel

theorem factsB_4 :
    factsOK 40382 5 fxB fcB fyB kindB wiB fsB ftB foB refsB pl (invLetter 2)
      wordsB [[0, 3], [0, 2, 0, 0, 2, 0]] 12000 3000 = true := by
  decide +kernel

theorem factsB_5 :
    factsOK 40382 5 fxB fcB fyB kindB wiB fsB ftB foB refsB pl (invLetter 2)
      wordsB [[0, 3], [0, 2, 0, 0, 2, 0]] 15000 1893 = true := by
  decide +kernel

theorem factsB_all :
    factsOK 40382 5 fxB fcB fyB kindB wiB fsB ftB foB refsB pl (invLetter 2)
      wordsB [[0, 3], [0, 2, 0, 0, 2, 0]] 0 16893 = true := by
  rw [show (16893 : ℕ) = 3000 + 13893 from rfl, factsOK_add, factsB_0,
    Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  rw [show (13893 : ℕ) = 3000 + 10893 from rfl, factsOK_add, factsB_1,
    Bool.true_and, show (3000 : ℕ) + 3000 = 6000 from rfl]
  rw [show (10893 : ℕ) = 3000 + 7893 from rfl, factsOK_add, factsB_2,
    Bool.true_and, show (6000 : ℕ) + 3000 = 9000 from rfl]
  rw [show (7893 : ℕ) = 3000 + 4893 from rfl, factsOK_add, factsB_3,
    Bool.true_and, show (9000 : ℕ) + 3000 = 12000 from rfl]
  rw [show (4893 : ℕ) = 3000 + 1893 from rfl, factsOK_add, factsB_4,
    Bool.true_and, show (12000 : ℕ) + 3000 = 15000 from rfl]
  exact factsB_5

theorem weightsG_0 :
    weightsOK wtG kindB wiB ftB foB refsB tgtG wordsB
      [[0, 3], [0, 2, 0, 0, 2, 0]] 0 3000 = true := by
  decide +kernel

theorem weightsG_1 :
    weightsOK wtG kindB wiB ftB foB refsB tgtG wordsB
      [[0, 3], [0, 2, 0, 0, 2, 0]] 3000 3000 = true := by
  decide +kernel

theorem weightsG_2 :
    weightsOK wtG kindB wiB ftB foB refsB tgtG wordsB
      [[0, 3], [0, 2, 0, 0, 2, 0]] 6000 3000 = true := by
  decide +kernel

theorem weightsG_3 :
    weightsOK wtG kindB wiB ftB foB refsB tgtG wordsB
      [[0, 3], [0, 2, 0, 0, 2, 0]] 9000 3000 = true := by
  decide +kernel

theorem weightsG_4 :
    weightsOK wtG kindB wiB ftB foB refsB tgtG wordsB
      [[0, 3], [0, 2, 0, 0, 2, 0]] 12000 3000 = true := by
  decide +kernel

theorem weightsG_5 :
    weightsOK wtG kindB wiB ftB foB refsB tgtG wordsB
      [[0, 3], [0, 2, 0, 0, 2, 0]] 15000 1893 = true := by
  decide +kernel

theorem weightsG_all :
    weightsOK wtG kindB wiB ftB foB refsB tgtG wordsB
      [[0, 3], [0, 2, 0, 0, 2, 0]] 0 16893 = true := by
  rw [show (16893 : ℕ) = 3000 + 13893 from rfl, weightsOK_add, weightsG_0,
    Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  rw [show (13893 : ℕ) = 3000 + 10893 from rfl, weightsOK_add, weightsG_1,
    Bool.true_and, show (3000 : ℕ) + 3000 = 6000 from rfl]
  rw [show (10893 : ℕ) = 3000 + 7893 from rfl, weightsOK_add, weightsG_2,
    Bool.true_and, show (6000 : ℕ) + 3000 = 9000 from rfl]
  rw [show (7893 : ℕ) = 3000 + 4893 from rfl, weightsOK_add, weightsG_3,
    Bool.true_and, show (9000 : ℕ) + 3000 = 12000 from rfl]
  rw [show (4893 : ℕ) = 3000 + 1893 from rfl, weightsOK_add, weightsG_4,
    Bool.true_and, show (12000 : ℕ) + 3000 = 15000 from rfl]
  exact weightsG_5

theorem weightsZ_0 :
    weightsOK wtZ kindB wiB ftB foB refsB tgtZ wordsB
      [[0, 3], [0, 2, 0, 0, 2, 0]] 0 3000 = true := by
  decide +kernel

theorem weightsZ_1 :
    weightsOK wtZ kindB wiB ftB foB refsB tgtZ wordsB
      [[0, 3], [0, 2, 0, 0, 2, 0]] 3000 3000 = true := by
  decide +kernel

theorem weightsZ_2 :
    weightsOK wtZ kindB wiB ftB foB refsB tgtZ wordsB
      [[0, 3], [0, 2, 0, 0, 2, 0]] 6000 3000 = true := by
  decide +kernel

theorem weightsZ_3 :
    weightsOK wtZ kindB wiB ftB foB refsB tgtZ wordsB
      [[0, 3], [0, 2, 0, 0, 2, 0]] 9000 3000 = true := by
  decide +kernel

theorem weightsZ_4 :
    weightsOK wtZ kindB wiB ftB foB refsB tgtZ wordsB
      [[0, 3], [0, 2, 0, 0, 2, 0]] 12000 3000 = true := by
  decide +kernel

theorem weightsZ_5 :
    weightsOK wtZ kindB wiB ftB foB refsB tgtZ wordsB
      [[0, 3], [0, 2, 0, 0, 2, 0]] 15000 1893 = true := by
  decide +kernel

theorem weightsZ_all :
    weightsOK wtZ kindB wiB ftB foB refsB tgtZ wordsB
      [[0, 3], [0, 2, 0, 0, 2, 0]] 0 16893 = true := by
  rw [show (16893 : ℕ) = 3000 + 13893 from rfl, weightsOK_add, weightsZ_0,
    Bool.true_and, show (0 : ℕ) + 3000 = 3000 from rfl]
  rw [show (13893 : ℕ) = 3000 + 10893 from rfl, weightsOK_add, weightsZ_1,
    Bool.true_and, show (3000 : ℕ) + 3000 = 6000 from rfl]
  rw [show (10893 : ℕ) = 3000 + 7893 from rfl, weightsOK_add, weightsZ_2,
    Bool.true_and, show (6000 : ℕ) + 3000 = 9000 from rfl]
  rw [show (7893 : ℕ) = 3000 + 4893 from rfl, weightsOK_add, weightsZ_3,
    Bool.true_and, show (9000 : ℕ) + 3000 = 12000 from rfl]
  rw [show (4893 : ℕ) = 3000 + 1893 from rfl, weightsOK_add, weightsZ_4,
    Bool.true_and, show (12000 : ℕ) + 3000 = 15000 from rfl]
  exact weightsZ_5

end CFSG.Sporadic.Bridge.J2Data
