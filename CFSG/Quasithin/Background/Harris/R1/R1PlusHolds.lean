module

public import CFSG.Quasithin.Background.Harris.R1.R1aLoc
public import CFSG.Quasithin.Recognition.SzR1cHolds
public import CFSG.Quasithin.Background.Harris.R1.NormGensL28Main
public import CFSG.Quasithin.Recognition.Kleidman.VBOdd.Main
public import CFSG.Quasithin.Recognition.SzVBA5EvenMain
public import CFSG.Quasithin.Recognition.Kleidman.VBEven.CaseB

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Quasithin


theorem f112R1PlusLoc_holds : F112R1PlusLocStatement :=
  f112R1PlusLoc_of_R1abcLoc
      (J2Vert.f112R1aLoc_of_abelian rankOneListedFacts
          (SzVB.f112R1aAbelian_of_A5 Kleidman.VBOdd.vbOddL24FarA5_holds
              (SzVB.vbEvenL24A5_of_leaves @Kleidman.VBEven.caseB_module
                  @Kleidman.VBEven.false_of_central))) (f112R1bLoc_of_gens normGensL28Stmt_holds)
      f112R1c_holds

end CFSG.Quasithin.Background.Harris.R1
