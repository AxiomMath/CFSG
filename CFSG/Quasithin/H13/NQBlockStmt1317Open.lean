module

public import CFSG.Quasithin.H13.NQBlockEscapeSimpleSource
public import CFSG.Quasithin.H13.NQBlockTerminalModule
public import CFSG.Quasithin.H13.NQBlockNoEscapeHolds
public import CFSG.Quasithin.H13.NQRigidR2aDeleted
public import CFSG.Quasithin.H13.NQRigidR1Open
public import CFSG.Quasithin.H13.NQCoreFourGroupProp

public section

namespace CFSG.Quasithin.H13.NQBlock

open CFSG.Open CFSG.QuasithinUnique

theorem stmt13_1_7_of_open
    (h1323 : Stmt13_1_2_three) (h3214 : Stmt3_2_14) (h56 : AsB56)
    (h317 : Theorem317Statement)
    (h3 : ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
      fusionIsBenderGroup G ∨ UniqueSmallModel G)
    (hpair : NQCore.StmtEscapingPairExcluded)
    : Stmt13_1_7 :=
  stmt13_1_7_of_witness_rigidity
    (NQCore.nonquasisimpleRadicalNormalizerWitness_of_open h3214 h1323)
    (NQRigid.nonquasisimpleInternalCentralizerRigidity_of_open h56 h317 h3
        (originalKEscapingSourceY_of_five h1323) originalNoNormalSourceYEscapes_holds
        (NQRigid.oblRigidCPUEvenLinearThreeParabolic_of_center NQRigid.factCenterOddPart_holds)
        (NQRigid.oblRigidCPUSymplecticFourDeleted_of_center NQRigid.factCenterOddPart_holds))
    (nonquasisimpleTITerminalContradiction_of_explicitModule
      (originalKEscapingSourceY_of_five h1323) originalNoNormalSourceYEscapes_holds
      (NQCore.nonquasisimpleTIEscapingResidual_of_pair h3 h1323 hpair)
      (NQRigid.oblRigidWholeModule_of_open h56 h317 h3 (originalKEscapingSourceY_of_five h1323)
        originalNoNormalSourceYEscapes_holds)
      NQCore.configurationFourGroupObstruction)

end CFSG.Quasithin.H13.NQBlock
