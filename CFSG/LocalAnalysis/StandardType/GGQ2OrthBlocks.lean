module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksZero
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksExt
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksComp
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksIdem
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthTauMemOmega

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem orthIsQuasisimpleYcode_holds : OrthIsQuasisimpleYcode := by
  intro K _ _ _ ζ t δ hK hζ c hc
  cases c with
  | zero S => exact orthIsQuasisimpleYcode_zero ζ t δ hK S hc
  | extension e => exact orthIsQuasisimpleYcode_extension ζ t δ hK hζ e hc

theorem orthNotIsComponentOfYcode_holds : OrthNotIsComponentOfYcode := by
  intro K _ _ _ ζ t δ hK hζ c hc X
  cases c with
  | zero S => exact orthNotIsComponentOfYcode_zero ζ t δ hK S hc X
  | extension e => exact orthNotIsComponentOfYcode_extension ζ t δ hK hζ e hc X

theorem orthTauMemYcodeIff_holds : OrthTauMemYcodeIff := by
  intro K _ _ _ ζ t δ hK hζ c hc u
  cases c with
  | zero S => exact orthTauMemYcodeIff_zero ζ t δ orthTauMemOmega_holds hK hζ S hc u
  | extension e => exact orthTauMemYcodeIff_extension ζ t δ hK hζ e hc u

theorem orthTauCommuteYcodeIff_holds : OrthTauCommuteYcodeIff := by
  intro K _ _ _ ζ t δ hK hζ c hc u
  cases c with
  | zero S => exact orthTauCommuteYcodeIff_zero ζ t δ orthTauMemOmega_holds hK hζ S hc u
  | extension e => exact orthTauCommuteYcodeIff_extension ζ t δ hK hζ e hc u

theorem orthMarkedYcode_holds : OrthMarkedYcode := by
  intro K _ _ _ ζ t δ hK hζ c hc
  cases c with
  | zero S => exact orthMarkedYcode_zero ζ t δ hK S hc
  | extension e => exact orthMarkedYcode_extension ζ t δ hK hζ e hc

theorem orthIsComponentOfCentralizerTorusSetIff_holds :
    OrthIsComponentOfCentralizerTorusSetIff :=
  orthIsComponentOfCentralizerTorusSetIff_of orthIsComponentOfGlBlockCentralizer_holds
    orthIsQuasisimpleYcode_holds orthNotIsComponentOfYcode_holds

end CFSG.StandardType.GGQ2Frame.OrthBlocks
