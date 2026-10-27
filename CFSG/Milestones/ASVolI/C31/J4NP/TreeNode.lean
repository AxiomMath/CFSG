module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Milestones.ASVolI.C31.J4NP.Base
public import CFSG.Milestones.ASVolI.C31.J4NP.HClDefs
public import Certificates.Data.CFSGNative.J4Tree.Node

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.J4Tree.Native CFSG.J4Tree.Native.Node
open CFSG.Quasithin.J4Loc (omegaZ)

set_option maxRecDepth 20000

section Node

theorem burnsideJ4NP_Is2A_sq {x : J} (h : burnsideJ4NP_Is2A x) : x * x = 1 := by
  obtain ⟨g, rfl⟩ := h
  calc g * CFSG.Quasithin.J4Loc.z0 * g⁻¹ * (g * CFSG.Quasithin.J4Loc.z0 * g⁻¹)
      = g * (CFSG.Quasithin.J4Loc.z0 * CFSG.Quasithin.J4Loc.z0) * g⁻¹ := by group
    _ = 1 := by rw [burnsideJ4NP_z0_sq]; group

end Node

end CFSG.ASVolI
