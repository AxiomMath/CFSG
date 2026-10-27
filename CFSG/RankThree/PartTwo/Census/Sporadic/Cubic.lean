module

public import CFSG.RankThree.PartTwo.Census.Sporadic.Common
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.J2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.M24
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.He
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.Ru
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.RuLocal

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint TauCeti CFSG.QuasithinUnique.SQTK
open scoped commutatorElement

theorem excluded433_M12 : Excluded433 (.sporadic .M12) := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.M12_sylow3_cubic_witness
  exact excluded433_sporadic_of_cubic (T := NativeSporadic.M12)
    (fun _ => CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv.map MulEquiv.symm)
    CFSG.Sporadic.Mathieu.card_M12 (by norm_num) ⟨x, y, hxy, hc⟩

theorem excluded433_M24 : Excluded433 (.sporadic .M24) := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
  exact excluded433_sporadic_of_cubic (T := NativeSporadic.Carrier .M24)
    (fun _ => nonempty_mulEquiv_carrier_M24) CFSG.Sporadic.Mathieu.card_M24 (by norm_num)
    ⟨x, y, hxy, hc⟩

theorem excluded433_J2 : Excluded433 (.sporadic .J2) := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.J2_sylow3_cubic_witness
  exact excluded433_sporadic_of_cubic (T := NativeSporadic.J2)
    (fun _ => CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv.map MulEquiv.symm)
    CFSG.Sporadic.J2.card_J2 (by norm_num) ⟨x, y, hxy, hc⟩

theorem excluded433_He : Excluded433 (.sporadic .He) := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
  exact excluded433_sporadic_of_cubic (T := NativeSporadic.Carrier .He)
    (fun _ => nonempty_mulEquiv_carrier_He) CFSG.Sporadic.He.card_He (by norm_num)
    ⟨x, y, hxy, hc⟩

theorem excluded433_Ru : Excluded433 (.sporadic .Ru) := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.Ru_sylow3_cubic_witness
  exact excluded433_sporadic_of_cubic (T := NativeSporadic.Carrier .Ru)
    (fun _ => nonempty_mulEquiv_carrier_Ru) CFSG.Sporadic.Ru.card_Ru (by norm_num)
    ⟨x, y, hxy, hc⟩

end CFSG.RankThree.PartTwo.Census
