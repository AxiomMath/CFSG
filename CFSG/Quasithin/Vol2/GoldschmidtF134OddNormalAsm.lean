module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporDef
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddAsmOut
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddMain
public import CFSG.Quasithin.H13.NQCoreP134Normal

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native

theorem facts134OddNormal_of_cases
    (hC : F6.NativeTheoremCSection) (h36 : A36CoreForSQTKCat)
    (hS : Facts134OddSporadic) (hL : Facts134OddLie) : Facts134OddNormal := by
  intro A _ _ p _ L P T hp5 hcfg
  have hp2 : p ≠ 2 := by omega
  have hq : CFSG.IsQuasisimple ↥L := hcfg.component.1
  have hLc : L ∈ cComp (⊤ : Subgroup A) := mem_cComp_top_of_isComponent hcfg.component
  have hZ := card_center_of_a36Common' hq (h36 A hcfg.hyp L hLc).2.1
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
  have hlist := hC A ⟨hcfg.hyp.sqt, hcfg.hyp.kgroup⟩ L (Subgroup.center ↥L) hq.2.2
  rcases hlist with ⟨n, h5, h8, ⟨e⟩⟩ | ⟨r, hr, hr2, h⟩ | ⟨⟨f, h⟩ | h⟩ | ⟨n, hn, h⟩ | ⟨s, hs, ⟨e⟩⟩
  · exact (hL.alt n h5 h8 A p L P T hp5 hcfg hZ ⟨e⟩).elim
  · rcases h with ⟨f, hf, h⟩ | h | h
    · exact (hL.psl2Odd r f hr hr2 hf A p L P T hp5 hcfg hZ h).elim
    · obtain ⟨hrp, hP⟩ := hL.psl3Odd r A p L P T hr hr2 hp5 hcfg hZ h
      exact oddOutcome_of_psl3 hq hZ hp2 (hrp ▸ h) hP
    · exact (hL.psu3Odd r hr hr2 A p L P T hp5 hcfg hZ h).elim
  · rcases h with h | h | h | h | h | h | h | h
    · exact (hL.psl2Even f A p L P T hp5 hcfg hZ h.2).elim
    · exact (hL.psl3Even f A p L P T hp5 hcfg hZ h.2).elim
    · exact (hL.psu3Even f A p L P T hp5 hcfg hZ h.2).elim
    · exact oddOutcome_of_psp4 hq hZ h.2 (hL.psp4Even f A p L P T hp5 hcfg hZ h.2)
    · exact (hL.g2Even f A p L P T hp5 hcfg hZ h.2).elim
    · exact (hL.d4Even f A p L P T hp5 hcfg hZ h.2).elim
    · exact (hL.f4Even f A p L P T hp5 hcfg hZ h.2.2).elim
    · exact (hL.sz f A p L P T hp5 hcfg hZ h.2.2).elim
  · exact (hL.tits A p L P T hp5 hcfg hZ h).elim
  · exact (hL.psl45 n hn A p L P T hp5 hcfg hZ h).elim
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hS.m11 A p L P T hp5 hcfg hZ ⟨e⟩).elim
    · exact (hS.m12 A p L P T hp5 hcfg hZ ⟨e⟩).elim
    · exact (hS.m22 A p L P T hp5 hcfg hZ ⟨e⟩).elim
    · exact (hS.m23 A p L P T hp5 hcfg hZ ⟨e⟩).elim
    · exact (hS.m24 A p L P T hp5 hcfg hZ ⟨e⟩).elim
    · exact (hS.j1 A p L P T hp5 hcfg hZ ⟨e⟩).elim
    · exact (hS.j2 A p L P T hp5 hcfg hZ ⟨e⟩).elim
    · exact (hS.j4 A p L P T hp5 hcfg hZ ⟨e⟩).elim
    · exact (hS.hs A p L P T hp5 hcfg hZ ⟨e⟩).elim
    · exact (hS.he A p L P T hp5 hcfg hZ ⟨e⟩).elim
    · exact (hS.ru A p L P T hp5 hcfg hZ ⟨e⟩).elim

end CFSG.Quasithin.H13.NQCore
