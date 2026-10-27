module

public import CFSG.Quasithin.Recognition.G23Ctx.Simple
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.All

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G23Type.Ctx

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23
  CFSG.GH74.QTGen4.Recog.G23.P7


theorem statementI45_holds : StatementI45 := by
  intro G _ _ ⟨H, H₁, H₂, M, hH, hM⟩
  obtain ⟨z, hz⟩ := exists_isZ hH
  obtain ⟨T, hTH, hT⟩ := exists_sylow_H H
  have hTG : quasithinIsSylowTwo T := sylow_G hH hz hTH hT
  obtain ⟨M', hM', hTM', hzV⟩ := exists_conj_M hH hM hz hTH hT
  have hVK : quasithinGenFitting M' ≤ H₁ ⊔ H₂ := fitting_le_sup hH hz hM' hzV
  have inv : ∀ w ∈ H, w ∉ H₁ ⊔ H₂ → Inverts H₁ w ∧ Inverts H₂ w :=
    fun w hw hwK => inverts_of_not_mem_sup hH hz hM' hzV hw hwK
  have cfg : Cfg G T H H₁ H₂ M' z :=
    ⟨hH, hM', hz, hTG, hTH, hTM', hzV, hVK, fun w hw hwK => (inv w hw hwK).1,
      fun w hw hwK => (inv w hw hwK).2⟩
  exact g23AtInv_holds G T H H₁ H₂ M'
    ⟨cfg.isSimpleGroup, hTG, hTH, hTM', hH, hM',
      fun w hw hwK x hx => inv_field hH hw (inv w hw hwK).1 (inv w hw hwK).2 x hx⟩

end CFSG.Quasithin.G23Type.Ctx
