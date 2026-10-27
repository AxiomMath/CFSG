module

public import CFSG.Quasithin.Vol2.Ch3E213MP6BG
public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2GrpLine
public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2FldA
public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2FldC

public section

namespace CFSG.Quasithin.Ch3E213M.Sp4C2

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (uElt)
open CFSG.Quasithin.SteinbergBS (upper_of_mem_normalizer)

theorem factSp4CTwo_holds : FactSp4CTwo := by
  intro k _ _ _ n hn hk W hWZ hl hsp hT g hg htr htr'
  obtain ⟨h, hhN, j, ⟨r, rfl⟩, hσ⟩ := hT
  have hh : IsUpper h := upper_of_mem_normalizer hhN
  obtain ⟨b₀, c₀, hb₀, hc₀, hz₀⟩ := P6B.exists_c2_mem hWZ hl hh hσ hsp
  have hz₀I : uElt 0 b₀ c₀ 0 ∈ W ⊔ W.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_sup_left hz₀
  have hz₀g : g * uElt 0 b₀ c₀ 0 * g⁻¹ ∈ W ⊔ W.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_sup_right ⟨_, hz₀, rfl⟩
  obtain ⟨Γ, φ, -, h2, h3⟩ := exists_twisted_line htr htr' hg hb₀ hc₀ hz₀I hz₀g
  obtain ⟨s, hs⟩ := exists_subfield_line hc₀ hb₀ Γ φ h3 h2
  exact exists_szCentre_of_twist hWZ hsp hh hσ hc₀ hb₀ fun b c hw =>
    hs b c (Subgroup.mem_sup_left hw)

end CFSG.Quasithin.Ch3E213M.Sp4C2
