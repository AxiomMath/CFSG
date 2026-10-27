module

public import CFSG.Quasithin.Background.P4InspectStmt
public import CFSG.Quasithin.Background.P4InspEndPerm
public import CFSG.Quasithin.Background.P4InspEndA6
public import CFSG.Quasithin.Background.P4InspEndS5

public section

namespace CFSG.Quasithin.G11

open CFSG.Quasithin.G11.P4InspEnd

theorem inspectOuterEnd : InspectOuterEnd := by
  intro U _ _ _ f M K Q v hd _ hdata α P hαP hα2 hcomm
  rcases hdata with ha | ⟨-, ⟨θ⟩, hL⟩ | hc | hc8
  ·
    obtain ⟨φ, β, hβs, hker, hβe⟩ := ha
    obtain ⟨σ, hσ⟩ := p4inspend_aut_alt (n := 5) le_rfl (by norm_num) φ α
    exact p4inspend_induced φ β hβs hker hβe α σ hσ
  ·
    obtain ⟨⟨e⟩, -⟩ := hL
    obtain ⟨m, -, hm⟩ := p4inspend_outer_s5 M K hd.K_le hd.K_norm θ e α
    exact ⟨m, hm⟩
  ·
    obtain ⟨φ, β, hβs, hker, hβe⟩ := hc
    obtain ⟨σ, hσ⟩ := p4inspend_a6_outer φ α P hαP hα2 (fun s hs => (hcomm s hs s hs).2)
    exact p4inspend_induced φ β hβs hker hβe α σ hσ
  ·
    obtain ⟨φ, β, hβs, hker, hβe⟩ := hc8
    obtain ⟨σ, hσ⟩ := p4inspend_aut_alt (n := 8) (by norm_num) (by norm_num) φ α
    exact p4inspend_induced φ β hβs hker hβe α σ hσ

end CFSG.Quasithin.G11
