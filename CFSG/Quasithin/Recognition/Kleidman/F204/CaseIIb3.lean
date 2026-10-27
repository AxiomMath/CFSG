module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIPropB
public import CFSG.Quasithin.Recognition.Kleidman.F204.T3Edge

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

section B3

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
  {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α)
include F hT1 hc hII

theorem caseII_T1_b3_false (hb : bMin (P1 L1 L2 S) (P2 L1 L2 S) = 3) : False := by
  have hA := Amal.of_frame F
  obtain ⟨hα, hβf, hα'f, -, -⟩ := t1II_setup F hT1 hc hII
  have hβ : β ∈ nbrs α := hc.adj
  obtain ⟨γ, hβγ, hγα'⟩ := exists_adj_dist_eq hA.amalgam.gen (α := α') (δ := β) (d := 1)
    (by rw [CosetGeom.dist_comm]; have := hc.dist_eq'; omega)
  have hγβ : β ∈ nbrs γ := (show (graph _ _ _).Adj β γ from hβγ).symm
  have hγα' : α' ∈ nbrs γ := by
    have : (graph _ _ _).Adj α' γ := dist_eq_one_iff_adj.mp hγα'
    exact this.symm
  have hγ : vtype γ = true := by
    have := vtype_ne_of_adj (show (graph _ _ _).Adj β γ from hβγ)
    rw [hβf] at this
    simpa using this.symm
  obtain ⟨r, -, hrβ, hrα', hr3, hr1⟩ := exists_three_two F hγ hγβ hγα'
  exact propB_false F hT1 hc hII hrα' hrβ hr3 hr1

end B3

end CFSG.Quasithin.Kleidman.F204
