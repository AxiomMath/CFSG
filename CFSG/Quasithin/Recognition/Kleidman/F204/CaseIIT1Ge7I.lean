module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7H
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Sec

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

section CaseII

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
  {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α)
  (hb7 : 7 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S))
  (hF1 : ∀ x : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype x = true → ∀ d ∈ nbrs x, ∀ d' ∈ nbrs x,
    d ≠ d' → Zv d ⊓ Zv d' = ⊥)
include F hT1 hc hII hb7 hF1

theorem caseII_T1_false_ge7_mu {μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hμ : μ ∈ nbrs α')
    (hμβ : ¬ Zv μ ≤ Qv β) : False := by
  have hA := Amal.of_frame F
  obtain ⟨-, hβ, -, -, -⟩ := t1II_setup F hT1 hc hII
  refine caseII_T1_false_ge7_of F hT1 hc hII hb7 hF1 hμ hμβ ?_
  intro t htβ htQ ht2 Y hYU hYidx hYt
  refine five_centralizes_mod F hβ (hA.isElemAbelian_Vball (by omega) β)
    (stab_le_normalizer_Vball 3 β) (Vn_le_Vball_one β |>.trans (Vball_mono (by omega) β))
    (stab_le_normalizer_Vn β) htβ htQ ?_ hYU hYidx hYt
  rw [ht2]
  exact one_mem _

end CaseII

end CFSG.Quasithin.Kleidman.F204
