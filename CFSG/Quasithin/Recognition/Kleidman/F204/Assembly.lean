module

public import CFSG.Quasithin.Recognition.Kleidman.F204.T3Main
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIMain
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIKills
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIO1Geo
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIOffNatA

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

section Assembly

variable (F : Frame L1 L2 S D X)
include F

theorem caseI_T1_false (hT1 : ConfigT1 L1 L2 S)
    {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hI : ¬ Zv α' ≤ Qv α) :
    False := by
  have hA := Amal.of_frame F
  have hb2 := two_le_bMin F
  by_cases hb : bMin (P1 L1 L2 S) (P2 L1 L2 S) = 2
  · exact caseI_b2_false F hT1 hb hc hI
  · have hb3 : 3 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S) := by omega
    obtain ⟨hvα, hvα', -, -, hrel1, hrel2⟩ := H4 F hT1 hc hI
    obtain ⟨hbα', hfα, hfα'⟩ := hA.caseI (frame_dichotomy F) hc hI
    have hsx : Zv α' ≤ stab α :=
      hA.Zv_le_stab_of_dist_le (by rw [CosetGeom.dist_comm, hc.dist_eq, hbα'])
    have hsy : Zv α ≤ stab α' := hA.Zv_le_stab_of_dist_le (by rw [hc.dist_eq, hc.bAt_eq])
    have hEx := inf_centralizer_eq_inf_Qv F hfα' hsy
    have hV2 : ∀ a ∈ Zv α', a ^ 2 = 1 := fun a ha => (hA.isElemAbelian_Zv α').2 a ha
    obtain ⟨hNα, -, -⟩ := H3_natA F hT1 hvα hsx
      (isPGroup_two_of_sq_gen fun u hu => Subtype.ext (by
        simpa using hV2 _ (Subgroup.mem_subgroupOf.mp hu)))
      (exists_noncomm_of_not_le F hEx hc.not_le) (by rw [hEx, hrel1, hrel2])
    exact caseI_false F hT1 (fun x hx => hNα.of_vtype_eq (hvα.trans hx.symm)) hc hI hrel1 hb3

theorem f204_false
    (hII1 : ConfigT1 L1 L2 S → ∀ {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)},
      IsCritData α β α' → Zv α' ≤ Qv α → False)
    (hII2 : (∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ZCentral δ ↔ vtype δ = true) →
      ∀ {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)}, IsCritData α β α' → Zv α' ≤ Qv α → False) :
    False := by
  have hA := Amal.of_frame F
  obtain ⟨α, hα⟩ := hA.exists_bAt_eq_bMin
  obtain ⟨β, hβ⟩ : ∃ β, β ∈ nbrs α := by
    by_contra hcon
    push Not at hcon
    have hcard := hA.card_nbrs α
    have : nbrs α = ∅ := Set.eq_empty_iff_forall_notMem.mpr hcon
    rw [this] at hcard
    simp at hcard
  obtain ⟨α', hc⟩ := hA.exists_critData hα (show (graph _ _ _).Adj α β from hβ)
  rcases hA.config with h1 | h2 | h3
  · by_cases hI : Zv α' ≤ Qv α
    · exact hII1 h1 hc hI
    · exact caseI_T1_false F h1 hc hI
  · by_cases hI : Zv α' ≤ Qv α
    · exact hII2 h2 hc hI
    · exact caseI_T2_false F h2 hc hI
  · exact T3_false F h3

end Assembly

end CFSG.Quasithin.Kleidman.F204
