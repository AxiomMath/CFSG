module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporKill

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open
open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.HardMathSupport.Dickson.I271 (SporPlaneKill CentGen)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (SporadicOnePairHolds)

namespace Spor

structure SporFacts (s : TauCeti.SporadicName) : Prop where
  finite : Finite (TauCeti.CFSGIndex.sporadic s).Group
  simple : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group
  nonabelian : ∃ a b : (TauCeti.CFSGIndex.sporadic s).Group, a * b ≠ b * a
  outer : Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group) ≤ 2
  bridge : Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group)

@[expose] def NoPlaneAt (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ Ē R : Subgroup (MulAut (TauCeti.CFSGIndex.sporadic s).Group),
    ¬ SporPlaneConf (TauCeti.CFSGIndex.sporadic s).Group p Ē R

theorem SporFacts.center_eq_bot {s : TauCeti.SporadicName} (F : SporFacts s) :
    Subgroup.center (TauCeti.CFSGIndex.sporadic s).Group = ⊥ := by
  haveI := F.simple
  exact CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup F.nonabelian

theorem noPlaneAt_of_sporPlaneKill {s : TauCeti.SporadicName} {p : ℕ} (F : SporFacts s) (hp : p.Prime)
    (hp2 : p ≠ 2) (h : SporPlaneKill s p) : NoPlaneAt s p := by
  haveI := F.finite
  haveI := F.simple
  intro Ē R
  exact not_sporPlaneConf_of_planeKill F.center_eq_bot hp hp2
    (h (TauCeti.CFSGIndex.sporadic s).Group F.simple F.nonabelian ⟨MulEquiv.refl _⟩).2

theorem noPlaneAt_of_sporadicOnePairHolds {s : TauCeti.SporadicName} {p : ℕ} (F : SporFacts s)
    (hp : p.Prime) (hp2 : p ≠ 2) (h : SporadicOnePairHolds s p) : NoPlaneAt s p := by
  haveI := F.finite
  haveI := F.simple
  intro Ē R
  have e : (TauCeti.CFSGIndex.sporadic s).Group ≃* NativeSporadic.Carrier s := F.bridge.some.symm
  exact not_sporPlaneConf_of_planeGenOrExc F.center_eq_bot hp hp2
    (planeGenOrExc_of_onePair F.center_eq_bot F.outer hp hp2 (h.1 _ ⟨e⟩) (h.2 _ ⟨e⟩))

theorem noPlaneAt_of_centGen {s : TauCeti.SporadicName} {p : ℕ} (F : SporFacts s) (hp : p.Prime)
    (hp2 : p ≠ 2) (h : CentGen p (TauCeti.CFSGIndex.sporadic s).Group) : NoPlaneAt s p := by
  haveI := F.finite
  haveI := F.simple
  intro Ē R
  exact not_sporPlaneConf_of_planeGenOrExc F.center_eq_bot hp hp2
    (planeGenOrExc_of_centGen F.center_eq_bot F.outer hp hp2 h)

theorem noPlaneAt_of_not_dvd {s : TauCeti.SporadicName} {p : ℕ} (F : SporFacts s) (hp : p.Prime)
    (hp2 : p ≠ 2) (h : ¬ p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group) : NoPlaneAt s p := by
  haveI := F.finite
  haveI := F.simple
  intro Ē R
  exact not_sporPlaneConf_of_planeGenOrExc F.center_eq_bot hp hp2
    (planeGenOrExc_of_not_dvd F.center_eq_bot
      (fun ε hε => mem_range_conj_of_card_outer_le_two F.outer hp hp2 ε hε) h)

end Spor

end CFSG.LocalAnalysis.UniquenessCase.UCK
