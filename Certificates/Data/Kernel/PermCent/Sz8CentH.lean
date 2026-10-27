module

public import Certificates.Data.Kernel.PermCent.KGrpC2
public import Certificates.Data.Kernel.PermCent.SmallK65
public import Certificates.Data.Kernel.PermCent.SplitC
public import CFSG.GH74.KGroups.Sz8TablesInputs

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5115

open CFSG.GH74.KGroups.Sz8

@[expose] noncomputable def centF (LS : List (CV 65)) (σ : CV 65) : Bool :=
  !(LS.all fun q => eq22C σ q q σ) || decide (σ ∈ LS)

@[expose] noncomputable def q0 : CV 65 := (elemsC QS).getD 1 1

@[expose] noncomputable def centH : Bool :=
  allSplit (levelsC QA) fun t r => !(cmPt t r q0 0 && cmPt t r q0 64) || centF (elemsC QS) (t * r)

theorem centH_gen (L : List (List (CV 65))) (LS : List (CV 65)) (q : CV 65) (hq : q ∈ LS) :
    allSplit L (fun t r => !(cmPt t r q 0 && cmPt t r q 64) || centF LS (t * r)) =
      (productsC L).all (centF LS) := by
  apply allSplit_pre
  intro t r h
  have hc : eq22C (t * r) q q (t * r) = false := by
    cases e : eq22C (t * r) q q (t * r)
    · rfl
    · rw [cmPt_of (p := 0) (by norm_num) e, cmPt_of (p := 64) (by norm_num) e] at h
      exact absurd h (by decide)
  have hall : (LS.all fun x => eq22C (t * r) x x (t * r)) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    have := List.all_eq_true.1 hh q hq
    rw [hc] at this
    exact Bool.false_ne_true this
  rw [centF, hall]
  rfl

end CFSG.Certificates.Kernel.PkCV.KGrp.K5115

end
