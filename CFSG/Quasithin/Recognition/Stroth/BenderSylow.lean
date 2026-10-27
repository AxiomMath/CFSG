module

public import CFSG.Quasithin.Recognition.Stroth.BenderFrame
public import CFSG.Quasithin.Recognition.Stroth.BenderAut
public import CFSG.Quasithin.Recognition.Stroth.SliceSplit

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem eq_sup_pCoreOf_of_bender_left (hF : Hyp111 L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hL : VSzBig L1 ∨ VU3Big L1 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L1)) :
    S = (S ⊓ L1) ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) :=
  eq_sup_pCoreOf_of_autFact hF hSB fun T _ hH hHodd hTH σ hσ hσT hσH =>
    mulAut_eq_one_of_fixes_borel_complement hL T hH hHodd hTH σ hσ hσT hσH

theorem eq_sup_pCoreOf_of_bender_right (hF : Hyp111 L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hL : VSzBig L2 ∨ VU3Big L2 ∨ ∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (oTwoQuot ↥L2)) :
    S = (S ⊓ L2) ⊔ pCoreOf 2 (L2 ⊔ bigB L1 L2 S) := by
  have h := eq_sup_pCoreOf_of_bender_left hF.symm (by rwa [bigB_comm]) hL
  rwa [bigB_comm] at h

end CFSG.Quasithin.Stroth
