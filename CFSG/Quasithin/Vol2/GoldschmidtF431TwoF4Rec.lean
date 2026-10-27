module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4F48Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctSys
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctLab
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Simple

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LocalAnalysis.EvenBN.TwoF4 CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.BN

set_option linter.unusedSectionVars false


section Input

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

@[expose] def octInputOf (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hR : RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a) (octRoot K a))
    [IsSimpleGroup (Gm K a)] : OctInput K a hK where
  R := octSystemOf hR
  simple := inferInstance
  hU := isSylowTwoOf_Ug hK
  root k h1 h8 := by
    rw [octSystemOf_root]
    exact octRoot_eq_rootV hK h1 h8
  cartan t := by
    rw [octSystemOf_cartan]
    exact Subgroup.mem_subgroupOf.2 (by rw [← torusH_eq_reeFixedTorus hK]; exact ⟨t, rfl⟩)

end Input

section Recognition

variable (f : ℕ)
  (oct : ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)
    (hK : Nat.card K = 2 ^ (2 * a + 1)), 1 ≤ a → OctInput K a hK)

include oct

theorem f431Facts45_f4 (hm : F431ModelFacts .twistedF4 0 f) : F431Facts45 .twistedF4 0 f hm := by
  intro D _ hD A
  obtain ⟨a, K, _, _, _, ha, hfa, hK0, ⟨e⟩⟩ := f4_model_data hD
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK0, hfa]
  have := (oct K a hK ha).simple
  exact facts45L_of_rankTwo (oct K a hK ha).R (oct K a hK ha).hU (hm D hD).1 (by norm_num)
    e.symm A

theorem f431Recognition_f4_of_oct : F431Recognition .twistedF4 0 f :=
  recognition_of_facts (f431ModelFacts_f4 f) (f431Generation_f4 f) (polyNumber .twistedF4)
    (three_le_polyNumber _) (f431Facts45_f4 f oct (f431ModelFacts_f4 f))
    (f431F48_f4 f (f431ModelFacts_f4 f) oct (f431Facts45_f4 f oct (f431ModelFacts_f4 f))
      (f431Generation_f4 f))

end Recognition

theorem f431Recognition_f4 (f : ℕ)
    (hR : ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ),
      1 ≤ a → Nat.card K = 2 ^ (2 * a + 1) →
        RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a) (octRoot K a)) :
    F431Recognition .twistedF4 0 f :=
  f431Recognition_f4_of_oct f fun K _ _ _ a hK ha =>
    haveI := isSimpleGroup_gm ha hK
    octInputOf hK (hR K a ha hK)

end CFSG.Quasithin.H13.F431.TwoF4
