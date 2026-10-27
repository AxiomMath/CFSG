module

public import CFSG.Quasithin.Vol2.Ch4Sec4Hyp
public import CFSG.Quasithin.Vol2.Ch4Sec4Frattini

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M L B Tp : Subgroup G}

theorem lemma_4_4_5_core (h : Hyp4_4_1Core G T M L B Tp) :
    conjClosure L T = perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ⊔
      pCoreOf 2 (conjClosure L T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQX := pCoreOf_le 2 (conjClosure L T)
  have hBX : B ≤ Subgroup.normalizer (conjClosure L T : Set G) :=
    le_normalizer_of_commutator_le_self (h.commutator_le.trans hQX)
  exact eq_perfectCore_sup (pCoreOf_isPGroup 2 _) h.B_odd hQX (le_normalizer_pCoreOf 2 _)
    (hBX.trans (normalizer_le_normalizer_pCoreOf 2 _)) h.commutator_le
    (conjClosure_perfect h.maximal.1.2.1.2.1)

theorem lemma_4_4_5 (h : Hyp4_4_1Two G T M L B Tp) :
    conjClosure L T = perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ⊔
      pCoreOf 2 (conjClosure L T) :=
  lemma_4_4_5_core h.toHyp4_4_1Core

theorem lemma_4_4_5_orbit (h : Hyp4_4_1TwoOrbit G T M L B Tp) :
    conjClosure L T = perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ⊔
      pCoreOf 2 (conjClosure L T) :=
  lemma_4_4_5_core h.toHyp4_4_1Core

end CFSG.Quasithin.H13
