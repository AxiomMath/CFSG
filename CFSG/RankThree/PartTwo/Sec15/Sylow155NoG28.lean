module

import CFSG.RankThree.PartTwo.Sec15.Sylow155CD1
import CFSG.RankThree.PartTwo.Sec15.Sylow155E0
public import CFSG.RankThree.PartTwo.Sec15.Sylow155E0Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155F1Con

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Step155NoG28W (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P → Item146 A (lB A) →
    CFSG.Open.pCoreOf 2 Y ≤ P →
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) →
      ∀ g ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ M,
        g ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G) →
          Odd (orderOf g) →
          (∀ B : Subgroup G, IsHyperplane A B → B ≠ A ⊓ L →
            CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (B : Set G) ≤
              Subgroup.centralizer ({g} : Set G)) →
          g = 1

@[expose] def Step155NoG28WR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → (omegaA A).ncard = 3 →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    Step155NoG28W A c L

theorem step155F1ZeroW_of_noG28
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h3 : (omegaA A).ncard = 3) (h142 : Concl142 A (lB A)) (hN : Step155NoG28W A c L) :
    Step155F1ZeroW A c L := by
  intro h X K Y M T P hC hmax hab hE h146 hRP hIX g hg hgZ hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAM : A ≤ M := fun a ha => hC.mem_m.2 (Subgroup.mem_sup_left ha)
  have hAV : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    hAM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hV3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 M) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
    rw [hk]
    intro h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  have hgA : g ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hg.1
  refine hN h X K Y M T P hC hmax hab hE h146 hRP hIX g hg hgZ hodd fun B hBA hBL => ?_
  exact Sylow155F1.inf_centralizer_le_of_bal h.isE27 h142
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hAV hgA
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hg.2) hgZ hodd hBA fun hfree =>
      Sylow155F1.commutator_le_pPrimeCoreOf_of_isPConstrained h hV3 hAV hBA
        (Sylow155CD1.isPConstrained_centralizer_of_ncard_three h134 h48 hR hJ h3 hBA hfree hBL)
        hgA

theorem step155HostE0W_of_noG28
    (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Concl142S14) (h1444 : Item1444S14)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h3 : (omegaA A).ncard = 3) (hN : Step155NoG28W A c L) : Step155HostE0W A c L :=
  step155HostE0W_of_hostCharSup (step155HostCharSupW_of_f1Zero (h1444 G A c L hR.toSec14Std)
    (step155F1ZeroW_of_noG28 h134 h48 hR hJ h3 (h142 G A c L hR.toSec14Std) hN))

end CFSG.RankThree.PartTwo.Sec15
