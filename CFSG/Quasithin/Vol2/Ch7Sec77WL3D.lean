module

public import CFSG.Quasithin.Vol2.Ch7Sec77L3D
public import CFSG.Quasithin.Vol2.Ch7Sec77WL3C

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17 CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem c134Two_of_sl3W (hMS : C134L32CorrM) (hF : CharTwo H) {K : Subgroup G}
    (hK : K ∈ cComp H)
    (hQN : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hMSp : IsMSPair (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G))
      (T ⊓ Subgroup.centralizer (fsuV T I : Set G)))
    (eX : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)))
    (hL₀K : oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ≤ K)
    (hTpK : T ⊓ Subgroup.centralizer (Vp : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hH : K ⊔ T ⊓ Subgroup.centralizer (Vp : Set G) = H) :
    IsC134Case 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G))
      (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) K := by
  obtain ⟨i, hi⟩ := exists_c134CaseW hMS hK hQN hMSp eX
  by_cases hi2 : i = 2
  · subst hi2
    exact hi
  · exfalso
    obtain ⟨hV1, hV2, hV3⟩ := C.vm_facts hF hK hQN hL₀K hTpK hH
    have hKX : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 168 :=
      (Nat.card_congr eX.toEquiv).trans card_statedSL_three_two
    exact false_of_c134CaseW card_vm hV1 hV2 hV3 hKX hi hi2


end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
