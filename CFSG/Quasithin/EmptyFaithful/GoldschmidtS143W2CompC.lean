module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompB
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoOfNoComponent

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

theorem pCoreOf_eq_map_pCore {G : Type*} [Group G] (H : Subgroup G) :
    pCoreOf 2 H = (CFSG.pCore 2 ↥H).map H.subtype := CFSG.openPCoreOf_eq_map_pCore 2 H

theorem isComponentIn_map {G : Type*} [Group G] {H : Subgroup G} {K : Subgroup ↥H}
    (hK : CFSG.IsComponent K) : IsComponentIn (K.map H.subtype) H :=
  ⟨Subgroup.map_subtype_le K, by
    have e : (K.map H.subtype).subgroupOf H = K :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
    rw [e]
    exact hK⟩

theorem charTwo_of_no_component {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hO : oddCoreIn H = ⊥) (hL : ∀ L : Subgroup G, ¬ IsComponentIn L H) : CharTwo H :=
  CFSG.QuasithinUnique.charTwo_of_forall_not_isComponentIn hL hO

section Gw

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem K0_ne_bot (h : Ctx T M g A t d x) : K0 T d x ≠ ⊥ := by
  intro hbot
  have h48 := h.hO.1
  rw [show (oTwoUpper (mcOf T) ⊓ Subgroup.centralizer ({wOfX d x} : Set G)) = ⊥ from hbot,
    Subgroup.card_bot] at h48
  omega

theorem exists_component_Gw (h : Ctx T M g A t d x) (hf : LocalFacts T d x) :
    ∃ L : Subgroup G, IsComponentIn L (Gw d x) := by
  by_contra hno
  have hchar := charTwo_of_no_component (oddCore_Gw h) fun L hL => hno ⟨L, hL⟩
  have hK0P : K0 T d x ≤ pCoreOf 2 (Gw d x) := by
    intro k hk
    refine hchar ⟨hk.2, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
    have hpB : p ∈ Bw T d x := hf.wp1.P_le_Bw hp
    exact ((Subgroup.mem_centralizer_iff.mp hpB.2 k hk)).symm
  apply K0_ne_bot h
  rw [eq_bot_iff, ← hf.wp1.P_inf_K0]
  exact le_inf hK0P le_rfl

end Gw

end InspW2

end S143

end CFSG.Quasithin
