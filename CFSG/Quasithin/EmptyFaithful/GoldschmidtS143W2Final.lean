module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2A8Fin
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2L34
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2U34
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Sz8
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2L33
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2M12
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2LocJ
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2PcD
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompX
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompO

public section

namespace CFSG.Quasithin

namespace S143

namespace InspW2

theorem hG24_of_certs
    : ∀ (X : Type) [Group X], CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 2 →
      2 ^ 9 ∣ Nat.card X := by
  intro X _ hG
  rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hG]
  exact (pow_dvd_pow 2 (by norm_num : 9 ≤ 6 * 2)).trans Insp7.two_pow_dvd_ordG2

theorem inspW_all
    : InspW :=
  inspW_cards_a8 resW_l34 resW_u34 resW_sz8 resW_l33 resW_m12

theorem inspWiw_all
    : InspWiw :=
  inspWi_weak inspW_all.1 (fun _ hs => Insp7.card_carrier_big hs) hG24_of_certs
    (fun _ hs => Insp7.isSimpleGroup_carrier_small hs) resW_l34 resW_m12 numFactW_sporNoM12

theorem lemma14322InspectW2_of_checks
    (hloc : LocalFactsHold) (hcomp : ComponentAnalysis) (h4 : Clause4) :
    Lemma14322InspectW2 :=
  lemma14322InspectW2_of_parts hloc hcomp inspWo inspWiw_all h4

theorem localFactsHold_all : LocalFactsHold := fun _ _ _ _ _ _ _ _ _ _ h =>
  ⟨wp0_of_ctx h, wp1_of_wp0 h (wp0_of_ctx h)⟩

theorem componentAnalysis_all (hlist : CFSG.QuasithinUnique.Lemma115_3_List) : ComponentAnalysis :=
  fun _ _ _ _ _ _ _ _ _ _ h hf => by
    obtain ⟨L, hL⟩ := exists_component_Gw h hf
    exact ⟨L, hL, inspData_of_normal hlist h hf hL (normalizer_of_component h hf hL)⟩

theorem lemma14322InspectW2_of_clause4
    (hlist : CFSG.QuasithinUnique.Lemma115_3_List) (h4 : Clause4) : Lemma14322InspectW2 :=
  lemma14322InspectW2_of_checks localFactsHold_all (componentAnalysis_all hlist) h4

end InspW2

end S143

end CFSG.Quasithin
