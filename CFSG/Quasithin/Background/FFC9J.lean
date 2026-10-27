module

public import CFSG.Quasithin.Background.FFC9D
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.FFC9I
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.B5CompB

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

section Fit

variable {V : Type} [CommGroup V] [Finite V]

theorem nilpotent_le_of_pCoreOf {G N C : Subgroup (MulAut V)} (hNG : N ≤ G)
    (hn : (N.subgroupOf G).Normal) (hnil : Group.IsNilpotent ↥N)
    (hC : ∀ p : ℕ, p.Prime → pCoreOf p G ≤ C) : N ≤ C := by
  have hnilF : Group.IsNilpotent ↥(N.subgroupOf G) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hNG)).2 hnil
  have h1 := CFSG.normal_nilpotent_le_sup_pCore hn hnilF
  have h2 := Subgroup.map_mono (f := G.subtype) h1
  rw [Subgroup.map_subgroupOf_eq_of_le hNG, Subgroup.map_iSup] at h2
  refine h2.trans (iSup_le fun p => ?_)
  have hp : p.1.1.Prime := Nat.prime_of_mem_primeFactors p.1.2
  refine le_trans (le_of_eq ?_) (hC _ hp)
  rw [pCoreOf]

theorem genFitting_eq_of_layer (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hJ : G = ffJ G)
    (hO2 : pCoreOf 2 G = ⊥) (hO3 : pCoreOf 3 G ≤ centerOf G) (hL : CFSG.Open.IsComponentOf L G)
    (hlayer : ∀ K : Subgroup (MulAut V), CFSG.Open.IsComponentOf K G → K = L) :
    quasithinGenFitting G = L ⊔ centerOf G := by
  have hC : ∀ p : ℕ, p.Prime → pCoreOf p G ≤ centerOf G := by
    intro p hp
    by_cases h2 : p = 2
    · subst h2
      rw [hO2]
      exact bot_le
    by_cases h3 : p = 3
    · subst h3
      exact hO3
    · have : Fact p.Prime := ⟨hp⟩
      exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le p G) (B55.pCoreOf_le_centralizer hV hJ h2 h3)
  apply le_antisymm
  · unfold quasithinGenFitting
    refine sup_le ?_ ?_
    · refine sSup_le fun N hN => ?_
      obtain ⟨hNG, hNn, hnil⟩ := hN
      exact (nilpotent_le_of_pCoreOf hNG hNn hnil hC).trans le_sup_right
    · refine sSup_le fun K hK => ?_
      rw [hlayer K hK]
      exact le_sup_left
  · refine sup_le ?_ (centerOf_le_genFitting G)
    unfold quasithinGenFitting
    exact le_sup_of_le_right (le_sSup hL)

theorem case1_of_layer (hB51 : AsB51) (hA21 : AsA21SQTKSection) {G L : Subgroup (MulAut V)}
    (hc : B56Counterex G) (hL : CFSG.Open.IsComponentOf L G) (hO3 : pCoreOf 3 G ≤ centerOf G)
    (hlayer : ∀ K : Subgroup (MulAut V), CFSG.Open.IsComponentOf K G → K = L) : B56Case1 G := by
  have hFit := genFitting_eq_of_layer hc.hV hc.hyp.2.1 hc.hyp.1 hO3 hL hlayer
  have hLq : CFSG.IsQuasisimple ↥L := B1Red.isQuasisimple_of_open hL.2.2
  have hq := isQuotientOfSQTKTauCeti_of_b53 hc.hyp
  have hSQ : SQTKGroup ↥L := sqtk_of_le hA21 hq hL.1 hLq
  have hyp : B51Hyp G L := ⟨hFit, hLq, hSQ, hL.1, hc.hyp.1, hc.hyp.2.1⟩
  have hconc := hB51 V hc.hV G L hyp
  have hF : quasithinGenFitting G = L := hconc.1.1
  have hlist := b56List_of_b51 hconc
  rw [← hF] at hLq hconc hlist
  exact ⟨hLq, hconc, hlist⟩

end Fit

theorem b57Input_of_exc (hB51 : AsB51) (hA21 : AsA21SQTKSection) (hLay : B57Layer) (hExc : B57Exc) :
    B57Input := by
  intro V _ _ G hc L hL h3
  by_cases hO3 : pCoreOf 3 G ≤ centerOf G
  · exact hc.not_cases (Or.inl (case1_of_layer hB51 hA21 hc hL hO3 (hLay V G hc L hL h3)))
  · exact hc.not_cases (Or.inr (Or.inr (Or.inr (Or.inl
      (hExc V G hc L hL h3 (hLay V G hc L hL h3) hO3)))))

theorem b57Input_of (hP4 : AsB15Part4) (hB51 : AsB51)
    (hA21 : AsA21SQTKSection) (hExc : B57Exc) : B57Input :=
  b57Input_of_exc hB51 hA21 (b57Layer_of hP4 hB51 hA21) hExc

theorem asB56_of_exc_b59
    (hP4 : AsB15Part4) (hB51 : AsB51) (hB42 : AsB42)
    (hA21 : AsA21SQTKSection) (hExc : B57Exc) (hLast : B59Last) (hI16 : AsI16Cover) :
    AsB56 :=
  asB56_of_quoted_inputs hP4 hB51 hB42 hA21 (b57Input_of hP4 hB51 hA21 hExc) hLast hI16
      b510SumNat_of

end FFC

end CFSG.Quasithin
