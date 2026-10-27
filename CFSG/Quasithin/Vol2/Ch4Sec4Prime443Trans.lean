module

public import CFSG.Quasithin.Vol2.Ch4Sec4L443E17Trans
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PrimeDefs
public import CFSG.Quasithin.Vol2.Ch4Sec4HypPrime
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E10Sub
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E13Eq
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E15FF
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E16Shape

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L B Tp VB : Subgroup G}

theorem concl_or_J4' (s : Setting443 G T M L B Tp VB) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) {K : Subgroup G} (hVK : VB ≤ K)
    (h : Concl443B' G T M L K (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)))
      VB) :
    Concl4_4_3' G T M L B VB ∨
      (IsSporadic .J4 ↥K ∧
        (IsSporadic .M24 (↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) ⧸
            CFSG.pCore 2 ↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)))) ∨
          LieModel (↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) ⧸
            CFSG.pCore 2 ↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))))
            .PSL 5 2 1)) := by
  set LB := perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) with hLB
  rcases h with ⟨hq, hshape, hcase⟩ | hJ
  swap
  · exact Or.inr hJ
  refine Or.inl (Or.inr ⟨le_normalizer_of_quasisimple s h37 h38 h39 hq, ?_⟩)
  have hML : conjClosure L T = L := conjClosure_eq_of_quasisimple s h37 h39 hq
  have hLBL : LB ≤ L := (LB_le L T B).trans hML.le
  have h445 : conjClosure L T = LB ⊔ pCoreOf 2 (conjClosure L T) :=
    lemma_4_4_5_orbit s.hyp.toHyp4_4_1TwoOrbit
  have hY : L = LB ⊔ pCoreOf 2 L := by
    calc L = conjClosure L T := hML.symm
      _ = LB ⊔ pCoreOf 2 (conjClosure L T) := h445
      _ = LB ⊔ pCoreOf 2 L := by rw [hML]
  have hQ : pCoreOf 2 LB ≤ pCoreOf 2 L := (pCoreOf_LB_le s).trans (congrArg (pCoreOf 2) hML).le
  have hQV : pCoreOf 2 L ≤ Subgroup.centralizer (VB : Set G) := by
    have := VB_le_centralizer_pCoreOf_Mp s
    rwa [hML] at this
  have hLBN : LB ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hLBL.trans (le_normalizer_pCoreOf 2 L)
  have hLBV : LB ≤ Subgroup.normalizer (VB : Set G) :=
    (LB_le L T B).trans (le_sup_left.trans s.hyp.VB_normalized)
  have hAut : autOn L VB = autOn LB VB :=
    (congrArg (autOn · VB) hY).trans (autOn_sup_eq hLBN hQV hLBV)
  have hNat : ∀ n : ℕ, IsNaturalSumUnder n LB VB → IsNaturalSumUnder n L VB := fun n hn => by
    rw [hY]
    exact isNaturalSumUnder_sup hLBN hQV hn
  obtain ⟨e⟩ := nonempty_quotEquiv hLBL hY hQ
  refine ⟨shape443_of_mulEquiv e hshape, ?_⟩
  rcases hcase with ⟨⟨hc, hFF⟩, hI2, hI3, hI4, hI5⟩ | ⟨m, hm, hm2, hc, hO⟩ | ⟨h3, hc, hF⟩
  · refine Or.inl ⟨⟨hc, ?_⟩, fun h3 => hNat 3 (hI2 (lieModel_of_mulEquiv' e h3)), fun h4 => ?_,
      fun h6 hcard z hz hz2 hVz => ?_, fun hU h64 => ?_⟩
    · have hTH : T ≤ M ⊓ Subgroup.normalizer (VB : Set G) :=
        le_inf s.hyp.T_le (le_sup_right.trans s.hyp.VB_normalized)
      exact isFFModule_of_le (autOn_mono' le_sup_right) (isFFModule_of_isSylowTwoOf
        (isSylowTwoOf_autOn inf_le_right (isSylowTwoOf_of_le s.hyp.sylow hTH)) hFF)
    · rcases hI3 (lieModel_of_mulEquiv' e h4) with h | ⟨hc', hS⟩
      · exact Or.inl (hNat 4 h)
      · exact Or.inr ⟨hc', by rw [hAut]; exact hS⟩
    · refine hI4 (threeA6_of_mulEquiv e.symm h6) hcard z (by rw [hML]; exact hz) hz2 ?_
      have h1 := pCoreOf_inf_le (Subgroup.centralizer ({z} : Set G)) K
      rw [inf_comm (Subgroup.centralizer ({z} : Set G))] at h1
      exact (le_inf hVz hVK).trans h1
    · obtain ⟨V₃, h1, h2, h3, h4⟩ := hI5 (lieModel_of_mulEquiv' e hU) h64
      exact ⟨V₃, h1, h2, by rw [← hML]; exact h3, fun hC => h4 (inf_le_right.trans hC)⟩
  · exact Or.inr (Or.inl ⟨m, hm, lieModel_of_mulEquiv' e.symm hm2, hc, by rw [hAut]; exact hO⟩)
  · exact Or.inr (Or.inr ⟨lieModel_of_mulEquiv' e.symm h3, hc, by rw [hAut]; exact hF⟩)

end CFSG.Quasithin.H13.Ch4.E443
