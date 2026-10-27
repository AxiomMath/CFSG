module

public import CFSG.Quasithin.EmptyFaithful.A38c13S1469B
public import CFSG.Quasithin.EmptyFaithful.S1469Eight
public import CFSG.Quasithin.EmptyFaithful.S1469CaseA4

public section

namespace CFSG.Quasithin

section CaseB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.QuasithinUnique.Ch1

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.caseB_falseNoN (hE22 : E2.E22StatementNoN) (hlist : Lemma115_3_List)
    (i8 : Input1469B1NoN) (i9 : Input1469B2NoN) (h1 : Stage1463One) (h2 : Stage1463Two)
    (h4 : Stage1463Four) {H : Subgroup G} {u : G} {I : Subgroup G} (c : Ctx1469 T M H u I)
    (hchar : ¬ CharTwo I) : False := by
  have S := c.setting
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.hyp1281.omegaOneCenter_ne_bot
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hidx := (h1 G T M S H c.hH u c.hu).2.1
  have hN0 := h2 G T M S H c.hH u c.hu
  have hNu := (h4 G T M S H c.hH u c.hu).1
  obtain ⟨hsyl, -⟩ := isIStar_sylow_cases S c.hu hidx hN0 hNu c.hI.1
  have hSQ : IsSQTKTC I := S.isSQTKTC_of_pCoreOf_ne_bot c.hI.1.1.1.2
  have hO := S.oddCoreIn_eq_bot c.hH c.hu c.hI.1 hsyl hzZ hz1'
  obtain ⟨K₀, hK₀⟩ := exists_isComponentIn_of_not_charTwo hO hchar
  have hnonsolv : ¬ Group.IsSolvable ↥I := by
    intro hsolv
    have hper : Group.IsPerfect K₀ := isPerfect_of_isComponentIn hK₀
    have hne : K₀ ≠ ⊥ := ne_bot_of_isComponentIn hK₀
    have hsolvK : Group.IsSolvable ↥K₀ :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hK₀.1)
        (Subgroup.inclusion_injective hK₀.1)
    have : Nontrivial ↥K₀ := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable ↥K₀ hsolvK
  have h115 := S.lemma115Hyp_of_isIStar c.hH c.hu c.hI.1 hsyl hzZ hz1'
  have hsimple : IsSimpleGroup G := S.hyp1281.simple
  have hqtke : QTKECore G := qtkeCore_of_cat S.hyp1281.nonabelian S.hyp1281.qtke
  have hcomp : ∀ L : Subgroup G, IsComponentIn L I →
      ⁅L, Subgroup.zpowers z⁆ = L ∧ Lemma115Cases L z := fun L hL =>
    let h := hlist.component_cases S.hyp1281.simple S.hyp1281.nonabelian hqtke h115 hL
    ⟨h.2.1, h.2.2.2⟩
  have hE := (hE22 G I (T ⊓ I) (I ⊓ mcOf T) c.minPar (⟨hSQ.2, hSQ.1⟩ : SQTKGroup ↥I) hnonsolv).1
  have hzT : z ∈ T := S146T.Z_le hzZ
  have huQ : u ∈ pCoreOf 2 (mcOf T) := S.conjClosure_le_pCoreOf_mcOf c.hH c.hu.mem
  have hQ1T : pCoreOf 2 (mcOf T) ≤ T := S.pCoreOf_mcOf_le
  have hzu : z ∈ tU T u := (S146T.mem_tU_iff).mpr ⟨hzT,
    commutatorElement_eq_one_iff_mul_comm.mpr (S146T.comm_Z_T (hQ1T huQ) hzZ).symm⟩
  have hzI : z ∈ I := c.hI.1.1.1.1 hzu
  have hzS : z ∈ quasithinOmegaOneCenter (T ⊓ I) :=
    (mem_quasithinOmegaOneCenter_iff).mpr ⟨⟨hzT, hzI⟩,
      Subgroup.mem_centralizer_iff.mpr fun g hg => S146T.comm_Z_T hg.1 hzZ, S146T.Z_sq hzZ⟩
  have hIz : I ⊓ mcOf T = I ⊓ Subgroup.centralizer ({z} : Set G) := by
    rw [S.mcOf_eq_centralizer hzZ hz1']
  obtain ⟨K, hKc, hIK, hKq, hKE, hShape⟩ :=
    i8 G I (T ⊓ I) (I ⊓ mcOf T) z hSQ hchar c.minPar hzS hz1' hIz ⟨K₀, hK₀⟩ hcomp hE
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two c.hH
  have hUT : conjClosure (VZ T M) H ≤ T :=
    (S.conjClosure_le_pCoreOf c.hH).trans (S.pCoreOf_le_T c.hH)
  have hUu : conjClosure (VZ T M) H ≤ T ⊓ I := by
    intro a ha
    have hcomm : u * a = a * u :=
      congrArg Subtype.val (hUab.1.is_comm.comm (⟨u, c.hu.mem⟩ : conjClosure (VZ T M) H) ⟨a, ha⟩)
    refine ⟨hUT ha, c.hI.1.1.1.1 ((S146T.mem_tU_iff).mpr ⟨hUT ha,
      commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm⟩)⟩
  have hTH : T ≤ H := c.hH.1.1
  have hnorm : T ⊓ I ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    inf_le_left.trans (hTH.trans (le_normalizer_conjClosure _ _))
  have hrank : 4 ≤ mIdx (conjClosure (VZ T M) H) (pCoreOf 2 I) :=
    c.hrank.trans (S.lemma_14_6_8 c.hH c.hu c.hI.1 hsyl hchar)
  exact i9 G I (T ⊓ I) (I ⊓ mcOf T) K hSQ hchar c.minPar hKc hIK hKq hKE hShape
    (conjClosure (VZ T M) H) hUu hnorm hUab hrank

end CaseB

section Top

open CFSG.Open CFSG.QuasithinUnique

theorem main1469_of_named_inputsNoN (hE22 : E2.E22StatementNoN) (hlist : Lemma115_3_List)
    (i1 : Input1469C126) (i2 : Input1469Lin2) (i3 : Input1469C61) (i4 : Input1469A5J)
    (i5 : Input1469A5C567) (i6a : Input1469A5DOne) (i6b : Input1469A5DTwo)
    (i7 : Input1469A5Fin) (i8 : Input1469B1NoN) (i9 : Input1469B2NoN)
    (h1 : Stage1463One) (h2 : Stage1463Two) (h4 : Stage1463Four) (h5 : Stage1461Five) :
    Main1469 := by
  intro G _ _ T M H u I c
  by_cases hchar : CharTwo I
  · exact Setting146.caseA_false i1 i2 i3 i4 i5 i6a i6b i7 h1 h2 h4 h5 c hchar
  · exact Setting146.caseB_falseNoN hE22 hlist i8 i9 h1 h2 h4 c hchar

end Top

end CFSG.Quasithin
