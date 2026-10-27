module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67S3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67TI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen68Close

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s1667_cfg (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h61 : UC6.R6_1 D) (h1217 : R1217 D) (h129 : R129_1 D) (h159 : R15_9Small D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hs : Sit1665 D V₀ V hV L) (h0 : V₀ = ⊥) {x : G} (hxM : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V hV L) :
    Cfg1667 D.M V (wSub V₀ V hV L) (conjSubgroup (wSub V₀ V hV L) x) := by
  subst h0
  have hW0 : ⁅E3.wClos V 0 D.T, V⁆ = ⊥ :=
    (sixteen_sixtyThree D hSg h129 h61 h159 ⊥ V L hV hS ⟨Or.inr hs.1, hs.2⟩).1
  refine ⟨hV, s1667_sup_conj_eq D h1217 hS hs.1 hxM hxn,
    s1667_inf_conj_eq D hS hs.1 hxM hxn, ?_, ?_,
    Hyp125.normalizer_eq hS.setting.hyp16.hyp125, ?_, ?_, ?_, ?_⟩
  · rw [s1667_card_wSub D hS hs.1, Subgroup.card_bot, mul_one]
  · rw [E3.card_conjSubgroup (wSub ⊥ V hV L) x, s1667_card_wSub D hS hs.1,
      Subgroup.card_bot, mul_one]
  · intro m hm
    exact s1667_conj_cases D hS hs.1 hxM hxn hm
  · intro F hFV hF
    exact s1667_centralizer_le_of_four_le_card D hSg h61 h1217 hS hs rfl hFV hF
  · intro y hy
    exact s1667_card_inf_conj_le D hSg h1219 h61 h1217 hS hs rfl hy
  · intro y hy
    exact s1668_comm_eq_bot_of_conj_le D hS.setting.hyp16.hyp125 hW0 hy

theorem IsQ8Q8S3.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hA : IsQ8Q8S3 A) : IsQ8Q8S3 B := by
  obtain ⟨N, hN, hE, hS⟩ := hA
  have hN' : (N.map (e : A →* B)).Normal := hN.map (e : A →* B) e.surjective
  haveI : N.Normal := hN
  haveI : (N.map (e : A →* B)).Normal := hN'
  refine ⟨N.map (e : A →* B), hN', ?_, ?_⟩
  · exact isExtraspecialPlus2_of_mulEquiv
      (N.equivMapOfInjective (e : A →* B) e.injective) hE
  · obtain ⟨f⟩ := hS
    exact ⟨(QuotientGroup.congr N (N.map (e : A →* B)) e rfl).symm.trans f⟩

theorem s1667_concl_bot (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h61 : UC6.R6_1 D) (h1217 : R1217 D) (h129 : R129_1 D) (h159 : R15_9Small D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hs : Sit1665 D V₀ V hV L) (h0 : V₀ = ⊥) {g : G} (hg : conjSubgroup V g ∈ calO 1 D.M V₀ V) :
    Concl1667pre D V₀ V L hV g := by
  subst h0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxM, hxn⟩ :=
    c23_exists_mem_not_nBar D hS.setting.hyp151 hV hs.1.2.2.1
  have hcfg : Cfg1667 D.M V (wSub ⊥ V hV L) (conjSubgroup (wSub ⊥ V hV L) x) :=
    s1667_cfg D hSg h1219 h61 h1217 h129 h159 hS hs rfl hxM hxn
  have hg' : InCalO 1 D.M ⊥ V g := inCalO_bot_of_mem_calO hcfg.normalizer_eq hg
  unfold Concl1667pre
  refine ⟨hcfg.not_le_normalizer_W hg', ?_, hcfg.exists_eq_zpowers hg', ?_⟩
  · have hA : conjSubgroup V g ⊓ D.M ≤ normalizer (V : Set G) := by
      rw [hcfg.normalizer_eq]
      exact inf_le_right
    have hcard := s1668_card_barSub_bot (V := V) (A := conjSubgroup V g ⊓ D.M) hV hA
    have hrel := hcfg.relIndex_centralizer_B hg'
    rw [rk, hcard, hrel, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact padicValNat.prime_pow (p := 2) 2
  · have hK : (⊥ ⊔ conjSubgroup ⊥ g).subgroupOf (V ⊔ conjSubgroup V g) = ⊥ := by
      rw [E3.conjSubgroup_bot, bot_sup_eq, Subgroup.bot_subgroupOf]
    rw [hK]
    have hq : (↥(V ⊔ conjSubgroup V g) ⧸
        (⊥ : Subgroup ↥(V ⊔ conjSubgroup V g))) ≃* ↥(V ⊔ conjSubgroup V g) :=
      QuotientGroup.quotientBot
    exact ⟨inferInstance, IsQ8Q8S3.of_mulEquiv hq.symm (hcfg.isQ8Q8S3_X hg')⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
