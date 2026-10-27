module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67Trans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67Bot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def FischerStronglyThreeEmbedded : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (H H₀ : Subgroup A) (t : A),
    H₀ ≤ H → CFSG.Open.pRank 3 H ≤ 1 →
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 (H₀.subgroupOf H) →
    (∃ S : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 S H ∧ S ≤ H₀) →
    ¬ H ≤ H₀ ⊔ CFSG.Open.relPPrimeCore 3 H →
    t ∈ H → t ^ 2 = 1 → t ∉ CFSG.Open.relPPrimeCore 3 H →
    ∃ a ∈ H, (t * (a * t * a⁻¹)) ^ 2 ∉ CFSG.Open.relPPrimeCore 3 H ∧
      (t * (a * t * a⁻¹)) ^ 3 ∉ CFSG.Open.relPPrimeCore 3 H

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_67aGap (D : Data G) : Prop :=
  UC6S846.SigmaStd D → D.sig = D.sig1 → UC6.R6_1 D → R1217 D → R129_1 D → R15_9Small D →
    ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
      Sit1665 D V₀ V hV L → V₀ = ⊥ → ∀ g : G, conjSubgroup V g ∈ calO 1 D.M V₀ V →
        Concl1667pre D V₀ V L hV g → ∀ z : G, orderOf z = 2 →
          V ⊓ conjSubgroup D.M g ⊓ (conjSubgroup V g ⊓ D.M) = Subgroup.zpowers z →
            (CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G))).relIndex V ≤ 2

@[expose] def R16_67aNe (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Sit1665 D V₀ V hV L → V₀ ≠ ⊥ → ∀ g : G, conjSubgroup V g ∈ calO 1 D.M V₀ V →
      Concl1667pre D V₀ V L hV g → False

theorem r16_67a_bot (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h61 : UC6.R6_1 D) (h1217 : R1217 D) (h129 : R129_1 D) (h159 : R15_9Small D)
    (hgap : R16_67aGap D) (hKF : FischerStronglyThreeEmbedded)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hs : Sit1665 D V₀ V hV L) (h0 : V₀ = ⊥) {g : G}
    (hg : conjSubgroup V g ∈ calO 1 D.M V₀ V) (hpre : Concl1667pre D V₀ V L hV g) : False := by
  obtain ⟨x, hxM, hxn⟩ := c23_exists_mem_not_nBar D hS.setting.hyp151 hV hs.1.2.2.1
  have hc := s1667_cfg D hSg h1219 h61 h1217 h129 h159 hS hs h0 hxM hxn
  have hg' : InCalO 1 D.M ⊥ V g := inCalO_bot_of_mem_calO hc.normalizer_eq (h0 ▸ hg)
  obtain ⟨z, hz2, hz⟩ := hpre.2.2.1
  have hzV : z ∈ V := by
    have hzm : z ∈ V ⊓ conjSubgroup D.M g ⊓ (conjSubgroup V g ⊓ D.M) := by
      rw [hz]; exact Subgroup.mem_zpowers z
    exact hzm.1.1
  have hnot := hc.not_centralizer_le hg' hz
  have hrank := s1667_pRank_centralizer D hSg h1219 h61 h1217 hS hs h0 hzV hz2 hnot
  have hse := s1667_isStronglyPEmbedded D hSg h1219 h1217 hS hs h0 hzV hnot
  obtain ⟨S, hVS, hSM, hSyl⟩ := s1667_exists_sylow D hSg h61 h129 h159 hS hs hzV
  have hnsup := hc.not_le_sup_relPPrimeCore hg' hz
  have hKV := hgap hSg h1219 h61 h1217 h129 h159 V₀ V L hV hS hs h0 g hg hpre z hz2 hz
  obtain ⟨t, ht, htK⟩ := SetLike.not_le_iff_exists.mp (hc.not_le_relPPrimeCore hg' hz)
  have htH : t ∈ centralizer ({z} : Set G) :=
    hc.le_centralizer_of_eq_zpowers hz (Subgroup.mem_sup_left ht)
  obtain ⟨a, ha, h2, h3⟩ := hKF G (centralizer ({z} : Set G))
    (centralizer ({z} : Set G) ⊓ D.M) t inf_le_left hrank.le hse
    ⟨S, hSyl, le_inf hSyl.le hSM⟩ hnsup htH (hV.2 t ht) htK
  exact (hc.sq_or_cube_mem_relPPrimeCore hg' hz hVS hSM hSyl hKV ht htK ha).elim h2 h3

theorem r16_67a_of_ne (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h61 : UC6.R6_1 D) (h1217 : R1217 D) (h129 : R129_1 D) (h159 : R15_9Small D)
    (hne : R16_67aNe D) (hgap : R16_67aGap D) (hKF : FischerStronglyThreeEmbedded) :
    R16_67a D := by
  intro V₀ V L hV hS hs g hg hpre
  by_cases h0 : V₀ = ⊥
  · exact r16_67a_bot D hSg h1219 h61 h1217 h129 h159 hgap hKF hS hs h0 hg hpre
  · exact hne V₀ V L hV hS hs h0 g hg hpre

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
