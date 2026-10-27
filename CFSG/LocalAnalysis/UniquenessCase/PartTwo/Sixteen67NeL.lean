module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67NeK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67NeI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67Fin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_67aNeGap (D : Data G) : Prop :=
  UC6S846.SigmaStd D → D.sig = D.sig1 → R1621 D → UC6.R6_1 D → R1217 D → R129_1 D →
    R15_9Small D → ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
      Sit1665 D V₀ V hV L → V₀ ≠ ⊥ → ∀ g : G, conjSubgroup V g ∈ calO 1 D.M V₀ V →
        Concl1667pre D V₀ V L hV g → ∀ z : G, orderOf z = 2 →
          V ⊓ conjSubgroup D.M g ⊓ (conjSubgroup V g ⊓ D.M) = Subgroup.zpowers z →
            (CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G))).relIndex V ≤ 2

section Certified


theorem r16_67aNe_of_gap (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h61 : UC6.R6_1 D) (h1217 : R1217 D) (h129 : R129_1 D) (h159 : R15_9Small D)
    (hgap : R16_67aNeGap D) (hKF : FischerStronglyThreeEmbedded) : R16_67aNe D := by
  intro V₀ V L hV hS hsit h0 g hg hpre
  obtain ⟨x, hxM, hxn⟩ := c23_exists_mem_not_nBar D hS.setting.hyp151 hV hsit.1.2.2.1
  have hc := s1667ne_cfg D hSg h1219 h21 h61 h1217 h129 h159 hS hsit h0 hxM hxn
  have hg' : InCalO 1 D.M V₀ V g :=
    inCalO_of_mem_calO hc.normalizer_eq hc.le_normalizer₀ hg
  have hs : InCalOStar 1 D.M V₀ V g := hc.inCalOStar hg'
  have hs' : InCalOStar 1 (conjSubgroup D.M g) (conjSubgroup V₀ g)
      (conjSubgroup V g) g⁻¹ := hc.inCalOStar_conj hg'
  have hstar : ∀ y : G, InCalO 1 D.M V₀ V y → InCalOStar 1 D.M V₀ V y ∧
      InCalOStar 1 (conjSubgroup D.M y) (conjSubgroup V₀ y) (conjSubgroup V y) y⁻¹ :=
    fun y hy => ⟨hc.inCalOStar hy, hc.inCalOStar_conj hy⟩
  obtain ⟨z, hz2, hz⟩ := hpre.2.2.1
  have hzV : z ∈ V := by
    have hzm : z ∈ V ⊓ conjSubgroup D.M g ⊓ (conjSubgroup V g ⊓ D.M) := by
      rw [hz]; exact Subgroup.mem_zpowers z
    exact hzm.1.1
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hnot := hc.not_centralizer_le hg' hz
  have hrank := s1667ne_pRank_centralizer D hSg h1219 h21 h61 hS hsit hzV hz2 hnot
  have hse := s1667ne_isStronglyPEmbedded D hSg h1219 h21 hS hsit hzV hz1 hnot
  obtain ⟨S, hVS, hSM, hSyl⟩ := s1667_exists_sylow D hSg h61 h129 h159 hS hsit hzV
  have hnsup := hc.not_le_sup_relPPrimeCore hs hs' hz
  have hKV := hgap hSg h1219 h21 h61 h1217 h129 h159 V₀ V L hV hS hsit h0 g hg hpre
    z hz2 hz
  have hV₀K := hc.V₀_le_relPPrimeCore hs hs' hz hKV
  obtain ⟨t, ht, htK⟩ := SetLike.not_le_iff_exists.mp (hc.not_le_relPPrimeCore hs hs' hz)
  have htH : t ∈ centralizer ({z} : Set G) :=
    hc.le_centralizer_of_eq_zpowers hz (Subgroup.mem_sup_left ht)
  obtain ⟨a, ha, h2, h3⟩ := hKF G (centralizer ({z} : Set G))
    (centralizer ({z} : Set G) ⊓ D.M) t inf_le_left hrank.le hse
    ⟨S, hSyl, le_inf hSyl.le hSM⟩ hnsup htH (hV.2 t ht) htK
  exact (hc.sq_or_cube_mem_relPPrimeCore hstar hz hVS hSM hSyl hKV hV₀K ht htK ha).elim h2 h3

theorem r16_67a_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h61 : UC6.R6_1 D) (h1217 : R1217 D) (h129 : R129_1 D) (h159 : R15_9Small D)
    (hgapNe : R16_67aNeGap D) (hgap : R16_67aGap D) (hKF : FischerStronglyThreeEmbedded) :
    R16_67a D := by
  exact r16_67a_of_ne D hSg h1219 h61 h1217 h129 h159
    (r16_67aNe_of_gap D hSg h1219 h21 h61 h1217 h129 h159 hgapNe hKF) hgap hKF

theorem r16_67_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h61 : UC6.R6_1 D) (h1217 : R1217 D) (h129 : R129_1 D) (h159 : R15_9Small D)
    (hgapNe : R16_67aNeGap D) (hgap : R16_67aGap D) (hKF : FischerStronglyThreeEmbedded) :
    R16_67 D := by
  exact sixteen_sixtySeven D (r16_67_pre_holds D hSg h1219 h21 h61 h1217 h129 h159)
    (r16_67a_holds D hSg h1219 h21 h61 h1217 h129 h159 hgapNe hgap hKF)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
