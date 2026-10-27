module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.PlusModel
public import CFSG.OddTranspositions.PartThree.Eleven.FivePlusModel
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Centralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity



private theorem s11m_odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
    unfold CFSG.oddCore CFSG.pPrimeCore
    simp_rw [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem theorem11_1_holds (hW : WongPSp4Five) : Theorem11_1 := by
  intro G _ _ D hC hrad hZ hmod
  obtain ⟨π, hmod⟩ := hmod
  have h : ElevenOneHyp hC := ⟨hrad, hZ, o4PlusFacts_of_isFiveReflectionModel hmod⟩
  obtain ⟨A, B, hAB⟩ := h.facts.factors
  obtain ⟨hcommAB, hsupAB, hinfM, hidx, hswap, -⟩ := h.derived hAB
  have hu : orderOf hC.d = 2 := hC.setup.oddT.1 hC.d hC.hd
  have hu2 : hC.d * hC.d = 1 := by
    have hh := pow_orderOf_eq_one hC.d
    rw [hu] at hh
    simpa [pow_two] using hh
  have huinv : hC.d⁻¹ = hC.d := inv_eq_of_mul_eq_one_left hu2
  have hMne : Malpha D hC.alpha ≠ ⊥ := by
    rw [h.Malpha_eq, Ne, Subgroup.zpowers_eq_bot]
    intro h1
    rw [h1] at hu
    norm_num at hu
  have hmap_top : Subgroup.map (Halpha D hC.alpha).subtype ⊤ = Halpha D hC.alpha := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hrel : (liftH hC A ⊔ liftH hC B).relIndex (Subgroup.centralizer {hC.d}) = 2 := by
    rw [h.centralizer_eq, hsupAB]
    have hrf := Subgroup.relIndex_map_map_of_injective
      (f := (Halpha D hC.alpha).subtype)
      (commutator (Halpha D hC.alpha)) ⊤ Subtype.coe_injective
    rw [hmap_top] at hrf
    rw [hrf, Subgroup.relIndex_top_right]
    exact hidx
  have htop : Subgroup.centralizer {hC.d} ⊔ CFSG.oddCore G ≠ ⊤ := by
    intro hsup'
    obtain ⟨v, hv⟩ := DstarH_nonempty hC
    have hvDstar : (v : G) ∈ DalphaStar D hC.alpha := (mem_DstarH_iff hC).mp hv
    have hvD : (v : G) ∈ D := DalphaStar_subset hC.isBlock_alpha hvDstar
    have hv2 : orderOf (v : G) = 2 := hC.setup.oddT.1 (v : G) hvD
    have hv2sq : (v : G) * (v : G) = 1 := by
      have hh := pow_orderOf_eq_one (v : G)
      rw [hv2] at hh
      simpa [pow_two] using hh
    have hcommv : Commute hC.d (v : G) := (hC.DalphaStar_subset_commute hvDstar).2.symm
    have hne : hC.d ≠ (v : G) := by
      have hvE : (v : G) ∈ hC.E := by
        rw [← hC.DalphaStar_alpha]
        exact hvDstar
      have hnotE : hC.d ∉ hC.E := by
        have hh := hC.d_mem_alpha
        rw [hC.alpha_eq_normSet_diff] at hh
        exact hh.2
      exact fun heq => hnotE (heq ▸ hvE)
    obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hvD)
    have hgmem : g ∈ CFSG.oddCore G ⊔ Subgroup.centralizer {hC.d} := by
      rw [sup_comm, hsup']
      exact Subgroup.mem_top g
    obtain ⟨o, ho, c, hc, hoc⟩ := Subgroup.mem_sup_of_normal_left.mp hgmem
    have hcu : c * hC.d * c⁻¹ = hC.d := by
      have hh := ((Subgroup.mem_centralizer_iff.mp hc) hC.d (Set.mem_singleton hC.d)).symm
      rw [hh]
      group
    have hvo : (v : G) = o * hC.d * o⁻¹ := by
      calc (v : G) = g * hC.d * g⁻¹ := hg.symm
        _ = (o * c) * hC.d * (o * c)⁻¹ := by rw [← hoc]
        _ = o * (c * hC.d * c⁻¹) * o⁻¹ := by group
        _ = o * hC.d * o⁻¹ := by rw [hcu]
    have huv : hC.d * (v : G) = (hC.d * o * hC.d⁻¹) * o⁻¹ := by
      rw [hvo, huinv]
      group
    have hO : hC.d * (v : G) ∈ CFSG.oddCore G := by
      rw [huv]
      exact (CFSG.oddCore G).mul_mem
        ((inferInstance : (CFSG.oddCore G).Normal).conj_mem o ho hC.d)
        ((CFSG.oddCore G).inv_mem ho)
    have hu_sq : hC.d ^ 2 = 1 := by rw [pow_two, hu2]
    have hv_sq : (v : G) ^ 2 = 1 := by rw [pow_two, hv2sq]
    have huv_sq : (hC.d * (v : G)) ^ 2 = 1 := by
      rw [hcommv.mul_pow, hu_sq, hv_sq, one_mul]
    have huv_ne : hC.d * (v : G) ≠ 1 := by
      intro h1
      exact mul_notMem_of_orderOf_eq_two hu hv2 hne (by simp [h1])
    have huv_order : orderOf (hC.d * (v : G)) = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime huv_sq huv_ne
    have hdvd : orderOf (hC.d * (v : G)) ∣ Nat.card (CFSG.oddCore G) := by
      have hh := orderOf_dvd_natCard (⟨hC.d * (v : G), hO⟩ : CFSG.oddCore G)
      rwa [← Subgroup.orderOf_coe] at hh
    have h2dvd : 2 ∣ Nat.card (CFSG.oddCore G) := by
      rw [← huv_order]
      exact hdvd
    exact (Nat.not_even_iff_odd.mpr (s11m_odd_card_oddCore G)) (even_iff_two_dvd.mpr h2dvd)
  obtain ⟨hL1e, hL2e⟩ := h.liftH_equiv hAB hMne
  have hinf : liftH hC A ⊓ liftH hC B = Subgroup.zpowers hC.d := hinfM.trans h.Malpha_eq
  rcases hW G hC.d (liftH hC A) (liftH hC B) hu hL1e hL2e hcommAB hinf hrel htop with
    hP | hPSp
  · exfalso
    obtain ⟨r, hr⟩ := DstarH_nonempty hC
    have hrDstar : (r : G) ∈ DalphaStar D hC.alpha := (mem_DstarH_iff hC).mp hr
    have hrC : (r : G) ∈ Subgroup.centralizer {hC.d} := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (hC.DalphaStar_subset_commute hrDstar).2.symm
    have hfix : (liftH hC A).map (MulAut.conj (r : G)).toMonoidHom = liftH hC A :=
      (hP.2 (r : G) hrC).1
    have hsw := hswap (r : G) hrDstar
    have hL1L2 : liftH hC A = liftH hC B := hfix.symm.trans hsw
    have hLM : liftH hC A = Malpha D hC.alpha := by
      rw [← hinfM, hL1L2, inf_idem]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨e⟩ := hL1e
    have hcard120 : Nat.card (liftH hC A) = 120 := by
      rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field]
      norm_num
    have hcard2 : Nat.card (liftH hC A) = 2 := by
      rw [hLM, h.Malpha_eq, Nat.card_zpowers, hu]
    omega
  · have hMcard : Nat.card (Malpha D hC.alpha) = 2 := by
      rw [h.Malpha_eq, Nat.card_zpowers, hu]
    have hsolvcard : Nat.card (CFSG.solvableRadical (Halpha D hC.alpha)) = 2 := by
      have hmap := Subgroup.card_map_of_injective
        (K := CFSG.solvableRadical (Halpha D hC.alpha))
        (f := (Halpha D hC.alpha).subtype) Subtype.coe_injective
      rw [← hmap]
      exact hMcard
    have hHcard : Nat.card (Halpha D hC.alpha) = 14400 := by
      have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (CFSG.solvableRadical (Halpha D hC.alpha))
      rw [h.facts.card, hsolvcard] at hq
      norm_num at hq
      exact hq
    have h64 : 64 ∣ Nat.card (Subgroup.centralizer {hC.d}) := by
      rw [h.centralizer_eq, hHcard]
      norm_num
    rw [hC.setup.eq_setOf_isConj hC.hd]
    exact isFiveReflectionModel_four_true_true_of_psp hC.d hu hPSp h64

end CFSG.OddTranspositions.PartThree
