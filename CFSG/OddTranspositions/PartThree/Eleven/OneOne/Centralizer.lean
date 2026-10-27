module

public import CFSG.OddTranspositions.PartThree.Eleven.GroupLemmas
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Dichotomy
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Involutions
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.TwoCentral

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity


variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem s11z_exists_conj_mem_sylow (S : Sylow 2 G) {M : Subgroup G}
    (hSM : (S : Subgroup G) ≤ M) {x : G} (hxM : x ∈ M) (hx2 : orderOf x = 2) :
    ∃ m ∈ M, m⁻¹ * x * m ∈ (S : Subgroup G) := by
  let x' : M := ⟨x, hxM⟩
  have hP : IsPGroup 2 (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx2]; norm_num)
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (S.subtype hSM) Q
  have hxQ : x' ∈ (Q : Subgroup M) := hQ (Subgroup.mem_zpowers x')
  rw [← hm, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  refine ⟨m, m.2, ?_⟩
  have h2 : (MulAut.conj m)⁻¹ • x' = m⁻¹ * x' * m := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  rw [h2, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hxQ
  exact hxQ

private theorem s11z_mem_Halpha_of_mem_D_commute {hC : HypothesisC D} (h : ElevenOneHyp hC)
    {g : G} (hgD : g ∈ D) (hcomm : Commute g hC.d) : g ∈ Halpha D hC.alpha := by
  by_cases hgd : g = hC.d
  · rw [hgd]
    exact h.d_mem_Halpha
  · rw [h.alpha_eq, Halpha]
    refine Subgroup.subset_closure ⟨{g}, ?_, Set.mem_singleton g⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨c, hc⟩ : ∃ c, c * hC.d * c⁻¹ = g := by
        rw [hC.setup.eq_setOf_isConj hC.hd] at hgD
        exact isConj_iff.mp hgD
      exact mem_blockClass_iff.mpr ⟨c, by rw [Set.image_singleton, hc]⟩
    · rw [Set.singleton_subset_iff]
      exact hgD
    · intro hEq
      exact hgd (by simpa using hEq)
    · intro a ha b hb
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
      exact hcomm.symm

private theorem s11z_notMem_of_mem_Halpha {hC : HypothesisC D} {h : ElevenOneHyp hC} {y a : G}
    (hyC : y ∈ Subgroup.centralizer {hC.d}) (hyH : y ∉ Halpha D hC.alpha)
    (hy2 : orderOf y = 2) (haH : a⁻¹ * y * a ∈ Halpha D hC.alpha) : False := by
  obtain ⟨hyNotD, hyNotProd⟩ := h.not_mem_of_not_mem_Halpha hyC hyH hy2
  have ha2 : orderOf (a⁻¹ * y * a) = 2 := by
    have hsem : SemiconjBy a⁻¹ y (a⁻¹ * y * a) := by
      show a⁻¹ * y = (a⁻¹ * y * a) * a⁻¹
      group
    rw [← SemiconjBy.orderOf_eq a⁻¹ hsem]
    exact hy2
  rcases h.involution_mem haH ha2 with haD | ⟨p, hpD, q, hqD, hpq, hcomm, hpqeq⟩
  · apply hyNotD
    have hconj : a * (a⁻¹ * y * a) * a⁻¹ ∈ D := hC.setup.conj_mem a haD
    rwa [show a * (a⁻¹ * y * a) * a⁻¹ = y by group] at hconj
  · apply hyNotProd
    refine ⟨a * p * a⁻¹, hC.setup.conj_mem a hpD, a * q * a⁻¹, hC.setup.conj_mem a hqD,
      ?_, hcomm.conj a, ?_⟩
    · intro heq
      exact hpq (by
        have := congrArg (fun z => a⁻¹ * z * a) heq
        simpa using this)
    · calc y = a * (a⁻¹ * y * a) * a⁻¹ := by group
        _ = a * (p * q) * a⁻¹ := by rw [hpqeq]
        _ = (a * p * a⁻¹) * (a * q * a⁻¹) := by group

theorem ElevenOneHyp.centralizer_eq {hC : HypothesisC D} (h : ElevenOneHyp hC) :
    Subgroup.centralizer {hC.d} = Halpha D hC.alpha := by
  have hHC : Halpha D hC.alpha ≤ Subgroup.centralizer {hC.d} := by
    rw [Halpha, Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hC.DalphaStar_subset_commute hx).2
  refine le_antisymm ?_ hHC
  rcases h.centralizer_le_or_index_two with hCH | ⟨hidx, x, hxC, hxH, hx2⟩
  · exact hCH
  · exfalso
    haveI hHn : ((Halpha D hC.alpha).subgroupOf
        (Subgroup.centralizer {hC.d})).Normal :=
      Subgroup.normal_of_index_eq_two hidx
    have hHnormC : ∀ h k, h ∈ Halpha D hC.alpha → k ∈ Subgroup.centralizer {hC.d} →
        k * h * k⁻¹ ∈ Halpha D hC.alpha :=
      (Subgroup.normal_subgroupOf_iff hHC).mp hHn
    obtain ⟨S, hSC⟩ := h.exists_sylow_le_centralizer
    obtain ⟨c, hcC, hcyS⟩ := s11z_exists_conj_mem_sylow S hSC hxC hx2
    set y : G := c⁻¹ * x * c with hy_def
    have hyS : y ∈ (S : Subgroup G) := by rw [hy_def]; exact hcyS
    have hyC : y ∈ Subgroup.centralizer {hC.d} := hSC hyS
    have hcyc : c * y * c⁻¹ = x := by rw [hy_def]; group
    have hyH : y ∉ Halpha D hC.alpha := by
      intro hyHmem
      exact hxH (by rw [← hcyc]; exact hHnormC y c hyHmem hcC)
    have hy2 : orderOf y = 2 := by
      have hsem : SemiconjBy c⁻¹ x y := by
        show c⁻¹ * x = y * c⁻¹
        rw [hy_def]
        group
      rw [← SemiconjBy.orderOf_eq c⁻¹ hsem]
      exact hx2
    have hy_inv : y * y = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy2, pow_two] at this
    set Q : Subgroup G := (S : Subgroup G) ⊓ Halpha D hC.alpha with hQdef
    have hQS : Q ≤ (S : Subgroup G) := by rw [hQdef]; exact inf_le_left
    have hQle : Q.relIndex (S : Subgroup G) ≤ 2 := by
      have hle : (Halpha D hC.alpha).relIndex (S : Subgroup G) ≤ 2 := by
        have hlt := Subgroup.relIndex_le_of_le_right (H := Halpha D hC.alpha)
          (K := (S : Subgroup G)) (L := Subgroup.centralizer {hC.d}) hSC
          (by rw [hidx]; norm_num)
        rwa [hidx] at hlt
      calc Q.relIndex (S : Subgroup G)
          = ((S : Subgroup G) ⊓ Halpha D hC.alpha).relIndex (S : Subgroup G) := by
              rw [hQdef]
        _ = (Halpha D hC.alpha).relIndex (S : Subgroup G) := by
              rw [Subgroup.inf_relIndex_left]
        _ ≤ 2 := hle
    have hQne1 : Q.relIndex (S : Subgroup G) ≠ 1 := by
      intro h1
      have hSleQ : (S : Subgroup G) ≤ Q := (Subgroup.relIndex_eq_one).mp h1
      have hyQ : y ∈ Q := hSleQ hyS
      rw [hQdef] at hyQ
      exact hyH hyQ.2
    have hQne0 : Q.relIndex (S : Subgroup G) ≠ 0 := by
      have hlt : (Q.subgroupOf (S : Subgroup G)).index ≠ 0 :=
        Subgroup.index_ne_zero_of_finite
      exact hlt
    have hindex : Q.relIndex (S : Subgroup G) = 2 := by omega
    have hSD : ∀ g ∈ (S : Subgroup G), IsConj hC.d g → g ∈ Q := by
      intro g hgS hconj
      refine ⟨hgS, s11z_mem_Halpha_of_mem_D_commute h ?_ ?_⟩
      · rw [hC.setup.eq_setOf_isConj hC.hd]
        exact hconj
      · exact Subgroup.mem_centralizer_singleton_iff.mp (hSC hgS)
    have hQnot : ∀ a : G, a⁻¹ * y * a ∉ Q := by
      intro a ha
      exact s11z_notMem_of_mem_Halpha (h := h) hyC hyH hy2 ha.2
    have hd2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
    have hgen : Subgroup.closure {g : G | IsConj hC.d g} = ⊤ := by
      rw [← hC.setup.eq_setOf_isConj hC.hd, hC.setup.gen]
    exact false_of_transfer hC.d hd2 hgen S hQS hindex hSD hy_inv hyS hQnot

end CFSG.OddTranspositions.PartThree
