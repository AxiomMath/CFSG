module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaMinus
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitaryAux
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeFixedIndex
import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeFixedSylow

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open FrameRoute

variable {G : Type} [Group G] [Finite G]

theorem GGSecFiveRestHyp.card_bstar_of_twD5
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 5 ∧ lab.n = 1)) :
    Nat.card Bs = 3 ^ 6 := by
  have hsup : Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L) :=
    (GGSecFiveRestHyp.bstar_eq_sup_of_twD5 hR hlab).2
  have hcard_inf : Nat.card ↥(Bs ⊓ L) = 3 ^ 5 :=
    GGSecFiveRestHyp.card_bstar_inf_of_twD5 hR hlab
  have hS : LargeEvenSStar 3 B x L := hR.1.1.2.2.2.2.2.2.1
  obtain ⟨-, hBs, hxB, -, -⟩ := hR.1.tableB_facts
  have horderx : orderOf x = 3 := orderOf_eq_prime (hBs.2 x hxB) hS.2.2.1
  have hcard_zp : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, horderx]
  have hzp_le_bs : Subgroup.zpowers x ≤ Bs := Subgroup.zpowers_le.mpr hxB
  have hinf_bot_L : Subgroup.zpowers x ⊓ L = ⊥ := by
    apply Subgroup.eq_bot_of_card_le
    have h_card_inter : Nat.card ↥(Subgroup.zpowers x ⊓ L) ≤ Nat.card ↥(Subgroup.zpowers x) :=
      Subgroup.card_le_of_le inf_le_left
    rw [hcard_zp] at h_card_inter
    have hx_notin_L : x ∉ L := (GGSecFiveRestHyp.bstar_eq_sup_of_twD5 hR hlab).1
    have h_ne_3 : Nat.card ↥(Subgroup.zpowers x ⊓ L) ≠ 3 := by
      intro h3
      have h_le_zp : Subgroup.zpowers x ⊓ L = Subgroup.zpowers x := by
        apply Subgroup.eq_of_le_of_card_ge _ _
        · exact inf_le_left
        · rw [h3, hcard_zp]
      have hx_in_L : x ∈ L := by
        have hx_in_zp : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
        have hx_in_inf : x ∈ Subgroup.zpowers x ⊓ L := by
          rw [h_le_zp]
          exact hx_in_zp
        exact (Subgroup.mem_inf.mp hx_in_inf).2
      exact hx_notin_L hx_in_L
    have h_dvd : Nat.card ↥(Subgroup.zpowers x ⊓ L) ∣ 3 := by
      have h_eq_card : Nat.card ↥(Subgroup.zpowers x ⊓ L) =
          Nat.card ((Subgroup.zpowers x ⊓ L).subgroupOf (Subgroup.zpowers x)) := by
        rw [CFSG.DisconnectedInvolutionGraph.Helpers.card_subgroupOf_eq_inf]
        simp [inf_assoc, inf_comm]
      rw [h_eq_card]
      have h_dvd' : Nat.card ((Subgroup.zpowers x ⊓ L).subgroupOf (Subgroup.zpowers x)) ∣
          Nat.card ↥(Subgroup.zpowers x) :=
        Subgroup.card_subgroup_dvd_card _
      rwa [hcard_zp] at h_dvd'
    rcases Nat.dvd_prime (by norm_num : Nat.Prime 3) |>.mp h_dvd with h | h
    · exact Nat.le_of_eq h
    · exact absurd h h_ne_3
  have hnormal : (Bs ⊓ L) ≤ Subgroup.normalizer ((Subgroup.zpowers x) : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have hc_bs : c ∈ Bs := (Subgroup.mem_inf.mp hc).1
      have ha_bs : a ∈ Bs := hzp_le_bs ha
      have h_comm : c * a = a * c := congrArg Subtype.val (hBs.1.is_comm.comm ⟨c, hc_bs⟩ ⟨a, ha_bs⟩)
      rw [h_comm, mul_assoc, mul_inv_cancel, mul_one]
      exact ha
    · intro hconj
      have hc_bs : c ∈ Bs := (Subgroup.mem_inf.mp hc).1
      have hc_inv_bs : c⁻¹ ∈ Bs := Bs.inv_mem hc_bs
      have h_conj_bs : c * a * c⁻¹ ∈ Bs := hzp_le_bs hconj
      have h_mul1 : c * a ∈ Bs := by
        have h_eq : c * a = (c * a * c⁻¹) * c := by group
        rw [h_eq]
        exact Bs.mul_mem h_conj_bs hc_bs
      have ha_bs : a ∈ Bs := by
        have h_eq : a = c⁻¹ * (c * a) := by group
        rw [h_eq]
        exact Bs.mul_mem hc_inv_bs h_mul1
      have h_comm : c * a = a * c := congrArg Subtype.val (hBs.1.is_comm.comm ⟨c, hc_bs⟩ ⟨a, ha_bs⟩)
      rw [h_comm, mul_assoc, mul_inv_cancel, mul_one] at hconj
      exact hconj
  have hinf_bot : Subgroup.zpowers x ⊓ (Bs ⊓ L) = ⊥ := by
    rw [← inf_assoc, inf_eq_left.mpr hzp_le_bs, hinf_bot_L]
  have hdisjoint : Disjoint (Subgroup.zpowers x) (Bs ⊓ L) := by
    rw [disjoint_iff]
    exact hinf_bot
  calc Nat.card Bs = Nat.card ↥(Subgroup.zpowers x ⊔ (Bs ⊓ L)) := by
        simpa using congrArg (fun H : Subgroup G => Nat.card ↥H) hsup
    _ = Nat.card ↥(Subgroup.zpowers x) * Nat.card ↥(Bs ⊓ L) :=
        CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
          (Subgroup.zpowers x) (Bs ⊓ L) hnormal hdisjoint
    _ = 3 * 3 ^ 5 := by rw [hcard_zp, hcard_inf]
    _ = 3 ^ 6 := by ring

theorem GGSecFiveRestHyp.isMaxElemAb3_centralizer
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) :
    IsMaxElemAb3 (Subgroup.centralizer ({x} : Set G)) Bs := by
  obtain ⟨-, hBs, hxB, -, -⟩ := hR.1.tableB_facts
  have hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hR.1.2.1.2.2.2
  refine ⟨?_, hBs, ?_⟩
  · intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact IsElemAbelian.comm hBs hxB hb
  · intro E' hE'C hE' hBsE'
    refine le_antisymm ?_ hBsE'
    intro g hgE'
    have hgC : g ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact IsElemAbelian.comm hE' (hBsE' hb) hgE'
    exact hstar g hgC (hE'.2 g hgE')

end CFSG.StandardType

end
