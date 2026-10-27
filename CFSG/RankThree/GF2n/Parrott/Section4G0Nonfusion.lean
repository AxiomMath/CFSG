module

public import CFSG.RankThree.GF2n.Parrott.Section4Lemma41
public import CFSG.RankThree.GF2n.Parrott.Section1

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_index_two_not_le_H_of_nonfusion (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hH' : (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex (H z) = 2)
    (hx : ∃ x ∈ H z, orderOf x = 2 ∧ x ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) ∧
      ∀ g : G, g⁻¹ * x * g ∉ ⁅H z, H z⁆ ⊔ centerIn (J z)) :
    ∃ G₀ : Subgroup G, G₀.Normal ∧ G₀.index = 2 ∧ ¬ H z ≤ G₀ := by
  obtain ⟨x, hxH, hx2, hxN, hxc⟩ := hx
  have hxx : x * x = 1 := by
    have h1 := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at h1
  have hxp : IsPGroup 2 (Subgroup.zpowers (⟨x, hxH⟩ : ↥(H z))) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact hx2
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  have hT : IsSylowOf 2 ((Q : Subgroup ↥(H z)).map (H z).subtype) (H z) := ⟨Q, rfl⟩
  have hxT : x ∈ (Q : Subgroup ↥(H z)).map (H z).subtype :=
    ⟨⟨x, hxH⟩, hQ (Subgroup.mem_zpowers _), rfl⟩
  have hTH : (Q : Subgroup ↥(H z)).map (H z).subtype ≤ H z := hT.le
  have hTtop := isSylowOf_top_of_isSylowOf_H h hZ _ hT
  obtain ⟨-, hTp, hdvd⟩ := isSylowOf_iff.mp hTtop
  have hdvd' : ¬ 2 ∣ ((Q : Subgroup ↥(H z)).map (H z).subtype).index := by
    rwa [← Subgroup.relIndex_top_right]
  let S : Sylow 2 G := hTp.toSylow hdvd'
  have hS : (S : Subgroup G) = (Q : Subgroup ↥(H z)).map (H z).subtype :=
    IsPGroup.toSylow_coe hTp hdvd'
  have hne0 : (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex
      ((Q : Subgroup ↥(H z)).map (H z).subtype) ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card (⁅H z, H z⁆ ⊔ centerIn (J z))
      ((Q : Subgroup ↥(H z)).map (H z).subtype)
    rw [h0, zero_mul] at h1
    exact absurd h1.symm Nat.card_pos.ne'
  have hne1 : (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex
      ((Q : Subgroup ↥(H z)).map (H z).subtype) ≠ 1 := by
    intro h1
    exact hxN ((Subgroup.relIndex_eq_one.mp h1) hxT)
  have hle2 : (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex
      ((Q : Subgroup ↥(H z)).map (H z).subtype) ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right hTH (by rw [hH']; omega :
      (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex (H z) ≠ 0)
    rwa [hH'] at this
  have hindex : ((⁅H z, H z⁆ ⊔ centerIn (J z)) ⊓
      ((Q : Subgroup ↥(H z)).map (H z).subtype)).relIndex (S : Subgroup G) = 2 := by
    rw [hS, Subgroup.inf_relIndex_right]
    omega
  obtain ⟨G₀, hGn, hGi, hxG⟩ := prop3_index_two S hindex hxx (hS ▸ hxT)
    (fun hm => hxN (Subgroup.mem_inf.mp hm).1)
    (fun g hg => hxc g (Subgroup.mem_inf.mp hg).1)
  exact ⟨G₀, hGn, hGi, fun hHG => hxG (hHG hxH)⟩

end CFSG.RankThree.GF2n.Parrott
