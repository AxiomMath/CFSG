module

public import CFSG.RankThree.PartTwo.Sec16.Item1613ResProofOut
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13Tools
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

open CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.RankThree.PartTwo.Sec16.Proof1613
  CFSG.RankThree.PartTwo.Sec16.Proof1613Res

open scoped commutatorElement

section Item1613Res10WC

variable {G : Type} [Group G] [Finite G]

theorem mem_omegaA_of_weaklyClosed {A L : Subgroup G} {c : G} (h : Ctx169 G A c L) {d : G}
    {Q : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q
      (Subgroup.centralizer ((Subgroup.zpowers d ⊔ Subgroup.zpowers c : Subgroup G) : Set G)))
    (hAQ : A ≤ Q)
    (hWC : ∀ v ∈ Subgroup.normalizer
        ((Subgroup.zpowers d ⊔ Subgroup.zpowers c : Subgroup G) : Set G) ⊓
          Subgroup.normalizer (Subgroup.zpowers d : Set G),
        A.map (MulAut.conj v).toMonoidHom ≤ Q ⊓ Subgroup.normalizer (A : Set G) →
          A.map (MulAut.conj v).toMonoidHom = A)
    {u : G} (huU : u ∈ Subgroup.normalizer
        ((Subgroup.zpowers d ⊔ Subgroup.zpowers c : Subgroup G) : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    Subgroup.zpowers (u * c * u⁻¹) ∈ omegaA A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := Subgroup.zpowers d ⊔ Subgroup.zpowers c with hB
  set CB := Subgroup.centralizer (B : Set G) with hCB
  set U := Subgroup.normalizer (B : Set G) ⊓
    Subgroup.normalizer (Subgroup.zpowers d : Set G) with hU
  have hcA : c ∈ A := h.mem_A
  have hcB : c ∈ B := (le_sup_right : Subgroup.zpowers c ≤ B) (Subgroup.mem_zpowers c)
  have hCBU : CB ≤ U := le_inf (Subgroup.centralizer_le_normalizer _)
    ((Subgroup.centralizer_le (le_sup_left : Subgroup.zpowers d ≤ B)).trans
      (Subgroup.centralizer_le_normalizer _))
  have huB : u ∈ Subgroup.normalizer (B : Set G) := (Subgroup.mem_inf.mp huU).1
  have huCB : CB.map (MulAut.conj u).toMonoidHom = CB := by
    rw [hCB, map_conj_centralizer]
    congr 2
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp huB
  have hQu : CFSG.ABGLocalTools.IsSylowOf 3 (Q.map (MulAut.conj u).toMonoidHom) CB := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rw [← huCB]
      exact Subgroup.map_mono hQ.le
    · rw [Subgroup.card_map_of_injective (MulAut.conj u).injective]
      exact hQ.card_eq
  obtain ⟨z, hzCB, hzQ⟩ := hQ.exists_mem_conj hQu
  set w := z⁻¹ * u with hw
  have hwU : w ∈ U := U.mul_mem (U.inv_mem (hCBU hzCB)) huU
  have hAwQ : A.map (MulAut.conj w).toMonoidHom ≤ Q := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : u * y * u⁻¹ ∈ Q.map (MulAut.conj u).toMonoidHom := ⟨y, hAQ hy, rfl⟩
    have h2 := (hzQ _).mp h1
    have h3 : (MulAut.conj w).toMonoidHom y = z⁻¹ * (u * y * u⁻¹) * z := by
      simp only [hw, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h3]
    exact h2
  have hAw : A.map (MulAut.conj w).toMonoidHom = A := by
    by_contra hne
    obtain ⟨z', hz', hz'Q, hz'ne⟩ := exists_conj_le_inf_normalizer hQ.isPGroup hAQ hAwQ hne
    have hz'U : z' ∈ U := by
      rcases hz' with rfl | hz'
      · exact hwU
      · exact hCBU (hQ.le hz')
    exact hz'ne (hWC z' hz'U hz'Q)
  have hwW : w ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hAw
  have hcuB : u * c * u⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp huB c).mp hcB
  have hzc : z⁻¹ * (u * c * u⁻¹) * z = u * c * u⁻¹ := by
    have h1 := Subgroup.mem_centralizer_iff.mp hzCB _ hcuB
    calc z⁻¹ * (u * c * u⁻¹) * z = z⁻¹ * ((u * c * u⁻¹) * z) := by group
      _ = z⁻¹ * (z * (u * c * u⁻¹)) := by rw [h1]
      _ = u * c * u⁻¹ := by group
  have hwc : w * c * w⁻¹ = u * c * u⁻¹ := by
    rw [hw, ← hzc]
    group
  have hmem := (map_conj_mem_omegaA_iff hwW).mpr h.zpowers_mem_omegaA
  rwa [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hwc] at hmem

end Item1613Res10WC

end CFSG.RankThree.PartTwo.Sec16
