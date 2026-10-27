module

public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Sig5
import CFSG.RankThree.PartTwo.Sec16.Item1611Res2ProofModel
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesModel
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

namespace Proof1611Res2HJ

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

theorem exists_equiv_E0
    {X : Type*} [Group X]
    (φ : X ≃* CFSG.Blueprint.NativeSporadic.J2) {E : Subgroup X} (hE : Nat.card E = 9) :
    ∃ φ' : X ≃* GJ, E.map φ'.toMonoidHom = E0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e : X ≃* GJ := φ.trans CFSG.ComponentClassification.J2Cover.nativeEquivP with he
  set T := E.map e.toMonoidHom with hT
  have hT9 : Nat.card T = 9 := by rw [hT, Subgroup.card_map_of_injective e.injective, hE]
  have hT3 : IsPGroup 3 T := IsPGroup.of_card (n := 2) (by rw [hT9]; norm_num)
  have hP3 : Nat.card P3 = 3 ^ (Nat.card GJ).factorization 3 := by
    rw [card_P3, card_GJ, CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 604800 = 3 ^ 3 * 22400 by norm_num) (by norm_num)]
    norm_num
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_map_conj_le hP3 hT3
  set T' := T.map (MulAut.conj g).toMonoidHom with hT'
  have hT'9 : Nat.card T' = 9 := by
    rw [hT', Subgroup.card_map_of_injective (MulAut.conj g).injective, hT9]
  obtain ⟨n, -, hn⟩ := delta_transitive E0 ⟨E0_le_P3, by rw [card_E0]; norm_num⟩ T' ⟨hg, hT'9⟩
  refine Res5Types.exists_equiv_map_eq_of_conj e (g := g⁻¹ * n⁻¹) (fun x hx => ?_)
    (by rw [card_E0, hE]; norm_num)
  have hx' : g * e x * g⁻¹ ∈ T' := ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
  rw [hn] at hx'
  obtain ⟨p, hp, hpx⟩ := hx'
  refine ⟨p, hp, ?_⟩
  have hpx' : n⁻¹ * p * n⁻¹⁻¹ = g * e x * g⁻¹ := hpx
  calc g⁻¹ * n⁻¹ * p * (g⁻¹ * n⁻¹)⁻¹ = g⁻¹ * (n⁻¹ * p * n⁻¹⁻¹) * g := by group
    _ = g⁻¹ * (g * e x * g⁻¹) * g := by rw [hpx']
    _ = e x := by group

theorem two_subgroup_facts :
    (∀ X : Subgroup GJ, IsPGroup 2 X → E0 ≤ Subgroup.normalizer (X : Set GJ) → SJ 2 ≤ X →
      X ⊓ Subgroup.centralizer ({aJ 0} : Set GJ) = ⊥) ∧
    SJ 0 ⊓ Subgroup.centralizer ({aJ 0} : Set GJ) ≠ ⊥ := by
  refine ⟨fun X hX2 hXE hSX => ?_, fun hbot => ?_⟩
  · by_contra hne
    exact not_triple hX2 (Vk_le_of_ne_bot hX2 hXE 0 hne) (V1_le_S2.trans hSX)
      (V2_le_S2.trans hSX)
  · have hv : vkE 0 1 ∈ SJ 0 ⊓ Subgroup.centralizer ({aJ 0} : Set GJ) :=
      ⟨V0_le_S0 (vkE_mem 0 1), Vk_le_C 0 (vkE_mem 0 1)⟩
    rw [hbot, Subgroup.mem_bot] at hv
    apply v1_ne_one
    have h1 : cJ 0 * v1J * (cJ 0)⁻¹ = 1 := by simpa [vkE] using hv
    calc v1J = (cJ 0)⁻¹ * (cJ 0 * v1J * (cJ 0)⁻¹) * cJ 0 := by group
      _ = 1 := by rw [h1]; group

end Proof1611Res2HJ

open Proof1611Res2HJ CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 in
theorem ks169HJNotTrans :
    KS169HJNotTrans := by
  intro G _ _ A c L h hJ hAab hcA h142
  have : (ker142 A (lB A) c).Normal := ker142_normal hAab hcA
  have hS14 := h.toSec14Std
  have hD := h.toSec13Data
  obtain ⟨-, h9, hAc⟩ := j2_point_facts hD hJ
  obtain ⟨φ⟩ := hJ
  obtain ⟨φ', hφ'⟩ := exists_equiv_E0 φ (Res5Gen.card_image_inf hS14 h9)
  have hLK := Proof1611Res2.le_k142_of_item142 hS14 h142
    (by rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2]; norm_num)
  obtain ⟨h1, h2⟩ := two_subgroup_facts
  exact Proof1611Res2.not_transOn_of_model sporadicModels131 hS14 hLK
    (fun Q hQ => (h142 Q hQ).1) hAc φ' hφ' (aJ_mem_E0 0) (isPGroup_S 2) (E0_le_normalizer_S 2)
    (isPGroup_S 0) (E0_le_normalizer_S 0) h1 h2

end CFSG.RankThree.PartTwo.Sec16
