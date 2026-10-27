module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmE27Bound
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmE27Nor

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega MulAction
open CFSG.RankThree.PartTwo.Sec21.FF79

theorem card_N0 :
    Nat.card (Subgroup.normalizer (E0 : Set GL6) ⊓ O6 : Subgroup GL6) = 1296 := by
  have hP : P81 ≤ (Subgroup.normalizer (E0 : Set GL6) ⊓ O6 : Subgroup GL6) := fun g hg =>
    Subgroup.mem_inf.2
      ⟨L41.mem_nor_of_forall (V := E0) fun y hy => P81_conj_mem hg hy, P81_le_O6 hg⟩
  have hT : T16 ≤ (Subgroup.normalizer (E0 : Set GL6) ⊓ O6 : Subgroup GL6) := fun g hg =>
    Subgroup.mem_inf.2
      ⟨L41.mem_nor_of_forall (V := E0) fun y hy => T16_conj_mem hg hy, T16_le_O6 hg⟩
  have h81 := Subgroup.card_dvd_of_le hP
  have h16 := Subgroup.card_dvd_of_le hT
  rw [card_P81] at h81
  rw [card_T16] at h16
  have hdvd : 1296 ∣ Nat.card (Subgroup.normalizer (E0 : Set GL6) ⊓ O6 : Subgroup GL6) :=
    (show 1296 = 81 * 16 by norm_num) ▸
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h81 h16
  have hle := card_N_le
  have hpos : 0 < Nat.card (Subgroup.normalizer (E0 : Set GL6) ⊓ O6 : Subgroup GL6) :=
    Nat.card_pos
  have := Nat.le_of_dvd hpos hdvd
  omega

theorem factorization_51840 : (51840 : ℕ).factorization 3 = 4 := by
  have h : (51840 : ℕ) = 3 ^ 4 * 640 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_E0 {E : Subgroup GL6} (hE : E ≤ O6) (h3 : IsElemAb 3 3 E) :
    ∃ g ∈ O6, E.map (MulAut.conj g).toMonoidHom = E0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hel := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr h3.1
  haveI := hel.1
  have hcardO : Nat.card O6 = 51840 := card_orthogonalGroup_qMinusForm
  have hP'card : Nat.card (P81.subgroupOf O6) = 3 ^ (Nat.card O6).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P81_le_O6).toEquiv, card_P81, hcardO,
      factorization_51840]
    norm_num
  let S0 : Sylow 3 O6 := Sylow.ofCard (P81.subgroupOf O6) hP'card
  have hEp : IsPGroup 3 (E.subgroupOf O6) := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have hx : ((x : O6) : GL6) ∈ E := x.2
    have := hel.2 _ hx
    simpa using this
  obtain ⟨Q, hQ⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq O6 Q S0
  refine ⟨(g : GL6), g.2, ?_⟩
  have hinj : Function.Injective (MulAut.conj (g : GL6)).toMonoidHom :=
    (MulAut.conj (g : GL6)).injective
  refine eq_E0_of_comm_card ?_ ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : (⟨y, hE hy⟩ : O6) ∈ E.subgroupOf O6 := hy
    have hmem : MulAut.conj g (⟨y, hE hy⟩ : O6) ∈ (S0 : Subgroup O6) := by
      rw [← hg]
      show _ ∈ ((g • Q : Sylow 3 O6) : Subgroup O6)
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) (Q : Subgroup O6) (hQ hy')
    have : (g : GL6) * y * (g : GL6)⁻¹ ∈ P81 := by
      have := (Subgroup.mem_subgroupOf).1 hmem
      simpa [MulAut.conj_apply] using this
    simpa [MulAut.conj_apply] using this
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx, hax⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hby⟩ := Subgroup.mem_map.1 b.2
    have hcomm := congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
    simp only [Subgroup.coe_mul] at hcomm
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [← hax, ← hby, ← map_mul, ← map_mul, hcomm]
  · rw [← Nat.card_congr (Subgroup.equivMapOfInjective E _ hinj).toEquiv, h3.2]
    norm_num

theorem Om_normalizer_E27 (E : Subgroup (F6 ≃ₗ[ZMod 2] F6))
    (hE : E ≤ TauCeti.QuadraticMap.orthogonalGroup qMinusForm) (h27 : IsElemAb 3 3 E) :
    Nat.card ↥(Subgroup.normalizer (E : Set (F6 ≃ₗ[ZMod 2] F6)) ⊓
      TauCeti.QuadraticMap.orthogonalGroup qMinusForm) = 1296 := by
  obtain ⟨g, hgO, hgE⟩ := exists_conj_E0 hE h27
  have hbij : Function.Bijective (MulAut.conj g).toMonoidHom := (MulAut.conj g).bijective
  have hO : O6.map (MulAut.conj g).toMonoidHom = O6 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hgO)
  have hN : (Subgroup.normalizer (E0 : Set GL6) ⊓ O6 : Subgroup GL6) =
      (Subgroup.normalizer (E : Set GL6) ⊓ O6 : Subgroup GL6).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ hbij.1, Subgroup.map_normalizer_eq_of_bijective E hbij, hO, hgE]
  rw [← card_N0, hN]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ hbij.1).toEquiv)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
