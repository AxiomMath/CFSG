module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddThree
public import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

theorem le_of_mem_uniqueSet_of_isPGroup {M E P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : rankThreeIsMaxTwoLocal M) (hE : E ∈ uniqueSet M) (hEP : E ≤ P) (hP : IsPGroup p ↥P) :
    P ≤ M := by
  by_contra hnot
  have hlt : P ⊓ M < P := lt_of_le_of_ne inf_le_left (fun hEq => hnot (hEq ▸ inf_le_right))
  have hgrow : P ⊓ M < P ⊓ normalizer ((P ⊓ M : Subgroup G) : Set G) :=
    CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hP hlt
  have hYU : P ⊓ M ∈ uniqueSet M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hE (le_inf hEP hE.1) inf_le_right
  have hNY : normalizer ((P ⊓ M : Subgroup G) : Set G) ≤ M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet hM hYU
  exact (not_lt_of_ge (le_inf inf_le_left (inf_le_right.trans hNY))) hgrow

theorem mem_of_map_conj_le_of_mem_uniqueSet {M E : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hE : E ∈ uniqueSet M) {h : G} (hh : E.map (MulAut.conj h).toMonoidHom ≤ M) : h ∈ M := by
  have h1 : E ≤ M.map (MulAut.conj h⁻¹).toMonoidHom := by
    intro e he
    refine Subgroup.mem_map.2 ⟨h * e * h⁻¹, hh (Subgroup.mem_map.2 ⟨e, he, rfl⟩), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have h2 : h⁻¹ ∈ normalizer (M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (hE.2 h⁻¹ h1)
  rw [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing M hM] at h2
  simpa using M.inv_mem h2

private theorem exists_isSylowOf_ge_chain {p : ℕ} [Fact p.Prime] {K E : Subgroup G} (hEK : E ≤ K)
    (hE : IsPGroup p ↥E) : ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P K ∧ E ≤ P := by
  obtain ⟨T, hT⟩ := (hE.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(T : Subgroup K).map K.subtype, ⟨T, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hEK hx⟩, hT (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

private theorem eq_of_card_eq_of_le_cyclic {Q A B : Subgroup G} (hQ : IsCyclic ↥Q) (hA : A ≤ Q)
    (hB : B ≤ Q) (h : Nat.card A = Nat.card B) : A = B := by
  have h1 : A.subgroupOf Q = B.subgroupOf Q := by
    refine (IsCyclic.subgroup_eq_iff_card_eq (H := A.subgroupOf Q) (K := B.subgroupOf Q)).2 ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv]
    exact h
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hA, inf_of_le_left hB] at h1
  exact h1

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem exists_sylow_le_M (S : SliceCore D L D₃ Y H) {E : Subgroup G} (hEX : E ≤ Opp 3 Y)
    (hE3 : IsPGroup 3 ↥E) (hEU : E ∈ uniqueSet D.M) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P H ∧ E ≤ P ∧ P ≤ D.M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP, hEP⟩ :=
    exists_isSylowOf_ge_chain (hEX.trans ((opp_le 3 Y).trans S.Y_le_H)) hE3
  exact ⟨P, hP, hEP, le_of_mem_uniqueSet_of_isPGroup D.maxLocal hEU hEP hP.isPGroup⟩

theorem map_conj_L_ne (S : SliceCore D L D₃ Y H) {E P : Subgroup G} (hEX : E ≤ Opp 3 Y)
    (hE3 : Nat.card E = 3) (hP : IsPGroup 3 ↥P) {h : G} (hEP : E ≤ P)
    (hhP : E.map (MulAut.conj h).toMonoidHom ≤ P)
    (hne : E.map (MulAut.conj h).toMonoidHom ≠ E) : L.map (MulAut.conj h).toMonoidHom ≠ L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hL
  apply hne
  have hEL : E ≤ L := hEX.trans S.opp_le_L
  have hE'L : E.map (MulAut.conj h).toMonoidHom ≤ L := hL ▸ Subgroup.map_mono hEL
  have hE'3 : Nat.card (E.map (MulAut.conj h).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hE3]
  have hPL : IsPGroup 3 ↥(P ⊓ L) := hP.to_inf_left
  have hC : IsPGroup 3 ↥((P ⊓ L).subgroupOf L) := hPL.comap_subtype
  obtain ⟨T, hT⟩ := hC.exists_le_sylow
  have hE₁ : E.subgroupOf L ≤ (T : Subgroup ↥L) := fun x hx =>
    hT (Subgroup.mem_subgroupOf.2 ⟨hEP hx, hEL hx⟩)
  have hE₂ : (E.map (MulAut.conj h).toMonoidHom).subgroupOf L ≤ (T : Subgroup ↥L) := fun x hx =>
    hT (Subgroup.mem_subgroupOf.2 ⟨hhP hx, hE'L hx⟩)
  have h1 := eq_of_card_eq_of_le_cyclic (S.isCyclic_sylow_three_L T) hE₂ hE₁ (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'L).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE'3, hE3])
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hE'L, inf_of_le_left hEL] at h1
  exact h1

end SliceCore

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
