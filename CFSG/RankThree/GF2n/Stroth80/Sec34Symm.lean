module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Spure

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem StrothHyp.QB_Z (H : StrothHyp M Q Z) : QB Z = Q := by
  unfold QB
  rw [H.normalizer_Z.1, H.hQ]
  unfold inSubgroup
  rw [H.fitting]

theorem StrothHyp.le_QB_of_le_QB (H : StrothHyp M Q Z) {B C : Subgroup G}
    (hB : ∃ g : G, B = conjSubgroup g Z) (hC : ∃ h : G, C = conjSubgroup h Z)
    (hne : B ≠ C) (hBC : B ≤ QB C) : C ≤ QB B := by
  obtain ⟨g, hg⟩ := hB
  obtain ⟨h, hh⟩ := hC
  have hCZ : conjSubgroup h⁻¹ C = Z := by
    rw [hh, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hB'Q : conjSubgroup h⁻¹ B ≤ Q := by
    have h1 : conjSubgroup h⁻¹ B ≤ conjSubgroup h⁻¹ (QB C) := Subgroup.map_mono hBC
    have h2 : conjSubgroup h⁻¹ (QB C) = QB Z := by
      rw [← QB_conj, hCZ]
    exact h1.trans (h2.trans H.QB_Z).le
  have hB'Z : conjSubgroup h⁻¹ B ≠ Z := by
    intro h'
    apply hne
    have e : conjSubgroup h (conjSubgroup h⁻¹ B) = B := by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    exact e.symm.trans ((congrArg (conjSubgroup h) h').trans hh.symm)
  have hc : Ctx M Q Z (conjSubgroup h⁻¹ B) :=
    { hyp := H
      conj := ⟨h⁻¹ * g, by rw [hg, conjSubgroup_mul]⟩
      le := hB'Q
      ne := hB'Z }
  have h4 : conjSubgroup h Z ≤ conjSubgroup h (QB (conjSubgroup h⁻¹ B)) :=
    Subgroup.map_mono hc.Z_le_QB.1
  have h5 : conjSubgroup h (QB (conjSubgroup h⁻¹ B)) = QB B := by
    rw [← QB_conj, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  rw [hh]
  rw [h5] at h4
  exact h4

theorem StrothHyp.le_QB_iff_le_QB (H : StrothHyp M Q Z) {B C : Subgroup G}
    (hB : ∃ g : G, B = conjSubgroup g Z) (hC : ∃ h : G, C = conjSubgroup h Z)
    (hne : B ≠ C) : B ≤ QB C ↔ C ≤ QB B :=
  ⟨H.le_QB_of_le_QB hB hC hne, fun h => H.le_QB_of_le_QB hC hB (Ne.symm hne) h⟩

theorem Ctx.conj_le_QB_of_card_Spure (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hS : Nat.card Q * Nat.card Z < Nat.card hc.Spure)
    {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ conjSubgroup m B) (hx1 : x ≠ 1)
    (hxC : x ∈ Subgroup.centralizer (B : Set G)) : conjSubgroup m B ≤ QB B := by
  have hBC : B ≤ QB (conjSubgroup m B) :=
    hc.le_QB_conj_of_card_Spure hw hn hno hS hm hx hx1 hxC
  by_cases hCB : conjSubgroup m B = B
  · rw [hCB]
    exact hc.B_le_QB
  · obtain ⟨g, hg⟩ := hc.conj
    have hC : ∃ h : G, conjSubgroup m B = conjSubgroup h Z :=
      ⟨m * g, by rw [hg, conjSubgroup_mul]⟩
    exact hc.hyp.le_QB_of_le_QB ⟨g, hg⟩ hC (Ne.symm hCB) hBC

end CFSG.RankThree.GF2n.Stroth80
