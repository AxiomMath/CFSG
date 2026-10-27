module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight61Conclusion
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet mem_uniqueSet_of_le)

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_nine_le_of_isExtraspecialExpP
    {Q : Subgroup G}
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q) :
    ∃ E : Subgroup G, E ≤ Q ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  have hQ' := hQ
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hQ'
  obtain ⟨hQcard', hQexp, -, hQcenter⟩ := hQ'
  have hQcard : Nat.card ↥Q = 27 := by
    rw [hQcard']
    norm_num
  have hQrank : 2 ≤ CFSG.Open.pRank 3 Q :=
    two_le_pRank_three_of_isExtraspecialExpP_le (G := G) (Q := Q) (H := Q) le_rfl hQ
  obtain ⟨E, hEQ, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num : 1 < 3) Q
  have hrank : CFSG.Open.pRank 3 Q = 2 := by
    refine le_antisymm ?_ hQrank
    by_contra hle
    have h3 : 3 ≤ CFSG.Open.pRank 3 Q := by omega
    have hpow : 3 ^ 3 ≤ 3 ^ CFSG.Open.pRank 3 Q :=
      Nat.pow_le_pow_right (by norm_num) h3
    have hcardE : Nat.card E = 3 ^ CFSG.Open.pRank 3 Q := hEcard
    have hle27 : Nat.card E ≤ 27 := by
      have hsub : Nat.card E ≤ Nat.card ↥Q := by
        have h := Subgroup.card_le_card_group (E.subgroupOf Q)
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ).toEquiv] at h
      rwa [hQcard] at hsub
    have hge27 : 27 ≤ Nat.card E := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ CFSG.Open.pRank 3 Q := hpow
        _ = Nat.card E := hcardE.symm
    have hEcard27 : Nat.card E = 27 := le_antisymm hle27 hge27
    have hEtop : E = Q :=
      Subgroup.eq_of_le_of_card_ge hEQ (by rw [hQcard, hEcard27])
    haveI : IsMulCommutative ↥Q := by
      rw [← hEtop]
      exact hEel.1
    have hcenter : Subgroup.center ↥Q = ⊤ := Subgroup.center_eq_top
    have hcardcenter : Nat.card (Subgroup.center ↥Q) = 27 := by
      rw [hcenter, Subgroup.card_top, hQcard]
    have hcenter3 : Nat.card (Subgroup.center ↥Q) = 3 := hQcenter
    omega
  rw [hrank] at hEcard
  exact ⟨E, hEQ, hEel, hEcard⟩

theorem mem_uniqueSet_of_fusion_control
    {M P Z : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P M)
    (hZP : Z ≤ P) (hZcard : Nat.card Z = 3)
    (hN : Subgroup.normalizer (Z : Set G) ≤ M)
    (hfusion : ∀ g : G, Z.map (MulAut.conj g).toMonoidHom ≤ P →
      ∃ m ∈ M, Z.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj m).toMonoidHom) :
    Z ∈ uniqueSet M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hZP.trans hP.le, ?_⟩
  intro g hZg
  have hYle : Z.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
    have h1 : Z.map (MulAut.conj g⁻¹).toMonoidHom ≤
        (M.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.map_mono hZg
    rw [Subgroup.map_map] at h1
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rwa [hcomp, Subgroup.map_id] at h1
  have hYp : IsPGroup 3 (Z.map (MulAut.conj g⁻¹).toMonoidHom) := by
    have hZ3 : IsPGroup 3 Z := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [hZcard, pow_one]
    exact hZ3.map _
  have hYpM : IsPGroup 3 ((Z.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf M) :=
    hYp.comap_subtype
  obtain ⟨S, hYS⟩ := hYpM.exists_le_sylow
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 ((S : Subgroup ↥M).map M.subtype) M := ⟨S, rfl⟩
  obtain ⟨m, hmM, hconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hP hS
  have hYS' : Z.map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup ↥M).map M.subtype := by
    intro y hy
    exact ⟨⟨y, hYle hy⟩, hYS (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have hYP : Z.map (MulAut.conj (m⁻¹ * g⁻¹)).toMonoidHom ≤ P := by
    rintro _ ⟨z, hz, rfl⟩
    have hy : MulAut.conj g⁻¹ z ∈ Z.map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hz
    have hmem := (hconj (MulAut.conj g⁻¹ z)).mp (hYS' hy)
    simpa [MulAut.conj_apply, mul_assoc] using hmem
  obtain ⟨m', hm'M, heq⟩ := hfusion (m⁻¹ * g⁻¹) hYP
  have hcancel : Z.map (MulAut.conj (m'⁻¹ * (m⁻¹ * g⁻¹))).toMonoidHom = Z := by
    have h2 := congrArg (fun H : Subgroup G => H.map (MulAut.conj m'⁻¹).toMonoidHom) heq
    rw [Subgroup.map_map, Subgroup.map_map] at h2
    have hcomp1 : (MulAut.conj m'⁻¹).toMonoidHom.comp (MulAut.conj m').toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have hcomp2 : (MulAut.conj m'⁻¹).toMonoidHom.comp
        (MulAut.conj (m⁻¹ * g⁻¹)).toMonoidHom =
        (MulAut.conj (m'⁻¹ * (m⁻¹ * g⁻¹))).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp2, hcomp1, Subgroup.map_id] at h2
    exact h2
  have hmemN : m'⁻¹ * (m⁻¹ * g⁻¹) ∈ Subgroup.normalizer (Z : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcancel
  have hM : m'⁻¹ * (m⁻¹ * g⁻¹) ∈ M := hN hmemN
  have hg_inv : g⁻¹ ∈ M := by
    have heqg : g⁻¹ = m * m' * (m'⁻¹ * (m⁻¹ * g⁻¹)) := by group
    rw [heqg]
    exact M.mul_mem (M.mul_mem hmM hm'M) hM
  have hgM : g ∈ M := by
    simpa using M.inv_mem hg_inv
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgM)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
