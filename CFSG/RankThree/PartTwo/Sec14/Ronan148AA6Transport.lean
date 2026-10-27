module

public import CFSG.RankThree.PartTwo.Sec14.Std
import CFSG.RankThree.PartTwo.Sec14.Ronan148BA6Sylow
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHJ
import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_eq_sup_of_le_yb148
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {B : Subgroup G} (hB : IsHyperplane A B)
    {b d : G} {Lb : Subgroup G} (hc : IsLBConfig A B b d Lb) {YB : Subgroup G}
    (hle : YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B)
    {E : Subgroup G} (hEY : E ≤ YB) (hE3 : IsPGroup 3 E) (hE9 : Nat.card E = 9) :
    ∃ u ∈ Subgroup.centralizer ({b} : Set G),
      A.map (MulAut.conj u).toMonoidHom = Subgroup.zpowers b ⊔ E ∧
      (A ⊓ Lb).map (MulAut.conj u).toMonoidHom = E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, -, -, -, hCB⟩ := Main148.lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hb3 : b ^ 3 = 1 := hA.1.2 b hbA
  set CB := Subgroup.centralizer (B : Set G) with hCBdef
  set O := pPrimeCoreOf 3 CB with hOdef
  set J₀ := lB A B with hJ₀def
  have hLbmem : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  have hLbC : Lb ≤ Subgroup.centralizer ({b} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt hLbmem.1
  have hJ₀ : J₀ ≤ Lb ⊓ Subgroup.centralizer ({d} : Set G) := by
    rw [hJ₀def, Item148HJ.lB_eq_residual hS hB hc]
    exact Subgroup.map_subtype_le _
  have hJ₀CB : J₀ ≤ CB := by
    rw [hCB]
    exact fun x hx => ⟨hLbC (hJ₀ hx).1, (hJ₀ hx).2⟩
  have hOCB : O ≤ CB := pPrimeCoreOf_le 3 CB
  have hCBb : CB ≤ Subgroup.centralizer ({b} : Set G) := by
    rw [hCB]
    exact inf_le_left
  have hEle : E ≤ O ⊔ J₀ := hEY.trans hle
  have hECB : E ≤ CB := hEle.trans (sup_le hOCB hJ₀CB)
  set N : Subgroup ↥CB := O.subgroupOf CB with hNdef
  haveI hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOCB).mpr
    (le_normalizer_pPrimeCoreOf 3 CB)
  have hN3 : ¬ 3 ∣ Nat.card N := by
    rw [hNdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOCB).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 CB)
  set EH : Subgroup ↥CB := E.subgroupOf CB with hEHdef
  have hEH3 : IsPGroup 3 EH := hE3.of_equiv (Subgroup.subgroupOfEquivOfLe hECB).symm
  set U : Subgroup ↥CB := J₀.subgroupOf CB with hUdef
  have hEU : EH.map (QuotientGroup.mk' N) ≤ U.map (QuotientGroup.mk' N) := by
    rintro _ ⟨e, he, rfl⟩
    have heNU : e ∈ N ⊔ U := by
      rw [hNdef, hUdef, ← Subgroup.subgroupOf_sup hOCB hJ₀CB]
      exact hEle he
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at heNU
    obtain ⟨n, hn, j, hj, rfl⟩ := heNU
    refine ⟨j, hj, ?_⟩
    have h1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [map_mul, h1, one_mul]
  obtain ⟨P, hPU, -, hPE, hPcard⟩ :=
    Ronan148B.exists_le_map_eq_of_le_map (p := 3) hN3 hEU (hEH3.map _)
  have hPcard' : Nat.card P = Nat.card EH := by
    rw [hPcard, Ronan148B.card_map_mk'_of_isPGroup hN3 hEH3]
  obtain ⟨n, hnN, hPn⟩ := Ronan148B.exists_mem_map_conj_eq_of_map_eq hN3 hEH3 hPcard' hPE.symm
  set o : G := (n : G) with hodef
  have hoO : o ∈ O := hnN
  have hob : o ∈ Subgroup.centralizer ({b} : Set G) := hCBb (hOCB hoO)
  set E' := E.map (MulAut.conj o).toMonoidHom with hE'def
  have hE'J : E' ≤ J₀ := by
    rintro _ ⟨e, he, rfl⟩
    have hmem : n * (⟨e, hECB he⟩ : ↥CB) * n⁻¹ ∈ P := by
      rw [hPn]
      exact ⟨⟨e, hECB he⟩, he, rfl⟩
    exact hPU hmem
  have hE'9 : Nat.card E' = 9 := by
    rw [hE'def, Subgroup.card_map_of_injective (MulAut.conj o).injective, hE9]
  have hE'Lb : E' ≤ Lb := fun x hx => (hJ₀ (hE'J hx)).1
  have hS' := Item148HJ.sec14Std_of_isLBConfig hS hc
  have hJ2 := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨hbL, -, hAb⟩ := j2_point_facts hS'.toSec13Data hJ2
  have hbLC : b ∈ Subgroup.centralizer (Lb : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLbC hy)
  have hbE'C : b ∈ Subgroup.centralizer (E' : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hE'Lb) hbLC
  have hbE' : b ∉ E' := fun hb => hbL (hE'Lb hb)
  set F := Subgroup.zpowers b ⊔ E' with hFdef
  have hF27 : Nat.card F = 27 := by
    have h := KFacts.KS14.card_eq_three_mul_card_inf hbE'C hbE' hb3 le_rfl
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
    rw [inf_of_le_right le_sup_right, hE'9] at h
    rw [hFdef, h]
  have hFle : F ≤ Subgroup.zpowers b ⊔ Lb := sup_le_sup_left hE'Lb _
  have hAle : A ≤ Subgroup.zpowers b ⊔ Lb := hAb ▸ sup_le_sup_left inf_le_right _
  have hbF : b ∈ F := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  obtain ⟨g, hgL, hFA⟩ := KFacts.KS14.Native.j2_exists_conjugate_of_card_twentySeven_of_quot
    (L := Lb) (N := aschbacherSolvableCore 3 ↥Lb) hθ3 hJ2 hbLC hbL hb3 hAle hFle hbA hbF hA.2 hF27
  rw [conjugate] at hFA
  have hFL : F ⊓ Lb = E' := by
    have hE'FL : E' ≤ F ⊓ Lb := le_inf le_sup_right hE'Lb
    have h1 : Nat.card ↥(F ⊓ Lb) ∣ 27 := hF27 ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : 9 ∣ Nat.card ↥(F ⊓ Lb) := hE'9 ▸ Subgroup.card_dvd_of_le hE'FL
    have h3 : Nat.card ↥(F ⊓ Lb) ≠ 27 := by
      intro h
      have hFeq : F ⊓ Lb = F := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hF27])
      have hbFL : b ∈ F ⊓ Lb := by rw [hFeq]; exact hbF
      exact hbL hbFL.2
    have h9 : Nat.card ↥(F ⊓ Lb) = 9 := by
      obtain ⟨m, hm⟩ := h2
      rw [hm] at h1 h3 ⊢
      have hm3 : m ∣ 3 := by
        have h1' : 9 * m ∣ 9 * 3 := by simpa using h1
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1'
      rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with h | h
      · rw [h]
      · exfalso
        apply h3
        rw [h]
    exact (Subgroup.eq_of_le_of_card_ge hE'FL (by rw [h9, hE'9])).symm
  have hgLb : Lb.map (MulAut.conj g⁻¹).toMonoidHom = Lb :=
    Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (Lb.inv_mem hgL))
  have hALb : (A ⊓ Lb).map (MulAut.conj g⁻¹).toMonoidHom = E' := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective, hgLb, ← hFA, hFL]
  have hE'o : E'.map (MulAut.conj o⁻¹).toMonoidHom = E := by
    rw [hE'def, Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one]
  have hbo : (Subgroup.zpowers b).map (MulAut.conj o⁻¹).toMonoidHom = Subgroup.zpowers b := by
    rw [MonoidHom.map_zpowers]
    congr 1
    have hob' : o * b = b * o := Subgroup.mem_centralizer_singleton_iff.mp hob
    show o⁻¹ * b * o⁻¹⁻¹ = b
    rw [inv_inv, mul_assoc, ← hob', ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨o⁻¹ * g⁻¹, Subgroup.mul_mem _ (Subgroup.inv_mem _ hob)
    (Subgroup.inv_mem _ (hLbC hgL)), ?_, ?_⟩
  · rw [← Late.map_conj_map_conj, ← hFA, hFdef, Subgroup.map_sup, hbo, hE'o]
  · rw [← Late.map_conj_map_conj, hALb, hE'o]

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
