module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec101SLVec

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem isZConjugate_of_isConjB (hc : Ctx M Q Z B) {P : Subgroup G} (hP : IsConjB M B P) :
    Smith81.IsZConjugate Z P := by
  obtain ⟨m, hm, rfl⟩ := hP
  obtain ⟨g₀, hg₀⟩ := hc.conj
  exact ⟨m * g₀, by rw [hg₀, conjSubgroup_mul]⟩

theorem exists_good_point_of_mem_U₁ (hc : Ctx M Q Z B) {Y U₁ : Subgroup G}
    (ha : ∀ u ∈ U₁, ∃ m ∈ M, ∃ b ∈ B, u * (m * b * m⁻¹)⁻¹ ∈ Z)
    (hb : ∀ m ∈ M, ∀ u ∈ U₁, u ∉ Z → u ∈ (conjSubgroup m B ⊔ Z : Subgroup G) →
      GoodPt M Q B Y (conjSubgroup m B))
    {u : G} (hu : u ∈ U₁) (huZ : u ∉ Z) :
    ∃ P : Subgroup G, IsConjB M B P ∧ u ∈ P ∧ GoodPt M Q B Y P := by
  obtain ⟨m, hm, b, hbB, hz⟩ := ha u hu
  have hcm : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  have hmb : m * b * m⁻¹ ∈ conjSubgroup m B := by
    rw [mem_conjSubgroup, show m⁻¹ * (m * b * m⁻¹) * m = b by group]
    exact hbB
  have hsup : u ∈ (conjSubgroup m B ⊔ Z : Subgroup G) := by
    have e : u = (u * (m * b * m⁻¹)⁻¹) * (m * b * m⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left hmb)
  obtain ⟨p, hpQ, hup⟩ := hcm.exists_mem_conj_of_mem_sup hsup huZ
  have hpM : p ∈ M := hc.hyp.Q_normal.1 hpQ
  have hpm : p * m ∈ M := M.mul_mem hpM hm
  have hP : conjSubgroup p (conjSubgroup m B) = conjSubgroup (p * m) B :=
    (conjSubgroup_mul p m B).symm
  rw [hP] at hup
  refine ⟨conjSubgroup (p * m) B, ⟨p * m, hpm, rfl⟩, hup, ?_⟩
  exact hb (p * m) hpm u hu huZ (Subgroup.mem_sup_left hup)

theorem good_of_mem_U₁_inf_QB (hc : Ctx M Q Z B) {Y U₁ : Subgroup G} (h4 : FourConcl M Q B Y)
    (ha : ∀ u ∈ U₁, ∃ m ∈ M, ∃ b ∈ B, u * (m * b * m⁻¹)⁻¹ ∈ Z)
    (hb : ∀ m ∈ M, ∀ u ∈ U₁, u ∉ Z → u ∈ (conjSubgroup m B ⊔ Z : Subgroup G) →
      GoodPt M Q B Y (conjSubgroup m B))
    {F : Subgroup G} (hF : IsConjB M B F) {u : G} (hu : u ∈ U₁) (huZ : u ∉ Z)
    (huF : u ∈ QB F) : GoodPt M Q B Y F := by
  obtain ⟨P, hP, huP, hgood⟩ := exists_good_point_of_mem_U₁ hc ha hb hu huZ
  have hu1 : u ≠ 1 := fun h => huZ (h ▸ Z.one_mem)
  have hPF : P ≤ QB F := Smith81.IsZConjugate.le_QB_of_mem hc.hyp
    (isZConjugate_of_isConjB hc hF) (isZConjugate_of_isConjB hc hP) hu1 huP huF
  have hFP : F ≤ QB P := (Smith81.IsZConjugate.le_QB_iff hc.hyp
    (isZConjugate_of_isConjB hc hF) (isZConjugate_of_isConjB hc hP)).mp hPF
  exact h4 P F hP hF hgood hFP

end HS9

end CFSG.RankThree.GF2n.Stroth80
