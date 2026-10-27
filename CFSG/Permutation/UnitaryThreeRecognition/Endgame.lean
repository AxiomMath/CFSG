module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.Reconstruction
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Permutation.UnitaryThreeRecognition.Basic
public import CFSG.Permutation.UnitaryThreeRecognition.ModelBasic

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1 CFSG.BenderSuzuki.PFchapter4section1
open CFSG.UnitaryThreeRecognition.Model

variable {G Ω : Type*} [Group G] [MulAction G Ω]

omit [MulAction G Ω] in
theorem mem_rightConjugate {H : Subgroup G} {g x : G} :
    x ∈ rightConjugate H g ↔ g * x * g⁻¹ ∈ H := by
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

theorem pairStab_eq_inf_rightConjugate {a b : Ω} {s : G} (hsa : s • a = b) (hs2 : s * s = 1) :
    stabilizer G a ⊓ rightConjugate (stabilizer G a) s = pairStab G a b := by
  have hsb : s • b = a := by rw [← hsa, ← mul_smul, hs2, one_smul]
  have hs : s⁻¹ = s := by rw [inv_eq_iff_mul_eq_one, hs2]
  ext x
  rw [Subgroup.mem_inf, mem_rightConjugate, mem_stabilizer_iff, mem_stabilizer_iff, mem_pairStab,
    hs]
  constructor
  · rintro ⟨hxa, hxb⟩
    refine ⟨hxa, ?_⟩
    have h1 : s • (x • b) = a := by
      rw [← hsa, ← mul_smul, ← mul_smul]; exact hxb
    calc x • b = (s * s) • (x • b) := by rw [hs2, one_smul]
      _ = s • (s • (x • b)) := mul_smul _ _ _
      _ = b := by rw [h1, hsa]
  · rintro ⟨hxa, hxb⟩
    refine ⟨hxa, ?_⟩
    rw [mul_smul, mul_smul, hsa, hxb, hsb]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem sup_pairStab_eq_stabilizer {b : Ω} (hb : b ≠ a) :
    Q ⊔ pairStab G a b = stabilizer G a := by
  apply le_antisymm
  · exact sup_le hQ.le_stabilizer (fun x hx => hx.1)
  · intro g hg
    obtain ⟨x, hx, h, hh, rfl⟩ := hQ.exists_mul_pairStab hb hg
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hh)

theorem subgroupOf_stabilizer_normal : (Q.subgroupOf (stabilizer G a)).Normal :=
  ⟨fun n hn g => hQ.normal g g.2 n hn⟩

theorem closure_eq_top [Finite G] [Finite Ω] [IsSimpleGroup G]
    (h2 : IsMultiplyPretransitive G Ω 2) (hQ1 : Q ≠ ⊥) {b : Ω} (hb : b ≠ a) {s : G}
    (hsa : s • a = b) (hs2 : s * s = 1) :
    Subgroup.closure ((Q : Set G) ∪ {s}) = ⊤ := by
  have hs1 : s ≠ 1 := by rintro rfl; rw [one_smul] at hsa; exact hb hsa.symm
  have hle := rankOneNormalClosure_le_generated (stabilizer G a) Q _ s a h2 rfl
    ⟨hs1, by rw [sq, hs2]⟩ (fun h => hb (hsa.symm.trans h)) rfl
    (hQ.subgroupOf_stabilizer_normal)
    (by rw [pairStab_eq_inf_rightConjugate hsa hs2]; exact hQ.disjoint_pairStab hb)
    (by rw [pairStab_eq_inf_rightConjugate hsa hs2]; exact hQ.sup_pairStab_eq_stabilizer hb)
  rw [iSup_rightConjugate_eq_normalClosure] at hle
  have htop : Subgroup.normalClosure (Q : Set G) = ⊤ := by
    rcases (Subgroup.normalClosure_normal (s := (Q : Set G))).eq_bot_or_eq_top with hbot | htop
    · exfalso
      apply hQ1
      rw [eq_bot_iff]
      intro r hr
      have hr' := Subgroup.le_normalClosure hr
      rw [hbot] at hr'
      exact hr'
    · exact htop
  rw [htop] at hle
  exact top_le_iff.mp hle

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
