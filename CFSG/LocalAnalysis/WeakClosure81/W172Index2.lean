module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.W172Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem w172_mem_M_of_relIndex_le_two (D : Data G) {g : G}
    (hN : Subgroup.normalizer ((D.T ⊓ conjSubgroup D.M g : Subgroup G) : Set G) ≤ D.M)
    (hi : (conjSubgroup D.M g).relIndex D.T ≤ 2) : g ∈ D.M := by
  classical
  have hS : IsSylowIn 2 D.T D.M := isSylowOf_two_iff_isSylowIn.mp D.sylowM
  set T₁ : Subgroup G := D.T ⊓ conjSubgroup D.M g with hT₁
  have hT₁T : T₁ ≤ D.T := inf_le_left
  have hT₁M : T₁ ≤ conjSubgroup D.M g := inf_le_right
  have hT₁p : IsPGroup 2 T₁ := hS.isPGroup.to_inf_left
  have hUM : conjSubgroup T₁ g⁻¹ ≤ D.M := by
    intro x hx
    have h1 : g⁻¹ * x * g⁻¹⁻¹ ∈ T₁ := mem_conjSubgroup_iff.mp hx
    have h2 : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.mp (hT₁M h1)
    simpa [mul_assoc] using h2
  obtain ⟨k, hkM, hle⟩ :=
    E3.exists_le_conj_of_isSylowIn hS hUM (E3.isPGroup_conjSubgroup hT₁p g⁻¹)
  set S : Subgroup G := conjSubgroup D.T (k * g) with hSdef
  have hT₁S : T₁ ≤ S := by
    have h1 := E3.conjSubgroup_mono_left g hle
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one] at h1
    exact h1
  have hSM : S ≤ conjSubgroup D.M g := by
    intro x hx
    have h1 : (k * g) * x * (k * g)⁻¹ ∈ D.T := mem_conjSubgroup_iff.mp hx
    rw [mem_conjSubgroup_iff]
    have h2 : k * (g * x * g⁻¹) * k⁻¹ ∈ D.M := by
      have := D.sylowM.le h1
      simpa [mul_assoc] using this
    have h3 := D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hkM) h2) hkM
    simpa [mul_assoc] using h3
  have hSp : IsPGroup 2 S := E3.isPGroup_conjSubgroup hS.isPGroup (k * g)
  have hcardS : Nat.card S = Nat.card D.T := E3.card_conjSubgroup D.T (k * g)
  have hcT : T₁.relIndex D.T * Nat.card T₁ = Nat.card D.T := by
    have := Subgroup.relIndex_mul_card (H := T₁) (K := D.T)
    rwa [inf_eq_left.mpr hT₁T] at this
  have hcS : T₁.relIndex S * Nat.card T₁ = Nat.card S := by
    have := Subgroup.relIndex_mul_card (H := T₁) (K := S)
    rwa [inf_eq_left.mpr hT₁S] at this
  have hpos : 0 < Nat.card T₁ := Nat.card_pos
  have hrelS : T₁.relIndex S = T₁.relIndex D.T :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [hcS, hcT, hcardS])
  have hrelT : T₁.relIndex D.T = (conjSubgroup D.M g).relIndex D.T := by
    rw [hT₁, inf_comm]
    exact Subgroup.inf_relIndex_right _ _
  have hidx2 : (T₁.subgroupOf S).index ≤ 2 := by
    have : (T₁.subgroupOf S).index = (conjSubgroup D.M g).relIndex D.T := by
      rw [← hrelT, ← hrelS]
      rfl
    rw [this]
    exact hi
  have hidx0 : (T₁.subgroupOf S).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hnormal : (T₁.subgroupOf S).Normal := by
    have : (T₁.subgroupOf S).index = 1 ∨ (T₁.subgroupOf S).index = 2 := by omega
    rcases this with h | h
    · rw [Subgroup.index_eq_one.mp h]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h
  have hSnorm : S ≤ Subgroup.normalizer (T₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT₁S).mp hnormal
  have hSMM : S ≤ D.M := fun x hx => hN (hSnorm hx)
  obtain ⟨m, hmM, hSm⟩ := E3.exists_le_conj_of_isSylowIn hS hSMM hSp
  have heq : S = conjSubgroup D.T m := by
    exact Subgroup.eq_of_le_of_card_ge hSm ((E3.card_conjSubgroup D.T m).le.trans hcardS.symm.le)
  have h2 : conjSubgroup D.T (k * g * m⁻¹) = D.T := by
    rw [← conjSubgroup_conjSubgroup, ← hSdef, heq, conjSubgroup_conjSubgroup, mul_inv_cancel,
      conjSubgroup_one]
  have h3 : k * g * m⁻¹ ∈ Subgroup.normalizer (D.T : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp h2
  have h4 : k * g * m⁻¹ ∈ D.M := D.normalizer_le h3
  have h5 : g ∈ D.M := by
    have := D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hkM) h4) hmM
    simpa [mul_assoc] using this
  exact h5

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

theorem w172_normalizer_inf_le_M (c : MinCex172 D V₀ V H) {g : G}
    (hW : E3.wClos V 1 D.T ≤ conjSubgroup D.M g) :
    Subgroup.normalizer ((D.T ⊓ conjSubgroup D.M g : Subgroup G) : Set G) ≤ D.M := by
  have hWle : E3.wClos V 1 D.T ≤ D.T ⊓ conjSubgroup D.M g := le_inf (E3.wClos_le 1 D.T) hW
  have hEq : E3.wClos V 1 (D.T ⊓ conjSubgroup D.M g) = E3.wClos V 1 D.T := by
    refine le_antisymm (E3.wClos_mono inf_le_left) (E3.wClos_le_of_forall fun A hA => ?_)
    refine E3.le_wClos ?_
    rw [E3.mem_gammaSet_iff] at hA ⊢
    exact ⟨le_inf hA.1 ((E3.le_wClos (E3.mem_gammaSet_iff.mpr hA)).trans hW), hA.2⟩
  intro y hy
  have hy' := E3.normalizer_le_normalizer_wClos (V := V) (i := 1)
    (D.T ⊓ conjSubgroup D.M g) hy
  rw [hEq] at hy'
  exact c.hyp.normW hy'

theorem w172_mem_M_of_relIndex_le_two (c : MinCex172 D V₀ V H) {g : G}
    (hW : E3.wClos V 1 D.T ≤ conjSubgroup D.M g)
    (hi : (conjSubgroup D.M g).relIndex D.T ≤ 2) : g ∈ D.M :=
  CFSG.LocalAnalysis.WeakClosure81.w172_mem_M_of_relIndex_le_two D
    (c.w172_normalizer_inf_le_M hW) hi

end MinCex172

end CFSG.LocalAnalysis.WeakClosure81

end
