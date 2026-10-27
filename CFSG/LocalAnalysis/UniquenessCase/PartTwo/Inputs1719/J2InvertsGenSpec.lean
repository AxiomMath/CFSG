module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import Certificates.Certificate17264
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallOddCore
open CFSG.ComponentClassification.J2Cover

@[expose] def InvertsGenModel : Prop :=
  ∀ r ∈ [permA, permTwoA, permU], ∃ x ∈ P, ∃ g ∈ P,
    (orderOf (x⁻¹ * (r * x * r⁻¹)) = 5 ∨ orderOf (x⁻¹ * (r * x * r⁻¹)) = 7) ∧
      Subgroup.closure {x⁻¹ * (r * x * r⁻¹), g * (x⁻¹ * (r * x * r⁻¹)) * g⁻¹} = P

private theorem ivg_rep_foldl {G : Array (Array ℕ)} (g : ℕ → Equiv.Perm (Fin 315))
    (hg : ∀ i < G.size, Rep 315 G[i]! (g i)) :
    ∀ (w : List ℕ), (∀ i ∈ w, i < G.size) → ∀ (acc : Array ℕ) (x : Equiv.Perm (Fin 315)),
      Rep 315 acc x →
        Rep 315 (w.foldl (fun acc i => compA 315 acc G[i]!) acc) (w.foldl (fun x i => x * g i) x)
  | [], _, _, _, h => h
  | i :: w, hw, acc, x, h => by
      simp only [List.foldl_cons]
      exact ivg_rep_foldl g hg w (fun j hj => hw j (List.mem_cons_of_mem _ hj)) _ _
        (rep_compA h (hg i (hw i List.mem_cons_self)))

private theorem ivg_foldl_mem {H : Subgroup (Equiv.Perm (Fin 315))} (g : ℕ → Equiv.Perm (Fin 315)) :
    ∀ (w : List ℕ), (∀ i ∈ w, g i ∈ H) → ∀ x ∈ H, w.foldl (fun x i => x * g i) x ∈ H
  | [], _, _, hx => hx
  | i :: w, hw, x, hx => by
      simp only [List.foldl_cons]
      exact ivg_foldl_mem g w (fun j hj => hw j (List.mem_cons_of_mem _ hj)) _
        (H.mul_mem hx (hw i List.mem_cons_self))

private theorem ivg_word_mem {t t₂ u : Array ℕ} {Y Y₂ U : Equiv.Perm (Fin 315)} (hY : Rep 315 t Y)
    (hY₂ : Rep 315 t₂ Y₂) {w : List ℕ} (hw : w.all (· < 2) = true) (hU : Rep 315 u U)
    (he : eqA 315 (ivgEval #[t, t₂] w) u = true) : U ∈ Subgroup.closure {Y, Y₂} := by
  let g : ℕ → Equiv.Perm (Fin 315) := fun j => if j = 0 then Y else Y₂
  have hg : ∀ i < (#[t, t₂] : Array (Array ℕ)).size,
      Rep 315 (#[t, t₂] : Array (Array ℕ))[i]! (g i) := by
    intro i hi
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
    interval_cases i
    · simpa [g] using hY
    · simpa [g] using hY₂
  have hw' : ∀ i ∈ w, i < (#[t, t₂] : Array (Array ℕ)).size := by
    intro i hi
    have := List.all_eq_true.1 hw i hi
    simpa using this
  have h1 := ivg_rep_foldl g hg w hw' (idA 315) 1 rep_idA
  have h2 : w.foldl (fun x i => x * g i) 1 = U := eq_of_eqA h1 hU he
  rw [← h2]
  refine ivg_foldl_mem g w (fun i _ => ?_) 1 (Subgroup.one_mem _)
  by_cases h0 : i = 0
  · simp only [g, h0, if_true]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · simp only [g, h0, if_false]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem invertsGenModel_of_check (hc : ivgCheck = true) :
    InvertsGenModel := by
  have key : ∀ i < 3, ∀ r : Equiv.Perm (Fin 315), Rep 315 invReps[i]! r → r⁻¹ = r →
      (ivgOrd[i]! = 5 ∨ ivgOrd[i]! = 7) →
      ∃ x ∈ P, ∃ g ∈ P,
        (orderOf (x⁻¹ * (r * x * r⁻¹)) = 5 ∨ orderOf (x⁻¹ * (r * x * r⁻¹)) = 7) ∧
          Subgroup.closure {x⁻¹ * (r * x * r⁻¹), g * (x⁻¹ * (r * x * r⁻¹)) * g⁻¹} = P := by
    intro i hi r hr hrinv hp
    have h := List.all_eq_true.1 hc i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hxinv, hxP⟩, hkinv⟩, hkP⟩, hyP⟩, hord⟩, hwa0⟩, hwb0⟩, hwa⟩, hwb⟩ := h
    obtain ⟨hX, hXinv⟩ := rep_permOfArr hxinv
    obtain ⟨hK, hKinv⟩ := rep_permOfArr hkinv
    have hy : Rep 315 (ivgY i)
        ((permOfArr 315 ivgX[i]!)⁻¹ * (r * permOfArr 315 ivgX[i]! * r⁻¹)) := by
      have := rep_compA hXinv (rep_compA hr (rep_compA hX hr))
      rw [hrinv, mul_assoc r]
      exact this
    have hy2 : Rep 315 (ivgY2 i) (permOfArr 315 ivgK[i]! *
        ((permOfArr 315 ivgX[i]!)⁻¹ * (r * permOfArr 315 ivgX[i]! * r⁻¹)) *
          (permOfArr 315 ivgK[i]!)⁻¹) := by
      have := rep_compA hK (rep_compA hy hKinv)
      rw [mul_assoc]
      exact this
    have hYP := (mem_P_iff hy).1 hyP
    have hKP := (mem_P_iff hK).1 hkP
    refine ⟨_, (mem_P_iff hX).1 hxP, _, hKP, ?_, ?_⟩
    · have hpos : 0 < ivgOrd[i]! := by rcases hp with h | h <;> rw [h] <;> norm_num
      rw [(ordTest_iff_perm (rep_arrTable (by norm_num) hy) hpos).1 hord]
      exact hp
    · apply le_antisymm
      · rw [Subgroup.closure_le]
        intro z hz
        rcases hz with rfl | rfl
        · exact hYP
        · exact P.mul_mem (P.mul_mem hKP hYP) (P.inv_mem hKP)
      · rw [P, Subgroup.closure_le]
        intro z hz
        rcases hz with rfl | rfl
        · exact ivg_word_mem hy hy2 hwa0 rep_permA hwa
        · exact ivg_word_mem hy hy2 hwb0 rep_permB hwb
  have hAinv : permA⁻¹ = permA := by
    have h2 := pow_orderOf_eq_one permA
    rw [orderOf_permA, pow_two] at h2
    exact inv_eq_of_mul_eq_one_right h2
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact key 0 (by norm_num) _ rep_permA hAinv (Or.inl rfl)
  · exact key 1 (by norm_num) _ rep_permTwoA permTwoA_inv (Or.inl rfl)
  · exact key 2 (by norm_num) _ rep_permU permU_inv (Or.inr rfl)

theorem invertsGenModel_holds :
    InvertsGenModel :=
  invertsGenModel_of_check Certificates.certificate17264

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact
