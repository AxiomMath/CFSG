module

public import CFSG.Milestones.ASVolI.H13

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.ChH

@[expose] def m22InvolutionArr : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22]

@[expose] def outerFptFreeArr : Array ℕ :=
  #[1, 0, 3, 2, 5, 4, 7, 6, 10, 11, 8, 9, 14, 15, 12, 13, 19, 18, 17, 16, 23, 22, 21, 20]

@[expose] def outerOctadArr : Array ℕ :=
  #[1, 0, 2, 3, 4, 5, 7, 6, 8, 9, 11, 10, 13, 12, 14, 15, 22, 23, 21, 20, 19, 18, 16, 17]

@[expose] def fptFreeArr : Array ℕ :=
  #[3, 4, 20, 0, 1, 13, 18, 11, 19, 16, 23, 7, 14, 5, 12, 22, 9, 21, 6, 8, 2, 17, 15, 10]

@[expose] def octadArr : Array ℕ :=
  #[22, 1, 6, 14, 20, 12, 2, 7, 8, 17, 10, 11, 5, 23, 3, 15, 18, 9, 16, 19, 4, 21, 0, 13]

theorem inAutOK_m22InvolutionArr : inAutOK m22InvolutionArr = true := by decide +kernel
theorem inAutOK_outerFptFreeArr : inAutOK outerFptFreeArr = true := by decide +kernel
theorem inAutOK_outerOctadArr : inAutOK outerOctadArr = true := by decide +kernel
theorem arr_involutive_m22 : ∀ i < 24, m22InvolutionArr[m22InvolutionArr[i]!]! = i := by
  decide +kernel
theorem arr_involutive_outerFptFree : ∀ i < 24,
    outerFptFreeArr[outerFptFreeArr[i]!]! = i := by decide +kernel
theorem arr_involutive_outerOctad : ∀ i < 24, outerOctadArr[outerOctadArr[i]!]! = i := by
  decide +kernel
theorem arr_involutive_fptFree : ∀ i < 24, fptFreeArr[fptFreeArr[i]!]! = i := by decide +kernel
theorem arr_involutive_octad : ∀ i < 24, octadArr[octadArr[i]!]! = i := by decide +kernel

theorem isOctad_of_synd_eq_zero (O : Finset (Fin 24)) (h8 : O.card = 8)
    (hs : synd (fun i : Fin 24 => if i ∈ O then (1 : ZMod 2) else 0) = 0) : IsOctad O := by
  refine ⟨h8, ?_⟩
  rw [mem_golayC_iff', ← synd_eq_zero_iff]
  have : Multiplicative.toAdd (eY O) = fun i : Fin 24 => if i ∈ O then (1 : ZMod 2) else 0 := by
    funext i
    exact toAdd_eY _ i
  rw [this]
  exact hs

@[expose] def octadOfM22Involution : Finset (Fin 24) := {0, 1, 2, 3, 4, 5, 6, 7}

@[expose] def octadOfOuterInvolution : Finset (Fin 24) := {2, 3, 4, 5, 8, 9, 14, 15}

@[expose] def octadOf2AInvolution : Finset (Fin 24) := {1, 7, 8, 10, 11, 15, 19, 21}

theorem isOctad_octadOf2AInvolution : IsOctad octadOf2AInvolution :=
  isOctad_of_synd_eq_zero _ (by decide +kernel) (by decide +kernel)

theorem hasArr_fix_iff {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (h : HasArr σ a) (i : Fin 24) :
    σ i = i ↔ a[(i : ℕ)]! = (i : ℕ) := by
  rw [← Fin.val_inj, h i]

theorem fixed_iff_outerOctad : ∀ i : Fin 24,
    outerOctadArr[(i : ℕ)]! = (i : ℕ) ↔ i ∈ octadOfOuterInvolution := by decide +kernel

theorem fixed_iff_octad : ∀ i : Fin 24,
    octadArr[(i : ℕ)]! = (i : ℕ) ↔ i ∈ octadOf2AInvolution := by decide +kernel

theorem not_fixed_outerFptFree : ∀ i : Fin 24, outerFptFreeArr[(i : ℕ)]! ≠ (i : ℕ) := by
  decide +kernel

theorem not_fixed_fptFree : ∀ i : Fin 24, fptFreeArr[(i : ℕ)]! ≠ (i : ℕ) := by decide +kernel

theorem outer_arrs_swap_zero_one :
    outerFptFreeArr[0]! = 1 ∧ outerFptFreeArr[1]! = 0 ∧ outerOctadArr[0]! = 1 ∧
      outerOctadArr[1]! = 0 ∧ m22InvolutionArr[0]! = 0 ∧ m22InvolutionArr[1]! = 1 := by
  decide +kernel

theorem card_fixed_act10_m22 :
    ((List.range (2 ^ 10)).filter fun m => act10 m22InvolutionArr m == m).length = 2 ^ 6 := by
  decide +kernel
theorem card_fixed_actC10_m22 :
    ((List.range (2 ^ 10)).filter fun m => actC10 m22InvolutionArr m == m).length = 2 ^ 6 := by
  decide +kernel
theorem card_fixed_act10_outerFptFree :
    ((List.range (2 ^ 10)).filter fun m => act10 outerFptFreeArr m == m).length = 2 ^ 5 := by
  decide +kernel
theorem card_fixed_actC10_outerFptFree :
    ((List.range (2 ^ 10)).filter fun m => actC10 outerFptFreeArr m == m).length = 2 ^ 5 := by
  decide +kernel
theorem card_fixed_act10_outerOctad :
    ((List.range (2 ^ 10)).filter fun m => act10 outerOctadArr m == m).length = 2 ^ 7 := by
  decide +kernel
theorem card_fixed_actC10_outerOctad :
    ((List.range (2 ^ 10)).filter fun m => actC10 outerOctadArr m == m).length = 2 ^ 7 := by
  decide +kernel
theorem card_fixed_act11_octad :
    ((List.range (2 ^ 11)).filter fun m => act11 octadArr m == m).length = 2 ^ 7 := by
  decide +kernel
theorem card_fixed_actC11_octad :
    ((List.range (2 ^ 11)).filter fun m => actC11 octadArr m == m).length = 2 ^ 7 := by
  decide +kernel
theorem card_fixed_act11_fptFree :
    ((List.range (2 ^ 11)).filter fun m => act11 fptFreeArr m == m).length = 2 ^ 6 := by
  decide +kernel
theorem card_fixed_actC11_fptFree :
    ((List.range (2 ^ 11)).filter fun m => actC11 fptFreeArr m == m).length = 2 ^ 6 := by
  decide +kernel

end CFSG.Quasithin.AppendixH.H14
