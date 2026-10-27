module

public import CFSG.Quasithin.Background.HModChk
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Milestones.ASVolI.H1
public import CFSG.Quasithin.Background.HCocBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.Coc

theorem maskSub_cons (n b : ℕ) (l : List ℕ) :
    maskSub n (b :: l) = maskSub n l ⊔ maskSub n [b] := by
  have hb : b ∈ combos [b] := by simp [combos]
  have hb' : b ∈ combos (b :: l) := by
    rw [combos]
    exact List.mem_append_right _ (List.mem_map.2 ⟨0, zero_mem_combos l, Nat.zero_xor b⟩)
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro v ⟨m, hm, rfl⟩
    rw [combos, List.mem_append, List.mem_map] at hm
    rcases hm with hm | ⟨m', hm', rfl⟩
    · exact Subgroup.mem_sup_left (toW_mem_maskSub hm)
    · rw [toW_xor]
      exact Subgroup.mul_mem_sup (toW_mem_maskSub hm') (toW_mem_maskSub hb)
  · rintro v ⟨m, hm, rfl⟩
    exact toW_mem_maskSub (by rw [combos]; exact List.mem_append_left _ hm)
  · rintro v ⟨m, hm, rfl⟩
    have h : m = 0 ∨ m = b := by simpa [combos] using hm
    rcases h with rfl | rfl
    · exact toW_mem_maskSub (zero_mem_combos (b :: l))
    · exact toW_mem_maskSub hb'

theorem maskSub_mono_of_combos {n : ℕ} {l₁ l₂ : List ℕ} (h : ∀ m ∈ combos l₁, m ∈ combos l₂) :
    maskSub n l₁ ≤ maskSub n l₂ := by
  rintro v ⟨m, hm, rfl⟩
  exact toW_mem_maskSub (h m hm)

theorem maskSub_eq_of_combos {n : ℕ} {l₁ l₂ : List ℕ} (h₁ : ∀ m ∈ combos l₁, m ∈ combos l₂)
    (h₂ : ∀ m ∈ combos l₂, m ∈ combos l₁) : maskSub n l₁ = maskSub n l₂ :=
  le_antisymm (maskSub_mono_of_combos h₁) (maskSub_mono_of_combos h₂)

theorem rk_maskSub {n : ℕ} {l : List ℕ} (hl : ∀ a ∈ l, a < 2 ^ n) (hnd : (combos l).Nodup) :
    rk ↥(maskSub n l) = l.length := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [rk, card_maskSub hl hnd, padicValNat.prime_pow]

end CFSG.ASVolI.H16
