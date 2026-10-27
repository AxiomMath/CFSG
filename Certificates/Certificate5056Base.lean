
module

public import CFSG.GH74.GLS.C3.Layer2.L5C2fInputs

@[expose] public section

open CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus Equiv Perm

namespace CertificateChecks.Batch5056

private theorem foldl16_inj : ∀ (l₁ l₂ : List Nat) (a b : Nat), l₁.length = l₂.length →
    (∀ x ∈ l₁, x < 16) → (∀ x ∈ l₂, x < 16) →
    l₁.foldl (fun acc d => acc * 16 + d) a = l₂.foldl (fun acc d => acc * 16 + d) b →
      a = b ∧ l₁ = l₂
  | [], [], _, _, _, _, _, h => ⟨h, rfl⟩
  | x :: l₁, y :: l₂, a, b, hl, h₁, h₂, h => by
    simp only [List.foldl_cons] at h
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    obtain ⟨e, rfl⟩ := foldl16_inj l₁ l₂ _ _ hl (fun z hz => h₁ z (List.mem_cons_of_mem _ hz))
      (fun z hz => h₂ z (List.mem_cons_of_mem _ hz)) h
    have hx := h₁ x List.mem_cons_self
    have hy := h₂ y List.mem_cons_self
    have hab : a = b := by omega
    have hxy : x = y := by omega
    exact ⟨hab, by rw [hxy]⟩

private theorem codeP16_injective : Function.Injective codeP16 := by
  intro p q h
  unfold codeP16 at h
  rw [← List.foldl_map (f := fun i => (p i).val) (g := fun acc d => acc * 16 + d),
    ← List.foldl_map (f := fun i => (q i).val) (g := fun acc d => acc * 16 + d)] at h
  obtain ⟨-, e⟩ := foldl16_inj _ _ 0 0 (by simp) (by simp) (by simp) h
  ext i
  exact (List.map_inj_left.1 e) i (List.mem_finRange i)

private theorem sh0_codes : (sh0M.map sh0Code).Nodup := by
  unfold sh0M
  exact (Sh0L_nodup.pmap fun _ _ _ _ h => congrArg Subtype.val h).map
    fun _ _ h => Subtype.ext (codeP16_injective h)

end CertificateChecks.Batch5056

