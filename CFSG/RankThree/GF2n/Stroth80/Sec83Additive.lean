module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem card_sup_mul_card_inf_addSubgroup {N : Type*} [AddCommGroup N] (A B : AddSubgroup N) :
    Nat.card ↥(A ⊔ B : AddSubgroup N) * Nat.card ↥(A ⊓ B : AddSubgroup N) =
      Nat.card ↥A * Nat.card ↥B := by
  have hA : B.relIndex A * Nat.card ↥(A ⊓ B : AddSubgroup N) = Nat.card ↥A := by
    have h := AddSubgroup.relIndex_mul_card B A
    rwa [inf_comm] at h
  have hS : B.relIndex A * Nat.card ↥B = Nat.card ↥(A ⊔ B : AddSubgroup N) := by
    have h := AddSubgroup.relIndex_mul_card B (A ⊔ B)
    rw [inf_eq_left.mpr (le_sup_right : B ≤ A ⊔ B), AddSubgroup.relIndex_sup_right A B] at h
    exact h
  calc Nat.card ↥(A ⊔ B : AddSubgroup N) * Nat.card ↥(A ⊓ B : AddSubgroup N)
      = (B.relIndex A * Nat.card ↥B) * Nat.card ↥(A ⊓ B : AddSubgroup N) := by rw [hS]
    _ = (B.relIndex A * Nat.card ↥(A ⊓ B : AddSubgroup N)) * Nat.card ↥B := by ring
    _ = Nat.card ↥A * Nat.card ↥B := by rw [hA]

theorem sec83_lower_additive {M : Type*} [AddCommGroup M] [Finite M] (δ ε : M →+ M)
    (hcomm : ∀ a, ε (δ a) = δ (ε a)) {V V₁ W₁ : AddSubgroup M}
    (hV : V = ε.range) (hVV₁ : V ≤ V₁) (hV₁W₁ : V₁ ≤ W₁) (hW₁ : W₁ ≤ ε.ker)
    (hδV₁ : ∀ a ∈ V₁, δ a ∈ V₁) (hδW₁ : ∀ a ∈ W₁, δ a ∈ W₁) :
    Nat.card ↥(V.map δ) ^ 2 * Nat.card ↥(W₁.map δ ⊔ V₁) ≤ Nat.card ↥δ.range * Nat.card ↥V₁ := by
  have hcd : ε.comp δ = δ.comp ε := AddMonoidHom.ext fun a => hcomm a
  have hDV : δ.range.map ε = V.map δ := by
    rw [hV, AddMonoidHom.map_range, AddMonoidHom.map_range, hcd]
  have hd : Nat.card ↥(V.map δ) * Nat.card ↥(δ.range ⊓ ε.ker) = Nat.card ↥δ.range := by
    have h := AddSubgroup.relIndex_mul_card ε.ker δ.range
    rw [AddSubgroup.relIndex_ker, inf_comm, hDV] at h
    exact h
  have hW : W₁.map δ ≤ δ.range ⊓ ε.ker := by
    rintro x ⟨w, hw, rfl⟩
    exact ⟨AddMonoidHom.mem_range.mpr ⟨w, rfl⟩, hW₁ (hδW₁ w hw)⟩
  have hPle : Nat.card ↥(W₁.map δ) ≤ Nat.card ↥(δ.range ⊓ ε.ker) :=
    AddSubgroup.card_le_of_le hW
  have hSI : Nat.card ↥(W₁.map δ ⊔ V₁) * Nat.card ↥(W₁.map δ ⊓ V₁) =
      Nat.card ↥(W₁.map δ) * Nat.card ↥V₁ :=
    card_sup_mul_card_inf_addSubgroup _ _
  have hVI : V.map δ ≤ W₁.map δ ⊓ V₁ := by
    have h1 : V₁.map δ ≤ W₁.map δ := AddSubgroup.map_mono hV₁W₁
    have h2 : V₁.map δ ≤ V₁ := by
      rintro x ⟨v, hv, rfl⟩
      exact hδV₁ v hv
    have h3 : V.map δ ≤ V₁.map δ := AddSubgroup.map_mono hVV₁
    exact h3.trans (le_inf h1 h2)
  have hIle : Nat.card ↥(V.map δ) ≤ Nat.card ↥(W₁.map δ ⊓ V₁) :=
    AddSubgroup.card_le_of_le hVI
  have hd' : Nat.card ↥(V.map δ) * Nat.card ↥(W₁.map δ) ≤ Nat.card ↥δ.range := by
    rw [← hd]
    exact Nat.mul_le_mul_left _ hPle
  calc Nat.card ↥(V.map δ) ^ 2 * Nat.card ↥(W₁.map δ ⊔ V₁)
      = Nat.card ↥(W₁.map δ ⊔ V₁) * (Nat.card ↥(V.map δ) * Nat.card ↥(V.map δ)) := by ring
    _ ≤ Nat.card ↥(W₁.map δ ⊔ V₁) * (Nat.card ↥(V.map δ) * Nat.card ↥(W₁.map δ ⊓ V₁)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hIle)
    _ = Nat.card ↥(V.map δ) * (Nat.card ↥(W₁.map δ ⊔ V₁) * Nat.card ↥(W₁.map δ ⊓ V₁)) := by
        ring
    _ = Nat.card ↥(V.map δ) * (Nat.card ↥(W₁.map δ) * Nat.card ↥V₁) := by rw [hSI]
    _ = Nat.card ↥(V.map δ) * Nat.card ↥(W₁.map δ) * Nat.card ↥V₁ := by ring
    _ ≤ Nat.card ↥δ.range * Nat.card ↥V₁ := Nat.mul_le_mul_right _ hd'

end CFSG.RankThree.GF2n.Stroth80
