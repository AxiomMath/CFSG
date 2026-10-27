module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C621b
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B4
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588B2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G}

theorem mem_W_of_mem_L {m : Mz614 Dat} (h620 : m.C620) {x : G} (hxL : x ∈ m.L)
    (hxB : ∀ b ∈ m.A ⊓ m.L, x * b * x⁻¹ ∈ m.A ⊓ m.L) : x ∈ m.W :=
  mem_normalizer_A_of_mem_normalizer_E h620 hxL (mem_normalizer_of_forward_uc6 hxB)

theorem coe_conj_L {m : Mz614 Dat} (x y : ↥m.L) :
    (x : G) * (y : G) * (x : G)⁻¹ = ((x * y * x⁻¹ : ↥m.L) : G) := by
  simp

variable (m : Mz614 Dat)

theorem map_conj_Z_of_mem_L {n : G} (hn : n ∈ m.L) :
    m.Z.map (MulAut.conj n).toMonoidHom = m.Z := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have := m.Z_comm_L hz hn
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← this]
    group
    exact hz
  · intro hx
    refine ⟨x, hx, ?_⟩
    have := m.Z_comm_L hx hn
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← this]
    group

theorem map_conj_pair (h620 : m.C620) {Z₂ Z₃ : Subgroup G} (hZ₂L : Z₂ ≤ m.A ⊓ m.L)
    (hZ₃L : Z₃ ≤ m.A ⊓ m.L) (hZ₂1 : Z₂ ≠ ⊥) (hZ₃1 : Z₃ ≠ ⊥) (hZ₂₃ : Z₂ ⊓ Z₃ = ⊥)
    (horb : ∀ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = m.Z ∨
      m.Z.map (MulAut.conj w).toMonoidHom = Z₂ ∨ m.Z.map (MulAut.conj w).toMonoidHom = Z₃)
    (h₂ : ∃ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = Z₂)
    (h₃ : ∃ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = Z₃) {n : G} (hn : n ∈ m.L ⊓ m.W) :
    (Z₂.map (MulAut.conj n).toMonoidHom = Z₂ ∧ Z₃.map (MulAut.conj n).toMonoidHom = Z₃) ∨
      (Z₂.map (MulAut.conj n).toMonoidHom = Z₃ ∧ Z₃.map (MulAut.conj n).toMonoidHom = Z₂) := by
  have hZL : ∀ X : Subgroup G, X ≤ m.A ⊓ m.L → X ≠ ⊥ → X ≠ m.Z := by
    intro X hX hX1 hXZ
    apply hX1
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ m.Z ⊓ m.L := ⟨hXZ ▸ hx, (hX hx).2⟩
    rwa [inf_eq_bot_of_not_le_of_card_prime m.hr m.card_Z h620.2] at h1
  have hne : Z₂ ≠ Z₃ := by
    intro h
    apply hZ₂1
    rw [← inf_idem Z₂]
    nth_rewrite 2 [h]
    exact hZ₂₃
  have himg : ∀ (X : Subgroup G), X ≤ m.A ⊓ m.L → X ≠ ⊥ →
      (∃ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = X) →
      X.map (MulAut.conj n).toMonoidHom = Z₂ ∨ X.map (MulAut.conj n).toMonoidHom = Z₃ := by
    rintro X hX hX1 ⟨w, hw, rfl⟩
    rw [← map_conj_mul_uc6]
    rcases horb (n * w) (m.W.mul_mem hn.2 hw) with h | h | h
    · exfalso
      rw [map_conj_mul_uc6] at h
      have h' : m.Z.map (MulAut.conj w).toMonoidHom = m.Z := by
        apply map_conj_injective_uc6 n
        simp only
        rw [h, m.map_conj_Z_of_mem_L hn.1]
      exact hZL _ hX hX1 h'
    · exact Or.inl h
    · exact Or.inr h
  have hn2 := himg Z₂ hZ₂L hZ₂1 h₂
  have hn3 := himg Z₃ hZ₃L hZ₃1 h₃
  have hinj := map_conj_injective_uc6 n
  rcases hn2 with h2 | h2 <;> rcases hn3 with h3 | h3
  · exact absurd (hinj (h2.trans h3.symm)) hne
  · exact Or.inl ⟨h2, h3⟩
  · exact Or.inr ⟨h2, h3⟩
  · exact absurd (hinj (h2.trans h3.symm)) hne

theorem map_conj_sq_pair (h620 : m.C620) {Z₂ Z₃ : Subgroup G} (hZ₂L : Z₂ ≤ m.A ⊓ m.L)
    (hZ₃L : Z₃ ≤ m.A ⊓ m.L) (hZ₂1 : Z₂ ≠ ⊥) (hZ₃1 : Z₃ ≠ ⊥) (hZ₂₃ : Z₂ ⊓ Z₃ = ⊥)
    (horb : ∀ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = m.Z ∨
      m.Z.map (MulAut.conj w).toMonoidHom = Z₂ ∨ m.Z.map (MulAut.conj w).toMonoidHom = Z₃)
    (h₂ : ∃ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = Z₂)
    (h₃ : ∃ w ∈ m.W, m.Z.map (MulAut.conj w).toMonoidHom = Z₃) {n : G} (hn : n ∈ m.L ⊓ m.W) :
    Z₂.map (MulAut.conj (n ^ 2)).toMonoidHom = Z₂ := by
  rw [sq, map_conj_mul_uc6]
  rcases m.map_conj_pair h620 hZ₂L hZ₃L hZ₂1 hZ₃1 hZ₂₃ horb h₂ h₃ hn with ⟨h2, -⟩ | ⟨h2, h3⟩
  · rw [h2, h2]
  · rw [h2, h3]

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
