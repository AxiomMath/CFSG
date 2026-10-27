module

public import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.StandardType.SylowPair

variable {Q : Type*} [Group Q]

@[expose] def pairClosure (P : Subgroup Q) (g : Q) : Subgroup Q :=
  P ⊔ P.map (MulAut.conj g).toMonoidHom

theorem conj_pairClosure_le {P N Y : Subgroup Q} (hN : N ≤ Subgroup.normalizer (P : Set Q))
    (hPY : P ≤ Y) {a b g y : Q} (ha : a ∈ N) (hb : b ∈ N) (hy : y ∈ Y) (h : y = a * g * b) :
    (pairClosure P g).map (MulAut.conj a).toMonoidHom ≤ Y := by
  have hg : g = a⁻¹ * y * b⁻¹ := by rw [h]; group
  unfold pairClosure
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    exact hPY ((Subgroup.mem_normalizer_iff.1 (hN ha) r).1 hr)
  · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    have hb' : b⁻¹ * r * b ∈ P := by
      have := (Subgroup.mem_normalizer_iff.1 (hN (N.inv_mem hb)) r).1 hr
      simpa using this
    have hmem : y * (b⁻¹ * r * b) * y⁻¹ ∈ Y :=
      Y.mul_mem (Y.mul_mem hy (hPY hb')) (Y.inv_mem hy)
    have e : (MulAut.conj a).toMonoidHom ((MulAut.conj g).toMonoidHom r) =
        y * (b⁻¹ * r * b) * y⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hg]
      group
    rw [e]
    exact hmem

theorem le_or_le_of_subset_union {Y M₁ M₂ : Subgroup Q}
    (h : (Y : Set Q) ⊆ (M₁ : Set Q) ∪ (M₂ : Set Q)) : Y ≤ M₁ ∨ Y ≤ M₂ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨y₁, hy₁, hy₁M⟩ := SetLike.not_le_iff_exists.1 h1
  obtain ⟨y₂, hy₂, hy₂M⟩ := SetLike.not_le_iff_exists.1 h2
  have hy₁' : y₁ ∈ M₂ := (h hy₁).resolve_left hy₁M
  have hy₂' : y₂ ∈ M₁ := (h hy₂).resolve_right hy₂M
  rcases h (Y.mul_mem hy₁ hy₂) with hm | hm
  · exact hy₁M (by simpa using M₁.mul_mem hm (M₁.inv_mem hy₂'))
  · exact hy₂M (by simpa using M₂.mul_mem (M₂.inv_mem hy₁') hm)

end CFSG.StandardType.SylowPair
