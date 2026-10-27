module

public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.RankThree.PartOne

variable {H : Type*} [Group H] {p : ℕ} {Y X : Subgroup H}

theorem IsStronglyPEmbedded.mem_of_centralizer_le
    (hY : IsStronglyPEmbedded p Y) (hX : Subgroup.centralizer (X : Set H) ≤ Y) {g : H}
    (hp : p ∣ Nat.card (Y ⊓ Subgroup.centralizer
      ((X.map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H) : Subgroup H)) : g ∈ Y := by
  have hcent : Subgroup.centralizer
      ((X.map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H) ≤
      Y.map (MulAut.conj g).toMonoidHom := by
    intro y hy
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * y * g, hX ?_, by
      change (MulAut.conj g) (g⁻¹ * y * g) = y
      rw [MulAut.conj_apply]
      group⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hx
    have h := hy (g * x * g⁻¹) (Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩)
    calc x * (g⁻¹ * y * g) = g⁻¹ * ((g * x * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * x * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * y * g) * x := by group
  have hdvd : p ∣ Nat.card (Y ⊓ Y.map (MulAut.conj g).toMonoidHom : Subgroup H) :=
    hp.trans (Subgroup.card_dvd_of_le (inf_le_inf le_rfl hcent))
  by_contra hg
  exact hY.2.2 g hg hdvd

end CFSG.RankThree.PartOne
