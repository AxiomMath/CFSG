module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5Norm
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFrame

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly TableB

variable {G0 : Type} [Group G0] [Finite G0]

theorem hcount_of_toral {T : Subgroup G0} {r : ℕ}
    (hSC : ∀ E : Subgroup G0, IsElemAbelian 3 E → 3 ^ r ≤ Nat.card E →
      (∀ g : G0, g ^ 3 = 1 → (∀ e ∈ E, g * e = e * g) → g ∈ E) →
      ∃ c : G0, E = T.map (MulAut.conj c).toMonoidHom)
    (hN : ∀ A : Subgroup G0, A ≤ T → 3 ^ r ≤ Nat.card A → ∀ x ∈ A, x ≠ 1 → NodeCount 3 A x) :
    ∀ B : Subgroup G0, IsElemAbelian 3 B → 3 ^ r ≤ Nat.card B → NormalizesTwoGroup B →
      ∀ x ∈ B, x ≠ 1 → NodeCount 3 B x := by
  intro B hB hcard _ x hx hx1
  obtain ⟨M, hBM, hM, hMsc⟩ :=
    CFSG.StandardType.A6InsideSp.exists_elemAbelian_le_selfCentralizing Nat.prime_three hB
  obtain ⟨c, hc⟩ := hSC M hM (hcard.trans (Subgroup.card_le_of_le hBM))
    (fun g hg3 hgc => hMsc g hgc hg3)
  refine nodeCount_of_map (MulAut.conj c⁻¹) ?_
  have hle : B.map (MulAut.conj c⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨t, ht, htb⟩ := hc ▸ hBM hb
    have : (MulAut.conj c⁻¹).toMonoidHom b = t := by
      rw [← htb]
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact ht
  refine hN _ hle ?_ _ (Subgroup.mem_map_of_mem _ hx) ?_
  · rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective]
    exact hcard
  · intro h
    exact hx1 ((MulAut.conj c⁻¹).injective (h.trans (map_one _).symm))

end CFSG.StandardType.SmallExc

end
