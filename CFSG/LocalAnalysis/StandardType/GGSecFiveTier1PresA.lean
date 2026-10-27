module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.ClassicalInvolution.WeakCT.Main

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.WeakCT

section PresAAux

variable {G : Type} [Group G] [Finite G]

private theorem ggPresentsG0_typeA_of_system_aux {n f : ℕ} (hn : 3 ≤ n) (hq : 4 ≤ 2 ^ f)
    {H : Subgroup G} {U : Fin n → Subgroup ↥H}
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      ∃ W, LinearBlockStandardPair (GaloisField 2 f) W (U i) (U j))
    (hgen : ⨆ i, U i = ⊤) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G,
      GGPresentsG0 H (SpecialLinear.rootDatum n (GaloisField 2 f)) .PSL (n + 1) f ψ := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with hf0 | h
    · subst hf0
      norm_num at hq
    · exact h
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ψ₀, hsurj, hker, hqs, hmodel⟩ :=
    weakCT_recognition_of_pairs (GaloisField 2 f) 2 f Nat.prime_two hK hq hn
      hcomm hpair hgen
  refine ⟨H.subtype.comp ψ₀, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, hmodel⟩
  ·
    exact ⟨Nat.prime_two, hf, by omega, fun h => by simp only [Prod.mk.injEq] at h; omega,
      fun h => by simp only [Prod.mk.injEq] at h; omega⟩
  ·
    show 2 ≤ (SpecialLinear.rootDatum n (GaloisField 2 f)).rank
    exact (show 2 ≤ n from by omega)
  ·
    rw [← MonoidHom.map_range H.subtype ψ₀, MonoidHom.range_eq_top_of_surjective ψ₀ hsurj,
      Subgroup.map_top, Subgroup.range_subtype]
  ·
    have hk : (H.subtype.comp ψ₀).ker = ψ₀.ker :=
      MonoidHom.ker_comp_of_injective (f := ψ₀) (g := H.subtype) Subtype.val_injective
    exact (le_of_eq hk).trans hker
  ·
    exact Group.isPerfect_def.mp hqs.1

end PresAAux

section PresA

variable {G : Type} [Group G] [Finite G]

theorem ggPresentsG0_typeA_of_system {n f : ℕ} (hn : 3 ≤ n) (hq : 4 ≤ 2 ^ f) {H : Subgroup G}
    {U : Fin n → Subgroup ↥H}
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      ∃ W, LinearBlockStandardPair (GaloisField 2 f) W (U i) (U j))
    (hgen : ⨆ i, U i = ⊤) :
    ∃ ψ : (ggU .PSL (n + 1) f).K →* G,
      GGPresentsG0 H (ggU .PSL (n + 1) f).D .PSL (n + 1) f ψ := by
  obtain ⟨ψ, hψ⟩ := ggPresentsG0_typeA_of_system_aux hn hq hcomm hpair hgen
  refine ⟨ψ, ?_⟩
  show GGPresentsG0 H (ggU .PSL (n + 1) f).D .PSL (n + 1) f ψ
  exact hψ

end PresA

end CFSG.StandardType

end
