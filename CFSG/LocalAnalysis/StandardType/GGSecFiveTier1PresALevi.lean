module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.ClassicalInvolution.WeakCT.Main

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.WeakCT

section PresALeviAux

variable {G : Type} [Group G] [Finite G]

private theorem ggPresentsG0_typeA_of_system_levi_aux {n f : ℕ} (hn : 3 ≤ n) (hq : 4 ≤ 2 ^ f)
    {H : Subgroup G} {U : Fin n → Subgroup ↥H}
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      ∃ W, LinearBlockStandardPair (GaloisField 2 f) W (U i) (U j))
    (hgen : ⨆ i, U i = ⊤) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G,
      GGPresentsG0 H (SpecialLinear.rootDatum n (GaloisField 2 f)) .PSL (n + 1) f ψ ∧
        ∀ k : Fin n,
          (CFSG.LieType.CurtisTits.rankOne
            (SpecialLinear.rootDatum n (GaloisField 2 f)).rootGroup k).map ψ =
            (U k).map H.subtype := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with hf0 | h
    · subst hf0
      norm_num at hq
    · exact h
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK4 : 4 ≤ Nat.card (GaloisField 2 f) := by rw [hK]; exact hq
  obtain ⟨F, hF⟩ :=
    exists_ctFamily_of_pairs (K := GaloisField 2 f) hK4 (by omega) hcomm hpair
  have hgen' : ⨆ i, (F.ι i).range = ⊤ := by
    simp only [fun i => (hF i).1]
    exact hgen
  have hnt : ∃ i, ∃ A, F.ι i A ≠ 1 := by
    obtain ⟨s, hs⟩ := exists_unit_ne_one (by omega : 3 ≤ Nat.card (GaloisField 2 f))
    refine ⟨⟨0, by omega⟩, torusHom (GaloisField 2 f) s, fun h => hs ?_⟩
    apply torusHom_injective
    rw [map_one]
    exact (hF ⟨0, by omega⟩).2 (h.trans (map_one _).symm)
  obtain ⟨ψ₀, hblocks, hsurj, hker, hqs, -, hmodel⟩ :=
    exists_recognition (K := GaloisField 2 f) hn Nat.prime_two hf hK F hgen' hnt
  have hlevi : ∀ k : Fin n,
      (CFSG.LieType.CurtisTits.rankOne
        (SpecialLinear.rootDatum n (GaloisField 2 f)).rootGroup k).map ψ₀ = U k := by
    intro k
    show (CFSG.LieType.CurtisTits.rankOne
      (SpecialLinear.rootGroup n (GaloisField 2 f)) k).map ψ₀ = U k
    rw [rankOne_eq_range, MonoidHom.map_range]
    rw [show ψ₀.comp (blockSL2 (GaloisField 2 f) n k) = F.ι k from MonoidHom.ext (hblocks k)]
    exact (hF k).1
  refine ⟨H.subtype.comp ψ₀, ?_, ?_⟩
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, hmodel⟩
    ·
      exact ⟨Nat.prime_two, hf, by omega, fun h => by
          simp only [Prod.mk.injEq] at h; omega,
        fun h => by simp only [Prod.mk.injEq] at h; omega⟩
    ·
      show 2 ≤ (SpecialLinear.rootDatum n (GaloisField 2 f)).rank
      exact (show 2 ≤ n from by omega)
    ·
      rw [← MonoidHom.map_range H.subtype ψ₀,
        MonoidHom.range_eq_top_of_surjective ψ₀ hsurj,
        Subgroup.map_top, Subgroup.range_subtype]
    ·
      have hk : (H.subtype.comp ψ₀).ker = ψ₀.ker :=
        MonoidHom.ker_comp_of_injective (f := ψ₀) (g := H.subtype) Subtype.val_injective
      exact (le_of_eq hk).trans hker
    ·
      exact Group.isPerfect_def.mp hqs.1
  ·
    intro k
    rw [← Subgroup.map_map, hlevi k]

end PresALeviAux

section PresALevi

variable {G : Type} [Group G] [Finite G]

theorem ggPresentsG0_typeA_of_system_levi {n f : ℕ} (hn : 3 ≤ n) (hq : 4 ≤ 2 ^ f)
    {H : Subgroup G} {U : Fin n → Subgroup ↥H}
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      ∃ W, LinearBlockStandardPair (GaloisField 2 f) W (U i) (U j))
    (hgen : ⨆ i, U i = ⊤) :
    ∃ ψ : (ggU .PSL (n + 1) f).K →* G,
      GGPresentsG0 H (ggU .PSL (n + 1) f).D .PSL (n + 1) f ψ ∧
        ∃ σ : Fin (ggU .PSL (n + 1) f).D.rank ≃ Fin n, (∀ k, ((σ k : Fin n) : ℕ) = k) ∧
          ∀ k, (CFSG.LieType.CurtisTits.rankOne (ggU .PSL (n + 1) f).D.rootGroup k).map ψ =
            (U (σ k)).map H.subtype := by
  obtain ⟨ψ, hψ, hl⟩ := ggPresentsG0_typeA_of_system_levi_aux hn hq hcomm hpair hgen
  exact ⟨ψ, hψ, Equiv.refl _, fun k => rfl, hl⟩

end PresALevi

end CFSG.StandardType

end
