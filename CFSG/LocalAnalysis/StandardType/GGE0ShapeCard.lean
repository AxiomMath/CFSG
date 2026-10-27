module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeCardAux

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem a1_centralizer_card
    {L : Type} [Field L]
    (B J : Subgroup (ModGL .E6 L)) [Finite B]
    (hBT : B ≤ torusGroup .E6 L) (hB3 : ∀ b ∈ B, b ^ 3 = 1)
    (α : Fin Tag.E6.rank → ℤ) (hJ : J ≤ rootSpan .E6 L {α, -α}) :
    Nat.card B ≤ 3 * Nat.card
      (B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L)) : Subgroup (ModGL .E6 L)) := by
  haveI : Finite ↥(B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L))) :=
    finite_inf_centralizer B J
  by_cases hα : IsRoot .E6 α
  · have hb := rank_one_bound B hBT hB3 α hα
    have hcent : Subgroup.centralizer
        (rootSpan .E6 L ({α, -α} : Set (Fin Tag.E6.rank → ℤ)) : Set (ModGL .E6 L)) ≤
        Subgroup.centralizer (J : Set (ModGL .E6 L)) := Subgroup.centralizer_le hJ
    have hsub : B ⊓ Subgroup.centralizer
        (rootSpan .E6 L ({α, -α} : Set (Fin Tag.E6.rank → ℤ)) : Set (ModGL .E6 L)) ≤
        B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L)) :=
      inf_le_inf_left _ hcent
    exact hb.trans (Nat.mul_le_mul_left 3 (Subgroup.card_le_of_le hsub))
  · have hb := rank_one_bound B hBT hB3 (Pi.single (0 : Fin Tag.E6.rank) 1)
      (IsRoot.basis (0 : Fin Tag.E6.rank))
    have hspan := rootSpan_pair_le_of_not_isRoot (L := L) hα
    have hle : J ≤ rootSpan .E6 L
        ({(Pi.single (0 : Fin Tag.E6.rank) 1), -(Pi.single (0 : Fin Tag.E6.rank) 1)} :
          Set (Fin Tag.E6.rank → ℤ)) := hJ.trans hspan
    have hcent : Subgroup.centralizer
        (rootSpan .E6 L
          ({(Pi.single (0 : Fin Tag.E6.rank) 1), -(Pi.single (0 : Fin Tag.E6.rank) 1)} :
            Set (Fin Tag.E6.rank → ℤ)) : Set (ModGL .E6 L)) ≤
        Subgroup.centralizer (J : Set (ModGL .E6 L)) := Subgroup.centralizer_le hle
    have hsub : B ⊓ Subgroup.centralizer
        (rootSpan .E6 L
          ({(Pi.single (0 : Fin Tag.E6.rank) 1), -(Pi.single (0 : Fin Tag.E6.rank) 1)} :
            Set (Fin Tag.E6.rank → ℤ)) : Set (ModGL .E6 L)) ≤
        B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L)) :=
      inf_le_inf_left _ hcent
    exact hb.trans (Nat.mul_le_mul_left 3 (Subgroup.card_le_of_le hsub))

theorem a2_centralizer_card
    {L : Type} [Field L]
    (B J : Subgroup (ModGL .E6 L)) [Finite B]
    (hBT : B ≤ torusGroup .E6 L) (hB3 : ∀ b ∈ B, b ^ 3 = 1)
    (α β : Fin Tag.E6.rank → ℤ) (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β)
    (hαβ : IsRoot .E6 (α + β)) (hJ : J ≤ rootSpan .E6 L (a2roots α β)) :
    Nat.card B ≤ 9 * Nat.card
      (B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L)) : Subgroup (ModGL .E6 L)) := by
  haveI : Finite ↥(B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L))) :=
    finite_inf_centralizer B J
  have hb := rank_two_bound B hBT hB3 α β hα hβ hαβ
  have hcent : Subgroup.centralizer
      (rootSpan .E6 L (a2roots α β) : Set (ModGL .E6 L)) ≤
      Subgroup.centralizer (J : Set (ModGL .E6 L)) := Subgroup.centralizer_le hJ
  have hsub : B ⊓ Subgroup.centralizer
      (rootSpan .E6 L (a2roots α β) : Set (ModGL .E6 L)) ≤
      B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L)) :=
    inf_le_inf_left _ hcent
  exact hb.trans (Nat.mul_le_mul_left 9 (Subgroup.card_le_of_le hsub))

theorem a2_centralizer_card_of_root_zero
    {L : Type} [Field L]
    (B J : Subgroup (ModGL .E6 L)) [Finite B]
    (hBT : B ≤ torusGroup .E6 L) (hB3 : ∀ b ∈ B, b ^ 3 = 1)
    (α β : Fin Tag.E6.rank → ℤ) (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β)
    (hαβ : IsRoot .E6 (α + β)) (hJ : J ≤ rootSpan .E6 L (a2roots α β))
    (hz : ∃ γ ∈ a2roots α β, ∀ t : Fin Tag.E6.rank → Lˣ,
      rootDiagUnit .E6 t ∈ B → rootChar t γ = 1) :
    Nat.card B ≤ 3 * Nat.card
      (B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L)) : Subgroup (ModGL .E6 L)) := by
  haveI : Finite ↥(B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L))) :=
    finite_inf_centralizer B J
  let f : (Fin Tag.E6.rank → Lˣ) →* ModGL .E6 L := rootDiagUnitHom .E6 L
  let T : Subgroup (Fin Tag.E6.rank → Lˣ) := B.comap f
  obtain ⟨γ, hγmem, hγ1⟩ := hz
  have hγ1' : ∀ t : T, rootChar (t : Fin Tag.E6.rank → Lˣ) γ = 1 :=
    fun t => hγ1 _ t.2
  have hT3 : ∀ t : T, (t : Fin Tag.E6.rank → Lˣ) ^ 3 = 1 :=
    fun t => comap_pow_three_eq_one B hB3 t
  simp only [a2roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγmem
  have key : ∀ (ψ : (Fin Tag.E6.rank → Lˣ) →* Lˣ),
      (∀ t : T, (ψ (t : Fin Tag.E6.rank → Lˣ)) ^ 3 = 1) →
      (∀ t : T, ψ (t : Fin Tag.E6.rank → Lˣ) = 1 →
        rootChar (t : Fin Tag.E6.rank → Lˣ) α = 1 ∧
          rootChar (t : Fin Tag.E6.rank → Lˣ) β = 1) →
      Nat.card B ≤ 3 * Nat.card
        (B ⊓ Subgroup.centralizer
          (rootSpan .E6 L (a2roots α β) : Set (ModGL .E6 L)) :
            Subgroup (ModGL .E6 L)) := by
    intro ψ hψ3 hψ
    let χ : T →* Lˣ := ψ.comp T.subtype
    have hrange : Nat.card χ.range ≤ 3 := by
      have hle : χ.range ≤ rootsOfUnity 3 L := by
        intro x hx
        obtain ⟨t, rfl⟩ := hx
        rw [mem_rootsOfUnity]
        exact hψ3 t
      calc Nat.card χ.range ≤ Nat.card (rootsOfUnity 3 L) := Subgroup.card_le_of_le hle
        _ ≤ 3 := card_rootsOfUnity L 3
    have hker : ∀ t : T, χ t = 1 →
        rootDiagUnitHom .E6 L (t : Fin Tag.E6.rank → Lˣ) ∈
          B ⊓ Subgroup.centralizer
            (rootSpan .E6 L (a2roots α β) : Set (ModGL .E6 L)) := by
      intro t ht
      rw [Subgroup.mem_inf]
      refine ⟨t.2, ?_⟩
      have ht1 : ψ (t : Fin Tag.E6.rank → Lˣ) = 1 := by
        simpa [χ] using ht
      obtain ⟨hα1, hβ1⟩ := hψ t ht1
      exact rootDiagUnit_mem_centralizer_of_char
        (a2roots_char_eq_one (t : Fin Tag.E6.rank → Lˣ) hα hβ hαβ hα1 hβ1)
    exact card_le_mul_card_inf_centralizer B
      (rootSpan .E6 L (a2roots α β)) hBT T rfl χ 3 hrange hker
  have hfin : Nat.card B ≤ 3 * Nat.card
      (B ⊓ Subgroup.centralizer
        (rootSpan .E6 L (a2roots α β) : Set (ModGL .E6 L)) :
          Subgroup (ModGL .E6 L)) := by
    rcases hγmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact key (charHom β) (charHom_pow_three β hT3) (fun t ht => ⟨hγ1' t, ht⟩)
    · refine key (charHom β) (charHom_pow_three β hT3) (fun t ht => ⟨?_, ht⟩)
      have h := hγ1' t
      rwa [rootChar_neg_left, inv_eq_one] at h
    · exact key (charHom α) (charHom_pow_three α hT3) (fun t ht => ⟨ht, hγ1' t⟩)
    · refine key (charHom α) (charHom_pow_three α hT3) (fun t ht => ⟨ht, ?_⟩)
      have h := hγ1' t
      rwa [rootChar_neg_left, inv_eq_one] at h
    · refine key (charHom β) (charHom_pow_three β hT3) (fun t ht => ⟨?_, ht⟩)
      have htβ : rootChar (t : Fin Tag.E6.rank → Lˣ) β = 1 := ht
      have h := hγ1' t
      rw [rootChar_add, htβ, mul_one] at h
      exact h
    · refine key (charHom β) (charHom_pow_three β hT3) (fun t ht => ⟨?_, ht⟩)
      have htβ : rootChar (t : Fin Tag.E6.rank → Lˣ) β = 1 := ht
      have h := hγ1' t
      rw [rootChar_neg_left, inv_eq_one] at h
      rw [rootChar_add, htβ, mul_one] at h
      exact h
  have hcent : Subgroup.centralizer
      (rootSpan .E6 L (a2roots α β) : Set (ModGL .E6 L)) ≤
      Subgroup.centralizer (J : Set (ModGL .E6 L)) := Subgroup.centralizer_le hJ
  have hsub : B ⊓ Subgroup.centralizer
      (rootSpan .E6 L (a2roots α β) : Set (ModGL .E6 L)) ≤
      B ⊓ Subgroup.centralizer (J : Set (ModGL .E6 L)) :=
    inf_le_inf_left _ hcent
  exact hfin.trans (Nat.mul_le_mul_left 3 (Subgroup.card_le_of_le hsub))

end CFSG.StandardType
