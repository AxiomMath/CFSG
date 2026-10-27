module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinCentralizerLam
public import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviPlane
public import CFSG.LieType.Universal.Symplectic
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix

variable {G : Type} [Group G]

private theorem natCard_eq_two_or_four_le (F : Type) [Field F] [Finite F] [CharP F 2] :
    Nat.card F = 2 ∨ 4 ≤ Nat.card F := by
  haveI := Fintype.ofFinite F
  obtain ⟨k, -, hk⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hk]
  rcases Nat.lt_or_ge (k : ℕ) 2 with h | h
  · left
    have hk1 : (k : ℕ) = 1 := by
      have := k.pos
      omega
    rw [hk1]
    norm_num
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k : ℕ) := Nat.pow_le_pow_right (by norm_num) h

theorem isSimpleGroup_statedSp_of_three_le {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hm : 3 ≤ m) : IsSimpleGroup (StatedSp m F) := by
  have hF : (Infinite F ∨ 4 ≤ Nat.card F) ∨ (Nat.card F = 3 ∧ 2 ≤ m) ∨
      (Nat.card F = 2 ∧ 3 ≤ m) := by
    rcases natCard_eq_two_or_four_le F with h | h
    · exact Or.inr (Or.inr ⟨h, hm⟩)
    · exact Or.inl (Or.inr h)
  have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple m F (by omega) hF
  have hsimple : IsSimpleGroup (StatedSp m F ⧸ Subgroup.center (StatedSp m F)) := hq.2.1
  have hZ : Subgroup.center (StatedSp m F) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem le_range_comp_spLeviBlock_of_perfect {F : Type} [Field F] [CharP F 2] {m : ℕ}
    {ψ : StatedSp (m + 1) F →* G} (hψ : Function.Injective ψ) {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {J : Subgroup G} (hperf : J ≤ ⁅J, J⁆)
    (hJX : J ≤ ψ.range)
    (hJc : ∀ j ∈ J, j * ψ (lam (0 : Fin (m + 1)) g) = ψ (lam (0 : Fin (m + 1)) g) * j) :
    J ≤ (ψ.comp (CFSG.StandardType.spLeviBlock m F)).range := by
  classical
  let J' : Subgroup (StatedSp (m + 1) F) := J.comap ψ
  have hJ'map : J'.map ψ = J := Subgroup.map_comap_eq_self hJX
  have hperf' : J' ≤ ⁅J', J'⁆ := by
    intro x hx
    have hxJ : ψ x ∈ J := hx
    have h1 : ψ x ∈ ⁅J, J⁆ := hperf hxJ
    rw [← hJ'map, ← Subgroup.map_commutator] at h1
    obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp h1
    rw [← hψ hxx']
    exact hx'
  have hcomm : ∀ j ∈ J', j * lam (0 : Fin (m + 1)) g = lam (0 : Fin (m + 1)) g * j := by
    intro j hj
    apply hψ
    rw [map_mul, map_mul]
    exact hJc (ψ j) hj
  have hle := le_range_spLeviBlock_of_perfect_of_commute htr hperf' hcomm
  intro z hz
  rw [← hJ'map] at hz
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hz
  rw [MonoidHom.range_comp]
  exact Subgroup.mem_map.mpr ⟨j, hle hj, rfl⟩

theorem range_comp_spLeviBlock_eq_of_isSubnormal {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 3 ≤ m) {ψ : StatedSp (m + 1) F →* G} (hψ : Function.Injective ψ)
    {g : SpecialLinearGroup (Fin 2) F} (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    {J C : Subgroup G} (hperf : J ≤ ⁅J, J⁆) (hJne : J ≠ ⊥) (hJX : J ≤ ψ.range)
    (hJc : ∀ j ∈ J, j * ψ (lam (0 : Fin (m + 1)) g) = ψ (lam (0 : Fin (m + 1)) g) * j)
    (hsub : CFSG.Assembly.IsSubnormal J C)
    (hSC : (ψ.comp (CFSG.StandardType.spLeviBlock m F)).range ≤ C) :
    (ψ.comp (CFSG.StandardType.spLeviBlock m F)).range = J := by
  have hle := le_range_comp_spLeviBlock_of_perfect hψ htr hperf hJX hJc
  have hinj : Function.Injective (ψ.comp (CFSG.StandardType.spLeviBlock m F)) :=
    hψ.comp CFSG.StandardType.spLeviBlock_injective
  haveI : IsSimpleGroup (StatedSp m F) := isSimpleGroup_statedSp_of_three_le hm
  haveI hSsimple : IsSimpleGroup ↥(ψ.comp (CFSG.StandardType.spLeviBlock m F)).range :=
    (MonoidHom.ofInjective hinj).symm.isSimpleGroup
  have hsub' := hsub.inf_of_le hSC
  have hsub'' : CFSG.Assembly.IsSubnormal J
      (ψ.comp (CFSG.StandardType.spLeviBlock m F)).range := by
    rwa [inf_eq_left.2 hle] at hsub'
  rcases hsub''.eq_bot_or_eq_of_isSimpleGroup hSsimple with h | h
  · exact absurd h hJne
  · exact h.symm

theorem range_comp_spLeviBlock_eq_of_card_le [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ}
    {ψ : StatedSp (m + 1) F →* G} (hψ : Function.Injective ψ) {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {J : Subgroup G} (hperf : J ≤ ⁅J, J⁆)
    (hJX : J ≤ ψ.range)
    (hJc : ∀ j ∈ J, j * ψ (lam (0 : Fin (m + 1)) g) = ψ (lam (0 : Fin (m + 1)) g) * j)
    (hcard : Nat.card (StatedSp m F) ≤ Nat.card J) :
    (ψ.comp (CFSG.StandardType.spLeviBlock m F)).range = J := by
  have hle := le_range_comp_spLeviBlock_of_perfect hψ htr hperf hJX hJc
  have hinj : Function.Injective (ψ.comp (CFSG.StandardType.spLeviBlock m F)) :=
    hψ.comp CFSG.StandardType.spLeviBlock_injective
  have hcardS : Nat.card (ψ.comp (CFSG.StandardType.spLeviBlock m F)).range =
      Nat.card (StatedSp m F) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  exact (Subgroup.eq_of_le_of_card_ge hle (hcardS ▸ hcard)).symm

end CFSG.StandardType.SpJoin
