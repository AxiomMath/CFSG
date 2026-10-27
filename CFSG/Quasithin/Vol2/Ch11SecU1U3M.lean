module

public import CFSG.Quasithin.Vol2.Ch11SecU1U3L
public import CFSG.Quasithin.Vol2.Ch11SecU1U3I

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear (isometrySL)

theorem exists_ne_comm_of_isPerfect {N : Type*} [Group N] [Nontrivial N] [Group.IsPerfect N] :
    ∃ a b : N, a * b ≠ b * a := by
  by_contra hall
  push Not at hall
  have hbot : commutator N = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro b _
    exact hall b a
  obtain ⟨a, ha⟩ := exists_ne (1 : N)
  have h1 : a ∈ commutator N := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top a
  rw [hbot, Subgroup.mem_bot] at h1
  exact ha h1

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K]

theorem exists_fixed_sigma (h : UnitaryFieldData p 1 K) (hp5 : 5 ≤ p)
    {A : GL (HypIndex 1 1) K} (hA : A ∈ hypUnitary h 1 1) {c : K} (hc0 : c ≠ 0)
    (hAc : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar = c • 1)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = h.bar x)
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex 1 1) K) ∈ semilinearSimilitudes h 1 1) :
    ∃ M : Subgroup (hypPSU h 1 1),
      (∀ y, y ∈ M ↔ semilinearAutHom h (le_refl 1) (le_refl 1) ⟨_, hx⟩ y = y) ∧
      IsSimpleGroup ↥⁅M, M⁆ ∧ (∃ a b : ↥⁅M, M⁆, a * b ≠ b * a) ∧
      Subgroup.centralizer ((⁅M, M⁆ : Subgroup (hypPSU h 1 1)) : Set (hypPSU h 1 1)) = ⊥ := by
  have : Finite K := h.finite
  have : CharP K p := h.charP
  have : Fintype h.fixedField := Fintype.ofFinite _
  have hcardF : Fintype.card h.fixedField = p := by
    rw [← Nat.card_eq_fintype_card, h.card_fixedField, pow_one]
  obtain ⟨R, φ, Hm, Wm, hRdet, hRs, hφinj, hHW, hWH, hfix, hmat⟩ :=
    exists_fixed_data h (by omega) hA hc0 hAc hσ hx
  set e := ZMod.ringEquiv h.fixedField hcardF with he
  have hMM : ⁅φ.range, φ.range⁆ = (commutator ↥(isometrySL R)).map φ := by
    rw [MonoidHom.range_eq_map, commutator_def, Subgroup.map_commutator]
  have E : ↥⁅φ.range, φ.range⁆ ≃* ↥(commutator ↥(isometrySL R)) :=
    (MulEquiv.subgroupCongr hMM).trans
      ((commutator ↥(isometrySL R)).equivMapOfInjective φ hφinj).symm
  have : IsSimpleGroup ↥(commutator ↥(isometrySL R)) :=
    isSimpleGroup_commutator_isometry e hp5 hRs hRdet
  have : Group.IsPerfect ↥(commutator ↥(isometrySL R)) :=
    isPerfect_commutator_isometry e hp5 hRs hRdet
  have hsimple : IsSimpleGroup ↥⁅φ.range, φ.range⁆ := E.isSimpleGroup
  have : Group.IsPerfect ↥⁅φ.range, φ.range⁆ :=
    Group.IsPerfect.ofSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  refine ⟨φ.range, hfix, hsimple, exists_ne_comm_of_isPerfect, ?_⟩
  rw [hMM]
  exact centralizer_map_commutator_eq_bot h hp5 hRdet hRs hHW hWH hmat

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3
