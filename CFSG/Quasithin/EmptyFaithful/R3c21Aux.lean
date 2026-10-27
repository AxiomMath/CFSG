module

public import CFSG.Quasithin.Background.E2Three
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAlt3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B2F

namespace R3c21

open E2
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem subgroupOf_commutator {Nv A B : Subgroup G} (hA : A ≤ Nv) (hB : B ≤ Nv) :
    ⁅A, B⁆.subgroupOf Nv = ⁅A.subgroupOf Nv, B.subgroupOf Nv⁆ := by
  have hAB : ⁅A, B⁆ ≤ Nv := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact Nv.mul_mem (Nv.mul_mem (Nv.mul_mem (hA ha) (hB hb)) (Nv.inv_mem (hA ha)))
      (Nv.inv_mem (hB hb))
  apply Subgroup.map_injective Nv.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left hA, inf_of_le_left hB, inf_of_le_left hAB]

omit [Finite G] in
theorem autI_commutator {V : Subgroup G} (hV : IsElemAbelian 2 V) {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (V : Set G)) (hB : B ≤ Subgroup.normalizer (V : Set G)) :
    autI hV ⁅A, B⁆ = ⁅autI hV A, autI hV B⁆ := by
  have hAB : ⁅A, B⁆ ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact (Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).mul_mem
          ((Subgroup.normalizer (V : Set G)).mul_mem (hA ha) (hB hb))
          ((Subgroup.normalizer (V : Set G)).inv_mem (hA ha)))
        ((Subgroup.normalizer (V : Set G)).inv_mem (hB hb))
  rw [autI_eq_map_convHom hV (le_refl _) hAB, autI_eq_map_convHom hV (le_refl _) hA,
    autI_eq_map_convHom hV (le_refl _) hB, subgroupOf_commutator hA hB, Subgroup.map_commutator]

theorem charTwo_of_card_two_pow {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) : CharP F 2 := by
  have h2 : ringChar F = 2 := by
    rw [FiniteField.even_card_iff_char_two]
    rw [hcard]
    simp [Nat.pow_mod, Nat.pos_iff_ne_zero.mp hn]
  rw [← h2]
  exact ringChar.charP F

theorem isSimpleGroup_sl2_of_card_two_pow {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hchar : CharP F 2 := charTwo_of_card_two_pow (by omega) hcard
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have h2 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, hcard]; exact h2)
    exact ⟨s, hs⟩
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl (Or.inr h4)
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
    rw [Fintype.card_fin] at hr
    have h2 := sub_pow_char (p := 2) r 1
    rw [hr, one_pow, sub_self] at h2
    have hr1 : r = 1 := sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h2)
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hrA, hr1, map_one]
    rfl
  have hinj : Function.Injective
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  let e := MulEquiv.ofBijective
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
    ⟨hinj, QuotientGroup.mk'_surjective _⟩
  exact e.isSimpleGroup

theorem eq_bot_or_eq_top_of_isL2Natural {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}
    {C : Subgroup W} {n : ℕ} (h : E2.IsL2Natural L C n) (hn : 2 ≤ n) (B : Subgroup ↥L)
    [B.Normal] : B = ⊥ ∨ B = ⊤ := by
  obtain ⟨-, F, hF, hFin, hcard, e, -⟩ := h
  have hs := isSimpleGroup_sl2_of_card_two_pow hn hcard
  have : IsSimpleGroup ↥L := @MulEquiv.isSimpleGroup _ _ _ _ hs e
  exact Subgroup.Normal.eq_bot_or_eq_top B

end R3c21

end CFSG.Quasithin
