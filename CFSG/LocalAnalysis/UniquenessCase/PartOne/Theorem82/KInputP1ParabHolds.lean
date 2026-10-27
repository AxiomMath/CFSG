module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1ParabCore
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1ParabDickson
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1ParabU3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

set_option linter.unusedSectionVars false


theorem odd_of_two_pow_mod_three {f : ℕ} (h : 2 ^ f % 3 = 2) : Odd f := by
  rcases Nat.even_or_odd f with ⟨k, rfl⟩ | ho
  · exfalso
    rw [← two_mul, pow_mul, Nat.pow_mod] at h
    norm_num at h
  · exact ho

theorem l3EvenParabolic_holds : L3EvenParabolic := by
  intro X _ _ hX J K hJ hpar hKJ hK hne
  rcases hX with ⟨f, hf3, hX⟩ | ⟨f, -, hX⟩
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := Fintype.ofFinite F
    haveI : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hF)
    have hJ' : J.map e.toMonoidHom ≠ ⊤ := fun h =>
      hJ (Subgroup.map_injective e.injective (h.trans
        (Subgroup.map_top_of_surjective _ e.surjective).symm))
    have hK' : ⁅K.map e.toMonoidHom, K.map e.toMonoidHom⁆ = K.map e.toMonoidHom := by
      rw [← Subgroup.map_commutator, hK]
    have hne' : K.map e.toMonoidHom ≠ ⊥ := fun h =>
      hne ((Subgroup.map_eq_bot_iff_of_injective K e.injective).mp h)
    exact HasOffender.of_map_mulEquiv e (hasOffender_projectiveSL dicksonSL2_holds hF
      (odd_of_two_pow_mod_three hf3) hJ' (isParabolicTwo_map_mulEquiv e hpar)
      (Subgroup.map_mono hKJ) hK' hne')
  · exact absurd (l3EvenParabolic_psu hX J K hJ hpar hKJ hK) hne

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
