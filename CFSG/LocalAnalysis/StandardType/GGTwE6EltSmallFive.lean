module

public import CFSG.LocalAnalysis.StandardType.GGTwE6EltSmallMat
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC6Defs

public section

namespace CFSG.StandardType.TwE6EltSmall

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.TwE6Transport

set_option linter.unusedSectionVars false


theorem ggTwE6EltNormSmallInput_holds : SmallExc.GGTwE6EltNormSmallInput := by
  rintro K _ _ n p hn hK hp hpq hp3 A hA hA5 - ⟨U, hU, hU2, hAU⟩ a ha ha1 D hDa hDn hDq hcomm
    hsmall
  exfalso
  obtain ⟨σ, hσ, ε, -⟩ := exists_recipeConj hn hK
  have hp5 : 5 ≤ p := by
    have h2 : p ≠ 2 := by
      rintro rfl
      exact absurd ((Nat.dvd_add_right (dvd_pow_self 2 (by omega))).1 hpq) (by norm_num)
    have := hp.two_le
    have := hp.eq_two_or_odd.resolve_left h2
    omega
  have hcard : ∀ H : Subgroup (TwE6Delta.RecipeR K n),
      Nat.card ↥(H.comap ε.toMonoidHom) = Nat.card H :=
    fun H => Nat.card_congr (ε.toEquiv.subtypeEquiv fun _ => Iff.rfl)
  have hcardAD : Nat.card ↥(A.comap ε.toMonoidHom ⊓ D.comap ε.toMonoidHom) = Nat.card ↥(A ⊓ D) :=
    Nat.card_congr (ε.toEquiv.subtypeEquiv fun _ => Iff.rfl)
  have hfix : ∀ g, g ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
      (MulAut.conj (ε.symm a)) ↔ ε g ∈ Subgroup.centralizer {a} := fun g => by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.conj_apply,
      mul_inv_eq_iff_eq_mul, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' := congrArg ε h
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'
      exact h'.symm
    · intro h
      apply ε.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h.symm
  have hle : D.comap ε.toMonoidHom ≤
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj (ε.symm a)) :=
    fun g hg => (hfix g).2 (hDa hg)
  have e : ↥(D.comap ε.toMonoidHom) ≃* ↥D :=
    (MulEquiv.subgroupCongr (Subgroup.comap_equiv_eq_map_symm' ε D)).trans
      (D.equivMapOfInjective _ ε.symm.injective).symm
  have hQq := hDq.of_mulEquiv e
  refine false_of_isComponentOf_fixSubgroup hn hK hσ hp hp5 hpq (B := A.comap ε.toMonoidHom)
    (hA.comap (f := ε.toMonoidHom) ε.injective) (by rw [hcard]; exact hA5)
    (twNormTwo_eltMat σ ε hU hU2 hAU) (a := ε.symm a)
    (show ε (ε.symm a) ∈ A by rw [MulEquiv.apply_symm_apply]; exact ha)
    (ε.symm.map_ne_one_iff.2 ha1) (Q := D.comap ε.toMonoidHom)
    ⟨hle, .step hle ⟨fun x hx g => ?_⟩ (.refl _), hQq.1.commutator_eq_top, hQq.2.1⟩ ?_
    (by rw [hcardAD]; exact hsmall (A ⊓ D) (hA.mono inf_le_left) inf_le_right inf_le_left)
  ·
    show ε ((g : twistedE6RootGroup K σ) * x * (g : twistedE6RootGroup K σ)⁻¹) ∈ D
    rw [map_mul, map_mul, map_inv]
    exact hDn (ε g) ((hfix g).1 g.2) (ε x) hx
  ·
    intro b hb hbQ
    have hb' : ε b ∈ Subgroup.zpowers a := hcomm (ε b) hb fun d hd => by
      have h := congrArg ε (hbQ (ε.symm d)
        (show ε (ε.symm d) ∈ D by rw [MulEquiv.apply_symm_apply]; exact hd))
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hb'
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← map_zpow, hk, MulEquiv.symm_apply_apply]⟩

end CFSG.StandardType.TwE6EltSmall

end
