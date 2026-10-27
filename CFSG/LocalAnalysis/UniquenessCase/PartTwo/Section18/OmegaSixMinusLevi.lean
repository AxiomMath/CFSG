module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusStdFrame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusIsometry
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizer
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedInf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.Open
open CFSG.LieType.Universal.Spin (quadMinus)
open scoped commutatorElement

@[expose] noncomputable def leviEmb {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) : Gom (Q.restrict P.perp) →* Gom Q :=
  extId P.isCompl_perp (fun _ hp _ hw => P.polar_eq_zero_of_mem_span_perp hp hw)

@[expose] noncomputable def leviSub {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) : Subgroup (Gom Q) :=
  (leviEmb P).range

section Generic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem gom_app_zero_restrict_T2J4 (P : HypPair Q) (g' : Gom (Q.restrict P.perp)) :
    (g'.app ⟨0, P.perp.zero_mem⟩ : V) = 0 := by
  change ((g' : ↥P.perp ≃ₗ[K] ↥P.perp) (0 : ↥P.perp) : V) = 0
  rw [map_zero]
  rfl

theorem leviEmb_app (P : HypPair Q) (g' : Gom (Q.restrict P.perp)) {p w : V}
    (hp : p ∈ Submodule.span K {P.e, P.f}) (hw : w ∈ P.perp) :
    (leviEmb P g').app (p + w) = p + (g'.app ⟨w, hw⟩ : V) :=
  extId_app _ _ g' hp hw

theorem leviEmb_injective (P : HypPair Q) : Function.Injective (leviEmb P) := by
  intro g' h' hgh
  apply Gom.ext'
  intro w
  have h := congrArg (fun (g : Gom Q) => g.app (0 + (w : V))) hgh
  rw [leviEmb_app P g' (Submodule.zero_mem _) w.2,
    leviEmb_app P h' (Submodule.zero_mem _) w.2] at h
  simp only [zero_add] at h
  exact Subtype.ext h

theorem leviSub_le_pointStabilizer (P : HypPair Q) : leviSub P ≤ pointStabilizer Q P.e := by
  intro g hg
  rw [mem_pointStabilizer]
  obtain ⟨g', rfl⟩ := hg
  refine ⟨1, ?_⟩
  have he : P.e ∈ Submodule.span K {P.e, P.f} := Submodule.subset_span (by simp)
  have h := leviEmb_app P g' he P.perp.zero_mem
  rw [gom_app_zero_restrict_T2J4] at h
  simpa using h

theorem app_eq_of_mem_leviSub (P : HypPair Q) {g : Gom Q} (hg : g ∈ leviSub P) :
    g.app P.e = P.e ∧ g.app P.f = P.f := by
  obtain ⟨g', rfl⟩ := hg
  have he : P.e ∈ Submodule.span K {P.e, P.f} := Submodule.subset_span (by simp)
  have hf : P.f ∈ Submodule.span K {P.e, P.f} := Submodule.subset_span (by simp)
  constructor
  · have h := leviEmb_app P g' he P.perp.zero_mem
    rw [gom_app_zero_restrict_T2J4] at h
    simpa using h
  · have h := leviEmb_app P g' hf P.perp.zero_mem
    rw [gom_app_zero_restrict_T2J4] at h
    simpa using h

theorem exists_mem_leviSub_app_ne (P : HypPair Q) [Nontrivial (Gom (Q.restrict P.perp))] :
    ∃ l ∈ leviSub P, ∃ a ∈ P.perp, l.app a ≠ a := by
  obtain ⟨g', hg'⟩ : ∃ g' : Gom (Q.restrict P.perp), g' ≠ 1 := exists_ne 1
  have hmove : ∃ w : ↥P.perp, g'.app w ≠ w := by
    by_contra h
    push Not at h
    exact hg' (Gom.ext' fun w => by rw [Gom.app_one]; exact h w)
  obtain ⟨w, hw⟩ := hmove
  refine ⟨leviEmb P g', ⟨g', rfl⟩, (w : V), w.2, ?_⟩
  intro hc
  refine hw (Subtype.ext ?_)
  have h := leviEmb_app P g' (Submodule.zero_mem _) w.2
  simp only [zero_add] at h
  exact h.symm.trans hc

end Generic

section Four

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

private theorem finrank_four_T2J4 :
    Module.finrank F (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → F) = 4 := by
  simp [Module.finrank_fintype_fun_eq_card, Fintype.card_sum]

theorem nonempty_gom_restrict_perp_equiv (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {P : HypPair Q}
    (hP : PerpIsMinusTwo P b c) :
    Nonempty (Gom (Q.restrict P.perp) ≃* ↥(StatedOmega (StatedQuadMinus 2 F b c))) := by
  obtain ⟨φ, hφ⟩ := hP
  obtain ⟨ψ, -⟩ := exists_mulEquiv_gom_of_isometry (Q := Q.restrict P.perp)
    (Q' := quadMinus 2 F b c) φ hφ
  exact ⟨ψ.trans (statedOmegaMinusEquiv (m := 2) (by norm_num) hirr).symm⟩

theorem nonempty_leviSub_equiv_statedOmega (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {P : HypPair Q} (hP : PerpIsMinusTwo P b c) :
    Nonempty (↥(leviSub P) ≃* ↥(StatedOmega (StatedQuadMinus 2 F b c))) := by
  obtain ⟨e⟩ := nonempty_gom_restrict_perp_equiv hirr hP
  exact ⟨(MonoidHom.ofInjective (leviEmb_injective P)).symm.trans e⟩

theorem nontrivial_gom_restrict_perp (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {P : HypPair Q}
    (hP : PerpIsMinusTwo P b c) : Nontrivial (Gom (Q.restrict P.perp)) := by
  obtain ⟨e⟩ := nonempty_gom_restrict_perp_equiv hirr hP
  have hQ : (polarBilin (quadMinus 2 F b c)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 2 F hirr
  have h3 : 2 < Module.finrank F (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → F) := by
    rw [finrank_four_T2J4]; norm_num
  set x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → F := Pi.single (Sum.inl (0 : Fin (2 - 1))) 1
    with hx
  have hu : quadMinus 2 F b c x = 0 := by rw [hx]; exact quadMinus_single_inl 0
  have hx0 : x ≠ 0 := by
    intro h
    have h1 := congrFun h (Sum.inl (0 : Fin (2 - 1)))
    simp [hx] at h1
  have hne : Lom (quadMinus 2 F b c) x ≠ ⊥ := Lom_ne_bot hQ h3 hu hx0
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha' : (a : Gom (quadMinus 2 F b c)) ≠ 1 := fun h1 => ha (Subtype.ext h1)
  haveI : Nontrivial (Gom (quadMinus 2 F b c)) := Nontrivial.mk ⟨(a : Gom _), 1, ha'⟩
  exact Equiv.nontrivial (e.trans (statedOmegaMinusEquiv (m := 2) (by norm_num) hirr)).toEquiv

end Four

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end
