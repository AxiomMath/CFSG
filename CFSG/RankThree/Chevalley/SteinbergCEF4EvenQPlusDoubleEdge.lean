module

public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenLeviCentralizer

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint F4Weyl
  EvenG2 EvenF4QPlus CFSG.RankThree.E6 NativeLevi
open scoped Pointwise commutatorElement

namespace EvenF4QPlus

section ListProd

variable {τ : Tag} (L : Type) [Field L]

@[expose] def rootListProd
    (l : List (Fin τ.rank → ℤ)) (A : SL2 L) : ModGL τ L :=
  (l.map fun β => rootSL2 τ L β A).prod

variable {L}

theorem rootListProd_nSL_eq_canonicalRep
    [CharP L 2] {l : List (Fin τ.rank → ℤ)}
    (hl : ∀ β ∈ l, IsRoot τ β) :
    rootListProd L l (nSL 1) = canonicalRep (coxeterSystem τ) L (l.map rootReflection).prod := by
  induction l with
  | nil => simp [rootListProd, canonicalRep_one]
  | cons β l ih =>
    rw [List.map_cons, List.prod_cons, canonicalRep_mul_of_charTwo,
      ← ih fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ),
      ← rootWeylSL2_one_eq_canonicalRep_of_charTwo (hl β List.mem_cons_self)]
    rfl

end ListProd

section Twisted

variable {τ : Tag} {L : Type} [Field L]

theorem units_map_entrywiseHom_mem_subsystemGroup
    (σ : L →+* L) {J : Set (Fin τ.rank)}
    {y : ModGL τ L} (hy : y ∈ subsystemGroup τ L J) :
    Units.map (entrywiseHom σ) y ∈ subsystemGroup τ L J := by
  have hle : subsystemGroup τ L J ≤ (subsystemGroup τ L J).comap (Units.map (entrywiseHom σ)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, c, rfl | rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, units_map_entrywiseHom_xUnit]
      exact xUnit_mem_subsystemGroup hj _
    · rw [SetLike.mem_coe, Subgroup.mem_comap, units_map_entrywiseHom_yUnit]
      exact yUnit_mem_subsystemGroup hj _
  exact hle hy

end Twisted

theorem subsystemGroup_le_adjointGroup'
    {τ : Tag} {L : Type} [Field L] (J : Set (Fin τ.rank)) :
    subsystemGroup τ L J ≤ adjointGroup τ L :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨j, -, c, rfl | rfl⟩
    exacts [xUnit_mem_adjointGroup j c, yUnit_mem_adjointGroup j c])

theorem map_baseChangeGL_subsystemGroup
    {τ : Tag} {R S : Type} [Field R] [Field S] (f : R →+* S)
    (J : Set (Fin τ.rank)) :
    (subsystemGroup τ R J).map (baseChangeGL f) = Subgroup.closure
      {g | ∃ j ∈ J, ∃ c ∈ Set.range f, g = xUnit τ S j c ∨ g = yUnit τ S j c} := by
  rw [subsystemGroup, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨j, hj, c, rfl | rfl⟩, rfl⟩
    · exact ⟨j, hj, f c, ⟨c, rfl⟩, Or.inl (baseChangeGL_xUnit f j c)⟩
    · exact ⟨j, hj, f c, ⟨c, rfl⟩, Or.inr (baseChangeGL_yUnit f j c)⟩
  · rintro ⟨j, hj, _, ⟨c, rfl⟩, rfl | rfl⟩
    · exact ⟨_, ⟨j, hj, c, Or.inl rfl⟩, baseChangeGL_xUnit f j c⟩
    · exact ⟨_, ⟨j, hj, c, Or.inr rfl⟩, baseChangeGL_yUnit f j c⟩

theorem commutator_standardLevi_le {τ : Tag} {M : Type} [Field M] (J : Set (Fin τ.rank)) :
    ⁅standardLevi τ M J, standardLevi τ M J⁆ ≤ subsystemGroup τ M J := by
  have hTcomm := (triangular_borel_structure.{0, 0} τ M).1
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [← SetLike.mem_coe, coe_standardLevi] at hx hy
  obtain ⟨h, hh, q, hq, rfl⟩ := hx
  obtain ⟨h', hh', q', hq', rfl⟩ := hy
  have hN : ∀ t ∈ torusGroup τ M, ∀ u ∈ subsystemGroup τ M J,
      t * u * t⁻¹ ∈ subsystemGroup τ M J := fun t ht u hu =>
    (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_subsystemGroup J ht) u).1 hu
  have e1 : ⁅h * q, h' * q'⁆ = (h * h') * (h'⁻¹ * q * h' * (q' * q⁻¹)) * (h' * h)⁻¹ *
      (h' * q'⁻¹ * h'⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e1, ← hTcomm h hh h' hh']
  refine mul_mem (hN _ (mul_mem hh hh') _ (mul_mem ?_ (mul_mem hq' (inv_mem hq))))
    (hN _ hh' _ (inv_mem hq'))
  have := hN _ (inv_mem hh') _ hq
  rwa [inv_inv] at this

end EvenF4QPlus

open EvenF4QPlus

end CFSG.RankThree.Chevalley
