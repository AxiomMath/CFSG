module

public import CFSG.RankThree.PartOne.KC.OrthogonalPairedBlock

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Representatives

theorem exists_involution_representatives {α : Type*} [Finite α] (σ : α → α)
    (hσ : ∀ a, σ (σ a) = a) : ∃ s : Set α, ∀ a, ∃! r, r ∈ s ∧ (a = r ∨ a = σ r) := by
  let S : Setoid α :=
    { r := fun a b => a = b ∨ a = σ b
      iseqv := ⟨fun a => Or.inl rfl, fun {a b} h => by
        rcases h with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, hσ]), fun {a b c} hab hbc => by
        rcases hab with hab | hab <;> rcases hbc with hbc | hbc
        · exact Or.inl (hab.trans hbc)
        · exact Or.inr (hab.trans hbc)
        · exact Or.inr (by rw [hab, hbc])
        · exact Or.inl (by rw [hab, hbc, hσ])⟩ }
  refine ⟨Set.range (Quotient.out : Quotient S → α), fun a => ?_⟩
  have key : ∀ r, (a = r ∨ a = σ r) ↔ (Quotient.mk S r = Quotient.mk S a) := fun r => by
    rw [Quotient.eq]
    constructor
    · intro h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, hσ])
    · intro h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, hσ])
  refine ⟨(Quotient.mk S a).out, ⟨⟨_, rfl⟩, (key _).mpr (Quotient.out_eq _)⟩, ?_⟩
  rintro r ⟨⟨q, rfl⟩, hr⟩
  have h1 := (key _).mp hr
  rw [Quotient.out_eq] at h1
  rw [← h1]

end Representatives

section Product

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.exists_orbitRepresentatives (hx : OddOrderIsometry Q p x) :
    ∃ Rep : Finset K[X], IsOrbitRepresentatives x Rep := by
  classical
  let σ : primaryFactors x.toLinearMap → primaryFactors x.toLinearMap := fun k =>
    ⟨reciprocalPolynomial k, hx.reciprocalPolynomial_mem k.2⟩
  have hσ : ∀ a, σ (σ a) = a := fun a => Subtype.ext (hx.reciprocal_reciprocal_eq a.2)
  obtain ⟨s, hs⟩ := exists_involution_representatives σ hσ
  refine ⟨(Set.toFinite s).toFinset.image Subtype.val, fun r hr => ?_, fun k hk => ?_⟩
  · obtain ⟨r', -, rfl⟩ := Finset.mem_image.mp hr
    exact r'.2
  · obtain ⟨r, ⟨hrs, hkr⟩, huniq⟩ := hs ⟨k, hk⟩
    refine ⟨r.1, ⟨Finset.mem_image.mpr ⟨r, (Set.Finite.mem_toFinset _).mpr hrs, rfl⟩, ?_⟩, ?_⟩
    · rcases hkr with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    · rintro r' ⟨hr', hkr'⟩
      obtain ⟨r'', hr'', rfl⟩ := Finset.mem_image.mp hr'
      have := huniq r'' ⟨(Set.Finite.mem_toFinset _).mp hr'', by
        rcases hkr' with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)⟩
      rw [this]

omit [FiniteDimensional K V] in
theorem IsOrbitRepresentatives.ne_reciprocal {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) {i j : K[X]} (hi : i ∈ Rep) (hj : j ∈ Rep) (hij : i ≠ j) :
    j ≠ reciprocalPolynomial i := by
  intro h
  obtain ⟨r, -, hr⟩ := hRep.2 j (hRep.1 hj)
  have h1 := hr j ⟨hj, Or.inl rfl⟩
  have h2 := hr i ⟨hi, Or.inr h⟩
  exact hij (h2.trans h1.symm)

theorem OddOrderIsometry.blocks_commute (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) :
    Pairwise fun i j : ↥Rep => ∀ g g' : V ≃ₗ[K] V, g ∈ supportedBlock Q x i →
      g' ∈ supportedBlock Q x j → Commute g g' := by
  intro i j hij g g' hg hg'
  exact hx.commute_supportedBlock (hRep.1 i.2) (hRep.1 j.2) (fun e => hij (Subtype.ext e.symm))
    (hRep.ne_reciprocal i.2 j.2 (fun e => hij (Subtype.ext e))) hg hg'

theorem OddOrderIsometry.blocks_iSupIndep (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) :
    iSupIndep (fun i : ↥Rep => supportedBlock Q x i) := by
  classical
  intro i
  refine (hx.disjoint_supportedBlock hRep i.2).mono_right ?_
  refine iSup₂_le fun j hj => ?_
  exact le_iSup₂_of_le j.1 (Finset.mem_erase.mpr ⟨fun e => hj (Subtype.ext e), j.2⟩) le_rfl

theorem OddOrderIsometry.blocks_iSup_eq (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) :
    ⨆ i : ↥Rep, supportedBlock Q x i = isometryCentralizer Q x := by
  refine le_antisymm (iSup_le fun i => supportedBlock_le_isometryCentralizer _) ?_
  have := hx.isometryCentralizer_le hRep
  rw [iSup_subtype'] at this
  exact this

@[expose] noncomputable def blockProduct (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) :
    (∀ i : ↥Rep, ↥(supportedBlock Q x i)) →* V ≃ₗ[K] V :=
  Subgroup.noncommPiCoprod (H := fun i : ↥Rep => supportedBlock Q x i) (hx.blocks_commute hRep)

theorem blockProduct_injective (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) : Function.Injective (blockProduct hx hRep) :=
  Subgroup.injective_noncommPiCoprod_of_iSupIndep (hx.blocks_iSupIndep hRep)

theorem range_blockProduct (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) :
    (blockProduct hx hRep).range = isometryCentralizer Q x := by
  rw [blockProduct, Subgroup.noncommPiCoprod_range, hx.blocks_iSup_eq hRep]

theorem exists_blockProduct_eq (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) {v : V ≃ₗ[K] V} (hv : v ∈ isometryCentralizer Q x) :
    ∃ t, blockProduct hx hRep t = v := by
  rw [← range_blockProduct hx hRep] at hv
  exact hv

theorem blockProduct_mulSingle (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) [DecidableEq ↥Rep] (i : ↥Rep)
    (g : ↥(supportedBlock Q x i)) : blockProduct hx hRep (Pi.mulSingle i g) = g :=
  Subgroup.noncommPiCoprod_mulSingle (H := fun i : ↥Rep => supportedBlock Q x i) i g

theorem blockProduct_mem {Rep : Finset K[X]} (hx : OddOrderIsometry Q p x)
    (hRep : IsOrbitRepresentatives x Rep) (F : Subgroup (V ≃ₗ[K] V))
    (t : ∀ i : ↥Rep, ↥(supportedBlock Q x i)) (ht : ∀ i, (t i : V ≃ₗ[K] V) ∈ F) :
    blockProduct hx hRep t ∈ F := by
  rw [blockProduct, Subgroup.noncommPiCoprod_apply]
  exact Subgroup.noncommProd_mem F _ fun i _ => ht i

end Product

end CFSG.RankThree.PartOne.KCOrthogonal
