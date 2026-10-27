module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Iso

public section

namespace CFSG.Quasithin.H13.F48Rig

open CFSG.Quasithin CFSG.Quasithin.H13.F431.F45

universe u w w'

section Geodesics

variable {Y : Type*} [Group Y]

@[expose] def GeodUnique (G₀ G₁ G₂ : Subgroup Y) (m : ℕ) : Prop :=
  ∀ p q : GPath (CosetGeom.graph G₀ G₁ G₂) m, p.IsGeodesic → q.IsGeodesic → p 0 = q 0 →
    p m = q m → p = q

theorem geodUnique_of_iso {V W : Type*} {Γ : SimpleGraph V} {Δ : SimpleGraph W} (e : Γ ≃g Δ)
    {m : ℕ} (h : ∀ p q : GPath Γ m, p.IsGeodesic → q.IsGeodesic → p 0 = q 0 → p m = q m → p = q) :
    ∀ p q : GPath Δ m, p.IsGeodesic → q.IsGeodesic → p 0 = q 0 → p m = q m → p = q := by
  intro p q hp hq h0 hm
  have hmap : ∀ a b : W, Δ.Adj a b → Γ.Adj (e.symm a) (e.symm b) :=
    fun a b hab => e.symm.map_rel_iff.mpr hab
  have hgeo : ∀ r : GPath Δ m, r.IsGeodesic → (r.map e.symm hmap).IsGeodesic := by
    intro r hr
    show Γ.dist ((r.map e.symm hmap) 0) ((r.map e.symm hmap) m) = m
    simp only [GPath.map_apply]
    rw [iso_dist e.symm]
    exact hr
  have h' := h (p.map e.symm hmap) (q.map e.symm hmap) (hgeo p hp) (hgeo q hq) (by simp [h0])
    (by simp [hm])
  refine GPath.ext' fun i _ => ?_
  have := congrArg (fun r : GPath Γ m => r i) h'
  simp only [GPath.map_apply] at this
  exact e.symm.injective this

@[expose] def cosetGraphSwap (G₀ G₁ G₂ : Subgroup Y) :
    CosetGeom.graph G₀ G₁ G₂ ≃g CosetGeom.graph G₀ G₂ G₁ where
  toEquiv := Equiv.sumComm _ _
  map_rel_iff' := by
    intro a b
    rcases a with x | y <;> rcases b with x' | y'
    · exact iff_of_false CosetGeom.not_adj_inr_inr CosetGeom.not_adj_inl_inl
    · exact CosetGeom.adj_inr_inl.trans
        ((exists_congr fun g => and_comm).trans CosetGeom.adj_inl_inr.symm)
    · exact CosetGeom.adj_inl_inr.trans
        ((exists_congr fun g => and_comm).trans CosetGeom.adj_inr_inl.symm)
    · exact iff_of_false CosetGeom.not_adj_inl_inl CosetGeom.not_adj_inr_inr

theorem geodUnique_swap (G₀ G₁ G₂ : Subgroup Y) (m : ℕ) :
    GeodUnique G₀ G₁ G₂ m ↔ GeodUnique G₀ G₂ G₁ m :=
  ⟨geodUnique_of_iso (cosetGraphSwap G₀ G₁ G₂), geodUnique_of_iso (cosetGraphSwap G₀ G₁ G₂).symm⟩

theorem geodUnique_congr {G₀ G₀' : Subgroup Y} (h : G₀ = G₀') (G₁ G₂ : Subgroup Y) (m : ℕ) :
    GeodUnique G₀ G₁ G₂ m ↔ GeodUnique G₀' G₁ G₂ m := by
  subst h
  exact Iff.rfl

end Geodesics

section Completion

variable {X : Type u} [Group X] {Y : Type w} [Group Y] (P1 P2 : Subgroup X)

theorem range_comp_mulEquiv {A B : Type*} [Group A] [Group B] (f : A →* Y) (e : B ≃* A) :
    (f.comp e.toMonoidHom).range = f.range := by
  ext y
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨e b, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨e.symm a, by simp⟩

@[expose] def swapCompletion (β : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) :
    (RankTwoAmalgam.ofSubgroups P2 P1).Completion Y where
  φ1 := β.φ2
  φ12 := β.φ12.comp (MulEquiv.subgroupCongr (inf_comm P2 P1)).toMonoidHom
  φ2 := β.φ1
  comm1 g := β.comm2 (MulEquiv.subgroupCongr (inf_comm P2 P1) g)
  comm2 g := β.comm1 (MulEquiv.subgroupCongr (inf_comm P2 P1) g)
  inter := by
    have h1 : β.φ2.range ⊓ β.φ1.range = β.φ12.range := by
      rw [inf_comm]
      exact β.inter
    exact h1.trans (range_comp_mulEquiv β.φ12 _).symm
  gen := by
    have h1 : β.φ2.range ⊔ β.φ1.range = ⊤ := by
      rw [sup_comm]
      exact β.gen
    exact h1

variable {P1 P2}

@[simp] theorem swapCompletion_φ1 (β : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) :
    (swapCompletion P1 P2 β).φ1 = β.φ2 := rfl

@[simp] theorem swapCompletion_φ2 (β : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) :
    (swapCompletion P1 P2 β).φ2 = β.φ1 := rfl

theorem swapCompletion_φ12 (β : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (g : ↥(P2 ⊓ P1)) :
    (swapCompletion P1 P2 β).φ12 g = β.φ12 (MulEquiv.subgroupCongr (inf_comm P2 P1) g) := rfl

theorem swapCompletion_isFaithful_iff (β : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) :
    (swapCompletion P1 P2 β).IsFaithful ↔ β.IsFaithful := by
  constructor
  · rintro ⟨h1, h12, h2⟩
    refine ⟨h2, fun (a b : ↥(P1 ⊓ P2)) hab => ?_, h1⟩
    have h : (MulEquiv.subgroupCongr (inf_comm P2 P1)).symm a =
        (MulEquiv.subgroupCongr (inf_comm P2 P1)).symm b := h12 (by
      rw [swapCompletion_φ12, swapCompletion_φ12,
        (MulEquiv.subgroupCongr (inf_comm P2 P1)).apply_symm_apply,
        (MulEquiv.subgroupCongr (inf_comm P2 P1)).apply_symm_apply]
      exact hab)
    exact (MulEquiv.subgroupCongr (inf_comm P2 P1)).symm.injective h
  · rintro ⟨h1, h12, h2⟩
    exact ⟨h2, h12.comp (MulEquiv.subgroupCongr (inf_comm P2 P1)).injective, h1⟩

theorem swapCompletion_isLarge_iff (β : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (m : ℕ) : (swapCompletion P1 P2 β).IsLarge m ↔ β.IsLarge m :=
  (geodUnique_congr (sup_comm β.φ2.range β.φ1.range) β.φ2.range β.φ1.range m).trans
    (geodUnique_swap (β.φ1.range ⊔ β.φ2.range) β.φ2.range β.φ1.range m)

theorem swapCompletion_isSmall_iff (β : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (m : ℕ) : (swapCompletion P1 P2 β).IsSmall m ↔ β.IsSmall m :=
  not_congr (swapCompletion_isLarge_iff β m)

end Completion

section Equivalence

variable {X : Type u} [Group X] {Y : Type w} [Group Y] {Y' : Type w'} [Group Y']
  {P1 P2 : Subgroup X}

theorem swapCompletion_isEquivalent_iff (β : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (η : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y') :
    Amalgam.Completion.IsEquivalent (swapCompletion P1 P2 β).toCompletion
        (swapCompletion P1 P2 η).toCompletion ↔
      Amalgam.Completion.IsEquivalent β.toCompletion η.toCompletion := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun d x => ?_⟩
    cases d
    · exact hφ RankTwoIndex.two x
    · exact hφ RankTwoIndex.one x
    · have key : ∀ y : ↥(P1 ⊓ P2), φ (β.φ12 y) = η.φ12 y := fun y => by
        have h := hφ RankTwoIndex.onetwo ((MulEquiv.subgroupCongr (inf_comm P2 P1)).symm y)
        change φ (β.φ12 (MulEquiv.subgroupCongr (inf_comm P2 P1)
            ((MulEquiv.subgroupCongr (inf_comm P2 P1)).symm y))) =
          η.φ12 (MulEquiv.subgroupCongr (inf_comm P2 P1)
            ((MulEquiv.subgroupCongr (inf_comm P2 P1)).symm y)) at h
        rwa [(MulEquiv.subgroupCongr (inf_comm P2 P1)).apply_symm_apply] at h
      exact key x
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun d x => ?_⟩
    cases d
    · exact hφ RankTwoIndex.two x
    · exact hφ RankTwoIndex.one x
    · exact hφ RankTwoIndex.onetwo (MulEquiv.subgroupCongr (inf_comm P2 P1) x)

theorem swapCompletion_inclusion_isEquivalent (G0 G0' : Subgroup X) (h : P1 ⊔ P2 = G0)
    (h' : P2 ⊔ P1 = G0') :
    Amalgam.Completion.IsEquivalent
      (swapCompletion P1 P2 (RankTwoAmalgam.inclusionCompletion P1 P2 G0 h)).toCompletion
      (RankTwoAmalgam.inclusionCompletion P2 P1 G0' h').toCompletion := by
  refine ⟨MulEquiv.subgroupCongr (h.symm.trans ((sup_comm P1 P2).trans h')), fun d x => ?_⟩
  cases d <;> rfl

theorem isEquivalent_of_swap_inclusion (G0 G0' : Subgroup X) (h : P1 ⊔ P2 = G0)
    (h' : P2 ⊔ P1 = G0') (β : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    (he : Amalgam.Completion.IsEquivalent (swapCompletion P1 P2 β).toCompletion
      (RankTwoAmalgam.inclusionCompletion P2 P1 G0' h').toCompletion) :
    Amalgam.Completion.IsEquivalent β.toCompletion
      (RankTwoAmalgam.inclusionCompletion P1 P2 G0 h).toCompletion :=
  (swapCompletion_isEquivalent_iff β (RankTwoAmalgam.inclusionCompletion P1 P2 G0 h)).mp
    (he.trans (swapCompletion_inclusion_isEquivalent G0 G0' h h').symm)

end Equivalence

end CFSG.Quasithin.H13.F48Rig
