module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBPosition

public section

namespace CFSG.StandardType

theorem ggTableB_cover_of_product_generator {A : Type*} [Group A] (J I C : Subgroup A) [J.Normal]
    (hI : I ≤ J ⊔ C) {u f a : A} (hu : u ∈ I) (hf : u * f ∈ C)
    (ha : a ∈ I ⊔ Subgroup.zpowers f) : ∃ j ∈ J, ∃ c ∈ C, a = j * c := by
  have huH : u ∈ J ⊔ C := hI hu
  have hufH : u * f ∈ J ⊔ C := (show C ≤ J ⊔ C from le_sup_right) hf
  have hfH : f ∈ J ⊔ C := by
    have hmem : u⁻¹ * (u * f) ∈ J ⊔ C := (J ⊔ C).mul_mem ((J ⊔ C).inv_mem huH) hufH
    rwa [show u⁻¹ * (u * f) = f by group] at hmem
  have hle : I ⊔ Subgroup.zpowers f ≤ J ⊔ C := sup_le hI (Subgroup.zpowers_le.2 hfH)
  obtain ⟨j, hj, c, hc, hjc⟩ := (Subgroup.mem_sup_of_normal_left).1 (hle ha)
  exact ⟨j, hj, c, hc, hjc.symm⟩

private theorem ggTableB_normal_inn {R : Type*} [Group R] :
    ((MulAut.conj : R →* MulAut R).range).Normal := by
  refine Subgroup.Normal.mk (fun n hn g => ?_)
  rcases hn with ⟨z, rfl⟩
  refine ⟨g z, ?_⟩
  ext w
  simp [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, mul_assoc]

theorem ggTableB_automorphism_cover_of_product_generator {R : Type*} [Group R]
    (I : Subgroup (MulAut R)) (E : Set (MulAut R))
    (hI : I ≤ (MulAut.conj : R →* MulAut R).range ⊔ Subgroup.centralizer E)
    {u f a : MulAut R} (hu : u ∈ I) (hf : u * f ∈ Subgroup.centralizer E)
    (ha : a ∈ I ⊔ Subgroup.zpowers f) :
    ∃ ρ : R, ∀ e ∈ E, Commute ((MulAut.conj ρ)⁻¹ * a) e := by
  have : ((MulAut.conj : R →* MulAut R).range).Normal := ggTableB_normal_inn
  obtain ⟨j, hj, c, hc, hjc⟩ :=
    ggTableB_cover_of_product_generator (MulAut.conj : R →* MulAut R).range I
      (Subgroup.centralizer E) hI hu hf ha
  rcases hj with ⟨ρ, hρ⟩
  refine ⟨ρ, fun e he => ?_⟩
  have hae : (MulAut.conj ρ)⁻¹ * a = c := by
    rw [hjc, ← hρ, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hae]
  exact (Subgroup.mem_centralizer_iff.1 hc e he).symm

@[expose] def GGTableBFieldSylowMark {R : Type} [Group R] (p : ℕ) (F : Set (MulAut R))
    (f : MulAut R) : Prop :=
  f ∈ Subgroup.closure F ∧ (∃ c : ℕ, orderOf f = p ^ c) ∧
    ∀ g ∈ Subgroup.closure F, (∃ k : ℕ, g ^ p ^ k = 1) → ∃ j : ℤ, g = f ^ j

@[expose] def GGTableBMarkedFactorization {R : Type} [Group R] (p : ℕ) (I : Set (MulAut R))
    (f : MulAut R) : Prop :=
  ∀ a : MulAut R, (∃ k : ℕ, a ^ p ^ k = 1) → ∃ i ∈ I, ∃ j : ℤ, a = i * f ^ j

@[expose] def GGTableBFieldRepresentativeAt {R : Type} [Group R] (p : ℕ) (I : Set (MulAut R))
    (f : MulAut R) : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (L' E : Subgroup M)
    (θ : L' ⧸ Subgroup.center L' ≃* R) (hE : E ≤ Subgroup.normalizer (L' : Set M)),
    GGTableBPosition p L' E I θ hE →
      ∃ u ∈ I, ∀ e : E, Commute (u * f) (ggLAut L' θ ⟨e, hE e.2⟩)

@[expose] def GGTableBAbsorptionAt {R : Type} [Group R] (p : ℕ) (I : Set (MulAut R)) : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (L' E : Subgroup M)
    (θ : L' ⧸ Subgroup.center L' ≃* R) (hE : E ≤ Subgroup.normalizer (L' : Set M)),
    GGTableBPosition p L' E I θ hE →
      ∀ i ∈ I, ∃ ρ : R, ∃ t : MulAut R, i = MulAut.conj ρ * t ∧
        ∀ e : E, Commute t (ggLAut L' θ ⟨e, hE e.2⟩)

private theorem ggTableB_closure_le_of_absorption {R : Type} [Group R] {p : ℕ} {I : Set (MulAut R)}
    (habs : GGTableBAbsorptionAt p I) {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E I θ hE) :
    Subgroup.closure I ≤ (MulAut.conj : R →* MulAut R).range ⊔
      Subgroup.centralizer (Set.range fun e : E => ggLAut L' θ ⟨e, hE e.2⟩) := by
  rw [Subgroup.closure_le]
  intro i hi
  obtain ⟨ρ, t, hρt, htC⟩ := habs M L' E θ hE hpos i hi
  have htmem : t ∈ Subgroup.centralizer (Set.range fun e : E => ggLAut L' θ ⟨e, hE e.2⟩) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨e, rfl⟩
    exact (htC e).symm
  rw [hρt]
  exact Subgroup.mul_mem_sup ⟨ρ, rfl⟩ htmem

theorem ggTableB_assemble_for_generator {R : Type} [Group R] (p : ℕ) (I : Set (MulAut R))
    (f : MulAut R) (hfac : GGTableBMarkedFactorization p I f)
    (hrep : GGTableBFieldRepresentativeAt p I f) (habs : GGTableBAbsorptionAt p I) :
    GGCoverPTableB p R I := by
  intro M _ _ L' E θ hE hpos a ha
  obtain ⟨u, huI, hurep⟩ := hrep M L' E θ hE hpos
  have huC : u * f ∈ Subgroup.centralizer (Set.range fun e : E => ggLAut L' θ ⟨e, hE e.2⟩) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨e, rfl⟩
    exact (hurep e).symm
  obtain ⟨i, hiI, j, haeq⟩ := hfac a ha
  have ha_mem : a ∈ Subgroup.closure I ⊔ Subgroup.zpowers f := by
    rw [haeq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_closure_of_mem hiI)
      (Subgroup.mem_zpowers_iff.2 ⟨j, rfl⟩)
  obtain ⟨ρ, hρ⟩ := ggTableB_automorphism_cover_of_product_generator (Subgroup.closure I) _
    (ggTableB_closure_le_of_absorption habs hpos) (Subgroup.mem_closure_of_mem huI) huC ha_mem
  exact ⟨ρ, fun e => hρ _ (Set.mem_range_self e)⟩

theorem ggTableB_assemble_of_bundle {R : Type} [Group R] (p : ℕ) (F I : Set (MulAut R))
    (h : ∃ f : MulAut R, GGTableBFieldSylowMark p F f ∧ GGTableBMarkedFactorization p I f ∧
      GGTableBFieldRepresentativeAt p I f)
    (habs : GGTableBAbsorptionAt p I) : GGCoverPTableB p R I := by
  obtain ⟨f, -, hfac, hrep⟩ := h
  exact ggTableB_assemble_for_generator p I f hfac hrep habs

end CFSG.StandardType
