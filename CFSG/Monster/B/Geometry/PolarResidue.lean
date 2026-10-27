module

public import CFSG.Monster.B.Geometry.PolarFlag

public section

namespace CFSG.Monster.B.Geometry

open Module CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

section Coord

variable (K : Type*) [Field K] {n : ℕ}

@[expose] def cspan (s : Finset (Fin n)) : Submodule K (Fin n → K) :=
  Submodule.span K ((fun i => (Pi.single i 1 : Fin n → K)) '' s)

variable {K}

theorem mem_cspan {s : Finset (Fin n)} {v : Fin n → K} : v ∈ cspan K s ↔ ∀ i ∉ s, v i = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro i hi
      change (Pi.single j 1 : Fin n → K) i = 0
      have hij : i ≠ j := fun h => hi (by rw [h]; exact Finset.mem_coe.mp hj)
      simp [hij]
    | zero => intro i _; rfl
    | add x y _ _ hx hy => intro i hi; simp [hx i hi, hy i hi]
    | smul c x _ hx => intro i hi; simp [hx i hi]
  · intro hv
    have : v = ∑ i ∈ s, v i • (Pi.single i 1 : Fin n → K) := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
        mul_zero]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · exact hv j h
    rw [this]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem single_mem_cspan {s : Finset (Fin n)} {i : Fin n} (hi : i ∈ s) :
    (Pi.single i 1 : Fin n → K) ∈ cspan K s :=
  Submodule.subset_span ⟨i, hi, rfl⟩

theorem finrank_cspan (s : Finset (Fin n)) : finrank K (cspan K s) = s.card := by
  have hli : LinearIndependent K (fun i : (s : Set (Fin n)) => (Pi.single (i : Fin n) 1 :
      Fin n → K)) := by
    have := (Pi.basisFun K (Fin n)).linearIndependent.comp _
      (Subtype.val_injective (p := fun i => i ∈ (s : Set (Fin n))))
    simpa [Function.comp_def] using this
  have h := finrank_span_eq_card hli
  have e : cspan K s = Submodule.span K (Set.range fun i : (s : Set (Fin n)) =>
      (Pi.single (i : Fin n) 1 : Fin n → K)) := by
    rw [cspan, Set.image_eq_range]
  rw [e, h]
  simp

theorem cspan_mono {s t : Finset (Fin n)} (h : s ⊆ t) : cspan K s ≤ cspan K t :=
  Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr h))

theorem cspan_singleton (i : Fin n) : cspan K {i} = K ∙ (Pi.single i 1 : Fin n → K) := by
  rw [cspan, Finset.coe_singleton, Set.image_singleton]

theorem cspan_insert (i : Fin n) (s : Finset (Fin n)) :
    cspan K (insert i s) = K ∙ (Pi.single i 1 : Fin n → K) ⊔ cspan K s := by
  rw [cspan, cspan, Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert]

theorem map_cspan_insert {V : Type*} [AddCommGroup V] [Module K V] (g : (Fin n → K) →ₗ[K] V)
    (i : Fin n) (s : Finset (Fin n)) :
    (cspan K (insert i s)).map g = K ∙ g (Pi.single i 1) ⊔ (cspan K s).map g := by
  rw [cspan_insert, Submodule.map_sup, Submodule.map_span, Set.image_singleton]

theorem map_cspan_singleton {V : Type*} [AddCommGroup V] [Module K V]
    (g : (Fin n → K) →ₗ[K] V) (i : Fin n) : (cspan K {i}).map g = K ∙ g (Pi.single i 1) := by
  rw [cspan_singleton, Submodule.map_span, Set.image_singleton]

@[expose] def coordFlag (P : PolarSpace K (Fin n → K)) (s₁ s₂ s₃ : Finset (Fin n))
    (h1 : s₁.card = 1) (h2 : s₂.card = 2) (h3 : s₃.card = 3) (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃)
    (hTI : ∀ v ∈ cspan K s₃, P.Iso v) : PFlag P :=
  ⟨cspan K s₁, cspan K s₂, cspan K s₃, by rw [finrank_cspan, h1], by rw [finrank_cspan, h2],
    by rw [finrank_cspan, h3], cspan_mono h12, cspan_mono h23, hTI⟩

end Coord

section InjOn

variable {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V']
  [Module K V'] (ρ : V →ₗ[K] V') {S : Submodule K V} (hρ : Set.InjOn ρ S)
include hρ

theorem finrank_map_of_injOn {U : Submodule K V} (hUS : U ≤ S) :
    finrank K (U.map ρ) = finrank K U := by
  have hinj : Function.Injective (ρ ∘ₗ U.subtype) := fun a b h =>
    Subtype.ext (hρ (hUS a.2) (hUS b.2) h)
  rw [← LinearMap.finrank_range_of_inj hinj, LinearMap.range_comp, Submodule.range_subtype]

theorem eq_of_map_eq_of_injOn {U U' : Submodule K V} (hU : U ≤ S) (hU' : U' ≤ S)
    (h : U.map ρ = U'.map ρ) : U = U' := by
  have key : ∀ {A B : Submodule K V}, A ≤ S → B ≤ S → A.map ρ = B.map ρ → A ≤ B := by
    intro A B hA hB hAB v hv
    obtain ⟨w, hw, hwv⟩ := (Submodule.mem_map.mp (hAB ▸ Submodule.mem_map_of_mem hv :
      ρ v ∈ B.map ρ))
    rw [← hρ (hB hw) (hA hv) hwv]
    exact hw
  exact le_antisymm (key hU hU' h) (key hU' hU h.symm)

theorem map_inf_comap_of_injOn [FiniteDimensional K V] [FiniteDimensional K V']
    (hdim : finrank K S = finrank K V') (U' : Submodule K V') :
    (S ⊓ U'.comap ρ).map ρ = U' := by
  have hsurj : LinearMap.range (ρ ∘ₗ S.subtype) = ⊤ := by
    have hinj : Function.Injective (ρ ∘ₗ S.subtype) := fun a b h =>
      Subtype.ext (hρ a.2 b.2 h)
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [LinearMap.finrank_range_of_inj hinj, hdim]
  refine le_antisymm ?_ fun w hw => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact (Submodule.mem_inf.mp hv).2
  · obtain ⟨⟨v, hvS⟩, hv⟩ := LinearMap.mem_range.mp (hsurj ▸ Submodule.mem_top : w ∈ _)
    refine ⟨v, Submodule.mem_inf.mpr ⟨hvS, ?_⟩, hv⟩
    change ρ v ∈ U'
    rw [show ρ v = w from hv]
    exact hw

end InjOn

section PlaneResidue

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {P : PolarSpace K V} {ι : Type*} {p l π : ι}
  {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {C : Type*} {δ : C → C → W} {f : C → PFlag P}

omit [FiniteDimensional K V] in
theorem PFlag.V₁_le_V₃ (x : PFlag P) : x.V₁ ≤ x.V₃ := x.le₁₂.trans x.le₂₃

open _root_.Classical in
@[expose] noncomputable def planeResidueModel (f : C → PFlag P) (x : C)
    (ρ : V →ₗ[K] (Fin 3 → K)) (hρ : Set.InjOn ρ (f x).V₃) (y : C) : PlaneFlag K :=
  if h : (f y).V₃ = (f x).V₃ then
    ⟨(f y).V₁.map ρ, (f y).V₂.map ρ,
      (finrank_map_of_injOn ρ hρ (h ▸ (f y).V₁_le_V₃)).trans (f y).finrank₁,
      (finrank_map_of_injOn ρ hρ (h ▸ (f y).le₂₃)).trans (f y).finrank₂,
      Submodule.map_mono (f y).le₁₂⟩
  else PlaneFlag.c K

variable {x : C} (ρ : V →ₗ[K] (Fin 3 → K)) (hρ : Set.InjOn ρ (f x).V₃)

omit [FiniteDimensional K V] in
theorem planeResidueModel_pt {y : C} (h : (f y).V₃ = (f x).V₃) :
    (planeResidueModel f x ρ hρ y).pt = (f y).V₁.map ρ := by
  rw [planeResidueModel, dite_eq_left h]

omit [FiniteDimensional K V] in
theorem planeResidueModel_line {y : C} (h : (f y).V₃ = (f x).V₃) :
    (planeResidueModel f x ρ hρ y).line = (f y).V₂.map ρ := by
  rw [planeResidueModel, dite_eq_left h]

variable (hf : IsChamberModel cs δ (polarChamber P p l π) f) (hpl : p ≠ l) (hlπ : l ≠ π)
  (hpπ : p ≠ π)
include hf hpl hlπ hpπ

theorem isModelResidue_planeResidueModel :
    IsModelResidue cs δ PlaneFlag.SameLine PlaneFlag.SamePt p l x (planeResidueModel f x ρ hρ) := by
  have hR : ∀ y, y ∈ residue cs δ {p, l} x ↔ (f y).V₃ = (f x).V₃ := fun y =>
    polar_mem_residue_pl hf hpl hlπ hpπ
  have hdim : finrank K (f x).V₃ = finrank K (Fin 3 → K) := by
    rw [(f x).finrank₃, Module.finrank_fin_fun]
  refine ⟨⟨fun _ _ => Set.mem_univ _, fun y hy z hz e => ?_, fun F _ => ?_⟩, fun y hy z hz => ?_⟩
  · have hy' := (hR y).mp hy
    have hz' := (hR z).mp hz
    have e1 := congrArg PlaneFlag.pt e
    have e2 := congrArg PlaneFlag.line e
    rw [planeResidueModel_pt ρ hρ hy', planeResidueModel_pt ρ hρ hz'] at e1
    rw [planeResidueModel_line ρ hρ hy', planeResidueModel_line ρ hρ hz'] at e2
    refine hf.1.1 (PFlag.ext ?_ ?_ (hy'.trans hz'.symm))
    · exact eq_of_map_eq_of_injOn ρ hρ (hy' ▸ (f y).V₁_le_V₃) (hz' ▸ (f z).V₁_le_V₃) e1
    · exact eq_of_map_eq_of_injOn ρ hρ (hy' ▸ (f y).le₂₃) (hz' ▸ (f z).le₂₃) e2
  ·
    set S := (f x).V₃
    have hmap := map_inf_comap_of_injOn ρ hρ hdim
    have h1 : finrank K ↥(S ⊓ F.pt.comap ρ) = 1 := by
      rw [← finrank_map_of_injOn ρ hρ inf_le_left, hmap, F.finrank_pt]
    have h2 : finrank K ↥(S ⊓ F.line.comap ρ) = 2 := by
      rw [← finrank_map_of_injOn ρ hρ inf_le_left, hmap, F.finrank_line]
    obtain ⟨y, hy⟩ := hf.1.2 ⟨S ⊓ F.pt.comap ρ, S ⊓ F.line.comap ρ, S, h1, h2, (f x).finrank₃,
      inf_le_inf_left _ (Submodule.comap_mono F.pt_le_line), inf_le_left, (f x).isTI⟩
    have hy3 : (f y).V₃ = S := by rw [hy]
    refine ⟨y, (hR y).mpr hy3, PlaneFlag.ext ?_ ?_⟩
    · rw [planeResidueModel_pt ρ hρ hy3, hy]
      exact hmap F.pt
    · rw [planeResidueModel_line ρ hρ hy3, hy]
      exact hmap F.line
  · have hy' := (hR y).mp hy
    have hz' := (hR z).mp hz
    have hinj : ∀ {A B : Submodule K V}, A ≤ (f x).V₃ → B ≤ (f x).V₃ →
        (A.map ρ = B.map ρ ↔ A = B) := fun hA hB =>
      ⟨eq_of_map_eq_of_injOn ρ hρ hA hB, fun h => h ▸ rfl⟩
    rw [hf.2, hf.2, polarChamber_adj_p, polarChamber_adj_l hpl]
    simp only [PlaneFlag.SameLine, PlaneFlag.SamePt, planeResidueModel_pt ρ hρ hy',
      planeResidueModel_pt ρ hρ hz', planeResidueModel_line ρ hρ hy',
      planeResidueModel_line ρ hρ hz', hinj (hy' ▸ (f y).le₂₃) (hz' ▸ (f z).le₂₃),
      hinj (hy' ▸ (f y).V₁_le_V₃) (hz' ▸ (f z).V₁_le_V₃), hy', hz', and_true]

theorem isPlaneFlagResidue_polar (ρ' : V →ₗ[K] (Fin 3 → K)) (hρ' : Set.InjOn ρ' (f x).V₃) :
    IsPlaneFlagResidue cs δ K p l x :=
  ⟨_, Or.inr (isModelResidue_planeResidueModel ρ' hρ' hf hpl hlπ hpπ)⟩

end PlaneResidue

end CFSG.Monster.B.Geometry
