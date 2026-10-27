module

public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.Finsupp.SMul

public section

namespace CFSG.RankThree.GF2n.Smith81.Gen76

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def act (g : (Module.End K V)ˣ) (P : Submodule K V) : Submodule K V :=
  P.map (g : Module.End K V)

theorem act_mul (g h : (Module.End K V)ˣ) (P : Submodule K V) :
    act (g * h) P = act g (act h P) := by
  simp only [act, Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp]

theorem act_one (P : Submodule K V) : act 1 P = P := by
  rw [act, Units.val_one, Module.End.one_eq_id, Submodule.map_id]

theorem act_injective (g : (Module.End K V)ˣ) : Function.Injective (act g) := by
  apply Submodule.map_injective_of_injective
  intro x y h
  calc x = (↑g⁻¹ * ↑g : Module.End K V) x := by rw [Units.inv_mul, Module.End.one_apply]
    _ = (↑g⁻¹ * ↑g : Module.End K V) y := by rw [Module.End.mul_apply, h, ← Module.End.mul_apply]
    _ = y := by rw [Units.inv_mul, Module.End.one_apply]

theorem act_span_singleton (g : (Module.End K V)ˣ) (v : V) :
    act g (K ∙ v) = K ∙ ((g : Module.End K V) v) := by
  simp [act, Submodule.map_span, Set.image_singleton]

@[expose] def IsLine (Γ : Subgroup (Module.End K V)ˣ) (𝓛₀ 𝓛 : Set (Submodule K V)) : Prop :=
  ∃ g ∈ Γ, 𝓛 = act g '' 𝓛₀

@[expose] def IsLineClosed (Γ : Subgroup (Module.End K V)ˣ) (𝓛₀ S : Set (Submodule K V)) :
    Prop :=
  ∀ 𝓛, IsLine Γ 𝓛₀ 𝓛 → ∀ P ∈ 𝓛, ∀ P' ∈ 𝓛, P ≠ P' → P ∈ S → P' ∈ S → 𝓛 ⊆ S

theorem IsLine.act {Γ : Subgroup (Module.End K V)ˣ} {𝓛₀ 𝓛 : Set (Submodule K V)}
    (h : IsLine Γ 𝓛₀ 𝓛) {u : (Module.End K V)ˣ} (hu : u ∈ Γ) :
    IsLine Γ 𝓛₀ (act u '' 𝓛) := by
  obtain ⟨g, hg, rfl⟩ := h
  refine ⟨u * g, Γ.mul_mem hu hg, ?_⟩
  rw [Set.image_image]
  exact Set.image_congr fun P _ => (act_mul u g P).symm

theorem IsLineClosed.preimage {Γ : Subgroup (Module.End K V)ˣ} {𝓛₀ S : Set (Submodule K V)}
    (hS : IsLineClosed Γ 𝓛₀ S) {u : (Module.End K V)ˣ} (hu : u ∈ Γ) :
    IsLineClosed Γ 𝓛₀ (act u ⁻¹' S) := by
  intro 𝓛 h𝓛 P hP P' hP' hne hPS hP'S Q hQ
  exact hS _ (h𝓛.act hu) _ ⟨P, hP, rfl⟩ _ ⟨P', hP', rfl⟩
    (fun h => hne (act_injective u h)) hPS hP'S ⟨Q, hQ, rfl⟩

theorem act_mem_of_isLineClosed {Γ : Subgroup (Module.End K V)ˣ} {R : Set (Module.End K V)ˣ}
    (hR : Subgroup.closure R = Γ) (hRinv : ∀ u ∈ R, u⁻¹ ∈ R) {𝓛₀ Pts : Set (Submodule K V)}
    (hPts : ∀ u ∈ R, ∀ P ∈ Pts, act u P ∈ Pts ∨ ∃ 𝓛, IsLine Γ 𝓛₀ 𝓛 ∧ act u P ∈ 𝓛 ∧
      ∃ P₁ ∈ 𝓛, ∃ P₂ ∈ 𝓛, P₁ ≠ P₂ ∧ P₁ ∈ Pts ∧ P₂ ∈ Pts)
    {S : Set (Submodule K V)} (hS : IsLineClosed Γ 𝓛₀ S) (hPtsS : Pts ⊆ S)
    {g : (Module.End K V)ˣ} (hg : g ∈ Γ) {P : Submodule K V} (hP : P ∈ Pts) : act g P ∈ S := by
  have hRΓ : R ⊆ Γ := hR ▸ Subgroup.subset_closure
  set T : Set (Submodule K V) := {Q | ∀ S', IsLineClosed Γ 𝓛₀ S' → Pts ⊆ S' → Q ∈ S'} with hT
  have hPtsT : Pts ⊆ T := fun Q hQ S' _ hS' => hS' hQ
  have hstep : ∀ u ∈ R, ∀ Q ∈ T, act u Q ∈ T := by
    intro u hu Q hQ S' hS'c hS'Pts
    refine hQ (act u ⁻¹' S') (hS'c.preimage (hRΓ hu)) fun Q' hQ' => ?_
    rcases hPts u hu Q' hQ' with h | ⟨𝓛, h𝓛, hQ'𝓛, P₁, hP₁, P₂, hP₂, hne, hP₁Pts, hP₂Pts⟩
    · exact hS'Pts h
    · exact hS'c 𝓛 h𝓛 P₁ hP₁ P₂ hP₂ hne (hS'Pts hP₁Pts) (hS'Pts hP₂Pts) hQ'𝓛
  have hall : ∀ x ∈ Subgroup.closure R, ∀ Q ∈ T, act x Q ∈ T := by
    intro x hx
    induction hx using Subgroup.closure_induction'' with
    | mem x hx => exact hstep x hx
    | inv_mem x hx => exact hstep x⁻¹ (hRinv x hx)
    | one => intro Q hQ; rwa [act_one]
    | mul x y _ _ ihx ihy => intro Q hQ; rw [act_mul]; exact ihx _ (ihy Q hQ)
  exact hall g (hR ▸ hg) P (hPtsT hP) S hS hPtsS

section Basis

variable {ι : Type*}

@[expose] def Moves (g : (Module.End K (ι →₀ K))ˣ) (σ : ι → ι) : Prop :=
  ∀ c, (g : Module.End K (ι →₀ K)) (Finsupp.single c 1) = Finsupp.single (σ c) 1

theorem Moves.one : Moves (1 : (Module.End K (ι →₀ K))ˣ) id := fun _ => rfl

theorem Moves.mul {g h : (Module.End K (ι →₀ K))ˣ} {σ τ : ι → ι} (hg : Moves g σ)
    (hh : Moves h τ) : Moves (g * h) (σ ∘ τ) := by
  intro c
  rw [Units.val_mul, Module.End.mul_apply, hh c, hg (τ c), Function.comp_apply]

@[expose] def rootLine (a b : ι) : Set (Submodule K (ι →₀ K)) :=
  insert (K ∙ Finsupp.single b 1)
    (Set.range fun t : K => K ∙ (Finsupp.single a 1 + t • Finsupp.single b 1))

theorem left_mem_rootLine (a b : ι) : (K ∙ Finsupp.single a (1 : K)) ∈ rootLine a b :=
  Set.mem_insert_of_mem _ ⟨0, by simp⟩

theorem right_mem_rootLine (a b : ι) : (K ∙ Finsupp.single b (1 : K)) ∈ rootLine a b :=
  Set.mem_insert _ _

theorem Moves.image_rootLine {g : (Module.End K (ι →₀ K))ˣ} {σ : ι → ι} (hg : Moves g σ)
    (a b : ι) : act g '' rootLine a b = rootLine (σ a) (σ b) := by
  rw [rootLine, rootLine, Set.image_insert_eq, ← Set.range_comp, act_span_singleton, hg b]
  congr 1
  refine congrArg Set.range (funext fun t => ?_)
  rw [Function.comp_apply, act_span_singleton, map_add, map_smul, hg a, hg b]

theorem span_single_ne {a b : ι} (h : a ≠ b) :
    (K ∙ Finsupp.single a (1 : K)) ≠ K ∙ Finsupp.single b 1 := by
  intro he
  have hb : Finsupp.single b (1 : K) ∈ K ∙ Finsupp.single a (1 : K) :=
    he ▸ Submodule.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hb
  have := congrArg (fun v : ι →₀ K => v b) hr
  simp [Finsupp.single_apply, h] at this

theorem span_mem_of_rootLines {Γ : Subgroup (Module.End K (ι →₀ K))ˣ}
    {R : Set (Module.End K (ι →₀ K))ˣ} (hR : Subgroup.closure R = Γ)
    (hRinv : ∀ u ∈ R, u⁻¹ ∈ R) {𝓛₀ : Set (Submodule K (ι →₀ K))}
    (hu : ∀ u ∈ R, ∀ c : ι,
      (u : Module.End K (ι →₀ K)) (Finsupp.single c 1) = Finsupp.single c 1 ∨
      ∃ b, b ≠ c ∧ IsLine Γ 𝓛₀ (rootLine c b) ∧ ∃ t : K,
        (u : Module.End K (ι →₀ K)) (Finsupp.single c 1) =
          Finsupp.single c 1 + t • Finsupp.single b 1)
    {S : Set (Submodule K (ι →₀ K))} (hS : IsLineClosed Γ 𝓛₀ S)
    (hP : ∀ c : ι, (K ∙ Finsupp.single c (1 : K)) ∈ S)
    {g : (Module.End K (ι →₀ K))ˣ} (hg : g ∈ Γ) (c : ι) :
    (K ∙ (g : Module.End K (ι →₀ K)) (Finsupp.single c 1)) ∈ S := by
  rw [← act_span_singleton]
  refine act_mem_of_isLineClosed hR hRinv (Pts := Set.range fun c => K ∙ Finsupp.single c 1)
    ?_ hS (Set.range_subset_iff.2 hP) hg ⟨c, rfl⟩
  rintro u huR _ ⟨c', rfl⟩
  rw [act_span_singleton]
  rcases hu u huR c' with h | ⟨b, hb, hline, t, ht⟩
  · exact Or.inl ⟨c', by rw [h]⟩
  · refine Or.inr ⟨rootLine c' b, hline, ?_, _, left_mem_rootLine c' b, _,
      right_mem_rootLine c' b, span_single_ne hb.symm, ⟨c', rfl⟩, ⟨b, rfl⟩⟩
    rw [ht]
    exact Set.mem_insert_of_mem _ ⟨t, rfl⟩

end Basis

end CFSG.RankThree.GF2n.Smith81.Gen76
