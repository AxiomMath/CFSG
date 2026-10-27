module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoStd

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open scoped Matrix

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ} (hR : TauCeti.IsFiniteType R)

abbrev Wg : Type := (coxeterMatrix hR).Group

abbrev sg (i : ι) : Wg hR := (coxeterMatrix hR).toCoxeterSystem.simple i

@[expose] def IsRt (v : ι → ℤ) : Prop := ∃ (w : Wg hR) (j : ι), weylAction hR w (Pi.single j 1) = v

open Classical in
@[expose] noncomputable def rRefl (β : ι → ℤ) : Wg hR :=
  if h : IsRt hR β then
    Classical.choose h * sg hR (Classical.choose (Classical.choose_spec h)) *
      (Classical.choose h)⁻¹
  else 1

@[expose] def Refl : Set (Wg hR) := {g | ∃ (w : Wg hR) (i : ι), g = w * sg hR i * w⁻¹}

inductive Cl (S : Set (ι → ℤ)) : (ι → ℤ) → Prop
  | base {β : ι → ℤ} : β ∈ S → Cl S β
  | refl {α β : ι → ℤ} : Cl S α → Cl S β → Cl S (weylAction hR (rRefl hR α) β)

@[expose] def Wsub (S : Set (ι → ℤ)) : Subgroup (Wg hR) := Subgroup.closure (rRefl hR '' S)

@[expose] def TCRoot (Φ : Set (ι → ℤ)) : Prop :=
  ∀ S : Set (ι → ℤ), (∀ β ∈ S, IsRt hR β) → ∃ S' : Finset (ι → ℤ), (S' : Set (ι → ℤ)) ⊆ S ∧
    S'.card ≤ 2 ∧ Cl hR (Φ ∪ S) = Cl hR (Φ ∪ (S' : Set (ι → ℤ)))

@[expose] def TwoCover (X : Subgroup (Wg hR)) : Prop :=
  ∀ T : Set (Wg hR), T ⊆ Refl hR → ∃ T' : Finset (Wg hR), (T' : Set (Wg hR)) ⊆ T ∧ T'.card ≤ 2 ∧
    X ⊔ Subgroup.closure T = X ⊔ Subgroup.closure (T' : Set (Wg hR))

theorem isRt_smul {β : ι → ℤ} (hβ : IsRt hR β) (w : Wg hR) : IsRt hR (weylAction hR w β) := by
  obtain ⟨w', j, rfl⟩ := hβ
  exact ⟨w * w', j, weylAction_mul_apply hR w w' (Pi.single j 1)⟩

private theorem levTwoS1_coroot_conj {u : Wg hR} {i j : ι}
    (h : weylAction hR u (Pi.single i 1) = Pi.single j 1) (x : ι → ℤ) :
    coroot R j x = coroot R i (weylAction hR u⁻¹ x) := by
  have hsym : symmetrizer hR i = symmetrizer hR j := by
    have h2 : form hR (toRat (Pi.single j 1)) (toRat (Pi.single j 1)) =
        form hR (toRat (Pi.single i 1)) (toRat (Pi.single i 1)) := by
      have := form_weylAction hR u (Pi.single i 1) (Pi.single i 1)
      rwa [h] at this
    rw [toRat_single, toRat_single, form_single_single, form_single_single] at h2
    linarith
  have hq : symmetrizer hR j * (coroot R j x : ℚ) =
      symmetrizer hR i * (coroot R i (weylAction hR u⁻¹ x) : ℚ) := by
    have hform : form hR (toRat (Pi.single j 1)) (toRat x) =
        form hR (toRat (Pi.single i 1)) (toRat (weylAction hR u⁻¹ x)) := by
      have := form_weylAction hR u (Pi.single i 1) (weylAction hR u⁻¹ x)
      rwa [h, weylAction_apply_inv_apply] at this
    rw [toRat_single, toRat_single, form_single_left, form_single_left] at hform
    rw [coroot_apply, coroot_apply]
    push_cast
    simpa only [toRat_apply] using hform
  rw [hsym] at hq
  exact_mod_cast mul_left_cancel₀ (symmetrizer_pos hR j).ne' hq

theorem rRefl_eq_conj {β : ι → ℤ} {w : Wg hR} {j : ι}
    (h : weylAction hR w (Pi.single j 1) = β) : rRefl hR β = w * sg hR j * w⁻¹ := by
  have hβ : IsRt hR β := ⟨w, j, h⟩
  have hspec : weylAction hR (Classical.choose hβ)
      (Pi.single (Classical.choose (Classical.choose_spec hβ)) 1) = β :=
    Classical.choose_spec (Classical.choose_spec hβ)
  set u := Classical.choose hβ with hu
  set i := Classical.choose (Classical.choose_spec hβ) with hi
  have hui : weylAction hR u (Pi.single i 1) = β := by rw [hu, hi]; exact hspec
  have hrr : rRefl hR β = u * sg hR i * u⁻¹ := by
    simp only [rRefl, hβ, ↓reduceDIte]
    rw [hu, hi]
  have hv : weylAction hR (w⁻¹ * u) (Pi.single i 1) = Pi.single j 1 := by
    rw [weylAction_mul_apply, hui, ← h, weylAction_inv_apply_apply]
  have hvconj : w⁻¹ * u * sg hR i * (w⁻¹ * u)⁻¹ = sg hR j := by
    apply weylAction_injective hR
    refine LinearMap.ext fun x => ?_
    calc weylAction hR (w⁻¹ * u * sg hR i * (w⁻¹ * u)⁻¹) x
        = weylAction hR (w⁻¹ * u)
            (weylAction hR (sg hR i) (weylAction hR (w⁻¹ * u)⁻¹ x)) := by
          rw [weylAction_mul_apply, weylAction_mul_apply]
      _ = weylAction hR (w⁻¹ * u)
            (weylAction hR (w⁻¹ * u)⁻¹ x -
              (coroot R i (weylAction hR (w⁻¹ * u)⁻¹ x)) • Pi.single i 1) := by
          rw [weylAction_simple, reflection_apply_coroot]
      _ = x - (coroot R j x) • Pi.single j 1 := by
          rw [map_sub, map_zsmul, weylAction_apply_inv_apply,
            ← levTwoS1_coroot_conj hR hv x, hv]
      _ = weylAction hR (sg hR j) x := by
          rw [weylAction_simple, reflection_apply_coroot]
  have heq : u * sg hR i * u⁻¹ = w * sg hR j * w⁻¹ := by
    calc u * sg hR i * u⁻¹ = w * (w⁻¹ * u * sg hR i * (w⁻¹ * u)⁻¹) * w⁻¹ := by
          rw [show u = w * (w⁻¹ * u) from (mul_inv_cancel_left w u).symm]
          group
      _ = w * sg hR j * w⁻¹ := by rw [hvconj]
  rw [hrr, heq]

theorem mem_Refl_iff {g : Wg hR} : g ∈ Refl hR ↔ ∃ β, IsRt hR β ∧ rRefl hR β = g := by
  constructor
  · rintro ⟨w, i, rfl⟩
    exact ⟨weylAction hR w (Pi.single i 1), ⟨w, i, rfl⟩, rRefl_eq_conj hR rfl⟩
  · rintro ⟨β, hβ, rfl⟩
    obtain ⟨u, i, hui⟩ := hβ
    exact ⟨u, i, rRefl_eq_conj hR hui⟩

theorem rRefl_smul {β : ι → ℤ} (hβ : IsRt hR β) (w : Wg hR) :
    rRefl hR (weylAction hR w β) = w * rRefl hR β * w⁻¹ := by
  obtain ⟨u, j, hu⟩ := hβ
  rw [rRefl_eq_conj hR (show weylAction hR (w * u) (Pi.single j 1) = weylAction hR w β by
        rw [weylAction_mul_apply, hu]),
      rRefl_eq_conj hR hu]
  group

theorem isRt_neg {β : ι → ℤ} (hβ : IsRt hR β) : IsRt hR (-β) := by
  obtain ⟨u, j, hu⟩ := hβ
  exact ⟨u * sg hR j, j, by rw [weylAction_mul_apply, weylAction_simple_single, map_neg, hu]⟩

theorem rRefl_neg {β : ι → ℤ} (hβ : IsRt hR β) : rRefl hR (-β) = rRefl hR β := by
  obtain ⟨u, j, hu⟩ := hβ
  have hneg : weylAction hR (u * sg hR j) (Pi.single j 1) = -β := by
    rw [weylAction_mul_apply, weylAction_simple_single, map_neg, hu]
  have hs : sg hR j * sg hR j = 1 :=
    (coxeterMatrix hR).toCoxeterSystem.simple_mul_simple_self j
  have hsinv : (sg hR j)⁻¹ = sg hR j := inv_eq_of_mul_eq_one_right hs
  rw [rRefl_eq_conj hR hneg, rRefl_eq_conj hR hu, mul_inv_rev, hsinv]
  calc (u * sg hR j) * sg hR j * (sg hR j * u⁻¹)
      = u * (sg hR j * sg hR j) * (sg hR j * u⁻¹) := by group
    _ = u * sg hR j * u⁻¹ := by rw [hs]; group

theorem weylAction_rRefl {β : ι → ℤ} (hβ : IsRt hR β) (v : ι → ℤ) :
    ∃ k : ℤ, (k : ℚ) * form hR (toRat β) (toRat β) = 2 * form hR (toRat β) (toRat v) ∧
      weylAction hR (rRefl hR β) v = v - k • β := by
  obtain ⟨u, j, hu⟩ := hβ
  refine ⟨coroot R j (weylAction hR u⁻¹ v), ?_, ?_⟩
  · have hbb : form hR (toRat β) (toRat β) = 2 * symmetrizer hR j := by
      rw [← hu, form_weylAction, toRat_single, form_single_single]
    have hv' : toRat v = toRat (weylAction hR u (weylAction hR u⁻¹ v)) := by
      rw [weylAction_apply_inv_apply]
    have hbv : form hR (toRat β) (toRat v) =
        symmetrizer hR j * (coroot R j (weylAction hR u⁻¹ v) : ℚ) := by
      rw [← hu, hv', form_weylAction, toRat_single, form_single_left]
      congr 1
      rw [coroot_apply]
      push_cast
      simp only [toRat_apply]
    rw [hbb, hbv]; ring
  · rw [rRefl_eq_conj hR hu]
    calc weylAction hR (u * sg hR j * u⁻¹) v
        = weylAction hR u (weylAction hR (sg hR j) (weylAction hR u⁻¹ v)) := by
          rw [weylAction_mul_apply, weylAction_mul_apply]
      _ = weylAction hR u
            (weylAction hR u⁻¹ v - (coroot R j (weylAction hR u⁻¹ v)) • Pi.single j 1) := by
          rw [weylAction_simple, reflection_apply_coroot]
      _ = v - (coroot R j (weylAction hR u⁻¹ v)) • β := by
          rw [map_sub, map_zsmul, weylAction_apply_inv_apply, hu]

theorem Cl_isRt {S : Set (ι → ℤ)} (hS : ∀ β ∈ S, IsRt hR β) {β : ι → ℤ} (h : Cl hR S β) :
    IsRt hR β := by
  induction h with
  | base hβ => exact hS _ hβ
  | refl hα hβ ihα ihβ => exact isRt_smul hR ihβ (rRefl hR _)

theorem Wsub_Cl {S : Set (ι → ℤ)} (hS : ∀ β ∈ S, IsRt hR β) :
    Wsub hR {β | Cl hR S β} = Wsub hR S := by
  refine le_antisymm ?_ ?_
  · rw [Wsub, Subgroup.closure_le]
    rintro _ ⟨γ, hγ, rfl⟩
    induction hγ with
    | base hb => exact Subgroup.subset_closure ⟨_, hb, rfl⟩
    | refl hα hβ ihα ihβ =>
        rw [rRefl_smul hR (Cl_isRt hR hS hβ) (rRefl hR _)]
        exact mul_mem (mul_mem ihα ihβ) (inv_mem ihα)
  · rw [Wsub]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨γ, hγ, rfl⟩
    exact ⟨γ, Cl.base hγ, rfl⟩

theorem Cl_smul {S : Set (ι → ℤ)} (hS : ∀ β ∈ S, IsRt hR β) (w : Wg hR) :
    Cl hR (weylAction hR w '' S) = fun β => Cl hR S (weylAction hR w⁻¹ β) := by
  have hS' : ∀ β ∈ weylAction hR w '' S, IsRt hR β := by
    rintro β ⟨α, hα, rfl⟩
    exact isRt_smul hR (hS α hα) w
  have h2 : ∀ γ, Cl hR S γ → Cl hR (weylAction hR w '' S) (weylAction hR w γ) :=
    fun γ hγ => Cl.rec (motive := fun γ _ => Cl hR (weylAction hR w '' S) (weylAction hR w γ))
      (fun {γ} hb => Cl.base ⟨γ, hb, rfl⟩)
      (fun {α β} hα hβ ihα ihβ => by
        have hαr : IsRt hR α := Cl_isRt hR hS hα
        have heq : weylAction hR (rRefl hR (weylAction hR w α)) (weylAction hR w β) =
            weylAction hR w (weylAction hR (rRefl hR α) β) := by
          rw [rRefl_smul hR hαr w, weylAction_mul_apply, weylAction_mul_apply,
            weylAction_inv_apply_apply]
        rw [← heq]
        exact Cl.refl ihα ihβ) hγ
  have h1 : ∀ β, Cl hR (weylAction hR w '' S) β → Cl hR S (weylAction hR w⁻¹ β) :=
    fun β hβ => Cl.rec (motive := fun β _ => Cl hR S (weylAction hR w⁻¹ β))
      (fun {β} hb => by
        obtain ⟨α, hαS, rfl⟩ := hb
        rw [weylAction_inv_apply_apply]
        exact Cl.base hαS)
      (fun {α β} hα hβ ihα ihβ => by
        have hαr : IsRt hR α := Cl_isRt hR hS' hα
        have heq : weylAction hR (rRefl hR (weylAction hR w⁻¹ α)) (weylAction hR w⁻¹ β) =
            weylAction hR w⁻¹ (weylAction hR (rRefl hR α) β) := by
          rw [rRefl_smul hR hαr w⁻¹, inv_inv, weylAction_mul_apply, weylAction_mul_apply,
            weylAction_apply_inv_apply]
        rw [← heq]
        exact Cl.refl ihα ihβ) hβ
  funext β
  exact propext ⟨h1 β, fun h => by
    have h' := h2 (weylAction hR w⁻¹ β) h
    rwa [weylAction_apply_inv_apply hR w β] at h'⟩

theorem tcRoot_smul {Φ : Set (ι → ℤ)} (hΦ : ∀ β ∈ Φ, IsRt hR β) (w : Wg hR) (h : TCRoot hR Φ) :
    TCRoot hR (weylAction hR w '' Φ) := by
  intro S hS
  have hS0 : ∀ β ∈ {β | weylAction hR w β ∈ S}, IsRt hR β := by
    intro β hβ
    have h' := isRt_smul hR (hS _ hβ) w⁻¹
    rwa [weylAction_inv_apply_apply] at h'
  obtain ⟨S₀', hS₀'sub, hcard, hCl⟩ := h {β | weylAction hR w β ∈ S} hS0
  refine ⟨S₀'.image (weylAction hR w), ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hγ
    exact hS₀'sub hβ
  · calc (S₀'.image (weylAction hR w)).card ≤ S₀'.card := Finset.card_image_le
      _ ≤ 2 := hcard
  · have himg : weylAction hR w '' (Φ ∪ {β | weylAction hR w β ∈ S}) =
        (weylAction hR w '' Φ) ∪ S := by
      rw [Set.image_union]
      congr 1
      ext γ
      constructor
      · rintro ⟨β, hβ, rfl⟩; exact hβ
      · intro hγ
        refine ⟨weylAction hR w⁻¹ γ, ?_, ?_⟩
        · change weylAction hR w (weylAction hR w⁻¹ γ) ∈ S
          rw [weylAction_apply_inv_apply]
          exact hγ
        · rw [weylAction_apply_inv_apply]
    have himg' : weylAction hR w '' (Φ ∪ (S₀' : Set (ι → ℤ))) =
        (weylAction hR w '' Φ) ∪ (S₀'.image (weylAction hR w) : Set (ι → ℤ)) := by
      rw [Set.image_union, Finset.coe_image]
    have hΦS0 : ∀ β ∈ Φ ∪ {β | weylAction hR w β ∈ S}, IsRt hR β := by
      intro β hβ
      rcases hβ with hβ | hβ
      · exact hΦ β hβ
      · exact hS0 β hβ
    have hΦS0' : ∀ β ∈ Φ ∪ (S₀' : Set (ι → ℤ)), IsRt hR β := by
      intro β hβ
      rcases hβ with hβ | hβ
      · exact hΦ β hβ
      · exact hS0 β (hS₀'sub hβ)
    rw [← himg, ← himg', Cl_smul hR hΦS0 w, Cl_smul hR hΦS0' w, hCl]

theorem twoCover_of_tcRoot {Φ : Set (ι → ℤ)} (hΦ : ∀ β ∈ Φ, IsRt hR β) (h : TCRoot hR Φ) :
    TwoCover hR (Wsub hR Φ) := by
  classical
  intro T hT
  set S : Set (ι → ℤ) := {β | IsRt hR β ∧ rRefl hR β ∈ T} with hSdef
  have hSdef' : ∀ β, β ∈ S ↔ IsRt hR β ∧ rRefl hR β ∈ T := by
    intro β
    simp only [hSdef, Set.mem_setOf_eq]
  have hS : ∀ β ∈ S, IsRt hR β := fun β hβ => ((hSdef' β).mp hβ).1
  obtain ⟨S', hS'sub, hcard, hCl⟩ := h S hS
  refine ⟨S'.image (rRefl hR), ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hg
    exact ((hSdef' β).mp (hS'sub hβ)).2
  · calc (S'.image (rRefl hR)).card ≤ S'.card := Finset.card_image_le
      _ ≤ 2 := hcard
  · have hT_eq : T = rRefl hR '' S := by
      ext g
      constructor
      · intro hg
        obtain ⟨β, hβ, hβg⟩ := (mem_Refl_iff hR).mp (hT hg)
        exact ⟨β, ⟨hβ, by rw [hβg]; exact hg⟩, hβg⟩
      · rintro ⟨β, hβ, rfl⟩
        exact ((hSdef' β).mp hβ).2
    have himg : rRefl hR '' (Φ ∪ S) = (rRefl hR '' Φ) ∪ T := by
      rw [Set.image_union, hT_eq]
    have himg' : rRefl hR '' (Φ ∪ (S' : Set (ι → ℤ))) =
        (rRefl hR '' Φ) ∪ (S'.image (rRefl hR) : Set (Wg hR)) := by
      rw [Set.image_union, Finset.coe_image]
    have hΦS : ∀ β ∈ Φ ∪ S, IsRt hR β := by
      intro β hβ
      rcases hβ with hβ | hβ
      · exact hΦ β hβ
      · exact hS β hβ
    have hΦS' : ∀ β ∈ Φ ∪ (S' : Set (ι → ℤ)), IsRt hR β := by
      intro β hβ
      rcases hβ with hβ | hβ
      · exact hΦ β hβ
      · exact hS β (hS'sub hβ)
    have hW1 : Wsub hR (Φ ∪ S) = Wsub hR Φ ⊔ Subgroup.closure T := by
      rw [Wsub, himg, Subgroup.closure_union]
      rfl
    have hW2 : Wsub hR (Φ ∪ (S' : Set (ι → ℤ))) =
        Wsub hR Φ ⊔ Subgroup.closure (S'.image (rRefl hR) : Set (Wg hR)) := by
      rw [Wsub, himg', Subgroup.closure_union]
      rfl
    have hWsub : Wsub hR (Φ ∪ S) = Wsub hR (Φ ∪ (S' : Set (ι → ℤ))) := by
      rw [← Wsub_Cl hR hΦS, hCl, Wsub_Cl hR hΦS']
    rw [← hW1, ← hW2, hWsub]

@[expose] def lam {p : ℕ} (c : ι → ZMod p) (v : ι → ℤ) : ZMod p := ∑ j, (v j : ZMod p) * c j

structure PhiStruct (Φ : Set (ι → ℤ)) : Prop where
  isRt : ∀ β ∈ Φ, IsRt hR β
  neg : ∀ β ∈ Φ, -β ∈ Φ
  closed : ∀ α ∈ Φ, ∀ β ∈ Φ, weylAction hR (rRefl hR α) β ∈ Φ
  irred : ∀ α ∈ Φ, ∀ β ∈ Φ,
    Relation.ReflTransGen (fun a b => b ∈ Φ ∧ form hR (toRat a) (toRat b) ≠ 0) α β
  oneLen : ∀ α ∈ Φ, ∀ β ∈ Φ, form hR (toRat α) (toRat α) = form hR (toRat β) (toRat β)

structure LevTwoData (p : ℕ) (c : ι → ZMod p) (Φ : Set (ι → ℤ)) : Prop extends PhiStruct hR Φ where
  fix : ∀ β ∈ Φ, lam c β = 0
  sat : ∀ β, IsRt hR β → lam c β = 0 → (∃ α ∈ Φ, ∃ w : Wg hR, weylAction hR w α = β) → β ∈ Φ
  rank : ∃ s : Finset (ι → ℤ), (s : Set (ι → ℤ)) ⊆ Φ ∧
    LinearIndependent ℚ (fun v : s => toRat (v : ι → ℤ)) ∧
    3 ≤ s.card ∧ Fintype.card ι ≤ s.card + 2 ∧
    (Fintype.card ι ≤ s.card + 1 ∨ (p : ℤ) ∣ R.det)

end Generic

open LevTwoType in
@[expose] def LevTwoEngine (T : LevTwoType) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (c : Fin T.n → ZMod p) (Φ : Set (Fin T.n → ℤ)),
    LevTwoData T.rootFT p c Φ → TCRoot T.rootFT Φ

end CFSG.StandardType.LevTwo
