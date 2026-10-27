module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalTwisted

public noncomputable section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SignalizerFunctorTheorem.NonLocalExc CFSG.SignalizerFunctorTheorem.CatalogBridge

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem nonLocalized_of_regular_closing
    {τ : Tag} {K : Type} [Field K] [Finite K] (r : ℕ) [Fact r.Prime]
    [CharP K r] {X J : Subgroup (ModGL τ K)} (hXC : X ≤ adjointGroup τ K) (hJX : J ≤ X)
    (hJs : IsSimpleGroup ↥(J.subgroupOf X)) {y : Fin τ.rank → ModGL τ K}
    (hyJ : ∀ i, y i ∈ J) (hyU : ∀ i, y i ∈ posUnipotent τ K) {c : Fin τ.rank → K}
    (hc : ∀ i, c i ≠ 0) (hco : ∀ i, HasCoord i (y i) (c i)) {w₀ : WeylGroup τ}
    (hw₀ : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀)
    (hJn : canonicalRep (coxeterSystem τ) K w₀ ∈ J)
    (hclose : ∀ s : ℕ, s.Prime → s ≠ r → ∀ V : Subgroup ↥X, V ≠ ⊥ →
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) → (∀ v ∈ V, v ^ s = 1) →
      (∀ j ∈ J.subgroupOf X, ∀ v ∈ V, j * v * j⁻¹ ∈ V) →
      (∀ j ∈ J.subgroupOf X, (∀ v ∈ V, j * v * j⁻¹ = v) → j = 1) → False) :
    NonLocalized (J.subgroupOf X) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite ↥X := Subtype.finite
  have hcent : ∀ x : ↥X, (∀ j ∈ J.subgroupOf X, x * j = j * x) → x = 1 := by
    intro x hx
    refine Subtype.ext (eq_one_of_commute_regular (hXC x.2) hyU hc hco hw₀ (fun i => ?_) ?_)
    · have := hx ⟨y i, hJX (hyJ i)⟩ (Subgroup.mem_subgroupOf.2 (hyJ i))
      exact congrArg Subtype.val this
    · have := hx ⟨canonicalRep (coxeterSystem τ) K w₀, hJX hJn⟩ (Subgroup.mem_subgroupOf.2 hJn)
      exact congrArg Subtype.val this
  have hrsub : ∀ E : Subgroup ↥X, IsPGroup r E →
      (∀ j ∈ J.subgroupOf X, ∀ e ∈ E, j * e * j⁻¹ ∈ E) → E = ⊥ := by
    intro E hEr hEn
    have hWr : IsPGroup r (E.map X.subtype) := hEr.map _
    have hWC : E.map X.subtype ≤ adjointGroup τ K := by
      rintro _ ⟨e, -, rfl⟩
      exact hXC e.2
    have hbot := eq_bot_of_isPGroup_of_normalized_regular r (hJX.trans hXC) hWC hWr hyJ hyU hc hco
      hw₀ hJn (fun j hj w hw => by
        obtain ⟨e, he, rfl⟩ := hw
        have := hEn ⟨j, hJX hj⟩ (Subgroup.mem_subgroupOf.2 hj) e he
        exact ⟨_, this, rfl⟩)
    exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 hbot
  exact nonLocalized_of_closing hJs hcent hrsub hclose

theorem nonLocalized_twisted_of_no_small_action
    (t : TwistTag) (r : ℕ) [Fact r.Prime] {K k : Type}
    [Field K] [Finite K] [CharP K r] [Field k] (ι : k →+* K) (σ : K →+* K) (σ₀ : k →+* k)
    (hσ₀ : Function.Surjective σ₀) (hσι : ∀ c, σ (ι c) = ι (σ₀ c))
    (hs : IsSimpleGroup ↥(((graphFixedRootGroup t k σ₀).map (baseChangeGL ι)).subgroupOf
      (graphFixedRootGroup t K σ)))
    (hno : ∀ (Λ : Type) [Finite Λ], Nat.card Λ ≤ t.tag.rank + t.tag.rootCount →
      ∀ π : ↥(graphFixedRootGroup t k σ₀) →* Equiv.Perm Λ, Function.Injective π → False) :
    NonLocalized (((graphFixedRootGroup t k σ₀).map (baseChangeGL ι)).subgroupOf
      (graphFixedRootGroup t K σ)) := by
  classical
  let C := graphFixedRootGroup t K σ
  let Γ₀ := graphFixedRootGroup t k σ₀
  let J : Subgroup (ModGL t.tag K) := Γ₀.map (baseChangeGL ι)
  have hXC : C ≤ adjointGroup t.tag K :=
    (graphFixedRootGroup_le t K σ).trans (twistedFixedGroup_le_adjointGroup t K σ)
  have hJX : J ≤ C := map_baseChangeGL_graphFixedRootGroup_le hσ₀ hσι
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element t.tag
  have hn : canonicalRep (coxeterSystem t.tag) K w₀ ∈ J := by
    refine ⟨canonicalRep (coxeterSystem t.tag) k w₀, ?_, baseChangeGL_canonicalRep ι w₀⟩
    exact canonicalRep_mem_graphFixedRootGroup (mem_relWeylTwist_of_forall_length_le hw₀)
  choose a ha using exists_orbit_mem t
  have hyJ : ∀ i, (orbitX t K σ (a i) 1 : ModGL t.tag K) ∈ J := by
    intro i
    refine ⟨(orbitX t k σ₀ (a i) 1 : ModGL t.tag k),
      graphFixedPosUnipotent_le_graphFixedRootGroup t k σ₀
        (orbitX_mem_graphFixedPosUnipotent t σ₀ (a i) 1), ?_⟩
    rw [baseChangeGL_orbitX hσι (a i) 1]
    congr 2
    exact Subtype.ext (map_one ι)
  have hyU : ∀ i, (orbitX t K σ (a i) 1 : ModGL t.tag K) ∈ posUnipotent t.tag K := fun i =>
    (Subgroup.mem_inf.1 (orbitX_mem_graphFixedPosUnipotent t σ (a i) 1)).1
  have hmem : ∀ g : ↥Γ₀, baseChangeGL ι (g : ModGL t.tag k) ∈ C := fun g => hJX ⟨g, g.2, rfl⟩
  let φ : ↥Γ₀ →* ↥C :=
    ((baseChangeGL ι).comp Γ₀.subtype).codRestrict C hmem
  have hφinj : Function.Injective φ := fun g h hgh =>
    Subtype.ext (baseChangeGL_injective ι (congrArg Subtype.val hgh))
  have hφJ : ∀ g : ↥Γ₀, φ g ∈ J.subgroupOf C := fun g =>
    Subgroup.mem_subgroupOf.2 ⟨g, g.2, rfl⟩
  let F := AlgebraicClosure K
  have hFr : CharP F r := charP_of_injective_algebraMap (algebraMap K F).injective r
  let ρ : ↥C →* Module.End F (Label t.tag → F) := (adjRep t.tag K F).comp C.subtype
  have hρ : Function.Injective ρ := (adjRep_injective t.tag K F).comp Subtype.val_injective
  refine nonLocalized_of_regular_closing (τ := t.tag) r hXC hJX hs
    (y := fun i => (orbitX t K σ (a i) 1 : ModGL t.tag K)) hyJ hyU (c := fun _ => 1)
    (fun _ => one_ne_zero) (fun i => hasCoord_orbitX_one σ (a i) (ha i)) hw₀ hn ?_
  intro s hs' hsr V hV0 hVcomm hVexp hVnorm hVfaith
  have : Fact s.Prime := ⟨hs'⟩
  have hVc : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVcomm _ a.2 _ b.2)⟩⟩
  have : Finite V := Subtype.finite
  have hinv : (Nat.card V : F) ≠ 0 :=
    cast_card_ne_zero_of_exponent (Fact.out : r.Prime) hs' hsr hVexp
  obtain ⟨hfin, hcard⟩ := finite_card_weights ρ V hVc
  have hnorm : ∀ g : ↥Γ₀, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V := fun g v hv =>
    hVnorm (φ g) (hφJ g) v hv
  have hπ : Function.Injective (weightAction ρ V φ hnorm) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 := centralizes_of_weightAction_eq_one ρ hρ V hVc hinv φ hnorm g hg
    exact hφinj ((hVfaith (φ g) (hφJ g) h1).trans (map_one φ).symm)
  have hcard' : Nat.card (Wt ρ V) ≤ t.tag.rank + t.tag.rootCount := by
    rw [finrank_label_pi, card_label_eq] at hcard
    exact hcard
  exact hno (Wt ρ V) hcard' (weightAction ρ V φ hnorm) hπ

end CFSG.SignalizerFunctorTheorem.NonLocal
