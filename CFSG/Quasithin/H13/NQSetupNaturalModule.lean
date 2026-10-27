module

public import CFSG.Quasithin.H13.NQSetupPlaneAction
public import CFSG.Quasithin.H13.NQSetupCcomponent
public import CFSG.LieType.SteinbergBRTransvectionStabilizers
public import CFSG.LinearAlgebra.SteinbergBQNaturalThreeStabilizers
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.Quasithin.SteinbergCCLocalSylowAction

public section

namespace CFSG.Quasithin.H13.NQSetup

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open scoped IsMulCommutative

section Alternatives

variable {G : Type} [Group G]

@[expose] def QTNQNaturalFour (L M : Subgroup G) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 4 ∧
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module k V), Module.finrank k V = 2 ∧
      ∃ (β : (L ⧸ CFSG.solvableRadical L) ≃* SpecialLinearGroup k V)
        (φ : Additive (qtnqU L M) →+ V), Function.Surjective φ ∧
        (∀ (l : L) (x y : qtnqU L M), (y : G) = (l : G) * x * (l : G)⁻¹ →
          φ (Additive.ofMul y) = β (l : L ⧸ CFSG.solvableRadical L) (φ (Additive.ofMul x))) ∧
        ∀ (l : L) (x : qtnqU L M), φ (Additive.ofMul x) = 0 → (l : G) * x * (l : G)⁻¹ = x

@[expose] def QTNQNaturalThreeDouble (L M : Subgroup G) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V), Module.finrank (ZMod 2) V = 3 ∧
    ∃ (β : (L ⧸ CFSG.solvableRadical L) ≃* (V ≃ₗ[ZMod 2] V))
      (ψ : Additive (qtnqU L M) ≃+ V × V),
      ∀ (l : L) (x y : qtnqU L M), (y : G) = (l : G) * x * (l : G)⁻¹ →
        ψ (Additive.ofMul y) = (β (l : L ⧸ CFSG.solvableRadical L) (ψ (Additive.ofMul x)).1,
          β (l : L ⧸ CFSG.solvableRadical L) (ψ (Additive.ofMul x)).2)

@[expose] def QTNQNaturalThreeExtension (L M : Subgroup G) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V), Module.finrank (ZMod 2) V = 3 ∧
    ∃ (β : (L ⧸ CFSG.solvableRadical L) ≃* (V ≃ₗ[ZMod 2] V))
      (φ : Additive (qtnqU L M) →+ V), Function.Surjective φ ∧
      (∀ (l : L) (x y : qtnqU L M), (y : G) = (l : G) * x * (l : G)⁻¹ →
        φ (Additive.ofMul y) = β (l : L ⧸ CFSG.solvableRadical L) (φ (Additive.ofMul x))) ∧
      ∀ (l : L) (x : qtnqU L M), φ (Additive.ofMul x) = 0 → (l : G) * x * (l : G)⁻¹ = x

end Alternatives

section Stabilizers

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

omit [Finite G] in
theorem units_zmod_two_eq_one : ∀ v : (ZMod 2)ˣ, v = 1 := by
  decide

theorem exists_qtnqU_action (h : QTNQ T L M) :
    ∃ c : (L ⧸ CFSG.solvableRadical L) →* MulAut (qtnqU L M),
      ∀ (l : L) (x : qtnqU L M),
        ((c (l : L ⧸ CFSG.solvableRadical L) x : qtnqU L M) : G) = (l : G) * x * (l : G)⁻¹ := by
  obtain ⟨-, -, -, -, ⟨-, hUM, hUn, -⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have hLNU : L ≤ normalizer (qtnqU L M : Set G) :=
    h.l_le.trans ((normal_subgroupOf_iff_le_normalizer hUM).mp hUn)
  set c₀ : L →* MulAut (qtnqU L M) := (qtnqU L M).normalizerMonoidHom.comp (inclusion hLNU)
    with hc₀
  have hc₀R : CFSG.solvableRadical L ≤ c₀.ker := fun r hr => by
    rw [MonoidHom.mem_ker]
    ext x
    change (r : G) * x * (r : G)⁻¹ = x
    rw [radical_commute_qtnqVc h hr (qtnqU_le_qtnqVc h x.2), mul_inv_cancel_right]
  exact ⟨QuotientGroup.lift _ c₀ hc₀R, fun l x => rfl⟩

omit [Finite G] in
theorem mem_map_centralizer_of_fix {c : (L ⧸ CFSG.solvableRadical L) →* MulAut (qtnqU L M)}
    (hc : ∀ (l : L) (x : qtnqU L M),
      ((c (l : L ⧸ CFSG.solvableRadical L) x : qtnqU L M) : G) = (l : G) * x * (l : G)⁻¹)
    {u : G} (hu : u ∈ qtnqU L M) {q : L ⧸ CFSG.solvableRadical L} (hq : c q ⟨u, hu⟩ = ⟨u, hu⟩) :
    q ∈ ((centralizer ({u} : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.solvableRadical L)) := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have h1 : (l : G) * u * (l : G)⁻¹ = u := by
    have := congrArg Subtype.val hq
    rwa [hc] at this
  refine ⟨l, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_subgroupOf, mem_centralizer_singleton_iff]
  calc (l : G) * u = (l : G) * u * (l : G)⁻¹ * l := by group
    _ = u * l := by rw [h1]

theorem exists_four_of_qtnqNaturalFour (h : QTNQ T L M) {u : G} (hu : u ∈ qtnqU L M)
    (ha : QTNQNaturalFour L M) :
    ∃ B : Subgroup (L ⧸ CFSG.solvableRadical L),
      B ≤ ((centralizer ({u} : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.solvableRadical L)) ∧
      CFSG.IsElementaryAbelian 2 B ∧ Nat.card B = 4 := by
  classical
  obtain ⟨k, _, _, hk, V, _, _, hV, β, φ, hφs, hφ, hker⟩ := ha
  obtain ⟨-, -, -, -, ⟨-, -, -, hUel⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have := hUel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_qtnqU_action h
  have hk' : Nat.card k = 2 ^ 2 := by rw [Nat.card_eq_fintype_card, hk]; norm_num
  have : CharP k 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by norm_num) hk'
  have : Finite (Additive (qtnqU L M)) := inferInstanceAs (Finite (qtnqU L M))
  have : FiniteDimensional (ZMod 2) (Additive (qtnqU L M)) := Module.Finite.of_finite
  set ρ : SpecialLinearGroup k V →* (Additive (qtnqU L M) ≃ₗ[ZMod 2] Additive (qtnqU L M)) :=
    (mulAutLinear 2 (qtnqU L M)).comp (c.comp β.symm.toMonoidHom) with hρ
  have hρapp : ∀ (l : L) (x : qtnqU L M),
      ρ (β (l : L ⧸ CFSG.solvableRadical L)) (Additive.ofMul x) =
        Additive.ofMul (c (l : L ⧸ CFSG.solvableRadical L) x) := by
    intro l x
    simp [hρ, mulAutLinear_apply]
  have hβs : ∀ s : SpecialLinearGroup k V, ∃ l : L, s = β (l : L ⧸ CFSG.solvableRadical L) := by
    intro s
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (β.symm s)
    exact ⟨l, by rw [hl, MulEquiv.apply_symm_apply]⟩
  have hequiv : ∀ (s : SpecialLinearGroup k V) (x : Additive (qtnqU L M)),
      φ (ρ s x) = s (φ x) := by
    intro s x
    obtain ⟨l, rfl⟩ := hβs s
    rw [show x = Additive.ofMul x.toMul from rfl, hρapp]
    exact hφ l x.toMul _ (hc l x.toMul)
  have hker' : ∀ (s : SpecialLinearGroup k V) (x : Additive (qtnqU L M)), φ x = 0 → ρ s x = x := by
    intro s x hx
    obtain ⟨l, rfl⟩ := hβs s
    rw [show x = Additive.ofMul x.toMul from rfl, hρapp]
    exact congrArg Additive.ofMul (Subtype.ext ((hc l x.toMul).trans (hker l x.toMul hx)))
  obtain ⟨⟨A, hAfix, hAel, hAcard⟩, -⟩ :=
    LieType.nq_natural_central_extension_transvection_stabilizers (k := k) le_rfl hV ρ φ hφs
      hequiv hker' (Additive.ofMul ⟨u, hu⟩)
  refine ⟨A.map β.symm.toMonoidHom, ?_, IsElementaryAbelian.map _, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine mem_map_centralizer_of_fix hc hu ?_
    obtain ⟨l, rfl⟩ := hβs a
    have hfix := hAfix _ ha
    rw [hρapp] at hfix
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact Additive.ofMul.injective hfix
  · rw [card_map_of_injective β.symm.injective, hAcard, Nat.card_eq_fintype_card, hk]
    norm_num

theorem exists_four_of_qtnqNaturalThreeExtension (h : QTNQ T L M) {u : G}
    (hu : u ∈ qtnqU L M) (hc2 : QTNQNaturalThreeExtension L M) :
    ∃ B : Subgroup (L ⧸ CFSG.solvableRadical L),
      B ≤ ((centralizer ({u} : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.solvableRadical L)) ∧
      CFSG.IsElementaryAbelian 2 B ∧ Nat.card B = 4 := by
  classical
  obtain ⟨V, _, _, hV, β, φ, hφs, hφ, hker⟩ := hc2
  obtain ⟨-, -, -, -, ⟨-, -, -, hUel⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have := hUel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_qtnqU_action h
  have : Finite (Additive (qtnqU L M)) := inferInstanceAs (Finite (qtnqU L M))
  have : FiniteDimensional (ZMod 2) (Additive (qtnqU L M)) := Module.Finite.of_finite
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_eq_succ hV
  have hdet : ∀ g : V ≃ₗ[ZMod 2] V, LinearEquiv.det g = 1 := fun g => units_zmod_two_eq_one _
  set ι : (V ≃ₗ[ZMod 2] V) →* SpecialLinearGroup (ZMod 2) V :=
    { toFun := fun g => ⟨g, hdet g⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } with hι
  set ρ : SpecialLinearGroup (ZMod 2) V →*
      (Additive (qtnqU L M) ≃ₗ[ZMod 2] Additive (qtnqU L M)) :=
    (mulAutLinear 2 (qtnqU L M)).comp
      (c.comp (β.symm.toMonoidHom.comp SpecialLinearGroup.toLinearEquiv)) with hρ
  have hρapp : ∀ (l : L) (x : qtnqU L M),
      ρ (ι (β (l : L ⧸ CFSG.solvableRadical L))) (Additive.ofMul x) =
        Additive.ofMul (c (l : L ⧸ CFSG.solvableRadical L) x) := by
    intro l x
    simp [hρ, hι, mulAutLinear_apply, SpecialLinearGroup.toLinearEquiv]
  have hβs : ∀ s : SpecialLinearGroup (ZMod 2) V,
      ∃ l : L, s = ι (β (l : L ⧸ CFSG.solvableRadical L)) := by
    intro s
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (β.symm (SpecialLinearGroup.toLinearEquiv s))
    refine ⟨l, Subtype.ext ?_⟩
    change (s : V ≃ₗ[ZMod 2] V) = β (l : L ⧸ CFSG.solvableRadical L)
    calc (s : V ≃ₗ[ZMod 2] V) = SpecialLinearGroup.toLinearEquiv s := rfl
      _ = β (β.symm (SpecialLinearGroup.toLinearEquiv s)) := (MulEquiv.apply_symm_apply β _).symm
      _ = β (l : L ⧸ CFSG.solvableRadical L) := by rw [hl]
  have hequiv : ∀ (s : SpecialLinearGroup (ZMod 2) V) (x : Additive (qtnqU L M)),
      φ (ρ s x) = s (φ x) := by
    intro s x
    obtain ⟨l, rfl⟩ := hβs s
    rw [show x = Additive.ofMul x.toMul from rfl, hρapp]
    exact hφ l x.toMul _ (hc l x.toMul)
  have hker' : ∀ (s : SpecialLinearGroup (ZMod 2) V) (x : Additive (qtnqU L M)),
      φ x = 0 → ρ s x = x := by
    intro s x hx
    obtain ⟨l, rfl⟩ := hβs s
    rw [show x = Additive.ofMul x.toMul from rfl, hρapp]
    exact congrArg Additive.ofMul (Subtype.ext ((hc l x.toMul).trans (hker l x.toMul hx)))
  obtain ⟨⟨A, hAfix, hAel, hAcard⟩, -⟩ :=
    LieType.nq_natural_central_extension_transvection_stabilizers (k := ZMod 2) (n := 3)
      (by norm_num) hV ρ φ hφs hequiv hker' (Additive.ofMul ⟨u, hu⟩)
  set f : SpecialLinearGroup (ZMod 2) V →* (L ⧸ CFSG.solvableRadical L) :=
    β.symm.toMonoidHom.comp SpecialLinearGroup.toLinearEquiv with hf
  have hfinj : Function.Injective f :=
    β.symm.injective.comp SpecialLinearGroup.toLinearEquiv_injective
  refine ⟨A.map f, ?_, IsElementaryAbelian.map _, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine mem_map_centralizer_of_fix hc hu ?_
    obtain ⟨l, rfl⟩ := hβs a
    have hfix := hAfix _ ha
    rw [hρapp] at hfix
    have hfl : f (ι (β (l : L ⧸ CFSG.solvableRadical L))) = (l : L ⧸ CFSG.solvableRadical L) :=
      β.symm_apply_apply _
    rw [hfl]
    exact Additive.ofMul.injective hfix
  · rw [card_map_of_injective hfinj, hAcard, Nat.card_eq_fintype_card, ZMod.card]
    norm_num

theorem exists_four_of_qtnqNaturalThreeDouble (h : QTNQ T L M) {u : G} (hu : u ∈ qtnqU L M)
    (hc1 : QTNQNaturalThreeDouble L M) :
    ∃ B : Subgroup (L ⧸ CFSG.solvableRadical L),
      B ≤ ((centralizer ({u} : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.solvableRadical L)) ∧
      CFSG.IsElementaryAbelian 2 B ∧ Nat.card B = 4 := by
  classical
  obtain ⟨V, _, _, hV, β, ψ, hψ⟩ := hc1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_qtnqU_action h
  set e : Additive (qtnqU L M) := Additive.ofMul ⟨u, hu⟩ with he
  obtain ⟨B', hB'fix, hB'el, hB'card⟩ :=
    CFSG.LinearAlgebra.nq_two_natural_three_space_stabilizers hV
    (d := 2) (Or.inr rfl) ![(ψ e).1, (ψ e).2]
  set gle := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V with hgle
  set f : LinearMap.GeneralLinearGroup (ZMod 2) V →* (L ⧸ CFSG.solvableRadical L) :=
    β.symm.toMonoidHom.comp gle.toMonoidHom with hf
  have hfinj : Function.Injective f := β.symm.injective.comp gle.injective
  refine ⟨B'.map f, ?_, IsElementaryAbelian.map _, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    refine mem_map_centralizer_of_fix hc hu ?_
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (f b)
    rw [← hl]
    have hβl : β (l : L ⧸ CFSG.solvableRadical L) = gle b := by
      rw [hl, hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]
    have hfix0 := hB'fix b hb 0
    have hfix1 := hB'fix b hb 1
    have h1 := hψ l ⟨u, hu⟩ (c (l : L ⧸ CFSG.solvableRadical L) ⟨u, hu⟩) (hc l ⟨u, hu⟩)
    rw [hβl] at h1
    have h2 : ψ (Additive.ofMul (c (l : L ⧸ CFSG.solvableRadical L) ⟨u, hu⟩)) = ψ e := by
      rw [h1]
      ext
      · simpa [hgle] using hfix0
      · simpa [hgle] using hfix1
    exact Additive.ofMul.injective (ψ.injective h2)
  · rw [card_map_of_injective hfinj, hB'card]

end Stabilizers

theorem natural_module_centralizer_Sylow_action_on_original_prime_plane_is_noncyclic
    {G : Type} [Group G] [Finite G] {T L M : Subgroup G} (h : QTNQ T L M)
    {p : ℕ} (_hp : p.Prime) (_hp5 : 5 ≤ p) {X : Subgroup G} (hXL : X ≤ L)
    (hXc : (X.subgroupOf L).Characteristic) (_hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (_hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {u : G} (hu : u ∈ qtnqU L M)
    (hQ : IsSylowOf 2 (T ⊓ centralizer {u}) (M ⊓ centralizer {u}))
    (halt : QTNQNaturalFour L M ∨ QTNQNaturalThreeDouble L M ∨ QTNQNaturalThreeExtension L M ∨
      ∃ B : Subgroup (L ⧸ CFSG.solvableRadical L),
        B ≤ ((centralizer ({u} : Set G)).subgroupOf L).map
          (QuotientGroup.mk' (CFSG.solvableRadical L)) ∧
        CFSG.IsElementaryAbelian 2 B ∧ Nat.card B = 4) :
    ¬ IsCyclic (((T ⊓ centralizer {u} ⊓ L).subgroupOf (normalizer (X : Set G))).map
        (normalizerFrattiniConj X)) ∧
      ¬ IsCyclic (((T ⊓ centralizer {u}).subgroupOf (normalizer (X : Set G))).map
        (normalizerFrattiniConj X)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.solvableRadical L with hR
  have hLC := isCComponent_top_of_qtnq h
  set H : Subgroup L := (centralizer ({u} : Set G)).subgroupOf L with hH
  obtain ⟨B, hBH, hBel, hB4⟩ : ∃ B : Subgroup (L ⧸ R),
      B ≤ H.map (QuotientGroup.mk' R) ∧ CFSG.IsElementaryAbelian 2 B ∧ Nat.card B = 4 := by
    rcases halt with ha | hc1 | hc2 | hB
    · exact exists_four_of_qtnqNaturalFour h hu ha
    · exact exists_four_of_qtnqNaturalThreeDouble h hu hc1
    · exact exists_four_of_qtnqNaturalThreeExtension h hu hc2
    · exact hB
  have hB2 : IsPGroup 2 B := by
    have := hBel
    exact CFSG.IsElementaryAbelian.isPGroup 2 _
  have hBnc : ¬ IsCyclic B := by
    have := hBel
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) (by rw [hB4]; norm_num)
  have hLN : L ≤ normalizer (X : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_of_characteristic hXL hXc)
  set α : L →* MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    (normalizerFrattiniConj X).comp (inclusion hLN) with hα
  have hα1 : α ≠ 1 := by
    obtain ⟨l, hlL, hl1⟩ := hLW
    intro h1
    apply hl1
    have h2 := DFunLike.congr_fun h1 ⟨l, hlL⟩
    simp only [MonoidHom.one_apply, hα, MonoidHom.comp_apply] at h2
    rwa [show inclusion hLN ⟨(l : G), hlL⟩ = l from Subtype.ext rfl] at h2
  set QL := T ⊓ centralizer ({u} : Set G) ⊓ L with hQLdef
  have hQLL : QL ≤ L := inf_le_right
  have hS : IsSylowOf 2 (QL.subgroupOf L) H := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L, map_subgroupOf_eq_of_le hQLL, hH,
      subgroupOf_map_subtype, inf_comm]
    exact isSylowOf_inf_of_qtnq h u hQ
  obtain ⟨S, hSeq⟩ := hS.exists_sylow_eq_subgroupOf
  have hnc := nontrivial_Ccomponent_images_retain_radical_quotient_Sylow_noncyclicity hLC α hα1
    Nat.prime_two H S ⟨B, hBH, hB2, hBnc⟩
  have himage : (S : Subgroup H).map (α.comp H.subtype) =
      (QL.subgroupOf (normalizer (X : Set G))).map (normalizerFrattiniConj X) := by
    ext f
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : (((s : H) : L) : G) ∈ QL := by
        have hs2 : s ∈ (S : Subgroup H) := hs
        rw [hSeq] at hs2
        exact mem_subgroupOf.mp (mem_subgroupOf.mp hs2)
      exact ⟨inclusion hLN (s : L), mem_subgroupOf.mpr hs', rfl⟩
    · rintro ⟨n, hn, rfl⟩
      have hn' : (n : G) ∈ QL := mem_subgroupOf.mp hn
      have hnL : (n : G) ∈ L := hQLL hn'
      have hnH : (⟨n, hnL⟩ : L) ∈ H := by
        rw [hH, mem_subgroupOf]
        exact (mem_inf.mp (mem_inf.mp hn').1).2
      have hnS : (⟨⟨n, hnL⟩, hnH⟩ : H) ∈ (S : Subgroup H) := by
        rw [hSeq]
        exact mem_subgroupOf.mpr (mem_subgroupOf.mpr hn')
      exact ⟨⟨⟨n, hnL⟩, hnH⟩, hnS, rfl⟩
  rw [himage] at hnc
  refine ⟨hnc, fun hcyc => hnc ?_⟩
  have hle : (QL.subgroupOf (normalizer (X : Set G))).map (normalizerFrattiniConj X) ≤
      ((T ⊓ centralizer {u}).subgroupOf (normalizer (X : Set G))).map
        (normalizerFrattiniConj X) :=
    map_mono fun n hn => mem_subgroupOf.mpr (mem_inf.mp (mem_subgroupOf.mp hn)).1
  exact Subgroup.isCyclic_of_le hle

end CFSG.Quasithin.H13.NQSetup
