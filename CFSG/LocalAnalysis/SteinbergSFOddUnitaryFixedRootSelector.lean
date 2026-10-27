module

public import CFSG.LocalAnalysis.SteinbergSFOddSymplecticRootCentralizer
public import CFSG.LocalAnalysis.SteinbergSFOddOrthogonalScalarQuotientSL2
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorU

public noncomputable section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

open Subgroup Module CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBUnitaryB
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace OddUnitaryRoot

section Lift

open CatalogueBFixedCentralQuotient

theorem exists_fixed_root_lift {U : Type*} [Group U] [Finite U] (Z : Subgroup U) [Z.Normal]
    (hZ : Z ≤ center U) (φ : MulAut U) (hφZ : Z.map φ.toMonoidHom = Z)
    (hφφ : ∀ g, φ (φ g) = g) {P : Type*} [Group P] (β : MulAut P) (ι : P →* U ⧸ Z)
    (hι : Function.Injective ι) (hιβ : ∀ y, ι (β y) = onQuotient Z φ hφZ (ι y))
    (hN : (ι.range.subgroupOf (fixedSubgroup (onQuotient Z φ hφZ))).Normal)
    {K : Type*} [Field K] (h : FixedRootConfig β K) :
    ∃ Y : Subgroup U, CFSG.Assembly.IsComponentOf Y (fixedSubgroup φ) ∧
      (∃ (A : Subgroup Y) (_ : A.Normal), (∀ a ∈ A, (a : U) ∈ Z) ∧
        Nonempty (Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∧
      ∀ z₁ z₂ : U, QuotientGroup.mk' Z z₁ ∈ ι.range → QuotientGroup.mk' Z z₂ ∈ ι.range →
        (∀ y ∈ Y, y * z₁ = z₁ * y) → (∀ y ∈ Y, y * z₂ = z₂ * y) →
        z₁⁻¹ * φ z₁ ∈ Z → z₂⁻¹ * φ z₂ ∈ Z → z₁ ∉ Z → z₂ ∉ Z → z₁ * z₂⁻¹ ∉ Z → False := by
  classical
  set β' := onQuotient Z φ hφZ with hβ'
  obtain ⟨S, hSn, hSs, hSnab, ⟨eS⟩, hcard⟩ := h
  set X := S.map (fixedSubgroup β).subtype with hXdef
  have hX : CFSG.Assembly.IsComponentOf X (fixedSubgroup β) :=
    isComponentOf_map_subtype S hSn hSs hSnab
  have hmap : (fixedSubgroup β).map ι = ι.range ⊓ fixedSubgroup β' := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, rfl⟩, ?_⟩
      change β' (ι y) = ι y
      rw [← hιβ]
      exact congrArg ι hy
    · rintro ⟨⟨y, rfl⟩, hz⟩
      refine ⟨y, ?_, rfl⟩
      change β y = y
      apply hι
      rw [hιβ]
      exact hz
  have hX₁ := SymmetricLocal.isComponentOf_map_of_injective ι hι hX
  rw [hmap] at hX₁
  have hX₂ : CFSG.Assembly.IsComponentOf (X.map ι) (fixedSubgroup β') :=
    OddClassSelector.isComponentOf_of_normal_le hX₁ inf_le_right (by
      rw [Subgroup.inf_subgroupOf_right]
      exact hN)
  obtain ⟨Y, hY, ⟨σY, hσYs, -, hσY⟩, -⟩ := OddClassSelector.central_lift Z hZ φ hφZ hφφ hX₂
  refine ⟨Y, hY, ⟨σY.ker, inferInstance, fun a ha => ?_, ⟨?_⟩⟩, ?_⟩
  · have h1 : QuotientGroup.mk' Z (a : U) = 1 := by
      rw [← hσY a, MonoidHom.mem_ker.mp ha]
      rfl
    exact (QuotientGroup.eq_one_iff _).mp h1
  · exact (QuotientGroup.quotientKerEquivOfSurjective σY hσYs).trans
      ((X.equivMapOfInjective ι hι).symm.trans
        ((S.equivMapOfInjective _ (Subgroup.subtype_injective _)).symm.trans eS))
  · intro z₁ z₂ hr₁ hr₂ hz₁ hz₂ hφ₁ hφ₂ hn₁ hn₂ hn₁₂
    have : Finite P := Finite.of_injective ι hι
    have hmem : ∀ z : U, QuotientGroup.mk' Z z ∈ ι.range → (∀ y ∈ Y, y * z = z * y) →
        z⁻¹ * φ z ∈ Z → ∃ x ∈ fixedSubgroup β ⊓ centralizer (X : Set P),
          ι x = QuotientGroup.mk' Z z := by
      rintro z ⟨x, hx⟩ hzY hzφ
      refine ⟨x, mem_inf.mpr ⟨?_, ?_⟩, hx⟩
      · change β x = x
        apply hι
        rw [hιβ, hx, hβ', onQuotient_mk]
        have h1 : QuotientGroup.mk' Z (z⁻¹ * φ z) = 1 := (QuotientGroup.eq_one_iff _).mpr hzφ
        rw [map_mul, map_inv, inv_mul_eq_one] at h1
        exact h1.symm
      · rw [mem_centralizer_iff]
        intro s hs
        apply hι
        obtain ⟨y, hy⟩ := hσYs ⟨ι s, mem_map_of_mem ι hs⟩
        have hs' : ι s = QuotientGroup.mk' Z (y : U) :=
          (congrArg Subtype.val hy).symm.trans (hσY y)
        rw [map_mul, map_mul, hs', hx, ← map_mul, ← map_mul, hzY y y.2]
    obtain ⟨x₁, hx₁, hι₁⟩ := hmem z₁ hr₁ hz₁ hφ₁
    obtain ⟨x₂, hx₂, hι₂⟩ := hmem z₂ hr₂ hz₂ hφ₂
    have h3 := three_le_card hx₁ hx₂
      (fun h => hn₁ ((QuotientGroup.eq_one_iff _).mp (by
        change QuotientGroup.mk' Z z₁ = 1
        rw [← hι₁, h, map_one])))
      (fun h => hn₂ ((QuotientGroup.eq_one_iff _).mp (by
        change QuotientGroup.mk' Z z₂ = 1
        rw [← hι₂, h, map_one])))
      (fun h => hn₁₂ ((QuotientGroup.eq_one_iff _).mp (by
        change QuotientGroup.mk' Z (z₁ * z₂⁻¹) = 1
        rw [map_mul, map_inv, ← hι₁, ← hι₂, h, mul_inv_cancel])))
    omega

end Lift

section Inner

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]

theorem half_false (h : UnitaryFieldData p f E) (hp : p ≠ 2) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    {W F : Submodule E V} (hWs : (B.domRestrict₁₂ W W).IsSymm)
    (hWl : (B.domRestrict₁₂ W W).SeparatingLeft) (hW1 : 1 ≤ finrank E W) (hF0 : F ≠ ⊥)
    {Y : Subgroup (sesqUnitaryGroup B)} (hYF : ∀ y ∈ Y, ∀ w ∈ F, unitaryOp y w = w)
    (ρ : Y →* sesqUnitaryGroup (B.domRestrict₁₂ W W)) (hρi : Function.Injective ρ)
    (hρc : CFSG.IsComponent ρ.range) (A : Subgroup Y) [A.Normal]
    (hAZ : ∀ a ∈ A, (a : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have hnd := CatalogueBUnitaryB.nondegenerate_of_isSymm hWs hWl
  obtain ⟨hdim2, -, hρeq⟩ := eq_unitarySpecial_of_isComponent h hp hW1 hWs hWl hρc
  have hA : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr fun a ha =>
    Subtype.ext (eq_one_of_mem_sesqNormOneScalars (hAZ a ha) hF0 (hYF a a.2))
  obtain ⟨eU⟩ := OddClassSelector.nonempty_unitarySpecial_equiv h (B.domRestrict₁₂ W W)
  let ι : Y ≃* CatalogueBUnitaryIsometry.specialIsometry
      (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq)
      (B.domRestrict₁₂ W W) :=
    (MonoidHom.ofInjective hρi).trans ((MulEquiv.subgroupCongr hρeq).trans eU)
  obtain ⟨-, hn', ⟨eQ'⟩⟩ := nonempty_quotient_map ι A eQ
  have hbot : A.map ι.toMonoidHom = ⊥ := by rw [hA, Subgroup.map_bot]
  obtain ⟨-, -, -, hcard, -⟩ := SteinbergBT.unitary_scalar_quotient_SL2 hp h.one_le
    h.card_eq_sq (B.domRestrict₁₂ W W) hWs hnd hdim2 hn K hK (A.map ι.toMonoidHom)
    (fun g hg => ⟨1, fun v => by
      rw [hbot, Subgroup.mem_bot] at hg
      rw [hg, one_smul]
      rfl⟩) eQ'
  rw [hbot, Subgroup.card_bot] at hcard
  omega

theorem inner_case_false (h : UnitaryFieldData p f E) (hp : p ≠ 2) (hn : 3 ≤ finrank E V)
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {T : sesqUnitaryGroup B} (hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h B) = 2)
    {Y : Subgroup (sesqUnitaryGroup B)}
    (hY : CFSG.Assembly.IsComponentOf Y (centralizer ({T} : Set (sesqUnitaryGroup B))))
    (A : Subgroup Y) [A.Normal]
    (hAZ : ∀ a ∈ A, (a : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B)
    {K : Type*} [Field K] {n : ℕ} (hn2 : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  obtain ⟨l, -, -, hN, hP, hM, -, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp (by omega) hB hBl hT
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY : Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))) ≃* Y :=
    Subgroup.subgroupOfEquivOfLe hY.1
  rcases hN with hN | hN
  ·
    obtain ⟨-, hsepP, hsepM, e, he⟩ := hsplit hN
    have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
      ⟨fun x y => hB.eq (x : V) (y : V)⟩
    rcases CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
        (isComponent_map_of_isComponent e hY₁) with h2 | h1
    · have h2' : ∀ x ∈ Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))),
          (e x).2 = 1 := fun x hx => h2 _ (mem_map_of_mem _ hx)
      obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := OddClassSelector.restrict_component e hY₁ h2'
      have hYF : ∀ y ∈ Y, ∀ w ∈ eigenMinus l (unitaryOp T), unitaryOp y w = w := by
        intro y hy w hw
        have h4 := LinearMap.congr_fun (he (eY.symm ⟨y, hy⟩)).2 ⟨w, hw⟩
        rw [h2' _ (eY.symm ⟨y, hy⟩).2] at h4
        exact h4.symm
      refine half_false h hp (hsymm _) hsepP (Submodule.one_le_finrank_iff.mpr hP) hM hYF
        (ρ₁.comp eY.symm.toMonoidHom) (hρ₁i.comp eY.symm.injective) ?_ A hAZ hn2 hK eQ
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
    · have h1' : ∀ x ∈ Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))),
          ((e.trans MulEquiv.prodComm) x).2 = 1 := fun x hx => h1 _ (mem_map_of_mem _ hx)
      obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ :=
        OddClassSelector.restrict_component (e.trans MulEquiv.prodComm) hY₁ h1'
      have hYF : ∀ y ∈ Y, ∀ w ∈ eigenPlus l (unitaryOp T), unitaryOp y w = w := by
        intro y hy w hw
        have h4 := LinearMap.congr_fun (he (eY.symm ⟨y, hy⟩)).1 ⟨w, hw⟩
        rw [show (e (eY.symm ⟨y, hy⟩)).1 = 1 from h1' _ (eY.symm ⟨y, hy⟩).2] at h4
        exact h4.symm
      refine half_false h hp (hsymm _) hsepM (Submodule.one_le_finrank_iff.mpr hM) hP hYF
        (ρ₁.comp eY.symm.toMonoidHom) (hρ₁i.comp eY.symm.injective) ?_ A hAZ hn2 hK eQ
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
  ·
    obtain ⟨-, -, -, hdim2, -, -, e, -, -, hscal⟩ := hpaired hN
    obtain ⟨bP⟩ : Nonempty (Basis (Fin (finrank E (eigenPlus l (unitaryOp T)))) E
        (eigenPlus l (unitaryOp T))) := ⟨Module.finBasis E _⟩
    let Fm : centralizer ({T} : Set (sesqUnitaryGroup B)) ≃*
        GL (Fin (finrank E (eigenPlus l (unitaryOp T)))) E :=
      e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv)
    have hq3 : 3 ≤ p ^ f := by
      have := h.prime.two_le
      have : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
      omega
    have hodd : Odd (Nat.card E) := by
      rw [h.card_eq_sq]
      exact ((h.prime.odd_of_ne_two hp).pow).pow
    obtain ⟨-, hn₁, ⟨eQ₁⟩⟩ := nonempty_quotient_map eY.symm A eQ
    have hA₁ : ∀ a ∈ A.map eY.symm.toMonoidHom, ∃ c : E,
        ((Fm a : GL (Fin (finrank E (eigenPlus l (unitaryOp T)))) E) :
          Matrix (Fin (finrank E (eigenPlus l (unitaryOp T))))
            (Fin (finrank E (eigenPlus l (unitaryOp T)))) E) = c • 1 := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨c, -, hc⟩ := (hscal (eY.symm a)).mp (hAZ a ha)
      refine ⟨c, ?_⟩
      change LinearMap.toMatrixAlgEquiv bP ((e (eY.symm a) : LinearMap.GeneralLinearGroup E
        (eigenPlus l (unitaryOp T))) : Module.End E (eigenPlus l (unitaryOp T))) = c • 1
      rw [hc, map_smul, map_one]
    obtain ⟨-, h5, -⟩ := gl_component_quotient hodd (by omega) Fm hY₁ _ hA₁ hn2 hK eQ₁
    rw [h.card_eq_sq] at h5
    nlinarith

end Inner

section Anti

theorem exists_pair_of_three_le {G : Type*} [Group G] (N : Subgroup G)
    (h3 : 3 ≤ Nat.card (G ⧸ N)) : ∃ a b : G, a ∉ N ∧ b ∉ N ∧ a * b⁻¹ ∉ N := by
  by_contra hcon
  push Not at hcon
  have hfin : Finite (G ⧸ N) := Nat.finite_of_card_ne_zero (by omega)
  have hle : Nat.card (G ⧸ N) ≤ 2 := by
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : G, ∀ b : G, b ∉ N → a₀⁻¹ * b ∈ N := by
      by_cases hex : ∃ a₀ : G, a₀ ∉ N
      · obtain ⟨a₀, ha₀⟩ := hex
        refine ⟨a₀, fun b hb => ?_⟩
        have h1 := hcon a₀⁻¹ b⁻¹ (fun h => ha₀ (by rw [← inv_inv a₀]; exact N.inv_mem h))
          (fun h => hb (by rw [← inv_inv b]; exact N.inv_mem h))
        rwa [inv_inv] at h1
      · push Not at hex
        exact ⟨1, fun b hb => absurd (hex b) hb⟩
    have hsurj : Function.Surjective
        (fun i : Fin 2 => ![(QuotientGroup.mk 1 : G ⧸ N), QuotientGroup.mk a₀] i) := by
      intro x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
      by_cases hb : b ∈ N
      · refine ⟨0, ?_⟩
        show (QuotientGroup.mk 1 : G ⧸ N) = QuotientGroup.mk b
        exact QuotientGroup.eq.mpr (by rw [inv_one, one_mul]; exact hb)
      · refine ⟨1, ?_⟩
        show (QuotientGroup.mk a₀ : G ⧸ N) = QuotientGroup.mk b
        exact QuotientGroup.eq.mpr (ha₀ b hb)
    have := Nat.card_le_card_of_surjective _ hsurj
    rwa [Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at this
  omega

theorem exists_pair_of_equiv {U : Type*} [Group U] {F : Subgroup U} {O : Type*} [Group O]
    (Ψ : F ≃* O) {T : Subgroup O} (N : Subgroup T) (Z : Subgroup U)
    (hnotZ : ∀ x : T, x ∉ N → ((Ψ.symm x : F) : U) ∉ Z) (h3 : 3 ≤ Nat.card (T ⧸ N))
    (P : U → Prop) (hP : ∀ x : T, P (Ψ.symm x)) :
    ∃ z₁ z₂ : U, P z₁ ∧ P z₂ ∧ z₁ ∉ Z ∧ z₂ ∉ Z ∧ z₁ * z₂⁻¹ ∉ Z := by
  obtain ⟨a₁, a₂, ha₁, ha₂, ha₁₂⟩ := exists_pair_of_three_le N h3
  refine ⟨_, _, hP a₁, hP a₂, hnotZ a₁ ha₁, hnotZ a₂ ha₂, ?_⟩
  have h1 := hnotZ _ ha₁₂
  rwa [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, Subgroup.coe_mul,
    Subgroup.coe_inv] at h1

theorem map_eq_one_of_perfect {U : Type*} [Group U] {C : Subgroup U} {H : Type*} [Group H]
    (Ψ : C ≃* H) {M : Type*} [CommGroup M] (δ : U →* M) {T : Subgroup H}
    (hT : Group.IsPerfect T) (x : T) : δ (Ψ.symm x : C) = 1 := by
  have h1 : x ∈ commutator T := by rw [hT.commutator_eq_top]; exact mem_top x
  exact Abelianization.commutator_subset_ker
    (δ.comp (C.subtype.comp (Ψ.symm.toMonoidHom.comp T.subtype))) h1

theorem orth_branch {U : Type*} [Group U] {Z C : Subgroup U} {M : Type*} [CommGroup M]
    (δ : U →* M) {k : Type} [Field k] [Finite k] (hk : Odd (Nat.card k)) {W : Type*}
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] (q : QuadraticForm k W)
    (hQ : q.polarBilin.Nondegenerate) (Ψ : C ≃* TauCeti.QuadraticMap.orthogonalGroup q)
    (hZ : ∀ g : C, (g : U) ∈ Z → Ψ g ∈ OddOrthogonalQuotient.scalarIsometries q)
    {Y : Subgroup U} (hY : CFSG.Assembly.IsComponentOf Y C) (A : Subgroup Y) [A.Normal]
    (hAZ : ∀ a ∈ A, (a : U) ∈ Z) {K : Type*} [Field K] {n : ℕ} (hn2 : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hsmall : ∀ z₁ z₂ : U, δ z₁ = 1 → δ z₂ = 1 → (∀ y ∈ Y, y * z₁ = z₁ * y) →
      (∀ y ∈ Y, y * z₂ = z₂ * y) → z₁ ∈ C → z₂ ∈ C → z₁ ∉ Z → z₂ ∉ Z → z₁ * z₂⁻¹ ∉ Z → False) :
    n = 2 ∧ Nat.card k = 5 ∧ finrank k W = 3 := by
  classical
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY : Y.subgroupOf C ≃* Y := Subgroup.subgroupOfEquivOfLe hY.1
  obtain ⟨-, hn₁, ⟨eQ₁⟩⟩ := nonempty_quotient_map eY.symm A eQ
  have hBc := isComponent_map_of_isComponent Ψ hY₁
  let ιB := (Y.subgroupOf C).equivMapOfInjective Ψ.toMonoidHom Ψ.injective
  obtain ⟨-, hn₂, ⟨eQ₂⟩⟩ := nonempty_quotient_map ιB (A.map eY.symm.toMonoidHom) eQ₁
  have hA₂ : ∀ a ∈ (A.map eY.symm.toMonoidHom).map ιB.toMonoidHom, ∃ c : k, ∀ w,
      ((a : TauCeti.QuadraticMap.orthogonalGroup q) : W ≃ₗ[k] W) w = c • w := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := hZ (eY.symm a) (hAZ a ha)
    exact ⟨c, hc⟩
  obtain ⟨hn2', h5, hcase⟩ := odd_orthogonal_component_scalar_quotients_even_SL2_small_exceptions
    hk q hQ hBc _ hA₂ hn2 K hK ⟨eQ₂⟩
  rcases hcase with ⟨h3, -⟩ | ⟨-, -, -, -, -, T, hTcomm, hTperf, -, hT60, -⟩
  · exact ⟨hn2', h5, h3⟩
  exfalso
  have hnotZ : ∀ x : T, x ∉ (OddOrthogonalQuotient.scalarIsometries q).subgroupOf T →
      ((Ψ.symm x : C) : U) ∉ Z := by
    intro x hx hxZ
    apply hx
    rw [Subgroup.mem_subgroupOf]
    have h1 := hZ _ hxZ
    rwa [MulEquiv.apply_symm_apply] at h1
  have hcomm : ∀ x : T, ∀ y ∈ Y, y * ((Ψ.symm x : C) : U) = ((Ψ.symm x : C) : U) * y := by
    intro x y hy
    have h1 := hTcomm (Ψ ⟨y, hY.1 hy⟩) (mem_map_of_mem Ψ.toMonoidHom
      (Subgroup.mem_subgroupOf.mpr hy)) (x : TauCeti.QuadraticMap.orthogonalGroup q) x.2
    rw [← MulEquiv.apply_symm_apply Ψ (x : TauCeti.QuadraticMap.orthogonalGroup q), ← map_mul,
      ← map_mul] at h1
    exact congrArg Subtype.val (Ψ.injective h1)
  obtain ⟨z₁, z₂, ⟨hd₁, hc₁, hf₁⟩, ⟨hd₂, hc₂, hf₂⟩, hn₁, hn₂, hn₁₂⟩ := exists_pair_of_equiv Ψ
    ((OddOrthogonalQuotient.scalarIsometries q).subgroupOf T) Z hnotZ (by omega)
    (fun z => δ z = 1 ∧ (∀ y ∈ Y, y * z = z * y) ∧ z ∈ C)
    fun x => ⟨map_eq_one_of_perfect Ψ δ hTperf x, hcomm x, (Ψ.symm x).2⟩
  exact hsmall z₁ z₂ hd₁ hd₂ hc₁ hc₂ hf₁ hf₂ hn₁ hn₂ hn₁₂

theorem sp_branch {U : Type*} [Group U] {Z C : Subgroup U} {k : Type} [Field k] [Finite k]
    (hk : Odd (Nat.card k)) {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {B' : LinearMap.BilinForm k W} (halt : B'.IsAlt) (hnd : B'.Nondegenerate)
    (hdim : 3 ≤ finrank k W) (Ψ : C ≃* CatalogueBAlternatingIsometry.isometryGroup B')
    (hZ : ∀ g : C, (g : U) ∈ Z → ∃ c : k, ∀ w,
      ((Ψ g : CatalogueBAlternatingIsometry.isometryGroup B') : W ≃ₗ[k] W) w = c • w)
    {Y : Subgroup U} (hY : CFSG.Assembly.IsComponentOf Y C) (A : Subgroup Y) [A.Normal]
    (hAZ : ∀ a ∈ A, (a : U) ∈ Z) {K : Type*} [Field K] {n : ℕ} (hn2 : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY : Y.subgroupOf C ≃* Y := Subgroup.subgroupOfEquivOfLe hY.1
  obtain ⟨-, hn₁, ⟨eQ₁⟩⟩ := nonempty_quotient_map eY.symm A eQ
  obtain ⟨hdim2, -, -⟩ := sp_component_quotient hk halt hnd (by omega) Ψ hY₁
    (A.map eY.symm.toMonoidHom) (by rintro _ ⟨a, ha, rfl⟩; exact hZ (eY.symm a) (hAZ a ha))
    hn2 hK eQ₁
  omega

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

theorem exists_smul_of_restrict {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    {W : Submodule h.fixedField V} {C : Subgroup (sesqUnitaryGroup B)}
    {G : Subgroup (W ≃ₗ[h.fixedField] W)} (Ψ : C ≃* G)
    (hΨ : ∀ g w, ((((Ψ g : G) : W ≃ₗ[h.fixedField] W) w : W) : V) =
      unitaryOp (g : sesqUnitaryGroup B) w) (g : C)
    (hg : unitaryOp (g : sesqUnitaryGroup B) = 1 ∨ unitaryOp (g : sesqUnitaryGroup B) = -1) :
    ∃ c : h.fixedFieldˣ, ∀ w, ((Ψ g : G) : W ≃ₗ[h.fixedField] W) w = (c : h.fixedField) • w := by
  rcases hg with hg | hg
  · refine ⟨1, fun w => Subtype.ext ?_⟩
    rw [hΨ, hg, Units.val_one, one_smul]
    rfl
  · refine ⟨-1, fun w => Subtype.ext ?_⟩
    rw [hΨ, hg, Units.val_neg, Units.val_one, neg_one_smul, Submodule.coe_neg]
    rfl

theorem anti_case [FiniteDimensional E V] (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    (hn : 3 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (τ₀ : V →ₛₗ[h.bar] V) (hτ₀ : Function.Bijective τ₀)
    (hτ₀B : ∀ v w, B (τ₀ v) (τ₀ w) = h.bar (B v w)) (μ : Eˣ)
    (hμ : ∀ v, τ₀ (τ₀ v) = (μ : E) • v) {Y : Subgroup (sesqUnitaryGroup B)}
    (hY : CFSG.Assembly.IsComponentOf Y (fixedSubgroup (antiConj h τ₀ hτ₀ hτ₀B)))
    (A : Subgroup Y) [A.Normal]
    (hAZ : ∀ a ∈ A, (a : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B)
    {K : Type*} [Field K] {n : ℕ} (hn2 : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hsmall : ∀ z₁ z₂ : sesqUnitaryGroup B, z₁ ∈ CatalogueBUnitaryB.unitarySpecial B →
      z₂ ∈ CatalogueBUnitaryB.unitarySpecial B → (∀ y ∈ Y, y * z₁ = z₁ * y) →
      (∀ y ∈ Y, y * z₂ = z₂ * y) → z₁ ∈ fixedSubgroup (antiConj h τ₀ hτ₀ hτ₀B) →
      z₂ ∈ fixedSubgroup (antiConj h τ₀ hτ₀ hτ₀B) → z₁ ∉ sesqNormOneScalars h B →
      z₂ ∉ sesqNormOneScalars h B → z₁ * z₂⁻¹ ∉ sesqNormOneScalars h B → False) :
    n = 2 ∧ finrank E V = 3 ∧ p ^ f = 5 ∧ μ = 1 := by
  classical
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have : Finite E := h.finite
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by omega) hB hBl τ₀ hτ₀ hτ₀B μ hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField (conjFixed h ((b : E) • τ₀)) := finite_conjFixed
  have hkodd : Odd (Nat.card h.fixedField) := by
    rw [h.card_fixedField]
    exact hodd.pow
  have hpm : ∀ g : fixedSubgroup (antiConj h τ₀ hτ₀ hτ₀B),
      (g : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B →
        unitaryOp (g : sesqUnitaryGroup B) = 1 ∨ unitaryOp (g : sesqUnitaryGroup B) = -1 :=
    fun g hg => (fixed_mem_scalars_iff h _ _ hτ₀B (by omega) g).mp hg
  have hδ : ∀ z : sesqUnitaryGroup B, (Units.map (LinearMap.det : Module.End E V →* E)).comp
      (sesqUnitaryGroup B).subtype z = 1 → z ∈ CatalogueBUnitaryB.unitarySpecial B := fun z hz =>
    CatalogueBUnitaryB.mem_unitarySpecial.mpr (congrArg Units.val hz)
  rcases hμ1 with hμ1 | hμ1
  ·
    obtain ⟨B', -, hsym, hnd, Φ, hΦ⟩ := hB1 hμ1
    have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
      have h1 := congrArg h.fixedField.subtype h0
      rw [map_ofNat, map_zero] at h1
      exact UnitaryHigher.two_ne_zero_of_odd h hp h1
    have hQ : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
      rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
      exact hnd
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : fixedSubgroup (antiConj h τ₀ hτ₀ hτ₀B) ≃*
        TauCeti.QuadraticMap.orthogonalGroup (CatalogueBOrthogonalDescent.originalQuadratic B'),
        ∀ g w, ((((Ψ g : TauCeti.QuadraticMap.orthogonalGroup
          (CatalogueBOrthogonalDescent.originalQuadratic B')) :
            conjFixed h ((b : E) • τ₀) ≃ₗ[h.fixedField] conjFixed h ((b : E) • τ₀)) w :
              conjFixed h ((b : E) • τ₀)) : V) = unitaryOp (g : sesqUnitaryGroup B) w :=
      ⟨(fixedCommutingEquiv h τ₀ hτ₀ hτ₀B).trans
        (Φ.trans (MulEquiv.subgroupCongr (isometryGroup_eq_orthogonalGroup B' hsym h2))),
        fun g w => hΦ _ w⟩
    obtain ⟨hn2', h5, h3⟩ := orth_branch _ hkodd _ hQ Ψ
      (fun g hg => exists_smul_of_restrict Ψ hΨ g (hpm g hg)) hY A hAZ hn2 hK eQ
      fun z₁ z₂ hd₁ hd₂ => hsmall z₁ z₂ (hδ z₁ hd₁) (hδ z₂ hd₂)
    exact ⟨hn2', by rw [← hfinW]; exact h3, by rw [← h.card_fixedField]; exact h5, hμ1⟩
  ·
    obtain ⟨B', -, halt, hnd, -, Φ, hΦ⟩ := hB2 hμ1
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : fixedSubgroup (antiConj h τ₀ hτ₀ hτ₀B) ≃*
        CatalogueBAlternatingIsometry.isometryGroup B',
        ∀ g w, ((((Ψ g : CatalogueBAlternatingIsometry.isometryGroup B') :
          conjFixed h ((b : E) • τ₀) ≃ₗ[h.fixedField] conjFixed h ((b : E) • τ₀)) w :
            conjFixed h ((b : E) • τ₀)) : V) = unitaryOp (g : sesqUnitaryGroup B) w :=
      ⟨(fixedCommutingEquiv h τ₀ hτ₀ hτ₀B).trans Φ, fun g w => hΦ _ w⟩
    refine (sp_branch hkodd halt hnd (by rw [hfinW]; exact hn) Ψ (fun g hg => ?_) hY A hAZ hn2
      hK eQ).elim
    obtain ⟨c, hc⟩ := exists_smul_of_restrict Ψ hΨ g (hpm g hg)
    exact ⟨c, hc⟩

theorem symmetric_descent (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    (hn : 1 ≤ finrank E V) {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} (hH : Hf.IsSymm)
    (hnd : Hf.SeparatingLeft) (τ₀ : V →ₛₗ[h.bar] V) (hτ₀ : Function.Bijective τ₀)
    (hτ₀H : ∀ v w, Hf (τ₀ v) (τ₀ w) = h.bar (Hf v w)) (hsq : ∀ v, τ₀ (τ₀ v) = v) :
    finrank h.fixedField (conjFixed h τ₀) = finrank E V ∧
      Function.Bijective (LinearMap.liftBaseChange E (conjFixed h τ₀).subtype) ∧
      ∃ Bf : LinearMap.BilinForm h.fixedField (conjFixed h τ₀),
        (∀ v w, (Bf v w : E) = Hf v w) ∧ Bf.IsSymm ∧ Bf.Nondegenerate ∧
        ∃ Φ : commutingUnitary Hf τ₀ ≃* TauCeti.BilinForm.isometryGroup Bf,
          ∀ g w, (((Φ g : conjFixed h τ₀ ≃ₗ[h.fixedField] conjFixed h τ₀) w : conjFixed h τ₀) :
            V) = ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) w := by
  obtain ⟨-, -, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    (h.prime.odd_of_ne_two hp) hn hH hnd τ₀ hτ₀ hτ₀H 1 fun v => by
      rw [hsq, Units.val_one, one_smul]
  obtain ⟨-, hfin, hbij, hB1, -⟩ := hall 1 t (by simp [UnitaryFieldData.norm]) ht
  have h1 : ((1 : Eˣ) : E) • τ₀ = τ₀ := by rw [Units.val_one, one_smul]
  rw [h1] at hfin hbij hB1
  exact ⟨hfin, hbij, hB1 rfl⟩

end Anti

section Model

open Matrix

variable {p f : ℕ} {E : Type} [Field E] {r ε : ℕ}

theorem hyperbolic_core (h : UnitaryFieldData p f E) (hp : p ≠ 2) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 3 ≤ 2 * r + ε) {K : Type*} [Field K] {n : ℕ} (hn2 : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (β : MulAut (hypPSU h r ε)) (hβ : orderOf β = 2) (hcfg : FixedRootConfig β K)
    (A : GL (HypIndex r ε) E) (σ : E ≃+* E)
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex r ε) E) ∈ semilinearSimilitudes h r ε)
    (hA : A ∈ hypUnitary h r ε) (hβA : semilinearAutHom h hr hε ⟨_, hx⟩ = β) :
    n = 2 ∧ 2 * r + ε = 3 ∧ p ^ f = 5 ∧ (∀ c, σ c = h.bar c) ∧
      (A : Matrix (HypIndex r ε) (HypIndex r ε) E) *
        (A : Matrix (HypIndex r ε) (HypIndex r ε) E).map h.bar = 1 := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have hdim : finrank E (HypIndex r ε → E) = 2 * r + ε := UnitaryHigher.finrank_hypIndex_fun
  have hsq : semilinearAutHom h hr hε (⟨⟨A, σ⟩, hx⟩ * ⟨⟨A, σ⟩, hx⟩) = 1 := by
    rw [map_mul, hβA, ← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hβ])
  obtain ⟨hσσ, c, hc⟩ := (semilinearAutHom_eq_one_iff h hr hε hn _).mp hsq
  change σ * σ = RingEquiv.refl E at hσσ
  change A * glAut σ A = GeneralLinearGroup.scalar (HypIndex r ε) c at hc
  let ι : hypPSU h r ε →* sesqProjUnitary h (hypForm h r ε) :=
    (projSpecial h (hypForm h r ε)).subtype.comp (hypModelEquiv h).toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp (hypModelEquiv h).injective
  have hιr : ι.range = projSpecial h (hypForm h r ε) := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (hypModelEquiv h).surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have happly : ∀ g : hypSU h r ε,
      β (hypProj h r ε g) = hypProj h r ε ⟨_, conj_mem_hypSU hx g⟩ := by
    intro g
    rw [← hβA]
    exact semilinearAutHom_apply h hr hε _ g
  have hZc := sesqNormOneScalars_le_center h (hypForm h r ε)
  rcases ringEquiv_eq_refl_or_bar h hσσ with rfl | hσ
  ·
    exfalso
    have hAA : A * A = GeneralLinearGroup.scalar (HypIndex r ε) c := by
      have h1 : glAut (RingEquiv.refl E) A = A :=
        congrArg (fun φ : MulAut (GL (HypIndex r ε) E) => φ A) (map_one glAut)
      rwa [h1] at hc
    have hcN : h.norm (c : E) = 1 := by
      have hU := mul_mem hA hA
      rw [hAA, mem_hypUnitary, GeneralLinearGroup.coe_scalar, scalar_gram] at hU
      have h2 := congrFun (congrFun hU (.inl ⟨0, hr⟩)) (hypPartner (.inl ⟨0, hr⟩))
      simpa [hypGram_apply] using h2
    have hAord : orderOf (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h r ε) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_two]
        exact ⟨c, hcN, pow_zero c, by rw [Subgroup.coe_mul, hAA]⟩
      · intro h1
        rw [QuotientGroup.eq_one_iff] at h1
        obtain ⟨c', -, -, hc'⟩ := h1
        have hΦ1 := (semilinearAutHom_eq_one_iff h hr hε hn ⟨⟨A, RingEquiv.refl E⟩, hx⟩).mpr
          ⟨rfl, c', hc'⟩
        rw [hβA] at hΦ1
        rw [hΦ1, orderOf_one] at hβ
        exact absurd hβ (by norm_num)
    set T : sesqUnitaryGroup (hypForm h r ε) := hypUnitaryEquiv h ⟨A, hA⟩ with hTdef
    have hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h (hypForm h r ε)) = 2 := by
      rw [hTdef, ← hypUnitaryModEquiv_mk, MulEquiv.orderOf_eq]
      exact hAord
    have he : ∀ y, ι (β y) =
        MulAut.conj (QuotientGroup.mk' (sesqNormOneScalars h (hypForm h r ε)) T) (ι y) := by
      intro y
      obtain ⟨g, rfl⟩ := hypProj_surjective h r ε y
      rw [happly]
      refine hypModelEquiv_conj h ⟨A, hA⟩ g _ ?_
      have hg : glAut (RingEquiv.refl E) (g : GL (HypIndex r ε) E) =
          (g : GL (HypIndex r ε) E) :=
        congrArg (fun φ : MulAut (GL (HypIndex r ε) E) => φ (g : GL (HypIndex r ε) E))
          (map_one glAut)
      change A * glAut (RingEquiv.refl E) (g : GL (HypIndex r ε) E) * A⁻¹ = _
      rw [hg]
    have hφZ := OddClassSelector.map_conj_eq_of_le_center hZc T
    rw [← OddClassSelector.onQuotient_conj T hφZ] at he
    have hTT : T * T ∈ center (sesqUnitaryGroup (hypForm h r ε)) := by
      apply hZc
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hT,
        pow_orderOf_eq_one]
    have hφφ : ∀ g, MulAut.conj T (MulAut.conj T g) = g := by
      intro g
      rw [MulAut.conj_apply, MulAut.conj_apply]
      have h1 := mem_center_iff.mp hTT g
      calc T * (T * g * T⁻¹) * T⁻¹ = (T * T) * g * (T * T)⁻¹ := by group
        _ = g := by rw [← h1, mul_inv_cancel_right]
    obtain ⟨Y, hY, ⟨Ak, _, hAZ, ⟨eQ⟩⟩, -⟩ := exists_fixed_root_lift _ hZc _ hφZ hφφ β ι hι he
      (by rw [hιr]; exact (projSpecial_normal h _).subgroupOf _) hcfg
    rw [CatalogueBUnitaryB.fixedSubgroup_conj] at hY
    exact inner_case_false h hp (by rw [hdim]; omega) (hypForm_isSymm h)
      (hypForm_separatingLeft h) hT hY Ak hAZ hn2 hK eQ
  ·
    have hmap : (A : Matrix (HypIndex r ε) (HypIndex r ε) E).map σ =
        (A : Matrix (HypIndex r ε) (HypIndex r ε) E).map h.bar :=
      Matrix.ext fun i j => hσ _
    have hAc : (A : Matrix (HypIndex r ε) (HypIndex r ε) E) *
        (A : Matrix (HypIndex r ε) (HypIndex r ε) E).map h.bar = (c : E) • 1 := by
      have h1 := congrArg (fun g : GL (HypIndex r ε) E =>
        (g : Matrix (HypIndex r ε) (HypIndex r ε) E)) hc
      simp only [Units.val_mul, coe_glAut, GeneralLinearGroup.coe_scalar, hmap] at h1
      rw [h1, scalar_apply, smul_one_eq_diagonal]
    have hτB := hypForm_semilinearMatrixMap h hA
    have he : ∀ y, ι (β y) = antiProjConj h
        (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) E))
        (semilinearMatrixMap_bijective h c.ne_zero hAc) hτB (ι y) := by
      intro y
      obtain ⟨g, rfl⟩ := hypProj_surjective h r ε y
      rw [happly]
      exact hypModelEquiv_antiConj h A c.ne_zero hAc hτB σ hσ g _
    obtain ⟨Y, hY, ⟨Ak, _, hAZ, ⟨eQ⟩⟩, hsmall⟩ := exists_fixed_root_lift _ hZc _
      (map_scalars_unitaryConj h _ _ hτB)
      (unitaryConj_unitaryConj h _ _ hτB c (semilinearMatrixMap_sq h hAc)) β ι hι he
      (by rw [hιr]; exact (projSpecial_normal h _).subgroupOf _) hcfg
    have hrange : ∀ z : sesqUnitaryGroup (hypForm h r ε),
        z ∈ CatalogueBUnitaryB.unitarySpecial (hypForm h r ε) →
          QuotientGroup.mk' (sesqNormOneScalars h (hypForm h r ε)) z ∈ ι.range := by
      intro z hz
      rw [hιr]
      exact ⟨z, hz, rfl⟩
    have hfix : ∀ z : sesqUnitaryGroup (hypForm h r ε),
        z ∈ fixedSubgroup (antiConj h
          (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) E))
          (semilinearMatrixMap_bijective h c.ne_zero hAc) hτB) →
          z⁻¹ * antiConj h (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) E))
            (semilinearMatrixMap_bijective h c.ne_zero hAc) hτB z ∈
              sesqNormOneScalars h (hypForm h r ε) := by
      intro z hz
      rw [show antiConj h _ _ hτB z = z from hz, inv_mul_cancel]
      exact one_mem _
    obtain ⟨hn2', hd3, hq5, hc1⟩ := anti_case h hp (by rw [hdim]; omega) (hypForm_isSymm h)
      (hypForm_separatingLeft h) _ _ hτB c (semilinearMatrixMap_sq h hAc) hY Ak hAZ hn2 hK eQ
      fun z₁ z₂ hd₁ hd₂ hc₁ hc₂ hf₁ hf₂ => hsmall z₁ z₂ (hrange z₁ hd₁) (hrange z₂ hd₂) hc₁ hc₂
        (hfix z₁ hf₁) (hfix z₂ hf₂)
    refine ⟨hn2', by rw [← hdim]; exact hd3, hq5, hσ, ?_⟩
    rw [hAc, hc1, Units.val_one, one_smul]

end Model

end OddUnitaryRoot

open OddUnitaryRoot in
theorem odd_unitary_involution_fixed_root_small_field_selector
    (K : Type*) [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {D : Type} [Group D] (α : MulAut D) (hα : orderOf α = 2)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id D))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K))
    (hcard : Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓
      centralizer ((S.map (α.toMonoidHom.eqLocus (MonoidHom.id D)).subtype : Subgroup D) :
        Set D) : Subgroup D) ≤ 2)
    (d p f : ℕ) (hp : p ≠ 2) (hM : StatedClassicalModel D .PSU d p f) :
    n = 2 ∧ d = 3 ∧ p = 5 ∧ f = 1 ∧ α ∉ (MulAut.conj : D →* MulAut D).range ∧
      (∃ (E : Type) (_ : Field E) (h : UnitaryFieldData p f E) (θ : D ≃* hypPSU h 1 1)
        (A : GL (HypIndex 1 1) E) (σ : E ≃+* E)
        (hx : (⟨A, σ⟩ : SemiGL (HypIndex 1 1) E) ∈ semilinearSimilitudes h 1 1),
        A ∈ hypUnitary h 1 1 ∧ semilinearAutHom h le_rfl le_rfl ⟨_, hx⟩ = MulAut.congr θ α) ∧
      ∀ (E : Type) [Field E] (h : UnitaryFieldData p f E) (θ : D ≃* hypPSU h 1 1)
        (A : GL (HypIndex 1 1) E) (σ : E ≃+* E)
        (hx : (⟨A, σ⟩ : SemiGL (HypIndex 1 1) E) ∈ semilinearSimilitudes h 1 1),
        A ∈ hypUnitary h 1 1 → semilinearAutHom h le_rfl le_rfl ⟨_, hx⟩ = MulAut.congr θ α →
        let τ₀ := semilinearMatrixMap h (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E)
        (∀ c, σ c = h.bar c) ∧ (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E) *
          (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E).map h.bar = 1 ∧
        (∀ v w, hypForm h 1 1 (τ₀ v) (τ₀ w) = h.bar (hypForm h 1 1 v w)) ∧
        (∀ v, τ₀ (τ₀ v) = v) ∧ Nat.card h.fixedField = 5 ∧
        finrank h.fixedField (conjFixed h τ₀) = 3 ∧
        Function.Bijective (LinearMap.liftBaseChange E (conjFixed h τ₀).subtype) ∧
        ∃ Bf : LinearMap.BilinForm h.fixedField (conjFixed h τ₀),
          (∀ v w, (Bf v w : E) = hypForm h 1 1 v w) ∧ Bf.IsSymm ∧ Bf.Nondegenerate ∧
          ∃ Φ : commutingUnitary (hypForm h 1 1) τ₀ ≃* TauCeti.BilinForm.isometryGroup Bf,
            ∀ g w, (((Φ g : conjFixed h τ₀ ≃ₗ[h.fixedField] conjFixed h τ₀) w : conjFixed h τ₀) :
              HypIndex 1 1 → E) = ((g : LinearMap.GeneralLinearGroup E (HypIndex 1 1 → E)) :
                (HypIndex 1 1 → E) →ₗ[E] HypIndex 1 1 → E) w := by
  classical
  obtain ⟨⟨hprime, hf, hd3, -⟩, E₀, _, _, hE₀, ⟨e⟩⟩ := hM
  have hud : UnitaryFieldData p f E₀ := ⟨hprime, hf, by rw [hE₀, ← pow_mul, mul_comm]⟩
  have h0 : FixedRootConfig α K := ⟨S, hSn, hSs, hSnab, hSK, hcard⟩
  have hcore : ∀ (E : Type) [Field E] (h : UnitaryFieldData p f E) {r ε : ℕ} (hr : 1 ≤ r)
      (hε : ε ≤ 1), 2 * r + ε = d → ∀ (θ : D ≃* hypPSU h r ε) (A : GL (HypIndex r ε) E)
      (σ : E ≃+* E) (hx : (⟨A, σ⟩ : SemiGL (HypIndex r ε) E) ∈ semilinearSimilitudes h r ε),
      A ∈ hypUnitary h r ε → semilinearAutHom h hr hε ⟨_, hx⟩ = MulAut.congr θ α →
      n = 2 ∧ 2 * r + ε = 3 ∧ p ^ f = 5 ∧ (∀ c, σ c = h.bar c) ∧
        (A : Matrix (HypIndex r ε) (HypIndex r ε) E) *
          (A : Matrix (HypIndex r ε) (HypIndex r ε) E).map h.bar = 1 := by
    intro E _ h r ε hr hε hrd θ A σ hx hA hβA
    exact hyperbolic_core h hp hr hε (by omega) hn hK (MulAut.congr θ α)
      (by rw [MulEquiv.orderOf_eq]; exact hα)
      (h0.of_mulEquiv θ fun x => by
        change θ (α x) = θ (α (θ.symm (θ x)))
        rw [MulEquiv.symm_apply_apply]) A σ hx hA hβA
  obtain ⟨r, ε, hr, hε, rfl⟩ : ∃ r ε, 1 ≤ r ∧ ε ≤ 1 ∧ d = 2 * r + ε :=
    ⟨d / 2, d % 2, by omega, by omega, by omega⟩
  obtain ⟨R, hR⟩ := (unitary_hyperbolic_model_transport hud hr hε).1
  let θ : D ≃* hypPSU hud r ε := e.trans (hypPSUEquivStatedProj hud hR (by omega)).symm
  obtain ⟨-, -, -, hrep⟩ := odd_unitary_automorphism_semilinear_representation hud hp hr hε
    (by omega)
  obtain ⟨A₀, σ₀, hx₀, hA₀, hβ₀, -, -, -⟩ := hrep (MulAut.congr θ α)
    (by rw [MulEquiv.orderOf_eq]; exact hα)
  obtain ⟨hn2, hd3', hq5, -, -⟩ := hcore E₀ hud hr hε rfl θ A₀ σ₀ hx₀ hA₀ hβ₀
  obtain rfl : r = 1 := by omega
  obtain rfl : ε = 1 := by omega
  have hp5 : p = 5 := by
    have h5 : p ∣ 5 := hq5 ▸ dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hprime (by norm_num)).mp h5
  subst hp5
  have hf1 : f = 1 := by
    have h1 : 5 ^ f = 5 ^ 1 := by rw [hq5, pow_one]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) h1
  subst hf1
  refine ⟨hn2, rfl, rfl, rfl, ?_, ⟨E₀, inferInstance, hud, θ, A₀, σ₀, hx₀, hA₀, hβ₀⟩, ?_⟩
  ·
    rintro ⟨g, hg⟩
    obtain ⟨s, hs⟩ := hypProj_surjective hud 1 1 (θ g)
    have hxs := inl_mem_semilinearSimilitudes (h := hud) s
    have hsU : (s : GL (HypIndex 1 1) E₀) ∈ hypUnitary hud 1 1 := (mem_gramSU.mp s.2).1
    have hΦ : semilinearAutHom hud le_rfl le_rfl ⟨_, hxs⟩ = MulAut.congr θ α := by
      refine MulEquiv.ext fun y => ?_
      obtain ⟨x, rfl⟩ := hypProj_surjective hud 1 1 y
      rw [semilinearAutHom_apply, ← hg]
      change _ = θ (MulAut.conj g (θ.symm (hypProj hud 1 1 x)))
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hs,
        ← map_mul, ← map_inv, ← map_mul]
      congr 1
    obtain ⟨-, -, -, hbar, -⟩ := hcore E₀ hud le_rfl le_rfl rfl θ _ _ hxs hsU hΦ
    obtain ⟨c, hc⟩ := hud.exists_bar_ne
    exact hc (hbar c).symm
  ·
    intro E _ h θ' A σ hx hA hβA τ₀
    obtain ⟨-, -, -, hσ, hAA⟩ := hcore E h le_rfl le_rfl rfl θ' A σ hx hA hβA
    have := h.finite
    have hAA' : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E) *
        (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E).map h.bar = ((1 : Eˣ) : E) • 1 := by
      rw [hAA, Units.val_one, one_smul]
    have hτB := hypForm_semilinearMatrixMap h hA
    have hτ₀ := semilinearMatrixMap_bijective h one_ne_zero hAA'
    have hsq : ∀ v, τ₀ (τ₀ v) = v := fun v => by
      rw [semilinearMatrixMap_sq h hAA', Units.val_one, one_smul]
    have hdim : finrank E (HypIndex 1 1 → E) = 3 := UnitaryHigher.finrank_hypIndex_fun
    obtain ⟨hfin, hbij, hdesc⟩ := symmetric_descent h hp (by omega) (hypForm_isSymm h)
      (hypForm_separatingLeft h) τ₀ hτ₀ hτB hsq
    exact ⟨hσ, hAA, hτB, hsq, by rw [h.card_fixedField, pow_one], by rw [hfin, hdim], hbij,
      hdesc⟩

open OddUnitaryRoot in
theorem odd_unitary_involution_fixed_root_small_field_selector_of_classicalModel
    (K : Type*) [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {D : Type} [Group D] (α : MulAut D) (hα : orderOf α = 2)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id D))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K))
    (hcard : Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓
      centralizer ((S.map (α.toMonoidHom.eqLocus (MonoidHom.id D)).subtype : Subgroup D) :
        Set D) : Subgroup D) ≤ 2)
    (d p f : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hL : CFSG.Assembly.ComponentType.ClassicalModel D .PSU d p f) :
    n = 2 ∧ d = 3 ∧ p = 5 ∧ f = 1 ∧ α ∉ (MulAut.conj : D →* MulAut D).range ∧
      (∃ (E : Type) (_ : Field E) (h : UnitaryFieldData p f E) (θ : D ≃* hypPSU h 1 1)
        (A : GL (HypIndex 1 1) E) (σ : E ≃+* E)
        (hx : (⟨A, σ⟩ : SemiGL (HypIndex 1 1) E) ∈ semilinearSimilitudes h 1 1),
        A ∈ hypUnitary h 1 1 ∧ semilinearAutHom h le_rfl le_rfl ⟨_, hx⟩ = MulAut.congr θ α) ∧
      ∀ (E : Type) [Field E] (h : UnitaryFieldData p f E) (θ : D ≃* hypPSU h 1 1)
        (A : GL (HypIndex 1 1) E) (σ : E ≃+* E)
        (hx : (⟨A, σ⟩ : SemiGL (HypIndex 1 1) E) ∈ semilinearSimilitudes h 1 1),
        A ∈ hypUnitary h 1 1 → semilinearAutHom h le_rfl le_rfl ⟨_, hx⟩ = MulAut.congr θ α →
        let τ₀ := semilinearMatrixMap h (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E)
        (∀ c, σ c = h.bar c) ∧ (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E) *
          (A : Matrix (HypIndex 1 1) (HypIndex 1 1) E).map h.bar = 1 ∧
        (∀ v w, hypForm h 1 1 (τ₀ v) (τ₀ w) = h.bar (hypForm h 1 1 v w)) ∧
        (∀ v, τ₀ (τ₀ v) = v) ∧ Nat.card h.fixedField = 5 ∧
        finrank h.fixedField (conjFixed h τ₀) = 3 ∧
        Function.Bijective (LinearMap.liftBaseChange E (conjFixed h τ₀).subtype) ∧
        ∃ Bf : LinearMap.BilinForm h.fixedField (conjFixed h τ₀),
          (∀ v w, (Bf v w : E) = hypForm h 1 1 v w) ∧ Bf.IsSymm ∧ Bf.Nondegenerate ∧
          ∃ Φ : commutingUnitary (hypForm h 1 1) τ₀ ≃* TauCeti.BilinForm.isometryGroup Bf,
            ∀ g w, (((Φ g : conjFixed h τ₀ ≃ₗ[h.fixedField] conjFixed h τ₀) w : conjFixed h τ₀) :
              HypIndex 1 1 → E) = ((g : LinearMap.GeneralLinearGroup E (HypIndex 1 1 → E)) :
                (HypIndex 1 1 → E) →ₗ[E] HypIndex 1 1 → E) w :=
  odd_unitary_involution_fixed_root_small_field_selector K hn hK α hα S hSn hSs hSnab hSK hcard
    d p f hp (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSU d p f hL)

end CFSG.LocalAnalysis.SymplecticFourStandard
