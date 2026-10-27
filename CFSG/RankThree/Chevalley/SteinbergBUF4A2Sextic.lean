module

public import CFSG.RankThree.Chevalley.SteinbergBUF4A2SexticDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4A2SexticCentralizer
public import CFSG.RankThree.Chevalley.SteinbergBUF4A2SexticRoot

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix SteinbergBN
open CFSG.RankThree.Classical

theorem exists_f4A2_sextic_twist_element {K : Type} [Field K] [Fintype K] [CharP K 2]
    {K₆ : Type} [Field K₆] [Algebra K K₆] [CharP K₆ 2] {K₃ : Type} [Field K₃] [Algebra K K₃]
    [Algebra K₃ K₆] [FiniteDimensional K K₃] (h3 : Module.finrank K K₃ = 3) (σ : K₆ ≃+* K₆)
    (hσ : ∀ b, σ b = b ^ Fintype.card K) (κ : F4A2Kind) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ a, ∃ ha : a ∈ subsystemGroup Tag.F4 K₃ {κ.i, κ.j},
      ((f4A2Equiv K₆ κ ⟨_, weyl_word_mem_pair (M := K₆) κ ε⟩ :
          Matrix.SpecialLinearGroup (Fin 3) K₆) : Matrix (Fin 3) (Fin 3) K₆) =
        ((f4A2Equiv K₆ κ ⟨baseChangeGL (algebraMap K₃ K₆) a,
            baseChangeGL_mem_subsystemGroup _ ha⟩ : Matrix.SpecialLinearGroup (Fin 3) K₆) :
          Matrix (Fin 3) (Fin 3) K₆) *
          (((f4A2Equiv K₆ κ ⟨baseChangeGL (algebraMap K₃ K₆) a,
            baseChangeGL_mem_subsystemGroup _ ha⟩ : Matrix.SpecialLinearGroup (Fin 3) K₆) :
              Matrix (Fin 3) (Fin 3) K₆).map σ)ᵀ := by
  have : CharP K₃ 2 := charP_of_injective_algebraMap (algebraMap K K₃).injective 2
  let σ₃ : K₃ ≃+* K₃ := (FiniteField.frobeniusAlgEquivOfAlgebraic K K₃).toRingEquiv
  have hσ₃ : ∀ b, σ₃ b = b ^ Fintype.card K := fun b => by
    change FiniteField.frobeniusAlgEquivOfAlgebraic K K₃ b = _
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  obtain ⟨P, hP⟩ := exists_f4A2_orthogonal_coboundary h3 σ₃ hσ₃ κ hε
  obtain ⟨a, ha⟩ := (f4A2Equiv K₃ κ).surjective P
  refine ⟨a, a.2, ?_⟩
  have bcw : ∀ k : Fin Tag.F4.rank,
      baseChangeGL (algebraMap K₃ K₆) (weylElt Tag.F4 K₃ k 1) = weylElt Tag.F4 K₆ k 1 :=
    fun k => by
      rw [Blueprint.Chevalley.weylElt_eq_xUnit_mul, map_mul, map_mul, baseChangeGL_xUnit,
        baseChangeGL_yUnit, Blueprint.Chevalley.weylElt_eq_xUnit_mul]
      simp
  have hm : (weylElt Tag.F4 K₆ κ.i 1 * weylElt Tag.F4 K₆ κ.j 1) ^ ε =
      baseChangeGL (algebraMap K₃ K₆)
        ((weylElt Tag.F4 K₃ κ.i 1 * weylElt Tag.F4 K₃ κ.j 1) ^ ε) := by
    rw [map_zpow, map_mul, bcw, bcw]
  have e1 : (⟨_, weyl_word_mem_pair (M := K₆) κ ε⟩ : subsystemGroup Tag.F4 K₆ {κ.i, κ.j}) =
      ⟨_, baseChangeGL_mem_subsystemGroup (algebraMap K₃ K₆) (weyl_word_mem_pair (M := K₃) κ ε)⟩ :=
    Subtype.ext hm
  rw [e1, f4A2Equiv_baseChange_algebraMap κ ⟨_, weyl_word_mem_pair (M := K₃) κ ε⟩, hP,
    f4A2Equiv_baseChange_algebraMap κ a, ha, Matrix.map_mul, Matrix.transpose_map]
  simp only [Matrix.map_map]
  congr 3
  funext b
  change algebraMap K₃ K₆ (σ₃ b) = σ (algebraMap K₃ K₆ b)
  rw [hσ, hσ₃, map_pow]

theorem exists_map_of_map_map_eq {K : Type} [Field K] [Fintype K] {K₆ : Type} [Field K₆]
    [Algebra K K₆] [Finite K₆] (K₂ : IntermediateField K K₆) (h2 : Module.finrank K K₂ = 2)
    (σ : K₆ ≃+* K₆) (hσ : ∀ b, σ b = b ^ Fintype.card K) (B : Matrix (Fin 3) (Fin 3) K₆)
    (hB : (B.map σ).map σ = B) :
    ∃ B₂ : Matrix (Fin 3) (Fin 3) K₂, B₂.map (algebraMap K₂ K₆) = B := by
  have : Fintype K₂ := Fintype.ofFinite K₂
  have hcard : Fintype.card K₂ = Fintype.card K ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := K) (V := K₂), h2]
  refine exists_map_algebraMap_of_map_eq (σ.trans σ) (fun b => ?_) ?_
  · rw [RingEquiv.trans_apply, hσ, hσ, ← pow_mul, hcard, sq]
  · rw [RingEquiv.coe_trans, ← Matrix.map_map]
    exact hB

theorem f4A2_unitary_center_quasisimple (K : Type) [Field K] [Fintype K] [CharP K 2]
    (K₂ : Type) [Field K₂] [Algebra K K₂] (h2 : Module.finrank K K₂ = 2) (σ₂ : K₂ ≃+* K₂)
    (hσ₂ : ∀ b, σ₂ b = b ^ Fintype.card K) {w₀ : WeylGroup Tag.F4}
    (hw₀ : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v) (κ : F4A2Kind)
    {U : Subgroup (ModGL Tag.F4 K₂)}
    (hU : ∀ v, v ∈ U ↔ ∃ hv : v ∈ subsystemGroup Tag.F4 K₂ {κ.i, κ.j},
      ((f4A2Equiv K₂ κ ⟨v, hv⟩ : Matrix (Fin 3) (Fin 3) K₂).map σ₂)ᵀ *
        (f4A2Equiv K₂ κ ⟨v, hv⟩ : Matrix (Fin 3) (Fin 3) K₂) = 1) :
    (∀ (g : subsystemGroup Tag.F4 K₂ {κ.i, κ.j}) (hg : (g : ModGL Tag.F4 K₂) ∈ U),
      (⟨g, hg⟩ : U) ∈ Subgroup.center U ↔ ∃ t : K₂, t ^ (Fintype.card K + 1) = 1 ∧
        t ^ 3 = 1 ∧ (f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) = scalar (Fin 3) t) ∧
    (4 ≤ Fintype.card K → CFSG.IsQuasisimple U ∧ Group.IsPerfect U) := by
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
  have hσ₂' : ∀ c, σ₂ c = c ^ Nat.card K := fun c => by rw [hσ₂, Nat.card_eq_fintype_card]
  have hUR : U = subsystemGroup Tag.F4 K₂ {κ.i, κ.j} ⊓ (adjointGroup Tag.F4 K₂ ⊓
      (twistedEntrywise (canonicalRep (coxeterSystem Tag.F4) K₂ w₀)
        (σ₂ : K₂ →+* K₂)).eqLocus (MonoidHom.id _)) := by
    ext v
    rw [hU, Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hv, hunit⟩
      exact ⟨hv, EvenF4QPlus.subsystemGroup_le_adjointGroup' _ hv,
        (EvenF4QPlus.twistedEntrywise_eq_self_iff_unitary κ (σ₂ : K₂ →+* K₂) hw₀ ⟨v, hv⟩).2
          hunit⟩
    · rintro ⟨hv, -, hfix⟩
      exact ⟨hv, (EvenF4QPlus.twistedEntrywise_eq_self_iff_unitary κ (σ₂ : K₂ →+* K₂) hw₀
        ⟨v, hv⟩).1 hfix⟩
  obtain ⟨-, hcenter, -, hqs, -⟩ :=
    even_F4_qplus_A2_root_kernel_unitary_fixed_derived_group K K₂ h2 σ₂ hσ₂' w₀ hw₀ _ rfl κ U hUR
  refine ⟨fun g hg => ?_, fun h4 => hqs (by rwa [Nat.card_eq_fintype_card])⟩
  rw [hcenter g hg, Nat.card_eq_fintype_card]

theorem map_swapMat01 {K₂ K₆ : Type} [Field K₂] [Field K₆] (f : K₂ →+* K₆) (c : K₂) :
    (EvenF4QPlus.swapMat01 c).map f = EvenF4QPlus.swapMat01 (f c) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [EvenF4QPlus.swapMat01, map_inv₀]

theorem map_swapMat02 {K₂ K₆ : Type} [Field K₂] [Field K₆] (f : K₂ →+* K₆) :
    (EvenF4QPlus.swapMat02 : Matrix (Fin 3) (Fin 3) K₂).map f = EvenF4QPlus.swapMat02 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [EvenF4QPlus.swapMat02]

theorem scalar_of_commute_baseChange_unitary {K₂ K₆ : Type} [Field K₂] [Field K₆]
    [Algebra K₂ K₆] [CharP K₂ 2] [CharP K₆ 2] (κ : F4A2Kind) (σ₂ : K₂ ≃+* K₂) {ζ : K₂}
    (hζ0 : ζ ≠ 0) (hζ2 : ζ ^ 2 ≠ 1) (hσζ : σ₂ ζ = ζ⁻¹) {U : Subgroup (ModGL Tag.F4 K₂)}
    (hU : ∀ v, v ∈ U ↔ ∃ hv : v ∈ subsystemGroup Tag.F4 K₂ {κ.i, κ.j},
      ((f4A2Equiv K₂ κ ⟨v, hv⟩ : Matrix (Fin 3) (Fin 3) K₂).map σ₂)ᵀ *
        (f4A2Equiv K₂ κ ⟨v, hv⟩ : Matrix (Fin 3) (Fin 3) K₂) = 1)
    (hVQ : U.map (baseChangeGL (algebraMap K₂ K₆)) ≤ subsystemGroup Tag.F4 K₆ {κ.i, κ.j})
    (X : Matrix (Fin 3) (Fin 3) K₆)
    (hX : ∀ s (hs : s ∈ U.map (baseChangeGL (algebraMap K₂ K₆))),
      X * ((f4A2Equiv K₆ κ ⟨s, hVQ hs⟩ : Matrix.SpecialLinearGroup (Fin 3) K₆) :
        Matrix (Fin 3) (Fin 3) K₆) =
      ((f4A2Equiv K₆ κ ⟨s, hVQ hs⟩ : Matrix.SpecialLinearGroup (Fin 3) K₆) :
        Matrix (Fin 3) (Fin 3) K₆) * X) :
    X ∈ Set.range (scalar (Fin 3)) := by
  have hel : ∀ A : Matrix (Fin 3) (Fin 3) K₂, A.det = 1 → (A.map σ₂)ᵀ * A = 1 →
      X * A.map (algebraMap K₂ K₆) = A.map (algebraMap K₂ K₆) * X := by
    intro A hA hAu
    obtain ⟨u, hu⟩ := (f4A2Equiv K₂ κ).surjective ⟨A, hA⟩
    have hru : (f4A2Equiv K₂ κ u : Matrix (Fin 3) (Fin 3) K₂) = A := by rw [hu]
    have huU : (u : ModGL Tag.F4 K₂) ∈ U := (hU _).2 ⟨u.2, by rw [hru]; exact hAu⟩
    have hs : baseChangeGL (algebraMap K₂ K₆) u ∈ U.map (baseChangeGL (algebraMap K₂ K₆)) :=
      ⟨u, huU, rfl⟩
    have h := hX _ hs
    rwa [f4A2Equiv_baseChange_algebraMap κ u, hru] at h
  have h1 := hel _ (EvenF4QPlus.det_swapMat01 one_ne_zero)
    (EvenF4QPlus.unitary_swapMat01 (σ₂ : K₂ →+* K₂) one_ne_zero (by simp))
  have h2 := hel _ (EvenF4QPlus.det_swapMat01 hζ0)
    (EvenF4QPlus.unitary_swapMat01 (σ₂ : K₂ →+* K₂) hζ0 hσζ)
  have h3 := hel _ EvenF4QPlus.det_swapMat02 (EvenF4QPlus.unitary_swapMat02 (σ₂ : K₂ →+* K₂))
  rw [map_swapMat01, map_one] at h1
  rw [map_swapMat01] at h2
  rw [map_swapMat02] at h3
  have hζ0' : algebraMap K₂ K₆ ζ ≠ 0 := (map_ne_zero _).2 hζ0
  have hζ2' : algebraMap K₂ K₆ ζ ^ 2 ≠ 1 := fun h =>
    hζ2 ((algebraMap K₂ K₆).injective (by rw [map_pow, h, map_one]))
  exact ⟨X 0 0, (EvenF4QPlus.eq_scalar_of_commute_swapMat hζ0' hζ2' h1 h2 h3).symm⟩

theorem mulEquiv_apply_mem_center_iff {A B : Type*} [Group A] [Group B] (e : A ≃* B) (x : A) :
    e x ∈ Subgroup.center B ↔ x ∈ Subgroup.center A := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h y
    apply e.injective
    rw [map_mul, map_mul, h]
  · intro h y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, h]

theorem even_F4_native_A2_sextic_unitary_permutation_descent
    (K : Type) [Field K] [Fintype K] [CharP K 2] (K₆ : Type) [Field K₆] [Algebra K K₆]
    [FiniteDimensional K K₆] (K₂ K₃ : IntermediateField K K₆)
    (h2 : Module.finrank K K₂ = 2) (h3 : Module.finrank K K₃ = 3)
    (σ : K₆ ≃+* K₆) (hσ : ∀ b, σ b = b ^ Fintype.card K)
    (σ₂ : K₂ ≃+* K₂) (hσ₂ : ∀ b, σ₂ b = b ^ Fintype.card K) (κ : F4A2Kind)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (w₀ : WeylGroup Tag.F4)
    (hw₀ : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v) (θ : ModGL Tag.F4 K₆ →* ModGL Tag.F4 K₆)
    (hθ : ∀ g, θ g = (weylElt Tag.F4 K₆ κ.i 1 * weylElt Tag.F4 K₆ κ.j 1) ^ ε *
        canonicalRep (coxeterSystem Tag.F4) K₆ w₀ * Units.map (entrywiseHom σ.toRingHom) g *
      ((weylElt Tag.F4 K₆ κ.i 1 * weylElt Tag.F4 K₆ κ.j 1) ^ ε *
        canonicalRep (coxeterSystem Tag.F4) K₆ w₀)⁻¹)
    (U : Subgroup (ModGL Tag.F4 K₂))
    (hU : ∀ v, v ∈ U ↔ ∃ hv : v ∈ subsystemGroup Tag.F4 K₂ {κ.i, κ.j},
      ((f4A2Equiv K₂ κ ⟨v, hv⟩ : Matrix (Fin 3) (Fin 3) K₂).map σ₂)ᵀ *
        (f4A2Equiv K₂ κ ⟨v, hv⟩ : Matrix (Fin 3) (Fin 3) K₂) = 1)
    (Z L : Subgroup (ModGL Tag.F4 K₆))
    (hZ : ∀ h, h ∈ Z ↔ h ∈ torusGroup Tag.F4 K₆ ∧ torusRootChar h (Pi.single κ.i 1) = 1 ∧
      torusRootChar h (Pi.single κ.j 1) = 1)
    (hL : L = torusGroup Tag.F4 K₆ ⊔ subsystemGroup Tag.F4 K₆ {κ.i, κ.j}) :
    (∀ A : Matrix.SpecialLinearGroup (Fin 3) K₂,
      ((A : Matrix (Fin 3) (Fin 3) K₂).map σ₂)ᵀ * A = 1 ↔
        ∃ g : subsystemGroup Tag.F4 K₂ {κ.i, κ.j}, (g : ModGL Tag.F4 K₂) ∈ U ∧
          f4A2Equiv K₂ κ g = A) ∧
    ∃ a ∈ subsystemGroup Tag.F4 K₃ {κ.i, κ.j},
      subsystemGroup Tag.F4 K₆ {κ.i, κ.j} ⊓ θ.eqLocus (MonoidHom.id _) =
        U.map ((MulAut.conj (baseChangeGL (algebraMap K₃ K₆) a)).toMonoidHom.comp
          (baseChangeGL (algebraMap K₂ K₆))) ∧
      (∃ e : U ≃* ↥(subsystemGroup Tag.F4 K₆ {κ.i, κ.j} ⊓ θ.eqLocus (MonoidHom.id _)),
        (∀ u : U, (e u : ModGL Tag.F4 K₆) = baseChangeGL (algebraMap K₃ K₆) a *
          baseChangeGL (algebraMap K₂ K₆) u * (baseChangeGL (algebraMap K₃ K₆) a)⁻¹) ∧
        ∀ (g : subsystemGroup Tag.F4 K₂ {κ.i, κ.j}) (hg : (g : ModGL Tag.F4 K₂) ∈ U),
          e ⟨g, hg⟩ ∈ Subgroup.center
              ↥(subsystemGroup Tag.F4 K₆ {κ.i, κ.j} ⊓ θ.eqLocus (MonoidHom.id _)) ↔
            ∃ t : K₂, t ^ (Fintype.card K + 1) = 1 ∧ t ^ 3 = 1 ∧
              (f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) = scalar (Fin 3) t) ∧
      (4 ≤ Fintype.card K →
        CFSG.IsQuasisimple
          ↥(subsystemGroup Tag.F4 K₆ {κ.i, κ.j} ⊓ θ.eqLocus (MonoidHom.id _)) ∧
        Group.IsPerfect
          ↥(subsystemGroup Tag.F4 K₆ {κ.i, κ.j} ⊓ θ.eqLocus (MonoidHom.id _))) ∧
      L ⊓ Subgroup.centralizer ((subsystemGroup Tag.F4 K₆ {κ.i, κ.j} ⊓
          θ.eqLocus (MonoidHom.id _) : Subgroup (ModGL Tag.F4 K₆)) : Set (ModGL Tag.F4 K₆)) =
        Z ∧
      (Subgroup.center L).map L.subtype = Z ∧ Odd (Nat.card Z) ∧
      ∃ P : GL (Fin 2) K₂, ∀ A : SL2 K,
        baseChangeGL (algebraMap K₃ K₆) a * rootSL2 Tag.F4 K₆ (Pi.single κ.i 1)
            (Matrix.SpecialLinearGroup.map (algebraMap K₂ K₆)
              (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K K₂) A))) *
          (baseChangeGL (algebraMap K₃ K₆) a)⁻¹ ∈
        subsystemGroup Tag.F4 K₆ {κ.i, κ.j} ⊓ θ.eqLocus (MonoidHom.id _) := by
  classical
  have : CharP K₆ 2 := charP_of_injective_algebraMap (algebraMap K K₆).injective 2
  have : Finite K₆ := Module.finite_of_finite K
  have : FiniteDimensional K K₃ := Module.finite_of_finrank_pos (by rw [h3]; norm_num)
  have hσ₂' : ∀ c, σ₂ c = c ^ Nat.card K := fun c => by rw [hσ₂, Nat.card_eq_fintype_card]
  have hSU : ∀ A : Matrix.SpecialLinearGroup (Fin 3) K₂,
      ((A : Matrix (Fin 3) (Fin 3) K₂).map σ₂)ᵀ * A = 1 ↔
        ∃ g : subsystemGroup Tag.F4 K₂ {κ.i, κ.j}, (g : ModGL Tag.F4 K₂) ∈ U ∧
          f4A2Equiv K₂ κ g = A := by
    intro A
    constructor
    · intro hA
      obtain ⟨g, rfl⟩ := (f4A2Equiv K₂ κ).surjective A
      exact ⟨g, (hU _).2 ⟨g.2, hA⟩, rfl⟩
    · rintro ⟨g, hgU, rfl⟩
      obtain ⟨_, hunit⟩ := (hU _).1 hgU
      exact hunit
  refine ⟨hSU, ?_⟩
  obtain ⟨a, ha, hma⟩ := exists_f4A2_sextic_twist_element h3 σ hσ κ hε
  have ha₆ : baseChangeGL (algebraMap K₃ K₆) a ∈ subsystemGroup Tag.F4 K₆ {κ.i, κ.j} :=
    baseChangeGL_mem_subsystemGroup _ ha
  have hcomp₂ : ∀ b, σ (algebraMap K₂ K₆ b) = algebraMap K₂ K₆ (σ₂ b) := fun b => by
    rw [hσ, hσ₂, map_pow]
  have hF := f4A2_sextic_fixed_eq κ σ σ₂ hcomp₂
    (exists_map_of_map_map_eq K₂ h2 σ hσ) hw₀ (weyl_word_mem_pair (M := K₆) κ ε) ⟨_, ha₆⟩
    hma θ hθ hU
  have hφinj : Function.Injective
      ((MulAut.conj (baseChangeGL (algebraMap K₃ K₆) a)).toMonoidHom.comp
        (baseChangeGL (algebraMap K₂ K₆))) :=
    (MulAut.conj _).injective.comp (baseChangeGL_injective _)
  let e : U ≃* ↥(subsystemGroup Tag.F4 K₆ {κ.i, κ.j} ⊓ θ.eqLocus (MonoidHom.id _)) :=
    (U.equivMapOfInjective _ hφinj).trans (MulEquiv.subgroupCongr hF.symm)
  obtain ⟨hcenU, hqsU⟩ := f4A2_unitary_center_quasisimple K K₂ h2 σ₂ hσ₂ hw₀ κ hU
  have hVQ : U.map (baseChangeGL (algebraMap K₂ K₆)) ≤ subsystemGroup Tag.F4 K₆ {κ.i, κ.j} := by
    rintro _ ⟨u, hu, rfl⟩
    exact baseChangeGL_mem_subsystemGroup _ ((hU u).1 hu).1
  obtain ⟨ζ, hζq, hζ0, hζ2⟩ := EvenF4QPlus.exists_pow_card_add_one_eq_one (K := K) (K₂ := K₂) h2
  have hσζ : σ₂ ζ = ζ⁻¹ := by
    rw [hσ₂]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, ← Nat.card_eq_fintype_card]
    exact hζq
  have hQK : ∀ g, g ∈ subsystemGroup Tag.F4 K₆ {κ.i, κ.j} ⊓ θ.eqLocus (MonoidHom.id _) ↔
      ∃ y ∈ U.map (baseChangeGL (algebraMap K₂ K₆)),
        g = baseChangeGL (algebraMap K₃ K₆) a * y * (baseChangeGL (algebraMap K₃ K₆) a)⁻¹ := by
    intro g
    rw [hF, Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, rfl⟩
  obtain ⟨hcent, hcenter, hodd⟩ := levi_centralizer_of_scalar κ hZ hL hVQ
    (scalar_of_commute_baseChange_unitary κ σ₂ hζ0 hζ2 hσζ hU hVQ) ha₆ hQK
  obtain ⟨P, hP⟩ := exists_conjSL_rootSL2_mem K K₂ h2 σ₂ hσ₂' κ hU
  refine ⟨a, ha, hF, ⟨e, fun u => rfl, fun g hg => ?_⟩, fun h4 => ?_, hcent, hcenter, hodd, P,
    fun A => ?_⟩
  · rw [mulEquiv_apply_mem_center_iff, hcenU g hg]
  · obtain ⟨hq, hp⟩ := hqsU h4
    exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq,
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective⟩
  · rw [← baseChangeGL_rootSL2_of_charTwo (algebraMap K₂ K₆) (isRoot_single _ κ.i), hF]
    exact ⟨_, hP A, rfl⟩

end CFSG.RankThree.Chevalley
