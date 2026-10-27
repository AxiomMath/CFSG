module

public import CFSG.RankThree.Chevalley.SteinbergBUF4A2SL3Restriction
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusDoubleEdge
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.RankThree.Coprime.EvenCenterSectionCover
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusRootPair

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint F4Weyl
  EvenG2 EvenF4QPlus CFSG.RankThree.E6 NativeLevi
open scoped Pointwise commutatorElement Matrix

namespace EvenF4QPlus

section Swap

variable {L : Type} [Field L]

@[expose] def swapMat01 (c : L) : Matrix (Fin 3) (Fin 3) L := !![0, c⁻¹, 0; c, 0, 0; 0, 0, 1]

@[expose] def swapMat02 : Matrix (Fin 3) (Fin 3) L := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem eq_scalar_of_commute_swapMat {ζ : L} (hζ : ζ ≠ 0) (hζ2 : ζ ^ 2 ≠ 1)
    {X : Matrix (Fin 3) (Fin 3) L} (h1 : X * swapMat01 1 = swapMat01 1 * X)
    (h2 : X * swapMat01 ζ = swapMat01 ζ * X) (h3 : X * swapMat02 = swapMat02 * X) :
    X = Matrix.scalar (Fin 3) (X 0 0) := by
  have hζζ : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ
  have hζ1 : ζ - 1 ≠ 0 := fun h => hζ2 (by rw [sub_eq_zero.1 h, one_pow])
  have hζ21 : ζ ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hζ2
  have a00 := congrFun (congrFun h1 0) 0
  have a01 := congrFun (congrFun h1 0) 1
  have a02 := congrFun (congrFun h1 0) 2
  have a20 := congrFun (congrFun h1 2) 0
  have b00 := congrFun (congrFun h2 0) 0
  have b12 := congrFun (congrFun h2 1) 2
  have b20 := congrFun (congrFun h2 2) 0
  have c02 := congrFun (congrFun h3 0) 2
  simp [swapMat01, Matrix.mul_apply, Fin.sum_univ_three] at a00 a01 a02 a20 b00 b12 b20
  simp [swapMat02, Matrix.mul_apply, Fin.sum_univ_three] at c02
  have x01 : X 0 1 = 0 := by
    have h : X 0 1 * (ζ ^ 2 - 1) = 0 := by linear_combination ζ * b00 + X 1 0 * hζζ - a00
    exact (mul_eq_zero.1 h).resolve_right hζ21
  have x12 : X 1 2 = 0 := by
    have h : X 1 2 * (ζ - 1) = 0 := by linear_combination -b12 - ζ * a02
    exact (mul_eq_zero.1 h).resolve_right hζ1
  have x21 : X 2 1 = 0 := by
    have h : X 2 1 * (ζ - 1) = 0 := by linear_combination b20 - a20
    exact (mul_eq_zero.1 h).resolve_right hζ1
  have x10 : X 1 0 = 0 := by rw [← a00, x01]
  have x02 : X 0 2 = 0 := by rw [a02, x12]
  have x20 : X 2 0 = 0 := by rw [← a20, x21]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.scalar_apply, x01, x02, x10, x12, x20, x21, ← a01, ← c02]

theorem det_swapMat01 [CharP L 2] {c : L} (hc : c ≠ 0) : (swapMat01 c).det = 1 := by
  simp [swapMat01, Matrix.det_fin_three, hc, CharTwo.neg_eq]

theorem det_swapMat02 [CharP L 2] : (swapMat02 : Matrix (Fin 3) (Fin 3) L).det = 1 := by
  simp [swapMat02, Matrix.det_fin_three, CharTwo.neg_eq]

theorem unitary_swapMat01 (σ : L →+* L) {c : L} (hc : c ≠ 0) (hσc : σ c = c⁻¹) :
    ((swapMat01 c).map σ)ᵀ * swapMat01 c = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [swapMat01, Matrix.mul_apply, Fin.sum_univ_three, map_inv₀, hσc, hc]

theorem unitary_swapMat02 (σ : L →+* L) :
    ((swapMat02 : Matrix (Fin 3) (Fin 3) L).map σ)ᵀ * swapMat02 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [swapMat02, Matrix.mul_apply, Fin.sum_univ_three]

end Swap

theorem exists_pow_card_add_one_eq_one {K K₂ : Type} [Field K] [Finite K] [CharP K 2] [Field K₂]
    [Algebra K K₂] (hdeg : Module.finrank K K₂ = 2) :
    ∃ ζ : K₂, ζ ^ (Nat.card K + 1) = 1 ∧ ζ ≠ 0 ∧ ζ ^ 2 ≠ 1 := by
  classical
  have : Module.Finite K K₂ := Module.finite_of_finrank_pos (by omega)
  have : Finite K₂ := Module.finite_of_finite K
  have : Fintype K₂ := Fintype.ofFinite K₂
  have hq2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have heven : 2 ∣ Nat.card K := by
    have : Fintype K := Fintype.ofFinite K
    have h0 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
    rw [Fintype.card_eq_nat_card] at h0
    exact (CharP.cast_eq_zero_iff K 2 _).1 h0
  have hq2' : 2 ≤ Nat.card K := Nat.le_of_dvd hq1 heven
  have hrp : (Nat.card K + 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hrdvd : (Nat.card K + 1).minFac ∣ Nat.card K + 1 := Nat.minFac_dvd _
  have hr2 : (Nat.card K + 1).minFac ≠ 2 := by
    intro h
    rw [h] at hrdvd
    omega
  have hdvd₂ : Nat.card K + 1 ∣ Nat.card K₂ - 1 := by
    refine ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  have hrK : (Nat.card K + 1).minFac ∣ Fintype.card K₂ˣ := by
    rw [Fintype.card_eq_nat_card, Nat.card_units]
    exact hrdvd.trans hdvd₂
  have : Fact (Nat.card K + 1).minFac.Prime := ⟨hrp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card _ hrK
  refine ⟨u, ?_, u.ne_zero, ?_⟩
  · have h1 : u ^ (Nat.card K + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hu ▸ hrdvd)
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  · intro h
    have h1 : u ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hu] at h2
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).1 h2)

theorem twistedEntrywise_eq_self_iff_unitary
    {K₂ : Type} [Field K₂] [CharP K₂ 2] (κ : F4A2Kind)
    (σ : K₂ →+* K₂) {w₀ : WeylGroup .F4} (hw₀ : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v)
    (g : subsystemGroup .F4 K₂ {κ.i, κ.j}) :
    twistedEntrywise (canonicalRep (coxeterSystem .F4) K₂ w₀) σ g = g ↔
      ((f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂).map σ)ᵀ *
        (f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) = 1 := by
  obtain ⟨-, -, -, -, -, -, hmapσ, -, hneg, -⟩ :=
    even_F4_native_A2_root_groups_exact_SL3_restriction K₂ κ
  obtain ⟨hσg, hσr⟩ := hmapσ σ g
  obtain ⟨hN, hNr⟩ := hneg w₀ hw₀
  have hθ : twistedEntrywise (canonicalRep (coxeterSystem .F4) K₂ w₀) σ g =
      ((⟨_, hN _ hσg⟩ : subsystemGroup .F4 K₂ {κ.i, κ.j}) : ModGL .F4 K₂) := by
    rw [twistedEntrywise_apply]
  have hr : ((f4A2Equiv K₂ κ ⟨_, hN _ hσg⟩ : Matrix.SpecialLinearGroup (Fin 3) K₂) :
      Matrix (Fin 3) (Fin 3) K₂) =
      (((f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂).map σ)⁻¹)ᵀ := by
    rw [hNr ⟨_, hσg⟩, hσr]
  have hdet : IsUnit ((f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂).map σ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe,
      map_one]
    exact isUnit_one
  rw [hθ]
  constructor
  · intro h
    have h1 : (⟨_, hN _ hσg⟩ : subsystemGroup .F4 K₂ {κ.i, κ.j}) = g := Subtype.ext h
    have h2 : ((f4A2Equiv K₂ κ ⟨_, hN _ hσg⟩ : Matrix.SpecialLinearGroup (Fin 3) K₂) :
        Matrix (Fin 3) (Fin 3) K₂) = (f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) := by
      rw [h1]
    rw [hr] at h2
    have key : ((f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂).map σ)ᵀ *
        (((f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂).map σ)⁻¹)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one]
    rwa [h2] at key
  · intro h
    have h2 : (((f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂).map σ)⁻¹)ᵀ =
        (f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) := by
      rw [Matrix.transpose_nonsing_inv]
      exact Matrix.inv_eq_right_inv h
    have h1 : (⟨_, hN _ hσg⟩ : subsystemGroup .F4 K₂ {κ.i, κ.j}) = g :=
      (f4A2Equiv K₂ κ).injective (Subtype.ext (by rw [hr, h2]))
    exact congrArg Subtype.val h1

end EvenF4QPlus

open EvenF4QPlus

theorem even_F4_qplus_A2_root_kernel_unitary_fixed_derived_group
    (K : Type) [Field K] [Finite K]
    [CharP K 2] (K₂ : Type) [Field K₂] [Algebra K K₂] (hdeg : Module.finrank K K₂ = 2)
    (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K) (w₀ : WeylGroup .F4)
    (hw₀ : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v) (Γ : Subgroup (ModGL .F4 K₂))
    (hΓ : Γ = adjointGroup .F4 K₂ ⊓ (twistedEntrywise (canonicalRep (coxeterSystem .F4) K₂ w₀)
      (σ : K₂ →+* K₂)).eqLocus (MonoidHom.id _))
    (κ : F4A2Kind) (R : Subgroup (ModGL .F4 K₂))
    (hR : R = subsystemGroup .F4 K₂ {κ.i, κ.j} ⊓ Γ) :
    (∀ g : subsystemGroup .F4 K₂ {κ.i, κ.j}, (g : ModGL .F4 K₂) ∈ R ↔
      ((f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂).map σ)ᵀ *
        (f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) = 1) ∧
    (∀ (g : subsystemGroup .F4 K₂ {κ.i, κ.j}) (hg : (g : ModGL .F4 K₂) ∈ R),
      (⟨g, hg⟩ : R) ∈ Subgroup.center R ↔ ∃ t : K₂, t ^ (Nat.card K + 1) = 1 ∧ t ^ 3 = 1 ∧
        (f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) = Matrix.scalar (Fin 3) t) ∧
    Subgroup.centralizer (((R.subgroupOf (subsystemGroup .F4 K₂ {κ.i, κ.j})).map
        (Matrix.SpecialLinearGroup.toGL.comp (f4A2Equiv K₂ κ).toMonoidHom) :
          Subgroup (GL (Fin 3) K₂)) : Set (GL (Fin 3) K₂)) =
      (Matrix.GeneralLinearGroup.scalar (Fin 3)).range ∧
    (4 ≤ Nat.card K → CFSG.IsQuasisimple R ∧ Group.IsPerfect R) ∧
    standardLevi .F4 K₂ {κ.i, κ.j} ⊓ Subgroup.centralizer (R : Set (ModGL .F4 K₂)) =
      (Subgroup.center (standardLevi .F4 K₂ {κ.i, κ.j})).map
        (standardLevi .F4 K₂ {κ.i, κ.j}).subtype ∧
    (∀ y, y ∈ (Subgroup.center (standardLevi .F4 K₂ {κ.i, κ.j})).map
        (standardLevi .F4 K₂ {κ.i, κ.j}).subtype ↔
      y ∈ torusGroup .F4 K₂ ∧ ∀ j ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)),
        torusRootChar y (Pi.single j 1) = 1) ∧
    Odd (Nat.card (Subgroup.center (standardLevi .F4 K₂ {κ.i, κ.j}))) ∧
    ∀ p : ℕ, p.Prime → 3 < p → p ∣ Nat.card K + 1 →
    ∀ x ∈ torusGroup .F4 K₂ ⊓ Γ, orderOf x = p →
      {β | IsRoot .F4 β ∧ torusRootChar x β = 1} = parabolicRoots .F4 {κ.i, κ.j} →
      ∀ D : Subgroup (ModGL .F4 K₂), D = Γ ⊓ Subgroup.centralizer {x} →
        ⁅D, D⁆ = R ∧ CFSG.layer R = ⊤ ∧ R ≠ ⊥ ∧
        D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 K₂)) = (Subgroup.center D).map D.subtype ∧
        (Subgroup.center D).map D.subtype ≤ torusGroup .F4 K₂ ∧
        Odd (Nat.card (Subgroup.center D)) := by
  classical
  obtain ⟨hfin, -, -⟩ := quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
  obtain ⟨ζ, hζq, hζ0, hζ2⟩ := exists_pow_card_add_one_eq_one (K := K) (K₂ := K₂) hdeg
  have hσinv : ∀ c : K₂, c ^ (Nat.card K + 1) = 1 → σ c = c⁻¹ := fun c hc => by
    rw [hσ]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hc])
  obtain ⟨-, -, -, -, htoriff, -, -, -, -, hconj⟩ :=
    even_F4_native_A2_root_groups_exact_SL3_restriction K₂ κ
  set J : Set (Fin Tag.F4.rank) := {κ.i, κ.j} with hJ
  have hQC : subsystemGroup .F4 K₂ J ≤ adjointGroup .F4 K₂ := subsystemGroup_le_adjointGroup' J
  have hRQ : R ≤ subsystemGroup .F4 K₂ J := by
    rw [hR]
    exact inf_le_left
  have hRΓ : R ≤ Γ := by
    rw [hR]
    exact inf_le_right
  have hmemR : ∀ g : subsystemGroup .F4 K₂ J, (g : ModGL .F4 K₂) ∈ R ↔
      ((f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂).map σ)ᵀ *
        (f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) = 1 := by
    intro g
    rw [hR, hΓ]
    constructor
    · rintro ⟨-, -, h⟩
      exact (twistedEntrywise_eq_self_iff_unitary κ (σ : K₂ →+* K₂) hw₀ g).1 h
    · intro h
      exact ⟨g.2, hQC g.2, (twistedEntrywise_eq_self_iff_unitary κ (σ : K₂ →+* K₂) hw₀ g).2 h⟩
  have hsw : ∀ A : Matrix.SpecialLinearGroup (Fin 3) K₂,
      ((A : Matrix (Fin 3) (Fin 3) K₂).map σ)ᵀ * (A : Matrix (Fin 3) (Fin 3) K₂) = 1 →
      ∃ g : subsystemGroup .F4 K₂ J, (g : ModGL .F4 K₂) ∈ R ∧ f4A2Equiv K₂ κ g = A := by
    intro A hA
    obtain ⟨g, rfl⟩ := (f4A2Equiv K₂ κ).surjective A
    exact ⟨g, (hmemR g).2 hA, rfl⟩
  obtain ⟨g₁, hg₁R, hg₁⟩ := hsw ⟨swapMat01 1, det_swapMat01 one_ne_zero⟩
    (unitary_swapMat01 (σ : K₂ →+* K₂) one_ne_zero (by rw [inv_one]; exact map_one σ))
  obtain ⟨g₂, hg₂R, hg₂⟩ := hsw ⟨swapMat01 ζ, det_swapMat01 hζ0⟩
    (unitary_swapMat01 (σ : K₂ →+* K₂) hζ0 (hσinv ζ hζq))
  obtain ⟨g₃, hg₃R, hg₃⟩ := hsw ⟨swapMat02, det_swapMat02⟩ (unitary_swapMat02 (σ : K₂ →+* K₂))
  have hcomm : ∀ X : Matrix (Fin 3) (Fin 3) K₂,
      (∀ g : subsystemGroup .F4 K₂ J, (g : ModGL .F4 K₂) ∈ R →
        X * (f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) =
          (f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) * X) →
      X = Matrix.scalar (Fin 3) (X 0 0) := by
    intro X hX
    have h1 := hX g₁ hg₁R
    have h2 := hX g₂ hg₂R
    have h3 := hX g₃ hg₃R
    rw [hg₁] at h1
    rw [hg₂] at h2
    rw [hg₃] at h3
    exact eq_scalar_of_commute_swapMat hζ0 hζ2 h1 h2 h3
  have hcent : Subgroup.centralizer (((R.subgroupOf (subsystemGroup .F4 K₂ J)).map
      (Matrix.SpecialLinearGroup.toGL.comp (f4A2Equiv K₂ κ).toMonoidHom) :
        Subgroup (GL (Fin 3) K₂)) : Set (GL (Fin 3) K₂)) =
      (Matrix.GeneralLinearGroup.scalar (Fin 3)).range := by
    apply le_antisymm
    · intro X hX
      have hX' : (X : Matrix (Fin 3) (Fin 3) K₂) =
          Matrix.scalar (Fin 3) ((X : Matrix (Fin 3) (Fin 3) K₂) 0 0) := by
        apply hcomm
        intro g hg
        have h1 := Subgroup.mem_centralizer_iff.1 hX
          (Matrix.SpecialLinearGroup.toGL (f4A2Equiv K₂ κ g)) ⟨g, hg, rfl⟩
        have h2 := congrArg Units.val h1
        simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h2
        exact h2.symm
      have hu : (X : Matrix (Fin 3) (Fin 3) K₂) 0 0 ≠ 0 := by
        intro h0
        have h1 := X.mul_inv
        rw [hX', h0, map_zero, zero_mul] at h1
        exact zero_ne_one h1
      refine ⟨Units.mk0 _ hu, Units.ext ?_⟩
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
      exact hX'.symm
    · rintro _ ⟨u, rfl⟩
      have hz : Matrix.GeneralLinearGroup.scalar (Fin 3) u ∈ Subgroup.center (GL (Fin 3) K₂) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨u, rfl⟩
      exact Subgroup.mem_centralizer_iff.2 fun A _ => (Subgroup.mem_center_iff.1 hz A)
  have hcenter : ∀ (g : subsystemGroup .F4 K₂ J) (hg : (g : ModGL .F4 K₂) ∈ R),
      (⟨g, hg⟩ : R) ∈ Subgroup.center R ↔ ∃ t : K₂, t ^ (Nat.card K + 1) = 1 ∧ t ^ 3 = 1 ∧
        (f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) = Matrix.scalar (Fin 3) t := by
    intro g hg
    constructor
    · intro hz
      have hX : (f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) =
          Matrix.scalar (Fin 3) ((f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) 0 0) := by
        apply hcomm
        intro g' hg'
        have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g', hg'⟩)
        have h2 : g' * g = g * g' := Subtype.ext h1
        have h3 := congrArg (fun z => ((f4A2Equiv K₂ κ z : Matrix.SpecialLinearGroup (Fin 3) K₂) :
          Matrix (Fin 3) (Fin 3) K₂)) h2
        simp only [map_mul, Matrix.SpecialLinearGroup.coe_mul] at h3
        exact h3.symm
      refine ⟨(f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) 0 0, ?_, ?_, hX⟩
      · have hu := (hmemR g).1 hg
        rw [hX] at hu
        have h00 := congrFun (congrFun hu 0) 0
        simp [Matrix.mul_apply, Fin.sum_univ_three, hσ] at h00
        rw [pow_succ]
        exact h00
      · have hd := Matrix.SpecialLinearGroup.det_coe (f4A2Equiv K₂ κ g)
        rw [hX, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin] at hd
        exact hd
    · rintro ⟨t, -, -, ht⟩
      rw [Subgroup.mem_center_iff]
      rintro ⟨y, hy⟩
      have hyQ : y ∈ subsystemGroup .F4 K₂ J := hRQ hy
      have h1 : (⟨y, hyQ⟩ : subsystemGroup .F4 K₂ J) * g = g * ⟨y, hyQ⟩ :=
        (f4A2Equiv K₂ κ).injective (Subtype.ext (by
          simp only [map_mul, Matrix.SpecialLinearGroup.coe_mul, ht]
          exact ((Matrix.scalar_commute t (fun r => Commute.all t r) _).eq).symm))
      exact Subtype.ext (show y * (g : ModGL .F4 K₂) = (g : ModGL .F4 K₂) * y from
        congrArg Subtype.val h1)
  have hq4part : 4 ≤ Nat.card K → CFSG.IsQuasisimple R ∧ Group.IsPerfect R := by
    intro hq4
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨m, -, hm⟩ := FiniteField.card K 2
    have hqm : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcard : Nat.card K₂ = (2 ^ (m : ℕ)) ^ 2 := by
      rw [natCard_eq_sq_of_finrank_eq_two hdeg, hqm]
    have hU : UnitaryFieldData 2 m K₂ :=
      ⟨Nat.prime_two, m.pos, by rw [hcard, ← pow_mul, mul_comm]⟩
    have hbar : (⇑hU.bar : K₂ → K₂) = ⇑σ := funext fun c => by
      rw [UnitaryFieldData.bar_apply, hσ, hqm]
    set φ : R →* GL (Fin 3) K₂ := Matrix.SpecialLinearGroup.toGL.comp
      ((f4A2Equiv K₂ κ).toMonoidHom.comp (Subgroup.inclusion hRQ)) with hφ
    have hφinj : Function.Injective φ :=
      Matrix.SpecialLinearGroup.toGL_injective.comp
        ((f4A2Equiv K₂ κ).injective.comp (Subgroup.inclusion_injective hRQ))
    have hrange : φ.range = CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 m K₂ 3 := by
      ext A
      rw [CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff hU, MonoidHom.mem_range, hbar]
      constructor
      · rintro ⟨y, rfl⟩
        refine ⟨Matrix.SpecialLinearGroup.det_coe _, ?_⟩
        exact (hmemR (Subgroup.inclusion hRQ y)).1 y.2
      · rintro ⟨hdet, hunit⟩
        obtain ⟨g, hg⟩ := (f4A2Equiv K₂ κ).surjective ⟨A, hdet⟩
        have hgR : (g : ModGL .F4 K₂) ∈ R := (hmemR g).2 (by rw [hg]; exact hunit)
        refine ⟨⟨g, hgR⟩, Units.ext ?_⟩
        rw [hφ, MonoidHom.comp_apply, MonoidHom.comp_apply,
          Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
        have h1 : Subgroup.inclusion hRQ ⟨g, hgR⟩ = g := rfl
        rw [h1, MulEquiv.coe_toMonoidHom, hg]
    let e : R ≃* CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 m K₂ 3 :=
      (MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hrange)
    have hnq : (3, 2 ^ (m : ℕ)) ≠ (3, 2) := fun h => by
      have h2 := (Prod.mk_inj.1 h).2
      rw [← hqm] at h2
      omega
    have hQS := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K₂)
      (p := 2) (f := m) hcard le_rfl hnq).1
    have hQR : CFSG.IsQuasisimple R :=
      CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e.symm hQS
    exact ⟨hQR, hQR.1⟩
  have hRL : R ≤ standardLevi .F4 K₂ J := hRQ.trans (subsystemGroup_le_standardLevi J)
  have hconjcomm : ∀ h ∈ torusGroup .F4 K₂, ∀ (v : ModGL .F4 K₂)
      (hv : v ∈ subsystemGroup .F4 K₂ J), h * v ∈ Subgroup.centralizer (R : Set (ModGL .F4 K₂)) →
      Matrix.diagonal ![torusRootChar h (Pi.single κ.i 1) * torusRootChar h (Pi.single κ.j 1),
          torusRootChar h (Pi.single κ.j 1), 1] *
          (f4A2Equiv K₂ κ ⟨v, hv⟩ : Matrix (Fin 3) (Fin 3) K₂) =
        Matrix.scalar (Fin 3) ((Matrix.diagonal ![torusRootChar h (Pi.single κ.i 1) *
          torusRootChar h (Pi.single κ.j 1), torusRootChar h (Pi.single κ.j 1), 1] *
          (f4A2Equiv K₂ κ ⟨v, hv⟩ : Matrix (Fin 3) (Fin 3) K₂)) 0 0) := by
    intro h hh v hv hC
    obtain ⟨hN, hNr⟩ := hconj h hh v hv
    have hχi := torusRootChar_ne_zero (torusGroup_le_diagonalGroup hh) (Pi.single κ.i 1)
    have hχj := torusRootChar_ne_zero (torusGroup_le_diagonalGroup hh) (Pi.single κ.j 1)
    have hYdet : IsUnit (Matrix.diagonal ![torusRootChar h (Pi.single κ.i 1) *
        torusRootChar h (Pi.single κ.j 1), torusRootChar h (Pi.single κ.j 1), 1] *
        (f4A2Equiv K₂ κ ⟨v, hv⟩ : Matrix (Fin 3) (Fin 3) K₂)).det := by
      rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three,
        Matrix.SpecialLinearGroup.det_coe, mul_one, isUnit_iff_ne_zero]
      simp [hχi, hχj]
    apply hcomm
    intro z hz
    have hzc : (z : ModGL .F4 K₂) * (h * v) = h * v * z := Subgroup.mem_centralizer_iff.1 hC z hz
    have hfix : (⟨h * v * z * (h * v)⁻¹, hN z z.2⟩ : subsystemGroup .F4 K₂ J) = z :=
      Subtype.ext (show h * v * z * (h * v)⁻¹ = z by rw [← hzc, mul_inv_cancel_right])
    have h1 : ((f4A2Equiv K₂ κ ⟨_, hN z z.2⟩ : Matrix.SpecialLinearGroup (Fin 3) K₂) :
        Matrix (Fin 3) (Fin 3) K₂) = (f4A2Equiv K₂ κ z : Matrix (Fin 3) (Fin 3) K₂) := by
      rw [hfix]
    rw [hNr z] at h1
    rw [← mul_one (_ * (f4A2Equiv K₂ κ z : Matrix (Fin 3) (Fin 3) K₂)),
      ← Matrix.nonsing_inv_mul _ hYdet, ← mul_assoc, h1]
  have hcentL : standardLevi .F4 K₂ J ⊓ Subgroup.centralizer (R : Set (ModGL .F4 K₂)) =
      (Subgroup.center (standardLevi .F4 K₂ J)).map (standardLevi .F4 K₂ J).subtype := by
    rw [map_center_standardLevi]
    apply le_antisymm
    · intro y hy
      obtain ⟨hyL, hyC⟩ := Subgroup.mem_inf.1 hy
      rw [← SetLike.mem_coe, coe_standardLevi] at hyL
      obtain ⟨h, hh, v, hv, rfl⟩ := hyL
      have hχi := torusRootChar_ne_zero (torusGroup_le_diagonalGroup hh) (Pi.single κ.i 1)
      have hχj := torusRootChar_ne_zero (torusGroup_le_diagonalGroup hh) (Pi.single κ.j 1)
      have hY := hconjcomm h hh v hv hyC
      have hdiag : (f4A2Equiv K₂ κ ⟨v, hv⟩ : Matrix (Fin 3) (Fin 3) K₂).IsDiag := by
        intro a b hab
        have h1 := congrFun (congrFun hY a) b
        rw [Matrix.diagonal_mul, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hab] at h1
        refine (mul_eq_zero.1 h1).resolve_left ?_
        fin_cases a <;> simp [hχi, hχj]
      obtain ⟨g', hg'T, hg'⟩ := (htoriff _).2 hdiag
      have hg'v : g' = ⟨v, hv⟩ := (f4A2Equiv K₂ κ).injective hg'
      have hvT : v ∈ torusGroup .F4 K₂ := by
        have h1 := subsystemTorus_le_torusGroup hg'T
        rwa [hg'v] at h1
      have hyT : h * v ∈ torusGroup .F4 K₂ := mul_mem hh hvT
      have hY' := hconjcomm (h * v) hyT 1 (one_mem _) (by rw [mul_one]; exact hyC)
      have hr1 : ((f4A2Equiv K₂ κ ⟨1, one_mem _⟩ : Matrix.SpecialLinearGroup (Fin 3) K₂) :
          Matrix (Fin 3) (Fin 3) K₂) = 1 := by
        rw [show (⟨1, one_mem _⟩ : subsystemGroup .F4 K₂ J) = 1 from rfl, map_one,
          Matrix.SpecialLinearGroup.coe_one]
      rw [hr1, mul_one] at hY'
      have e1 := congrFun (congrFun hY' 1) 1
      have e2 := congrFun (congrFun hY' 2) 2
      simp [Matrix.scalar_apply] at e1 e2
      have hj1 : torusRootChar (h * v) (Pi.single κ.j 1) = 1 := by
        rw [e1]
        exact e2.symm
      have hi1 : torusRootChar (h * v) (Pi.single κ.i 1) = 1 := by
        have h1 := e2.symm
        rwa [hj1, mul_one] at h1
      refine ⟨hyT, fun j hj => ?_⟩
      rcases Set.mem_insert_iff.1 hj with rfl | hj'
      · exact hi1
      · rw [Set.mem_singleton_iff.1 hj']
        exact hj1
    · intro y hy
      exact ⟨torusGroup_le_standardLevi J hy.1, Subgroup.mem_centralizer_iff.2 fun z hz =>
        Subgroup.mem_centralizer_singleton_iff.1 (standardLevi_le_centralizer_of_mem hy (hRL hz))⟩
  have hZchar : ∀ y, y ∈ (Subgroup.center (standardLevi .F4 K₂ J)).map
      (standardLevi .F4 K₂ J).subtype ↔
      y ∈ torusGroup .F4 K₂ ∧ ∀ j ∈ J, torusRootChar y (Pi.single j 1) = 1 := by
    intro y
    rw [map_center_standardLevi]
    exact Iff.rfl
  have hZodd : Odd (Nat.card (Subgroup.center (standardLevi .F4 K₂ J))) := by
    rw [← Subgroup.card_map_of_injective (standardLevi .F4 K₂ J).subtype_injective,
      map_center_standardLevi]
    exact odd_card_simpleCharKernel J
  refine ⟨hmemR, hcenter, hcent, hq4part, hcentL, hZchar, hZodd,
    fun p hp hp3 hpq x hxT hx hsurv D hD => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hq4 : 4 ≤ Nat.card K := by
    have := Nat.le_of_dvd (Nat.succ_pos _) hpq
    have := five_le_of_prime_of_three_lt hp hp3
    omega
  obtain ⟨hquasi, hperf⟩ := hq4part hq4
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT.1
  have hker : rootCharKernel b = parabolicRoots .F4 J := by
    rw [← hsurv]
    ext β
    constructor
    · rintro ⟨hβ, h1⟩
      exact ⟨hβ, by rw [torusRootChar_rootDiagUnit b hβ, h1, Units.val_one]⟩
    · rintro ⟨hβ, h1⟩
      rw [torusRootChar_rootDiagUnit b hβ, Units.val_eq_one] at h1
      exact ⟨hβ, h1⟩
  have hob : orderOf b = p := (orderOf_rootDiagUnit b).symm.trans hx
  have hbp : b ^ p = 1 := hob ▸ pow_orderOf_eq_one b
  have hb1 : b ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hob
    exact hp.one_lt.ne hob
  have hX := toralCentralizer_eq_toralRootGroup_of_le (K := K₂)
    (F4_rootCharStabilizer_le_kernelReflectionGroup hp hp3 hbp hb1)
  have hCx : toralCentralizer .F4 K₂ b = standardLevi .F4 K₂ J := by
    rw [hX, toralRootGroup, hker, ← subsystemGroup_eq_rootSpan]
    rfl
  have hΓC : Γ ≤ adjointGroup .F4 K₂ := by
    rw [hΓ]
    exact inf_le_left
  have hDL : D = Γ ⊓ standardLevi .F4 K₂ J := by
    rw [hD, ← hCx, toralCentralizer, ← inf_assoc, inf_of_le_left hΓC]
  have hDle : D ≤ standardLevi .F4 K₂ J := by
    rw [hDL]
    exact inf_le_right
  have hDΓ : D ≤ Γ := by
    rw [hDL]
    exact inf_le_left
  have hRD : R ≤ D := by
    rw [hDL]
    exact le_inf hRΓ hRL
  have hRperf : ⁅R, R⁆ = R := Subgroup.isPerfect_iff.1 hperf
  have hcommD : ⁅D, D⁆ = R := by
    refine le_antisymm ?_ (hRperf.symm.le.trans (Subgroup.commutator_mono hRD hRD))
    rw [hR]
    exact le_inf ((Subgroup.commutator_mono hDle hDle).trans (commutator_standardLevi_le J))
      ((commutator_self_le D).trans hDΓ)
  have hlayer : CFSG.layer R = ⊤ := CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hquasi
  have hRne : R ≠ ⊥ := by
    intro hbot
    obtain ⟨-, hsimpQ, -⟩ := hquasi
    have h0 := (Subgroup.eq_bot_iff_forall R).1 hbot
    have hsub : Subsingleton (R ⧸ Subgroup.center R) := ⟨fun a c => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c
      rw [show a = 1 from Subtype.ext (h0 _ a.2), show c = 1 from Subtype.ext (h0 _ c.2)]⟩
    exact not_nontrivial_iff_subsingleton.2 hsub hsimpQ.toNontrivial
  have hcentD : D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 K₂)) =
      (Subgroup.center D).map D.subtype := by
    refine le_antisymm (fun y hy => ?_) ?_
    · obtain ⟨hyD, hyC⟩ := Subgroup.mem_inf.1 hy
      have hyZ : y ∈ (Subgroup.center (standardLevi .F4 K₂ J)).map
          (standardLevi .F4 K₂ J).subtype := by
        rw [← hcentL]
        exact ⟨hDle hyD, hyC⟩
      obtain ⟨z, hz, rfl⟩ := hyZ
      refine ⟨⟨_, hyD⟩, Subgroup.mem_center_iff.2 fun d => Subtype.ext ?_, rfl⟩
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨d, hDle d.2⟩)
      exact h1
    · rintro _ ⟨d, hd, rfl⟩
      refine ⟨d.2, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hd ⟨r, hRD hr⟩)
      exact h1
  have hZDle : (Subgroup.center D).map D.subtype ≤
      (Subgroup.center (standardLevi .F4 K₂ J)).map (standardLevi .F4 K₂ J).subtype := by
    rw [← hcentD, ← hcentL]
    exact inf_le_inf_right _ hDle
  refine ⟨hcommD, hlayer, hRne, hcentD, fun y hy => ((hZchar y).1 (hZDle hy)).1, ?_⟩
  have hdvd : Nat.card (Subgroup.center D) ∣
      Nat.card (Subgroup.center (standardLevi .F4 K₂ J)) := by
    rw [← Subgroup.card_map_of_injective D.subtype_injective,
      ← Subgroup.card_map_of_injective (standardLevi .F4 K₂ J).subtype_injective]
    exact Subgroup.card_dvd_of_le hZDle
  exact hZodd.of_dvd_nat hdvd

end CFSG.RankThree.Chevalley
