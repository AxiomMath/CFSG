module

public import CFSG.RankThree.GroupTheory.SteinbergCDCentralQuotientFixed
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.SteinbergR3ELinearPointwiseAutomorphisms

public section

open scoped commutatorElement MatrixGroups

namespace CFSG.RankThree.FieldFixedLayer

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.Classical CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)

attribute [local instance] LocalCores.layer_characteristic

section Abstract

theorem isSolvable_quotient_of_commutator_le {Q : Type*} [Group Q] (N : Subgroup Q) [N.Normal]
    (h : commutator Q ≤ N) : Group.IsSolvable (Q ⧸ N) := by
  refine Group.isSolvable_of_comm fun a b => ?_
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      apply h
      have hxy : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [hxy, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

variable {X : Type*} [Group X]

theorem isSolvable_layer_quotient_of_central_quotient (Z : Subgroup X) [Z.Normal]
    (hZ : Z ≤ Subgroup.center X) (β : MulAut X) (hβZ : Z.map (β : X →* X) = Z)
    (hM : CFSG.IsQuasisimple (((β : X →* X).eqLocus (MonoidHom.id X)).map
        (QuotientGroup.mk' Z)) ∨
      Group.IsSolvable (((β : X →* X).eqLocus (MonoidHom.id X)).map (QuotientGroup.mk' Z))) :
    Group.IsSolvable
      (((QuotientGroup.congr Z Z β hβZ : X ⧸ Z →* X ⧸ Z).eqLocus (MonoidHom.id _)) ⧸
        layer ((QuotientGroup.congr Z Z β hβZ : X ⧸ Z →* X ⧸ Z).eqLocus (MonoidHom.id _))) := by
  obtain ⟨_, δ, -, -, -, -, -, -, -, hCQ, hMn, ε, -, hεker, -, -, hab, -⟩ :=
    GroupTheory.central_quotient_fixed_group_exact_sequence Z hZ β hβZ
  have hcomm : commutator ((QuotientGroup.congr Z Z β hβZ : X ⧸ Z →* X ⧸ Z).eqLocus
      (MonoidHom.id _)) ≤ (((β : X →* X).eqLocus (MonoidHom.id X)).map
        (QuotientGroup.mk' Z)).subgroupOf ((QuotientGroup.congr Z Z β hβZ : X ⧸ Z →* X ⧸ Z).eqLocus
          (MonoidHom.id _)) := by
    rw [← hεker, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hab (ε x) (ε y),
      mul_inv_cancel_right, mul_inv_cancel]
  rcases hM with hq | hs
  ·
    have hMq := LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCQ).symm hq
    have hcompo : IsComponent ((((β : X →* X).eqLocus (MonoidHom.id X)).map
        (QuotientGroup.mk' Z)).subgroupOf ((QuotientGroup.congr Z Z β hβZ :
          X ⧸ Z →* X ⧸ Z).eqLocus (MonoidHom.id _))) := ⟨hMq, hMn.isSubnormal⟩
    exact isSolvable_quotient_of_commutator_le _ (hcomm.trans (le_sSup hcompo))
  ·
    have : Group.IsSolvable ((((β : X →* X).eqLocus (MonoidHom.id X)).map
        (QuotientGroup.mk' Z)).subgroupOf ((QuotientGroup.congr Z Z β hβZ :
          X ⧸ Z →* X ⧸ Z).eqLocus (MonoidHom.id _))) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hCQ).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hCQ).injective
    have := Group.isSolvable_of_comm hab
    have : Group.IsSolvable ((QuotientGroup.congr Z Z β hβZ : X ⧸ Z →* X ⧸ Z).eqLocus
        (MonoidHom.id _)) :=
      Group.isSolvable_of_ker_le_range (Subgroup.subtype _) ε
        (by rw [hεker, Subgroup.range_subtype])
    exact Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)

end Abstract

section Linear

variable {n : ℕ} {K : Type} [Field K]

theorem linear_fixed_image_isQuasisimple (hn : 3 ≤ n) (σ : K ≃+* K) :
    CFSG.IsQuasisimple (((slFieldAut
      (Fin n) K σ : SL(n, K) →* SL(n, K)).eqLocus
        (MonoidHom.id _)).map (QuotientGroup.mk' (scalars n K))) := by
  set k := fixSubfield σ
  set j : SL(n, k) →* SL(n, K) :=
    Matrix.SpecialLinearGroup.map k.subtype with hj
  have hjcoe : ∀ g : SL(n, k),
      ((j g : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
        (g : Matrix (Fin n) (Fin n) k).map k.subtype := fun _ => rfl
  have hjinj : Function.Injective j := fun g g' hgg' => Subtype.ext (Matrix.ext fun a b =>
    Subtype.val_injective (by
      have h1 := congrArg (fun x : SL(n, K) =>
        (x : Matrix (Fin n) (Fin n) K) a b) hgg'
      simp only [hjcoe, Matrix.map_apply] at h1
      exact h1))
  have hC : (slFieldAut (Fin n) K σ :
      SL(n, K) →* SL(n, K)).eqLocus (MonoidHom.id _) =
        j.range := by
    ext g
    constructor
    · intro hg
      have hg' : slFieldAut (Fin n) K σ g
          = g := hg
      have hent : ∀ a b, σ ((g : Matrix (Fin n) (Fin n) K) a b) =
          (g : Matrix (Fin n) (Fin n) K) a b := by
        intro a b
        have h1 := congrArg (fun x : SL(n, K) =>
          (x : Matrix (Fin n) (Fin n) K) a b) hg'
        simpa only [CFSG.RankThree.LinearPointwise.slFieldAut_apply, Matrix.map_apply] using h1
      let g₀ : Matrix (Fin n) (Fin n) k := Matrix.of fun a b => ⟨_, hent a b⟩
      have hg₀ : g₀.map k.subtype = g := Matrix.ext fun _ _ => rfl
      have hdet : g₀.det = 1 := Subtype.val_injective (by
        change k.subtype g₀.det = k.subtype 1
        rw [RingHom.map_det, map_one]
        change (g₀.map k.subtype).det = 1
        rw [hg₀]
        exact g.2)
      exact ⟨⟨g₀, hdet⟩, Subtype.ext hg₀⟩
    · rintro ⟨g₀, rfl⟩
      apply Subtype.ext
      ext a b
      change σ (((g₀ : Matrix (Fin n) (Fin n) k) a b : k) : K) = (((g₀ : Matrix (Fin n) (Fin n) k)
        a b : k) : K)
      exact ((g₀ : Matrix (Fin n) (Fin n) k) a b).2
  have hq : CFSG.IsQuasisimple j.range := LocalCores.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective hjinj) (Classical2.isQuasisimple_specialLinearGroup hn)
  rw [hC]
  refine LocalCores.isQuasisimple_map hq _ fun hle => ?_
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro h
    simp only [Fin.mk.injEq, zero_ne_one] at h
  have hmem := hle ⟨Matrix.SpecialLinearGroup.transvection h01 (1 : k), rfl⟩
  rw [QuotientGroup.ker_mk'] at hmem
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hmem
  have h1 := congrFun (congrFun hc ⟨0, by omega⟩) ⟨1, by omega⟩
  rw [hjcoe, Matrix.map_apply, CFSG.LinearGroups.coe_transvection, Matrix.add_apply,
    Matrix.one_apply_ne h01, Matrix.single_apply_same, zero_add, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ h01] at h1
  exact one_ne_zero h1

theorem linear_fixed_group_layer_quotient_solvable (hn : 3 ≤ n) (σ : K ≃+* K) :
    Group.IsSolvable (((fieldAut n K σ).toMonoidHom.eqLocus (MonoidHom.id _)) ⧸
      layer ((fieldAut n K σ).toMonoidHom.eqLocus (MonoidHom.id _))) :=
  isSolvable_layer_quotient_of_central_quotient (scalars n K) (scalars_le_center n K)
    (slFieldAut (Fin n) K σ)
    (map_scalars_eq n K _) (Or.inl (linear_fixed_image_isQuasisimple hn σ))

end Linear

section Unitary

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem unitary_fixed_image_isQuasisimple_or_isSolvable (h : UnitaryFieldData ℓ f K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) {n : ℕ} (hn : 3 ≤ n) :
    CFSG.IsQuasisimple ((((fieldSUHom h n σ :
        MulAut (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
          gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →*
            gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).eqLocus
              (MonoidHom.id _)).map (QuotientGroup.mk'
                (normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n))) ∨
      Group.IsSolvable ((((fieldSUHom h n σ :
        MulAut (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
          gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →*
            gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).eqLocus
              (MonoidHom.id _)).map (QuotientGroup.mk' (normOneScalars h
                (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n))) := by
  have := h.finite
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  have hinj := subfieldPSU_injective h h₀ hbar n (by omega)
  have hM : ((((fieldSUHom h n σ :
        MulAut (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
          gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →*
            gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).eqLocus
              (MonoidHom.id _)).map (QuotientGroup.mk'
                (normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n))) =
      (subfieldPSU h h₀ hbar n).range := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : glAut σ (g : GL (Fin n) K) = g := congrArg Subtype.val (hg : _ = g)
      obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed n hg'
      have hg₀S := mem_gramSU_of_subfieldGL h n h₀ hbar (hg₀ ▸ g.2)
      refine ⟨((⟨g₀, hg₀S⟩ : gramSU h₀ _) : primeFormP h₀ _), ?_⟩
      rw [subfieldPSU_mk]
      congr 1
      exact Subtype.ext hg₀
    · rintro ⟨y, rfl⟩
      induction y using QuotientGroup.induction_on with
      | H g₀ =>
        refine ⟨subfieldSU h h₀ hbar n g₀, ?_, (subfieldPSU_mk h h₀ hbar n g₀).symm⟩
        refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
        change σ ((((g₀ : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ))
          i j : fixSubfield σ) : K) = (((g₀ : GL (Fin n) (fixSubfield σ)) :
            Matrix (Fin n) (Fin n) (fixSubfield σ)) i j : K)
        exact (((g₀ : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j).2
  rw [hM]
  by_cases hq₀ : n = 3 ∧ ℓ ^ (f / p) = 2
  ·
    right
    obtain ⟨rfl, hq2⟩ := hq₀
    have h72 := card_primeFormP_three_two h₀ hq2
    have : Finite (primeFormP h₀ ((1 : GL (Fin 3) (fixSubfield σ)) :
        Matrix (Fin 3) (Fin 3) (fixSubfield σ))) :=
      Nat.finite_of_card_ne_zero (by rw [h72]; norm_num)
    have : Group.IsSolvable (primeFormP h₀ ((1 : GL (Fin 3) (fixSubfield σ)) :
        Matrix (Fin 3) (Fin 3) (fixSubfield σ))) := isSolvable_of_card_primeFactors_le_two (by
      rw [h72, show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
      decide)
    exact Group.isSolvable_of_surjective (MonoidHom.ofInjective hinj).surjective
  ·
    left
    have := isSimpleGroup_primeFormP_one h₀ hn hq₀
    have hnc := not_commute_primeFormP_one h₀ hn hq₀
    refine LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hinj)
      (LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
    by_contra hcon
    exact hnc fun a b => by
      by_contra hab
      exact hcon ⟨a, b, hab⟩

theorem unitary_fixed_group_layer_quotient_solvable (h : UnitaryFieldData ℓ f K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) {n : ℕ} (hn : 3 ≤ n) :
    Group.IsSolvable (fieldFixedPSU h n σ ⧸ layer (fieldFixedPSU h n σ)) :=
  isSolvable_layer_quotient_of_central_quotient
    (normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n)
    (normOneScalars_le_center h _ n) (fieldSUHom h n σ)
    (map_normOneScalars_field h isPrimeFormGram_one σ)
    (unitary_fixed_image_isQuasisimple_or_isSolvable h hp hp2 hσ hn)

end Unitary

theorem linear_unitary_odd_prime_field_fixed_group_solvable_layer_quotient {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n) :
    (∀ (ℓ f : ℕ) (K : Type) [Field K] [Finite K], ℓ.Prime → 1 ≤ f → Nat.card K = ℓ ^ f →
      ∀ σ : K ≃+* K, orderOf σ = p →
        Group.IsSolvable (((fieldAut n K σ).toMonoidHom.eqLocus (MonoidHom.id _)) ⧸
          layer ((fieldAut n K σ).toMonoidHom.eqLocus (MonoidHom.id _)))) ∧
    (∀ (ℓ f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K) (σ : K ≃+* K),
      orderOf σ = p → Group.IsSolvable (fieldFixedPSU h n σ ⧸ layer (fieldFixedPSU h n σ))) :=
  ⟨fun _ _ _ _ _ _ _ _ σ _ => linear_fixed_group_layer_quotient_solvable hn σ,
    fun _ _ _ _ h _ hσ => unitary_fixed_group_layer_quotient_solvable h hp hp2 hσ hn⟩

end CFSG.RankThree.FieldFixedLayer
