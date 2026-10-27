module

public import CFSG.Quasithin.H13.PSL3Tools
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.Quasithin.H13.Sp4SemilinearPower
public import CFSG.Quasithin.SteinbergBQReducibleTwoNormalizers
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.SteinbergBQ
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open scoped Pointwise

namespace CFSG.Quasithin.H13.PSL3

variable {F : Type} [Field F]

theorem slConjugation_transvection_of_monomial {A : GL (Fin 3) F} {w : Equiv.Perm (Fin 3)}
    {c : Fin 3 → Fˣ}
    (hA : ∀ j, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single j 1 = (c j : F) • Pi.single (w j) 1)
    {a b : Fin 3} (hab : a ≠ b) (t : F) :
    slConjugation 3 F A (SpecialLinearGroup.transvection hab t) =
      SpecialLinearGroup.transvection (w.injective.ne hab) ((c a : F) * (c b : F)⁻¹ * t) := by
  apply Subtype.ext
  rw [coe_slConjugation]
  change (A : Matrix (Fin 3) (Fin 3) F) * (1 + single a b t) * ((A⁻¹ : GL (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) = 1 + single (w a) (w b) ((c a : F) * (c b : F)⁻¹ * t)
  rw [Matrix.mul_add, Matrix.mul_one, monomial_mul_single (fun j => (c j).ne_zero)
    (monomial_apply hA), Matrix.add_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.mul_one]

theorem eq_top_of_unitriangular_le_of_monomialGL {Y : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hU : unitriangular 3 F ≤ Y) {A : GL (Fin 3) F} {w : Equiv.Perm (Fin 3)}
    (hA : IsMonomial (A : Matrix (Fin 3) (Fin 3) F) w) (hw1 : w ≠ 1) (hw3 : w ^ 3 = 1)
    (hAY : ∀ u ∈ unitriangular 3 F, slConjugation 3 F A u ∈ Y) : Y = ⊤ := by
  classical
  obtain ⟨c, hc⟩ := hA
  have hup : ∀ {i j : Fin 3} (hij : i < j) (t : F),
      SpecialLinearGroup.transvection hij.ne t ∈ Y := fun hij t =>
    hU (transvection_mem_unitriangular (K := F) hij t)
  have hlow : ∀ {a b : Fin 3} (hab : a < b) (t : F),
      SpecialLinearGroup.transvection (w.injective.ne hab.ne) t ∈ Y := by
    intro a b hab t
    have h1 := slConjugation_transvection_of_monomial hc hab.ne ((c b : F) * (c a : F)⁻¹ * t)
    have hcoef : (c a : F) * (c b : F)⁻¹ * ((c b : F) * (c a : F)⁻¹ * t) = t := by
      field_simp
    rw [hcoef] at h1
    rw [← h1]
    exact hAY _ (transvection_mem_unitriangular (K := F) hab _)
  have hcomm : ∀ {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
      (∀ s, SpecialLinearGroup.transvection hij s ∈ Y) →
      (∀ t, SpecialLinearGroup.transvection hjk t ∈ Y) →
      ∀ t, SpecialLinearGroup.transvection hik t ∈ Y := by
    intro i j k hij hjk hik h1 h2 t
    rw [← one_mul t, ← transvection_commutator hij hjk hik]
    exact mul_mem (mul_mem (mul_mem (h1 1) (h2 t)) (inv_mem (h1 1))) (inv_mem (h2 t))
  have hall : ∀ (i j : Fin 3) (hij : i ≠ j) (t : F), SpecialLinearGroup.transvection hij t ∈ Y := by
    rcases eq_finRotate_or_of_pow_three w hw1 hw3 with rfl | rfl
    · have h10 : ∀ t, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t ∈ Y :=
        fun t => hlow (a := 0) (b := 2) (by decide) t
      have h20 : ∀ t, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) t ∈ Y :=
        fun t => hlow (a := 1) (b := 2) (by decide) t
      have h21 : ∀ t, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t ∈ Y :=
        hcomm (j := 0) (by decide) (by decide) (by decide) h20 (fun t => hup (by decide) t)
      intro i j hij t
      fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd rfl hij
        | exact hup (by decide) t
        | exact h10 t
        | exact h20 t
        | exact h21 t
    · have h20 : ∀ t, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) t ∈ Y :=
        fun t => hlow (a := 0) (b := 1) (by decide) t
      have h21 : ∀ t, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t ∈ Y :=
        fun t => hlow (a := 0) (b := 2) (by decide) t
      have h10 : ∀ t, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t ∈ Y :=
        hcomm (j := 2) (by decide) (by decide) (by decide) (fun t => hup (by decide) t) h20
      intro i j hij t
      fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd rfl hij
        | exact hup (by decide) t
        | exact h10 t
        | exact h20 t
        | exact h21 t
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, t, rfl⟩
  exact hall i j hij t

theorem fieldAut_proj_planeElem {p : ℕ} [NeZero p] {ζ : F} (hζ : ζ ^ p = 1) (σ : F ≃+* F)
    {e : ℕ} (he : ∀ x, σ x = x ^ e) (v : sumZeroPlane p) :
    fieldAut 3 F σ (proj 3 F (planeElem ζ hζ v)) =
      proj 3 F (planeElem ζ hζ ((e : ZMod p) • v)) := by
  rw [fieldAut_proj]
  congr 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  change σ (diagPow ζ ((v : sumZeroPlane p) : Fin 3 → ZMod p) i j) =
    diagPow ζ (((e : ZMod p) • v : sumZeroPlane p) : Fin 3 → ZMod p) i j
  by_cases hij : i = j
  · subst hij
    rw [diagPow, diagonal_apply_eq, diagPow, diagonal_apply_eq, he, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, pow_val_mul hζ, pow_val_natCast hζ, ← pow_mul, ← pow_mul,
      mul_comm]
  · rw [diagPow, diagonal_apply_ne _ hij, diagPow, diagonal_apply_ne _ hij, map_zero]

theorem conjAut_proj_planeElem_of_monomial {p : ℕ} [NeZero p] {ζ : F} (hζ : ζ ^ p = 1)
    {A : GL (Fin 3) F} {w : Equiv.Perm (Fin 3)} {t : Fin 3 → F} (ht : ∀ m, t m ≠ 0)
    (hA : ∀ m, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single m 1 = t m • Pi.single (w m) 1)
    (v : sumZeroPlane p) :
    conjAut 3 F A (proj 3 F (planeElem ζ hζ v)) =
      proj 3 F (planeElem ζ hζ (permPlane w.symm v)) := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  change (A : Matrix (Fin 3) (Fin 3) F) * diagPow ζ ((v : sumZeroPlane p) : Fin 3 → ZMod p) *
    ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    diagPow ζ ((permPlane w.symm v : sumZeroPlane p) : Fin 3 → ZMod p)
  have hAA : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [diagPow, conj_diagonal_of_monomial hAA w t ht hA, diagPow, coe_permPlane]


theorem coe_smul_sylow {G : Type*} [Group G] {q : ℕ} (g : G) (P : Sylow q G) :
    ((g • P : Sylow q G) : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

theorem exists_monomial_sylow_of_permutable [Finite F] [CharP F 2] {p : ℕ} [Fact p.Prime]
    [NeZero p] (hp5 : 5 ≤ p) {ζ : F} (hζ : IsPrimitiveRoot ζ p) (U : Sylow 2 (projectiveSL 3 F))
    (hPU : (((diagPlane p ζ hζ.pow_eq_one).map (proj 3 F) : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)) * (U : Set (projectiveSL 3 F)) =
      (U : Set (projectiveSL 3 F)) * ((diagPlane p ζ hζ.pow_eq_one).map (proj 3 F) :
        Subgroup (projectiveSL 3 F))) :
    ∃ (N : SpecialLinearGroup (Fin 3) F) (wN : Equiv.Perm (Fin 3)),
      IsMonomial (N : Matrix (Fin 3) (Fin 3) F) wN ∧
      (U : Subgroup (projectiveSL 3 F)) =
        (projUnitriangular 3 F).map (MulAut.conj (proj 3 F N)).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3 : p ≠ 3 := by omega
  set Pd := (diagPlane p ζ hζ.pow_eq_one).map (proj 3 F) with hPd
  obtain ⟨Q₀, hQ₀⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (projectiveSL 3 F) Q₀ U
  have hU : (U : Subgroup (projectiveSL 3 F)) =
      (projUnitriangular 3 F).map (MulAut.conj x).toMonoidHom := by
    rw [← hx, coe_smul_sylow, hQ₀]
  obtain ⟨X, rfl⟩ := proj_surjective 3 F x
  set c : MulAut (projectiveSL 3 F) := MulAut.conj (proj 3 F X)⁻¹ with hc
  set Pd' := Pd.map c.toMonoidHom with hPd'
  have hcU : (U : Subgroup (projectiveSL 3 F)).map c.toMonoidHom = projUnitriangular 3 F := by
    rw [hU, Subgroup.map_map]
    convert Subgroup.map_id (projUnitriangular 3 F)
    ext y
    simp [hc]
  have hPU' : (Pd' : Set (projectiveSL 3 F)) * (projUnitriangular 3 F : Set (projectiveSL 3 F)) =
      (projUnitriangular 3 F : Set (projectiveSL 3 F)) * Pd' := by
    have hPU2 : (Pd : Set (projectiveSL 3 F)) * ((U : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)) = ((U : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) *
          (Pd : Set (projectiveSL 3 F)) := hPU
    rw [← hcU, hPd', Subgroup.coe_map c.toMonoidHom Pd,
      Subgroup.coe_map c.toMonoidHom (U : Subgroup (projectiveSL 3 F)), ← Set.image_mul, hPU2,
      Set.image_mul]
  have hPdp : IsPGroup p Pd' := by
    refine IsPGroup.iff_orderOf.mpr fun y => ?_
    obtain ⟨_, ⟨d, hd, rfl⟩, hy⟩ := y.2
    have h1 : y ^ p = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, ← hy, ← map_pow, ← map_pow, pow_eq_one_of_mem_diagPlane hd,
        map_one, map_one, OneMemClass.coe_one])
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  have h3 : ¬ 3 ∣ Nat.card Pd' := by
    obtain ⟨k, hk⟩ := hPdp.exists_card_eq
    rw [hk]
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hUp : IsPGroup 2 (projUnitriangular 3 F) := hQ₀ ▸ Q₀.isPGroup'
  have hperm := NQTerm.not_three_dvd_card_permProd Pd' (projUnitriangular 3 F) hPU' h3 hUp
  have hle := le_projUpperTriangular_of_not_three_dvd (NQTerm.le_permProd_right _ _ hPU') hperm
  have hPd'B : Pd' ≤ projUpperTriangular 3 F := (NQTerm.le_permProd_left _ _ hPU').trans hle
  set r := planeElem ζ hζ.pow_eq_one (regVec p) with hr
  have hrB : proj 3 F (X⁻¹ * r * X) ∈ projUpperTriangular 3 F := by
    apply hPd'B
    refine ⟨proj 3 F r, ⟨r, planeElem_mem _ _ _, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, hc, MulAut.conj_apply, inv_inv, ← map_inv, ← map_mul,
      ← map_mul]
  obtain ⟨b, hb, hbr⟩ := hrB
  have hz : b⁻¹ * (X⁻¹ * r * X) ∈ scalars 3 F := proj_eq_proj_iff.mp hbr
  obtain ⟨z, -, hzM⟩ := hz
  have hT : ((X : Matrix (Fin 3) (Fin 3) F)⁻¹ * diagPow ζ (regVec p : Fin 3 → ZMod p) *
      X).IsUpperTriangular := by
    have hXinv : ((X⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (X : Matrix (Fin 3) (Fin 3) F)⁻¹ := by
      symm
      apply Matrix.inv_eq_left_inv
      change ((X⁻¹ * X : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
      rw [inv_mul_cancel]
      rfl
    have h1 : (X : Matrix (Fin 3) (Fin 3) F)⁻¹ * diagPow ζ (regVec p : Fin 3 → ZMod p) * X =
        (b : Matrix (Fin 3) (Fin 3) F) * scalar (Fin 3) (z : F) := by
      rw [← hzM, ← hXinv]
      change ((X⁻¹ * r * X : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((b * (b⁻¹ * (X⁻¹ * r * X)) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      rw [mul_inv_cancel_left]
    rw [h1]
    intro i j hji
    rw [scalar_apply, mul_diagonal]
    rw [hb i j hji, zero_mul]
  obtain ⟨u, huU, wN, hN⟩ := exists_unitriangular_monomial hp5 hζ hT
  refine ⟨X * u, wN, hN, ?_⟩
  rw [hU, map_mul]
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨proj 3 F u⁻¹ * v * (proj 3 F u⁻¹)⁻¹, ?_, ?_⟩
    · obtain ⟨v', hv', rfl⟩ := hv
      refine ⟨u⁻¹ * v' * u⁻¹⁻¹, conj_mem_unitriangular (unitriangular_le_upperTriangular 3 F
        (inv_mem huU)) hv', ?_⟩
      simp only [map_mul, map_inv]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_inv]
      group
  · rintro ⟨v, hv, rfl⟩
    refine ⟨proj 3 F u * v * (proj 3 F u)⁻¹, ?_, ?_⟩
    · obtain ⟨v', hv', rfl⟩ := hv
      refine ⟨u * v' * u⁻¹, conj_mem_unitriangular (unitriangular_le_upperTriangular 3 F huU)
        hv', ?_⟩
      simp only [map_mul, map_inv]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem isMonomial_map {M : Matrix (Fin 3) (Fin 3) F} {w : Equiv.Perm (Fin 3)}
    (hM : IsMonomial M w) (σ : F ≃+* F) : IsMonomial (M.map σ) w := by
  obtain ⟨c, hc⟩ := hM
  refine ⟨fun j => Units.map σ.toRingHom.toMonoidHom (c j), fun j => ?_⟩
  ext i
  have h1 := monomial_apply hc i j
  rw [mulVec_single_one, col_apply, Matrix.map_apply, h1, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul]
  split_ifs <;> simp

theorem exists_monomial_of_normalizes_diagPlane [Finite F] {p : ℕ} [Fact p.Prime] [NeZero p]
    (hp5 : 5 ≤ p) {ζ : F} (hζ : IsPrimitiveRoot ζ p) (A : GL (Fin 3) F) (σ : F ≃+* F) {e : ℕ}
    (he : ∀ x, σ x = x ^ e)
    (hP : ((diagPlane p ζ hζ.pow_eq_one).map (proj 3 F)).map
        (conjAut 3 F A * fieldAut 3 F σ).toMonoidHom =
      (diagPlane p ζ hζ.pow_eq_one).map (proj 3 F)) :
    ∃ (w : Equiv.Perm (Fin 3)) (t : Fin 3 → F), (∀ m, t m ≠ 0) ∧
      ∀ m, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single m 1 = t m • Pi.single (w m) 1 := by
  classical
  have hp3 : 3 ≤ p := by omega
  set Pd := (diagPlane p ζ hζ.pow_eq_one).map (proj 3 F) with hPd
  set α := conjAut 3 F A * fieldAut 3 F σ with hα
  have hαinv : ∀ y ∈ Pd, α⁻¹ y ∈ Pd := by
    intro y hy
    rw [← hP] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    rw [MulEquiv.coe_toMonoidHom, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    exact hy'
  have hfP : ∀ y ∈ Pd, fieldAut 3 F σ y ∈ Pd := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨v, rfl⟩ := mem_diagPlane.1 hd
    rw [fieldAut_proj_planeElem hζ.pow_eq_one σ he]
    exact ⟨_, planeElem_mem _ _ _, rfl⟩
  set r := planeElem ζ hζ.pow_eq_one (regVec p) with hr
  have hcinv : conjAut 3 F A⁻¹ (proj 3 F r) ∈ Pd := by
    have h1 : conjAut 3 F A⁻¹ = fieldAut 3 F σ * α⁻¹ := by
      rw [map_inv, hα, _root_.mul_inv_rev, mul_inv_cancel_left]
    rw [h1, MulAut.mul_apply]
    exact hfP _ (hαinv _ ⟨r, planeElem_mem _ _ _, rfl⟩)
  rw [conjAut_proj] at hcinv
  obtain ⟨d, hd, hdr⟩ := hcinv
  obtain ⟨v, rfl⟩ := mem_diagPlane.1 hd
  obtain ⟨z, -, hz⟩ := proj_eq_proj_iff.mp hdr
  have hdiag : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      diagPow ζ (regVec p : Fin 3 → ZMod p) * (A : Matrix (Fin 3) (Fin 3) F) =
        diagonal fun k => ζ ^ ((v : Fin 3 → ZMod p) k).val * (z : F) := by
    have h2 : ((slConjugation 3 F A⁻¹ r : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = (planeElem ζ hζ.pow_eq_one v : Matrix (Fin 3) (Fin 3) F) *
          scalar (Fin 3) (z : F) := by
      rw [← hz]
      change _ = ((planeElem ζ hζ.pow_eq_one v * ((planeElem ζ hζ.pow_eq_one v)⁻¹ *
        slConjugation 3 F A⁻¹ r) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      rw [mul_inv_cancel_left]
    rw [coe_slConjugation, inv_inv, hr, coe_planeElem] at h2
    rw [h2, scalar_apply, coe_planeElem, diagPow, diagonal_mul_diagonal]
  have hN'N : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hNN' : (A : Matrix (Fin 3) (Fin 3) F) *
      ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact exists_perm_of_conj_diagonal hp3 hζ hN'N hNN' _ hdiag

theorem pow_three_of_ne_one_of_mul_self_ne_one : ∀ w : Equiv.Perm (Fin 3), w ≠ 1 →
    w * w ≠ 1 → w ^ 3 = 1 := by
  decide

theorem false_of_oddOrder_diagPlane [Finite F] [CharP F 2] {p : ℕ} [Fact p.Prime] [NeZero p]
    (hp5 : 5 ≤ p) {ζ : F} (hζ : IsPrimitiveRoot ζ p) (U : Sylow 2 (projectiveSL 3 F))
    (hPU : (((diagPlane p ζ hζ.pow_eq_one).map (proj 3 F) : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)) * (U : Set (projectiveSL 3 F)) =
      (U : Set (projectiveSL 3 F)) * ((diagPlane p ζ hζ.pow_eq_one).map (proj 3 F) :
        Subgroup (projectiveSL 3 F)))
    {A₀ : Subgroup (projectiveSL 3 F)} (hUA : (U : Subgroup (projectiveSL 3 F)) ≤ A₀)
    (hA₀ : A₀ ≠ ⊤) {α : MulAut (projectiveSL 3 F)} {n : ℕ} (hn : Odd n) (hαn : α ^ n = 1)
    (hαP : ((diagPlane p ζ hζ.pow_eq_one).map (proj 3 F)).map α.toMonoidHom =
      (diagPlane p ζ hζ.pow_eq_one).map (proj 3 F))
    (hαA : ∀ x ∈ A₀, α x ∈ A₀)
    (hnp : ¬ ∃ m : ℕ, ∀ v : sumZeroPlane p, α (proj 3 F (planeElem ζ hζ.pow_eq_one v)) =
      proj 3 F (planeElem ζ hζ.pow_eq_one v) ^ m) : False := by
  classical
  obtain ⟨N, wN, hN, hUN⟩ := exists_monomial_sylow_of_permutable hp5 hζ U hPU
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨-, -, -, -, -, -, -, hidx, -⟩ := standard_outer_quotients (n := 3) (K := F)
  have hidx' : (semilinearAutGroup 3 F).index ≤ 2 := by
    have h2 : (semilinearAutGroup 3 F).relIndex (standardAutGroup 3 F) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  have hαE : α ∈ semilinearAutGroup 3 F := by
    obtain ⟨j, hj⟩ := id hn
    by_cases h1 : (semilinearAutGroup 3 F).index = 1
    · rw [Subgroup.index_eq_one.mp h1]
      exact Subgroup.mem_top α
    have h2 : (semilinearAutGroup 3 F).index = 2 := by
      have h0 : (semilinearAutGroup 3 F).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    have hsq : α * α ∈ semilinearAutGroup 3 F := Subgroup.mul_self_mem_of_index_two h2 α
    have h3 : α ^ (2 * j) * α ∈ semilinearAutGroup 3 F := by
      rw [← pow_succ, ← hj, hαn]
      exact one_mem _
    rw [pow_mul, sq] at h3
    exact (Subgroup.mul_mem_cancel_left _ (pow_mem hsq j)).mp h3
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp hαE
  obtain ⟨i, hi⟩ := Sp4.exists_ringEquiv_eq_pow σ
  obtain ⟨w, t, ht0, hA⟩ := exists_monomial_of_normalizes_diagPlane hp5 hζ A σ hi hαP
  have hact : ∀ v : sumZeroPlane p, (conjAut 3 F A * fieldAut 3 F σ)
      (proj 3 F (planeElem ζ hζ.pow_eq_one v)) =
      proj 3 F (planeElem ζ hζ.pow_eq_one (((2 ^ i : ℕ) : ZMod p) • permPlane w.symm v)) := by
    intro v
    rw [MulAut.mul_apply, fieldAut_proj_planeElem hζ.pow_eq_one σ hi,
      conjAut_proj_planeElem_of_monomial hζ.pow_eq_one ht0 hA, map_smul]
  have hpow : ∀ (m : ℕ) (v : sumZeroPlane p), proj 3 F (planeElem ζ hζ.pow_eq_one
      ((m : ZMod p) • v)) = proj 3 F (planeElem ζ hζ.pow_eq_one v) ^ m := fun m v => by
    rw [planeElem_smul, map_pow]
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hnp
    refine ⟨2 ^ i, fun v => ?_⟩
    have hv : permPlane (Equiv.symm (1 : Equiv.Perm (Fin 3))) v = v := Subtype.ext rfl
    rw [hact, hv]
    exact hpow _ v
  have hw2 : w * w ≠ 1 := by
    intro hww
    apply hnp
    obtain ⟨j, hj⟩ := id hn
    have hsq : ∀ v : sumZeroPlane p, ((conjAut 3 F A * fieldAut 3 F σ) ^ 2)
        (proj 3 F (planeElem ζ hζ.pow_eq_one v)) =
          proj 3 F (planeElem ζ hζ.pow_eq_one v) ^ (2 ^ i * 2 ^ i) := by
      intro v
      rw [sq, MulAut.mul_apply, hact, hact, map_smul, smul_smul]
      have hperm : permPlane w.symm (permPlane w.symm v) = v := by
        apply Subtype.ext
        funext k
        have hinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
        change (v : Fin 3 → ZMod p) (w⁻¹ (w⁻¹ k)) = (v : Fin 3 → ZMod p) k
        rw [hinv, ← Equiv.Perm.mul_apply, hww, Equiv.Perm.one_apply]
      rw [hperm, ← Nat.cast_mul, hpow]
    have hpowk : ∀ (k : ℕ) (v : sumZeroPlane p), (((conjAut 3 F A * fieldAut 3 F σ) ^ 2) ^ k)
        (proj 3 F (planeElem ζ hζ.pow_eq_one v)) =
          proj 3 F (planeElem ζ hζ.pow_eq_one v) ^ ((2 ^ i * 2 ^ i) ^ k) := by
      intro k
      induction k with
      | zero => intro v; simp
      | succ k ih =>
        intro v
        rw [pow_succ, MulAut.mul_apply, hsq, map_pow, ih, ← pow_mul, pow_succ, mul_comm]
    refine ⟨(2 ^ i * 2 ^ i) ^ (j + 1), fun v => ?_⟩
    have h1 : conjAut 3 F A * fieldAut 3 F σ =
        ((conjAut 3 F A * fieldAut 3 F σ) ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = n + 1 by omega, pow_succ, hαn, one_mul]
    rw [h1, hpowk]
  have hw3 : w ^ 3 = 1 := pow_three_of_ne_one_of_mul_self_ne_one w hw1 hw2
  apply hA₀
  set c : MulAut (projectiveSL 3 F) := MulAut.conj (proj 3 F N)⁻¹ with hc
  set Y := (A₀.map c.toMonoidHom).comap (proj 3 F) with hY
  have hcproj : ∀ g : SpecialLinearGroup (Fin 3) F, c (proj 3 F g) = proj 3 F (N⁻¹ * g * N) := by
    intro g
    rw [hc, MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv]
  have hUY : unitriangular 3 F ≤ Y := by
    intro u hu
    refine ⟨proj 3 F (N * u * N⁻¹), hUA ?_, ?_⟩
    · rw [hUN]
      refine ⟨proj 3 F u, ⟨u, hu, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv]
    · rw [MulEquiv.coe_toMonoidHom, hcproj]
      congr 1
      group
  set σN : SpecialLinearGroup (Fin 3) F := SpecialLinearGroup.map σ.toRingHom N with hσN
  set M : GL (Fin 3) F := SpecialLinearGroup.toGL N⁻¹ * A * SpecialLinearGroup.toGL σN with hM
  have hMmon : IsMonomial (M : Matrix (Fin 3) (Fin 3) F) (wN⁻¹ * w * wN) := by
    have h1 := IsMonomial.inv hN
    have h2 : IsMonomial (A : Matrix (Fin 3) (Fin 3) F) w :=
      ⟨fun m => Units.mk0 (t m) (ht0 m), fun m => by rw [Units.val_mk0]; exact hA m⟩
    have h3 : IsMonomial (σN : Matrix (Fin 3) (Fin 3) F) wN := by
      rw [hσN, Matrix.SpecialLinearGroup.map_apply_coe]
      exact isMonomial_map hN σ
    exact (h1.mul h2).mul h3
  have hM3 : (wN⁻¹ * w * wN) ^ 3 = 1 := by
    have h1 : wN⁻¹ * w * wN = (MulAut.conj wN⁻¹) w := by
      rw [MulAut.conj_apply, inv_inv]
    rw [h1, ← map_pow, hw3, map_one]
  have hM1 : wN⁻¹ * w * wN ≠ 1 := by
    intro h1
    apply hw1
    have h2 : w = wN * (wN⁻¹ * w * wN) * wN⁻¹ := by group
    rw [h2, h1, mul_one, mul_inv_cancel]
  have hMY : ∀ u ∈ unitriangular 3 F, slConjugation 3 F M u ∈ Y := by
    intro u hu
    set u' := SpecialLinearGroup.map σ.symm.toRingHom u with hu'def
    have hu'U : u' ∈ unitriangular 3 F := by
      refine ⟨fun i j hji => ?_, fun i => ?_⟩
      · rw [hu'def, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
          Matrix.map_apply, hu.1 i j hji, map_zero]
      · rw [hu'def, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
          Matrix.map_apply, hu.2 i, map_one]
    have hσu' : SpecialLinearGroup.map σ.toRingHom u' = u := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rw [hu'def, Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe,
        RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply]
      exact σ.apply_symm_apply _
    have hmem : proj 3 F (N * u' * N⁻¹) ∈ A₀ := by
      apply hUA
      rw [hUN]
      refine ⟨proj 3 F u', ⟨u', hu'U, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv]
    have hmap : SpecialLinearGroup.map σ.toRingHom (N * u' * N⁻¹) = σN * u * σN⁻¹ := by
      rw [map_mul, map_mul, map_inv, hσu']
    have hMinv : M⁻¹ = SpecialLinearGroup.toGL σN⁻¹ * A⁻¹ * SpecialLinearGroup.toGL N := by
      rw [hM]
      simp only [map_inv]
      group
    refine ⟨_, hαA _ hmem, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, fieldAut_proj, hmap, conjAut_proj, hcproj]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_slConjugation,
      coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      hMinv, hM]
    simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.mul_assoc]
  have hYtop := eq_top_of_unitriangular_le_of_monomialGL hUY hMmon hM1 hM3 hMY
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  have hg : N⁻¹ * g * N ∈ Y := hYtop ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyc⟩ := hg
  rw [MulEquiv.coe_toMonoidHom, ← hcproj] at hyc
  rw [← c.injective hyc]
  exact hy

theorem oddOrder_acts_by_pow {C : Type*} [Group C] [Finite C] [Finite F] [CharP F 2]
    (ψ : C ≃* projectiveSL 3 F) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {P₀ U₀ A₀ : Subgroup C}
    (hU₀ : ∃ U : Sylow 2 C, (U : Subgroup C) = U₀) (hPexp : ∀ y ∈ P₀, y ^ p = 1)
    (hPnc : ¬ IsCyclic P₀) (hPU : (P₀ : Set C) * U₀ = U₀ * P₀) (hUA : U₀ ≤ A₀) (hA₀ : A₀ ≠ ⊤)
    {γ : MulAut C} {r : ℕ} (hr : Odd r) (hγr : γ ^ r = 1) (hγP : P₀.map γ.toMonoidHom = P₀)
    (hγA : ∀ y ∈ A₀, γ y ∈ A₀) :
    ∃ m : ℕ, ∀ y ∈ P₀, γ y = y ^ m := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hpF : ringChar F ≠ p := by
    rw [ringChar.eq F 2]
    omega
  obtain ⟨U, hU⟩ := hU₀
  set Pst := P₀.map ψ.toMonoidHom with hPst
  have hPstexp : ∀ x ∈ Pst, x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hPexp y hy, map_one]
  have hPstnc : ¬ IsCyclic Pst := fun hc =>
    hPnc (isCyclic_of_surjective (P₀.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm.toMonoidHom
      (MulEquiv.surjective _))
  obtain ⟨-, -, -, ζ, hζ, g, hg, -⟩ :=
    noncyclic_exponent_prime_projective_linear_three_subgroups_have_reducible_two_normalizers
      hp5 hpF Pst hPstnc hPstexp
  set φ : C ≃* projectiveSL 3 F := ψ.trans (conjAut 3 F g) with hφ
  set Pd := (diagPlane p ζ hζ.pow_eq_one).map (proj 3 F) with hPd
  have hφP : P₀.map φ.toMonoidHom = Pd := by
    rw [← hg, hPst, Subgroup.map_map]
    rfl
  have hφs : Function.Surjective φ.toMonoidHom := φ.surjective
  set U' : Sylow 2 (projectiveSL 3 F) := U.mapSurjective hφs with hU'def
  have hU' : (U' : Subgroup (projectiveSL 3 F)) = U₀.map φ.toMonoidHom := by
    rw [hU'def, Sylow.coe_mapSurjective, hU]
  have hPU' : (Pd : Set (projectiveSL 3 F)) *
        ((U' : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) =
      ((U' : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) *
        (Pd : Set (projectiveSL 3 F)) := by
    rw [hU', ← hφP, Subgroup.coe_map φ.toMonoidHom P₀, Subgroup.coe_map φ.toMonoidHom U₀,
      ← Set.image_mul, hPU, Set.image_mul]
  set A₀' := A₀.map φ.toMonoidHom with hA₀'
  have hUA' : (U' : Subgroup (projectiveSL 3 F)) ≤ A₀' := by
    rw [hU']
    exact Subgroup.map_mono hUA
  have hA₀'top : A₀' ≠ ⊤ := by
    intro htop
    apply hA₀
    rw [eq_top_iff]
    intro x _
    have hx : φ x ∈ A₀' := htop ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← φ.injective hyx]
    exact hy
  set α : MulAut (projectiveSL 3 F) := MulAut.congr φ γ with hαdef
  have hαapp : ∀ y : C, α (φ y) = φ (γ y) := fun y => by
    rw [hαdef]
    simp [MulAut.congr_apply]
  have hαr : α ^ r = 1 := by rw [hαdef, ← map_pow, hγr, map_one]
  have hαP : Pd.map α.toMonoidHom = Pd := by
    rw [← hφP, Subgroup.map_map]
    conv_rhs => rw [← hγP, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext fun y => hαapp y
  have hαA : ∀ x ∈ A₀', α x ∈ A₀' := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨γ y, hγA y hy, (hαapp y).symm⟩
  have hex : ∃ m : ℕ, ∀ v : sumZeroPlane p, α (proj 3 F (planeElem ζ hζ.pow_eq_one v)) =
      proj 3 F (planeElem ζ hζ.pow_eq_one v) ^ m := by
    by_contra hnp
    exact false_of_oddOrder_diagPlane hp5 hζ U' hPU' hUA' hA₀'top hr hαr hαP hαA hnp
  obtain ⟨m, hm⟩ := hex
  refine ⟨m, fun y hy => φ.injective ?_⟩
  have hφy : φ y ∈ Pd := by
    rw [← hφP]
    exact ⟨y, hy, rfl⟩
  obtain ⟨d, hd, hdy⟩ := hφy
  obtain ⟨v, rfl⟩ := mem_diagPlane.1 hd
  rw [← hαapp, map_pow, ← hdy]
  exact hm v

end CFSG.Quasithin.H13.PSL3
