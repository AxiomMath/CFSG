module

public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeTools
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.RankThree.PartTwo.Sec4.Item413AutL3

public section

namespace CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification

theorem exists_eq_pow_three_of_map_eq {G : Type*} [CommGroup G] [IsCyclic G] (φ : G →* G)
    {c : G} (hc : orderOf c = 3) (hφ : φ c = c) (x : G) : ∃ y : G, x⁻¹ * φ x = y ^ 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg (φ g))
  have hpow : ∀ w : G, φ w = w ^ m := by
    intro w
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg w)
    rw [map_zpow, ← hm, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  have h1 : c ^ (m - 1) = 1 := by
    rw [_root_.zpow_sub_one, ← hpow, hφ, mul_inv_cancel]
  obtain ⟨t, ht⟩ := orderOf_dvd_iff_zpow_eq_one.mpr h1
  refine ⟨x ^ t, ?_⟩
  rw [hpow, ← _root_.zpow_neg_one, ← _root_.zpow_add, ← zpow_natCast, ← _root_.zpow_mul]
  congr 1
  rw [hc] at ht
  push_cast at ht ⊢
  linarith

theorem commutator_mem_of_parts {G : Type*} [Group G] {I : Subgroup G} [I.Normal]
    {d e r s : G} (hrs : r * s = s * r) (hde : d * e * d⁻¹ * e⁻¹ ∈ I)
    (hre : r * e * r⁻¹ * e⁻¹ ∈ I) (hsd : s * d * s⁻¹ * d⁻¹ ∈ I) :
    d * r * (e * s) * (d * r)⁻¹ * (e * s)⁻¹ ∈ I := by
  have key : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ I ↔ Commute (a : G ⧸ I) (b : G ⧸ I) := by
    intro a b
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← commutatorElement_def,
      commutatorElement_eq_one_iff_mul_comm]
    rfl
  rw [key] at hde hre hsd ⊢
  have hrs' : Commute (r : G ⧸ I) (s : G ⧸ I) := by
    change (r : G ⧸ I) * s = s * r
    rw [← QuotientGroup.mk_mul, hrs, QuotientGroup.mk_mul]
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
  exact Commute.mul_left (Commute.mul_right hde hsd.symm) (Commute.mul_right hre hrs')

variable {K : Type} [Field K]

@[expose] noncomputable def stdAut3 (A : GL (Fin 3) K) (ρ : K ≃+* K) (ε : ℕ) :
    MulAut (SpecialLinearGroup (Fin 3) K) :=
  CatalogueBHigherLinearAction.slConjugation 3 K A *
    CatalogueBHigherLinearField.slFieldAut (Fin 3) K ρ * CatalogueBGraphForm.slGraphAut 3 K ^ ε

theorem descendAut_stdAut3 (A : GL (Fin 3) K) (ρ : K ≃+* K) (ε : ℕ) :
    descendAut 3 K (stdAut3 A ρ ε) = conjAut 3 K A * fieldAut 3 K ρ * dualAut 3 K ^ ε := by
  simp only [stdAut3, map_mul, map_pow]
  rfl

theorem exists_std_form [Finite K] (σ : MulAut (SpecialLinearGroup (Fin 3) K)) :
    ∃ (A : GL (Fin 3) K) (ρ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧ σ = stdAut3 A ρ ε := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  obtain ⟨A, ρ, ε, hε, hσ⟩ := hform (descendAut 3 K σ)
  exact ⟨A, ρ, ε, hε, CFSG.RankThree.PartTwo.Sec4.descendAut_three_injective
    (by rw [hσ, descendAut_stdAut3])⟩

theorem coe_stdAut3 (A : GL (Fin 3) K) (ρ : K ≃+* K) (ε : ℕ) (g : SpecialLinearGroup (Fin 3) K) :
    ((stdAut3 A ρ ε g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) *
        ((((CatalogueBGraphForm.slGraphAut 3 K ^ ε) g : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K).map ρ) * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [stdAut3, MulAut.mul_apply, MulAut.mul_apply,
    CatalogueBHigherLinearAction.slConjugation_matrix]
  rfl

theorem coe_inv_of_coe_eq_scalar {n : ℕ} {z : SpecialLinearGroup (Fin n) K} {c : Kˣ}
    (hz : (z : Matrix (Fin n) (Fin n) K) = scalar (Fin n) (c : K)) :
    ((z⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      scalar (Fin n) ((c⁻¹ : Kˣ) : K) := by
  have h1 : (z : Matrix (Fin n) (Fin n) K) * ((z⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := by
    have h := congrArg (fun w : SpecialLinearGroup (Fin n) K => (w : Matrix (Fin n) (Fin n) K))
      (mul_inv_cancel z)
    exact h
  calc ((z⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = scalar (Fin n) ((c⁻¹ : Kˣ) : K) * (scalar (Fin n) (c : K) *
          ((z⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        rw [← Matrix.mul_assoc, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          map_one, Matrix.one_mul]
    _ = scalar (Fin n) ((c⁻¹ : Kˣ) : K) := by rw [← hz, h1, Matrix.mul_one]

theorem conj_scalar_eq {n : ℕ} (A : GL (Fin n) K) (a : K) :
    (A : Matrix (Fin n) (Fin n) K) * scalar (Fin n) a *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = scalar (Fin n) a := by
  rw [← (Matrix.scalar_commute a (fun r => Commute.all a r) _).eq, Matrix.mul_assoc,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem map_scalar_eq {n : ℕ} (ρ : K ≃+* K) (a : K) :
    (scalar (Fin n) a).map ρ = scalar (Fin n) (ρ a) := by
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero ρ)]

theorem conjAut_mem_range_conj_of_det {C : GL (Fin 3) K} {y : Kˣ}
    (hC : GeneralLinearGroup.det C = y ^ 3) :
    conjAut 3 K C ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  have hdet : ((GeneralLinearGroup.scalar (Fin 3) y⁻¹ * C : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, map_mul, hC, ← Units.val_one]
    congr 1
    rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, inv_mul_cancel]
  obtain ⟨g, hg⟩ : ∃ g : SpecialLinearGroup (Fin 3) K,
      SpecialLinearGroup.toGL g = GeneralLinearGroup.scalar (Fin 3) y⁻¹ * C :=
    ⟨⟨_, hdet⟩, Units.ext rfl⟩
  refine ⟨proj 3 K g, ?_⟩
  rw [conj_proj_eq_conjAut, hg, map_mul, conjAut_scalar, one_mul]

theorem conjAut_commutator_mem (A B : GL (Fin 3) K) :
    conjAut 3 K A * conjAut 3 K B * (conjAut 3 K A)⁻¹ * (conjAut 3 K B)⁻¹ ∈
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  refine conjAut_mem_range_conj_of_det (y := 1) ?_
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, one_pow, ← commutatorElement_def,
    commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem fieldAut_dualAut_commutator_mem [Finite K] (ρ : K ≃+* K) (ε : ℕ) (hε : ε ≤ 1)
    {c : Kˣ} (hc : orderOf c = 3)
    (hfix : (Units.map (ρ : K →* K)) (c ^ ((-1 : ℤ) ^ ε)) = c) (B : GL (Fin 3) K) :
    fieldAut 3 K ρ * dualAut 3 K ^ ε * conjAut 3 K B * (fieldAut 3 K ρ * dualAut 3 K ^ ε)⁻¹ *
        (conjAut 3 K B)⁻¹ ∈
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  obtain ⟨-, -, hfc, hδδ, hδc, -, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  have hδinv : (dualAut 3 K)⁻¹ = dualAut 3 K := inv_eq_of_mul_eq_one_right hδδ
  set φ : Kˣ →* Kˣ := (Units.map (ρ : K →* K)).comp (zpowGroupHom ((-1 : ℤ) ^ ε)) with hφ
  have hφc : φ c = c := hfix
  obtain ⟨B', hB', hdet⟩ : ∃ B' : GL (Fin 3) K,
      fieldAut 3 K ρ * dualAut 3 K ^ ε * conjAut 3 K B * (fieldAut 3 K ρ * dualAut 3 K ^ ε)⁻¹ =
        conjAut 3 K B' ∧ GeneralLinearGroup.det B' = φ (GeneralLinearGroup.det B) := by
    rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
    · refine ⟨GeneralLinearGroup.map (ρ : K →+* K) B, ?_, ?_⟩
      · rw [pow_zero, mul_one]
        exact hfc ρ B
      · rw [GeneralLinearGroup.map_det, hφ, MonoidHom.comp_apply, pow_zero, zpowGroupHom_apply,
          zpow_one]
        rfl
    · refine ⟨GeneralLinearGroup.map (ρ : K →+* K) (GeneralLinearGroup.inverseTranspose B), ?_, ?_⟩
      · rw [pow_one, _root_.mul_inv_rev, hδinv]
        calc fieldAut 3 K ρ * dualAut 3 K * conjAut 3 K B * (dualAut 3 K * (fieldAut 3 K ρ)⁻¹)
            = fieldAut 3 K ρ * (dualAut 3 K * conjAut 3 K B * dualAut 3 K) *
                (fieldAut 3 K ρ)⁻¹ := by group
          _ = _ := by rw [hδc B, hfc ρ]
      · rw [GeneralLinearGroup.map_det, hφ, MonoidHom.comp_apply, pow_one, zpowGroupHom_apply,
          _root_.zpow_neg_one]
        congr 1
        apply Units.ext
        rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_inverseTranspose,
          Matrix.det_transpose, ← GeneralLinearGroup.val_det_apply, map_inv]
  rw [hB', ← map_inv, ← map_mul]
  obtain ⟨y, hy⟩ := exists_eq_pow_three_of_map_eq φ hc hφc (GeneralLinearGroup.det B)
  refine conjAut_mem_range_conj_of_det (y := y) ?_
  rw [map_mul, map_inv, hdet, mul_comm, hy]

theorem exists_descend_eq_of_fix [Finite K] {z : SpecialLinearGroup (Fin 3) K} {c : Kˣ}
    (hc : orderOf c = 3) (hzc : (z : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) (c : K))
    (σ : MulAut (SpecialLinearGroup (Fin 3) K)) (hσ : σ z = z) :
    ∃ (A : GL (Fin 3) K) (ρ : K ≃+* K) (ε : ℕ),
      descendAut 3 K σ = conjAut 3 K A * (fieldAut 3 K ρ * dualAut 3 K ^ ε) ∧
      ∀ B : GL (Fin 3) K, fieldAut 3 K ρ * dualAut 3 K ^ ε * conjAut 3 K B *
        (fieldAut 3 K ρ * dualAut 3 K ^ ε)⁻¹ * (conjAut 3 K B)⁻¹ ∈
        (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  obtain ⟨A, ρ, ε, hε, rfl⟩ := exists_std_form σ
  refine ⟨A, ρ, ε, by rw [descendAut_stdAut3, mul_assoc], ?_⟩
  have hfix : (Units.map (ρ : K →* K)) (c ^ ((-1 : ℤ) ^ ε)) = c := by
    have hm := congrArg (fun g : SpecialLinearGroup (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K) 0 0) hσ
    rw [coe_stdAut3] at hm
    have hgraph : ((((CatalogueBGraphForm.slGraphAut 3 K ^ ε) z : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) = scalar (Fin 3) ((c ^ ((-1 : ℤ) ^ ε) : Kˣ) : K) := by
      rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
      · rw [pow_zero, MulAut.one_apply, hzc, pow_zero, zpow_one]
      · rw [pow_one, CatalogueBGraphForm.slGraphAut_matrix, coe_inv_of_coe_eq_scalar hzc,
          pow_one, _root_.zpow_neg_one, Matrix.scalar_apply, Matrix.diagonal_transpose]
    rw [hgraph, map_scalar_eq, conj_scalar_eq, hzc] at hm
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at hm
    exact Units.ext hm
  exact fieldAut_dualAut_commutator_mem ρ ε hε hc hfix

theorem fixCommInner_specialLinear [Finite K] {z : SpecialLinearGroup (Fin 3) K}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) (hz3 : orderOf z = 3) :
    FixCommInner (SpecialLinearGroup (Fin 3) K) z := by
  rw [← scalars_eq_center] at hz
  obtain ⟨c, hc3, hzc⟩ := hz
  have hc : orderOf c = 3 := by
    refine orderOf_eq_prime hc3 fun h1 => ?_
    have hz1 : z = 1 := by
      ext i j
      rw [hzc, h1]
      simp
    rw [hz1, orderOf_one] at hz3
    norm_num at hz3
  intro σ τ hσ hτ
  have : (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  obtain ⟨A, ρ, ε, hα, hr⟩ := exists_descend_eq_of_fix hc hzc σ hσ
  obtain ⟨B, ρ', ε', hβ, hs⟩ := exists_descend_eq_of_fix hc hzc τ hτ
  have hrs : fieldAut 3 K ρ * dualAut 3 K ^ ε * (fieldAut 3 K ρ' * dualAut 3 K ^ ε') =
      fieldAut 3 K ρ' * dualAut 3 K ^ ε' * (fieldAut 3 K ρ * dualAut 3 K ^ ε) :=
    (standardFieldGraph_commute
      (mul_mem (fieldAut_mem_standardFieldGraph ρ) (pow_mem dualAut_mem_standardFieldGraph ε))
      (mul_mem (fieldAut_mem_standardFieldGraph ρ')
        (pow_mem dualAut_mem_standardFieldGraph ε'))).eq
  have hmem := commutator_mem_of_parts hrs (conjAut_commutator_mem A B) (hr B) (hs A)
  rw [← hα, ← hβ, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at hmem
  obtain ⟨x, hx⟩ := hmem
  obtain ⟨g, rfl⟩ := proj_surjective 3 K x
  refine ⟨g, CFSG.RankThree.PartTwo.Sec4.descendAut_three_injective ?_⟩
  rw [← hx]
  ext y
  obtain ⟨w, rfl⟩ := proj_surjective 3 K y
  rw [descendAut_proj, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

end CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree
