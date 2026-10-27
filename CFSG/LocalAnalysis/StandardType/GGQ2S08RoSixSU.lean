module

public import CFSG.RankThree.PartOne.KF.R9Perm
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelMono
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KF.UnitaryModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.RankThree.Classical (permGL)
open CFSG.RankThree.Classical2 (diagHom_unitary permGL_mul_diagHom_mul_inv)
open CFSG.RankThree.PartOne.KFU (permGL_mem_unitarySU)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {F : Type} [Field F] [Finite F]

private theorem ggQ2s08r6_pow_three_eq_one (hF : Nat.card F = 4) (c : Fˣ) : c ^ 3 = 1 := by
  have hcard : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have h := pow_card_eq_one' (G := Fˣ) (x := c)
  rwa [hcard] at h

private theorem ggQ2s08r6_det_diagHom_units {n : ℕ} (d : Fin n → Fˣ) :
    Matrix.GeneralLinearGroup.det (diagHom n d) = ∏ i, d i := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod, det_diagHom]

private theorem ggQ2s08r6_exists_omega (hF : Nat.card F = 4) :
    ∃ ω : Fˣ, ω ≠ 1 ∧ ω ^ 3 = 1 ∧ ω ≠ ω⁻¹ := by
  have hcard : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  haveI : Nontrivial Fˣ :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨ω, hω1⟩ := exists_ne (1 : Fˣ)
  refine ⟨ω, hω1, ggQ2s08r6_pow_three_eq_one hF ω, ?_⟩
  intro he
  have h2 : ω ^ 2 = 1 := by
    rw [pow_two]
    calc ω * ω = ω⁻¹ * ω := congrArg (fun x : Fˣ => x * ω) he
      _ = 1 := inv_mul_cancel ω
  have h3 : ω ^ 3 = 1 := ggQ2s08r6_pow_three_eq_one hF ω
  have h1 : ω = 1 := by
    have h := (pow_gcd_eq_one (m := 3) (n := 2)).mpr ⟨h3, h2⟩
    have hg : Nat.gcd 3 2 = 1 := by norm_num
    rwa [hg, pow_one] at h
  exact hω1 h1

private theorem ggQ2s08r6_prod_eq_one_of_conj {A : GL (Fin 6) F} {t t' : Fin 6 → Fˣ}
    (hconj : A * diagHom 6 t * A⁻¹ = diagHom 6 t') (ht : ∏ i, t i = 1) :
    ∏ i, t' i = 1 := by
  have hdet := congrArg Matrix.GeneralLinearGroup.det hconj
  rw [map_mul, map_mul, map_inv] at hdet
  simp only [ggQ2s08r6_det_diagHom_units, ht] at hdet
  simpa using hdet.symm

theorem ggQ2s08r6_scalar_mem (hF : Nat.card F = 4) (c : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ LargeEvenSUGroup (Fin 6) F 2 := by
  have hK : Nat.card F = (2 ^ 1) ^ 2 := by rw [hF]; norm_num
  change Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ unitarySU 2 1 F 6
  refine (CFSG.LinearGroups.scalar_mem_statedSU_iff (K := F) (p := 2) (f := 1) Nat.prime_two
    hK (n := 6) (by norm_num) c).mpr ⟨?_, ?_⟩
  · rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, ggQ2s08r6_pow_three_eq_one hF c, one_pow]
  · rw [show 2 ^ 1 + 1 = 3 by norm_num, ggQ2s08r6_pow_three_eq_one hF c]

theorem ggQ2s08r6_exists_monomial (hF : Nat.card F = 4) {A : GL (Fin 6) F}
    (h : ∀ t : Fin 6 → Fˣ, ∏ i, t i = 1 →
      ∃ t' : Fin 6 → Fˣ, A * diagHom 6 t * A⁻¹ = diagHom 6 t') :
    ∃ (σ : Equiv.Perm (Fin 6)) (u : Fin 6 → Fˣ), A = permGL σ * diagHom 6 u := by
  classical
  obtain ⟨ω, -, -, hωne⟩ := ggQ2s08r6_exists_omega (F := F) hF
  let S := {t : Fin 6 → Fˣ // ∏ i, t i = 1}
  let φ : S → S := fun t =>
    ⟨Classical.choose (h t.1 t.2), ggQ2s08r6_prod_eq_one_of_conj
      (Classical.choose_spec (h t.1 t.2)) t.2⟩
  have hφinj : Function.Injective φ := by
    intro t₁ t₂ h12
    apply Subtype.ext
    have hspec₁ := Classical.choose_spec (h t₁.1 t₁.2)
    have hspec₂ := Classical.choose_spec (h t₂.1 t₂.2)
    have hval : (φ t₁).1 = (φ t₂).1 := congrArg Subtype.val h12
    have heq : A * diagHom 6 t₁.1 * A⁻¹ = A * diagHom 6 t₂.1 * A⁻¹ := by
      calc A * diagHom 6 t₁.1 * A⁻¹ = diagHom 6 (φ t₁).1 := hspec₁
        _ = diagHom 6 (φ t₂).1 := by rw [hval]
        _ = A * diagHom 6 t₂.1 * A⁻¹ := hspec₂.symm
    exact diagHom_injective 6 (mul_left_cancel (mul_right_cancel heq))
  have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφinj
  have hcol : ∀ (i l l' : Fin 6),
      (A : Matrix (Fin 6) (Fin 6) F) l i ≠ 0 →
      (A : Matrix (Fin 6) (Fin 6) F) l' i ≠ 0 → l = l' := by
    intro i l l' hl hl'
    by_contra hne
    let t' : Fin 6 → Fˣ := Pi.mulSingle l ω * Pi.mulSingle l' ω⁻¹
    have ht'prod : ∏ k, t' k = 1 := by
      simp only [t', Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
      exact mul_inv_cancel ω
    have ht'l : t' l = ω := by
      simp only [t', Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hne, mul_one]
    have ht'l' : t' l' = ω⁻¹ := by
      simp only [t', Pi.mul_apply, Pi.mulSingle_eq_of_ne (Ne.symm hne),
        Pi.mulSingle_eq_same, one_mul]
    obtain ⟨t, ht⟩ := hφsurj ⟨t', ht'prod⟩
    have hspec := Classical.choose_spec (h t.1 t.2)
    have hDt' : diagHom 6 (φ t).1 = diagHom 6 t' :=
      congrArg (diagHom 6) (congrArg Subtype.val ht)
    have hD : A * diagHom 6 t.1 * A⁻¹ = diagHom 6 t' := hspec.trans hDt'
    have heq : A * diagHom 6 t.1 = diagHom 6 t' * A := by
      calc A * diagHom 6 t.1 = (A * diagHom 6 t.1 * A⁻¹) * A := by group
        _ = diagHom 6 t' * A := by rw [hD]
    have hmat : (A : Matrix (Fin 6) (Fin 6) F) * Matrix.diagonal (fun k => (t.1 k : F)) =
        Matrix.diagonal (fun k => (t' k : F)) * (A : Matrix (Fin 6) (Fin 6) F) := by
      simpa only [Units.val_mul, coe_diagHom] using
        congrArg (fun g : GL (Fin 6) F => (g : Matrix (Fin 6) (Fin 6) F)) heq
    have hmat1 := congrFun (congrFun hmat l) i
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hmat1
    have hmat1' := congrFun (congrFun hmat l') i
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hmat1'
    have e1 : (t.1 i : F) = (t' l : F) :=
      mul_left_cancel₀ hl (hmat1.trans (mul_comm _ _))
    have e2 : (t.1 i : F) = (t' l' : F) :=
      mul_left_cancel₀ hl' (hmat1'.trans (mul_comm _ _))
    have hval : t' l = t' l' := Units.ext (e1.symm.trans e2)
    rw [ht'l, ht'l'] at hval
    exact hωne hval
  obtain ⟨π, hπ⟩ := LinModel.exists_isPermOf (m := 5) hcol
  refine ⟨π, fun i => Units.mk0 ((A : Matrix (Fin 6) (Fin 6) F) (π i) i)
    ((hπ i (π i)).mpr rfl), ?_⟩
  apply Units.ext
  ext l i
  rw [Units.val_mul, coe_diagHom, Matrix.mul_diagonal, TableBUE.permGL_apply]
  by_cases hli : l = π i
  · rw [if_pos (Equiv.Perm.inv_eq_iff_eq.mpr hli), one_mul, hli, Units.val_mk0]
  · rw [if_neg (fun h => hli (Equiv.Perm.inv_eq_iff_eq.mp h)), zero_mul]
    by_contra hne
    exact hli ((hπ i l).mp hne)

end CFSG.StandardType
