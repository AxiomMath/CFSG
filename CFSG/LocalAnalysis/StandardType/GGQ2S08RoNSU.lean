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

variable {F : Type} [Field F] [Finite F] {N : ℕ}

omit [Finite F] in
private theorem ggQ2s08rN_pow_three_eq_one (hF : Nat.card F = 4) (c : Fˣ) : c ^ 3 = 1 := by
  have hcard : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have h := pow_card_eq_one' (G := Fˣ) (x := c)
  rwa [hcard] at h

omit [Finite F] in
private theorem ggQ2s08rN_det_diagHom_units {n : ℕ} (d : Fin n → Fˣ) :
    Matrix.GeneralLinearGroup.det (diagHom n d) = ∏ i, d i := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod, det_diagHom]

omit [Finite F] in
private theorem ggQ2s08rN_diagHom_const (c : Fˣ) :
    diagHom N (fun _ => c) = Matrix.GeneralLinearGroup.scalar (Fin N) c := by
  apply Units.ext
  rw [coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

private theorem ggQ2s08rN_exists_omega (hF : Nat.card F = 4) :
    ∃ ω : Fˣ, ω ≠ 1 ∧ ω ^ 3 = 1 ∧ ω ≠ ω⁻¹ := by
  have hcard : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have : Nontrivial Fˣ :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨ω, hω1⟩ := exists_ne (1 : Fˣ)
  refine ⟨ω, hω1, ggQ2s08rN_pow_three_eq_one hF ω, ?_⟩
  intro he
  have h2 : ω ^ 2 = 1 := by
    rw [pow_two]
    calc ω * ω = ω⁻¹ * ω := congrArg (fun x : Fˣ => x * ω) he
      _ = 1 := inv_mul_cancel ω
  have h3 : ω ^ 3 = 1 := ggQ2s08rN_pow_three_eq_one hF ω
  have h1 : ω = 1 := by
    have h := (pow_gcd_eq_one (m := 3) (n := 2)).mpr ⟨h3, h2⟩
    have hg : Nat.gcd 3 2 = 1 := by norm_num
    rwa [hg, pow_one] at h
  exact hω1 h1

omit [Finite F] in
private theorem ggQ2s08rN_prod_eq_one_of_conj {A : GL (Fin N) F} {t t' : Fin N → Fˣ}
    (hconj : A * diagHom N t * A⁻¹ = diagHom N t') (ht : ∏ i, t i = 1) :
    ∏ i, t' i = 1 := by
  have hdet := congrArg Matrix.GeneralLinearGroup.det hconj
  rw [map_mul, map_mul, map_inv] at hdet
  simp only [ggQ2s08rN_det_diagHom_units, ht] at hdet
  simpa using hdet.symm

omit [Finite F] in
theorem ggQ2s08rN_permGL_mem (hF : Nat.card F = 4) (σ : Equiv.Perm (Fin N)) :
    (permGL σ : GL (Fin N) F) ∈ LargeEvenSUGroup (Fin N) F 2 := by
  have hK : Nat.card F = (2 ^ 1) ^ 2 := by rw [hF]; norm_num
  have hunit : UnitaryFieldData 2 1 F :=
    TableBU.unitaryFieldData_of_card hK (by norm_num)
  change (permGL σ : GL (Fin N) F) ∈ unitarySU 2 1 F N
  exact permGL_mem_unitarySU hunit σ

omit [Finite F] in
theorem ggQ2s08rN_diagHom_mem_iff (hF : Nat.card F = 4) (t : Fin N → Fˣ) :
    diagHom N t ∈ LargeEvenSUGroup (Fin N) F 2 ↔ ∏ i, t i = 1 := by
  have hK : Nat.card F = (2 ^ 1) ^ 2 := by rw [hF]; norm_num
  have hunit : UnitaryFieldData 2 1 F :=
    TableBU.unitaryFieldData_of_card hK (by norm_num)
  change diagHom N t ∈ unitarySU 2 1 F N ↔ ∏ i, t i = 1
  constructor
  · intro hmem
    have hdet := ((mem_unitarySU_iff hunit).mp hmem).1
    rw [det_diagHom] at hdet
    exact Units.ext (by rw [Units.coe_prod, Units.val_one]; exact hdet)
  · intro hprod
    have hnorm : ∀ k, (t k : F) ^ (2 ^ 1 + 1) = 1 := fun k => by
      rw [show 2 ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val,
        ggQ2s08rN_pow_three_eq_one hF (t k), Units.val_one]
    have hdet : (diagHom N t : Matrix (Fin N) (Fin N) F).det = 1 := by
      rw [det_diagHom, ← Units.coe_prod, hprod, Units.val_one]
    exact (mem_unitarySU_iff hunit).mpr ⟨hdet, diagHom_unitary hunit hnorm⟩

theorem ggQ2s08rN_exists_diag_of_commute (hF : Nat.card F = 4) {A : GL (Fin N) F}
    (h : ∀ t : Fin N → Fˣ, ∏ i, t i = 1 → A * diagHom N t = diagHom N t * A) :
    ∃ u : Fin N → Fˣ, A = diagHom N u := by
  classical
  obtain ⟨ω, hω1, -, hωne⟩ := ggQ2s08rN_exists_omega (F := F) hF
  have hzero : ∀ i j : Fin N, i ≠ j → (A : Matrix (Fin N) (Fin N) F) i j = 0 := by
    intro i j hij
    by_contra hne
    let t : Fin N → Fˣ := Pi.mulSingle i ω * Pi.mulSingle j ω⁻¹
    have htprod : ∏ k, t k = 1 := by
      simp only [t, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
      exact mul_inv_cancel ω
    have hcomm := h t htprod
    have hmat : (A : Matrix (Fin N) (Fin N) F) * Matrix.diagonal (fun k => (t k : F)) =
        Matrix.diagonal (fun k => (t k : F)) * (A : Matrix (Fin N) (Fin N) F) := by
      simpa only [Units.val_mul, coe_diagHom] using
        congrArg (fun g : GL (Fin N) F => (g : Matrix (Fin N) (Fin N) F)) hcomm
    have hmat1 := congrFun (congrFun hmat i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hmat1
    have hji : (t j : F) = (t i : F) :=
      mul_left_cancel₀ hne (hmat1.trans (mul_comm _ _))
    have hti : (t i : F) = (ω : F) := by
      have hti' : t i = ω := by
        simp only [t, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij, mul_one]
      rw [hti']
    have htj : (t j : F) = ((ω⁻¹ : Fˣ) : F) := by
      have htj' : t j = ω⁻¹ := by
        simp only [t, Pi.mul_apply, Pi.mulSingle_eq_of_ne (Ne.symm hij),
          Pi.mulSingle_eq_same, one_mul]
      rw [htj']
    have hval : ((ω⁻¹ : Fˣ) : F) = (ω : F) := htj.symm.trans (hji.trans hti)
    exact hωne (Units.ext hval).symm
  have hdiag : (A : Matrix (Fin N) (Fin N) F) =
      Matrix.diagonal (fun i => (A : Matrix (Fin N) (Fin N) F) i i) := by
    ext i j
    by_cases hij : i = j
    · rw [← hij, Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij, hzero i j hij]
  have hdet : (A : Matrix (Fin N) (Fin N) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hdiagne : ∀ i, (A : Matrix (Fin N) (Fin N) F) i i ≠ 0 := by
    intro i
    have hprod : (∏ k, (A : Matrix (Fin N) (Fin N) F) k k) ≠ 0 := by
      rw [← Matrix.det_diagonal, ← hdiag]
      exact hdet
    exact (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  refine ⟨fun i => Units.mk0 ((A : Matrix (Fin N) (Fin N) F) i i) (hdiagne i), ?_⟩
  apply Units.ext
  ext i j
  rw [coe_diagHom]
  by_cases hij : i = j
  · rw [← hij, Matrix.diagonal_apply_eq, Units.val_mk0]
  · rw [Matrix.diagonal_apply_ne _ hij, hzero i j hij]

theorem ggQ2s08rN_exists_scalar_of_commute [NeZero N] (hF : Nat.card F = 4) {A : GL (Fin N) F}
    (h : ∀ g ∈ LargeEvenSUGroup (Fin N) F 2, A * g = g * A) :
    ∃ c : Fˣ, A = Matrix.GeneralLinearGroup.scalar (Fin N) c := by
  have hdiag : ∀ t : Fin N → Fˣ, ∏ i, t i = 1 → A * diagHom N t = diagHom N t * A :=
    fun t ht => h _ ((ggQ2s08rN_diagHom_mem_iff hF t).mpr ht)
  obtain ⟨u, hu⟩ := ggQ2s08rN_exists_diag_of_commute hF hdiag
  refine ⟨u 0, ?_⟩
  have hconst : ∀ i, u i = u 0 := by
    intro i
    by_cases hi : i = 0
    · rw [hi]
    · have hsw := h (permGL (Equiv.swap i 0))
        (ggQ2s08rN_permGL_mem hF (Equiv.swap i 0))
      rw [hu] at hsw
      have h1 : diagHom N u = permGL (Equiv.swap i 0) * diagHom N u *
          (permGL (Equiv.swap i 0))⁻¹ := by
        rw [← hsw, mul_inv_cancel_right]
      have h2 : diagHom N u = diagHom N (u ∘ (Equiv.swap i 0).symm) := by
        rw [h1, permGL_mul_diagHom_mul_inv]
      have h3 := congrFun (diagHom_injective N h2) i
      simp only [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_left] at h3
      exact h3
  have hconst' : u = fun _ => u 0 := funext hconst
  rw [hu, hconst', ggQ2s08rN_diagHom_const]

omit [Finite F] in
private theorem ggQ2s08rN_exists_isPermOf [NeZero N] {A : GL (Fin N) F}
    (hcol : ∀ i l l', (A : Matrix (Fin N) (Fin N) F) l i ≠ 0 →
      (A : Matrix (Fin N) (Fin N) F) l' i ≠ 0 → l = l') :
    ∃ π : Equiv.Perm (Fin N), ∀ i l, (A : Matrix (Fin N) (Fin N) F) l i ≠ 0 ↔ l = π i := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos N)).symm⟩
  obtain ⟨π, hπ⟩ := LinModel.exists_isPermOf hcol
  exact ⟨π, hπ⟩

theorem ggQ2s08rN_exists_monomial [NeZero N] (hF : Nat.card F = 4) {A : GL (Fin N) F}
    (h : ∀ t : Fin N → Fˣ, ∏ i, t i = 1 →
      ∃ t' : Fin N → Fˣ, A * diagHom N t * A⁻¹ = diagHom N t') :
    ∃ (σ : Equiv.Perm (Fin N)) (u : Fin N → Fˣ), A = permGL σ * diagHom N u := by
  classical
  obtain ⟨ω, -, -, hωne⟩ := ggQ2s08rN_exists_omega (F := F) hF
  let S := {t : Fin N → Fˣ // ∏ i, t i = 1}
  let φ : S → S := fun t =>
    ⟨Classical.choose (h t.1 t.2), ggQ2s08rN_prod_eq_one_of_conj
      (Classical.choose_spec (h t.1 t.2)) t.2⟩
  have hφinj : Function.Injective φ := by
    intro t₁ t₂ h12
    apply Subtype.ext
    have hspec₁ := Classical.choose_spec (h t₁.1 t₁.2)
    have hspec₂ := Classical.choose_spec (h t₂.1 t₂.2)
    have hval : (φ t₁).1 = (φ t₂).1 := congrArg Subtype.val h12
    have heq : A * diagHom N t₁.1 * A⁻¹ = A * diagHom N t₂.1 * A⁻¹ := by
      calc A * diagHom N t₁.1 * A⁻¹ = diagHom N (φ t₁).1 := hspec₁
        _ = diagHom N (φ t₂).1 := by rw [hval]
        _ = A * diagHom N t₂.1 * A⁻¹ := hspec₂.symm
    exact diagHom_injective N (mul_left_cancel (mul_right_cancel heq))
  have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφinj
  have hcol : ∀ (i l l' : Fin N),
      (A : Matrix (Fin N) (Fin N) F) l i ≠ 0 →
      (A : Matrix (Fin N) (Fin N) F) l' i ≠ 0 → l = l' := by
    intro i l l' hl hl'
    by_contra hne
    let t' : Fin N → Fˣ := Pi.mulSingle l ω * Pi.mulSingle l' ω⁻¹
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
    have hDt' : diagHom N (φ t).1 = diagHom N t' :=
      congrArg (diagHom N) (congrArg Subtype.val ht)
    have hD : A * diagHom N t.1 * A⁻¹ = diagHom N t' := hspec.trans hDt'
    have heq : A * diagHom N t.1 = diagHom N t' * A := by
      calc A * diagHom N t.1 = (A * diagHom N t.1 * A⁻¹) * A := by group
        _ = diagHom N t' * A := by rw [hD]
    have hmat : (A : Matrix (Fin N) (Fin N) F) * Matrix.diagonal (fun k => (t.1 k : F)) =
        Matrix.diagonal (fun k => (t' k : F)) * (A : Matrix (Fin N) (Fin N) F) := by
      simpa only [Units.val_mul, coe_diagHom] using
        congrArg (fun g : GL (Fin N) F => (g : Matrix (Fin N) (Fin N) F)) heq
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
  obtain ⟨π, hπ⟩ := ggQ2s08rN_exists_isPermOf hcol
  refine ⟨π, fun i => Units.mk0 ((A : Matrix (Fin N) (Fin N) F) (π i) i)
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
