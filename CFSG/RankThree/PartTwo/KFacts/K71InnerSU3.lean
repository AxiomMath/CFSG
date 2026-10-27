module

public import CFSG.RankThree.PartTwo.KFacts.K71Residual
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open Matrix
open scoped MatrixGroups

section SUModel

variable {K : Type} [Field K]

@[expose] def suCentralizer (q : ℕ) (t : GL (Fin 3) K) : Subgroup (StatedSU 3 q K) :=
  (Subgroup.centralizer {t}).subgroupOf (StatedSU 3 q K)

theorem mem_suCentralizer {q : ℕ} {t : GL (Fin 3) K} {x : StatedSU 3 q K} :
    x ∈ suCentralizer q t ↔ (x : GL (Fin 3) K) * t = t * x := by
  rw [suCentralizer, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]

variable {l m : K}

theorem entries_eq_zero_of_mul_diag_eq (hlm : l ≠ m) {X : Matrix (Fin 3) (Fin 3) K}
    (hX : X * diagonal ![l, l, m] = diagonal ![l, l, m] * X) :
    X 0 2 = 0 ∧ X 1 2 = 0 ∧ X 2 0 = 0 ∧ X 2 1 = 0 := by
  have e : ∀ i j, X i j * ![l, l, m] j = ![l, l, m] i * X i j := fun i j => by
    rw [← Matrix.mul_diagonal, ← Matrix.diagonal_mul, hX]
  have hml : m - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hlm)
  have h02 := e 0 2
  have h12 := e 1 2
  have h20 := e 2 0
  have h21 := e 2 1
  simp at h02 h12 h20 h21
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : X 0 2 * (m - l) = 0 := by linear_combination h02
    exact (mul_eq_zero.mp this).resolve_right hml
  · have : X 1 2 * (m - l) = 0 := by linear_combination h12
    exact (mul_eq_zero.mp this).resolve_right hml
  · have : X 2 0 * (m - l) = 0 := by linear_combination -h20
    exact (mul_eq_zero.mp this).resolve_right hml
  · have : X 2 1 * (m - l) = 0 := by linear_combination -h21
    exact (mul_eq_zero.mp this).resolve_right hml

theorem det_eq_of_entries_eq_zero {X : Matrix (Fin 3) (Fin 3) K}
    (h : X 0 2 = 0 ∧ X 1 2 = 0 ∧ X 2 0 = 0 ∧ X 2 1 = 0) :
    X.det = (X 0 0 * X 1 1 - X 0 1 * X 1 0) * X 2 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [Matrix.det_fin_three, h1, h2, h3, h4]
  ring

variable {q : ℕ} {t : GL (Fin 3) K}

theorem entries_eq_zero_of_mem_suCentralizer (hlm : l ≠ m)
    (ht : (t : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m]) {x : StatedSU 3 q K}
    (hx : x ∈ suCentralizer q t) :
    ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  apply entries_eq_zero_of_mul_diag_eq hlm
  have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
    (mem_suCentralizer.mp hx)
  simp only [Units.val_mul, ht] at h
  exact h

theorem corner_ne_zero (hlm : l ≠ m) (ht : (t : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m])
    {x : StatedSU 3 q K} (hx : x ∈ suCentralizer q t) :
    ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
  intro h0
  have hdet := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU x.2
  rw [det_eq_of_entries_eq_zero (entries_eq_zero_of_mem_suCentralizer hlm ht hx), h0,
    mul_zero] at hdet
  exact zero_ne_one hdet

@[expose] noncomputable def suCornerHom (hlm : l ≠ m)
    (ht : (t : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m]) : suCentralizer q t →* Kˣ where
  toFun x := Units.mk0 ((((x : StatedSU 3 q K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2)
    (corner_ne_zero hlm ht x.2)
  map_one' := Units.ext (by simp)
  map_mul' x y := by
    apply Units.ext
    obtain ⟨-, -, hx20, hx21⟩ := entries_eq_zero_of_mem_suCentralizer hlm ht x.2
    simp only [Units.val_mk0, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply,
      Fin.sum_univ_three]
    rw [hx20, hx21]
    ring

theorem coe_suCornerHom (hlm : l ≠ m) (ht : (t : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m])
    (x : suCentralizer q t) :
    (suCornerHom hlm ht x : K) =
      (((x : StatedSU 3 q K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 :=
  rfl

theorem leviSU3_le_suCentralizer (ht : (t : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m]) :
    leviSU3 (K := K) q ≤ suCentralizer q t := by
  rintro x ⟨A, -, hA⟩
  rw [mem_suCentralizer]
  have hA' : (x : GL (Fin 3) K) = blockGL3 A := hA.symm
  rw [hA']
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_blockGL3, ht]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [leviMat, mul_comm]

@[expose] noncomputable def leviSU3Equiv (hq : 1 ≤ q) :
    StatedSU 2 q K ≃* leviSU3 (K := K) q := by
  let φ : StatedSU 2 q K →* StatedSU 3 q K :=
    (blockGL3.comp (StatedSU 2 q K).subtype).codRestrict (StatedSU 3 q K) fun A =>
      map_blockGL3_statedSU_le hq ⟨A, A.2, rfl⟩
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro A hA
    have h1 : blockGL3 (A : GL (Fin 2) K) = 1 := congrArg Subtype.val hA
    exact Subtype.ext (blockGL3_eq_one_of_scalar (h1 ▸ one_mem _))
  have hrange : φ.range = leviSU3 q := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨A, A.2, rfl⟩
    · rintro ⟨A, hA, hAx⟩
      exact ⟨⟨A, hA⟩, Subtype.ext hAx⟩
  exact (MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hrange)

variable {p f : ℕ}

theorem isPerfect_leviSU3 [Finite K] (h : UnitaryFieldData p f K) (hq : 4 ≤ p ^ f) :
    Group.IsPerfect (leviSU3 (K := K) (p ^ f)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have : Group.IsPerfect (StatedSU 2 (p ^ f) K) := isPerfect_statedSU_two h.card_eq_sq hq
  exact Group.IsPerfect.ofSurjective (f := (leviSU3Equiv (K := K) (by omega)).toMonoidHom)
    (leviSU3Equiv (K := K) (by omega)).surjective

theorem mem_leviSU3_of_corner_eq_one (h : UnitaryFieldData p f K) (hlm : l ≠ m)
    {t : GL (Fin 3) K} (ht : (t : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m])
    {x : StatedSU 3 (p ^ f) K} (hx : x ∈ suCentralizer (p ^ f) t)
    (h22 : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1) :
    x ∈ leviSU3 (K := K) (p ^ f) := by
  obtain ⟨h02, h12, h20, h21⟩ := entries_eq_zero_of_mem_suCentralizer hlm ht hx
  have hdet := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU x.2
  have hu := ((mem_unitarySU_iff h).mp x.2).2
  generalize hX : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = X at h02 h12 h20 h21 h22 hdet hu
  rw [det_eq_of_entries_eq_zero ⟨h02, h12, h20, h21⟩, h22, mul_one] at hdet
  set B : Matrix (Fin 2) (Fin 2) K := !![X 0 0, X 0 1; X 1 0, X 1 1] with hB
  have hBdet : B.det = 1 := by
    rw [hB, Matrix.det_fin_two_of]
    exact hdet
  set A : GL (Fin 2) K := GeneralLinearGroup.mkOfDetNeZero B (by rw [hBdet]; exact one_ne_zero)
  have hAx : blockGL3 A = (x : GL (Fin 3) K) := by
    apply Units.ext
    rw [coe_blockGL3, hX]
    change leviMat B = X
    ext i j
    fin_cases i <;> fin_cases j <;> simp [leviMat, hB, h02, h12, h20, h21, h22]
  have hq0 : (0 : K) ^ p ^ f = 0 := zero_pow (pow_ne_zero _ h.prime.ne_zero)
  have hAmem : A ∈ StatedSU 2 (p ^ f) K := by
    apply Subgroup.subset_closure
    refine ⟨hBdet, ?_⟩
    change (B.map (· ^ p ^ f))ᵀ * B = 1
    have e := fun i j => congrFun (congrFun hu i) j
    ext i j
    have hij := e (Fin.castSucc i) (Fin.castSucc j)
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h.bar_apply, h20, h21, hq0,
        hB] at hij ⊢ <;> linear_combination hij
  exact ⟨A, hAmem, hAx⟩

theorem inSubgroup_perfectResidual_suCentralizer_eq [Finite K] (h : UnitaryFieldData p f K)
    (hq : 4 ≤ p ^ f) (hlm : l ≠ m) {t : GL (Fin 3) K}
    (ht : (t : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m]) :
    inSubgroup perfectResidual (suCentralizer (p ^ f) t) = leviSU3 (K := K) (p ^ f) := by
  apply le_antisymm
  · refine inSubgroup_perfectResidual_le (suCornerHom hlm ht) (fun x y => mul_comm _ _) ?_
    intro x hx
    refine mem_leviSU3_of_corner_eq_one h hlm ht x.2 ?_
    rw [← coe_suCornerHom hlm ht, hx, Units.val_one]
  · exact le_inSubgroup_perfectResidual (isPerfect_leviSU3 h hq) (leviSU3_le_suCentralizer ht)

theorem exists_perfectResidual_suCentralizer_mulEquiv [Finite K] (h : UnitaryFieldData p f K)
    (hq : 4 ≤ p ^ f) (hlm : l ≠ m) {t : GL (Fin 3) K}
    (ht : (t : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m]) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = p ^ f ∧
      Nonempty (inSubgroup perfectResidual (suCentralizer (p ^ f) t) ≃* SL(2, F₀)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  obtain ⟨ι⟩ := nonempty_sl2_mulEquiv_statedSU_two h.card_eq_sq
  refine ⟨CFSG.LieType.Steinberg.fixedSubfield K p f, inferInstance, inferInstance,
    CFSG.LieType.Steinberg.card_fixedSubfield h.card_eq_sq, ?_⟩
  exact ⟨(MulEquiv.subgroupCongr (inSubgroup_perfectResidual_suCentralizer_eq h hq hlm ht)).trans
    ((leviSU3Equiv (K := K) (by omega)).symm.trans ι.symm)⟩

end SUModel

section PSUModel

variable {p f : ℕ} {K : Type} [Field K] {l m : K}

theorem eq_one_of_mul_diag_eq (hl : l ≠ 0) {X : Matrix (Fin 3) (Fin 3) K} (hX : X.det ≠ 0)
    {c : K} (hc : ∀ i j, X i j * ![l, l, m] j = ![l, l, m] i * X i j * c) : c = 1 := by
  by_contra hc1
  have hc' : (1 - c) * l ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hc1)) hl
  have hv : ∀ k : Fin 2, ![l, l, m] (Fin.castSucc k) = l := fun k => by
    fin_cases k <;> simp
  have hz : ∀ i j : Fin 2, X (Fin.castSucc i) (Fin.castSucc j) = 0 := by
    intro i j
    have hij := hc (Fin.castSucc i) (Fin.castSucc j)
    rw [hv, hv] at hij
    have : X (Fin.castSucc i) (Fin.castSucc j) * ((1 - c) * l) = 0 := by
      linear_combination hij
    exact (mul_eq_zero.mp this).resolve_right hc'
  apply hX
  have h00 := hz 0 0
  have h01 := hz 0 1
  have h10 := hz 1 0
  have h11 := hz 1 1
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at h00 h01 h10 h11
  rw [Matrix.det_fin_three, h00, h01, h10, h11]
  ring

variable (h : UnitaryFieldData p f K)

theorem psuConj_fixed_iff {A : unitaryIsom3 h}
    (hA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m])
    (g : unitarySU p f K 3) :
    psuConj h A (unitaryProj h 3 g) = unitaryProj h 3 g ↔
      g ∈ suCentralizer (p ^ f) (A : GL (Fin 3) K) := by
  have hl : l ≠ 0 := by
    intro hl0
    have hdet := (GeneralLinearGroup.det (A : GL (Fin 3) K)).ne_zero
    rw [GeneralLinearGroup.val_det_apply, hA, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
    simp [hl0] at hdet
  rw [mem_suCentralizer, unitaryProj, QuotientGroup.mk'_apply, psuConj_mk]
  constructor
  · intro hfix
    rw [QuotientGroup.eq] at hfix
    obtain ⟨c, -, -, hc⟩ := hfix
    have h1 : ((A : GL (Fin 3) K) * g * (A : GL (Fin 3) K)⁻¹)⁻¹ * (g : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) c := by
      rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv, coe_suConj, Subgroup.coe_inv]
    have h2 := inv_mul_eq_iff_eq_mul.mp h1
    have h3 : (g : GL (Fin 3) K) * A =
        (A : GL (Fin 3) K) * g * GeneralLinearGroup.scalar (Fin 3) c := by
      have hcomm := (commute_scalar c (A : GL (Fin 3) K)).eq
      conv_lhs => rw [h2]
      rw [mul_assoc _ (GeneralLinearGroup.scalar (Fin 3) c), ← hcomm]
      group
    have hc1 : c = 1 := by
      have h4 := congrArg (fun y : GL (Fin 3) K => (y : Matrix (Fin 3) (Fin 3) K)) h3
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hA, Matrix.scalar_apply] at h4
      apply Units.ext
      rw [Units.val_one]
      refine eq_one_of_mul_diag_eq (m := m) (X := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        hl ?_ fun i j => ?_
      · rw [CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU g.2]
        exact one_ne_zero
      · have := congrFun (congrFun h4 i) j
        rwa [Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    rw [hc1, map_one, mul_one] at h3
    exact h3
  · intro hcomm
    congr 1
    apply Subtype.ext
    rw [coe_suConj, Subgroup.coe_inv, ← hcomm, mul_inv_cancel_right]

theorem mem_map_suCentralizer_iff {A : unitaryIsom3 h}
    (hA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m])
    (z : unitaryPSU h 3) :
    z ∈ (suCentralizer (p ^ f) (A : GL (Fin 3) K)).map (unitaryProj h 3) ↔ psuConj h A z = z := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (psuConj_fixed_iff h hA g).mpr hg
  · intro hz
    obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 z
    exact ⟨g, (psuConj_fixed_iff h hA g).mp hz, rfl⟩

theorem unitaryProj_comp_leviSU3_injective :
    Function.Injective ((unitaryProj h 3).comp (leviSU3 (K := K) (p ^ f)).subtype) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨x, B, hB, hBx⟩ hx
  have hBx' : blockGL3 B = (x : GL (Fin 3) K) := hBx
  rw [MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_unitaryProj] at hx
  obtain ⟨c, -, -, hc⟩ := hx
  have hsc : blockGL3 B ∈ StatedScalars (Fin 3) K := by
    rw [hBx']
    exact ⟨c, hc.symm⟩
  apply Subtype.ext
  apply Subtype.ext
  change (x : GL (Fin 3) K) = 1
  rw [← hBx', blockGL3_eq_one_of_scalar hsc, map_one]

theorem exists_perfectResidual_psuFixed_mulEquiv [Finite K] (hq : 4 ≤ p ^ f) (hlm : l ≠ m)
    {A : unitaryIsom3 h}
    (hA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m]) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = p ^ f ∧
      Nonempty (inSubgroup perfectResidual
        ((suCentralizer (p ^ f) (A : GL (Fin 3) K)).map (unitaryProj h 3)) ≃* SL(2, F₀)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  obtain ⟨ι⟩ := nonempty_sl2_mulEquiv_statedSU_two h.card_eq_sq
  refine ⟨CFSG.LieType.Steinberg.fixedSubfield K p f, inferInstance, inferInstance,
    CFSG.LieType.Steinberg.card_fixedSubfield h.card_eq_sq, ?_⟩
  have heq : inSubgroup perfectResidual
      ((suCentralizer (p ^ f) (A : GL (Fin 3) K)).map (unitaryProj h 3)) =
      ((unitaryProj h 3).comp (leviSU3 (K := K) (p ^ f)).subtype).range := by
    rw [← map_inSubgroup_perfectResidual_hom,
      inSubgroup_perfectResidual_suCentralizer_eq h hq hlm hA, MonoidHom.range_comp,
      Subgroup.range_subtype]
  exact ⟨(MulEquiv.subgroupCongr heq).trans
    ((MonoidHom.ofInjective (unitaryProj_comp_leviSU3_injective h)).symm.trans
      ((leviSU3Equiv (K := K) (by omega)).symm.trans ι.symm))⟩

end PSUModel

section Bar

open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {p f : ℕ} {K : Type} [Field K] {l m : K}

theorem exists_imageModTheta_mulEquiv_sl2_of_su3 [Finite K] (h : UnitaryFieldData p f K)
    (hq : 4 ≤ p ^ f) (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU p f K 3) {d : G}
    (hd : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : ∃ j : ℕ, d ^ 3 ^ j = 1) (hlm : l ≠ m)
    {t : GL (Fin 3) K} (ht : (t : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m])
    (hdt : ∀ g : unitarySU p f K 3,
      ((inducedAutHom L e ⟨d, hd⟩ g : unitarySU p f K 3) : GL (Fin 3) K) = t * g * t⁻¹) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = p ^ f ∧
      Nonempty (Sec8.imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}))
        ≃* SL(2, F₀)) := by
  obtain ⟨ι⟩ := nonempty_imageModTheta_perfectResidual_mulEquiv hd hd3 e (suCentralizer (p ^ f) t)
    fun z => by
      rw [mem_suCentralizer, ← Subtype.coe_inj, hdt, mul_inv_eq_iff_eq_mul, eq_comm]
  obtain ⟨F₀, hF₀, hF₀', hcard, ⟨κ⟩⟩ := exists_perfectResidual_suCentralizer_mulEquiv h hq hlm ht
  exact ⟨F₀, hF₀, hF₀', hcard, ⟨ι.trans κ⟩⟩

theorem imageModTheta_mulEquiv_projSL_of_su3 [Finite K] (h : UnitaryFieldData 2 f K)
    (hf : 2 ≤ f) (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU 2 f K 3) {d : G}
    (hd : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : ∃ j : ℕ, d ^ 3 ^ j = 1) (hlm : l ≠ m)
    {t : GL (Fin 3) K} (ht : (t : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m])
    (hdt : ∀ g : unitarySU 2 f K 3,
      ((inducedAutHom L e ⟨d, hd⟩ g : unitarySU 2 f K 3) : GL (Fin 3) K) = t * g * t⁻¹) :
    Nonempty (Sec8.imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
      projSL 2 (GaloisField 2 f)) ∧
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ≠ ⊥ := by
  have hq : 4 ≤ 2 ^ f := (Nat.pow_le_pow_right (by norm_num) hf : 2 ^ 2 ≤ 2 ^ f)
  obtain ⟨F₀, _, _, hcard, ⟨ι⟩⟩ := exists_imageModTheta_mulEquiv_sl2_of_su3 h hq e hd hd3 hlm ht hdt
  obtain ⟨κ⟩ := nonempty_sl2_mulEquiv_projSL hcard
  have := nontrivial_sl2 F₀
  exact ⟨⟨ι.trans κ⟩, ne_bot_of_imageModTheta_mulEquiv ι⟩

theorem exists_imageModTheta_mulEquiv_sl2_of_suConj [Finite K] (h : UnitaryFieldData p f K)
    (hq : 4 ≤ p ^ f) (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU p f K 3) {d : G}
    (hd : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : ∃ j : ℕ, d ^ 3 ^ j = 1) (hlm : l ≠ m)
    {A : unitaryIsom3 h}
    (hA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m])
    (hdA : inducedAutHom L e ⟨d, hd⟩ = suConj h A) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = p ^ f ∧
      Nonempty (Sec8.imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}))
        ≃* SL(2, F₀)) :=
  exists_imageModTheta_mulEquiv_sl2_of_su3 h hq e hd hd3 hlm hA fun g => by
    rw [hdA, coe_suConj, Subgroup.coe_inv]

theorem exists_imageModTheta_mulEquiv_sl2_of_psu3 [Finite K] (h : UnitaryFieldData p f K)
    (hq : 4 ≤ p ^ f) (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitaryPSU h 3) {d : G}
    (hd : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : ∃ j : ℕ, d ^ 3 ^ j = 1) (hlm : l ≠ m)
    {A : unitaryIsom3 h}
    (hA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m])
    (hdA : inducedAutHom L e ⟨d, hd⟩ = psuConj h A) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = p ^ f ∧
      Nonempty (Sec8.imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}))
        ≃* SL(2, F₀)) := by
  obtain ⟨ι⟩ := nonempty_imageModTheta_perfectResidual_mulEquiv hd hd3 e
    ((suCentralizer (p ^ f) (A : GL (Fin 3) K)).map (unitaryProj h 3)) fun z => by
      rw [hdA]
      exact mem_map_suCentralizer_iff h hA z
  obtain ⟨F₀, hF₀, hF₀', hcard, ⟨κ⟩⟩ := exists_perfectResidual_psuFixed_mulEquiv h hq hlm hA
  exact ⟨F₀, hF₀, hF₀', hcard, ⟨ι.trans κ⟩⟩

theorem imageModTheta_mulEquiv_projSL_of_psu3 [Finite K] (h : UnitaryFieldData 2 f K)
    (hf : 2 ≤ f) (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitaryPSU h 3) {d : G}
    (hd : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : ∃ j : ℕ, d ^ 3 ^ j = 1) (hlm : l ≠ m)
    {A : unitaryIsom3 h}
    (hA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m])
    (hdA : inducedAutHom L e ⟨d, hd⟩ = psuConj h A) :
    Nonempty (Sec8.imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
      projSL 2 (GaloisField 2 f)) ∧
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ≠ ⊥ := by
  have hq : 4 ≤ 2 ^ f := (Nat.pow_le_pow_right (by norm_num) hf : 2 ^ 2 ≤ 2 ^ f)
  obtain ⟨F₀, _, _, hcard, ⟨ι⟩⟩ :=
    exists_imageModTheta_mulEquiv_sl2_of_psu3 h hq e hd hd3 hlm hA hdA
  obtain ⟨κ⟩ := nonempty_sl2_mulEquiv_projSL hcard
  have := nontrivial_sl2 F₀
  exact ⟨⟨ι.trans κ⟩, ne_bot_of_imageModTheta_mulEquiv ι⟩

theorem inducesKindSU3_inner_or_diagonal (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU p f K 3) {d : G}
    (hd : d ∈ Subgroup.normalizer (L : Set G)) (A : unitaryIsom3 h)
    (hdA : inducedAutHom L e ⟨d, hd⟩ = suConj h A) :
    InducesKindSU3 h L hq d .inner ∨ InducesKindSU3 h L hq d .diagonal := by
  have hmem : MulAut.congr (suCenterEquiv h hq) (centerDescend _ (inducedAutHom L e ⟨d, hd⟩)) ∈
      (stdPinnedPSU3 h).inndiag := by
    rw [hdA, congr_centerDescend_suConj]
    exact ⟨A, rfl⟩
  by_cases hi : IsInnerAut
      (MulAut.congr (suCenterEquiv h hq) (centerDescend _ (inducedAutHom L e ⟨d, hd⟩)))
  · exact Or.inl ⟨e, hd, hi⟩
  · exact Or.inr ⟨e, hd, hmem, hi⟩

theorem inducesKindPSU3_inner_or_diagonal (h : UnitaryFieldData p f K)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitaryPSU h 3) {d : G}
    (hd : d ∈ Subgroup.normalizer (L : Set G)) (A : unitaryIsom3 h)
    (hdA : inducedAutHom L e ⟨d, hd⟩ = psuConj h A) :
    InducesKindPSU3 h L d .inner ∨ InducesKindPSU3 h L d .diagonal := by
  have hmem : inducedAutHom L e ⟨d, hd⟩ ∈ (stdPinnedPSU3 h).inndiag := by
    rw [hdA]
    exact ⟨A, rfl⟩
  by_cases hi : IsInnerAut (inducedAutHom L e ⟨d, hd⟩)
  · exact Or.inl ⟨e, hd, hi⟩
  · exact Or.inr ⟨e, hd, hmem, hi⟩

end Bar

end CFSG.RankThree.PartTwo.KFacts
