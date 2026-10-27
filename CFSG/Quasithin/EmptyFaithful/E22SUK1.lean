module

public import CFSG.Quasithin.EmptyFaithful.E22SQ
public import CFSG.Quasithin.EmptyFaithful.E22SUStd
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2
public import CFSG.Quasithin.EmptyFaithful.E22SUFrame

public section

namespace CFSG.Quasithin.E22S

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open scoped MatrixGroups Matrix

namespace UK1

section Matrices

variable {K : Type} [Field K]

theorem negBlock_three_zero : CFSG.ClassicalInvolution.Models.negBlock K 3 0 = matZ K := by
  rw [CFSG.ClassicalInvolution.Models.negBlock_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matZ]

theorem mulVec_e2_apply (X : Matrix (Fin 3) (Fin 3) K) (a : Fin 3) :
    (X *ᵥ (Pi.single 2 1 : Fin 3 → K)) a = X a 2 := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem col_two_of_mulVec {X : Matrix (Fin 3) (Fin 3) K}
    (h : X *ᵥ (Pi.single 2 1 : Fin 3 → K) = Pi.single 2 1) :
    X 0 2 = 0 ∧ X 1 2 = 0 ∧ X 2 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [mulVec_e2_apply, Pi.single_apply] using congrFun h 0
  · simpa [mulVec_e2_apply, Pi.single_apply] using congrFun h 1
  · simpa [mulVec_e2_apply, Pi.single_apply] using congrFun h 2

theorem mulVec_e2_of_cols {X : Matrix (Fin 3) (Fin 3) K}
    (h0 : X 0 2 = 0) (h1 : X 1 2 = 0) (h2 : X 2 2 = 1) :
    X *ᵥ (Pi.single 2 1 : Fin 3 → K) = Pi.single 2 1 := by
  funext a
  rw [mulVec_e2_apply]
  fin_cases a <;> simp [h0, h1, h2]

theorem row_two_of_mulVec_of_unitary {σ : K → K} (h0 : σ 0 = 0) (hinj : Function.Injective σ)
    {X : Matrix (Fin 3) (Fin 3) K}
    (h : X *ᵥ (Pi.single 2 1 : Fin 3 → K) = Pi.single 2 1) (hu : (X.map σ)ᵀ * X = 1) :
    X 2 0 = 0 ∧ X 2 1 = 0 := by
  have hrow : (X.map σ)ᵀ *ᵥ (Pi.single 2 1 : Fin 3 → K) = Pi.single 2 1 := by
    rw [← h, Matrix.mulVec_mulVec, hu, Matrix.one_mulVec, h]
  have hr : ∀ b : Fin 3, σ (X 2 b) = (Pi.single 2 1 : Fin 3 → K) b := fun b => by
    have := congrFun hrow b
    simpa [mulVec_e2_apply] using this
  refine ⟨hinj ?_, hinj ?_⟩
  · simpa [Pi.single_apply, h0] using hr 0
  · simpa [Pi.single_apply, h0] using hr 1

theorem mul_matZ_comm_of_mulVec_e2 {σ : K → K} (h0 : σ 0 = 0) (hinj : Function.Injective σ)
    {X : Matrix (Fin 3) (Fin 3) K}
    (h : X *ᵥ (Pi.single 2 1 : Fin 3 → K) = Pi.single 2 1) (hu : (X.map σ)ᵀ * X = 1) :
    X * matZ K = matZ K * X := by
  obtain ⟨c0, c1, c2⟩ := col_two_of_mulVec h
  obtain ⟨r0, r1⟩ := row_two_of_mulVec_of_unitary h0 hinj h hu
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [matZ, Matrix.mul_apply, Fin.sum_univ_three, c0, c1, c2, r0, r1]

end Matrices

section Stabilizer

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem mem_longRootGroupSU_three_iff (h2 : (2 : K) ≠ 0) (x : Su K p f 3) :
    x ∈ longRootGroupSU K p f (negBlock K 3 0) ↔
      suMat x *ᵥ (Pi.single 2 1 : Fin 3 → K) = Pi.single 2 1 := by
  rw [mem_longRootGroupSU, negBlock_three_zero]
  constructor
  · rintro ⟨-, h3⟩
    have h02 : suMat x 0 2 * 2 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three, matZ, one_add_one_eq_two] using
        congrFun (congrFun h3 0) 2
    have h12 : suMat x 1 2 * 2 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three, matZ, one_add_one_eq_two] using
        congrFun (congrFun h3 1) 2
    have h22 : suMat x 2 2 * 2 = 1 * 2 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_three, matZ, one_add_one_eq_two] using
        congrFun (congrFun h3 2) 2
    exact mulVec_e2_of_cols ((mul_eq_zero.mp h02).resolve_right h2)
      ((mul_eq_zero.mp h12).resolve_right h2) (mul_right_cancel₀ h2 h22)
  · intro h
    obtain ⟨h02, h12, h22⟩ := col_two_of_mulVec h
    refine ⟨mul_matZ_comm_of_mulVec_e2 (σ := unitaryInvolution K p f) (map_zero _)
      (unitaryInvolution K p f).injective h x.2.2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [matZ, Matrix.mul_apply, Fin.sum_univ_three, h02, h12, h22]

theorem nonempty_suStab_mulEquiv_sl2 (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    Nonempty (↥(suStab K (p ^ f) 2) ≃* SL(2, fixedSubfield K p f)) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  obtain ⟨eSU⟩ := nonempty_sl2_mulEquiv_su_two (K := K) (p := p) (f := f) hK
  let e0 : Su K p f 3 ≃* ↥(StatedSU 3 (p ^ f) K) :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3)
  let φ : Su K p f 2 →* ↥(StatedSU 3 (p ^ f) K) :=
    e0.toMonoidHom.comp (blockEmb K p f 3 2 0 (by norm_num))
  have hφinj : Function.Injective φ :=
    e0.injective.comp (blockEmb_injective (K := K) (p := p) (f := f) (by norm_num))
  have hrange : φ.range = suStab K (p ^ f) 2 := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact mem_suStab.mpr ((mem_longRootGroupSU_three_iff h2 _).mp
        (blockEmb_mem_longRootGroupSU (K := K) (p := p) (f := f) (n := 3) (j := 0) (by norm_num) A))
    · intro hx
      have hy : e0.symm x ∈ longRootGroupSU K p f (negBlock K 3 0) :=
        (mem_longRootGroupSU_three_iff h2 _).mpr (mem_suStab.mp hx)
      obtain ⟨A, hA⟩ := exists_blockEmb_of_mem_longRootGroupSU h2 (by norm_num : 0 + 2 ≤ 3) hy
      exact ⟨A, by simp [φ, hA]⟩
  exact ⟨((MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans
    eSU.symm⟩

end Stabilizer

section Image

variable {K : Type} [Field K] {p f : ℕ}

theorem eq_one_of_mem_suScalars_of_mem_suStab {z : ↥(unitarySU p f K 3)}
    (hz : z ∈ suScalars p f K) (hs : z ∈ suStab K (p ^ f) 2) : z = 1 := by
  obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp hz : (z : GL (Fin 3) K) ∈
    (Matrix.GeneralLinearGroup.scalar (Fin 3)).range)
  have hmat : ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) (c : K) := by
    rw [← hc]
    simp [Matrix.GeneralLinearGroup.coe_scalar]
  have h22 : ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 :=
    (col_two_of_mulVec (mem_suStab.mp hs)).2.2
  rw [hmat] at h22
  have hc1 : c = 1 := Units.ext (by simpa [Matrix.scalar_apply] using h22)
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem injective_mk_domRestrict_suStab :
    Function.Injective
      ((QuotientGroup.mk' (suScalars p f K)).domRestrict (suStab K (p ^ f) 2)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  exact Subtype.ext (eq_one_of_mem_suScalars_of_mem_suStab
    ((QuotientGroup.eq_one_iff _).mp ha) a.2)

theorem nonempty_suStab_mulEquiv_J12P :
    Nonempty (↥(suStab K (p ^ f) 2) ≃* ↥(J12P p f K)) :=
  ⟨(MonoidHom.ofInjective injective_mk_domRestrict_suStab).trans
    (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range _ _))⟩

theorem nonempty_J12P_mulEquiv_sl2 [Finite K] [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    Nonempty (↥(J12P p f K) ≃* SL(2, CFSG.LieType.Steinberg.fixedSubfield K p f)) := by
  obtain ⟨e1⟩ := nonempty_suStab_mulEquiv_J12P (K := K) (p := p) (f := f)
  obtain ⟨e2⟩ := nonempty_suStab_mulEquiv_sl2 (K := K) (p := p) (f := f) hK hp2
  exact ⟨e1.symm.trans e2⟩

end Image

section SL2

open CFSG.ClassicalInvolution

variable {F : Type*} [Field F] [Finite F] {P : Type*} [Group P]

omit [Finite F] in
theorem isSimpleGroup_quotient_center_of_equiv_sl2 (h4 : 4 ≤ Nat.card F) (e : P ≃* SL(2, F)) :
    IsSimpleGroup (P ⧸ Subgroup.center P) := by
  have : IsSimpleGroup (SL(2, F) ⧸ Subgroup.center SL(2, F)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hmap : (Subgroup.center P).map e.toMonoidHom = Subgroup.center SL(2, F) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_center_iff_of_equiv_sl2 e x).mp hx
    · intro hy
      exact ⟨e.symm y, (mem_center_iff_of_equiv_sl2 e _).mpr (by simpa using hy), by simp⟩
  exact (QuotientGroup.congr (Subgroup.center P) (Subgroup.center SL(2, F)) e hmap).isSimpleGroup

omit [Finite F] in
theorem sq_eq_one_of_mem_center_of_equiv_sl2 (e : P ≃* SL(2, F)) {z : P}
    (hz : z ∈ Subgroup.center P) : z ^ 2 = 1 := by
  apply e.injective
  rcases (mem_center_sl2_iff _).mp ((mem_center_iff_of_equiv_sl2 e z).mp hz) with h | h <;>
    simp [map_pow, h]

end SL2

section Normalizer

variable {K : Type} [Field K] {p f : ℕ}

theorem eq_zero_of_neg_eq_self {a : K} (h2 : (2 : K) ≠ 0) (h : -a = a) : a = 0 := by
  have : (2 : K) * a = 0 := by linear_combination -h
  exact (mul_eq_zero.mp this).resolve_left h2

theorem mulVec_e2_eq_smul_of_comm_matZ (h2 : (2 : K) ≠ 0) {T : Matrix (Fin 3) (Fin 3) K}
    (h : matZ K * T = T * matZ K) :
    T *ᵥ (Pi.single 2 1 : Fin 3 → K) = (T 2 2) • (Pi.single 2 1 : Fin 3 → K) := by
  have h02 : T 0 2 = 0 := by
    have := congrFun (congrFun h 0) 2
    simp only [matZ, Matrix.mul_apply, Fin.sum_univ_three] at this
    exact eq_zero_of_neg_eq_self h2 (by simpa using this)
  have h12 : T 1 2 = 0 := by
    have := congrFun (congrFun h 1) 2
    simp only [matZ, Matrix.mul_apply, Fin.sum_univ_three] at this
    exact eq_zero_of_neg_eq_self h2 (by simpa using this)
  funext a
  rw [mulVec_e2_apply]
  fin_cases a <;> simp [h02, h12]

theorem conj_mulVec_e2 (h2 : (2 : K) ≠ 0) {T T' X : Matrix (Fin 3) (Fin 3) K}
    (hTT' : T' * T = 1) (hcomm : matZ K * T = T * matZ K)
    (hX : X *ᵥ (Pi.single 2 1 : Fin 3 → K) = Pi.single 2 1) :
    (T * X * T') *ᵥ (Pi.single 2 1 : Fin 3 → K) = Pi.single 2 1 := by
  have hT := mulVec_e2_eq_smul_of_comm_matZ h2 hcomm
  have h1 : T' *ᵥ (T *ᵥ (Pi.single 2 1 : Fin 3 → K)) = Pi.single 2 1 := by
    rw [Matrix.mulVec_mulVec, hTT', Matrix.one_mulVec]
  have hc : T 2 2 ≠ 0 := by
    intro hc0
    rw [hT, hc0, zero_smul, Matrix.mulVec_zero] at h1
    have := congrFun h1 2
    simp at this
  rw [hT, Matrix.mulVec_smul] at h1
  have hT' : T' *ᵥ (Pi.single 2 1 : Fin 3 → K) = (T 2 2)⁻¹ • (Pi.single 2 1 : Fin 3 → K) := by
    calc T' *ᵥ (Pi.single 2 1 : Fin 3 → K)
        = (T 2 2)⁻¹ • ((T 2 2) • (T' *ᵥ (Pi.single 2 1 : Fin 3 → K))) := by
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = (T 2 2)⁻¹ • (Pi.single 2 1 : Fin 3 → K) := by rw [h1]
  calc (T * X * T') *ᵥ (Pi.single 2 1 : Fin 3 → K)
      = T *ᵥ (X *ᵥ (T' *ᵥ (Pi.single 2 1 : Fin 3 → K))) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = T *ᵥ (X *ᵥ ((T 2 2)⁻¹ • (Pi.single 2 1 : Fin 3 → K))) := by rw [hT']
    _ = T *ᵥ ((T 2 2)⁻¹ • (Pi.single 2 1 : Fin 3 → K)) := by rw [Matrix.mulVec_smul, hX]
    _ = Pi.single 2 1 := by
        rw [Matrix.mulVec_smul, hT, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem conj_mem_suStab_of_comm_zS (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {τ : ↥(unitarySU p f K 3)} (hτ : zS hU * τ = τ * zS hU) {x : ↥(unitarySU p f K 3)}
    (hx : x ∈ suStab K (p ^ f) 2) : τ * x * τ⁻¹ ∈ suStab K (p ^ f) 2 := by
  have h2 := two_ne_zero_of_unitaryFieldData hU hp2
  have hcomm : matZ K * ((τ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((τ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * matZ K :=
    congrArg (fun g : ↥(unitarySU p f K 3) => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hτ
  have hTT' : (((τ⁻¹ : ↥(unitarySU p f K 3)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((τ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul]
    simp
  have := conj_mulVec_e2 h2 hTT' hcomm (mem_suStab.mp hx)
  exact mem_suStab.mpr (by simpa [Units.val_mul, Matrix.mul_assoc] using this)

theorem conj_mem_J12P_of_commute_zP (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {t : PSU3 p f K} (ht : t * zP hU = zP hU * t) {j : PSU3 p f K} (hj : j ∈ J12P p f K) :
    t * j * t⁻¹ ∈ J12P p f K := by
  obtain ⟨x, hx, rfl⟩ := hj
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective t
  have hzτ : zS hU * τ = τ * zS hU :=
    commute_of_proj_commute_two_U (by rw [pow_two, zS_mul_self]) ht.symm
  exact ⟨τ * x * τ⁻¹, conj_mem_suStab_of_comm_zS hU hp2 hzτ hx, by simp⟩

theorem mem_normalizer_J12P_of_commute_zP (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {t : PSU3 p f K} (ht : t * zP hU = zP hU * t) :
    t ∈ Subgroup.normalizer (J12P p f K : Set (PSU3 p f K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro j
  refine ⟨fun hj => conj_mem_J12P_of_commute_zP hU hp2 ht hj, fun hj => ?_⟩
  have ht' : t⁻¹ * zP hU = zP hU * t⁻¹ := (Commute.inv_left (show Commute t (zP hU) from ht)).eq
  simpa [mul_assoc] using conj_mem_J12P_of_commute_zP hU hp2 ht' hj

end Normalizer

section Products

variable {G : Type*} [Group G]

theorem exists_mul_eq_of_le_normalizer {J T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (J : Set G)) {k : G} (hk : k ∈ J ⊔ T) :
    ∃ j ∈ J, ∃ t ∈ T, k = j * t := by
  let S : Subgroup G :=
    { carrier := {k | ∃ j ∈ J, ∃ t ∈ T, k = j * t}
      one_mem' := ⟨1, J.one_mem, 1, T.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨j₁, hj₁, t₁, ht₁, rfl⟩ ⟨j₂, hj₂, t₂, ht₂, rfl⟩
        exact ⟨j₁ * (t₁ * j₂ * t₁⁻¹),
          J.mul_mem hj₁ ((Subgroup.mem_normalizer_iff.mp (hT ht₁) j₂).mp hj₂),
          t₁ * t₂, T.mul_mem ht₁ ht₂, by group⟩
      inv_mem' := by
        rintro _ ⟨j, hj, t, ht, rfl⟩
        refine ⟨t⁻¹ * j⁻¹ * t, ?_, t⁻¹, T.inv_mem ht, by group⟩
        simpa using (Subgroup.mem_normalizer_iff.mp (hT (T.inv_mem ht)) j⁻¹).mp (J.inv_mem hj) }
  exact (sup_le (fun j hj => ⟨j, hj, 1, T.one_mem, (mul_one j).symm⟩)
    (fun t ht => ⟨1, J.one_mem, t, ht, (one_mul t).symm⟩) : J ⊔ T ≤ S) hk

theorem exists_pow_mul_eq {J T : Subgroup G} (hT : T ≤ Subgroup.normalizer (J : Set G)) {j t : G}
    (hj : j ∈ J) (ht : t ∈ T) (m : ℕ) : ∃ j' ∈ J, (j * t) ^ m = j' * t ^ m := by
  induction m with
  | zero => exact ⟨1, J.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨j', hj', h⟩ := ih
    refine ⟨j' * (t ^ m * j * (t ^ m)⁻¹), J.mul_mem hj'
      ((Subgroup.mem_normalizer_iff.mp (hT (T.pow_mem ht m)) j).mp hj), ?_⟩
    rw [pow_succ, h]
    group

theorem exists_pow_mem_of_le_normalizer {J T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (J : Set G)) (hTp : IsPGroup 2 T) {k : G} (hk : k ∈ J ⊔ T) :
    ∃ n : ℕ, k ^ 2 ^ n ∈ J := by
  obtain ⟨j, hj, t, ht, rfl⟩ := exists_mul_eq_of_le_normalizer hT hk
  obtain ⟨n, hn⟩ := hTp ⟨t, ht⟩
  have hn' : t ^ 2 ^ n = 1 := congrArg Subtype.val hn
  obtain ⟨j', hj', h⟩ := exists_pow_mul_eq hT hj ht (2 ^ n)
  exact ⟨n, by rw [h, hn', mul_one]; exact hj'⟩

theorem isSylowIn_of_le {T M H : Subgroup G} (hT : IsSylowIn 2 T H) (hTM : T ≤ M) (hMH : M ≤ H) :
    IsSylowIn 2 T M := by
  refine ⟨hTM, hT.isPGroup, fun hdvd => hT.not_dvd_relIndex ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex T M H hTM hMH]
  exact Dvd.dvd.mul_right hdvd _

end Products

section Involutions

variable {K : Type} [Field K] {p f : ℕ}

theorem zP_ne_one (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2) : zP hU ≠ 1 := by
  intro h
  have h1 : zS hU ∈ suScalars p f K :=
    (QuotientGroup.eq_one_iff (N := suScalars p f K) (zS hU)).mp h
  obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp h1 :
    ((zS hU : ↥(unitarySU p f K 3)) : GL (Fin 3) K) ∈
      (Matrix.GeneralLinearGroup.scalar (Fin 3)).range)
  have hmat : matZ K = Matrix.scalar (Fin 3) (c : K) := by
    have : ((zS hU : ↥(unitarySU p f K 3)) : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar
        (Fin 3) c := hc.symm
    rw [show matZ K = (((zS hU : ↥(unitarySU p f K 3)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      from rfl, this]
    simp [Matrix.GeneralLinearGroup.coe_scalar]
  have e0 := congrFun (congrFun hmat 0) 0
  have e2 := congrFun (congrFun hmat 2) 2
  simp [matZ, Matrix.scalar_apply] at e0 e2
  exact two_ne_zero_of_unitaryFieldData hU hp2 (by linear_combination e2 - e0)

theorem zP_mem_centralizer_J12P (hU : UnitaryFieldData p f K) :
    zP hU ∈ Subgroup.centralizer (J12P p f K : Set (PSU3 p f K)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hxz : x * zS hU = zS hU * x :=
    Subtype.ext (Units.ext (mul_matZ_comm_of_mulVec_e2 (σ := hU.bar) (map_zero _)
      hU.bar.injective (mem_suStab.mp hx) ((mem_unitarySU_iff hU).mp x.2).2))
  show QuotientGroup.mk x * QuotientGroup.mk (zS hU) = QuotientGroup.mk (zS hU) * QuotientGroup.mk x
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxz]

theorem swP_not_mem_centralizer_J12P (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    swP hU ∉ Subgroup.centralizer (J12P p f K : Set (PSU3 p f K)) := by
  intro hc
  have h2 := two_ne_zero_of_unitaryFieldData hU hp2
  let M₀ : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; -1, 0, 0; 0, 0, 1]
  have hdet : M₀.det = 1 := by simp [M₀, Matrix.det_fin_three]
  have hu : (M₀.map hU.bar)ᵀ * M₀ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M₀, Matrix.mul_apply, Fin.sum_univ_three]
  have hx₀ : suMk hU M₀ hdet hu ∈ suStab K (p ^ f) 2 := by
    rw [mem_suStab, suMk_val]
    exact mulVec_e2_of_cols (by simp [M₀]) (by simp [M₀]) (by simp [M₀])
  have hcomm := Subgroup.mem_centralizer_iff.mp hc (QuotientGroup.mk (suMk hU M₀ hdet hu))
    ⟨_, hx₀, rfl⟩
  have hsw : swS hU * suMk hU M₀ hdet hu = suMk hU M₀ hdet hu * swS hU :=
    commute_of_proj_commute_two_U (by rw [pow_two, swS_mul_self]) hcomm.symm
  have hm : matSw K * M₀ = M₀ * matSw K :=
    congrArg (fun g : ↥(unitarySU p f K 3) => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hsw
  have := congrFun (congrFun hm 0) 0
  simp [matSw, M₀, Matrix.mul_apply, Fin.sum_univ_three] at this
  exact h2 (by linear_combination -this)

theorem card_kleinSub_le_four {G : Type*} [Group G] (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : Nat.card ↥(kleinSub a b ha hb hab) ≤ 4 := by
  classical
  have hsub : (kleinSub a b ha hb hab : Set G) ⊆ ↑({1, a, b, a * b} : Finset G) := by
    intro x hx
    rcases mem_kleinSub.mp hx with h | h | h | h <;> simp [h]
  calc Nat.card ↥(kleinSub a b ha hb hab)
      = Set.ncard (kleinSub a b ha hb hab : Set G) := (Nat.card_coe_set_eq _).symm
    _ ≤ Set.ncard (↑({1, a, b, a * b} : Finset G) : Set G) :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ({1, a, b, a * b} : Finset G).card := Set.ncard_coe_finset _
    _ ≤ 4 := Finset.card_le_four

theorem relIndex_V0P_le_two (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {M : Subgroup (PSU3 p f K)} (hzM : zP hU ∈ M) :
    (M ⊓ Subgroup.centralizer (J12P p f K : Set (PSU3 p f K))).relIndex (V0P hU) ≤ 2 := by
  have := hU.finite
  have hmem : zP hU ∈ M ⊓ Subgroup.centralizer (J12P p f K : Set (PSU3 p f K)) ⊓ V0P hU :=
    ⟨⟨hzM, zP_mem_centralizer_J12P hU⟩, mem_kleinSub.mpr (Or.inr (Or.inl rfl))⟩
  have hge : 2 ≤
      Nat.card ↥(M ⊓ Subgroup.centralizer (J12P p f K : Set (PSU3 p f K)) ⊓ V0P hU) := by
    have : Nontrivial
        ↥(M ⊓ Subgroup.centralizer (J12P p f K : Set (PSU3 p f K)) ⊓ V0P hU) :=
      nontrivial_of_ne (⟨zP hU, hmem⟩ :
        ↥(M ⊓ Subgroup.centralizer (J12P p f K : Set (PSU3 p f K)) ⊓ V0P hU)) 1
        (fun h => zP_ne_one hU hp2 (congrArg Subtype.val h))
    exact Finite.one_lt_card_iff_nontrivial.mpr this
  have hcard := Subgroup.relIndex_mul_card
    (M ⊓ Subgroup.centralizer (J12P p f K : Set (PSU3 p f K))) (V0P hU)
  have h4 : Nat.card ↥(V0P hU) ≤ 4 := card_kleinSub_le_four _ _ _ _ _
  by_contra hcon
  have h3 := Nat.mul_le_mul (Nat.succ_le_of_lt (not_le.mp hcon)) hge
  omega

end Involutions

end UK1

open UK1

theorem isE_one_K1 {p f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (hq5 : 5 ≤ p ^ f) {T : Subgroup (PSU3 p f K)}
    (hO2 : pCoreOf 2 (⊤ : Subgroup (PSU3 p f K)) = ⊥) (hT : IsSylowIn 2 T ⊤)
    (hVT : V0P hU ≤ T) (hzT : ∀ t ∈ T, t * zP hU = zP hU * t) :
    IsE 1 ⊤ T (V0P hU) (J12P p f K ⊔ T) := by
  have := hU.finite
  have : Fact p.Prime := ⟨hU.prime⟩
  have := hU.charP
  have hK := hU.card_eq_sq
  have hTN : T ≤ Subgroup.normalizer (J12P p f K : Set (PSU3 p f K)) := fun t ht =>
    mem_normalizer_J12P_of_commute_zP hU hp2 (hzT t ht)
  have hJK : J12P p f K ≤ J12P p f K ⊔ T := le_sup_left
  have hJn : ((J12P p f K).subgroupOf (J12P p f K ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).mpr (sup_le Subgroup.le_normalizer hTN)
  obtain ⟨eJ⟩ := nonempty_J12P_mulEquiv_sl2 (K := K) (p := p) (f := f) hK hp2
  have h4 : 4 ≤ Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p f) := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hK]
    omega
  let e := (Subgroup.subgroupOfEquivOfLe hJK).trans eJ
  have hTK : T ≤ J12P p f K ⊔ T := le_sup_right
  have hSyl : IsSylowIn 2 (T ⊓ (J12P p f K ⊔ T)) (J12P p f K ⊔ T) := by
    rw [inf_eq_left.mpr hTK]
    exact isSylowIn_of_le hT hTK le_top
  have hzK : zP hU ∈ J12P p f K ⊔ T := hTK (hVT (mem_kleinSub.mpr (Or.inr (Or.inl rfl))))
  exact e22s_isE_of_quasisimple_normal hO2 hSyl hJK hJn
    (CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 h4 e)
    (isSimpleGroup_quotient_center_of_equiv_sl2 h4 e)
    (fun z hz => ⟨1, by simpa using sq_eq_one_of_mem_center_of_equiv_sl2 e hz⟩)
    (fun k hk => exists_pow_mem_of_le_normalizer hTN hT.isPGroup hk)
    (le_inf hVT (hVT.trans hTK))
    (fun hle => swP_not_mem_centralizer_J12P hU hp2
      (hle (mem_kleinSub.mpr (Or.inr (Or.inr (Or.inl rfl))))))
    (relIndex_V0P_le_two hU hp2 hzK) (inf_le_left.trans hTK)

end CFSG.Quasithin.E22S
