module

public import CFSG.RankThree.PartOne.S11d.LieCentralizerTags
public import CFSG.RankThree.PartOne.KC.LinearCommutantBlocks
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCPrimary Matrix
open scoped commutatorElement

theorem eq_one_of_sq_eq_one_of_lt_two {F : Type*} [Field F] (h2 : (2 : F) = 0) {k : ℕ} (hk : k < 2)
    (u : GL (Fin k) F) (hu : u ^ 2 = 1) : u = 1 := by
  interval_cases k
  · exact Units.ext (Subsingleton.elim _ _)
  · have h1 : (u : Matrix (Fin 1) (Fin 1) F) * (u : Matrix (Fin 1) (Fin 1) F) = 1 := by
      have := congrArg (fun v : GL (Fin 1) F => (v : Matrix (Fin 1) (Fin 1) F)) hu
      simpa [pow_two] using this
    have h3 : (u : Matrix (Fin 1) (Fin 1) F) 0 0 * (u : Matrix (Fin 1) (Fin 1) F) 0 0 = 1 := by
      have := congrFun (congrFun h1 0) 0
      simpa [Matrix.mul_apply] using this
    have h4 : (u : Matrix (Fin 1) (Fin 1) F) 0 0 = 1 := by
      have h5 : ((u : Matrix (Fin 1) (Fin 1) F) 0 0 - 1) ^ 2 = 0 := by
        have : ((u : Matrix (Fin 1) (Fin 1) F) 0 0 - 1) ^ 2 =
            (u : Matrix (Fin 1) (Fin 1) F) 0 0 * (u : Matrix (Fin 1) (Fin 1) F) 0 0 - 1 -
              2 * ((u : Matrix (Fin 1) (Fin 1) F) 0 0 - 1) := by ring
        rw [this, h3, h2]
        ring
      have := pow_eq_zero_iff (two_ne_zero) |>.mp h5
      exact sub_eq_zero.mp this
    refine Units.ext ?_
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simpa using h4

open scoped _root_.Classical in
theorem exists_mult_two_of_involution {n : ℕ} {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0)
    {a s : GL (Fin n) K}
    (hx : Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))))
    (hs : s ^ 2 = 1) (hs1 : s ≠ 1) (hcomm : s * a = a * s) :
    ∃ b : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)),
      2 ≤ mult (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) b := by
  by_contra hno
  push Not at hno
  set x := Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) with hxdef
  have hsC : s ∈ Subgroup.centralizer ({a} : Set (GL (Fin n) K)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  rw [← range_commutantUnitsToGL_eq_centralizer (x := x) a rfl, ← range_blockTheta hx] at hsC
  obtain ⟨w, hw⟩ := hsC
  have hw2 : w ^ 2 = 1 := by
    apply blockTheta_injective hx
    rw [map_pow, hw, hs, map_one]
  have hw1 : w = 1 := by
    funext b
    have hb := congrFun hw2 b
    have h2b : (2 : Efac x b) = 0 := by
      rw [← map_ofNat (algebraMap K (Efac x b)) 2, h2, map_zero]
    exact eq_one_of_sq_eq_one_of_lt_two h2b (hno b) (w b) hb
  apply hs1
  rw [← hw, hw1, map_one]

theorem not_le_center_of_isQuasisimple {Γ : Type*} [Group Γ] {Q : Subgroup Γ}
    (hQ : CFSG.IsQuasisimple ↥Q) : ¬ Q ≤ Subgroup.center Γ := by
  intro hle
  have hperf := hQ.1
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have hcomm : commutator ↥Q = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _ b _
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hle a.2) b)
  have : (⊤ : Subgroup ↥Q) = ⊥ := by
    rw [← hperf.commutator_eq_top, hcomm]
  exact (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup ↥Q)).mp inferInstance this

theorem mem_normalizer_of_forall_conj {Γ : Type*} [Group Γ] {H : Subgroup Γ} {g : Γ}
    (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    g ∈ Subgroup.normalizer (H : Set Γ) :=
  Subgroup.mem_normalizer_iff.mpr fun x => ⟨h1 x, fun hx => by simpa [mul_assoc] using h2 _ hx⟩

theorem conj_mem_centralizer_of_commutator_central {Γ : Type*} [Group Γ] {A G H : Γ}
    (hGA : ⁅G, A⁆ ∈ Subgroup.center Γ) (hH : H ∈ Subgroup.centralizer ({A} : Set Γ)) :
    G * H * G⁻¹ ∈ Subgroup.centralizer ({A} : Set Γ) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hH ⊢
  set z : Γ := ⁅G, A⁆ with hz
  have hzc : ∀ g : Γ, g * z = z * g := Subgroup.mem_center_iff.mp hGA
  have hzi : ∀ g : Γ, g * z⁻¹ = z⁻¹ * g := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hGA)
  have e2 : G * A * G⁻¹ = z * A := by rw [hz, commutatorElement_def]; group
  have e1 : G⁻¹ * A * G = z⁻¹ * A := by
    have h3 : A = z * (G⁻¹ * A * G) := by
      calc A = G⁻¹ * (G * A * G⁻¹) * G := by group
        _ = G⁻¹ * (z * A) * G := by rw [e2]
        _ = (G⁻¹ * z) * (A * G) := by group
        _ = (z * G⁻¹) * (A * G) := by rw [hzc G⁻¹]
        _ = z * (G⁻¹ * A * G) := by group
    exact eq_inv_mul_of_mul_eq h3.symm
  calc G * H * G⁻¹ * A = G * H * (G⁻¹ * A * G) * G⁻¹ := by group
    _ = G * H * (z⁻¹ * A) * G⁻¹ := by rw [e1]
    _ = (G * H * z⁻¹) * A * G⁻¹ := by group
    _ = (G * (H * z⁻¹)) * A * G⁻¹ := by group
    _ = (G * (z⁻¹ * H)) * A * G⁻¹ := by rw [hzi H]
    _ = (G * z⁻¹) * (H * A) * G⁻¹ := by group
    _ = (z⁻¹ * G) * (H * A) * G⁻¹ := by rw [hzi G]
    _ = z⁻¹ * (G * (A * H) * G⁻¹) := by rw [hH]; group
    _ = z⁻¹ * ((G * A * G⁻¹) * (G * H * G⁻¹)) := by group
    _ = z⁻¹ * ((z * A) * (G * H * G⁻¹)) := by rw [e2]
    _ = A * (G * H * G⁻¹) := by group

open scoped _root_.Classical in
theorem psl_commuting_involution_data {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} {A : SpecialLinearGroup (Fin n) K} {y : projectiveSL n K}
    (hx : (proj n K A) ^ p = 1) (hy : y ^ 2 = 1) (hy1 : y ≠ 1)
    (hxy : proj n K A * y = y * proj n K A) :
    ∃ (c : Kˣ) (s' : GL (Fin n) K),
      (SpecialLinearGroup.toGL A) ^ p = GeneralLinearGroup.scalar (Fin n) c ∧ s' ^ 2 = 1 ∧
      s' ≠ 1 ∧ s' * SpecialLinearGroup.toGL A = SpecialLinearGroup.toGL A * s' := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨S, rfl⟩ := proj_surjective n K y
  have hAp : A ^ p ∈ scalars n K := proj_eq_one_iff.mp (by rw [map_pow]; exact hx)
  obtain ⟨c, hc, hAc⟩ := mem_scalars.mp hAp
  have hS2 : S ^ 2 ∈ scalars n K := proj_eq_one_iff.mp (by rw [map_pow]; exact hy)
  obtain ⟨c₂, hc₂, hSc⟩ := mem_scalars.mp hS2
  have hAS : ⁅A, S⁆ ∈ scalars n K := proj_eq_one_iff.mp (by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hxy)
  obtain ⟨ν, hν, hASν⟩ := mem_scalars.mp hAS
  set a : GL (Fin n) K := SpecialLinearGroup.toGL A with ha
  set s : GL (Fin n) K := SpecialLinearGroup.toGL S with hs
  have hap : a ^ p = GeneralLinearGroup.scalar (Fin n) c := by
    refine Units.ext ?_
    rw [GeneralLinearGroup.coe_scalar, ← hAc, ha, ← map_pow]
    rfl
  have hs2 : s ^ 2 = GeneralLinearGroup.scalar (Fin n) c₂ := by
    refine Units.ext ?_
    rw [GeneralLinearGroup.coe_scalar, ← hSc, hs, ← map_pow]
    rfl
  have hcomm0 : a * s * a⁻¹ * s⁻¹ = GeneralLinearGroup.scalar (Fin n) ν := by
    have h1 : SpecialLinearGroup.toGL ⁅A, S⁆ = a * s * a⁻¹ * s⁻¹ := by
      rw [map_commutatorElement, commutatorElement_def]
    rw [← h1]
    refine Units.ext ?_
    rw [GeneralLinearGroup.coe_scalar, ← hASν]
    rfl
  obtain ⟨μ, hμ⟩ : ∃ μ : Kˣ, μ ^ 2 = c₂ := by
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (c₂ : K)
    have hr0 : r ≠ 0 := fun h => c₂.ne_zero (by rw [hr, h, mul_zero])
    exact ⟨Units.mk0 r hr0, Units.ext (by simp [hr, sq])⟩
  set w : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) μ with hw
  set z : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) ν with hz
  have hwc : ∀ g : GL (Fin n) K, w * g = g * w := fun g => GeneralLinearGroup.scalar_commute μ g
  have hzc : ∀ g : GL (Fin n) K, z * g = g * z := fun g => GeneralLinearGroup.scalar_commute ν g
  have hwic : ∀ g : GL (Fin n) K, w⁻¹ * g = g * w⁻¹ := fun g => by
    have h1 : w * g = g * w := hwc g
    calc w⁻¹ * g = w⁻¹ * (g * w) * w⁻¹ := by group
      _ = w⁻¹ * (w * g) * w⁻¹ := by rw [h1]
      _ = g * w⁻¹ := by group
  set s' : GL (Fin n) K := w⁻¹ * s with hs'
  have hss : s = w * s' := by rw [hs']; group
  have hww : w ^ 2 = GeneralLinearGroup.scalar (Fin n) c₂ := by
    rw [hw, ← map_pow, hμ]
  have hs'2 : s' ^ 2 = 1 := by
    have h1 : s' ^ 2 = w⁻¹ * w⁻¹ * s ^ 2 := by
      calc s' ^ 2 = w⁻¹ * s * (w⁻¹ * s) := by rw [hs', pow_two]
        _ = w⁻¹ * (s * w⁻¹) * s := by group
        _ = w⁻¹ * (w⁻¹ * s) * s := by rw [← hwic s]
        _ = w⁻¹ * w⁻¹ * (s * s) := by group
        _ = w⁻¹ * w⁻¹ * s ^ 2 := by rw [pow_two]
    rw [h1, hs2, ← hww]
    group
  have hcz : a * s' * a⁻¹ * s'⁻¹ = z := by
    have h1 : a * s * a⁻¹ * s⁻¹ = a * s' * a⁻¹ * s'⁻¹ := by
      calc a * s * a⁻¹ * s⁻¹ = a * (w * s') * a⁻¹ * (w * s')⁻¹ := by rw [← hss]
        _ = w * (a * s' * a⁻¹ * s'⁻¹) * w⁻¹ := by
          have := hwc a
          calc a * (w * s') * a⁻¹ * (w * s')⁻¹ = (a * w) * s' * a⁻¹ * s'⁻¹ * w⁻¹ := by group
            _ = (w * a) * s' * a⁻¹ * s'⁻¹ * w⁻¹ := by rw [← this]
            _ = w * (a * s' * a⁻¹ * s'⁻¹) * w⁻¹ := by group
        _ = a * s' * a⁻¹ * s'⁻¹ := by
          rw [hwc (a * s' * a⁻¹ * s'⁻¹)]
          group
    rw [← h1, hcomm0]
  have hs'1 : s' ≠ 1 := by
    intro h1
    apply hy1
    rw [proj_eq_one_iff]
    have hsw : s = w := by rw [hss, h1, mul_one]
    refine mem_scalars.mpr ⟨μ, ?_, ?_⟩
    · have hdet : ((S : Matrix (Fin n) (Fin n) K)).det = 1 := S.2
      have h3 : ((w : Matrix (Fin n) (Fin n) K)).det = (μ : K) ^ n := by
        rw [hw, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have h4 : ((S : Matrix (Fin n) (Fin n) K)) = (w : Matrix (Fin n) (Fin n) K) := by
        rw [← hsw, hs]
        rfl
      rw [h4] at hdet
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, ← h3, hdet]; rfl)
    · have h4 : ((S : Matrix (Fin n) (Fin n) K)) = (w : Matrix (Fin n) (Fin n) K) := by
        rw [← hsw, hs]
        rfl
      rw [h4, hw, GeneralLinearGroup.coe_scalar]
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact absurd (Units.ext (Subsingleton.elim _ _)) hs'1
    · exact h0
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hz1 : z = 1 := by
    have h1 : (a * s' * a⁻¹) ^ 2 = 1 := by
      calc (a * s' * a⁻¹) ^ 2 = a * s' ^ 2 * a⁻¹ := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hs'2]; group
    have h2' : a * s' * a⁻¹ = z * s' := by
      rw [← hcz]; group
    rw [h2'] at h1
    have h3 : z ^ 2 = 1 := by
      calc z ^ 2 = z * z * (s' * s') * (s' * s')⁻¹ := by rw [pow_two]; group
        _ = z * s' * (z * s') * (s' * s')⁻¹ := by
          have : s' * z = z * s' := (hzc s').symm
          calc z * z * (s' * s') * (s' * s')⁻¹ = z * (z * s') * s' * (s' * s')⁻¹ := by group
            _ = z * (s' * z) * s' * (s' * s')⁻¹ := by rw [← this]
            _ = z * s' * (z * s') * (s' * s')⁻¹ := by group
        _ = (z * s') ^ 2 * (s' * s')⁻¹ := by rw [pow_two]
        _ = 1 := by
          rw [h1, one_mul, ← pow_two, hs'2]
          group
    have h4 : (ν : K) ^ 2 = 1 := by
      have h5 : GeneralLinearGroup.scalar (Fin n) (ν ^ 2) = 1 := by
        rw [map_pow]
        exact h3
      have h7 : ((GeneralLinearGroup.scalar (Fin n) (ν ^ 2) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [h5]
      rw [GeneralLinearGroup.coe_scalar, Units.val_one,
        ← map_one (Matrix.scalar (Fin n) : K →+* Matrix (Fin n) (Fin n) K)] at h7
      have h8 := Matrix.scalar_inj.mp h7
      rw [Units.val_pow_eq_pow_val] at h8
      exact h8
    have h7 : (ν : K) = 1 := by
      have h8 : ((ν : K) - 1) ^ 2 = 0 := by
        have : ((ν : K) - 1) ^ 2 = (ν : K) ^ 2 - 1 - 2 * ((ν : K) - 1) := by ring
        rw [this, h4, h2]
        ring
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h8)
    rw [hz, show ν = 1 from Units.ext h7, map_one]
  have hcomm' : s' * a = a * s' := by
    have h1 : a * s' * a⁻¹ * s'⁻¹ = 1 := by rw [hcz, hz1]
    calc s' * a = (a * s' * a⁻¹ * s'⁻¹)⁻¹ * (a * s') := by group
      _ = a * s' := by rw [h1]; group
  exact ⟨c, s', hap, hs'2, hs'1, hcomm'⟩

open scoped _root_.Classical in
theorem exists_mult_two_PSL {n p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) {A : SpecialLinearGroup (Fin n) K} {y : projectiveSL n K}
    (hx : (proj n K A) ^ p = 1) (hy : y ^ 2 = 1) (hy1 : y ≠ 1)
    (hxy : proj n K A * y = y * proj n K A) :
    ∃ b : primaryFactors (Matrix.toLin' ((SpecialLinearGroup.toGL A : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)),
      2 ≤ mult (Matrix.toLin' ((SpecialLinearGroup.toGL A : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) b := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨c, s', hap, hs'2, hs'1, hcomm'⟩ := psl_commuting_involution_data hx hy hy1 hxy
  set a : GL (Fin n) K := SpecialLinearGroup.toGL A with ha

  have hpK : (p : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm
  have hMp : (a : Matrix (Fin n) (Fin n) K) ^ p = algebraMap K (Matrix (Fin n) (Fin n) K) c := by
    have h1 : ((a ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (a : Matrix (Fin n) (Fin n) K) ^ p := Units.val_pow_eq_pow_val _ _
    rw [← h1, hap, GeneralLinearGroup.coe_scalar]
    rfl
  have haeval : Polynomial.aeval (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))
      (Polynomial.X ^ p - Polynomial.C (c : K)) = 0 := by
    have hX : Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) =
        Matrix.toLinAlgEquiv' (a : Matrix (Fin n) (Fin n) K) :=
      (KCLinComm.toLinAlgEquiv'_eq_toLin' _).symm
    rw [hX]
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [← map_pow, hMp, AlgEquiv.commutes, sub_self]
  have hx_sq : Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) :=
    KCPrimary.squarefree_minpoly_of_aeval_eq_zero
      (Polynomial.separable_X_pow_sub_C (c : K) hpK c.ne_zero).squarefree haeval
  exact exists_mult_two_of_involution h2 hx_sq hs'2 hs'1 hcomm'

open scoped _root_.Classical in
theorem psl_centralizer_component {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x y : projectiveSL n K}
    (hx : x ^ p = 1) (hy : y ^ 2 = 1) (hy1 : y ≠ 1) (hxy : x * y = y * x) :
    ∃ D : Subgroup (projectiveSL n K), CFSG.IsQuasisimple ↥D ∧
      D ≤ Subgroup.centralizer ({x} : Set (projectiveSL n K)) ∧
      (D.subgroupOf (Subgroup.centralizer ({x} : Set (projectiveSL n K)))).IsSubnormal := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨A, rfl⟩ := proj_surjective n K x
  obtain ⟨c, s', hap', hs'2, hs'1, hcomm'⟩ := psl_commuting_involution_data hx hy hy1 hxy
  set a : GL (Fin n) K := SpecialLinearGroup.toGL A with ha
  have hap : a ^ p = GeneralLinearGroup.scalar (Fin n) c := hap'
  have hpK : (p : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm
  have hMp : (a : Matrix (Fin n) (Fin n) K) ^ p = algebraMap K (Matrix (Fin n) (Fin n) K) c := by
    have h1 : ((a ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (a : Matrix (Fin n) (Fin n) K) ^ p := Units.val_pow_eq_pow_val _ _
    rw [← h1, hap, GeneralLinearGroup.coe_scalar]
    rfl
  have haeval : Polynomial.aeval (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))
      (Polynomial.X ^ p - Polynomial.C (c : K)) = 0 := by
    have hX : Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) =
        Matrix.toLinAlgEquiv' (a : Matrix (Fin n) (Fin n) K) :=
      (KCLinComm.toLinAlgEquiv'_eq_toLin' _).symm
    rw [hX]
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [← map_pow, hMp, AlgEquiv.commutes, sub_self]
  have hx_sq : Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) :=
    KCPrimary.squarefree_minpoly_of_aeval_eq_zero
      (Polynomial.separable_X_pow_sub_C (c : K) hpK c.ne_zero).squarefree haeval
  set X := Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) with hX
  obtain ⟨b, hb⟩ := exists_mult_two_of_involution h2 hx_sq hs'2 hs'1 hcomm'
  set B : Subgroup (GL (Fin n) K) := blockImage hx_sq b with hB
  have hBq : CFSG.IsQuasisimple ↥B := isQuasisimple_blockImage hx_sq hK b hb
  have hBdet : B ≤ (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range := blockImage_le_range_toGL hx_sq hK b hb
  have hBC : B ≤ Subgroup.centralizer ({a} : Set (GL (Fin n) K)) := by
    rw [← range_commutantUnitsToGL_eq_centralizer (x := X) a rfl]
    exact blockImage_le_range hx_sq b
  have hBnorm : ∀ g ∈ Subgroup.centralizer ({a} : Set (GL (Fin n) K)), ∀ f ∈ B,
      g * f * g⁻¹ ∈ B := by
    intro g hg f hf
    rw [← range_commutantUnitsToGL_eq_centralizer (x := X) a rfl] at hg
    exact conj_mem_blockImage hx_sq b hg hf
  set toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K := SpecialLinearGroup.toGL with htoGL
  set B' : Subgroup (SpecialLinearGroup (Fin n) K) := B.comap toGL with hB'
  have hB'map : B'.map toGL = B := Subgroup.map_comap_eq_self hBdet
  have hB'q : CFSG.IsQuasisimple ↥B' := by
    have e : ↥B' ≃* ↥B := (Subgroup.equivMapOfInjective B' toGL
      SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr hB'map)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hBq
  set CA : Subgroup (SpecialLinearGroup (Fin n) K) :=
    Subgroup.centralizer ({A} : Set (SpecialLinearGroup (Fin n) K)) with hCA
  have hGLcent : ∀ H : SpecialLinearGroup (Fin n) K, H ∈ CA → toGL H ∈
      Subgroup.centralizer ({a} : Set (GL (Fin n) K)) := by
    intro H hH
    have hH' : H * A = A * H := Subgroup.mem_centralizer_singleton_iff.mp hH
    rw [Subgroup.mem_centralizer_singleton_iff, ha, ← map_mul, ← map_mul, hH']
  have hB'CA : B' ≤ CA := by
    intro g hg
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h1 : toGL g ∈ Subgroup.centralizer ({a} : Set (GL (Fin n) K)) := hBC hg
    rw [Subgroup.mem_centralizer_singleton_iff, ha, ← map_mul, ← map_mul] at h1
    exact SpecialLinearGroup.toGL_injective h1
  have hB'nc : ¬ B' ≤ (proj n K).ker := by
    intro hle
    apply not_le_center_of_isQuasisimple hB'q
    rw [← scalars_eq_center n K, ← ker_proj]
    exact hle
  set D₀ : Subgroup (projectiveSL n K) := B'.map (proj n K) with hD₀
  have hD₀q : CFSG.IsQuasisimple ↥D₀ := CFSG.LocalCores.isQuasisimple_map hB'q (proj n K) hB'nc
  set C0 : Subgroup (projectiveSL n K) := CA.map (proj n K) with hC0
  set Cx : Subgroup (projectiveSL n K) :=
    Subgroup.centralizer ({proj n K A} : Set (projectiveSL n K)) with hCx
  have hC0Cx : C0 ≤ Cx := by
    rintro _ ⟨H, hH, rfl⟩
    have hH' : H * A = A * H := Subgroup.mem_centralizer_singleton_iff.mp hH
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul, hH']
  have hD₀C0 : D₀ ≤ C0 := Subgroup.map_mono hB'CA
  have hconj1 : ∀ g ∈ Cx, ∀ h ∈ C0, g * h * g⁻¹ ∈ C0 := by
    intro g hg h hh
    obtain ⟨G, rfl⟩ := proj_surjective n K g
    obtain ⟨H, hH, rfl⟩ := hh
    refine ⟨G * H * G⁻¹, ?_, by simp [map_mul, map_inv]⟩
    refine conj_mem_centralizer_of_commutator_central ?_ hH
    rw [← scalars_eq_center n K, ← proj_eq_one_iff, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hconj0 : ∀ g ∈ C0, ∀ d ∈ D₀, g * d * g⁻¹ ∈ D₀ := by
    intro g hg d hd
    obtain ⟨H, hH, rfl⟩ := hg
    obtain ⟨b₀, hb₀, rfl⟩ := hd
    refine ⟨H * b₀ * H⁻¹, ?_, by simp [map_mul, map_inv]⟩
    show toGL (H * b₀ * H⁻¹) ∈ B
    rw [map_mul, map_mul, map_inv]
    exact hBnorm _ (hGLcent H hH) _ hb₀
  have hCxN : Cx ≤ Subgroup.normalizer (C0 : Set (projectiveSL n K)) := fun g hg =>
    mem_normalizer_of_forall_conj (hconj1 g hg) (fun x hx => by
      simpa using hconj1 g⁻¹ (Cx.inv_mem hg) x hx)
  refine ⟨D₀, hD₀q, hD₀C0.trans hC0Cx, ?_⟩
  have hD1C1 : D₀.subgroupOf Cx ≤ C0.subgroupOf Cx := fun g hg => hD₀C0 hg
  have hn1 : (C0.subgroupOf Cx).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hC0Cx]
    exact hCxN
  have hn2 : ((D₀.subgroupOf Cx).subgroupOf (C0.subgroupOf Cx)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hD1C1]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hgC0 : (g : projectiveSL n K) ∈ C0 := hg
    constructor
    · intro hh
      exact hconj0 _ hgC0 _ hh
    · intro hh
      have := hconj0 _ (C0.inv_mem hgC0) _ hh
      exact Subgroup.mem_subgroupOf.mpr (by simpa [mul_assoc] using this)
  exact Subgroup.IsSubnormal.trans hD1C1 hn2.isSubnormal hn1.isSubnormal

theorem charP_two_of_card_eq_pow {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])

theorem exists_centralizer_component_of_mulEquiv {T P : Type*} [Group T] [Group P] (e : T ≃* P)
    {x : T}
    (h : ∃ D : Subgroup P, CFSG.IsQuasisimple ↥D ∧ D ≤ Subgroup.centralizer ({e x} : Set P) ∧
      (D.subgroupOf (Subgroup.centralizer ({e x} : Set P))).IsSubnormal) :
    ∃ D : Subgroup T, CFSG.IsQuasisimple ↥D ∧ D ≤ Subgroup.centralizer ({x} : Set T) ∧
      (D.subgroupOf (Subgroup.centralizer ({x} : Set T))).IsSubnormal := by
  obtain ⟨D, hq, hle, hsn⟩ := h
  refine ⟨D.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective D e.symm.toMonoidHom e.symm.injective) hq
  · rintro _ ⟨d, hd, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hle hd)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    apply e.injective
    simpa using h1
  · let ψ : ↥(Subgroup.centralizer ({x} : Set T)) →* ↥(Subgroup.centralizer ({e x} : Set P)) :=
      (e.toMonoidHom.comp (Subgroup.centralizer ({x} : Set T)).subtype).codRestrict _ fun g => by
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp g.2
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        change e g * e x = e x * e g
        rw [← map_mul, ← map_mul, h1]
    have hH : (D.map e.symm.toMonoidHom).subgroupOf (Subgroup.centralizer ({x} : Set T)) =
        (D.subgroupOf (Subgroup.centralizer ({e x} : Set P))).comap ψ := by
      ext g
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_map]
      constructor
      · rintro ⟨d, hd, hdg⟩
        have : e (g : T) = d := by rw [← hdg]; simp
        change e (g : T) ∈ D
        rw [this]
        exact hd
      · intro hg
        refine ⟨e (g : T), hg, ?_⟩
        simp
    rw [hH]
    exact hsn.comap ψ

theorem lieCentralizerComponentT_PSL : LieCentralizerComponentT .PSL := by
  intro T _ _ p n f hp hp5 hf hmodel x y hxp _ hy2 hy1 hxy
  obtain ⟨K, hKf, hKfin, hcard, ⟨e⟩⟩ :=
    LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hmodel
  have hchar : CharP K 2 := charP_two_of_card_eq_pow hcard
  have hK4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (p * f) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hp2 : p ≠ 2 := by omega
  refine exists_centralizer_component_of_mulEquiv e ?_
  refine psl_centralizer_component (x := e x) (y := e y) hK4 hp hp2 ?_ ?_ ?_ ?_
  · rw [← map_pow, hxp, map_one]
  · rw [← map_pow, hy2, map_one]
  · intro h1
    exact hy1 (e.injective (by rw [h1, map_one]))
  · rw [← map_mul, ← map_mul, hxy]

end CFSG.RankThree.PartOne
