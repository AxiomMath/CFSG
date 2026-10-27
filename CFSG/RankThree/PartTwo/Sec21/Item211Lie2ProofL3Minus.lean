module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofL3
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofL3Inner
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofU42Char
import CFSG.Quasithin.EmptyFaithful.E22SUFrame
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Lie2Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.LocalAnalysis.ComponentInitial

theorem ringEquiv_fix_of_two_pow {K : Type*} [Field K] (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ (σ c)) = c) {x : K} {m : ℕ} (hx : x ^ (2 ^ m) = 1) : σ x = x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero m two_ne_zero)] at hx
    exact zero_ne_one hx
  set u : Kˣ := Units.mk0 x hx0 with hu
  have hu2 : u ^ (2 ^ m) = 1 := Units.ext (by simp [hu, hx])
  set n := orderOf u with hn
  have hprim : IsPrimitiveRoot x n := by
    have := IsPrimitiveRoot.orderOf u
    rw [← hn] at this
    exact (IsPrimitiveRoot.coe_units_iff).mpr this
  have hσn : (σ x) ^ n = 1 := by rw [← map_pow, hprim.pow_eq_one, map_one]
  have hfin : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.mpr ⟨2 ^ m, by positivity, hu2⟩
  have hn0 : n ≠ 0 := hfin.orderOf_pos.ne'
  have : NeZero n := ⟨hn0⟩
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hσn
  have h3 : x ^ (i ^ 3) = x := by
    have e1 : σ (σ x) = x ^ (i ^ 2) := by rw [← hi, map_pow, ← hi, ← pow_mul, sq]
    have e2 : σ (σ (σ x)) = x ^ (i ^ 3) := by rw [e1, map_pow, ← hi, ← pow_mul]; ring_nf
    rw [← e2, hσ]
  have hndvd : n ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hu2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hndvd
  rcases (by omega : 1 ≤ i ∨ i = 0) with hi1 | rfl
  · have hdvd : n ∣ i ^ 3 - 1 := by
      have : x ^ (i ^ 3 - 1) = 1 := by
        have h4 : x ^ (i ^ 3 - 1) * x = x := by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hi1), h3]
        calc x ^ (i ^ 3 - 1) = x ^ (i ^ 3 - 1) * x * x⁻¹ := by field_simp
          _ = 1 := by rw [h4, mul_inv_cancel₀ hx0]
      exact (hprim.pow_eq_one_iff_dvd _).mp this
    have hfac : i ^ 3 - 1 = (i - 1) * (i ^ 2 + i + 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    have hodd : Nat.Coprime n (i ^ 2 + i + 1) := by
      rw [hj]
      apply Nat.Coprime.pow_left
      rw [Nat.coprime_two_left]
      have : Even (i ^ 2 + i) := by
        rw [show i ^ 2 + i = i * (i + 1) by ring]
        exact Nat.even_mul_succ_self i
      exact this.add_one
    rw [hfac] at hdvd
    obtain ⟨k, hk⟩ := hodd.dvd_of_dvd_mul_right hdvd
    rw [← hi, show i = n * k + 1 by omega, pow_succ, pow_mul, hprim.pow_eq_one, one_pow,
      one_mul]
  · rw [pow_zero] at hi
    have : x = 1 := by
      have := congrArg σ.symm hi
      rw [map_one, RingEquiv.symm_apply_apply] at this
      exact this.symm
    rw [this, map_one]

@[expose] def L3MinusFor (Y : Type*) [Group Y] : Prop :=
  ∀ T : Subgroup (MulAut Y), T ≤ (MulAut.conj : Y →* MulAut Y).range → IsElemAbelian 2 T →
    Nat.card T = 4 → ∀ b : MulAut Y, b ^ 3 = 1 → b ∈ Subgroup.centralizer (T : Set (MulAut Y)) →
      ∀ W : Subgroup (MulAut Y), IsPGroup 2 W →
        W ≤ (MulAut.conj : Y →* MulAut Y).range ⊓ Subgroup.centralizer (T : Set (MulAut Y)) →
        W ≤ Subgroup.centralizer ({b} : Set (MulAut Y))

theorem l3MinusFor_of_hom {X Y : Type*} [Group X] [Group Y] (Φ : MulAut X →* MulAut Y)
    (hΦ : Function.Injective Φ)
    (hinn : ∀ x : X, Φ (MulAut.conj x) ∈ (MulAut.conj : Y →* MulAut Y).range)
    (hY : L3MinusFor Y) : L3MinusFor X := by
  intro T hTinn hTe hT4 b hb3 hbT W hW2 hWT
  have hinn' : ∀ τ ∈ (MulAut.conj : X →* MulAut X).range,
      Φ τ ∈ (MulAut.conj : Y →* MulAut Y).range := by
    rintro _ ⟨x, rfl⟩
    exact hinn x
  have hcent : ∀ {S : Subgroup (MulAut X)} {τ : MulAut X},
      τ ∈ Subgroup.centralizer (S : Set (MulAut X)) →
      Φ τ ∈ Subgroup.centralizer ((S.map Φ : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
    intro S τ hτ
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hτ s hs]
  have hTe' : IsElemAbelian 2 (T.map Φ) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      simp only [Subgroup.coe_mul]
      have h0 : x * y = y * x := congrArg Subtype.val (hTe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [← map_mul, ← map_mul, h0]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hTe.2 x hx, map_one]
  have hT4' : Nat.card (T.map Φ) = 4 := by rw [Subgroup.card_map_of_injective hΦ, hT4]
  have hW2' : IsPGroup 2 (W.map Φ) := hW2.map Φ
  have hWT' : W.map Φ ≤ (MulAut.conj : Y →* MulAut Y).range ⊓
      Subgroup.centralizer ((T.map Φ : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
    rintro _ ⟨w, hw, rfl⟩
    exact Subgroup.mem_inf.mpr ⟨hinn' w (hWT hw).1, hcent (hWT hw).2⟩
  have h := hY (T.map Φ) (fun _ ⟨t, ht, e⟩ => e ▸ hinn' t (hTinn ht)) hTe' hT4' (Φ b)
    (by rw [← map_pow, hb3, map_one]) (hcent hbT) (W.map Φ) hW2' hWT'
  intro w hw
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (h ⟨w, hw, rfl⟩)
  rw [← map_mul, ← map_mul] at h1
  exact hΦ h1

theorem l3MinusFor_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : L3MinusFor Y) : L3MinusFor X :=
  l3MinusFor_of_hom (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
    (fun x => ⟨e x, by
      ext y
      simp [MulAut.conj_apply, MulAut.congr_apply]⟩) hY

theorem l3MinusFor_of_perfect {S : Type*} [Group S] [Group.IsPerfect S]
    (hP : L3MinusFor (S ⧸ Subgroup.center S)) : L3MinusFor S := by
  refine l3MinusFor_of_hom (KFacts.centerDescend S) (fun α β hαβ => ?_) (fun s => ⟨s, ?_⟩) hP
  · refine Sec4.mulAut_eq_of_inv_mul_mem_center fun x => ?_
    have h1 := congrArg (fun σ : MulAut (S ⧸ Subgroup.center S) =>
      σ (x : S ⧸ Subgroup.center S)) hαβ
    simp only [KFacts.centerDescend_mk] at h1
    exact (QuotientGroup.eq).mp h1.symm
  · ext x
    induction x using QuotientGroup.induction_on with
    | H y => rfl

section Linear

open LinearFlag
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem center_projectiveSL_three_eq_bot' : Subgroup.center (projectiveSL 3 K) = ⊥ := by
  have hsimple : IsSimpleGroup (projectiveSL 3 K) := by
    have := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := 3) (by omega)
      (Or.inl le_rfl)).2.1
    exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K).symm.isSimpleGroup
  have hperf : Group.IsPerfect (projectiveSL 3 K) := by
    have := CFSG.LinearGroups.linear_projective_perfect (K := K) (n := 3) (by omega)
      (Or.inl le_rfl)
    exact Group.IsPerfect.ofSurjective
      (f := (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K).toMonoidHom)
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K).surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (projectiveSL 3 K)) with h | h
  · exact h
  · exfalso
    have h1 := (commutator_eq_bot_iff_center_eq_top (projectiveSL 3 K)).2 h
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact top_ne_bot h1

theorem proj_eq_proj_iff {x y : SL(3, K)} :
    proj 3 K x = proj 3 K y ↔
      ∃ c : K, c ^ 3 = 1 ∧ (y : Matrix (Fin 3) (Fin 3) K) = c • (x : Matrix (Fin 3) (Fin 3) K) := by
  change (x : SL(3, K) ⧸ scalars 3 K) = (y : SL(3, K) ⧸ scalars 3 K) ↔ _
  rw [QuotientGroup.eq]
  constructor
  · intro h
    obtain ⟨c, hc, hxy⟩ := mem_scalars.mp h
    refine ⟨c, by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one], ?_⟩
    have e : (y : Matrix (Fin 3) (Fin 3) K) =
        (x : Matrix (Fin 3) (Fin 3) K) * ((x⁻¹ * y : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    rw [e, hxy, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one]
  · rintro ⟨c, hc, hxy⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hc
      exact zero_ne_one hc
    refine mem_scalars.mpr ⟨Units.mk0 c hc0, Units.ext (by simp [hc]), ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, hxy, Matrix.mul_smul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_mul, Matrix.SpecialLinearGroup.det_coe,
      one_smul, Units.val_mk0, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem sum_ne_zero_of_signs (h3 : (3 : K) ≠ 0) {d : Fin 3 → K} (hd : ∀ i, d i * d i = 1) :
    ∑ i, d i ≠ 0 := by
  rw [Fin.sum_univ_three]
  intro hs
  apply h3
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  linear_combination (-(1 - 2 * d 1 * d 2)) * h0 + (-(1 - 2 * d 0 * d 2)) * h1 +
    (-(1 - 2 * d 0 * d 1)) * h2 + (d 0 + d 1 + d 2 - 2 * d 0 * d 1 * d 2) * hs

theorem commute_of_isDiag {A B : GL (Fin 3) K} (hA : (A : Matrix (Fin 3) (Fin 3) K).IsDiag)
    (hB : (B : Matrix (Fin 3) (Fin 3) K).IsDiag) : A * B = B * A := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← hA.diagonal_diag, ← hB.diagonal_diag,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem l3MinusFor_projectiveSL [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK3 : (3 : K) ≠ 0) : L3MinusFor (projectiveSL 3 K) := by
  classical
  intro T hTinn hTe hT4 b hb3 hbT W hW2 hWT
  have hK2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
  have hZ := center_projectiveSL_three_eq_bot' (K := K)
  have hinj := conj_injective' hZ
  set A := T.comap (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)) with hAdef
  have hAe : IsElemAbelian 2 A := Item211LieProof.isElemAbelian_comap_of_injective hinj hTe
  have hA4 : 4 ≤ Nat.card A := by
    rw [hAdef, Item211LieProof.card_comap_conj hZ hTinn, hT4]
  obtain ⟨g, hg⟩ := CFSG.Quasithin.E22S.exists_frame hp2 hAe
  have hbA : ∀ a ∈ A, b a = a := by
    intro a ha
    apply hinj
    have h1 := Subgroup.mem_centralizer_iff.mp hbT _ ha
    rw [← mul_conj_mul_inv', ← h1, mul_inv_cancel_right]
  obtain ⟨M, σ, ε, hε, hbMσ⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 b
  have hε0 : ε = 0 := by
    by_contra hne
    obtain rfl : ε = 1 := by omega
    set e := conjAut 3 K M * fieldAut 3 K σ with he_def
    have he : e ∈ semilinearAutGroup 3 K := mem_semilinearAutGroup_iff.mpr ⟨M, σ, rfl⟩
    have hb' : b = e * dualAut 3 K := by rw [hbMσ, pow_one]
    have hb3' : (e * (dualAut 3 K * e * dualAut 3 K) * e) * dualAut 3 K = 1 := by
      rw [← hb3, hb', pow_three]
      group
    have hmem : e * (dualAut 3 K * e * dualAut 3 K) * e ∈ semilinearAutGroup 3 K :=
      mul_mem (mul_mem he (dualAut_mul_mul_dualAut_mem he)) he
    apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := K) (n := 3) le_rfl
    rw [eq_inv_of_mul_eq_one_right hb3']
    exact inv_mem hmem
  subst hε0
  rw [pow_zero, mul_one] at hbMσ
  have hσ3 : ∀ c, σ (σ (σ c)) = c := by
    obtain ⟨N₃, hN₃⟩ : ∃ N₃ : GL (Fin 3) K, b ^ 3 = conjAut 3 K N₃ * fieldAut 3 K (σ * σ * σ) :=
      ⟨_, by rw [pow_three', hbMσ, conjAut_mul_fieldAut_mul, conjAut_mul_fieldAut_mul]⟩
    rw [hb3] at hN₃
    obtain ⟨hσ1, -⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl _ _ hN₃.symm
    intro c
    have := congrArg (fun τ : K ≃+* K => τ c) hσ1
    simpa using this
  set σG := Matrix.GeneralLinearGroup.map (n := Fin 3) (σ : K →+* K) with hσG
  have hσGval : ∀ X : GL (Fin 3) K,
      ((σG X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (X : Matrix (Fin 3) (Fin 3) K).map σ :=
    fun X => rfl
  have hact : ∀ x y : SL(3, K), b (proj 3 K x) = proj 3 K y ↔
      ∃ u : Kˣ, Matrix.SpecialLinearGroup.toGL y =
        Matrix.GeneralLinearGroup.scalar (Fin 3) u *
          (M * σG (Matrix.SpecialLinearGroup.toGL x) * M⁻¹) ∧ u ^ 3 = 1 := by
    intro x y
    rw [hbMσ, MulAut.mul_apply, fieldAut_proj, conjAut_proj, proj_eq_proj_iff, coe_slConjugation,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    constructor
    · rintro ⟨c, hc3, hc⟩
      have hc0 : c ≠ 0 := fun h => by rw [h, zero_pow (by norm_num)] at hc3; exact zero_ne_one hc3
      refine ⟨Units.mk0 c hc0, Units.ext ?_, Units.ext (by simp [hc3])⟩
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hc, Units.val_mul, Units.val_mul,
        Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, hσGval]
      rfl
    · rintro ⟨u, hu, hu3⟩
      refine ⟨u, by rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one], ?_⟩
      have := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) hu
      simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Units.val_mul,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at this
      rw [this, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, hσGval]
      rfl
  set Gg := Matrix.SpecialLinearGroup.toGL g with hGg
  set N : GL (Fin 3) K := Gg * M * (σG Gg)⁻¹ with hN
  have hconj : ∀ x : SL(3, K), Matrix.SpecialLinearGroup.toGL (g * x * g⁻¹) =
      Gg * Matrix.SpecialLinearGroup.toGL x * Gg⁻¹ := by
    intro x
    rw [map_mul, map_mul, map_inv]
  have hsign : ∀ x ∈ CFSG.Quasithin.E22S.invLifts A hAe, ∀ i,
      CFSG.Quasithin.E22S.dg g x i * CFSG.Quasithin.E22S.dg g x i = 1 :=
    fun x hx i => CFSG.Quasithin.E22S.dg_sq (hg x hx) hx.2 i
  have hDmat : ∀ x ∈ CFSG.Quasithin.E22S.invLifts A hAe,
      ((Matrix.SpecialLinearGroup.toGL (g * x * g⁻¹) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal (CFSG.Quasithin.E22S.dg g x) :=
    fun x hx => CFSG.Quasithin.E22S.conj_eq_diagonal (hg x hx)
  have hNcomm : ∀ x ∈ CFSG.Quasithin.E22S.invLifts A hAe,
      N * Matrix.SpecialLinearGroup.toGL (g * x * g⁻¹) =
        Matrix.SpecialLinearGroup.toGL (g * x * g⁻¹) * N := by
    intro x hx
    set Dg := Matrix.SpecialLinearGroup.toGL (g * x * g⁻¹) with hDg
    have hσD : σG Dg = Dg := by
      apply Units.ext
      rw [hσGval, hDmat x hx, Matrix.diagonal_map (map_zero σ)]
      congr 1
      funext i
      rcases mul_self_eq_one_iff.mp (hsign x hx i) with h | h
      · simp [h]
      · simp [h]
    obtain ⟨u, hu, -⟩ := (hact x x).mp (hbA _ hx.1)
    set Z := M * σG (Matrix.SpecialLinearGroup.toGL x) * M⁻¹ with hZdef
    have hx' : Matrix.SpecialLinearGroup.toGL x = Gg⁻¹ * Dg * Gg := by
      rw [hDg, hconj]
      group
    have e1 : N * Dg * N⁻¹ = Gg * Z * Gg⁻¹ := by
      rw [hZdef, hx', map_mul, map_mul, map_inv, hσD, hN]
      group
    have hD : Dg = Matrix.GeneralLinearGroup.scalar (Fin 3) u * (N * Dg * N⁻¹) := by
      rw [e1]
      calc Dg = Gg * Matrix.SpecialLinearGroup.toGL x * Gg⁻¹ := by rw [hDg, hconj]
        _ = Gg * (Matrix.GeneralLinearGroup.scalar (Fin 3) u * Z) * Gg⁻¹ := by rw [← hu]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) u * (Gg * Z * Gg⁻¹) := by
          rw [← mul_assoc, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u Gg).eq]
          group
    have hu1 : u = 1 := by
      have htr := congrArg (fun X : GL (Fin 3) K => Matrix.trace (X : Matrix (Fin 3) (Fin 3) K)) hD
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
        Matrix.trace_units_conj, smul_eq_mul] at htr
      have hne : Matrix.trace (Dg : Matrix (Fin 3) (Fin 3) K) ≠ 0 := by
        rw [hDmat x hx, Matrix.trace_diagonal]
        exact sum_ne_zero_of_signs hK3 (hsign x hx)
      apply Units.ext
      have : (1 - (u : K)) * Matrix.trace (Dg : Matrix (Fin 3) (Fin 3) K) = 0 := by
        linear_combination htr
      rw [Units.val_one]
      exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)).symm
    rw [hu1, map_one, one_mul] at hD
    calc N * Dg = N * Dg * N⁻¹ * N := by group
      _ = Dg * N := by rw [← hD]
  have hNdiag : (N : Matrix (Fin 3) (Fin 3) K).IsDiag := by
    intro i j hij
    obtain ⟨x, hx, hxij⟩ := CFSG.Quasithin.E22S.exists_sign_neg_one hAe hA4 hg hij
    have h1 := congrFun (congrFun (congrArg (fun X : GL (Fin 3) K =>
      (X : Matrix (Fin 3) (Fin 3) K)) (hNcomm x hx)) i) j
    simp only [Units.val_mul, hDmat x hx, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have hne : CFSG.Quasithin.E22S.dg g x j - CFSG.Quasithin.E22S.dg g x i ≠ 0 := by
      intro h0
      have hji := sub_eq_zero.mp h0
      have h2 := hsign x hx i
      rw [hji] at hxij
      rw [hxij] at h2
      apply hK2
      linear_combination -h2
    have : (N : Matrix (Fin 3) (Fin 3) K) i j *
        (CFSG.Quasithin.E22S.dg g x j - CFSG.Quasithin.E22S.dg g x i) = 0 := by
      linear_combination h1
    exact (mul_eq_zero.mp this).resolve_right hne
  intro w hw
  obtain ⟨y, rfl⟩ := (Subgroup.mem_inf.mp (hWT hw)).1
  have hyA : ∀ a ∈ A, y * a = a * y := by
    intro a ha
    have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hWT hw)).2 _ ha
    rw [← map_mul, ← map_mul] at h1
    exact (hinj h1).symm
  obtain ⟨m, hm⟩ := hW2 ⟨MulAut.conj y, hw⟩
  have hym : y ^ (2 ^ m) = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact congrArg Subtype.val hm
  obtain ⟨Y, rfl⟩ := proj_surjective 3 K y
  have hYc : ∀ x ∈ CFSG.Quasithin.E22S.invLifts A hAe, Y * x = x * Y := by
    intro x hx
    exact (CFSG.Quasithin.E22S.commute_of_proj_commute_two hx.2 (hyA _ hx.1).symm).symm
  have hYdiag := CFSG.Quasithin.E22S.isDiagIn_of_commute hK2 hAe hA4 hg hYc
  set e := CFSG.Quasithin.E22S.dg g Y with he
  set Eg := Matrix.SpecialLinearGroup.toGL (g * Y * g⁻¹) with hEg
  have hEmat : (Eg : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal e :=
    CFSG.Quasithin.E22S.conj_eq_diagonal hYdiag
  obtain ⟨ζ, hζ3, hζ⟩ := mem_scalars.mp (proj_eq_one_iff.mp (by rw [map_pow, hym]))
  have hepow : ∀ i, e i ^ (2 ^ m) = (ζ : K) := by
    intro i
    have h1 : Eg ^ (2 ^ m) = Gg * Matrix.SpecialLinearGroup.toGL (Y ^ (2 ^ m)) * Gg⁻¹ := by
      rw [hEg, hconj, map_pow, conj_pow]
    have h2 : ((Matrix.SpecialLinearGroup.toGL (Y ^ (2 ^ m)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) (ζ : K) := hζ
    have h3 : Matrix.SpecialLinearGroup.toGL (Y ^ (2 ^ m)) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) ζ := Units.ext (by
      rw [h2, Matrix.GeneralLinearGroup.coe_scalar])
    rw [h3, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ Gg).eq, mul_inv_cancel_right]
      at h1
    have h4 := congrFun (congrFun (congrArg (fun X : GL (Fin 3) K =>
      (X : Matrix (Fin 3) (Fin 3) K)) h1) i) i
    simp only [Units.val_pow_eq_pow_val, hEmat, Matrix.diagonal_pow,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Pi.pow_apply] at h4
    exact h4
  have hζ0 : (ζ : K) ≠ 0 := ζ.ne_zero
  have he0 : ∀ i, e i ≠ 0 := fun i h => hζ0 (by rw [← hepow i, h, zero_pow (by positivity)])
  have hfix : ∀ i, σ (e i / e 2) = e i / e 2 := fun i =>
    ringEquiv_fix_of_two_pow σ hσ3 (m := m) (by rw [div_pow, hepow i, hepow 2, div_self hζ0])
  set c := σ (e 2) / e 2 with hcdef
  have hσe : ∀ i, σ (e i) = c * e i := by
    intro i
    have h2 := he0 2
    have h1 : e i = e 2 * (e i / e 2) := by field_simp
    calc σ (e i) = σ (e 2) * σ (e i / e 2) := by rw [← map_mul, ← h1]
      _ = c * e i := by rw [hfix i, hcdef]; field_simp
  have hc3 : c ^ 3 = 1 := by
    have hp := CFSG.Quasithin.E22S.dg_prod hYdiag
    rw [← he, Fin.prod_univ_three] at hp
    have h1 := congrArg σ hp
    rw [map_mul, map_mul, hσe, hσe, hσe, map_one] at h1
    linear_combination h1 - c ^ 3 * hp
  have hc0 : c ≠ 0 := fun h => by rw [h, zero_pow (by norm_num)] at hc3; exact zero_ne_one hc3
  have hbY : b (proj 3 K Y) = proj 3 K Y := by
    refine (hact Y Y).mpr ⟨(Units.mk0 c hc0)⁻¹, ?_, ?_⟩
    · have hσE : σG Eg = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * Eg := by
        apply Units.ext
        rw [hσGval, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hEmat,
          Matrix.diagonal_map (map_zero σ), Units.val_mk0, Matrix.scalar_apply,
          Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        exact hσe i
      have hNE : N * σG Eg = σG Eg * N := by
        apply commute_of_isDiag hNdiag
        rw [hσGval, hEmat, Matrix.diagonal_map (map_zero σ)]
        exact Matrix.isDiag_diagonal _
      have hY' : Matrix.SpecialLinearGroup.toGL Y = Gg⁻¹ * Eg * Gg := by
        rw [hEg, hconj]
        group
      have e1 : M * σG (Matrix.SpecialLinearGroup.toGL Y) * M⁻¹ =
          Gg⁻¹ * (N * σG Eg * N⁻¹) * Gg := by
        rw [hY', map_mul, map_mul, map_inv, hN]
        group
      rw [e1, hNE, mul_inv_cancel_right, hσE, hY', map_inv]
      have hcomm := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (Units.mk0 c hc0) Gg⁻¹).eq
      calc Gg⁻¹ * Eg * Gg = (Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0))⁻¹ *
            ((Gg⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0)) * Eg * Gg) := by
            rw [hcomm]
            group
        _ = _ := by group
    · rw [inv_pow]
      apply inv_eq_one.mpr
      apply Units.ext
      simp [hc3]
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := mul_conj_mul_inv' b (proj 3 K Y)
  rw [hbY] at h1
  calc MulAut.conj (proj 3 K Y) * b = b * MulAut.conj (proj 3 K Y) * b⁻¹ * b := by rw [h1]
    _ = b * MulAut.conj (proj 3 K Y) := by group

end Linear

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem center_unitaryPSU_three_eq_bot (hq : 2 < p ^ f) :
    Subgroup.center (unitaryPSU h 3) = ⊥ := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hnq : (3, p ^ f) ≠ (3, 2) := fun h' => by
    have := (Prod.mk.inj h').2
    omega
  set E := unitaryPSUEquiv h (n := 3) (by norm_num) with hE
  have : IsSimpleGroup (unitaryPSU h 3) := by
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK 3 le_rfl hnq
    exact E.isSimpleGroup
  have : Group.IsPerfect (unitaryPSU h 3) := by
    have := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (K := K) hK le_rfl hnq
    exact Group.IsPerfect.ofSurjective (f := unitaryProj h 3) (unitaryProj_surjective h 3)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (unitaryPSU h 3)) with h1 | h1
  · exact h1
  · exfalso
    have h2 := (commutator_eq_bot_iff_center_eq_top (unitaryPSU h 3)).2 h1
    rw [Group.IsPerfect.commutator_eq_top] at h2
    exact top_ne_bot h2

theorem unitaryProj_eq_iff {g g' : unitarySU p f K 3} :
    unitaryProj h 3 g = unitaryProj h 3 g' ↔
      ∃ c : Kˣ, (g' : GL (Fin 3) K) = (g : GL (Fin 3) K) *
        Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  change (g : unitaryPSU h 3) = (g' : unitaryPSU h 3) ↔ _
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨c, -, -, hc⟩
    refine ⟨c, ?_⟩
    rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  · rintro ⟨c, hc⟩
    rw [unitaryScalars_eq h (by norm_num), Subgroup.mem_subgroupOf]
    refine ⟨c, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hc, inv_mul_cancel_left]

theorem l3MinusFor_unitaryPSU (hp2 : p ≠ 2) (hK3 : (3 : K) ≠ 0) (hq : 2 < p ^ f) :
    L3MinusFor (unitaryPSU h 3) := by
  classical
  intro T hTinn hTe hT4 b hb3 hbT W hW2 hWT
  have := h.finite
  have hK2 := CFSG.Quasithin.E22S.two_ne_zero_of_unitaryFieldData h hp2
  have hZ := center_unitaryPSU_three_eq_bot h hq
  have hinj := conj_injective' hZ
  set A := T.comap (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)) with hAdef
  have hAe : IsElemAbelian 2 A := Item211LieProof.isElemAbelian_comap_of_injective hinj hTe
  have hA4 : 4 ≤ Nat.card A := by
    rw [hAdef, Item211LieProof.card_comap_conj hZ hTinn, hT4]
  set Eq := unitaryPSUEquiv h (n := 3) (by norm_num) with hEq
  set A' := A.map Eq.toMonoidHom with hA'
  have hEqmk : ∀ g : unitarySU p f K 3, Eq (unitaryProj h 3 g) =
      (g : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) :=
    fun g => unitaryPSUEquiv_unitaryProj h _ g
  have hA'e : IsElemAbelian 2 A' := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      simp only [Subgroup.coe_mul]
      have h0 : x * y = y * x := congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [← map_mul, ← map_mul, h0]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hAe.2 x hx, map_one]
  have hA'4 : 4 ≤ Nat.card A' := by
    rw [hA', Subgroup.card_map_of_injective Eq.injective]
    exact hA4
  have hmemA' : ∀ g : unitarySU p f K 3, (g : CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) ∈ A' ↔ unitaryProj h 3 g ∈ A := by
    intro g
    rw [← hEqmk, hA']
    constructor
    · rintro ⟨a, ha, hae⟩
      rw [MulEquiv.coe_toMonoidHom] at hae
      rwa [← Eq.injective hae]
    · intro hg
      exact ⟨_, hg, rfl⟩
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.E22S.exists_unitary_frame h hp2 hA'e
  have hbA : ∀ a ∈ A, b a = a := by
    intro a ha
    apply hinj
    have h1 := Subgroup.mem_centralizer_iff.mp hbT _ ha
    rw [← mul_conj_mul_inv', ← h1, mul_inv_cancel_right]
  obtain ⟨A₀, σ, hbAσ⟩ := exists_psuConj_mul_psuField hq b
  have hσ3 : ∀ c, σ (σ (σ c)) = c := by
    obtain ⟨N₃, hN₃⟩ : ∃ N₃ : unitaryIsom3 h, b ^ 3 = psuConj h N₃ * psuField h (σ * σ * σ) :=
      ⟨_, by rw [pow_three', hbAσ, psuConj_mul_psuField_mul, psuConj_mul_psuField_mul]⟩
    rw [hb3] at hN₃
    obtain ⟨hσ1, -⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ hN₃.symm
    intro c
    have := congrArg (fun τ : K ≃+* K => τ c) hσ1
    simpa using this
  set σG := glAut (ι := Fin 3) (K := K) σ with hσG
  have hσGval : ∀ X : GL (Fin 3) K,
      ((σG X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (X : Matrix (Fin 3) (Fin 3) K).map σ :=
    fun X => coe_glAut σ X
  have hact : ∀ x y : unitarySU p f K 3, b (unitaryProj h 3 x) = unitaryProj h 3 y ↔
      ∃ u : Kˣ, (y : GL (Fin 3) K) = ((A₀ : GL (Fin 3) K) * σG (x : GL (Fin 3) K) *
        (A₀ : GL (Fin 3) K)⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
    intro x y
    rw [hbAσ, MulAut.mul_apply]
    change psuConj h A₀ (psuField h σ (x : unitaryPSU h 3)) = _ ↔ _
    rw [psuField_mk, psuConj_mk]
    change unitaryProj h 3 _ = unitaryProj h 3 y ↔ _
    rw [unitaryProj_eq_iff, coe_suConj, coe_suField]
    simp only [Subgroup.coe_inv, hσG]
  have hsign : ∀ x ∈ CFSG.Quasithin.E22S.invLiftsU A' hA'e, ∀ i,
      CFSG.Quasithin.E22S.dgU g (x : GL (Fin 3) K) i *
        CFSG.Quasithin.E22S.dgU g (x : GL (Fin 3) K) i = 1 :=
    fun x hx i => CFSG.Quasithin.E22S.dgU_sq (hg x hx) (by simpa using congrArg Subtype.val hx.2) i
  set N : GL (Fin 3) K := g * (A₀ : GL (Fin 3) K) * (σG g)⁻¹ with hN
  have hNcomm : ∀ x ∈ CFSG.Quasithin.E22S.invLiftsU A' hA'e,
      N * (g * (x : GL (Fin 3) K) * g⁻¹) = (g * (x : GL (Fin 3) K) * g⁻¹) * N := by
    intro x hx
    set Dg := g * (x : GL (Fin 3) K) * g⁻¹ with hDg
    have hσD : σG Dg = Dg := by
      apply Units.ext
      rw [hσGval, CFSG.Quasithin.E22S.conjU_eq_diagonal (hg x hx),
        Matrix.diagonal_map (map_zero σ)]
      congr 1
      funext i
      rcases mul_self_eq_one_iff.mp (hsign x hx i) with h1 | h1
      · simp [h1]
      · simp [h1]
    have hfx := hbA _ ((hmemA' x).mp hx.1)
    obtain ⟨u, hu⟩ := (hact x x).mp hfx
    set Z := (A₀ : GL (Fin 3) K) * σG (x : GL (Fin 3) K) * (A₀ : GL (Fin 3) K)⁻¹ with hZdef
    have hx' : (x : GL (Fin 3) K) = g⁻¹ * Dg * g := by rw [hDg]; group
    have e1 : N * Dg * N⁻¹ = g * Z * g⁻¹ := by
      rw [hZdef, hx', map_mul, map_mul, map_inv, hσD, hN]
      group
    have hD : Dg = Matrix.GeneralLinearGroup.scalar (Fin 3) u * (N * Dg * N⁻¹) := by
      rw [e1]
      calc Dg = g * (x : GL (Fin 3) K) * g⁻¹ := rfl
        _ = g * (Z * Matrix.GeneralLinearGroup.scalar (Fin 3) u) * g⁻¹ := by rw [← hu]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) u * (g * Z * g⁻¹) := by
          rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u Z).eq, ← mul_assoc,
            (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u g).eq]
          group
    have hu1 : u = 1 := by
      have htr := congrArg (fun X : GL (Fin 3) K => Matrix.trace (X : Matrix (Fin 3) (Fin 3) K)) hD
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
        Matrix.trace_units_conj, smul_eq_mul] at htr
      have hne : Matrix.trace (Dg : Matrix (Fin 3) (Fin 3) K) ≠ 0 := by
        rw [CFSG.Quasithin.E22S.conjU_eq_diagonal (hg x hx), Matrix.trace_diagonal]
        exact sum_ne_zero_of_signs hK3 (hsign x hx)
      apply Units.ext
      have : (1 - (u : K)) * Matrix.trace (Dg : Matrix (Fin 3) (Fin 3) K) = 0 := by
        linear_combination htr
      rw [Units.val_one]
      exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)).symm
    rw [hu1, map_one, one_mul] at hD
    calc N * Dg = N * Dg * N⁻¹ * N := by group
      _ = Dg * N := by rw [← hD]
  have hNdiag : (N : Matrix (Fin 3) (Fin 3) K).IsDiag := by
    intro i j hij
    obtain ⟨x, hx, hxij⟩ := CFSG.Quasithin.E22S.exists_sign_neg_oneU h hA'e hA'4 hg hij
    have h1 := congrFun (congrFun (congrArg (fun X : GL (Fin 3) K =>
      (X : Matrix (Fin 3) (Fin 3) K)) (hNcomm x hx)) i) j
    rw [Units.val_mul N (g * (x : GL (Fin 3) K) * g⁻¹),
      Units.val_mul (g * (x : GL (Fin 3) K) * g⁻¹) N,
      CFSG.Quasithin.E22S.conjU_eq_diagonal (hg x hx), Matrix.mul_diagonal,
      Matrix.diagonal_mul] at h1
    have hne : CFSG.Quasithin.E22S.dgU g (x : GL (Fin 3) K) j -
        CFSG.Quasithin.E22S.dgU g (x : GL (Fin 3) K) i ≠ 0 := by
      intro h0
      have hji := sub_eq_zero.mp h0
      have h2 := hsign x hx i
      rw [hji] at hxij
      rw [hxij] at h2
      apply hK2
      linear_combination -h2
    have : (N : Matrix (Fin 3) (Fin 3) K) i j * (CFSG.Quasithin.E22S.dgU g (x : GL (Fin 3) K) j -
        CFSG.Quasithin.E22S.dgU g (x : GL (Fin 3) K) i) = 0 := by
      linear_combination h1
    exact (mul_eq_zero.mp this).resolve_right hne
  intro w hw
  obtain ⟨y, rfl⟩ := (Subgroup.mem_inf.mp (hWT hw)).1
  have hyA : ∀ a ∈ A, y * a = a * y := by
    intro a ha
    have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hWT hw)).2 _ ha
    rw [← map_mul, ← map_mul] at h1
    exact (hinj h1).symm
  obtain ⟨m, hm⟩ := hW2 ⟨MulAut.conj y, hw⟩
  have hym : y ^ (2 ^ m) = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact congrArg Subtype.val hm
  obtain ⟨Y, rfl⟩ := unitaryProj_surjective h 3 y
  have hYc : ∀ x ∈ CFSG.Quasithin.E22S.invLiftsU A' hA'e,
      (Y : GL (Fin 3) K) * (x : GL (Fin 3) K) = (x : GL (Fin 3) K) * (Y : GL (Fin 3) K) := by
    intro x hx
    have h1 := hyA _ ((hmemA' x).mp hx.1)
    have h2 : (x : CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) * (Y : CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) = (Y : CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) * (x : CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) := by
      rw [← hEqmk x, ← hEqmk Y, ← map_mul Eq, ← map_mul Eq, ← h1]
    have h3 := CFSG.Quasithin.E22S.commute_of_proj_commute_two_U hx.2 h2
    exact (congrArg Subtype.val h3).symm
  have hYdiag := CFSG.Quasithin.E22S.isDiagU_of_commute h hp2 hA'e hA'4 hg hYc
  set e := CFSG.Quasithin.E22S.dgU g (Y : GL (Fin 3) K) with he
  set Eg := g * (Y : GL (Fin 3) K) * g⁻¹ with hEg
  have hEmat : (Eg : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal e :=
    CFSG.Quasithin.E22S.conjU_eq_diagonal hYdiag
  have hYm : unitaryProj h 3 (Y ^ (2 ^ m)) = unitaryProj h 3 1 := by rw [map_pow, hym, map_one]
  obtain ⟨ζ, hζ⟩ := (unitaryProj_eq_iff h).mp hYm.symm
  rw [Subgroup.coe_one, one_mul] at hζ
  have hepow : ∀ i, e i ^ (2 ^ m) = (ζ : K) := by
    intro i
    have h1 : Eg ^ (2 ^ m) = g * ((Y ^ (2 ^ m) : unitarySU p f K 3) : GL (Fin 3) K) * g⁻¹ := by
      rw [hEg, conj_pow, Subgroup.coe_pow]
    rw [hζ, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ g).eq, mul_inv_cancel_right]
      at h1
    have h4 := congrFun (congrFun (congrArg (fun X : GL (Fin 3) K =>
      (X : Matrix (Fin 3) (Fin 3) K)) h1) i) i
    simp only [Units.val_pow_eq_pow_val, hEmat, Matrix.diagonal_pow,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Pi.pow_apply] at h4
    exact h4
  have hζ0 : (ζ : K) ≠ 0 := ζ.ne_zero
  have he0 : ∀ i, e i ≠ 0 := fun i h1 => hζ0 (by rw [← hepow i, h1, zero_pow (by positivity)])
  have hfix : ∀ i, σ (e i / e 2) = e i / e 2 := fun i =>
    ringEquiv_fix_of_two_pow σ hσ3 (m := m) (by rw [div_pow, hepow i, hepow 2, div_self hζ0])
  set c := σ (e 2) / e 2 with hcdef
  have hσe : ∀ i, σ (e i) = c * e i := by
    intro i
    have h2 := he0 2
    have h1 : e i = e 2 * (e i / e 2) := by field_simp
    calc σ (e i) = σ (e 2) * σ (e i / e 2) := by rw [← map_mul, ← h1]
      _ = c * e i := by rw [hfix i, hcdef]; field_simp
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    exact div_ne_zero ((map_ne_zero σ).mpr (he0 2)) (he0 2)
  have hbY : b (unitaryProj h 3 Y) = unitaryProj h 3 Y := by
    refine (hact Y Y).mpr ⟨(Units.mk0 c hc0)⁻¹, ?_⟩
    have hσE : σG Eg = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * Eg := by
      apply Units.ext
      rw [hσGval, hEmat, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hEmat,
        Matrix.diagonal_map (map_zero σ), Units.val_mk0, Matrix.scalar_apply,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact hσe i
    have hNE : N * σG Eg = σG Eg * N := by
      apply commute_of_isDiag hNdiag
      rw [hσGval, hEmat, Matrix.diagonal_map (map_zero σ)]
      exact Matrix.isDiag_diagonal _
    have hY' : (Y : GL (Fin 3) K) = g⁻¹ * Eg * g := by rw [hEg]; group
    have e1 : (A₀ : GL (Fin 3) K) * σG (Y : GL (Fin 3) K) * (A₀ : GL (Fin 3) K)⁻¹ =
        g⁻¹ * (N * σG Eg * N⁻¹) * g := by
      rw [hY', map_mul, map_mul, map_inv, hN]
      group
    rw [e1, hNE, mul_inv_cancel_right, hσE, hY', map_inv]
    set sc := Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) with hsc
    have hcomm2 := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (Units.mk0 c hc0)
      (g⁻¹ * Eg * g)).eq
    calc g⁻¹ * Eg * g = (g⁻¹ * Eg * g) * sc * sc⁻¹ := by group
      _ = sc * (g⁻¹ * Eg * g) * sc⁻¹ := by rw [hcomm2]
      _ = g⁻¹ * (sc * Eg) * g * sc⁻¹ := by
        rw [← mul_assoc g⁻¹ sc Eg,
          (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (Units.mk0 c hc0) g⁻¹).eq, ← hsc]
        group
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := mul_conj_mul_inv' b (unitaryProj h 3 Y)
  rw [hbY] at h1
  calc MulAut.conj (unitaryProj h 3 Y) * b = b * MulAut.conj (unitaryProj h 3 Y) * b⁻¹ * b := by
        rw [h1]
    _ = b * MulAut.conj (unitaryProj h 3 Y) := by group

end Unitary

theorem three_ne_zero_of_charP {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp3 : 3 < p) : (3 : K) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h'
  have := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp h'
  omega

end Item211Lie2Proof

open Item211Lie2Proof
open CFSG.LocalAnalysis.ComponentInitial

theorem ks211L3Minus_holds : KS211L3Minus := by
  intro X _ _ hX hM
  obtain ⟨p, hp, hp3, e, he, hcase⟩ := hM
  have hp2 : p ≠ 2 := by omega
  have hpe : 2 < p ^ e := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
  change L3MinusFor X
  have : Group.IsPerfect X := hX.1
  rcases hcase with ⟨K, _, _, hK⟩ | hL
  · rcases hK with ⟨hcard, -, ⟨φ⟩⟩ | ⟨hcard, -, ⟨φ⟩⟩
    · have : Fintype K := Fintype.ofFinite K
      have : CharP K p := charP_of_card_eq_prime_pow (f := e)
        (by rw [← Nat.card_eq_fintype_card, hcard])
      exact l3MinusFor_of_perfect (l3MinusFor_of_mulEquiv
        ((quotientCenterCongr (φ.trans (Sec4.statedSLEquiv 3 K))).trans
          (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
        (l3MinusFor_projectiveSL hp2 (three_ne_zero_of_charP hp3)))
    · have h : UnitaryFieldData p e K := ⟨hp.out, he, by rw [hcard, ← pow_mul, mul_comm]⟩
      have : CharP K p := h.charP
      exact l3MinusFor_of_perfect (l3MinusFor_of_mulEquiv
        ((quotientCenterCongr φ).trans (KFacts.suCenterEquiv h hpe))
        (l3MinusFor_unitaryPSU h hp2 (three_ne_zero_of_charP hp3) hpe))
  · rcases hL with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · exact l3MinusFor_of_mulEquiv (φ.trans (Sec4.projSLEquivProjectiveSL 3 (GaloisField p e)))
        (l3MinusFor_projectiveSL hp2 (three_ne_zero_of_charP hp3))
    · have h := Sec4.unitaryFieldData_galoisField p e he
      exact l3MinusFor_of_mulEquiv (φ.trans (Sec4.projSUEquivUnitaryPSU p e h))
        (l3MinusFor_unitaryPSU h hp2 (three_ne_zero_of_charP hp3) hpe)

end CFSG.RankThree.PartTwo.Sec21
