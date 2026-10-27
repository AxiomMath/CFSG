module

public import CFSG.RankThree.PartTwo.Sec16.Item166Res5ProofZero
import CFSG.RankThree.PartTwo.Sec16.Item166Res3ProofComm
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTools
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeSL
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal

public section

namespace CFSG.RankThree.PartTwo.Sec16.ProofNoE4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification
open CFSG.RankThree.PartTwo.Sec16.ProofHess (not_cube_of_not_nine_dvd exists_normal_form_det_one
  eq_diagonal_of_commute exists_eq_smul_pow_of_diag conj_commute conj_pow unconj det_conj
  exists_two_of_card_nine)

section Groups

theorem commutator_mul_center {S : Type*} [Group S] {s t : S} (hs : s ∈ Subgroup.center S)
    (ht : t ∈ Subgroup.center S) (a b : S) :
    (s * a) * (t * b) * (s * a)⁻¹ * (t * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hs' : ∀ x : S, x * s = s * x := fun x => Subgroup.mem_center_iff.mp hs x
  have ht' : ∀ x : S, x * t = t * x := fun x => Subgroup.mem_center_iff.mp ht x
  calc (s * a) * (t * b) * (s * a)⁻¹ * (t * b)⁻¹
      = s * (a * (t * b) * a⁻¹) * s⁻¹ * (b⁻¹ * t⁻¹) := by group
    _ = (a * (t * b) * a⁻¹) * (b⁻¹ * t⁻¹) := by rw [← hs']; group
    _ = t * (a * b * a⁻¹ * b⁻¹) * t⁻¹ := by
        rw [show a * (t * b) * a⁻¹ = a * t * b * a⁻¹ by group, ht' a]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [← ht']; group

theorem eq_of_sq_eq_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {x y : C}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have : Fintype C := Fintype.ofFinite C
  classical
  by_contra hxy
  have hsub : ({1, x, y} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · simp
    · simpa using hx
    · simpa using hy
  have hcard := (Finset.card_le_card hsub).trans (IsCyclic.card_pow_eq_one_le (by norm_num))
  rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx1, Ne.symm hy1]),
    Finset.card_pair hxy] at hcard
  omega

theorem eq_one_of_sq_of_pow_three {S : Type*} [Monoid S] {γ : S} (hγ2 : γ ^ 2 = 1) {k : ℕ}
    (hk : γ ^ 3 ^ k = 1) : γ = 1 := by
  have h1 : orderOf γ ∣ 2 := orderOf_dvd_of_pow_eq_one hγ2
  have h2 : orderOf γ ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime 2 (3 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem eq_one_of_inner {X : Type*} [Group X] {D : Subgroup X}
    (hcent : IsPGroup 3 (Subgroup.centralizer (D : Set X))) {γ : MulAut X}
    (hγD : ∀ d ∈ D, γ d = d) (hγ2 : γ ^ 2 = 1) (hinn : ∃ x : X, MulAut.conj x = γ) : γ = 1 := by
  obtain ⟨x, rfl⟩ := hinn
  have hxC : x ∈ Subgroup.centralizer (D : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h := hγD d hd
    rw [MulAut.conj_apply] at h
    calc d * x = x * d * x⁻¹ * x := by rw [h]
      _ = x * d := by group
  obtain ⟨k, hk⟩ := hcent ⟨x, hxC⟩
  have hxk : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine eq_one_of_sq_of_pow_three hγ2 (k := k) ?_
  rw [← map_pow, hxk, map_one]

theorem exists_conj_of_conjAut {K : Type} [Field K] (A : GL (Fin 3) K)
    (h2 : conjAut 3 K A ^ 2 = 1) : ∃ x, MulAut.conj x = conjAut 3 K A := by
  obtain ⟨x, hx⟩ := Sec4.isInnerAut_conjAut_pow_n A
  refine ⟨x, ?_⟩
  rw [hx, pow_succ, h2, one_mul]

end Groups

section Linear

variable {K : Type} [Field K] [Finite K]

theorem pow_three_eq_one_of_proj (h9 : ¬ 9 ∣ Nat.card K - 1) {y : SpecialLinearGroup (Fin 3) K}
    (hy : proj 3 K y ^ 3 = 1) : y ^ 3 = 1 := by
  rw [← map_pow, proj_eq_one_iff] at hy
  obtain ⟨ε, hε3, hεy⟩ := mem_scalars.mp hy
  by_cases hε1 : ε = 1
  · ext i j
    rw [hεy, hε1]
    simp
  · exfalso
    have hε3' : (ε : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hε3, Units.val_one]
    have hε1' : (ε : K) ≠ 1 := fun h => hε1 (Units.ext h)
    have hcube : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = (ε : K) • 1 := by
      calc (y : Matrix (Fin 3) (Fin 3) K) ^ 3
          = ((y ^ 3 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
            (Matrix.SpecialLinearGroup.coe_pow y 3).symm
        _ = (ε : K) • 1 := by
            rw [hεy, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
    have h := Sec4.det_eq_of_cube (not_cube_of_not_nine_dvd h9 hε3' hε1') hcube
    rw [y.2] at h
    exact hε1' h.symm

theorem exists_hessian_lifts (h9 : ¬ 9 ∣ Nat.card K - 1) (h3 : (3 : K) ≠ 0) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {E : Subgroup (projectiveSL 3 K)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    ∃ g₁ g₂ : SpecialLinearGroup (Fin 3) K, proj 3 K g₁ ∈ E ∧ proj 3 K g₂ ∈ E ∧
      ∃ ζ : Kˣ, ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧
        ((g₁ * g₂ * g₁⁻¹ * g₂⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          scalar (Fin 3) (ζ : K) := by
  obtain ⟨e₁, he₁E, he₁1, e₂, he₂E, he₂⟩ := exists_two_of_card_nine hE hE9
  obtain ⟨y₁, rfl⟩ := proj_surjective 3 K e₁
  obtain ⟨y₂, rfl⟩ := proj_surjective 3 K e₂
  refine ⟨y₁, y₂, he₁E, he₂E, ?_⟩
  have hcomm_bar : proj 3 K y₁ * proj 3 K y₂ = proj 3 K y₂ * proj 3 K y₁ :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨_, he₁E⟩ ⟨_, he₂E⟩)
  set w := y₁ * y₂ * y₁⁻¹ * y₂⁻¹ with hw
  have hwsc : w ∈ scalars 3 K := by
    rw [← proj_eq_one_iff, hw, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm_bar]
    group
  obtain ⟨ζ, hζ3, hζw⟩ := mem_scalars.mp hwsc
  refine ⟨ζ, hζ3, fun hζ1 => ?_, hζw⟩
  have hw1 : w = 1 := by
    ext i j
    rw [hζw, hζ1]
    simp
  have hcomm : y₁ * y₂ = y₂ * y₁ := by
    calc y₁ * y₂ = w * (y₂ * y₁) := by rw [hw]; group
      _ = y₂ * y₁ := by rw [hw1, one_mul]
  have hy₁3 : y₁ ^ 3 = 1 := pow_three_eq_one_of_proj h9 (hE.2 _ he₁E)
  have hy₂3 : y₂ ^ 3 = 1 := pow_three_eq_one_of_proj h9 (hE.2 _ he₂E)
  have hdet₁ : (y₁ : Matrix (Fin 3) (Fin 3) K).det = 1 := y₁.2
  have hdet₂ : (y₂ : Matrix (Fin 3) (Fin 3) K).det = 1 := y₂.2
  have hy₁s : ∀ c : K, (y₁ : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro c hc
    apply he₁1
    have hc3 : c ^ 3 = 1 := by
      have h := hdet₁
      rwa [hc, Matrix.det_smul, det_one, mul_one, Fintype.card_fin] at h
    have hc0 : c ≠ 0 := by
      rintro rfl
      norm_num at hc3
    rw [proj_eq_one_iff]
    refine ⟨Units.mk0 c hc0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hc3,
      Units.val_one]), ?_⟩
    rw [hc, Units.val_mk0, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  have hy₁3m : (y₁ : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    calc (y₁ : Matrix (Fin 3) (Fin 3) K) ^ 3
        = ((y₁ ^ 3 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
          (Matrix.SpecialLinearGroup.coe_pow y₁ 3).symm
      _ = 1 := by rw [hy₁3]; rfl
  obtain ⟨P, j, hP, hPD⟩ := exists_normal_form_det_one hτ hτ1 h3 hy₁3m hdet₁ hy₁s
  set D : Matrix (Fin 3) (Fin 3) K := diagonal ![τ, τ ^ 2, 1] with hD
  set Y : Matrix (Fin 3) (Fin 3) K := τ ^ (j : ℕ) • (y₁ : Matrix (Fin 3) (Fin 3) K) with hY
  set Q := P⁻¹ with hQ
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P hPdet
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hYPD : Y = P * D * Q := by
    calc Y = Y * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = (Y * P) * Q := by rw [Matrix.mul_assoc]
      _ = P * D * Q := by rw [hPD]
  have hcomm' : (y₂ : Matrix (Fin 3) (Fin 3) K) * Y = Y * y₂ := by
    have h := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
      hcomm
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h
    rw [hY, Matrix.mul_smul, Matrix.smul_mul, h]
  set N := Q * (y₂ : Matrix (Fin 3) (Fin 3) K) * P with hN
  have hND : N * D = D * N := conj_commute hPQ hQP hPD hcomm'
  have hNdiag := eq_diagonal_of_commute hτ hτ1 hND
  have hNdet : N.det = 1 := by rw [hN, det_conj hQP, hdet₂]
  have hy₂3m : (y₂ : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    calc (y₂ : Matrix (Fin 3) (Fin 3) K) ^ 3
        = ((y₂ ^ 3 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
          (Matrix.SpecialLinearGroup.coe_pow y₂ 3).symm
      _ = 1 := by rw [hy₂3]; rfl
  have hN3 : N ^ 3 = 1 := by
    rw [hN, conj_pow hPQ hQP, hy₂3m, Matrix.mul_one, hQP]
  have hcub : ∀ i, (N i i) ^ 3 = 1 := by
    intro i
    have h := congrFun (congrFun hN3 i) i
    rw [hNdiag, diagonal_pow, diagonal_apply_eq, Matrix.one_apply_eq] at h
    simpa using h
  have habc : N 0 0 * N 1 1 * N 2 2 = 1 := by
    have h := hNdet
    rw [hNdiag, det_diagonal, Fin.prod_univ_three] at h
    exact h
  obtain ⟨i, hi⟩ := exists_eq_smul_pow_of_diag hτ hτ1 (hcub 0) (hcub 1) habc
  obtain ⟨c, hc⟩ : ∃ c : K, c = N 2 2 := ⟨_, rfl⟩
  have hNeq : N = c • D ^ i := by
    rw [hc, ← hi, hNdiag]
    congr 1
    funext l
    fin_cases l <;> rfl
  have hy₂eq : (y₂ : Matrix (Fin 3) (Fin 3) K) =
      (c * (τ ^ (j : ℕ)) ^ i) • (y₁ : Matrix (Fin 3) (Fin 3) K) ^ i := by
    have h1 : (y₂ : Matrix (Fin 3) (Fin 3) K) = P * N * Q := by rw [hN, unconj hPQ]
    have h2 : P * D ^ i * Q = Y ^ i := by
      rw [hYPD, conj_pow hQP hPQ D i]
    rw [h1, hNeq, Matrix.mul_smul, Matrix.smul_mul, h2, hY, smul_pow, smul_smul]
  apply he₂
  set c' := c * (τ ^ (j : ℕ)) ^ i with hc'
  have hsc : y₂ * (y₁ ^ i)⁻¹ ∈ scalars 3 K := by
    have hmat : ((y₂ * (y₁ ^ i)⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = c' • 1 := by
      have hinv : ((y₁ ^ i : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (((y₁ ^ i)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
      rw [Matrix.SpecialLinearGroup.coe_mul, hy₂eq, Matrix.smul_mul,
        ← Matrix.SpecialLinearGroup.coe_pow, hinv]
    have hc'3 : c' ^ 3 = 1 := by
      have h := (y₂ * (y₁ ^ i)⁻¹).2
      rwa [hmat, Matrix.det_smul, det_one, mul_one, Fintype.card_fin] at h
    have hc'0 : c' ≠ 0 := by
      rintro h0
      rw [h0] at hc'3
      norm_num at hc'3
    refine ⟨Units.mk0 c' hc'0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hc'3,
      Units.val_one]), ?_⟩
    rw [hmat, Units.val_mk0, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  have hmk := proj_eq_one_iff.mpr hsc
  rw [map_mul, map_inv, mul_inv_eq_one] at hmk
  rw [hmk, map_pow]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i

end Linear

section LinearAut

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
open KFacts.OutFixCentralThree in
theorem coe_stdAut3_scalar (A : GL (Fin 3) K) (ρ : K ≃+* K) {ε : ℕ} (hε : ε ≤ 1)
    {z : SpecialLinearGroup (Fin 3) K} {ζ : Kˣ}
    (hz : (z : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) (ζ : K)) :
    ((stdAut3 A ρ ε z : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      scalar (Fin 3) ((Units.map (ρ : K →* K) (ζ ^ ((-1 : ℤ) ^ ε)) : Kˣ) : K) := by
  rw [coe_stdAut3]
  have hgraph : ((((CatalogueBGraphForm.slGraphAut 3 K ^ ε) z : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) = scalar (Fin 3) ((ζ ^ ((-1 : ℤ) ^ ε) : Kˣ) : K) := by
    rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
    · rw [pow_zero, MulAut.one_apply, hz, pow_zero, zpow_one]
    · rw [pow_one, CatalogueBGraphForm.slGraphAut_matrix, coe_inv_of_coe_eq_scalar hz,
        pow_one, _root_.zpow_neg_one, Matrix.scalar_apply, Matrix.diagonal_transpose]
  rw [hgraph, map_scalar_eq, conj_scalar_eq, Units.coe_map]
  rfl

omit [Finite K] in
theorem map_zeta_of_fix {E : Subgroup (projectiveSL 3 K)} {g₁ g₂ : SpecialLinearGroup (Fin 3) K}
    (hg₁ : proj 3 K g₁ ∈ E) (hg₂ : proj 3 K g₂ ∈ E) {ζ : Kˣ}
    (hζ : ((g₁ * g₂ * g₁⁻¹ * g₂⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      scalar (Fin 3) (ζ : K))
    (A : GL (Fin 3) K) (ρ : K ≃+* K) {ε : ℕ} (hε : ε ≤ 1)
    (hfix : ∀ e ∈ E, (conjAut 3 K A * fieldAut 3 K ρ * dualAut 3 K ^ ε) e = e) :
    Units.map (ρ : K →* K) (ζ ^ ((-1 : ℤ) ^ ε)) = ζ := by
  have hdesc := KFacts.OutFixCentralThree.descendAut_stdAut3 A ρ ε
  have hcen : ∀ g : SpecialLinearGroup (Fin 3) K, proj 3 K g ∈ E →
      ∃ s ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K),
        KFacts.OutFixCentralThree.stdAut3 A ρ ε g = s * g := by
    intro g hg
    refine ⟨KFacts.OutFixCentralThree.stdAut3 A ρ ε g * g⁻¹, ?_, by group⟩
    rw [← scalars_eq_center, ← proj_eq_one_iff, map_mul, map_inv, mul_inv_eq_one,
      ← descendAut_proj, hdesc, hfix _ hg]
  obtain ⟨s₁, hs₁, he₁⟩ := hcen g₁ hg₁
  obtain ⟨s₂, hs₂, he₂⟩ := hcen g₂ hg₂
  have hw : KFacts.OutFixCentralThree.stdAut3 A ρ ε (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) =
      g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, he₁, he₂]
    exact commutator_mul_center hs₁ hs₂ g₁ g₂
  have hm := coe_stdAut3_scalar A ρ hε hζ
  rw [hw, hζ] at hm
  apply Units.ext
  have h00 := congrFun (congrFun hm 0) 0
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h00
  exact h00.symm

theorem linearAutGroup_normal : (linearAutGroup 3 K).Normal :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup_normal_of_three_le le_rfl

theorem noE4_linear (h9 : ¬ 9 ∣ Nat.card K - 1) (h3 : (3 : K) ≠ 0) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {E : Subgroup (projectiveSL 3 K)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9)
    (hcent : IsPGroup 3 (Subgroup.centralizer (E : Set (projectiveSL 3 K))))
    {α β : MulAut (projectiveSL 3 K)} (hα : ∀ d ∈ E, α d = d) (hβ : ∀ d ∈ E, β d = d)
    (hα2 : α ^ 2 = 1) (hβ2 : β ^ 2 = 1) (hcomm : α * β = β * α) (hα1 : α ≠ 1) (hβ1 : β ≠ 1) :
    α = β := by
  have hnorm := linearAutGroup_normal (K := K)
  obtain ⟨g₁, g₂, hg₁, hg₂, ζ, hζ3, hζ1, hζ⟩ := exists_hessian_lifts h9 h3 hτ hτ1 hE hE9
  have hζinv : ζ⁻¹ ≠ ζ := by
    intro h
    apply hζ1
    have h2 : ζ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← h]
      exact inv_mul_cancel ζ
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hζ3, h2]; group
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  have htrans := standard_automorphism_transport (K := K) (n := 3)
  have hδδ : dualAut 3 K * dualAut 3 K = 1 := htrans.2.2.2.1
  set π := QuotientGroup.mk' (linearAutGroup 3 K) with hπ
  have hπc : ∀ A, π (conjAut 3 K A) = 1 := fun A =>
    (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_linearAutGroup A)
  have hπδ : π (dualAut 3 K) ^ 2 = 1 := by rw [← map_pow, sq, hδδ, map_one]
  have hfδ : ∀ σ, Commute (π (fieldAut 3 K σ)) (π (dualAut 3 K)) := by
    intro σ
    have h : fieldAut 3 K σ * dualAut 3 K = dualAut 3 K * fieldAut 3 K σ := by
      calc fieldAut 3 K σ * dualAut 3 K
          = dualAut 3 K * fieldAut 3 K σ * dualAut 3 K * dualAut 3 K := by
            rw [htrans.2.2.2.2.2.1]
        _ = dualAut 3 K * fieldAut 3 K σ := by rw [mul_assoc _ (dualAut 3 K), hδδ, mul_one]
    change π _ * π _ = π _ * π _
    rw [← map_mul, ← map_mul, h]
  have hkey : ∀ γ : MulAut (projectiveSL 3 K), (∀ d ∈ E, γ d = d) → γ ^ 2 = 1 → γ ≠ 1 →
      ∃ ρ : K ≃+* K, ∃ ε : ℕ, ε ≤ 1 ∧ ρ ≠ 1 ∧ ρ ^ 2 = 1 ∧
        Units.map (ρ : K →* K) (ζ ^ ((-1 : ℤ) ^ ε)) = ζ ∧
        π γ = π (fieldAut 3 K ρ) * π (dualAut 3 K) ^ ε := by
    intro γ hγE hγ2 hγ1
    obtain ⟨A, ρ, ε, hε, hγeq⟩ := hgen γ
    have hz := map_zeta_of_fix hg₁ hg₂ hζ A ρ hε (hγeq ▸ hγE)
    have hπγ : π γ = π (fieldAut 3 K ρ) * π (dualAut 3 K) ^ ε := by
      rw [hγeq, map_mul, map_mul, map_pow, hπc, one_mul]
    have hρ2 : ρ ^ 2 = 1 := by
      have h1 : π (γ ^ 2) = 1 := by rw [hγ2, map_one]
      rw [map_pow, hπγ, ((hfδ ρ).pow_right ε).mul_pow, ← pow_mul, mul_comm ε 2, pow_mul, hπδ,
        one_pow, mul_one, ← map_pow, ← map_pow] at h1
      obtain ⟨B, hB⟩ := mem_linearAutGroup_iff.mp ((QuotientGroup.eq_one_iff _).mp h1)
      refine (eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl B⁻¹ (ρ ^ 2) ?_).1
      rw [map_inv, hB, inv_mul_cancel]
    refine ⟨ρ, ε, hε, fun hρ1 => ?_, hρ2, hz, hπγ⟩
    subst hρ1
    have hε0 : ε = 0 := by
      rcases (show ε = 0 ∨ ε = 1 by omega) with h0 | h1
      · exact h0
      · exfalso
        apply hζinv
        have hid : ∀ x : Kˣ, Units.map ((1 : K ≃+* K) : K →* K) x = x := fun x => Units.ext rfl
        rw [h1, pow_one, _root_.zpow_neg_one, hid] at hz
        exact hz
    rw [hε0, pow_zero, mul_one, map_one, mul_one] at hγeq
    subst hγeq
    exact hγ1 (eq_one_of_inner hcent hγE hγ2 (exists_conj_of_conjAut A hγ2))
  obtain ⟨ρ, ε, hε, hρ1, hρ2, hzα, hπα⟩ := hkey α hα hα2 hα1
  obtain ⟨ρ', ε', hε', hρ'1, hρ'2, hzβ, hπβ⟩ := hkey β hβ hβ2 hβ1
  have : IsCyclic (K ≃+* K) := CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (fun _ _ h => RingEquiv.ext (congrFun h))
  have hρρ' : ρ = ρ' := eq_of_sq_eq_one_of_isCyclic hρ2 hρ'2 hρ1 hρ'1
  subst hρρ'
  have hεε' : ε = ε' := by
    have hinj : Function.Injective (Units.map (ρ : K →* K)) := fun x y hxy =>
      Units.ext (ρ.injective (by simpa using congrArg Units.val hxy))
    have h := hinj (hzα.trans hzβ.symm)
    rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl <;>
      rcases (show ε' = 0 ∨ ε' = 1 by omega) with rfl | rfl
    · rfl
    · exfalso
      apply hζinv
      simpa using h.symm
    · exfalso
      apply hζinv
      simpa using h
    · rfl
  subst hεε'
  have hπαβ : π (α * β) = 1 := by
    rw [map_mul, hπβ, ← hπα, ← map_mul, ← sq, hα2, map_one]
  obtain ⟨C, hC⟩ := mem_linearAutGroup_iff.mp ((QuotientGroup.eq_one_iff _).mp hπαβ)
  have hαβ2 : (α * β) ^ 2 = 1 := by
    rw [sq, show α * β * (α * β) = α * (β * α) * β by group, ← hcomm,
      show α * (α * β) * β = α ^ 2 * β ^ 2 by rw [sq, sq]; simp only [mul_assoc], hα2, hβ2,
      one_mul]
  have hαβE : ∀ d ∈ E, (α * β) d = d := fun d hd => by
    rw [MulAut.mul_apply, hβ d hd, hα d hd]
  have hαβ1 := eq_one_of_inner hcent hαβE hαβ2
    (by rw [← hC] at hαβ2 ⊢; exact exists_conj_of_conjAut C hαβ2)
  calc α = α * β * β⁻¹ := by group
    _ = β⁻¹ := by rw [hαβ1, one_mul]
    _ = β := by rw [inv_eq_of_mul_eq_one_right (show β * β = 1 by rw [← sq, hβ2])]

end LinearAut

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem psuConj_range_normal (hq : 2 < p ^ f) : (KFacts.psuConj h).range.Normal := by
  refine ⟨fun d hd g => ?_⟩
  obtain ⟨B, rfl⟩ := hd
  obtain ⟨A, σ, rfl⟩ := KFacts.exists_psuConj_mul_psuField hq g
  have h1 := KFacts.psuField_mul_psuConj_mul_inv σ B
  refine ⟨A * ⟨UnitaryHigher.glAut σ B, KFacts.glAut_mem_unitaryIsom3 σ B.2⟩ * A⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, ← h1]
  group

theorem noE4_psu (hq : 2 < p ^ f) {E : Subgroup (unitaryPSU h 3)}
    (hcent : IsPGroup 3 (Subgroup.centralizer (E : Set (unitaryPSU h 3))))
    {α β : MulAut (unitaryPSU h 3)} (hα : ∀ d ∈ E, α d = d) (hβ : ∀ d ∈ E, β d = d)
    (hα2 : α ^ 2 = 1) (hβ2 : β ^ 2 = 1) (hcomm : α * β = β * α) (hα1 : α ≠ 1) (hβ1 : β ≠ 1) :
    α = β := by
  have := h.finite
  have hnorm := psuConj_range_normal h hq
  set π := QuotientGroup.mk' (KFacts.psuConj h).range with hπ
  have hπc : ∀ A, π (KFacts.psuConj h A) = 1 := fun A =>
    (QuotientGroup.eq_one_iff _).mpr ⟨A, rfl⟩
  have hinner : ∀ A : KFacts.unitaryIsom3 h, KFacts.psuConj h A ^ 2 = 1 →
      ∃ x, MulAut.conj x = KFacts.psuConj h A := by
    intro A h2
    obtain ⟨x, hx⟩ := Proof166Res3.isInnerAut_psuConj_pow_three A
    refine ⟨x, ?_⟩
    rw [hx, pow_succ, h2, one_mul]
  have hkey : ∀ γ : MulAut (unitaryPSU h 3), (∀ d ∈ E, γ d = d) → γ ^ 2 = 1 → γ ≠ 1 →
      ∃ ρ : K ≃+* K, ρ ≠ 1 ∧ ρ ^ 2 = 1 ∧ π γ = π (KFacts.psuField h ρ) := by
    intro γ hγE hγ2 hγ1
    obtain ⟨A, ρ, hγeq⟩ := KFacts.exists_psuConj_mul_psuField hq γ
    have hπγ : π γ = π (KFacts.psuField h ρ) := by rw [hγeq, map_mul, hπc, one_mul]
    have hρ2 : ρ ^ 2 = 1 := by
      have h1 : π (γ ^ 2) = 1 := by rw [hγ2, map_one]
      rw [map_pow, hπγ, ← map_pow, ← map_pow] at h1
      exact KFacts.psuField_mem_range_psuConj_iff.mp ((QuotientGroup.eq_one_iff _).mp h1)
    refine ⟨ρ, fun hρ1 => ?_, hρ2, hπγ⟩
    subst hρ1
    rw [map_one, mul_one] at hγeq
    subst hγeq
    exact hγ1 (eq_one_of_inner hcent hγE hγ2 (hinner A hγ2))
  obtain ⟨ρ, hρ1, hρ2, hπα⟩ := hkey α hα hα2 hα1
  obtain ⟨ρ', hρ'1, hρ'2, hπβ⟩ := hkey β hβ hβ2 hβ1
  have : IsCyclic (K ≃+* K) := CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (fun _ _ h => RingEquiv.ext (congrFun h))
  have hρρ' : ρ = ρ' := eq_of_sq_eq_one_of_isCyclic hρ2 hρ'2 hρ1 hρ'1
  subst hρρ'
  have hπαβ : π (α * β) = 1 := by
    rw [map_mul, hπβ, ← hπα, ← map_mul, ← sq, hα2, map_one]
  obtain ⟨C, hC⟩ := (QuotientGroup.eq_one_iff _).mp hπαβ
  have hαβ2 : (α * β) ^ 2 = 1 := by
    rw [sq, show α * β * (α * β) = α * (β * α) * β by group, ← hcomm,
      show α * (α * β) * β = α ^ 2 * β ^ 2 by rw [sq, sq]; simp only [mul_assoc], hα2, hβ2,
      one_mul]
  have hαβE : ∀ d ∈ E, (α * β) d = d := fun d hd => by
    rw [MulAut.mul_apply, hβ d hd, hα d hd]
  have hαβ1 := eq_one_of_inner hcent hαβE hαβ2
    (by rw [← hC] at hαβ2 ⊢; exact hinner C hαβ2)
  calc α = α * β * β⁻¹ := by group
    _ = β⁻¹ := by rw [hαβ1, one_mul]
    _ = β := by rw [inv_eq_of_mul_eq_one_right (show β * β = 1 by rw [← sq, hβ2])]

end Unitary

end CFSG.RankThree.PartTwo.Sec16.ProofNoE4

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open ProofNoE4

theorem ks168NoE4 : KS168NoE4 := by
  intro X _ _ n hn2 hn3 hiso D hD hD9 α β hα hβ hα2 hβ2 hcomm hα1 hβ1
  have h9' := ProofKSL3Two.not_two_pow_mod_nine hn3
  have key : ∀ {M : Type} [Group M] [Finite M] (ψ : X ≃* M), Sec4.IsoLThreePi M 2 n →
      (∀ E : Subgroup M, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
        IsPGroup 3 (Subgroup.centralizer (E : Set M)) →
        ∀ α' β' : MulAut M, (∀ d ∈ E, α' d = d) → (∀ d ∈ E, β' d = d) → α' ^ 2 = 1 →
          β' ^ 2 = 1 → α' * β' = β' * α' → α' ≠ 1 → β' ≠ 1 → α' = β') → α = β := by
    intro M _ _ ψ hisoM hM
    have hE := ProofPComm.isElemAbelian_map hD ψ.toMonoidHom
    have hE9 : Nat.card (D.map ψ.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective ψ.injective, hD9]
    have hcent := kS169HessCent M n (by omega) hisoM h9' _ hE hE9
    have hfix : ∀ γ : MulAut X, (∀ d ∈ D, γ d = d) →
        ∀ d ∈ D.map ψ.toMonoidHom, MulAut.congr ψ γ d = d := by
      rintro γ hγ _ ⟨d, hd, rfl⟩
      change ψ (γ (ψ.symm (ψ d))) = ψ d
      rw [MulEquiv.symm_apply_apply, hγ d hd]
    have hinj := (MulAut.congr ψ).injective
    refine hinj (hM _ hE hE9 hcent _ _ (hfix α hα) (hfix β hβ) (by rw [← map_pow, hα2, map_one])
      (by rw [← map_pow, hβ2, map_one]) (by rw [← map_mul, ← map_mul, hcomm])
      (fun h1 => hα1 (hinj (h1.trans (map_one _).symm)))
      (fun h1 => hβ1 (hinj (h1.trans (map_one _).symm))))
  rcases hiso with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  ·
    have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
    obtain ⟨φ⟩ := KFacts.nonempty_projSL_mulEquiv 3 (GaloisField 2 n)
    have h9 : ¬ 9 ∣ Nat.card (GaloisField 2 n) - 1 := by
      rw [hK]
      have := Nat.one_le_two_pow (n := n)
      omega
    have h3 : (3 : GaloisField 2 n) ≠ 0 := by
      have h2 : (2 : GaloisField 2 n) = 0 := CharTwo.two_eq_zero
      rw [show (3 : GaloisField 2 n) = 2 + 1 by norm_num, h2, zero_add]
      exact one_ne_zero
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 n)ˣ) 3
      (by rw [Nat.card_units, hK]; have := Nat.one_le_two_pow (n := n); omega)
    have hτ : ((x : GaloisField 2 n)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hx, pow_orderOf_eq_one, Units.val_one]
    have hτ1 : (x : GaloisField 2 n) ≠ 1 := by
      intro h1
      have : x = 1 := Units.ext h1
      rw [this, orderOf_one] at hx
      omega
    have : Finite (projectiveSL 3 (GaloisField 2 n)) := Finite.of_equiv X (e.trans φ).toEquiv
    exact key (e.trans φ) (Or.inl ⟨hq, ⟨φ.symm⟩⟩)
      (fun _ hE hE9 hcent _ _ hα' hβ' hα2' hβ2' hc' hα1' hβ1' =>
        noE4_linear h9 h3 hτ hτ1 hE hE9 hcent hα' hβ' hα2' hβ2' hc' hα1' hβ1')
  ·
    have hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
      ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
    obtain ⟨ψ₀⟩ := KFacts.nonempty_unitaryPSU_mulEquiv_projSU hU
    have hq2 : 2 < 2 ^ n :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ n))
    have : Finite (unitaryPSU hU 3) := Finite.of_equiv X (e.trans ψ₀.symm).toEquiv
    exact key (e.trans ψ₀.symm) (Or.inr ⟨hq, ⟨ψ₀⟩⟩)
      (fun _ _ _ hcent _ _ hα' hβ' hα2' hβ2' hc' hα1' hβ1' =>
        noE4_psu hU hq2 hcent hα' hβ' hα2' hβ2' hc' hα1' hβ1')

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec16

theorem step168OneZero_of_items (h138 : Item138N) (h1612 : Step1612) (h146 : Item146S14) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Empty168 G A c L → ∀ Y ∈ scriptY3 A (lB A), ∀ T : Subgroup G,
        CFSG.Open.fusionIsSylowIn 2 T Y → A ≤ Subgroup.normalizer (T : Set G) →
        ∀ I₁ ∈ scriptY3Star A (lB A), ∀ I₂ ∈ scriptY3Star A (lB A), Y ≤ I₁ → Y ≤ I₂ →
          CFSG.Open.fusionIsSylowIn 2 T I₁ → deltaZero A (lB A) I₁ = ⊥ → I₁ = I₂ :=
  step168OneZero_of_noE4 h138 h1612 h146 ks168NoE4

end CFSG.RankThree.PartTwo.Sec17
