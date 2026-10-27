module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeA
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTransport

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly

variable {d p : ℕ} {K : Type} [Field K]

section Perm

variable [CharP K 2]

@[expose] noncomputable def permSL (σ : Equiv.Perm (Fin d)) : SpecialLinearGroup (Fin d) K :=
  ⟨σ.permMatrix K, det_permMatrix_char_two σ⟩

theorem coe_permSL (σ : Equiv.Perm (Fin d)) :
    ((permSL σ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) = σ.permMatrix K :=
  rfl

theorem permSL_inv (σ : Equiv.Perm (Fin d)) :
    (permSL σ : SpecialLinearGroup (Fin d) K)⁻¹ = permSL σ⁻¹ := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_permSL, coe_permSL, ← permMatrix_mul,
    mul_inv_cancel, permMatrix_one, Matrix.SpecialLinearGroup.coe_one]

theorem coe_permSL_conj {D : SpecialLinearGroup (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) (σ : Equiv.Perm (Fin d)) :
    ((permSL σ * D * (permSL σ)⁻¹ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (t ∘ σ) := by
  rw [permSL_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_permSL, coe_permSL, hD, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    submatrix_submatrix, Equiv.Perm.inv_def, Equiv.symm_symm]
  exact submatrix_diagonal_equiv t σ

end Perm

section Pair

@[expose] def ggPairVec (k l : Fin d) (μ : K) : Fin d → K :=
  Pi.mulSingle k μ * Pi.mulSingle l μ⁻¹

theorem ggPairVec_apply (k l : Fin d) (μ : K) (m : Fin d) :
    ggPairVec k l μ m = (if m = k then μ else 1) * (if m = l then μ⁻¹ else 1) := by
  simp [ggPairVec, Pi.mulSingle_apply]

theorem prod_ggPairVec {k l : Fin d} (μ : K) (hμ : μ ≠ 0) : ∏ m, ggPairVec k l μ m = 1 := by
  simp only [ggPairVec, Pi.mul_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.prod_pi_mulSingle']
  simp [mul_inv_cancel₀ hμ]

theorem pow_ggPairVec {k l : Fin d} {μ : K} (hμ : μ ^ p = 1) (m : Fin d) :
    ggPairVec k l μ m ^ p = 1 := by
  rw [ggPairVec_apply, mul_pow]
  split_ifs <;> simp [hμ, inv_pow]

theorem ggPairVec_comp (k l : Fin d) (μ : K) (σ : Equiv.Perm (Fin d)) :
    ggPairVec k l μ ∘ σ = ggPairVec (σ.symm k) (σ.symm l) μ := by
  funext m
  simp only [Function.comp_apply, ggPairVec_apply, ← Equiv.eq_symm_apply]

theorem ggPairVec_pow (k l : Fin d) (μ : K) (n : ℕ) :
    (fun m => ggPairVec k l μ m ^ n) = ggPairVec k l (μ ^ n) := by
  funext m
  rw [ggPairVec_apply, ggPairVec_apply, mul_pow]
  split_ifs <;> simp [inv_pow]

theorem ggPairVec_swap {k l : Fin d} (μ : K) :
    ggPairVec l k μ = fun m => (ggPairVec k l μ m)⁻¹ := by
  funext m
  rw [ggPairVec_apply, ggPairVec_apply]
  split_ifs <;> simp [mul_comm]

end Pair

section Diag

theorem coe_inv_SL_of_diagonal {D : SpecialLinearGroup (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) :
    ((D⁻¹ : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal fun i => (t i)⁻¹ := by
  have ht : ∏ i, t i = 1 := by
    have h := D.2
    rw [hD, det_diagonal] at h
    exact h
  have ht0 : ∀ i, t i ≠ 0 := fun i h0 => by
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0] at ht
    exact zero_ne_one ht
  set E : SpecialLinearGroup (Fin d) K := ⟨diagonal fun i => (t i)⁻¹, by
    rw [det_diagonal, Finset.prod_inv_distrib, ht, inv_one]⟩ with hE
  have hDE : D * E = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, hD, Matrix.SpecialLinearGroup.coe_one]
    change (diagonal t * diagonal fun i => (t i)⁻¹) i j = (1 : Matrix (Fin d) (Fin d) K) i j
    rw [diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ (ht0 _)]
    rfl
  rw [inv_eq_of_mul_eq_one_right hDE]

theorem commute_of_diagonal {D E : SpecialLinearGroup (Fin d) K} {t u : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (hE : (E : Matrix (Fin d) (Fin d) K) = diagonal u) : D * E = E * D := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hD, hE,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  simp only [mul_comm]

end Diag

section Acts

variable {L' : Type} [Group L'] (φ' : SpecialLinearGroup (Fin d) K →* L')

@[expose] def GGActsBy (a : MulAut L') (D : SpecialLinearGroup (Fin d) K) : Prop :=
  ∀ s, a (φ' s) = φ' (D * s * D⁻¹)

variable {φ'}

theorem GGActsBy.one : GGActsBy φ' 1 1 := fun s => by simp

theorem GGActsBy.mul {a b : MulAut L'} {D E : SpecialLinearGroup (Fin d) K}
    (ha : GGActsBy φ' a D) (hb : GGActsBy φ' b E) : GGActsBy φ' (a * b) (D * E) := by
  intro s
  rw [MulAut.mul_apply, hb, ha]
  congr 1
  group

theorem GGActsBy.pow {a : MulAut L'} {D : SpecialLinearGroup (Fin d) K} (ha : GGActsBy φ' a D)
    (n : ℕ) : GGActsBy φ' (a ^ n) (D ^ n) :=
  pow_act ha n

theorem GGActsBy.inv {a : MulAut L'} {D : SpecialLinearGroup (Fin d) K} (ha : GGActsBy φ' a D) :
    GGActsBy φ' a⁻¹ D⁻¹ := by
  intro s
  have h := ha (D⁻¹ * s * D)
  have e : D * (D⁻¹ * s * D) * D⁻¹ = s := by group
  rw [e] at h
  rw [inv_inv, ← h, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem GGActsBy.conj {a : MulAut L'} {D : SpecialLinearGroup (Fin d) K}
    (ha : GGActsBy φ' a D) (P : SpecialLinearGroup (Fin d) K) :
    GGActsBy φ' (MulAut.conj (φ' P) * a * (MulAut.conj (φ' P))⁻¹) (P * D * P⁻¹) := by
  intro s
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
  have e : (φ' P)⁻¹ * φ' s * φ' P = φ' (P⁻¹ * s * P) := by simp only [map_mul, map_inv]
  rw [e, ha]
  simp only [map_mul, map_inv]
  group

theorem GGActsBy.unique (hφ's : Function.Surjective φ') {a b : MulAut L'}
    {D : SpecialLinearGroup (Fin d) K} (ha : GGActsBy φ' a D) (hb : GGActsBy φ' b D) : a = b := by
  ext l
  obtain ⟨s, rfl⟩ := hφ's l
  rw [ha, hb]

theorem GGActsBy.diag_eq (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) (hpd : Nat.Coprime p d)
    (hd : 0 < d) {a : MulAut L'} {D D' : SpecialLinearGroup (Fin d) K} {t t' : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (hD' : (D' : Matrix (Fin d) (Fin d) K) = diagonal t')
    (ht : ∀ i, t i ^ p = 1) (ht' : ∀ i, t' i ^ p = 1) (ha : GGActsBy φ' a D)
    (ha' : GGActsBy φ' a D') : t = t' := by
  have htp : ∏ i, t i = 1 := by
    have h := D.2
    rw [hD, det_diagonal] at h
    exact h
  have ht'p : ∏ i, t' i = 1 := by
    have h := D'.2
    rw [hD', det_diagonal] at h
    exact h
  have ht'0 : ∀ i, t' i ≠ 0 := fun i h0 => by
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0] at ht'p
    exact zero_ne_one ht'p
  set M := D'⁻¹ * D with hM
  have hMmat : (M : Matrix (Fin d) (Fin d) K) = diagonal fun i => (t' i)⁻¹ * t i := by
    rw [hM, Matrix.SpecialLinearGroup.coe_mul, coe_inv_SL_of_diagonal hD', hD, diagonal_mul_diagonal]
  have hMp : M ^ p = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hMmat, diagonal_pow, Matrix.SpecialLinearGroup.coe_one]
    have e : ((fun i => (t' i)⁻¹ * t i) ^ p) = fun _ => (1 : K) := by
      funext i
      simp [mul_pow, inv_pow, ht i, ht' i]
    rw [e, diagonal_one]
  have hfix : ∀ s, φ' (M * s * M⁻¹) = φ' s := by
    intro s
    have h3 : φ' (D * s * D⁻¹) = φ' (D' * s * D'⁻¹) := (ha s).symm.trans (ha' s)
    calc φ' (M * s * M⁻¹) = (φ' D')⁻¹ * φ' (D * s * D⁻¹) * φ' D' := by
          rw [hM]
          simp only [map_mul, map_inv]
          group
      _ = (φ' D')⁻¹ * φ' (D' * s * D'⁻¹) * φ' D' := by rw [h3]
      _ = φ' s := by
          simp only [map_mul, map_inv]
          group
  have hcent : ∀ s : SpecialLinearGroup (Fin d) K, s * M = M * s := fun s =>
    Subgroup.mem_centralizer_singleton_iff.mp (mem_centralizer_of_apply_eq hφker hpd hMp (hfix s))
  have hconst : ∀ i j, (t' i)⁻¹ * t i = (t' j)⁻¹ * t j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    by_contra hne
    have h := (commute_diagonal_iff hMmat).mp
      (hcent (SpecialLinearGroup.transvection hij (1 : K))) i j hne
    rw [CFSG.LinearGroups.coe_transvection] at h
    simp [hij] at h
  set i₀ : Fin d := ⟨0, hd⟩ with hi₀
  set c := (t' i₀)⁻¹ * t i₀ with hc
  have hcp : c ^ p = 1 := by rw [hc, mul_pow, inv_pow, ht i₀, ht' i₀, inv_one, one_mul]
  have hcd : c ^ d = 1 := by
    have h1 : ∏ i, ((t' i)⁻¹ * t i) = c ^ d := by
      rw [Finset.prod_congr rfl (fun i _ => hconst i i₀), Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    rw [← h1, Finset.prod_mul_distrib, Finset.prod_inv_distrib, htp, ht'p, inv_one, one_mul]
  have hc1 : c = 1 := by
    have h := (pow_gcd_eq_one (a := c) (m := p) (n := d)).mpr ⟨hcp, hcd⟩
    rwa [Nat.Coprime.gcd_eq_one hpd, pow_one] at h
  funext i
  have h1 : (t' i)⁻¹ * t i = 1 := by rw [hconst i i₀, ← hc, hc1]
  have h2 := congrArg (fun z => t' i * z) h1
  simp only [mul_one, ← mul_assoc, mul_inv_cancel₀ (ht'0 i), one_mul] at h2
  exact h2

theorem exists_ggActsBy_of_gen {A : Subgroup (MulAut L')}
    (hfull : ∀ t : Fin d → K, (∀ i, t i ^ p = 1) → ∏ i, t i = 1 →
      ∃ a ∈ A, ∃ D : SpecialLinearGroup (Fin d) K,
        (D : Matrix (Fin d) (Fin d) K) = diagonal t ∧ GGActsBy φ' a D)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) (hd : 0 < d) (P : MulAut L' → Prop)
    (hP1 : P 1) (hPmul : ∀ a ∈ A, ∀ b ∈ A, P a → P b → P (a * b))
    (hPv : ∀ k l : Fin d, k ≠ l → ∀ m : ℕ, ∀ a ∈ A, ∀ D : SpecialLinearGroup (Fin d) K,
      (D : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec k l (ζ ^ m)) → GGActsBy φ' a D → P a)
    {t : Fin d → K} (ht : ∀ i, t i ^ p = 1) (htp : ∏ i, t i = 1) :
    ∃ a ∈ A, P a ∧ ∃ D : SpecialLinearGroup (Fin d) K,
      (D : Matrix (Fin d) (Fin d) K) = diagonal t ∧ GGActsBy φ' a D := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  set k₀ : Fin d := ⟨0, hd⟩ with hk₀
  have ht0 : ∀ i, t i ≠ 0 := fun i h0 => by
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0] at htp
    exact zero_ne_one htp
  have hfac : ∀ k, ∃ a ∈ A, P a ∧ ∃ D : SpecialLinearGroup (Fin d) K,
      (D : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec k k₀ (t k)) ∧ GGActsBy φ' a D := by
    intro k
    by_cases hk : k = k₀
    · refine ⟨1, A.one_mem, hP1, 1, ?_, GGActsBy.one⟩
      have e : ggPairVec k k₀ (t k) = fun _ => 1 := by
        funext m
        rw [ggPairVec_apply, hk]
        split_ifs <;> simp [mul_inv_cancel₀ (ht0 _)]
      rw [Matrix.SpecialLinearGroup.coe_one, e, diagonal_one]
    · obtain ⟨m, -, hm⟩ := hζ.eq_pow_of_pow_eq_one (ht k)
      obtain ⟨a, haA, D, hD, ha⟩ := hfull (ggPairVec k k₀ (t k))
        (fun i => pow_ggPairVec (ht k) i) (prod_ggPairVec _ (ht0 k))
      exact ⟨a, haA, hPv k k₀ hk m a haA D (by rw [hD, hm]) ha, D, hD, ha⟩
  have hprod : ∀ s : Finset (Fin d), ∃ a ∈ A, P a ∧ ∃ D : SpecialLinearGroup (Fin d) K,
      (D : Matrix (Fin d) (Fin d) K) = diagonal (∏ k ∈ s, ggPairVec k k₀ (t k)) ∧
        GGActsBy φ' a D := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨1, A.one_mem, hP1, 1, ?_, GGActsBy.one⟩
      rw [Finset.prod_empty, Matrix.SpecialLinearGroup.coe_one]
      exact diagonal_one.symm
    | insert k s hks ih =>
      obtain ⟨a, haA, hPa, D, hD, ha⟩ := ih
      obtain ⟨b, hbA, hPb, E, hE, hb⟩ := hfac k
      refine ⟨b * a, A.mul_mem hbA haA, hPmul b hbA a haA hPb hPa, E * D, ?_, hb.mul ha⟩
      rw [Matrix.SpecialLinearGroup.coe_mul, hE, hD, diagonal_mul_diagonal,
        Finset.prod_insert hks]
      rfl
  obtain ⟨a, haA, hPa, D, hD, ha⟩ := hprod Finset.univ
  refine ⟨a, haA, hPa, D, ?_, ha⟩
  rw [hD]
  congr 1
  funext m
  rw [Finset.prod_apply]
  simp only [ggPairVec_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq Finset.univ m t, ite_eq_left (Finset.mem_univ m)]
  by_cases hm : m = k₀
  · simp only [hm, ite_true, Finset.prod_inv_distrib]
    rw [htp, inv_one, mul_one]
  · simp [hm]

end Acts

section Pairs

theorem exists_perm_pair {k l i j : Fin d} (hkl : k ≠ l) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin d), σ k = i ∧ σ l = j := by
  set σ₁ := Equiv.swap k i with hσ₁
  have hl' : σ₁ l ≠ i := by
    intro h
    apply hkl
    have h1 : σ₁ l = σ₁ k := by rw [h, hσ₁, Equiv.swap_apply_left]
    exact (σ₁.injective h1).symm
  refine ⟨Equiv.swap (σ₁ l) j * σ₁, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hσ₁, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hl') hij
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem ggPairVec_comp_of {k l i j : Fin d} {σ : Equiv.Perm (Fin d)} (hk : σ k = i) (hl : σ l = j)
    (μ : K) : ggPairVec i j μ ∘ σ = ggPairVec k l μ := by
  rw [ggPairVec_comp, ← hk, ← hl, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem mul_inv_comp_swap {t : Fin d → K} (ht0 : ∀ k, t k ≠ 0) {i j : Fin d} (hij : i ≠ j) :
    (fun k => t k * (t (Equiv.swap i j k))⁻¹) = ggPairVec i j (t i * (t j)⁻¹) := by
  funext k
  rw [ggPairVec_apply]
  by_cases hki : k = i
  · subst hki
    rw [Equiv.swap_apply_left, ite_eq_right hij]
    simp
  · by_cases hkj : k = j
    · subst hkj
      rw [Equiv.swap_apply_right, ite_eq_right hki]
      simp [_root_.mul_inv_rev, mul_comm]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, ite_eq_right hki, ite_eq_right hkj, mul_inv_cancel₀ (ht0 k),
        one_mul]

end Pairs

section Main

variable [Finite K] [CharP K 2]

theorem ggTorusIrred_coprime (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hd : 4 ≤ d) (hpd : Nat.Coprime p d) (hsec : SLHasSections d K) :
    GGTorusIrred p (d - 1) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have hd0 : 0 < d := by omega
  have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  obtain ⟨φ, hφs, hφ⟩ := exists_sl_cover hsec ψ hψ hker hperf
  obtain ⟨φ', hφ's, hφ'ker, hdiag, hle, hfull⟩ :=
    exists_diagonal_model hp hpK hd0 hpd hperfSL hψ hker hperf hφs hφ hA hAI
  have hcardA : Nat.card A = p ^ (d - 1) := le_antisymm hle hr
  have hfull' : ∀ t : Fin d → K, (∀ i, t i ^ p = 1) → ∏ i, t i = 1 →
      ∃ a ∈ A, ∃ D : SpecialLinearGroup (Fin d) K,
        (D : Matrix (Fin d) (Fin d) K) = diagonal t ∧ GGActsBy φ' a D := by
    intro t ht htp
    obtain ⟨a, ha, D, hD, haD⟩ := hfull hcardA t ht htp
    exact ⟨a, ha, D, hD, haD⟩
  have hM1 : ∀ a ∈ A, ∃ D : SpecialLinearGroup (Fin d) K, ∃ t : Fin d → K,
      (D : Matrix (Fin d) (Fin d) K) = diagonal t ∧ (∀ i, t i ^ p = 1) ∧ GGActsBy φ' a D := by
    intro a ha
    obtain ⟨D, ⟨t, hD⟩, hDp, haD⟩ := hdiag a ha
    refine ⟨D, t, hD, fun i => ?_, haD⟩
    have h1 : (D : Matrix (Fin d) (Fin d) K) ^ p = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hDp]
      rfl
    rw [hD, diagonal_pow] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa using h2
  have hprod1 : ∀ {D : SpecialLinearGroup (Fin d) K} {t : Fin d → K},
      (D : Matrix (Fin d) (Fin d) K) = diagonal t → ∏ i, t i = 1 := by
    intro D t hD
    have h := D.2
    rw [hD, det_diagonal] at h
    exact h
  have hnz : ∀ {D : SpecialLinearGroup (Fin d) K} {t : Fin d → K},
      (D : Matrix (Fin d) (Fin d) K) = diagonal t → ∀ i, t i ≠ 0 := by
    intro D t hD i h0
    have h := hprod1 hD
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0] at h
    exact zero_ne_one h
  have huniq : ∀ {a b : MulAut L'} {D E : SpecialLinearGroup (Fin d) K} {t : Fin d → K},
      (D : Matrix (Fin d) (Fin d) K) = diagonal t → (E : Matrix (Fin d) (Fin d) K) = diagonal t →
      GGActsBy φ' a D → GGActsBy φ' b E → a = b := by
    intro a b D E t hD hE ha hb
    have hDE : D = E := Subtype.ext (hD.trans hE.symm)
    subst hDE
    exact GGActsBy.unique hφ's ha hb
  have hconj : ∀ {a : MulAut L'} {D : SpecialLinearGroup (Fin d) K} {t : Fin d → K},
      (D : Matrix (Fin d) (Fin d) K) = diagonal t → GGActsBy φ' a D → ∀ σ : Equiv.Perm (Fin d),
      ((permSL σ * D * (permSL σ)⁻¹ : SpecialLinearGroup (Fin d) K) :
          Matrix (Fin d) (Fin d) K) = diagonal (t ∘ σ) ∧
        GGActsBy φ' (MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹)
          (permSL σ * D * (permSL σ)⁻¹) :=
    fun hD ha σ => ⟨coe_permSL_conj hD σ, ha.conj _⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  refine ⟨Set.range fun σ : Equiv.Perm (Fin d) => φ' (permSL σ), ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨σ, rfl⟩ a ha
    obtain ⟨D, t, hD, ht, haD⟩ := hM1 a ha
    have e : φ' (permSL σ) * (a (φ' (permSL σ)))⁻¹ =
        φ' (permSL σ * D * (permSL σ)⁻¹ * D⁻¹) := by
      rw [haD (permSL σ)]
      simp only [map_mul, map_inv]
      group
    have hEmat : ((permSL σ * D * (permSL σ)⁻¹ * D⁻¹ : SpecialLinearGroup (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = diagonal fun i => t (σ i) * (t i)⁻¹ := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_permSL_conj hD σ, coe_inv_SL_of_diagonal hD,
        diagonal_mul_diagonal]
      rfl
    refine ⟨?_, fun a' ha' => ?_⟩
    · rw [e, ← map_pow]
      have h1 : (permSL σ * D * (permSL σ)⁻¹ * D⁻¹) ^ p = 1 := by
        ext i j
        rw [Matrix.SpecialLinearGroup.coe_pow, hEmat, diagonal_pow,
          Matrix.SpecialLinearGroup.coe_one]
        have e2 : ((fun i => t (σ i) * (t i)⁻¹) ^ p) = fun _ => (1 : K) := by
          funext i
          simp [mul_pow, inv_pow, ht]
        rw [e2, diagonal_one]
      rw [h1, map_one]
    · obtain ⟨D', t', hD', -, ha'D⟩ := hM1 a' ha'
      rw [e, ha'D]
      congr 1
      rw [commute_of_diagonal hD' hEmat, mul_inv_cancel_right]
  ·
    intro A' hA'A hA'inv
    by_cases hbot : A' = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨a, haA', ha1⟩ : ∃ a ∈ A', a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hbot (eq_bot_iff.mpr fun a ha => (Subgroup.mem_bot).mpr (hcon a ha))
    obtain ⟨D, t, hD, ht, haD⟩ := hM1 a (hA'A haA')
    obtain ⟨i, j, hij⟩ : ∃ i j, t i ≠ t j := by
      by_contra hcon
      push Not at hcon
      apply ha1
      ext l
      obtain ⟨s, rfl⟩ := hφ's l
      rw [haD s, MulAut.one_apply]
      congr 1
      have hDs : D * s = s * D := by
        ext k m
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hD, diagonal_mul,
          mul_diagonal, hcon k m, mul_comm]
      rw [hDs, mul_inv_cancel_right]
    have hij' : i ≠ j := fun h => hij (h ▸ rfl)
    set lam := t i * (t j)⁻¹ with hlam
    have hlam1 : lam ≠ 1 := by
      intro h
      rw [hlam] at h
      exact hij ((mul_inv_eq_one₀ (hnz hD j)).mp h)
    have hlamp : lam ^ p = 1 := by rw [hlam, mul_pow, inv_pow, ht i, ht j, inv_one, one_mul]
    have hlamprim : IsPrimitiveRoot lam p :=
      IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hlamp hlam1)
    set τ := Equiv.swap i j with hτ
    obtain ⟨hDτ, haτ⟩ := hconj hD haD τ
    have hbA' : a * (MulAut.conj (φ' (permSL τ)) * a * (MulAut.conj (φ' (permSL τ)))⁻¹)⁻¹ ∈ A' :=
      A'.mul_mem haA' (A'.inv_mem (hA'inv _ ⟨τ, rfl⟩ a haA'))
    have hbD := haD.mul haτ.inv
    have hbmat : ((D * (permSL τ * D * (permSL τ)⁻¹)⁻¹ : SpecialLinearGroup (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec i j lam) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_inv_SL_of_diagonal hDτ, hD, diagonal_mul_diagonal,
        ← mul_inv_comp_swap (hnz hD) hij']
      rfl
    have hPv : ∀ k l : Fin d, k ≠ l → ∀ m : ℕ, ∀ c ∈ A, ∀ E : SpecialLinearGroup (Fin d) K,
        (E : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec k l (lam ^ m)) →
        GGActsBy φ' c E → c ∈ A' := by
      intro k l hkl m c _ E hE hcE
      obtain ⟨σ, hσk, hσl⟩ := exists_perm_pair hkl hij'
      have hpowmat : (((D * (permSL τ * D * (permSL τ)⁻¹)⁻¹) ^ m : SpecialLinearGroup (Fin d) K) :
          Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec i j (lam ^ m)) := by
        rw [Matrix.SpecialLinearGroup.coe_pow, hbmat, diagonal_pow, ← ggPairVec_pow]
        rfl
      obtain ⟨hσmat, hσact⟩ := hconj hpowmat (hbD.pow m) σ
      rw [ggPairVec_comp_of hσk hσl] at hσmat
      have heq := huniq hE hσmat hcE hσact
      rw [heq]
      exact hA'inv _ ⟨σ, rfl⟩ _ (A'.pow_mem hbA' m)
    refine le_antisymm hA'A (fun c hc => ?_)
    obtain ⟨E, u, hE, hu, hcE⟩ := hM1 c hc
    obtain ⟨c', -, hc'A', E', hE', hc'E'⟩ := exists_ggActsBy_of_gen hfull' hlamprim hp hd0
      (fun c => c ∈ A') A'.one_mem (fun a _ b _ ha hb => A'.mul_mem ha hb) hPv hu (hprod1 hE)
    rw [huniq hE hE' hcE hc'E']
    exact hc'A'
  ·
    set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
    set j₀ : Fin d := ⟨1, by omega⟩ with hj₀
    have hij₀ : i₀ ≠ j₀ := by simp [hi₀, hj₀]
    obtain ⟨a₁, ha₁, D₁, hD₁, ha₁D⟩ := hfull' (ggPairVec i₀ j₀ ζ)
      (fun m => pow_ggPairVec hζ.pow_eq_one m) (prod_ggPairVec ζ hζ0)
    refine ⟨_, ⟨Equiv.swap i₀ j₀, rfl⟩, a₁, ha₁, fun heq => ?_⟩
    obtain ⟨hτmat, hτact⟩ := hconj hD₁ ha₁D (Equiv.swap i₀ j₀)
    rw [heq] at hτact
    rw [ggPairVec_comp, Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right] at hτmat
    have h1 := GGActsBy.diag_eq hφ'ker hpd hd0 hD₁ hτmat (fun m => pow_ggPairVec hζ.pow_eq_one m)
      (fun m => pow_ggPairVec hζ.pow_eq_one m) ha₁D hτact
    have h2 := congrFun h1 i₀
    rw [ggPairVec_apply, ggPairVec_apply, ite_eq_left rfl, ite_eq_right hij₀, ite_eq_right hij₀, ite_eq_left rfl] at h2
    simp only [mul_one, one_mul] at h2
    exact ne_inv_of_isPrimitiveRoot hζ hp hp2 h2
  ·
    intro f hfA hfmul hfeq
    set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
    set j₀ : Fin d := ⟨1, by omega⟩ with hj₀
    have hij₀ : i₀ ≠ j₀ := by simp [hi₀, hj₀]
    have hζp : ∀ m, ggPairVec i₀ j₀ ζ m ^ p = 1 := fun m => pow_ggPairVec hζ.pow_eq_one m
    obtain ⟨a₁, ha₁, D₁, hD₁, ha₁D⟩ := hfull' (ggPairVec i₀ j₀ ζ) hζp (prod_ggPairVec ζ hζ0)
    have hf1 : f 1 = 1 := by
      have h := hfmul 1 A.one_mem 1 A.one_mem
      rw [mul_one] at h
      have h2 := congrArg (fun z => (f 1)⁻¹ * z) h
      simp only [inv_mul_cancel, inv_mul_cancel_left] at h2
      exact h2.symm
    have hfinv : ∀ a ∈ A, f a⁻¹ = (f a)⁻¹ := by
      intro a ha
      have h := hfmul a⁻¹ (A.inv_mem ha) a ha
      rw [inv_mul_cancel, hf1] at h
      exact eq_inv_of_mul_eq_one_left h.symm
    have hfpow : ∀ a ∈ A, ∀ m : ℕ, f (a ^ m) = (f a) ^ m := by
      intro a ha m
      induction m with
      | zero => simp [hf1]
      | succ m ih => rw [pow_succ, hfmul _ (A.pow_mem ha m) a ha, ih, pow_succ]
    obtain ⟨Dw, w, hDw, hw, hfa₁⟩ := hM1 (f a₁) (hfA a₁ ha₁)
    set τ := Equiv.swap i₀ j₀ with hτ
    obtain ⟨hτmat, hτact⟩ := hconj hD₁ ha₁D τ
    have hτmat' : ((permSL τ * D₁ * (permSL τ)⁻¹ : SpecialLinearGroup (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = diagonal fun m => (ggPairVec i₀ j₀ ζ m)⁻¹ := by
      rw [hτmat, ggPairVec_comp, hτ, Equiv.symm_swap, Equiv.swap_apply_left,
        Equiv.swap_apply_right, ggPairVec_swap]
    have hτa₁ : MulAut.conj (φ' (permSL τ)) * a₁ * (MulAut.conj (φ' (permSL τ)))⁻¹ = a₁⁻¹ :=
      huniq hτmat' (coe_inv_SL_of_diagonal hD₁) hτact ha₁D.inv
    have h1 := hfeq _ ⟨τ, rfl⟩ a₁ ha₁
    rw [hτa₁, hfinv a₁ ha₁] at h1
    obtain ⟨hwτmat, hwτact⟩ := hconj hDw hfa₁ τ
    rw [← h1] at hwτact
    have hw' : (fun m => (w m)⁻¹) = w ∘ τ :=
      GGActsBy.diag_eq hφ'ker hpd hd0 (coe_inv_SL_of_diagonal hDw) hwτmat
        (fun m => by rw [inv_pow, hw m, inv_one]) (fun m => hw (τ m)) hfa₁.inv hwτact
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (fun h => hp2 h.symm)
    have hwk : ∀ k, k ≠ i₀ → k ≠ j₀ → w k = 1 := by
      intro k hki hkj
      have h2 := congrFun hw' k
      simp only [Function.comp_apply, hτ, Equiv.swap_apply_of_ne_of_ne hki hkj] at h2
      have hsq : w k ^ 2 = 1 := by
        rw [sq]
        nth_rewrite 1 [← h2]
        exact inv_mul_cancel₀ (hnz hDw k)
      have h3 := (pow_gcd_eq_one (a := w k) (m := 2) (n := p)).mpr ⟨hsq, hw k⟩
      rwa [hcop.gcd_eq_one, pow_one] at h3
    have hwj : w j₀ = (w i₀)⁻¹ := by
      have h2 := congrFun hw' j₀
      simp only [Function.comp_apply, hτ, Equiv.swap_apply_right] at h2
      rw [← h2, inv_inv]
    obtain ⟨c, -, hc⟩ := hζ.eq_pow_of_pow_eq_one (hw i₀)
    have hwv : w = ggPairVec i₀ j₀ (ζ ^ c) := by
      funext k
      rw [ggPairVec_apply]
      by_cases hki : k = i₀
      · rw [hki, ite_eq_left rfl, ite_eq_right hij₀, hc, mul_one]
      · by_cases hkj : k = j₀
        · rw [hkj, ite_eq_right (Ne.symm hij₀), ite_eq_left rfl, hwj, hc, one_mul]
        · rw [ite_eq_right hki, ite_eq_right hkj, hwk k hki hkj, mul_one]
    have hpowmat : ∀ m : ℕ, ((D₁ ^ m : SpecialLinearGroup (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec i₀ j₀ (ζ ^ m)) := by
      intro m
      rw [Matrix.SpecialLinearGroup.coe_pow, hD₁, diagonal_pow, ← ggPairVec_pow]
      rfl
    have hfa₁c : f a₁ = a₁ ^ c :=
      huniq (by rw [hDw, hwv]) (hpowmat c) hfa₁ (ha₁D.pow c)
    refine ⟨c, fun a ha => ?_⟩
    have hPv : ∀ k l : Fin d, k ≠ l → ∀ m : ℕ, ∀ e ∈ A, ∀ E : SpecialLinearGroup (Fin d) K,
        (E : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec k l (ζ ^ m)) →
        GGActsBy φ' e E → f e = e ^ c := by
      intro k l hkl m e _ E hE heE
      obtain ⟨σ, hσk, hσl⟩ := exists_perm_pair hkl hij₀
      obtain ⟨hσmat, hσact⟩ := hconj (hpowmat m) (ha₁D.pow m) σ
      rw [ggPairVec_comp_of hσk hσl] at hσmat
      have heq := huniq hE hσmat heE hσact
      rw [heq, hfeq _ ⟨σ, rfl⟩ _ (A.pow_mem ha₁ m), hfpow a₁ ha₁ m, hfa₁c,
        show (a₁ ^ c) ^ m = (a₁ ^ m) ^ c by rw [← pow_mul, ← pow_mul, mul_comm]]
      exact conj_pow.symm
    have hP1 : f 1 = 1 ^ c := by rw [hf1, one_pow]
    have hPmul : ∀ a ∈ A, ∀ b ∈ A, f a = a ^ c → f b = b ^ c → f (a * b) = (a * b) ^ c := by
      intro a ha b hb hfa hfb
      have hab : Commute a b := TableB.IsElemAbelian.comm hA ha hb
      rw [hfmul a ha b hb, hfa, hfb, hab.mul_pow]
    obtain ⟨E, u, hE, hu, haE⟩ := hM1 a ha
    obtain ⟨a', -, ha'P, E', hE', ha'E'⟩ := exists_ggActsBy_of_gen hfull' hζ hp hd0
      (fun e => f e = e ^ c) hP1 hPmul hPv hu (hprod1 hE)
    rw [huniq hE hE' haE ha'E']
    exact ha'P

end Main

end CFSG.StandardType.TypeA

end
