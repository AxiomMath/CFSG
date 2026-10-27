module

public import CFSG.Quasithin.Vol2.Ch11SecAKA5
public import CFSG.Quasithin.Vol2.KGNatSp4Levi

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.QuasithinUnique.Vol2Native.A312L (blkQ blkQ_apply blkIdx sigma2 spMat)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (stabilizer flag)
open CFSG.Open (pCoreOf)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (mem_pCoreOf_Q0_iff pCoreOf_Q0_eq)

namespace KA

variable {K : Type} [Field K]

theorem eq_one_of_pow_two_pow [CharP K 2] {x : K} {k : ℕ} (h : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : (x - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp h1)

theorem exists_statedSp_of_isometry {L : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K)}
    (hbij : Function.Bijective L)
    (hB : ∀ x y, Matrix.toBilin' (spJ K) (L x) (L y) = Matrix.toBilin' (spJ K) x y) :
    ∃ N : StatedSp 2 K, ∀ v, mat 2 K N *ᵥ v = L v := by
  set g := LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.ofBijective L hbij)
  have hg : ∀ x y, Matrix.toBilin' (spJ K) ((g : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] _) x)
      ((g : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] _) y) = Matrix.toBilin' (spJ K) x y := hB
  refine ⟨⟨_, toLin_symm_mem_statedSp hg⟩, fun v => ?_⟩
  change ((Matrix.GeneralLinearGroup.toLin.symm g : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = L v
  rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin, MulEquiv.apply_symm_apply]
  rfl

theorem spMat_eq_mulVec (N : StatedSp 2 K) (i j : Fin 2 ⊕ Fin 2) :
    spMat N i j = (mat 2 K N *ᵥ Pi.single j 1) i := by
  rw [Matrix.mulVec_single_one]
  rfl

omit [Field K] in
theorem eq_plane {K : Type} [Field K] (v : Fin 2 ⊕ Fin 2 → K) (h2 : v (.inr 0) = 0)
    (h3 : v (.inr 1) = 0) : v = v (.inl 0) • vec4 1 0 0 0 + v (.inl 1) • vec4 0 1 0 0 :=
  vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4, h2]) (by simp [vec4, h3])

theorem single_inl0 : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) = vec4 1 0 0 0 :=
  vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4]) (by simp [vec4])

theorem single_inl1 : (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → K) = vec4 0 1 0 0 :=
  vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4]) (by simp [vec4])

theorem single_inr1 : (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → K) = vec4 0 0 0 1 :=
  vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4]) (by simp [vec4])

theorem vec4_e0_mem_spLine : (vec4 1 0 0 0 : Fin 2 ⊕ Fin 2 → K) ∈ spLine K :=
  ⟨rfl, rfl, rfl⟩

variable [Finite K] [CharP K 2]

theorem exists_pCore_eq (hK4 : ∃ s : Finset K, s.card = 4)
    {T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)} {σ : K →+* K}
    (hσ : ∀ (c : K) (x : Fin 2 ⊕ Fin 2 → K), T (c • x) = σ c • T x)
    (hL : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ x,
      T (mat 2 K γ *ᵥ x) = mat 2 K γ' *ᵥ T x)
    (hinj : Function.Injective T) (hline : T (vec4 1 0 0 0) ∈ spLine K)
    (hlevi : ∀ M ∈ perfectCore (Q2 K 0), ∃ N ∈ pCoreOf 2 (perfectCore (Q2 K 0)), ∀ v,
      T (mat 2 K M *ᵥ v) = mat 2 K N *ᵥ (mat 2 K M *ᵥ T v))
    {k : ℕ} (hk : ∀ v, (⇑T)^[2 ^ k] v = v) :
    ∃ N ∈ pCoreOf 2 (perfectCore (Q2 K 0)), ∀ v, mat 2 K N *ᵥ v = T v := by
  obtain ⟨hσ1, ha2, ha3, hb2, hb1, hab, ha1⟩ := shape_of_levi hK4 hσ hL hinj hline hlevi
  have hlin : ∀ (c : K) x, T (c • x) = c • T x := fun c x => by rw [hσ, hσ1]
  obtain ⟨l1, l2, l3⟩ := hline
  obtain ⟨lam, hlam⟩ : ∃ l, T (vec4 1 0 0 0) (.inl 0) = l := ⟨_, rfl⟩
  obtain ⟨a₁, ha₁⟩ : ∃ a, T (vec4 0 1 0 0) (.inl 1) = a := ⟨_, rfl⟩
  rw [ha₁] at hab ha1
  have he0 : T (vec4 1 0 0 0) = lam • vec4 1 0 0 0 :=
    vec4_eq (by rw [Pi.smul_apply, vec4_apply_inl0, smul_eq_mul, mul_one, hlam])
      (by rw [Pi.smul_apply, vec4_apply_inl1, smul_eq_mul, mul_zero, l1])
      (by rw [Pi.smul_apply, vec4_apply_inr0, smul_eq_mul, mul_zero, l2])
      (by rw [Pi.smul_apply, vec4_apply_inr1, smul_eq_mul, mul_zero, l3])
  have hplane : ∀ v : Fin 2 ⊕ Fin 2 → K, v (.inr 0) = 0 → v (.inr 1) = 0 →
      (T v) (.inl 1) = a₁ * v (.inl 1) ∧ (T v) (.inr 0) = 0 ∧ (T v) (.inr 1) = 0 := by
    intro v h2 h3
    have hTv : T v = v (.inl 0) • (lam • vec4 1 0 0 0) + v (.inl 1) • T (vec4 0 1 0 0) := by
      conv_lhs => rw [eq_plane v h2 h3]
      rw [map_add, hlin, hlin, he0]
    rw [hTv]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec4_apply_inl1, vec4_apply_inr0,
      vec4_apply_inr1, ha2, ha3, ha₁]
    exact ⟨by ring, by ring, by ring⟩
  have hit0 : ∀ m : ℕ, (⇑T)^[m] (vec4 1 0 0 0) = lam ^ m • vec4 1 0 0 0 := by
    intro m
    induction m with
    | zero => rw [Function.iterate_zero, id, pow_zero, one_smul]
    | succ m ih => rw [Function.iterate_succ_apply', ih, hlin, he0, smul_smul, pow_succ]
  have hit1 : ∀ m : ℕ, ((⇑T)^[m] (vec4 0 1 0 0)) (.inl 1) = a₁ ^ m ∧
      ((⇑T)^[m] (vec4 0 1 0 0)) (.inr 0) = 0 ∧ ((⇑T)^[m] (vec4 0 1 0 0)) (.inr 1) = 0 := by
    intro m
    induction m with
    | zero => exact ⟨by rw [pow_zero]; rfl, rfl, rfl⟩
    | succ m ih =>
      obtain ⟨h1, h2, h3⟩ := hplane _ ih.2.1 ih.2.2
      rw [Function.iterate_succ_apply', h1, ih.1, pow_succ, mul_comm]
      exact ⟨rfl, h2, h3⟩
  have hlam1 : lam = 1 := by
    have h := congrFun ((hit0 (2 ^ k)).symm.trans (hk _)) (.inl 0)
    rw [Pi.smul_apply, vec4_apply_inl0, smul_eq_mul, mul_one] at h
    exact eq_one_of_pow_two_pow h
  have ha11 : a₁ = 1 := by
    have h := (hit1 (2 ^ k)).1
    rw [hk] at h
    exact eq_one_of_pow_two_pow (h.symm.trans rfl)
  let TL : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := T, map_add' := map_add T, map_smul' := fun c v => hlin c v }
  have hTL : ∀ v, TL v = T v := fun v => rfl
  obtain ⟨c, hc⟩ := exists_similitude TL fun γ => by
    obtain ⟨γ', hγ'⟩ := hL γ
    exact ⟨γ', fun x => hγ' x⟩
  have hc1 : c = 1 := by
    have h := hc (vec4 0 1 0 0) (vec4 0 0 0 1)
    rw [toBilin'_spJ_apply, toBilin'_spJ_apply] at h
    simp only [Fin.sum_univ_two, hTL, vec4_apply_inl0, vec4_apply_inl1, vec4_apply_inr0,
      vec4_apply_inr1, hb2, ha2, ha3, hab, ha₁, ha11] at h
    linear_combination -h
  have hbij : Function.Bijective TL :=
    ⟨show Function.Injective T from hinj, Finite.surjective_of_injective (f := TL) hinj⟩
  obtain ⟨N, hN⟩ := exists_statedSp_of_isometry hbij fun x y => by rw [hc, hc1, one_mul]
  have hNQ : N ∈ Q2 K 0 := by
    show N ∈ stabilizer 2 K (flag 2 K 1)
    rw [flag_one_eq]
    refine mem_stabilizer_iff'.mpr fun y => ?_
    rw [hN, hTL]
    constructor
    · intro hy
      have hy' : y = y (.inl 0) • vec4 1 0 0 0 :=
        vec4_eq (by simp [vec4]) (by simp [vec4, hy.1]) (by simp [vec4, hy.2.1])
          (by simp [vec4, hy.2.2])
      rw [hy', hlin, he0, hlam1, one_smul]
      exact (spLine K).smul_mem _ vec4_e0_mem_spLine
    · intro hy
      have hy' : T y = T ((T y) (.inl 0) • vec4 1 0 0 0) := by
        rw [hlin, he0, hlam1, one_smul]
        exact vec4_eq (by simp [vec4]) (by simp [vec4, hy.1]) (by simp [vec4, hy.2.1])
          (by simp [vec4, hy.2.2])
      rw [hinj hy']
      exact (spLine K).smul_mem _ vec4_e0_mem_spLine
  have hχ : spMat N (.inl 0) (.inl 0) = 1 := by
    rw [spMat_eq_mulVec, single_inl0, hN, hTL, hlam, hlam1]
  have e11 : spMat N (.inl 1) (.inl 1) = 1 := by
    rw [spMat_eq_mulVec, single_inl1, hN, hTL, ha₁, ha11]
  have e13 : spMat N (.inl 1) (.inr 1) = 0 := by
    rw [spMat_eq_mulVec, single_inr1, hN, hTL, hb1]
  have e31 : spMat N (.inr 1) (.inl 1) = 0 := by
    rw [spMat_eq_mulVec, single_inl1, hN, hTL, ha3]
  have e33 : spMat N (.inr 1) (.inr 1) = 1 := by
    rw [spMat_eq_mulVec, single_inr1, hN, hTL, hab, ha11]
  have hB : blkQ 0 ⟨N, hNQ⟩ = 1 := by
    rw [blkQ_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkIdx, sigma2, e11, e13, e31, e33]
  refine ⟨N, ?_, hN⟩
  rw [← pCoreOf_Q0_eq hK4]
  exact (mem_pCoreOf_Q0_iff hK4).mpr ⟨hNQ, hχ, hB⟩

end KA

end CFSG.Quasithin.Vol2.KGNat
