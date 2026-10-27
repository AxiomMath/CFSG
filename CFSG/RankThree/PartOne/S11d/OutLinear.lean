module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.RankThree.PartOne.OutStructure

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem linear_D2 {p : ℕ} (hp : p.Prime) (hn : 3 ≤ n) (hdiag : ¬ p ∣ Nat.gcd n (Nat.card K - 1))
    (δ : MulAut (projectiveSL n K)) (hδ : δ ∈ linearAutGroup n K) (k : ℕ)
    (hk : δ ^ (p ^ k) ∈ Inn (projectiveSL n K)) : δ ∈ Inn (projectiveSL n K) := by
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hδ
  have hAk : conjAut n K A ^ (p ^ k) = conjAut n K (A ^ (p ^ k)) := (map_pow _ _ _).symm
  rw [hAk] at hk
  obtain ⟨s, hs⟩ := hk
  obtain ⟨g, rfl⟩ := proj_surjective n K s
  rw [← conjAut_toGL] at hs
  have h1 : conjAut n K (A ^ (p ^ k) * (SpecialLinearGroup.toGL g)⁻¹) = 1 := by
    rw [map_mul, ← hs, map_inv, mul_inv_cancel]
  obtain ⟨u, hu⟩ := (conjAut_eq_one_iff hn _).mp h1
  have hAu : A ^ (p ^ k) = Matrix.GeneralLinearGroup.scalar (Fin n) u *
      SpecialLinearGroup.toGL g := by
    rw [← hu]
    group
  have hdet : (GeneralLinearGroup.det A) ^ (p ^ k) = u ^ n := by
    have h2 := congrArg GeneralLinearGroup.det hAu
    rw [map_pow, map_mul] at h2
    have h3 : GeneralLinearGroup.det (SpecialLinearGroup.toGL g) = 1 := by
      ext
      simp
    have h4 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) u) = u ^ n := by
      ext
      simp [GeneralLinearGroup.scalar]
    rw [h2, h3, h4, mul_one]
  have hndvd : ¬ p ∣ Nat.gcd n (Nat.card Kˣ) := by
    rwa [Nat.card_units]
  obtain ⟨μ, hμ⟩ := exists_pow_eq_of_pow_eq hp hndvd hdet
  have hdetB : (GeneralLinearGroup.det ((GeneralLinearGroup.scalar (Fin n) μ)⁻¹ * A)) = 1 := by
    rw [map_mul, map_inv]
    have : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) μ) = μ ^ n := by
      ext
      simp [GeneralLinearGroup.scalar]
    rw [this, hμ, inv_mul_cancel]
  set B := (GeneralLinearGroup.scalar (Fin n) μ)⁻¹ * A with hB
  have hBmem : (B : Matrix (Fin n) (Fin n) K).det = 1 := by
    have := congrArg (fun x : Kˣ => (x : K)) hdetB
    simpa using this
  let g' : SpecialLinearGroup (Fin n) K := ⟨(B : Matrix (Fin n) (Fin n) K), hBmem⟩
  refine ⟨proj n K g', ?_⟩
  rw [← conjAut_toGL]
  have hAB : A = GeneralLinearGroup.scalar (Fin n) μ * B := by rw [hB]; group
  have hg' : SpecialLinearGroup.toGL g' = B := by
    ext1
    rfl
  rw [hg']
  conv_rhs => rw [hAB, map_mul, conjAut_scalar, one_mul]

theorem mem_of_pow_mem_of_index_le_two {Γ : Type*} [Group Γ] [Finite Γ] (E : Subgroup Γ)
    (h : E.index ≤ 2) {α : Γ} {N : ℕ} (hN : Odd N) (hα : α ^ N ∈ E) : α ∈ E := by
  have h0 : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  by_cases h1 : E.index = 1
  · rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top α
  · have h2 : E.index = 2 := by omega
    obtain ⟨m, rfl⟩ := hN
    have hsq : α * α ∈ E := Subgroup.mul_self_mem_of_index_two h2 α
    have : α = ((α * α) ^ m)⁻¹ * α ^ (2 * m + 1) := by
      rw [pow_succ, pow_mul, sq, ← mul_assoc]
      group
    rw [this]
    exact mul_mem (inv_mem (pow_mem hsq m)) hα

theorem outPNice_projectiveSL {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hdiag : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) : OutPNice p (projectiveSL n K) := by
  obtain ⟨hgenTop, hgen⟩ := automorphism_generation (K := K) hn
  obtain ⟨hID, -, hDn, -, -, ⟨g, -, hg⟩, -, hidx, -, -⟩ :=
    standard_outer_quotients (n := n) (K := K)
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut_projectiveSL n
  have hDnorm : (linearAutGroup n K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact mem_subgroupOf.mp this
  have hpE : ∀ α : MulAut (projectiveSL n K), (∃ k : ℕ, α ^ (p ^ k) ∈ linearAutGroup n K) →
      α ∈ semilinearAutGroup n K := by
    rintro α ⟨k, hk⟩
    have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
      have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
      rwa [hgenTop, Subgroup.relIndex_top_right] at h2
    have hpodd : Odd (p ^ k) := (Nat.Prime.odd_of_ne_two hp hp2).pow
    exact mem_of_pow_mem_of_index_le_two _ hidx' hpodd (linearAutGroup_le_semilinearAutGroup hk)
  have hD3 : ∀ γ α : MulAut (projectiveSL n K), α ∈ semilinearAutGroup n K →
      ⁅γ, α⁆ ∈ linearAutGroup n K := by
    intro γ α hα
    obtain ⟨B, τ, rfl⟩ := mem_semilinearAutGroup_iff.mp hα
    obtain ⟨A, σ, ε, hε, rfl⟩ := hgen γ
    set π := QuotientGroup.mk' (linearAutGroup n K) with hπ
    have hπc : ∀ C : GL (Fin n) K, π (conjAut n K C) = 1 := fun C =>
      (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_linearAutGroup C)
    have hfσ : Commute (π (fieldAut n K σ)) (π (fieldAut n K τ)) := by
      have h1 : fieldAut n K σ * fieldAut n K τ = fieldAut n K τ * fieldAut n K σ := by
        rw [htrans.2.1, htrans.2.1, ringAut_comm K σ τ]
      have h3 := congrArg π h1
      rw [map_mul π, map_mul π] at h3
      exact h3
    have hδf : Commute (π (dualAut n K)) (π (fieldAut n K τ)) := by
      have h1 : dualAut n K * fieldAut n K τ = fieldAut n K τ * dualAut n K := by
        have h2 := htrans.2.2.2.2.2.1 τ
        calc dualAut n K * fieldAut n K τ
            = (dualAut n K * fieldAut n K τ * dualAut n K) * dualAut n K := by
              rw [mul_assoc (dualAut n K * fieldAut n K τ), htrans.2.2.2.1, mul_one]
          _ = fieldAut n K τ * dualAut n K := by rw [h2]
      have h3 := congrArg π h1
      rw [map_mul π, map_mul π] at h3
      exact h3
    have hc : Commute (π (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε))
        (π (conjAut n K B * fieldAut n K τ)) := by
      rw [map_mul, map_mul, map_mul, hπc, hπc, one_mul, one_mul, map_pow]
      exact (hfσ.mul_left (hδf.pow_left ε))
    have h1 : π ⁅conjAut n K A * fieldAut n K σ * dualAut n K ^ ε,
        conjAut n K B * fieldAut n K τ⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr hc
    exact (QuotientGroup.eq_one_iff _).mp h1
  exact outPNice_of_tower hp g hID (fun δ hδ k hk => linear_D2 hp hn hdiag δ hδ k hk) hpE hD3 hg

theorem outPNice_PSL_ge_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    {n m : ℕ} (hn : 3 ≤ n) (h : StatedClassicalModel X .PSL n 2 m)
    (hdiag : ¬ p ∣ Nat.gcd n (2 ^ m - 1)) : OutPNice p X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : X ≃* projectiveSL n K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  refine OutPNice.of_mulEquiv e' (outPNice_projectiveSL hp hp2 hn ?_)
  rwa [hK]

end CFSG.RankThree.PartOne.OutStructure
