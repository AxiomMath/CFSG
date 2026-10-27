module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofGroup
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldFixed

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Matrix
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace Res4Seven

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem isSimpleGroup_projImage_slPi (hK : PiField π p f K) (hq2 : 2 < p ^ f) :
    IsSimpleGroup (projImage (slPi π 3 (p ^ f) K)) := by
  have := hK.finite
  have : Fact p.Prime := ⟨hK.prime⟩
  cases π
  · have hK' : Nat.card K = (p ^ f) ^ 2 := hK.card
    have hnq : (3, p ^ f) ≠ (3, 2) := by
      intro h
      have := (Prod.mk.inj h).2
      omega
    have hS := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK' 3 le_rfl
      hnq
    exact (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
      (StatedSU 3 (p ^ f) K)).symm.isSimpleGroup
  · have hS := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field K
    exact (MulEquiv.subgroupCongr (projSL_eq_projImage (p ^ f) K)).symm.isSimpleGroup

theorem projImage_slPi_le (hK : PiField π p f K) :
    projImage (slPi π 3 (p ^ f) K) ≤ projImage (glPi π 3 (p ^ f) K) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  exact Subgroup.map_mono (slPi_le_glPi hπ)

theorem commutator_mem_projImage_slPi (hK : PiField π p f K)
    (a b : projImage (glPi π 3 (p ^ f) K)) :
    a * b * a⁻¹ * b⁻¹ ∈ (projImage (slPi π 3 (p ^ f) K)).subgroupOf
      (projImage (glPi π 3 (p ^ f) K)) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨_, A, hA, rfl⟩ := a
  obtain ⟨_, B, hB, rfl⟩ := b
  rw [Subgroup.mem_subgroupOf]
  refine ⟨A * B * A⁻¹ * B⁻¹, (mem_slPi_iff hπ).2 ⟨?_, ?_⟩, ?_⟩
  · exact (glPi π 3 (p ^ f) K).mul_mem ((glPi π 3 (p ^ f) K).mul_mem
      ((glPi π 3 (p ^ f) K).mul_mem hA hB) ((glPi π 3 (p ^ f) K).inv_mem hA))
      ((glPi π 3 (p ^ f) K).inv_mem hB)
  · have h : GeneralLinearGroup.det (A * B * A⁻¹ * B⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [mul_comm (GeneralLinearGroup.det A) (GeneralLinearGroup.det B)]
      group
    have h' := congrArg Units.val h
    rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at h'
  · simp only [map_mul, map_inv]
    rfl

theorem mk_scalar_eq_one (u : Kˣ) :
    ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 3) u) = 1 := by
  rw [mk_eq_one_iff_mem_statedScalars]
  exact ⟨u, rfl⟩

theorem diagTau_pow_three {τ : K} (hτ : τ ^ 3 = 1) : diagTau hτ ^ 3 = 1 := by
  ext i j
  rw [Units.val_pow_eq_pow_val, coe_diagTau, Units.val_one]
  have h6 : τ ^ 2 * (τ ^ 2 * τ ^ 2) = 1 := by
    calc τ ^ 2 * (τ ^ 2 * τ ^ 2) = (τ ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hτ, one_pow]
  have h3 : τ * (τ * τ) = 1 := by rw [← hτ]; ring
  fin_cases i <;> fin_cases j <;> simp [pow_three, mul_apply, Fin.sum_univ_three, h3, h6]

theorem cycThree_pow_three : (cycThree : GL (Fin 3) K) ^ 3 = 1 :=
  CFSG.RankThree.PartTwo.Sec4.cycThree_pow_three

theorem diagTau_mul_cycThree {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) :
    diagTau hτ * cycThree =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * (cycThree * diagTau hτ) := by
  ext i j
  have h3 : τ * (τ * τ) = 1 := by rw [← hτ]; ring
  simp only [Units.val_mul, coe_diagTau, coe_cycThree, GeneralLinearGroup.coe_scalar,
    Units.val_mk0]
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h3, sq]

theorem mk_cycThree_ne {D : GL (Fin 3) K} (hD : ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    2 0 = 0) : ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) ≠ ProjGenLinGroup.mk D := by
  intro h
  have h1 : ProjGenLinGroup.mk (cycThree * D⁻¹) = 1 := by
    rw [map_mul, h, map_inv, mul_inv_cancel]
  rw [mk_eq_one_iff_mem_statedScalars] at h1
  obtain ⟨u, hu⟩ := h1
  have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hu
  simp only [GeneralLinearGroup.coe_scalar, Units.val_mul, coe_cycThree] at h2
  simp [mul_apply, Fin.sum_univ_three] at h2
  rw [← Matrix.coe_units_inv, hD] at h2
  exact u.ne_zero h2

variable [Finite K]

theorem not_hasType424_projImage_glPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) : ¬ Sec11.KS11Lie2Proof.HasType424 (projImage (glPi π 3 (p ^ f) K)) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  set Γ := projImage (glPi π 3 (p ^ f) K) with hΓ
  set S := projImage (slPi π 3 (p ^ f) K) with hS
  have hSΓ : S ≤ Γ := projImage_slPi_le hK
  have : IsSimpleGroup S := isSimpleGroup_projImage_slPi hK hq2
  set N : Subgroup Γ := S.subgroupOf Γ with hN
  have : IsSimpleGroup N := (Subgroup.subgroupOfEquivOfLe hSΓ).isSimpleGroup
  have hdS := diagTau_mem_slPi hπ hq' hτ
  have hcS : (cycThree : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K := cycThree_mem_slPi hπ
  set x : Γ := ⟨ProjGenLinGroup.mk (diagTau hτ), hSΓ ⟨_, hdS, rfl⟩⟩ with hx
  set y : Γ := ⟨ProjGenLinGroup.mk cycThree, hSΓ ⟨_, hcS, rfl⟩⟩ with hy
  have hxy : x * y = y * x := by
    apply Subtype.ext
    show ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk cycThree =
      ProjGenLinGroup.mk cycThree * ProjGenLinGroup.mk (diagTau hτ)
    rw [← map_mul, ← map_mul, diagTau_mul_cycThree hτ hτ0, map_mul, mk_scalar_eq_one, one_mul]
  have hc : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hxy
  refine Sec11.KS11Lie2Proof.not_hasType424_of_simple N (commutator_mem_projImage_slPi hK)
    (x := x) (y := y) ⟨_, hdS, rfl⟩ ⟨_, hcS, rfl⟩ ?_ ?_ ?_ (by rw [hc]; exact Commute.one_left _)
    (by rw [hc]; exact Commute.one_left _) ?_
  · intro h1
    have h2 : ProjGenLinGroup.mk (diagTau hτ) = 1 := congrArg Subtype.val h1
    rw [mk_eq_one_iff_mem_statedScalars] at h2
    obtain ⟨u, hu⟩ := h2
    have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hu
    have h22 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) hu
    simp [GeneralLinearGroup.coe_scalar, coe_diagTau] at h00 h22
    exact hτ1 (by rw [← h00, h22, Units.val_one])
  · apply Subtype.ext
    show ProjGenLinGroup.mk (diagTau hτ) ^ 3 = 1
    rw [← map_pow, diagTau_pow_three hτ, map_one]
  · apply Subtype.ext
    show ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) ^ 3 = 1
    rw [← map_pow, cycThree_pow_three, map_one]
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hx3 : x ^ 3 = 1 := by
      apply Subtype.ext
      show ProjGenLinGroup.mk (diagTau hτ) ^ 3 = 1
      rw [← map_pow, diagTau_pow_three hτ, map_one]
    have hx3z : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
    have hk3 : x ^ (k % 3) = y := by rw [← zpow_eq_zpow_emod k hx3z, hk]
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have h1 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    obtain ⟨m, hm3, hmk⟩ : ∃ m : ℕ, m < 3 ∧ (m : ℤ) = k % 3 :=
      ⟨(k % 3).toNat, by omega, Int.toNat_of_nonneg h0⟩
    rw [← hmk, zpow_natCast] at hk3
    have hval : ProjGenLinGroup.mk (diagTau hτ ^ m) =
        ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) := by
      rw [map_pow]
      exact congrArg Subtype.val hk3
    refine mk_cycThree_ne ?_ hval.symm
    have hinv : (((diagTau hτ)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        !![τ ^ 2, 0, 0; 0, τ, 0; 0, 0, 1] := rfl
    interval_cases m
    · simp
    · rw [pow_one, hinv]
      simp
    · rw [← inv_pow, pow_two, Units.val_mul, hinv]
      simp [mul_apply, Fin.sum_univ_three]

theorem not_hasType424_of_isSolvable {Γ : Type} [Group Γ] (hΓ : Group.IsSolvable Γ) :
    ¬ Sec11.KS11Lie2Proof.HasType424 Γ := by
  rintro ⟨L, ⟨hLp, -, hLq⟩, -⟩
  have : Group.IsSolvable L := inferInstance
  have hL := Sec11.KS11Lie4Proof.eq_bot_of_isPerfect_of_isSolvable hLp this
  subst hL
  obtain ⟨-, -, u, v, huv⟩ := hLq
  exact huv (Subsingleton.elim _ _)

omit [Finite K] in
theorem not_hasType424_projImage_glPi_two (hK : PiField false p f K) (h2 : p ^ f = 2) :
    ¬ Sec11.KS11Lie2Proof.HasType424 (projImage (glPi false 3 (p ^ f) K)) :=
  not_hasType424_of_isSolvable (Sec13.isSolvable_projImage_glPi_two hK h2)

theorem two_pow_mod_three_of_odd' {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_of_even' {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem not_hasType424_of_mulEquiv_pgu {X : Type} [Group X] [Finite X] {n : ℕ} (hn : Odd n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (e : X ≃* projImage (glPi false 3 (2 ^ n) K)) :
    ¬ Sec11.KS11Lie2Proof.HasType424 X := by
  have hPi : PiField false 2 n K := ⟨Nat.prime_two, hn.pos, hK⟩
  intro h
  have h' := h.of_mulEquiv e
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have hn1 : n = 1 := by
      obtain ⟨k, rfl⟩ := hn
      omega
    subst hn1
    exact not_hasType424_projImage_glPi_two hPi (by norm_num) h'
  · have hq2 : 2 < 2 ^ n := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge
    exact not_hasType424_projImage_glPi hPi (two_pow_mod_three_of_odd' hn) hq2 h'

theorem not_hasType424_of_mulEquiv_pgl {X : Type} [Group X] [Finite X] {n : ℕ} (hn : Even n)
    (hn1 : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : X ≃* projImage (glPi true 3 (2 ^ n) K)) : ¬ Sec11.KS11Lie2Proof.HasType424 X := by
  have hPi : PiField true 2 n K := ⟨Nat.prime_two, hn1, hK⟩
  have hge : 2 ≤ n := by
    obtain ⟨k, rfl⟩ := hn
    omega
  have hq2 : 2 < 2 ^ n := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge
  exact fun h => not_hasType424_projImage_glPi hPi (two_pow_mod_three_of_even' hn) hq2
    (h.of_mulEquiv e)

end Res4Seven

end CFSG.RankThree.PartTwo.Sec4
