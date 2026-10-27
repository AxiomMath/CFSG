module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenFlags
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public section

namespace CFSG.RankThree.PartTwo.Census

open Matrix CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.BorelTits

variable {K : Type} [Field K] {f : ℕ}

theorem coprime_card_two_of_pow_three {G : Type*} [Group G] [Finite G]
    (h : ∀ g : G, g ^ 3 = 1) : Nat.Coprime (Nat.card G) 2 := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro h2
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have := orderOf_dvd_of_pow_eq_one (h g)
  rw [hg] at this
  exact absurd this (by norm_num)

theorem det_natRep_statedSU (h : UnitaryFieldData 2 f K) {n : ℕ} (g : StatedSU n (2 ^ f) K) :
    LinearMap.det (natRep (StatedSU n (2 ^ f) K) g) = 1 := by
  change LinearMap.det (Matrix.toLin' ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1
  rw [LinearMap.det_toLin']
  exact ((mem_unitarySU_iff h).mp g.2).1

theorem exists_natRep_eq_smul {n : ℕ} {H : Subgroup (GL (Fin n) K)} {z : H}
    (hz : z ∈ (StatedScalars (Fin n) K).subgroupOf H) : ∃ c : K, natRep H z = c • 1 := by
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hz
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  rw [natRep_apply, ← hc, GeneralLinearGroup.coe_scalar, scalar_apply]
  funext i
  simp [mulVec_diagonal]

theorem statedScalars_subgroupOf_le_center {n : ℕ} (H : Subgroup (GL (Fin n) K)) :
    (StatedScalars (Fin n) K).subgroupOf H ≤ Subgroup.center H := by
  intro z hz
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hz
  have hcen : (z : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, hc⟩
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext ((Subgroup.mem_center_iff.mp hcen) g)

theorem pow_eq_one_of_mem_statedScalars (h : UnitaryFieldData 2 f K) {n : ℕ}
    {z : StatedSU n (2 ^ f) K}
    (hz : z ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)) : z ^ n = 1 := by
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hz
  have hdet := ((mem_unitarySU_iff h).mp z.2).1
  rw [← hc, GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hdet
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hc, ← map_pow,
    show c ^ n = 1 from Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hdet), map_one,
    OneMemClass.coe_one]

theorem localRank_three_statedSU_four_le [Finite K] (h : UnitaryFieldData 2 f K) :
    localRank 3 (StatedProj (StatedSU 4 (2 ^ f) K)) ≤ 2 := by
  have : CharP K 2 := h.charP
  set H := StatedSU 4 (2 ^ f) K
  set Z := (StatedScalars (Fin 4) K).subgroupOf H
  have hZ1 : ∀ z ∈ Z, z = 1 := by
    intro z hz
    have h4 := pow_eq_one_of_mem_statedScalars h hz
    have h2 : (z ^ 2) * (z ^ 2) = 1 := by rw [← pow_add]; exact h4
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hz
    have hc4 : (c : K) ^ 4 = 1 := by
      have := congrArg (fun g : H => ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0) h4
      simp only [Subgroup.coe_pow, ← hc, ← map_pow, GeneralLinearGroup.coe_scalar,
        scalar_apply, diagonal_apply_eq, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one, one_apply_eq] at this
      exact this
    have hc2 : (c : K) ^ 2 = 1 := eq_one_of_mul_self_eq_one (by rw [← pow_add]; exact hc4)
    have hc1 : (c : K) = 1 := eq_one_of_mul_self_eq_one (by rw [← pow_two]; exact hc2)
    apply Subtype.ext
    rw [OneMemClass.coe_one, ← hc, show c = 1 from Units.ext hc1, map_one]
  have hcardZ : Nat.card Z = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    exact fun z hz => (Subgroup.mem_bot).mpr (hZ1 z hz)
  have hZc : Z ≤ Subgroup.center H := by
    intro z hz
    rw [hZ1 z hz]
    exact Subgroup.one_mem _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine localRank_quotient_le_of_central Z hZc (by rw [hcardZ]; norm_num) Nat.prime_three
    fun P hP0 hP2 E _ hEN h3 hcomm => ?_
  have hab : ∀ x y : E, x * y = y * x := by
    intro x y
    have := hZ1 _ (hcomm x x.2 y y.2)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  let := commGroupOfCommute E hab
  set F := unitaryForm 2 f h.card_eq_sq 4
  set ρ := natRep H
  have hρ : IsIsometric F ρ := isIsometric_natRep_statedSU h.card_eq_sq 4
  have hle := card_le_nine_of_isotropic (A := E) (fun x => Subtype.ext (hZ1 _ (h3 x x.2)))
    (ρ.comp E.subtype) ((natRep_injective H).comp Subtype.val_injective)
    (fun x => det_natRep_statedSU h _) (Module.finrank_fin_fun K) F
    (fun x u v => hρ x u v) (W := isoSeq F ρ P 1)
    (fun x w hw => apply_mem_isoSeq F ρ hρ P 1 (hEN x.2) hw)
    (isoSeq_one_ne_bot F ρ 2 hρ (natRep_injective H) P hP2 hP0)
    (isoSeq_isTotallyIsotropic F ρ P 1)
  rw [hcardZ, mul_one]
  omega

theorem localRank_three_statedSU_three_le [Finite K] (h : UnitaryFieldData 2 f K) :
    localRank 3 (StatedProj (StatedSU 3 (2 ^ f) K)) ≤ 2 := by
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := StatedSU 3 (2 ^ f) K
  set Z := (StatedScalars (Fin 3) K).subgroupOf H
  have hZc : Z ≤ Subgroup.center H := statedScalars_subgroupOf_le_center H
  have hZ3 : Nat.Coprime (Nat.card Z) 2 :=
    coprime_card_two_of_pow_three fun z => Subtype.ext (pow_eq_one_of_mem_statedScalars h z.2)
  refine localRank_quotient_le_of_central Z hZc hZ3 Nat.prime_three
    fun P hP0 hP2 E _ hEN h3 hcomm => ?_
  set F := unitaryForm 2 f h.card_eq_sq 3
  set ρ := natRep H
  have hρ : IsIsometric F ρ := isIsometric_natRep_statedSU h.card_eq_sq 3
  set W := isoSeq F ρ P 1
  have hW0 : W ≠ ⊥ := isoSeq_one_ne_bot F ρ 2 hρ (natRep_injective H) P hP2 hP0
  have hWt : F.IsTotallyIsotropic W := isoSeq_isTotallyIsotropic F ρ P 1
  have hWV : W ≠ ⊤ := by
    intro htop
    have h1 := F.finrank_perp W
    have h2 : Module.finrank K W ≤ Module.finrank K (F.perp W) := Submodule.finrank_mono hWt
    rw [htop, finrank_top, Module.finrank_fin_fun] at h1 h2
    omega
  have hle := card_le_of_central_dim_three ρ (natRep_injective H) (det_natRep_statedSU h)
    (Module.finrank_fin_fun K) Z (fun z hz => exists_natRep_eq_smul hz) h3 hcomm
    (W := W) (fun x hx w hw => apply_mem_isoSeq F ρ hρ P 1 (hEN hx) hw) hW0 hWV
  calc Nat.card E ≤ 9 * Nat.card Z := hle
    _ = 3 ^ 2 * Nat.card Z := by norm_num

theorem card_statedSU_five_four [Finite K] (h : UnitaryFieldData 2 2 K) :
    Nat.card (StatedSU 5 (2 ^ 2) K) = 4 ^ 10 * 254840625 := by
  have hU := (CFSG.LinearGroups.unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin 5) (Fin 5) K)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun K) (by norm_num)).2.1
  have hprod : ∏ i ∈ Finset.Icc 2 5, (((2 ^ 2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 254840625 := by decide
  rw [hprod] at hU
  have : (Nat.card (StatedSU 5 (2 ^ 2) K) : ℤ) = 4 ^ 10 * 254840625 := by
    rw [show StatedSU 5 (2 ^ 2) K = unitarySU 2 2 K 5 from rfl, unitarySU_eq_gramSU h,
      card_gramSU, hU]
    norm_num
  exact_mod_cast this

theorem localRank_three_statedSU_five_four_le [Finite K] (h : UnitaryFieldData 2 2 K) :
    localRank 3 (StatedProj (StatedSU 5 (2 ^ 2) K)) ≤ 2 := by
  refine localRank_le_of_pRank_le Nat.prime_three (pRank_le_two_of_not_dvd Nat.prime_three ?_)
  intro hd
  have := hd.trans (Subgroup.card_quotient_dvd_card _)
  rw [card_statedSU_five_four h] at this
  exact absurd this (by decide)

end CFSG.RankThree.PartTwo.Census
