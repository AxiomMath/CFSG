module

public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSplit
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofTools
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofU4Lin
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofCharThree

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU projImage)
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open Matrix

namespace Item228Census2Proof

theorem two_pow_mod_fifteen {n : ℕ} (hn : Odd n) : 2 ^ n % 15 = 2 ∨ 2 ^ n % 15 = 8 := by
  obtain ⟨k, rfl⟩ := hn
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    rw [show 2 * (j + j) + 1 = 4 * j + 1 by ring, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  · right
    rw [show 2 * (2 * j + 1) + 1 = 4 * j + 3 by ring, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]

variable {n : ℕ}

theorem card_galoisField_two_mul (hn : 1 ≤ n) :
    Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul, mul_comm]

theorem eq_one_of_pow_five_galoisField (hn : 1 ≤ n) (hodd : Odd n) (μ : GaloisField 2 (2 * n))
    (hμ : μ ^ 5 = 1) : μ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype (GaloisField 2 (2 * n)) := Fintype.ofFinite _
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμ
  have h1 := FiniteField.pow_card_sub_one_eq_one μ hμ0
  rw [Fintype.card_eq_nat_card, card_galoisField_two_mul hn] at h1
  have h2 := two_pow_sq_mod_five hodd
  have hcop : Nat.Coprime 5 ((2 ^ n) ^ 2 - 1) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr ?_
    generalize (2 ^ n) ^ 2 = Q at h2
    omega
  have := (pow_gcd_eq_one (a := μ)).mpr ⟨hμ, h1⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

theorem eq_one_of_pow_four_charTwo {F : Type*} [Field F] [CharP F 2] {μ : F} (hμ : μ ^ 4 = 1) :
    μ = 1 := by
  have hc2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h1 : (μ ^ 2 - 1) ^ 2 = 0 := by linear_combination hμ - (μ ^ 2 - 1) * hc2
  have h2 : μ ^ 2 = 1 := sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h1)
  have h3 : (μ - 1) ^ 2 = 0 := by linear_combination h2 - (μ - 1) * hc2
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h3)

theorem exists_cube_root_galoisField (hn : 1 ≤ n) :
    ∃ ω : GaloisField 2 (2 * n), ω ^ 2 + ω + 1 = 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype (GaloisField 2 (2 * n)) := Fintype.ofFinite _
  have h3 : 3 ∣ Nat.card (GaloisField 2 (2 * n))ˣ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, Fintype.card_eq_nat_card,
      card_galoisField_two_mul hn, ← pow_mul, mul_comm, pow_mul]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 n
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨(u : GaloisField 2 (2 * n)), ?_⟩
  have hu3 : (u : GaloisField 2 (2 * n)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hu1 : (u : GaloisField 2 (2 * n)) ≠ 1 := by
    intro h
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu
    norm_num at hu
  have : ((u : GaloisField 2 (2 * n)) - 1) * ((u : GaloisField 2 (2 * n)) ^ 2 +
      (u : GaloisField 2 (2 * n)) + 1) = 0 := by linear_combination hu3
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hu1)

theorem eq_one_of_scalar_mem_statedSU_four (hn : 1 ≤ n) {l : (GaloisField 2 (2 * n))ˣ}
    (hl : GeneralLinearGroup.scalar (Fin 4) l ∈ StatedSU 4 (2 ^ n) (GaloisField 2 (2 * n))) :
    l = 1 := by
  have h4 := ((CFSG.LinearGroups.scalar_mem_statedSU_iff Nat.prime_two
    (card_galoisField_two_mul hn) (by norm_num) l).mp hl).1
  apply Units.ext
  rw [Units.val_one]
  exact eq_one_of_pow_four_charTwo (by rw [← Units.val_pow_eq_pow_val, h4, Units.val_one])

noncomputable def statedSUFourEquivProjSU (hn : 1 ≤ n) [Fact (Nat.Prime 2)] :
    StatedSU 4 (2 ^ n) (GaloisField 2 (2 * n)) ≃* projSU 4 2 n :=
  (MonoidHom.ofInjective (f := (Matrix.ProjGenLinGroup.mk :
      GL (Fin 4) (GaloisField 2 (2 * n)) →* Matrix.ProjGenLinGroup (Fin 4)
        (GaloisField 2 (2 * n))).comp (StatedSU 4 (2 ^ n) (GaloisField 2 (2 * n))).subtype) (by
    rw [injective_iff_map_eq_one]
    intro A hA
    have hc : (A : GL (Fin 4) (GaloisField 2 (2 * n))) ∈
        Subgroup.center (GL (Fin 4) (GaloisField 2 (2 * n))) :=
      Matrix.ProjGenLinGroup.mk_eq_one.mp hA
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨l, hl⟩ := hc
    have hlmem : GeneralLinearGroup.scalar (Fin 4) l ∈
        StatedSU 4 (2 ^ n) (GaloisField 2 (2 * n)) := hl ▸ A.2
    have hl1 := eq_one_of_scalar_mem_statedSU_four hn hlmem
    apply Subtype.ext
    rw [← hl, hl1, map_one]
    rfl)).trans
    (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact CFSG.RankThree.PartTwo.Census.projImage_statedSU 4 2 n))

theorem orderOf_ne_fifteen_statedSU_four (hn : 1 ≤ n) (hodd : Odd n)
    (A : StatedSU 4 (2 ^ n) (GaloisField 2 (2 * n))) : orderOf A ≠ 15 := by
  intro hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
    ⟨Nat.prime_two, hn, GaloisField.card 2 (2 * n) (by omega)⟩
  set M : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n)) :=
    ((A : GL (Fin 4) (GaloisField 2 (2 * n))) : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n)))
    with hM
  have hcoe : ∀ k : ℕ, (((A ^ k : StatedSU 4 (2 ^ n) (GaloisField 2 (2 * n))) :
      GL (Fin 4) (GaloisField 2 (2 * n))) : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) =
      M ^ k := by
    intro k
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hmem : ∀ k : ℕ, ((A ^ k : StatedSU 4 (2 ^ n) (GaloisField 2 (2 * n))) :
      GL (Fin 4) (GaloisField 2 (2 * n))) ∈ unitarySU 2 n (GaloisField 2 (2 * n)) 4 :=
    fun k => (A ^ k).2
  have hiso : ∀ k : ℕ, ∀ x y, stdHermForm hU 4 (M ^ k *ᵥ x) (M ^ k *ᵥ y) =
      stdHermForm hU 4 x y := by
    intro k x y
    rw [← hcoe]
    exact ((mem_unitarySU_iff_isometry hU).mp (hmem k)).2 x y
  have hdet : ∀ k : ℕ, (M ^ k).det = 1 := by
    intro k
    rw [← hcoe]
    exact ((mem_unitarySU_iff_isometry hU).mp (hmem k)).1
  have hpow : ∀ k : ℕ, M ^ k = 1 → A ^ k = 1 := by
    intro k h
    rw [← hcoe] at h
    exact Subtype.ext (Units.ext h)
  have hA15 : A ^ 15 = 1 := hA ▸ pow_orderOf_eq_one A
  have h15 : M ^ 15 = 1 := by
    rw [← hcoe, hA15]
    rfl
  have hndvd : ∀ k : ℕ, ¬ 15 ∣ k → M ^ k ≠ 1 := fun k hk h1 =>
    hk (hA ▸ orderOf_dvd_of_pow_eq_one (hpow k h1))
  set φ := (Matrix.toLinAlgEquiv' : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n)) ≃ₐ[_]
    Module.End (GaloisField 2 (2 * n)) (Fin 4 → GaloisField 2 (2 * n))) with hφ
  have hφM : ∀ (k : ℕ) (x : Fin 4 → GaloisField 2 (2 * n)), φ (M ^ k) x = M ^ k *ᵥ x :=
    fun k x => Matrix.toLin'_apply _ _
  obtain ⟨ω, hω⟩ := exists_cube_root_galoisField hn
  have hV : Module.finrank (GaloisField 2 (2 * n)) (Fin 4 → GaloisField 2 (2 * n)) = 4 := by
    simp
  refine no_commuting_unitary_three_five (stdHermForm hU 4) hV (q := 2 ^ n) hU.bar_apply
    (two_pow_mod_fifteen hodd) (eq_one_of_pow_five_galoisField hn hodd) hω ?_
    (a := φ (M ^ 5)) (c := φ (M ^ 3)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    intro x hx
    funext i
    have := hx (Pi.single i 1)
    simpa [stdHermForm_apply, Pi.single_apply] using this
  · intro x y
    rw [hφM, hφM]
    exact hiso 5 x y
  · intro x y
    rw [hφM, hφM]
    exact hiso 3 x y
  · rw [← map_mul, ← map_mul, ← pow_add, ← pow_add, add_comm]
  · rw [← map_pow, ← pow_mul, h15, map_one]
  ·
    intro μ hμ
    have hM5 : M ^ 5 = μ • (1 : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) :=
      φ.injective (by rw [hμ, map_smul, map_one])
    have hd := hdet 5
    rw [hM5, det_smul, det_one, Fintype.card_fin, mul_one] at hd
    have hμ1 : μ = 1 := eq_one_of_pow_four_charTwo hd
    rw [hμ1, one_smul] at hM5
    exact hndvd 5 (by norm_num) hM5
  · rw [← map_pow, ← pow_mul, h15, map_one]
  · intro h1
    exact hndvd 3 (by norm_num) (φ.injective (h1.trans (map_one φ).symm))

end Item228Census2Proof

open Item228Census2Proof

theorem census228U4Two_holds : Census228U4Two := by
  intro Y _ _ ⟨n, hn, hodd, ⟨eY⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSimpleGroup (projSU 4 2 n) := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 4 2 n
    (statedClassicalModel_projSU le_rfl hn)).2
  have : Finite (projSU 4 2 n) := Finite.of_equiv _ eY.toEquiv
  have h15 : ∀ g : projSU 4 2 n, orderOf g ≠ 15 := fun g => by
    rw [← MulEquiv.orderOf_eq (statedSUFourEquivProjSU hn).symm g]
    exact orderOf_ne_fifteen_statedSU_four hn hodd _
  refine Or.inr (Item228CensusProof.noL2Normal228_of_mulEquiv eY
    (noL2Normal228_of_simple_perfectResidual fun y hy h5 => ?_))
  exact Item22Res4Proof.not_five_dvd_centralizer_of_no15 h15 hy
    (h5.trans (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _)))

end CFSG.RankThree.PartTwo.Sec21
