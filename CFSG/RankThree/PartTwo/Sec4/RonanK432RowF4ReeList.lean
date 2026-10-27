module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Single
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeCent
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofReeConj
public import CFSG.RankThree.PartOne.KLCE.TypeSU
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.LieType.Ree CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KLCE

theorem exists_commute_notMem_zpowers_of_centralizer {G H : Type} [Group G] [Group H] (y : G)
    (ψ : Subgroup.centralizer ({y} : Set G) ≃* H) (d p : H) (hd : d ^ 3 = 1)
    (hdp : d * p ≠ p * d) : ∃ u : G, u ^ 3 = 1 ∧ y * u = u * y ∧ u ∉ Subgroup.zpowers y := by
  set u0 : Subgroup.centralizer ({y} : Set G) := ψ.symm d with hu0
  have hu0c : (u0 : G) ∈ Subgroup.centralizer ({y} : Set G) := u0.2
  have hcomm : ∀ c : Subgroup.centralizer ({y} : Set G), y * (c : G) = (c : G) * y := by
    intro c
    have hc := c.2
    rw [Subgroup.mem_centralizer_iff] at hc
    exact hc y (Set.mem_singleton y)
  refine ⟨(u0 : G), ?_, ?_, ?_⟩
  · have h3 : u0 ^ 3 = 1 := by
      rw [hu0, ← map_pow, hd, map_one]
    have := congrArg (fun t : Subgroup.centralizer ({y} : Set G) => (t : G)) h3
    simpa using this
  · have hc := hu0c
    rw [Subgroup.mem_centralizer_iff] at hc
    exact hc y (Set.mem_singleton y)
  · intro hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    apply hdp
    set c : Subgroup.centralizer ({y} : Set G) := ψ.symm p with hc
    have hcu : (c : G) * (u0 : G) = (u0 : G) * (c : G) := by
      rw [← hk]
      exact ((Commute.zpow_right (show Commute (c : G) y from (hcomm c).symm) k)).eq
    have hCu : c * u0 = u0 * c := Subtype.ext (by simpa using hcu)
    have hpd := congrArg ψ hCu
    simp only [map_mul, hu0, hc, MulEquiv.apply_symm_apply] at hpd
    exact hpd.symm

theorem listRow_of_centralizer_iso {G H : Type} [Group G] [Finite G] [Group H]
    (hcl : ∀ a b : G, orderOf a = 3 → orderOf b = 3 → ∃ k : G, k * a * k⁻¹ = b) {y : G}
    (hy : orderOf y = 3) (ψ : Subgroup.centralizer ({y} : Set G) ≃* H) (d p : H)
    (hd : d ^ 3 = 1) (hdp : d * p ≠ p * d) : ListRow G := by
  obtain ⟨u, hu3, hc, hn⟩ := exists_commute_notMem_zpowers_of_centralizer y ψ d p hd hdp
  exact listRow_of_single_class hcl hy hu3 hc hn

theorem exists_orderThree_ne_one (F : Type) [Field F] [Finite F] (h : 3 ∣ Nat.card F - 1) :
    ∃ ω : F, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : 3 ∣ Fintype.card Fˣ := by
    rw [Fintype.card_eq_nat_card, Nat.card_units]
    exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 3 hcard
  refine ⟨(x : F), ?_, ?_⟩
  · have hx3 : x ^ 3 = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one x
    rw [← Units.val_pow_eq_pow_val, hx3, Units.val_one]
  · intro h1
    have hx1 : x = 1 := Units.ext h1
    rw [hx1, orderOf_one] at hx
    norm_num at hx

theorem exists_su3_pair_noncommuting {F : Type} [Field F] [Finite F] [CharP F 2] {g : ℕ}
    (hF : Nat.card F = (2 ^ g) ^ 2) (hg : 2 ^ g % 3 = 2) {ω : F} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) :
    ∃ d p : CFSG.Open.StatedSU 3 (2 ^ g) F, d ^ 3 = 1 ∧ d * p ≠ p * d := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ g + 1 = 3 * t := ⟨(2 ^ g + 1) / 3, by omega⟩
  have hωq : ω ^ 2 ^ g * ω = 1 := by
    rw [← pow_succ, ht, pow_mul, hω3, one_pow]
  have hωi : (ω⁻¹) ^ 2 ^ g * ω⁻¹ = 1 := by
    rw [inv_pow, ← mul_inv, hωq, inv_one]
  have hωi' : (ω ^ 2 ^ g)⁻¹ * ω⁻¹ = 1 := by
    rw [← inv_pow]
    exact hωi
  set M : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![ω, ω⁻¹, 1] with hM
  have hdet : M.det = 1 := by
    rw [hM, Matrix.det_diagonal, Fin.prod_univ_three]
    simp [mul_inv_cancel₀ hω0]
  set d : GL (Fin 3) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero) with hd
  have hdM : (d : Matrix (Fin 3) (Fin 3) F) = M := rfl
  have hdmem : d ∈ CFSG.Open.StatedSU 3 (2 ^ g) F := by
    rw [mem_statedSU_iff hF d, hdM]
    refine ⟨hdet, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal, Matrix.one_apply,
        hωq, hωi, hωi']
  set P : GL (Fin 3) F := permGL (Equiv.swap (0 : Fin 3) 2) with hP
  have hPmem : P ∈ CFSG.Open.StatedSU 3 (2 ^ g) F := permGL_mem hF (Equiv.swap (0 : Fin 3) 2)
  refine ⟨⟨d, hdmem⟩, ⟨P, hPmem⟩, ?_, ?_⟩
  · apply Subtype.ext
    show d ^ 3 = 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hdM, Units.val_one, hM, Matrix.diagonal_pow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hω3]
  · intro h
    have h2 := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 0 2)
      (congrArg Subtype.val h)
    simp [hdM, hM, hP, coe_permGL, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal, Equiv.Perm.permMatrix, PEquiv.toMatrix] at h2
    exact hω1 h2


theorem three_dvd_two_pow_sub_one (a : ℕ) : 3 ∣ 2 ^ (2 * (2 * a + 1)) - 1 := by
  apply Nat.dvd_of_mod_eq_zero
  apply Nat.sub_mod_eq_zero_of_mod_eq
  rw [pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_odd_mod_three (a : ℕ) : 2 ^ (2 * a + 1) % 3 = 2 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

section ReeList


theorem listRow_reeGamma (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : ListRow ↥(ReeTag.F4.reeGamma K a) := by
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨y₀, hy₀, ⟨ψ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.exists_centralizer_mulEquiv_unitarySU a K hK
  have hFcard : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [GaloisField.card 2 (2 * (2 * a + 1)) (by omega), ← pow_mul, mul_comm]
  have h3 : 3 ∣ Nat.card (GaloisField 2 (2 * (2 * a + 1))) - 1 := by
    rw [GaloisField.card 2 (2 * (2 * a + 1)) (by omega)]
    exact three_dvd_two_pow_sub_one a
  obtain ⟨ω, hω3, hω1⟩ := exists_orderThree_ne_one _ h3
  obtain ⟨d, p, hd, hdp⟩ :=
    exists_su3_pair_noncommuting (g := 2 * a + 1) hFcard (two_pow_odd_mod_three a) hω3 hω1
  exact listRow_of_centralizer_iso
    (fun x z hx hz => CFSG.RankThree.PartTwo.Sec8.Item8KFacts3Ree.reeGamma_orderThree_conj a K hK
      x z hx hz) hy₀ ψ d p hd hdp

end ReeList

end CFSG.RankThree.PartTwo.Sec4.RonanK432
