module

public import CFSG.RankThree.PartTwo.Sec16.Item1621StepsProofNoTwo
public import CFSG.RankThree.PartTwo.KFacts.K71SU3TwoFree
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar
import CFSG.RankThree.PartTwo.KFacts.AutPSUDet

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace ProofKS1623SU3

open Polynomial

theorem det_eq_of_pow_three_eq_smul {K : Type} [Field K] (M : Matrix (Fin 3) (Fin 3) K) (c : K)
    (hM : M ^ 3 = c • 1) (hroot : ∀ r : K, r ^ 3 ≠ c) : M.det = c := by
  set P : K[X] := X ^ 3 - C c with hP
  have hdeg : P.natDegree = 3 := by rw [hP]; compute_degree!
  have hmon : P.Monic := by rw [hP]; monicity!
  have hirr : Irreducible P := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) ?_
    intro x hx
    apply hroot x
    simpa [hP, sub_eq_zero] using hx
  have haev : aeval M P = 0 := by
    simp [hP, hM, Algebra.algebraMap_eq_smul_one]
  have hmin : P = minpoly K M := minpoly.eq_of_irreducible_of_monic hirr haev hmon
  have hdvd : P ∣ M.charpoly := hmin ▸ Matrix.minpoly_dvd_charpoly M
  have hchar : M.charpoly = P := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic M) hdvd ?_)
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hdeg]
  rw [Matrix.det_eq_sign_charpoly_coeff, hchar, hP]
  simp only [coeff_sub, coeff_X_pow, coeff_C_zero, Fintype.card_fin]
  norm_num

theorem not_nine_dvd {n : ℕ} (h3 : 2 ^ n % 3 = 2) (h9 : ¬ 2 ^ n % 9 = 8) :
    ¬ 9 ∣ 2 ^ (2 * n) - 1 := by
  have hpow : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [mul_comm, pow_mul]
  rw [hpow]
  generalize 2 ^ n = a at h3 h9
  have ha : a % 9 = 2 ∨ a % 9 = 5 := by omega
  have hsq : a ^ 2 % 9 = (a % 9) ^ 2 % 9 := Nat.pow_mod a 2 9
  have ha1 : 1 ≤ a ^ 2 := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0; norm_num at h3
    · exact Nat.one_le_pow _ _ h0
  rcases ha with ha | ha <;> rw [ha] at hsq <;> norm_num at hsq <;> omega

theorem pow_three_ne {n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * n))
    (h3 : 2 ^ n % 3 = 2) (h9 : ¬ 2 ^ n % 9 = 8) {c : K} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (r : K) : r ^ 3 ≠ c := by
  intro hr
  have := Fintype.ofFinite K
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hr
    rw [← hr, zero_pow (by norm_num)] at hc3
    exact zero_ne_one hc3
  have h9r : r ^ 9 = 1 := by
    rw [show 9 = 3 * 3 by rfl, pow_mul, hr, hc3]
  have hq : r ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one r hr0
  rw [← Nat.card_eq_fintype_card, hK] at hq
  have hg : r ^ Nat.gcd 9 (2 ^ (2 * n) - 1) = 1 := pow_gcd_eq_one.mpr ⟨h9r, hq⟩
  have hgd : Nat.gcd 9 (2 ^ (2 * n) - 1) ∣ 3 := by
    have hd : Nat.gcd 9 (2 ^ (2 * n) - 1) ∣ 9 := Nat.gcd_dvd_left _ _
    have hne : Nat.gcd 9 (2 ^ (2 * n) - 1) ≠ 9 := fun he =>
      not_nine_dvd h3 h9 (he ▸ Nat.gcd_dvd_right 9 (2 ^ (2 * n) - 1))
    have hdiv : Nat.gcd 9 (2 ^ (2 * n) - 1) ∈ Nat.divisors 9 := by
      rw [Nat.mem_divisors]; exact ⟨hd, by norm_num⟩
    have h9d : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [h9d] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    rcases hdiv with h1 | h1 | h1
    · rw [h1]; exact one_dvd 3
    · rw [h1]
    · exact absurd h1 hne
  obtain ⟨k, hk⟩ := hgd
  have h3r : r ^ 3 = 1 := by rw [hk, pow_mul, hg, one_pow]
  exact hc1 (hr ▸ h3r)


open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open Matrix

variable {n : ℕ} {K : Type} [Field K]

theorem unitaryProj_eq_one_iff (h : UnitaryFieldData 2 n K) (g : unitarySU 2 n K 3) :
    unitaryProj h 3 g = 1 ↔ g ∈ unitaryScalars h 3 := by
  rw [← MonoidHom.mem_ker, ker_unitaryProj]

theorem pow_three_eq_one_of_mem_unitaryScalars' {h : UnitaryFieldData 2 n K}
    {z : unitarySU 2 n K 3} (hz : z ∈ unitaryScalars h 3) : z ^ 3 = 1 := by
  obtain ⟨c, -, hc3, hzc⟩ := hz
  apply Subtype.ext
  rw [Subgroup.coe_pow, hzc, ← map_pow, hc3, map_one, Subgroup.coe_one]

theorem mem_unitaryScalars_of_coe_eq_smul (h : UnitaryFieldData 2 n K) {g : unitarySU 2 n K 3}
    {a : K} (hg : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = a • 1) :
    g ∈ unitaryScalars h 3 := by
  have ha : a ≠ 0 := by
    rintro rfl
    have hdet := congrArg Matrix.det hg
    rw [zero_smul, Matrix.det_zero] at hdet
    exact ((g : GL (Fin 3) K).isUnit.map Matrix.detMonoidHom).ne_zero hdet
  rw [unitaryScalars_eq h (by norm_num), Subgroup.mem_subgroupOf]
  refine ⟨Units.mk0 a ha, ?_⟩
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, hg, Units.val_mk0, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem pow_three_eq_one_of_mem_unitaryScalars (h : UnitaryFieldData 2 n K)
    (h3 : 2 ^ n % 3 = 2) (h9 : ¬ 2 ^ n % 9 = 8) {g : unitarySU 2 n K 3}
    (hg : g ^ 3 ∈ unitaryScalars h 3) : g ^ 3 = 1 := by
  have := h.finite
  obtain ⟨c, -, hc3, hgc⟩ := hg
  by_contra hne
  have hc1 : (c : K) ≠ 1 := by
    intro h1
    apply hne
    apply Subtype.ext
    rw [hgc]
    have : c = 1 := Units.ext h1
    rw [this, map_one, Subgroup.coe_one]
  have hc3' : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hdet : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    ((mem_unitarySU_iff h).mp g.2).1
  have hM : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = (c : K) • 1 := by
    have h1 := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hgc
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar] at h1
    rw [h1, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hd := det_eq_of_pow_three_eq_smul _ _ hM (pow_three_ne h.card h3 h9 hc3' hc1)
  exact hc1 (hd ▸ hdet)


theorem piField_of_unitaryFieldData (h : UnitaryFieldData 2 n K) : Sec4.PiField false 2 n K :=
  ⟨Nat.prime_two, h.one_le, by rw [h.card, Sec4.piCard, Bool.cond_false, ← pow_mul, mul_comm]⟩

theorem ne_smul_one_of_not_mem (h : UnitaryFieldData 2 n K) {v : unitarySU 2 n K 3}
    (hv : v ∉ unitaryScalars h 3) (c : K) :
    ((v : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 :=
  fun hc => hv (mem_unitaryScalars_of_coe_eq_smul h hc)

theorem sq_eq_one_of_mem_closure {M : Type*} [Group M] {s : Set M} (hcomm : s.Pairwise Commute)
    (hs : ∀ x ∈ s, x ^ 2 = 1) {g : M} (hg : g ∈ Subgroup.closure s) : g ^ 2 = 1 := by
  have hc := Subgroup.isMulCommutative_closure hcomm
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := by
      have := hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem eq_bot_of_normalizes_psu (h : UnitaryFieldData 2 n K) (h3 : 2 ^ n % 3 = 2)
    (h9 : ¬ 2 ^ n % 9 = 8) {x : unitaryPSU h 3} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {S : Subgroup (unitaryPSU h 3)} (hS2 : IsPGroup 2 S) (hxS : ∀ s ∈ S, x * s * x⁻¹ ∈ S) :
    S = ⊥ := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := piField_of_unitaryFieldData h
  by_contra hne
  have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hne
  have hZ := hS2.center_nontrivial
  have h2Z : IsPGroup 2 (Subgroup.center S) := hS2.to_subgroup _
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    rcases h2Z.card_eq_or_dvd with h1 | h1
    · exact absurd h1 (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne'
    · exact h1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  set s : unitaryPSU h 3 := ((z : S) : unitaryPSU h 3) with hsdef
  have hsS : s ∈ S := (z : S).2
  have hs2 : s ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hz] at h1
    have h2 := congrArg (fun y : Subgroup.center S => ((y : S) : unitaryPSU h 3)) h1
    simpa [hsdef] using h2
  have hs1 : s ≠ 1 := by
    intro h1
    have : z = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hz
    norm_num at hz
  have hscomm : ∀ s' ∈ S, s * s' = s' * s := fun s' hs' => by
    have := Subgroup.mem_center_iff.mp z.2 ⟨s', hs'⟩
    exact (congrArg Subtype.val this).symm
  obtain ⟨v, rfl⟩ := unitaryProj_surjective h 3 x
  have hv3 : v ^ 3 = 1 := pow_three_eq_one_of_mem_unitaryScalars h h3 h9
    (by rw [← unitaryProj_eq_one_iff, map_pow, hx3])
  have hvZ : v ∉ unitaryScalars h 3 := fun hv => hx1 ((unitaryProj_eq_one_iff h v).mpr hv)
  obtain ⟨A, hA⟩ := unitaryProj_surjective h 3 s
  set t : unitarySU 2 n K 3 := A ^ 3 with htdef
  have hA2 : A ^ 2 ∈ unitaryScalars h 3 := by
    rw [← unitaryProj_eq_one_iff, map_pow, hA, hs2]
  have ht2 : t ^ 2 = 1 := by
    rw [htdef, ← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul,
      pow_three_eq_one_of_mem_unitaryScalars' hA2]
  have hts : unitaryProj h 3 t = s := by
    rw [htdef, map_pow, hA, pow_succ, hs2, one_mul]
  have ht1 : t ≠ 1 := fun h1 => hs1 (by rw [← hts, h1, map_one])
  have htinv : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one, ← sq, ht2]
  set w : unitarySU 2 n K 3 := v * t * v⁻¹ with hwdef
  set u : unitarySU 2 n K 3 := v * w * v⁻¹ with hudef
  have hw2 : w ^ 2 = 1 := by
    rw [hwdef, sq, show v * t * v⁻¹ * (v * t * v⁻¹) = v * (t * t) * v⁻¹ by group, ← sq, ht2,
      mul_one, mul_inv_cancel]
  have hwinv : w⁻¹ = w := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hw2]
  have hws : unitaryProj h 3 w = unitaryProj h 3 v * s * (unitaryProj h 3 v)⁻¹ := by
    rw [hwdef, map_mul, map_mul, map_inv, hts]
  have htw : t * w = w * t := by
    have hk : t * w * t⁻¹ * w⁻¹ ∈ unitaryScalars h 3 := by
      rw [← unitaryProj_eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv, hts, hws,
        hscomm _ (hxS s hsS)]
      group
    set z0 := t * w * t⁻¹ * w⁻¹ with hz0
    have hz0c : ∀ y : unitarySU 2 n K 3, z0 * y = y * z0 := fun y =>
      (Subgroup.mem_center_iff.mp (unitaryScalars_le_center h 3 hk) y).symm
    have hz03 : z0 ^ 3 = 1 := pow_three_eq_one_of_mem_unitaryScalars' hk
    have h1 : t * w * t = z0 * w := by
      rw [hz0, htinv, hwinv]
      calc t * w * t = t * w * t * (w * w) := by rw [← sq, hw2, mul_one]
        _ = t * w * t * w * w := by group
    have hz02 : z0 ^ 2 = 1 := by
      have h2 : (t * w * t) * (t * w * t) = 1 := by
        calc (t * w * t) * (t * w * t) = t * w * (t * t) * w * t := by group
          _ = 1 := by rw [← sq, ht2, mul_one, mul_assoc t w w, ← sq, hw2, mul_one, ← sq, ht2]
      rw [h1] at h2
      calc z0 ^ 2 = z0 * z0 * (w * w) := by rw [← sq w, hw2, mul_one, sq]
        _ = z0 * (z0 * w) * w := by group
        _ = z0 * (w * z0) * w := by rw [hz0c w]
        _ = z0 * w * (z0 * w) := by group
        _ = 1 := h2
    have hz01 : z0 = 1 := by
      calc z0 = z0 ^ 3 * (z0 ^ 2)⁻¹ := by group
        _ = 1 := by rw [hz03, hz02, inv_one, one_mul]
    rw [hz0] at hz01
    calc t * w = t * w * t⁻¹ * w⁻¹ * (w * t) := by group
      _ = w * t := by rw [hz01, one_mul]
  have hv2 : v * v = v⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, mul_assoc, ← pow_three, hv3]
  have huv : u = v⁻¹ * t * v := by
    calc u = (v * v) * t * (v * v)⁻¹ := by rw [hudef, hwdef]; group
      _ = v⁻¹ * t * v := by rw [hv2, inv_inv]
  have hwu : w * u = u * w := by
    rw [hudef]
    calc w * (v * w * v⁻¹) = v * (t * w) * v⁻¹ := by rw [hwdef]; group
      _ = v * (w * t) * v⁻¹ := by rw [htw]
      _ = v * w * v⁻¹ * w := by rw [hwdef]; group
  have htu : t * u = u * t := by
    rw [huv]
    have h1 : v * (t * (v⁻¹ * t * v)) * v⁻¹ = w * t := by rw [hwdef]; group
    have h2 : v * (v⁻¹ * t * v * t) * v⁻¹ = t * w := by rw [hwdef]; group
    have h3 : v * (t * (v⁻¹ * t * v)) * v⁻¹ = v * (v⁻¹ * t * v * t) * v⁻¹ := by
      rw [h1, h2, htw]
    exact mul_left_cancel (mul_right_cancel h3)
  have hvu : v * u * v⁻¹ = t := by
    rw [huv]
    group
  have hu2 : u ^ 2 = 1 := by
    rw [hudef, sq, show v * w * v⁻¹ * (v * w * v⁻¹) = v * (w * w) * v⁻¹ by group, ← sq, hw2,
      mul_one, mul_inv_cancel]
  have hvt : v * t * v⁻¹ = w := hwdef.symm
  have hvw : v * w * v⁻¹ = u := hudef.symm
  clear_value u w t
  set gens : Set (GL (Fin 3) K) :=
    {(t : GL (Fin 3) K), (w : GL (Fin 3) K), (u : GL (Fin 3) K)} with hgens
  set X : Subgroup (GL (Fin 3) K) := Subgroup.closure gens with hXdef
  have hcoe : ∀ a b : unitarySU 2 n K 3, a * b = b * a →
      Commute (a : GL (Fin 3) K) (b : GL (Fin 3) K) := fun a b hab => by
    have := congrArg Subtype.val hab
    exact this
  have hcomm : gens.Pairwise Commute := by
    intro a ha b hb _
    simp only [hgens, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact Commute.refl _
    · exact hcoe _ _ htw
    · exact hcoe _ _ htu
    · exact (hcoe _ _ htw).symm
    · exact Commute.refl _
    · exact hcoe _ _ hwu
    · exact (hcoe _ _ htu).symm
    · exact (hcoe _ _ hwu).symm
    · exact Commute.refl _
  have hsq : ∀ a ∈ gens, a ^ 2 = 1 := by
    intro a ha
    simp only [hgens, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · rw [← Subgroup.coe_pow, ht2, Subgroup.coe_one]
    · rw [← Subgroup.coe_pow, hw2, Subgroup.coe_one]
    · rw [← Subgroup.coe_pow, hu2, Subgroup.coe_one]
  have hX2 : IsPGroup 2 X := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact sq_eq_one_of_mem_closure hcomm hsq g.2)⟩
  have hXu : X ≤ Sec4.glPi false 3 (2 ^ n) K := by
    rw [hXdef, Subgroup.closure_le]
    intro a ha
    simp only [hgens, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    have hmem : ∀ b : unitarySU 2 n K 3, (b : GL (Fin 3) K) ∈ Sec4.glPi false 3 (2 ^ n) K :=
      fun b => Sec4.slPi_le_glPi (π := false) (fun _ => h) b.2
    rcases ha with rfl | rfl | rfl
    · exact hmem t
    · exact hmem w
    · exact hmem u
  have hconj : ∀ a b : unitarySU 2 n K 3, v * a * v⁻¹ = b →
      (v : GL (Fin 3) K) * a * (v : GL (Fin 3) K)⁻¹ = b := fun a b hab => by
    rw [← hab]
    rfl
  have hXv : ∀ y ∈ X, (v : GL (Fin 3) K) * y * (v : GL (Fin 3) K)⁻¹ ∈ X := by
    intro y hy
    have hmap : X ≤ X.comap (MulAut.conj (v : GL (Fin 3) K)).toMonoidHom := by
      rw [hXdef, Subgroup.closure_le]
      intro a ha
      simp only [hgens, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rcases ha with rfl | rfl | rfl
      · rw [hconj _ _ hvt]
        exact Subgroup.subset_closure (by simp [hgens])
      · rw [hconj _ _ hvw]
        exact Subgroup.subset_closure (by simp [hgens])
      · rw [hconj _ _ hvu]
        exact Subgroup.subset_closure (by simp [hgens])
    exact hmap hy
  have hv3' : (v : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hv3, Subgroup.coe_one]
  have hXbot := KFacts.eq_bot_of_normalizes hK h3 v.2 hv3' (ne_smul_one_of_not_mem h hvZ)
    hXu hX2 hXv
  apply ht1
  have htX : (t : GL (Fin 3) K) ∈ X := Subgroup.subset_closure (by simp [hgens])
  rw [hXbot, Subgroup.mem_bot] at htX
  exact Subtype.ext htX


theorem coe_eq_smul_of_conj {g A B : GL (Fin 3) K} {s : K}
    (hs : ((g⁻¹ * B * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      s • ((g⁻¹ * A * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    (B : Matrix (Fin 3) (Fin 3) K) = s • (A : Matrix (Fin 3) (Fin 3) K) := by
  have hB : B = g * (g⁻¹ * B * g) * g⁻¹ := by group
  have hA : A = g * (g⁻¹ * A * g) * g⁻¹ := by group
  rw [hB, Units.val_mul, Units.val_mul, hs, Matrix.mul_smul, Matrix.smul_mul, ← Units.val_mul,
    ← Units.val_mul, ← hA]

theorem mul_inv_mem_of_coe_eq_smul (h : UnitaryFieldData 2 n K) {Y Z : unitarySU 2 n K 3}
    {s : K} (hs : ((Y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      s • ((Z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) : Y * Z⁻¹ ∈ unitaryScalars h 3 := by
  refine mem_unitaryScalars_of_coe_eq_smul h (a := s) ?_
  rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hs, Matrix.smul_mul, ← Units.val_mul,
    mul_inv_cancel, Units.val_one]

theorem exists_mem_unitaryScalars_of_commute (h : UnitaryFieldData 2 n K) (h3 : 2 ^ n % 3 = 2)
    {X Y : unitarySU 2 n K 3} (hX3 : X ^ 3 = 1) (hY3 : Y ^ 3 = 1)
    (hXZ : X ∉ unitaryScalars h 3) (hXY : X * Y = Y * X) :
    ∃ j : ℕ, Y * (X ^ j)⁻¹ ∈ unitaryScalars h 3 := by
  have := h.finite
  have hK := piField_of_unitaryFieldData h
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hX3' : (X : GL (Fin 3) K) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hX3, Subgroup.coe_one]
  obtain ⟨g, d, e, -, hXg, hde, hd⟩ :=
    KFacts.exists_unitary_diagonal hK h3 X.2 hX3' (ne_smul_one_of_not_mem h hXZ)
  set Xg : GL (Fin 3) K := X.1 with hXgdef
  set Yg : GL (Fin 3) K := Y.1 with hYgdef
  have hXY' : Xg * Yg = Yg * Xg := congrArg Subtype.val hXY
  have hD : ((g⁻¹ * Xg * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hXg, ← Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  set M : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ * Yg * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    with hMdef
  have hMD : M * diagonal d = diagonal d * M := by
    have hc : (g⁻¹ * Yg * g) * (g⁻¹ * Xg * g) = (g⁻¹ * Xg * g) * (g⁻¹ * Yg * g) := by
      calc (g⁻¹ * Yg * g) * (g⁻¹ * Xg * g) = g⁻¹ * (Yg * Xg) * g := by group
        _ = g⁻¹ * (Xg * Yg) * g := by rw [hXY']
        _ = (g⁻¹ * Xg * g) * (g⁻¹ * Yg * g) := by group
    have := congrArg (fun z : GL (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K)) hc
    simp only [Units.val_mul] at this
    rw [hMdef, ← hD]
    simpa only [Units.val_mul] using this
  have hdne : ∀ i j, i ≠ j → d i ≠ d j := by
    intro i j hij hdij
    have hc := hd i j hij
    have : (1 : K) = 0 := by
      linear_combination -hc + hde i + hde j + h2 + (e j - e i) * hdij
    exact one_ne_zero this
  have hMdiag : M = diagonal fun i => M i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij]
      have h1 := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A i j) hMD
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
      have h2' : M i j * (d j - d i) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h2' with h0 | h0
      · exact h0
      · exact absurd (sub_eq_zero.mp h0).symm (hdne i j hij)
  obtain ⟨y, hydef⟩ : ∃ y : Fin 3 → K, y = fun i => M i i := ⟨_, rfl⟩
  rw [← hydef] at hMdiag
  have hM3 : M ^ 3 = 1 := by
    have : (g⁻¹ * Yg * g) ^ 3 = 1 := by
      have hY3' : Yg ^ 3 = 1 := by rw [hYgdef, ← Subgroup.coe_pow, hY3, Subgroup.coe_one]
      calc (g⁻¹ * Yg * g) ^ 3 = (g⁻¹ * Yg * g) * (g⁻¹ * Yg * g) * (g⁻¹ * Yg * g) :=
            pow_three' _
        _ = g⁻¹ * Yg ^ 3 * g := by rw [pow_three']; group
        _ = 1 := by rw [hY3']; group
    rw [hMdef, ← Units.val_pow_eq_pow_val, this, Units.val_one]
  have hy3 : ∀ i, y i ^ 3 = 1 := by
    intro i
    have h1 := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A i i) hM3
    rw [hMdiag, diagonal_pow] at h1
    simpa using h1
  have hdetM : y 0 * y 1 * y 2 = 1 := by
    have h1 : M.det = 1 := by
      rw [hMdef, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
        ((mem_unitarySU_iff h).mp Y.2).1, mul_one, ← Matrix.det_mul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.det_one]
    rw [hMdiag, det_diagonal, Fin.prod_univ_three] at h1
    exact h1
  obtain ⟨ρ, hρ⟩ : ∃ ρ : K, ρ = d 1 * e 0 := ⟨_, rfl⟩
  have hd1 : d 1 = ρ * d 0 := by linear_combination -(d 1) * hde 0 - d 0 * hρ
  have hρ2 : ρ ^ 2 + ρ + 1 = 0 := by
    have h01 := hd 0 1 (by decide)
    have h1 : ρ * (d 0 * e 1) = 1 := by
      rw [hρ]; linear_combination (d 1 * e 1) * hde 0 + hde 1
    linear_combination ρ * h01 - h1 + ρ * h2 + ρ * hρ
  have hd2 : d 2 = ρ ^ 2 * d 0 := by
    obtain ⟨ρ', hρ'⟩ : ∃ ρ' : K, ρ' = d 2 * e 1 := ⟨_, rfl⟩
    have hd2' : d 2 = ρ' * d 1 := by linear_combination -(d 2) * hde 1 - d 1 * hρ'
    have hρ'2 : ρ' ^ 2 + ρ' + 1 = 0 := by
      have h12 := hd 1 2 (by decide)
      have h1 : ρ' * (d 1 * e 2) = 1 := by
        rw [hρ']; linear_combination (d 2 * e 2) * hde 1 + hde 2
      linear_combination ρ' * h12 - h1 + ρ' * h2 + ρ' * hρ'
    have he : d 2 * e 0 = ρ * ρ' := by linear_combination e 0 * hd2' - ρ' * hρ
    have hρρ' : (ρ * ρ') ^ 2 + ρ * ρ' + 1 = 0 := by
      have h02 := hd 0 2 (by decide)
      have h1 : (ρ * ρ') * (d 0 * e 2) = 1 := by
        linear_combination -(d 0 * e 2) * he + (d 2 * e 2) * hde 0 + hde 2
      linear_combination (ρ * ρ') * h02 - h1 + (ρ * ρ') * h2 - (ρ * ρ') * he
    have hρ'ρ : ρ' = ρ := by
      have hprod : (ρ' - ρ) * (ρ' + ρ + 1) = 0 := by linear_combination hρ'2 - hρ2
      rcases mul_eq_zero.mp hprod with h0 | h0
      · exact sub_eq_zero.mp h0
      · exfalso
        have : (1 : K) = 0 := by
          linear_combination hρρ' - (ρ * ρ' + 2) * (ρ * h0 - hρ2) - h2
        exact one_ne_zero this
    rw [hd2', hρ'ρ, hd1]
    ring
  have hy0 : y 0 ≠ 0 := by
    intro h0
    have := hy3 0
    rw [h0] at this
    norm_num at this
  obtain ⟨a, ha⟩ : ∃ a : K, a = y 1 * (y 0)⁻¹ := ⟨_, rfl⟩
  have hy1 : y 1 = a * y 0 := by rw [ha, mul_assoc, inv_mul_cancel₀ hy0, mul_one]
  have ha3 : a ^ 3 = 1 := by
    rw [ha, mul_pow, hy3 1, inv_pow, hy3 0, inv_one, one_mul]
  have hy2 : y 2 = a ^ 2 * y 0 := by
    have h1 : y 0 * (a * y 0) * y 2 = 1 := by rw [← hy1]; exact hdetM
    have h03 := hy3 0
    linear_combination (a ^ 2 * y 0) * h1 - y 2 * (a ^ 3 * h03 + ha3)
  have hacase : a = 1 ∨ a = ρ ∨ a = ρ ^ 2 := by
    have hprod : (a - 1) * ((a - ρ) * (a - ρ ^ 2)) = 0 := by
      linear_combination ha3 + (a - 1) * (ρ - 1 - a) * hρ2
    rcases mul_eq_zero.mp hprod with h0 | h0
    · exact Or.inl (sub_eq_zero.mp h0)
    · rcases mul_eq_zero.mp h0 with h0 | h0
      · exact Or.inr (Or.inl (sub_eq_zero.mp h0))
      · exact Or.inr (Or.inr (sub_eq_zero.mp h0))
  have hd0 : d 0 ≠ 0 := by
    intro h0
    have := hde 0
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  rcases hacase with ha1 | haρ | haρ2
  ·
    refine ⟨0, ?_⟩
    rw [pow_zero, inv_one, mul_one]
    refine mem_unitaryScalars_of_coe_eq_smul h (a := y 0) ?_
    have hM : M = y 0 • ((g⁻¹ * 1 * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [show g⁻¹ * 1 * g = 1 by group, Units.val_one, hMdiag, Matrix.smul_one_eq_diagonal]
      congr 1
      funext i
      fin_cases i
      · rfl
      · change y 1 = y 0
        rw [hy1, ha1, one_mul]
      · change y 2 = y 0
        rw [hy2, ha1, one_pow, one_mul]
    have := coe_eq_smul_of_conj (g := g) (A := 1) (B := Yg) hM
    rw [Units.val_one] at this
    exact this
  ·
    refine ⟨1, ?_⟩
    rw [pow_one]
    refine mul_inv_mem_of_coe_eq_smul h (s := y 0 * e 0) ?_
    refine coe_eq_smul_of_conj (g := g) ?_
    rw [← hMdef, hD, hMdiag, Matrix.smul_eq_diagonal_mul, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i
    · change y 0 = y 0 * e 0 * d 0
      rw [mul_assoc, mul_comm (e 0), hde 0, mul_one]
    · change y 1 = y 0 * e 0 * d 1
      rw [hy1, haρ, hd1]
      calc ρ * y 0 = ρ * y 0 * (d 0 * e 0) := by rw [hde 0, mul_one]
        _ = y 0 * e 0 * (ρ * d 0) := by ring
    · change y 2 = y 0 * e 0 * d 2
      rw [hy2, haρ, hd2]
      calc ρ ^ 2 * y 0 = ρ ^ 2 * y 0 * (d 0 * e 0) := by rw [hde 0, mul_one]
        _ = y 0 * e 0 * (ρ ^ 2 * d 0) := by ring
  ·
    refine ⟨2, ?_⟩
    refine mul_inv_mem_of_coe_eq_smul h (s := y 0 * e 0 ^ 2) ?_
    rw [Subgroup.coe_pow]
    refine coe_eq_smul_of_conj (g := g) ?_
    have hX2 : g⁻¹ * Xg ^ 2 * g = (g⁻¹ * Xg * g) ^ 2 := by
      rw [sq, sq]
      group
    rw [← hMdef, hX2, Units.val_pow_eq_pow_val, hD, diagonal_pow, hMdiag,
      Matrix.smul_eq_diagonal_mul, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i
    · change y 0 = y 0 * e 0 ^ 2 * d 0 ^ 2
      calc y 0 = y 0 * (d 0 * e 0) ^ 2 := by rw [hde 0, one_pow, mul_one]
        _ = y 0 * e 0 ^ 2 * d 0 ^ 2 := by ring
    · change y 1 = y 0 * e 0 ^ 2 * d 1 ^ 2
      rw [hy1, haρ2, hd1]
      calc ρ ^ 2 * y 0 = ρ ^ 2 * y 0 * (d 0 * e 0) ^ 2 := by rw [hde 0, one_pow, mul_one]
        _ = y 0 * e 0 ^ 2 * (ρ * d 0) ^ 2 := by ring
    · change y 2 = y 0 * e 0 ^ 2 * d 2 ^ 2
      rw [hy2, haρ2, hd2]
      calc (ρ ^ 2) ^ 2 * y 0 = ρ ^ 4 * y 0 * (d 0 * e 0) ^ 2 := by
            rw [hde 0, one_pow, mul_one]; ring
        _ = y 0 * e 0 ^ 2 * (ρ ^ 2 * d 0) ^ 2 := by ring


theorem pow_apply_eq_pow_two_pow {φ : K ≃+* K} (hφ : ∀ a, φ a = a ^ 2) (k : ℕ) (a : K) :
    (φ ^ k) a = a ^ 2 ^ k := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, RingAut.mul_apply, hφ, ih, ← pow_mul, pow_succ']

theorem even_of_two_pow_mod_three {k : ℕ} (hk : 2 ^ k % 3 = 1) : Even k := by
  rcases Nat.even_or_odd k with he | ⟨m, rfl⟩
  · exact he
  · exfalso
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod] at hk
    norm_num at hk

theorem pow_eq_one_of_apply_eq (hK : Nat.card K = 2 ^ (2 * n)) (hn : Odd n) {ω : K}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {σ : K ≃+* K} (hσ : σ ω = ω) : σ ^ n = 1 := by
  have hn1 : 1 ≤ 2 * n := by obtain ⟨k, rfl⟩ := hn; omega
  obtain ⟨φ, hφ, hord, hzp, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn1 hK
  have hfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; omega)
  have hmem : σ ∈ Subgroup.zpowers φ := hzp ▸ Subgroup.mem_top σ
  rw [← hfin.mem_powers_iff_mem_zpowers] at hmem
  obtain ⟨k, rfl⟩ := hmem
  rw [pow_apply_eq_pow_two_pow hφ] at hσ
  have hord3 : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hmod : 2 ^ k % 3 = 1 := by
    have h1 : ω ^ (2 ^ k % 3) = ω := by
      rw [← hord3, pow_mod_orderOf]
      exact hσ
    have hlt : 2 ^ k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : 2 ^ k % 3
    · rw [pow_zero] at h1
      exact absurd h1.symm hω1
    · rfl
    · exfalso
      apply hω1
      have h2 : ω * ω = ω * 1 := by rw [← sq, h1, mul_one]
      exact mul_left_cancel₀ hω0 h2
  obtain ⟨m, hm⟩ := even_of_two_pow_mod_three hmod
  rw [← pow_mul, hm, show (m + m) * n = 2 * n * m by ring, pow_mul, ← hord, pow_orderOf_eq_one,
    one_pow]

theorem scalar_mem_unitaryIsom3 (h : UnitaryFieldData 2 n K) {c : Kˣ}
    (hc : h.norm (c : K) = 1) : GeneralLinearGroup.scalar (Fin 3) c ∈ KFacts.unitaryIsom3 h :=
  CFSG.RankThree.PartTwo.KFacts.scalar_mem_unitaryIsom3_of_norm hc

theorem norm_det_eq_one (h : UnitaryFieldData 2 n K) (N : KFacts.unitaryIsom3 h) :
    h.norm ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
  CFSG.RankThree.PartTwo.KFacts.norm_det_of_mem_unitaryIsom3 N.2

theorem mem_range_conj_of_pow_two_pow_eq_one (h : UnitaryFieldData 2 n K)
    (N : KFacts.unitaryIsom3 h) {k : ℕ} (hk : KFacts.psuConj h N ^ 2 ^ k = 1) :
    ∃ u : unitaryPSU h 3, KFacts.psuConj h N = MulAut.conj u := by
  set δ : Kˣ := Matrix.GeneralLinearGroup.det (N : GL (Fin 3) K) with hδdef
  have hδ : h.norm (δ : K) = 1 := norm_det_eq_one h N
  have hscal := scalar_mem_unitaryIsom3 h hδ
  set M : GL (Fin 3) K := (GeneralLinearGroup.scalar (Fin 3) δ)⁻¹ * (N : GL (Fin 3) K) ^ 3
    with hMdef
  have hMU : M ∈ KFacts.unitaryIsom3 h := mul_mem (inv_mem hscal) (pow_mem N.2 3)
  have hMdet : (M : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 : (M : Matrix (Fin 3) (Fin 3) K).det = (Matrix.GeneralLinearGroup.det M : K) := rfl
    rw [h1, hMdef, map_mul, map_inv, map_pow]
    have h2 : Matrix.GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) δ) = δ ^ 3 := by
      apply Units.ext
      change ((GeneralLinearGroup.scalar (Fin 3) δ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).det = _
      rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal, Fin.prod_univ_three,
        Units.val_pow_eq_pow_val]
      ring
    rw [h2, ← hδdef, inv_mul_cancel, Units.val_one]
  have hMSU : M ∈ unitarySU 2 n K 3 := (mem_unitarySU_iff h).mpr ⟨hMdet, hMU⟩
  have hNM : (N : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) δ * M := by
    rw [hMdef, mul_inv_cancel_left]
  have hN3 : N ^ 3 = ⟨_, hscal⟩ * ⟨M, hMU⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_mul]
    exact hNM
  have h3 : KFacts.psuConj h N ^ 3 = MulAut.conj (unitaryProj h 3 ⟨M, hMSU⟩) := by
    rw [← map_pow, hN3, map_mul, KFacts.psuConj_scalar hscal, one_mul]
    exact (KFacts.conj_mk_eq_psuConj (h := h) ⟨M, hMSU⟩).symm
  have hcop : Nat.Coprime 3 (orderOf (KFacts.psuConj h N)) := by
    have hdvd : orderOf (KFacts.psuConj h N) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hj]
    exact Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  exact ⟨(unitaryProj h 3 ⟨M, hMSU⟩) ^ m, by rw [← hm, h3, map_pow]⟩


theorem mulAut_mul_conj_mul_inv {U : Type*} [Group U] (τ : MulAut U) (x : U) :
    τ * MulAut.conj x * τ⁻¹ = MulAut.conj (τ x) := by
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem glAut_scalar (σ : K ≃+* K) (c : Kˣ) :
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ
        (GeneralLinearGroup.scalar (Fin 3) c) =
      GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) c) := by
  apply Units.ext
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut, GeneralLinearGroup.coe_scalar,
    GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.scalar_apply,
    diagonal_map (map_zero σ), Units.coe_map]
  rfl

theorem commutator_mul_central {M : Type*} [Group M] {z1 z2 : M} (c1 : ∀ w, z1 * w = w * z1)
    (c2 : ∀ w, z2 * w = w * z2) (X Y : M) :
    z1 * X * (z2 * Y) * (z1 * X)⁻¹ * (z2 * Y)⁻¹ = X * Y * X⁻¹ * Y⁻¹ := by
  calc z1 * X * (z2 * Y) * (z1 * X)⁻¹ * (z2 * Y)⁻¹
      = z1 * X * (Y * z2) * (X⁻¹ * z1⁻¹) * (Y⁻¹ * z2⁻¹) := by
        rw [_root_.mul_inv_rev, _root_.mul_inv_rev, c2 Y]
    _ = z1 * (X * Y * (z2 * X⁻¹)) * z1⁻¹ * (Y⁻¹ * z2⁻¹) := by group
    _ = z1 * (X * Y * (X⁻¹ * z2)) * z1⁻¹ * (Y⁻¹ * z2⁻¹) := by rw [c2 X⁻¹]
    _ = (z1 * (X * Y * X⁻¹ * z2)) * z1⁻¹ * (Y⁻¹ * z2⁻¹) := by group
    _ = (X * Y * X⁻¹ * z2) * z1 * z1⁻¹ * (Y⁻¹ * z2⁻¹) := by rw [c1]
    _ = X * Y * X⁻¹ * (z2 * Y⁻¹) * z2⁻¹ := by group
    _ = X * Y * X⁻¹ * (Y⁻¹ * z2) * z2⁻¹ := by rw [c2 Y⁻¹]
    _ = X * Y * X⁻¹ * Y⁻¹ := by group

theorem odd_of_two_pow_mod_three {n : ℕ} (h3 : 2 ^ n % 3 = 2) : Odd n := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ho
  · exfalso
    rw [← two_mul, pow_mul, Nat.pow_mod] at h3
    norm_num at h3
  · exact ho

theorem eq_bot_of_normalized_psu (h : UnitaryFieldData 2 n K) (hn : 2 ≤ n)
    (h3 : 2 ^ n % 3 = 2) (h9 : ¬ 2 ^ n % 9 = 8) (E : Subgroup (unitaryPSU h 3))
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (T : Subgroup (MulAut (unitaryPSU h 3))) (hT : IsPGroup 2 T)
    (hET : ∀ e ∈ E, MulAut.conj e ∈ Subgroup.normalizer (T : Set (MulAut (unitaryPSU h 3)))) :
    T = ⊥ := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd n := odd_of_two_pow_mod_three h3
  have hq2 : 2 < 2 ^ n := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE3 : ∀ a ∈ E, a ^ 3 = 1 := hE.2
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
    rw [this, Subgroup.card_bot] at hE9
    norm_num at hE9
  have hxo : orderOf x = 3 := orderOf_eq_prime (hE3 x hxE) hx1
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxo]
  obtain ⟨y, hyE, hyx⟩ : ∃ y ∈ E, y ∉ Subgroup.zpowers x := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (H := E) (K := Subgroup.zpowers x) hcon
    rw [hE9, hcardx] at hle
    norm_num at hle
  have hsimple : IsSimpleGroup (unitaryPSU h 3) := by
    have hK2 : Nat.card K = (2 ^ n) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 n hK2 3 le_rfl
      (by intro he; simp only [Prod.mk.injEq, true_and] at he; omega)
    exact (unitaryPSUEquiv h (by norm_num)).isSimpleGroup
  have hZ : Subgroup.center (unitaryPSU h 3) = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (unitaryPSU h 3)) with hb | ht
    · exact hb
    · exfalso
      have hcen : ∀ g a : unitaryPSU h 3, g * a * g⁻¹ = a := fun g a => by
        have := Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top a) g
        rw [this, mul_inv_cancel_right]
      have hnorm : (Subgroup.zpowers x).Normal := ⟨fun a ha g => by rw [hcen]; exact ha⟩
      rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with hb | ht'
      · exact hx1 (Subgroup.zpowers_eq_bot.mp hb)
      · have hle := Subgroup.card_le_of_le (H := E) (K := Subgroup.zpowers x)
          (ht' ▸ le_top)
        rw [hE9, hcardx] at hle
        norm_num at hle
  have hconj1 : ∀ u : unitaryPSU h 3, MulAut.conj u = 1 → u = 1 := by
    intro u hu
    have : u ∈ Subgroup.center (unitaryPSU h 3) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut (unitaryPSU h 3) => φ g) hu
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * u = u * g * u⁻¹ * u := by rw [this]
        _ = u * g := by group
    rw [hZ, Subgroup.mem_bot] at this
    exact this
  have hinn : ∀ u : unitaryPSU h 3, MulAut.conj u ∈ T → u = 1 := by
    set S : Subgroup (unitaryPSU h 3) := T.comap MulAut.conj with hSdef
    have hS2 : IsPGroup 2 S := by
      intro ⟨u, hu⟩
      obtain ⟨k, hk⟩ := hT ⟨MulAut.conj u, hu⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : MulAut.conj u ^ 2 ^ k = 1 := congrArg Subtype.val hk
      rw [← map_pow] at h1
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hconj1 _ h1
    have hxS : ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
      intro s hs
      change MulAut.conj (x * s * x⁻¹) ∈ T
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hET x hxE) _).mp hs
    have hSb := eq_bot_of_normalizes_psu h h3 h9 (hE3 x hxE) hx1 hS2 hxS
    intro u hu
    have : u ∈ S := hu
    rw [hSb, Subgroup.mem_bot] at this
    exact this
  have hfix : ∀ τ ∈ T, ∀ e ∈ E, τ e = e := by
    intro τ hτ e he
    have h1 : MulAut.conj e * τ * (MulAut.conj e)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hET e he) τ).mp hτ
    have h2 : MulAut.conj e * τ * (MulAut.conj e)⁻¹ * τ⁻¹ ∈ T := mul_mem h1 (inv_mem hτ)
    have h3' : MulAut.conj e * τ * (MulAut.conj e)⁻¹ * τ⁻¹ = MulAut.conj (e * τ e⁻¹) := by
      rw [map_mul, ← mulAut_mul_conj_mul_inv, map_inv]
      group
    rw [h3'] at h2
    have h4 := hinn _ h2
    rw [map_inv, mul_inv_eq_one] at h4
    exact h4.symm
  rw [eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  obtain ⟨A, σ, hτA⟩ := KFacts.exists_psuConj_mul_psuField hq2 τ
  obtain ⟨X, rfl⟩ := unitaryProj_surjective h 3 x
  obtain ⟨Y, rfl⟩ := unitaryProj_surjective h 3 y
  have hX3 : X ^ 3 = 1 := pow_three_eq_one_of_mem_unitaryScalars h h3 h9
    (by rw [← unitaryProj_eq_one_iff, map_pow, hE3 _ hxE])
  have hY3 : Y ^ 3 = 1 := pow_three_eq_one_of_mem_unitaryScalars h h3 h9
    (by rw [← unitaryProj_eq_one_iff, map_pow, hE3 _ hyE])
  have hXZ : X ∉ unitaryScalars h 3 := fun hX => hx1 ((unitaryProj_eq_one_iff h X).mpr hX)
  set C : unitarySU 2 n K 3 := X * Y * X⁻¹ * Y⁻¹ with hCdef
  have hCZ : C ∈ unitaryScalars h 3 := by
    rw [← unitaryProj_eq_one_iff, hCdef, map_mul, map_mul, map_mul, map_inv, map_inv,
      hEc _ hxE _ hyE]
    group
  obtain ⟨ω, hωn, hω3, hCω⟩ := hCZ
  have hω1 : (ω : K) ≠ 1 := by
    intro h1
    have hC1 : C = 1 := by
      apply Subtype.ext
      rw [hCω, show ω = 1 from Units.ext h1, map_one, Subgroup.coe_one]
    have hXY : X * Y = Y * X := by
      calc X * Y = C * (Y * X) := by rw [hCdef]; group
        _ = Y * X := by rw [hC1, one_mul]
    obtain ⟨j, hj⟩ := exists_mem_unitaryScalars_of_commute h h3 hX3 hY3 hXZ hXY
    apply hyx
    have : unitaryProj h 3 Y = unitaryProj h 3 X ^ j := by
      have h1 := (unitaryProj_eq_one_iff h _).mpr hj
      rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at h1
      exact h1
    rw [this]
    exact Subgroup.npow_mem_zpowers _ j
  have hω3' : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hτX := hfix τ hτ _ hxE
  have hτY := hfix τ hτ _ hyE
  set X' : unitarySU 2 n K 3 := KFacts.suConj h A (KFacts.suField h σ X) with hX'def
  set Y' : unitarySU 2 n K 3 := KFacts.suConj h A (KFacts.suField h σ Y) with hY'def
  have hτX' : unitaryProj h 3 X' = unitaryProj h 3 X := by
    rw [← hτX, hτA]
    rfl
  have hτY' : unitaryProj h 3 Y' = unitaryProj h 3 Y := by
    rw [← hτY, hτA]
    rfl
  have hzX : X' * X⁻¹ ∈ unitaryScalars h 3 := by
    rw [← unitaryProj_eq_one_iff, map_mul, map_inv, hτX', mul_inv_cancel]
  have hzY : Y' * Y⁻¹ ∈ unitaryScalars h 3 := by
    rw [← unitaryProj_eq_one_iff, map_mul, map_inv, hτY', mul_inv_cancel]
  have hcen : ∀ {z : unitarySU 2 n K 3}, z ∈ unitaryScalars h 3 →
      ∀ w : unitarySU 2 n K 3, z * w = w * z := fun hz w =>
    (Subgroup.mem_center_iff.mp (unitaryScalars_le_center h 3 hz) w).symm
  have hcomm' : X' * Y' * X'⁻¹ * Y'⁻¹ = C := by
    have hX'e : X' = (X' * X⁻¹) * X := by group
    have hY'e : Y' = (Y' * Y⁻¹) * Y := by group
    rw [hX'e, hY'e, commutator_mul_central (hcen hzX) (hcen hzY)]
  have hσω : σ (ω : K) = ω := by
    have h1 : X' * Y' * X'⁻¹ * Y'⁻¹ = KFacts.suConj h A (KFacts.suField h σ C) := by
      rw [hCdef, hX'def, hY'def]
      simp only [map_mul, map_inv]
    rw [hcomm'] at h1
    have h2 := congrArg (fun z : unitarySU 2 n K 3 => (z : GL (Fin 3) K)) h1
    simp only [KFacts.coe_suConj, KFacts.coe_suField] at h2
    rw [hCω, glAut_scalar, (commute_scalar _ _).eq, Subgroup.coe_inv, mul_inv_cancel_right] at h2
    have h3' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h2
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq,
      Units.coe_map] at h3'
    exact h3'.symm
  have hσn : σ ^ n = 1 := pow_eq_one_of_apply_eq h.card hodd hω3' hω1 hσω
  have hpow : ∀ m : ℕ, ∃ B : KFacts.unitaryIsom3 h,
      τ ^ m = KFacts.psuConj h B * KFacts.psuField h (σ ^ m) := by
    intro m
    induction m with
    | zero => exact ⟨1, by rw [pow_zero, pow_zero, map_one, map_one, one_mul]⟩
    | succ m ih =>
      obtain ⟨B, hB⟩ := ih
      exact ⟨_, by rw [pow_succ, hB, hτA, KFacts.psuConj_mul_psuField_mul, ← pow_succ]⟩
  obtain ⟨B, hB⟩ := hpow n
  rw [hσn, map_one, mul_one] at hB
  obtain ⟨k, hk⟩ := hT ⟨τ ^ n, pow_mem hτ n⟩
  have hk' : KFacts.psuConj h B ^ 2 ^ k = 1 := by
    rw [← hB]
    exact congrArg Subtype.val hk
  obtain ⟨u, hu⟩ := mem_range_conj_of_pow_two_pow_eq_one h B hk'
  have hτn : τ ^ n = 1 := by
    have hu1 := hinn u (by rw [← hu, ← hB]; exact pow_mem hτ n)
    rw [hB, hu, hu1, map_one]
  obtain ⟨k', hk''⟩ := hT ⟨τ, hτ⟩
  have hτk : τ ^ 2 ^ k' = 1 := congrArg Subtype.val hk''
  have hg : τ ^ Nat.gcd (2 ^ k') n = 1 := pow_gcd_eq_one.mpr ⟨hτk, hτn⟩
  have hcop : Nat.gcd (2 ^ k') n = 1 := Nat.Coprime.pow_left k' (Nat.coprime_two_left.mpr hodd)
  rw [hcop, pow_one] at hg
  exact hg

end ProofKS1623SU3

open CFSG.Assembly.RankThreeEven (projSU)

theorem ks1623SU3Aut : KS1623SU3Aut := by
  intro n hn h3 h9 E hE hE9 T hT hET
  have h := Sec4.unitaryFieldData_galoisField 2 n (by omega)
  set φ := Sec4.projSUEquivUnitaryPSU 2 n h with hφ
  set E' := E.map φ.toMonoidHom with hE'def
  set T' := T.map (MulAut.congr φ).toMonoidHom with hT'def
  have hE' : CFSG.Assembly.IsElemAbelian 3 E' := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩⟩ ⟨_, ⟨b, hb, rfl⟩⟩
      apply Subtype.ext
      change φ a * φ b = φ b * φ a
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · rintro _ ⟨a, ha, rfl⟩
      change (φ a) ^ 3 = 1
      rw [← map_pow, hE.2 a ha, map_one]
  have hE'9 : Nat.card E' = 9 := by
    rw [hE'def, Subgroup.card_map_of_injective φ.injective, hE9]
  have hT' : IsPGroup 2 T' := hT.map _
  have hET' : ∀ e ∈ E', MulAut.conj e ∈ Subgroup.normalizer
      (T' : Set (MulAut (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU h 3))) := by
    rintro _ ⟨a, ha, rfl⟩
    have hc : MulAut.conj (φ.toMonoidHom a) = (MulAut.congr φ).toMonoidHom (MulAut.conj a) := by
      ext u
      obtain ⟨v, rfl⟩ := φ.surjective u
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.congr_apply,
        MulEquiv.trans_apply, MulEquiv.symm_apply_apply, map_mul, map_inv]
    rw [hc]
    exact Subgroup.le_normalizer_map _ ⟨_, hET a ha, rfl⟩
  have hbot := ProofKS1623SU3.eq_bot_of_normalized_psu h hn h3 h9 E' hE' hE'9 T' hT' hET'
  exact (Subgroup.map_eq_bot_iff_of_injective T (MulAut.congr φ).injective).mp hbot

end CFSG.RankThree.PartTwo.Sec16
