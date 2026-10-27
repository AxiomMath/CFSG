module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CQA
import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis.FieldFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveFixed
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem uc22r3e5c_mem_pCoreOf_of_conj {L : Subgroup G} {b y : G}
    (hbL : b ∈ normalizer (L : Set G)) (hyL : y ∈ L)
    (hy : MulAut.conj (QuotientGroup.mk (⟨y, hyL⟩ : ↥L) : Bar2 L) =
      UC6S846.rhoL L ⟨b, hbL⟩) :
    ∀ x ∈ L, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  intro x hx
  let x' : ↥L := ⟨x, hx⟩
  have hmemL : b * (x' : G) * b⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hbL (x' : G)).mp x'.2
  have hlx : y * (x' : G) * y⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem hyL x'.2) (L.inv_mem hyL)
  have ha : Subgroup.normalizerMonoidHom L ⟨b, hbL⟩ x' =
      ⟨b * (x' : G) * b⁻¹, hmemL⟩ :=
    Subtype.ext (by rw [UC6S846.rhoL_mk_coe])
  have hb : (QuotientGroup.mk (⟨y, hyL⟩ : ↥L) : Bar2 L) *
      (QuotientGroup.mk x' : Bar2 L) *
      ((QuotientGroup.mk (⟨y, hyL⟩ : ↥L) : Bar2 L))⁻¹ =
      (QuotientGroup.mk (⟨y * (x' : G) * y⁻¹, hlx⟩ : ↥L) : Bar2 L) := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  have heq : (QuotientGroup.mk (⟨b * (x' : G) * b⁻¹, hmemL⟩ : ↥L) : Bar2 L) =
      QuotientGroup.mk (⟨y * (x' : G) * y⁻¹, hlx⟩ : ↥L) := by
    have h1 := DFunLike.congr_fun hy (QuotientGroup.mk x')
    rw [MulAut.conj_apply, UC6S846.rhoL_mk, hb, ha] at h1
    exact h1.symm
  have hdiv : ((⟨b * (x' : G) * b⁻¹, hmemL⟩ : ↥L) /
      (⟨y * (x' : G) * y⁻¹, hlx⟩ : ↥L)) ∈ CFSG.pCore 2 ↥L :=
    QuotientGroup.eq_iff_div_mem.mp heq
  have hcoe : ((((⟨b * (x' : G) * b⁻¹, hmemL⟩ : ↥L) /
      (⟨y * (x' : G) * y⁻¹, hlx⟩ : ↥L) : ↥L)) : G) =
      b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ := by
    rw [Subgroup.coe_div, div_eq_mul_inv]
  rw [← hcoe]
  exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := L) _).mpr hdiv

theorem uc22r3e5c_rhoL_not_inner {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    {b : G} (hbL : b ∈ normalizer (L : Set G))
    (hninn : ¬ ∃ y ∈ L, ∀ x ∈ L,
      b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) :
    UC6S846.rhoL L ⟨b, hbL⟩ ∉
      (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range := by
  intro h
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp h
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
  rw [← hl] at hy
  have hmem : ∀ x ∈ L, b * x * b⁻¹ * ((l : G) * x * (l : G)⁻¹)⁻¹ ∈
      CFSG.Open.pCoreOf 2 L :=
    uc22r3e5c_mem_pCoreOf_of_conj hbL l.2 (by simpa using hy)
  exact hninn ⟨(l : G), l.2, fun x hx =>
    CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hL.1 (hmem x hx)⟩

theorem uc22r3e5c_exists_sylow_rhoL_stable {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    {b : G} (hbL : b ∈ normalizer (L : Set G))
    (hbT : b ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G)) :
    ∃ U : Sylow 2 (Bar2 L), (U : Subgroup (Bar2 L)) = barImage L (D.T ⊓ L) ∧
      (U : Subgroup (Bar2 L)).map (UC6S846.rhoL L ⟨b, hbL⟩).toMonoidHom = U := by
  obtain ⟨U, hU⟩ := uc22r3e5c_exists_sylow_barImage hL
  refine ⟨U, hU, ?_⟩
  have hbTL : b ∈ normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
    uc22r3e5c_mem_normalizer_T_inf hbT hbL
  rw [hU, CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.rhoL_maps_barImage inf_le_right hbTL hbL]

theorem uc22r3e5c_conjClosure_eq_of_mem {M L K : Subgroup G} (hK : K ∈ conjSetOf M L) :
    conjClosure M K = conjClosure M L := by
  rw [conjClosure, conjClosure, uc22p2214_conjSetOf_eq hK]

private theorem uc22r3e5c_not_three_dvd_sq_add {m : ℕ} (hm : Odd m) :
    ¬ 3 ∣ (2 ^ m) ^ 2 + 2 ^ m + 1 := by
  by_contra h
  have hmod : 2 ^ m % 3 = 2 :=
    CFSG.RankThree.PartTwo.Sec8.Item82OneProof.two_pow_mod_three_of_odd hm
  have hsq : (2 ^ m) ^ 2 % 3 = 1 := by simp [Nat.pow_mod, hmod]
  have hN : ((2 ^ m) ^ 2 + 2 ^ m + 1) % 3 = 1 := by omega
  have h0 : ((2 ^ m) ^ 2 + 2 ^ m + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  omega

theorem uc22r3e5c_zmod_ne_of_sq_add {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) {y : ZMod r}
    (h : y ^ 2 + y + 1 = 0) : y ≠ y * y ∧ y ^ 2 ≠ y ^ 2 * y ^ 2 := by
  have : Fact r.Prime := ⟨hr⟩
  have hy3 : y ^ 3 = 1 := by
    rw [← sub_eq_zero]
    rw [show y ^ 3 - 1 = (y - 1) * (y ^ 2 + y + 1) by ring, h, mul_zero]
  have hy0 : y ≠ 0 := by
    intro hy
    simp [hy] at h
  have hy1 : y ≠ 1 := by
    intro hy
    have h3 : (3 : ZMod r) = 0 := by
      have h' := h
      rw [hy] at h'
      norm_num at h'
      exact h'
    have hdvd : r ∣ 3 := (ZMod.natCast_eq_zero_iff 3 r).mp h3
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp hdvd)
  constructor
  · intro h1
    apply hy1
    refine mul_left_cancel₀ hy0 ?_
    rw [mul_one]
    exact h1.symm
  · intro h1
    have hy20 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy0
    have h3 : y ^ 2 = 1 := by
      refine mul_left_cancel₀ hy20 ?_
      rw [mul_one]
      exact h1.symm
    apply hy1
    have h4 : y = 1 := by
      have h5 : y ^ 3 = y := by
        calc y ^ 3 = y ^ 2 * y := by ring
          _ = 1 * y := by rw [h3]
          _ = y := one_mul y
      rw [← h5, hy3]
    exact h4

private theorem uc22r3e5c_minFac_sq_add {n : ℕ} (hodd : Odd n) (h3 : 3 ∣ n) :
    ∃ (x r : ℕ), r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ∣ x ^ 2 + x + 1 ∧ x = 2 ^ (n / 3) := by
  let x := 2 ^ (n / 3)
  let N := x ^ 2 + x + 1
  have hm_odd : Odd (n / 3) := Odd.of_dvd_nat hodd (Nat.div_dvd_of_dvd h3)
  have h3n : 3 ≤ n := Nat.le_of_dvd (Odd.pos hodd) h3
  have hm1 : 1 ≤ n / 3 := Nat.div_pos h3n (by norm_num)
  have hx_even : Even x := by
    rw [show x = 2 ^ (n / 3) from rfl]
    exact Even.pow_of_ne_zero even_two (by omega)
  have hNodd : Odd N := by
    change Odd (x ^ 2 + x + 1)
    exact (Even.add (Even.pow_of_ne_zero hx_even (by norm_num)) hx_even).add_odd
      odd_one
  have hN : 1 < N := by
    have hx1 : 1 ≤ x := by
      rw [show x = 2 ^ (n / 3) from rfl]
      exact Nat.one_le_pow _ _ (by norm_num)
    have hx2 : 1 ≤ x ^ 2 := Nat.one_le_pow 2 x (by omega)
    change 1 < x ^ 2 + x + 1
    omega
  have hr : N.minFac.Prime := Nat.minFac_prime hN.ne'
  have hrdvdN : N.minFac ∣ N := Nat.minFac_dvd N
  have hr2 : N.minFac ≠ 2 := by
    intro h
    have h2N : 2 ∣ N := h ▸ hrdvdN
    obtain ⟨a, ha⟩ := hNodd
    obtain ⟨b, hb⟩ := h2N
    omega
  have hr3 : N.minFac ≠ 3 := by
    intro h
    exact uc22r3e5c_not_three_dvd_sq_add hm_odd (by
      simpa only [N, x] using (h ▸ hrdvdN : 3 ∣ N))
  exact ⟨x, N.minFac, hr, hr2, hr3, hrdvdN, rfl⟩

private theorem uc22r3e5c_dvd_two_pow_sub_one {n x r : ℕ} (h3 : 3 ∣ n)
    (hx : x = 2 ^ (n / 3)) (hr : r ∣ x ^ 2 + x + 1) : r ∣ 2 ^ n - 1 := by
  have hx1 : 1 ≤ x := by
    rw [hx]
    exact Nat.one_le_pow _ _ (by norm_num)
  have hx3 : x ^ 3 = 2 ^ n := by
    rw [hx, ← pow_mul, Nat.div_mul_cancel h3]
  have hcube : x ^ 2 + x + 1 ∣ x ^ 3 - 1 :=
    ⟨x - 1, (CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis.cube_sub_one_eq
      x hx1).trans (mul_comm _ _)⟩
  rw [← hx3]
  exact hr.trans hcube

theorem uc22r3e5c_exists_prime_pow_ne {n : ℕ} (hodd : Odd n) (h3 : 3 ∣ n) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ n - 1 ∧
      ∀ j ∈ ({1, 2} : Finset ℕ), (((2 ^ (n / 3)) ^ j : ℕ) : ZMod r) ≠
        (((2 ^ (n / 3)) ^ j * (2 ^ (n / 3)) ^ j : ℕ) : ZMod r) := by
  obtain ⟨x, r, hr, hr2, hr3, hrdvdN, hx⟩ := uc22r3e5c_minFac_sq_add hodd h3
  have hdvd : r ∣ 2 ^ n - 1 := uc22r3e5c_dvd_two_pow_sub_one h3 hx hrdvdN
  have hroot : ((x : ℕ) : ZMod r) ^ 2 + ((x : ℕ) : ZMod r) + 1 = 0 := by
    have h0 : ((x ^ 2 + x + 1 : ℕ) : ZMod r) = 0 :=
      (ZMod.natCast_eq_zero_iff _ r).mpr hrdvdN
    push_cast at h0
    exact h0
  refine ⟨r, hr, hr2, hdvd, ?_⟩
  intro j hj
  have hmain := uc22r3e5c_zmod_ne_of_sq_add hr hr3 hroot
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · simpa only [hx, pow_one, Nat.cast_mul] using hmain.1
  · simpa only [hx, Nat.cast_pow, Nat.cast_mul] using hmain.2

end CFSG.LocalAnalysis.UniquenessCase.UC22
