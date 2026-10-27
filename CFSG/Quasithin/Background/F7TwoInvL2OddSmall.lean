module

public import CFSG.Quasithin.Background.F7TwoInvL2OddSmallSeven
public import CFSG.Quasithin.Background.F7TwoInvL2OddSmallNine
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.F7Two

open CFSG.GorensteinWalter CFSG.PSL2Table
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem card_add_one_dvd_card_of_fix_le [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) {ν : K} (hν : ¬ IsSquare ν) {M : Subgroup (PSL2 K)}
    (hM : fixSubgroup (pgl2InnerAutPSL2 K hK hcard (N0 ν (ne_zero_of_not_isSquare hν))) ≤ M) :
    Nat.card K + 1 ∣ Nat.card M := by
  let : Fintype K := Fintype.ofFinite K
  have hF := ringChar_ne_two_of_isOddPrimePower hK
  have hq5 : 5 ≤ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card]
    exact five_le_of_odd_of_three_lt (odd_of_isOddPrimePower hK) hcard
  have h1 := card_normalizer_nonsplitTorus hF hq5 hν
  have h2 := card_nonsplitTorus hF hν
  have hNM := Subgroup.card_dvd_of_le ((normalizer_nonsplitTorus_le_fix_N0 hK hcard hν).trans hM)
  rw [h1] at hNM
  have h3 : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  rwa [show 2 * Nat.card (nonsplitTorus ν) = Nat.card K + 1 by omega] at hNM

theorem natCard_eq_of_mulEquiv_semidirect {H E C : Type*} [Group H] [Group E] [Group C]
    {φ : C →* MulAut E} (e : H ≃* E ⋊[φ] C) : Nat.card H = Nat.card E * Nat.card C := by
  rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]

theorem natCard_eq_of_isCoatom_seven {K : Type} [Field K] [Finite K]
    (h7 : Nat.card K = 7) {M : Subgroup (PSL2 K)} (hM : IsCoatom M) (h8 : 8 ∣ Nat.card M) :
    Nat.card M = 24 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hF : Nat.card K = 7 ^ 1 := by simpa using h7
  rcases CFSG.Glauberman.Dickson.MaxNode.isCoatom_isomorphism_types (F := K) (p := 7) (f := 1)
      hF (by norm_num) (by norm_num) hM with h | h | h | h | h | h | h | h
  · obtain ⟨E, C, -, -, hE, -, hC, -, -, -, φ, -, ⟨e⟩⟩ := h
    have h' : Nat.card M = Nat.card E * Nat.card C := natCard_eq_of_mulEquiv_semidirect e
    rw [hE, hC] at h'
    norm_num at h'
    omega
  · exact absurd h.1 (by norm_num)
  · exact absurd (by norm_num) h.1
  · obtain ⟨m, hm, -⟩ := h
    omega
  · obtain ⟨m, r, hr, -, hmr, -⟩ := h
    exact absurd (Nat.eq_one_of_mul_eq_one_left hmr.symm) hr.ne_one
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · obtain ⟨-, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv, Nat.card_perm]
    simp [Nat.factorial]

theorem nonempty_mulEquiv_alternatingGroup_of_isCoatom_nine
    {K : Type} [Field K] [Finite K] (h9 : Nat.card K = 9) {M : Subgroup (PSL2 K)}
    (hM : IsCoatom M) (h10 : 10 ∣ Nat.card M) : Nonempty (M ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hF : Nat.card K = 3 ^ 2 := by simpa using h9
  rcases CFSG.Glauberman.Dickson.MaxNode.isCoatom_isomorphism_types (F := K) (p := 3) (f := 2)
      hF (by norm_num) (by norm_num) hM with h | h | h | h | h | h | h | h
  · obtain ⟨E, C, -, -, hE, -, hC, -, -, -, φ, -, ⟨e⟩⟩ := h
    have h' : Nat.card M = Nat.card E * Nat.card C := natCard_eq_of_mulEquiv_semidirect e
    rw [hE, hC] at h'
    norm_num at h'
    omega
  · exact absurd h.1 (by norm_num)
  · exact absurd (by norm_num) h.2.1
  · obtain ⟨m, hm, ⟨e⟩⟩ := h
    have hm1 : m = 1 := by omega
    subst hm1
    have h24 : Nat.card M = 24 := by
      rw [Nat.card_congr e.toEquiv, pgl2_card_formula, GaloisField.card 3 1 one_ne_zero]
      norm_num
    omega
  · obtain ⟨m, r, hr, hr2, hmr, -⟩ := h
    exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (Dvd.intro_left m hmr.symm)) hr2
  · exact h.2
  · exact absurd h.1.1 (by norm_num)
  · exact absurd h.1.1 (by norm_num)

theorem alternatingGroup_five_pow_four :
    ∀ z : alternatingGroup (Fin 5), z ^ 4 = 1 → z ^ 2 = 1 := by
  decide +kernel

theorem invAutGen_pgl2_nonsplit_nine {K : Type} [Field K]
    [Finite K] (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (h9 : Nat.card K = 9) {ν : K} (hν : ¬ IsSquare ν) :
    InvAutGen (PSL2 K) (pgl2InnerAutPSL2 K hK hcard (N0 ν (ne_zero_of_not_isSquare hν))) := by
  refine invAutGen_of_forall_coatom
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)) psl2_nonabelian
    (pgl2InnerAutPSL2_N0_mul_self hK hcard _ _) (pgl2InnerAutPSL2_N0_ne_one hK hcard _ _)
    fun M hM hle => ?_
  have h10 : 10 ∣ Nat.card M := by
    have := card_add_one_dvd_card_of_fix_le hK hcard hν hle
    rwa [h9] at this
  obtain ⟨e⟩ := nonempty_mulEquiv_alternatingGroup_of_isCoatom_nine h9 hM h10
  obtain ⟨y, hy, hy4, hy2⟩ := exists_mem_invXiAut_order_four_nine hK hcard h9 hν
  refine ⟨y, hy, fun hyM => ?_⟩
  have h4 : (e ⟨y, hyM⟩) ^ 4 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyM⟩ : M) ^ 4 = 1 := Subtype.ext (by simpa using hy4)
    rw [this, map_one]
  have h2 := alternatingGroup_five_pow_four _ h4
  rw [← map_pow] at h2
  have : (⟨y, hyM⟩ : M) ^ 2 = 1 := e.injective (h2.trans (map_one e).symm)
  exact hy2 (by simpa using congrArg Subtype.val this)

theorem invAutGen_pgl2_nonsplit_seven {K : Type} [Field K]
    [Finite K] (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (h7 : Nat.card K = 7) {ν : K} (hν : ¬ IsSquare ν) :
    InvAutGen (PSL2 K) (pgl2InnerAutPSL2 K hK hcard (N0 ν (ne_zero_of_not_isSquare hν))) := by
  refine invAutGen_of_forall_coatom
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)) psl2_nonabelian
    (pgl2InnerAutPSL2_N0_mul_self hK hcard _ _) (pgl2InnerAutPSL2_N0_ne_one hK hcard _ _)
    fun M hM hle => ?_
  have h8 : 8 ∣ Nat.card M := by
    have := card_add_one_dvd_card_of_fix_le hK hcard hν hle
    rwa [h7] at this
  have h24 := natCard_eq_of_isCoatom_seven h7 hM h8
  obtain ⟨y, hy, hord⟩ := exists_mem_invXiAut_orderOf_seven hK hcard h7 hν
  refine ⟨y, hy, fun hyM => ?_⟩
  have := Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).2 hyM)
  rw [Nat.card_zpowers, hord, h24] at this
  omega

end CFSG.Quasithin.F7Two
