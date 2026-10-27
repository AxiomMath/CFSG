module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutModel
import all CFSG.Fischer.F4

public section

namespace CFSG.GGQ2Prime

open CFSG.Fischer
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (autT)

private theorem hermStd_single_single (i j : Fin 6) :
    hermStd (Pi.single i 1) (Pi.single j 1) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [hermStd, Fin.sum_univ_six, Pi.single_apply]

private theorem hermStd_basis_pair {i j : Fin 6} (hij : i ≠ j) (a : F4) :
    hermStd (Pi.single i 1 + a • Pi.single j 1) (Pi.single i 1 + a • Pi.single j 1) =
      1 + a ^ 3 := by
  simp [hermStd_add_left, hermStd_add_right, hermStd_smul_left, hermStd_smul_right,
    hermStd_single_single, hij, Ne.symm hij] <;> ring

private theorem one_add_one_F4 : (1 : F4) + 1 = 0 := by decide

private theorem basis_pair_ne_zero {i j : Fin 6} (hij : i ≠ j) (a : F4) :
    Pi.single i 1 + a • Pi.single j 1 ≠ (0 : Fin 6 → F4) := fun h => by
  simpa [Pi.single_apply, hij] using congrFun h i

private theorem pair_coord {M : Matrix (Fin 6) (Fin 6) F4} {c a : F4} {i j k : Fin 6}
    (h : M.mulVec (Pi.single i 1 + a • Pi.single j 1) =
      c • (Pi.single i 1 + a • Pi.single j 1)) :
    M k i + a * M k j =
      c * ((Pi.single i 1 : Fin 6 → F4) k + a * (Pi.single j 1 : Fin 6 → F4) k) := by
  simpa [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one] using congrFun h k

private abbrev gU0Mat (g : GU0) : Matrix (Fin 6) (Fin 6) F4 := Units.val g.1

private theorem mulVec_eq_smul_of_fix (g : GU0)
    (hfix : ∀ p : Fin 693, g • p = p) {w : W} (hw : w ≠ 0) (hiso : hermStd w w = 0) :
    ∃ c : F4, c ≠ 0 ∧ (gU0Mat g).mulVec w = c • w := by
  have hfixi : ptIdx ((gU0Mat g).mulVec (uVec (ptIdx w))) = ptIdx w := by
    obtain ⟨p, hp⟩ : ∃ p : Fin 693, p.val = ptIdx w :=
      ⟨⟨ptIdx w, ptIdx_lt ptsFacts hw hiso⟩, by simp⟩
    have h := congrArg Fin.val (hfix p)
    rw [smul_val, hp] at h
    exact h
  rw [uVec_ptIdx ptsFacts hw hiso] at hfixi
  have hv0 : (gU0Mat g).mulVec w ≠ 0 := mulVec_ne_zero _ hw
  have hvis : hermStd ((gU0Mat g).mulVec w) ((gU0Mat g).mulVec w) = 0 :=
    (hermStd_mulVec g w w).trans hiso
  have hpt : ptIdx ((gU0Mat g).mulVec w) = ptIdx w :=
    (ptIdx_mulVec_normV _ hw).symm.trans hfixi
  have hsame : normV w = normV ((gU0Mat g).mulVec w) := by
    have h2 := uVec_ptIdx ptsFacts hv0 hvis
    rw [hpt] at h2
    exact (uVec_ptIdx ptsFacts hw hiso).symm.trans h2
  obtain ⟨c0, hc0, hn0⟩ := normV_eq_smul hw
  obtain ⟨c1, hc1, hn1⟩ := normV_eq_smul hv0
  have hv_eq : c1 • (gU0Mat g).mulVec w = c0 • w := by
    rw [← hn1, ← hn0]
    exact hsame.symm
  refine ⟨c1⁻¹ * c0, mul_ne_zero (inv_ne_zero hc1) hc0, ?_⟩
  calc (gU0Mat g).mulVec w = c1⁻¹ • (c1 • (gU0Mat g).mulVec w) := by
        rw [smul_smul, inv_mul_cancel₀ hc1, one_smul]
    _ = c1⁻¹ • (c0 • w) := by rw [hv_eq]
    _ = (c1⁻¹ * c0) • w := by rw [smul_smul]

private theorem matrix_eq_smul_one_of_pairs (M : Matrix (Fin 6) (Fin 6) F4)
    (H1 : ∀ i j : Fin 6, i ≠ j → ∃ c : F4, c ≠ 0 ∧
      M.mulVec (Pi.single i 1 + (1 : F4) • Pi.single j 1) =
        c • (Pi.single i 1 + (1 : F4) • Pi.single j 1))
    (H2 : ∀ i j : Fin 6, i ≠ j → ∃ c : F4, c ≠ 0 ∧
      M.mulVec (Pi.single i 1 + F4.ω • Pi.single j 1) =
        c • (Pi.single i 1 + F4.ω • Pi.single j 1)) :
    ∃ d : F4, d ≠ 0 ∧ M = d • 1 := by
  have hex : ∀ j k : Fin 6, k ≠ j → ∃ i : Fin 6, i ≠ j ∧ i ≠ k := by decide
  have hoff : ∀ j k : Fin 6, k ≠ j → M k j = 0 := by
    intro j k hkj
    obtain ⟨i, hij, hik⟩ := hex j k hkj
    obtain ⟨_, -, h1⟩ := H1 i j hij
    obtain ⟨_, -, h2⟩ := H2 i j hij
    have e1 := pair_coord h1 (k := k)
    have e2 := pair_coord h2 (k := k)
    simp [Pi.single_apply, Ne.symm hik, hkj] at e1 e2
    have hm : (F4.ω + 1) * M k j = 0 := by
      linear_combination e2 - e1 + (M k j) * F4.two_eq_zero
    exact (mul_eq_zero.1 hm).resolve_left (by decide)
  have hdiag : ∀ j : Fin 6, j ≠ 0 → ∃ c : F4, c ≠ 0 ∧ M 0 0 = c ∧ M j j = c := by
    intro j hj
    obtain ⟨c, hc, h⟩ := H1 0 j (Ne.symm hj)
    have e0 := pair_coord h (k := 0)
    have ej := pair_coord h (k := j)
    simp [Pi.single_apply, hj, Ne.symm hj, hoff j 0 (Ne.symm hj), hoff 0 j hj] at e0 ej
    exact ⟨c, hc, by linear_combination e0, by linear_combination ej⟩
  obtain ⟨c, hc, h0, -⟩ := hdiag 1 (by decide)
  refine ⟨M 0 0, by rw [h0]; exact hc, ?_⟩
  ext k l
  by_cases hkl : k = l
  · subst hkl
    by_cases hk : k = 0
    · subst hk
      simp
    · obtain ⟨_, -, h0', hkk⟩ := hdiag k hk
      rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, hkk, h0']
  · rw [Matrix.smul_apply, Matrix.one_apply_ne hkl, smul_eq_mul, mul_zero]
    exact hoff l k hkl

private theorem piGU_ker_matrix (g : GU0) (hg : piGU g = 1) :
    ∃ d : F4, d ≠ 0 ∧ gU0Mat g = d • 1 := by
  have hfix : ∀ p : Fin 693, g • p = p := fun p => by
    simpa only [piGU, MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply]
      using congrArg (fun σ : Equiv.Perm (Fin 693) => σ p) hg
  refine matrix_eq_smul_one_of_pairs _ (fun i j hij => ?_) (fun i j hij => ?_)
  · exact mulVec_eq_smul_of_fix g hfix (basis_pair_ne_zero hij 1)
      (by rw [hermStd_basis_pair hij 1, one_pow, one_add_one_F4])
  · exact mulVec_eq_smul_of_fix g hfix (basis_pair_ne_zero hij F4.ω)
      (by rw [hermStd_basis_pair hij F4.ω, (by decide : F4.ω ^ 3 = 1), one_add_one_F4])

private theorem card_piGU_ker_le : Nat.card piGU.ker ≤ 3 := by
  have hscal : ∀ g : GU0, piGU g = 1 → gU0Mat g = (gU0Mat g) 0 0 • 1 := by
    intro g hg
    obtain ⟨d, -, hM⟩ := piGU_ker_matrix g hg
    rw [show (gU0Mat g) 0 0 = d by simp [hM]]
    exact hM
  have hne : ∀ g : GU0, piGU g = 1 → (gU0Mat g) 0 0 ≠ 0 := by
    intro g hg
    obtain ⟨d, hd, hM⟩ := piGU_ker_matrix g hg
    rw [hM]
    simpa using hd
  let f : piGU.ker → {x : F4 // x ≠ 0} := fun g =>
    ⟨(gU0Mat g.1) 0 0, hne g.1 (MonoidHom.mem_ker.1 g.2)⟩
  have hinj : Function.Injective f := by
    intro g h hgh
    have h1 : (gU0Mat g.1) 0 0 = (gU0Mat h.1) 0 0 := congrArg Subtype.val hgh
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    show gU0Mat g.1 = gU0Mat h.1
    rw [hscal g.1 (MonoidHom.mem_ker.1 g.2), hscal h.1 (MonoidHom.mem_ker.1 h.2), h1]
  have hcard : Nat.card {x : F4 // x ≠ 0} = 3 := by rw [Nat.card_eq_fintype_card]; decide
  exact (Nat.card_le_card_of_injective f hinj).trans hcard.le

private theorem rhoTOrderThree_conj_mem_SU0 (w : GU0)
    {s : Matrix.GeneralLinearGroup (Fin 6) F4} (hs : s ∈ SU0) :
    w.1 * s * w.1⁻¹ ∈ SU0 := by
  have hsG : s ∈ GU0 := SU0_le_GU0 hs
  have hk : (⟨s, hsG⟩ : GU0) ∈ detGU.ker := by
    rw [ker_detGU]
    exact Subgroup.mem_subgroupOf.2 hs
  have hc : w * (⟨s, hsG⟩ : GU0) * w⁻¹ ∈ detGU.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, MonoidHom.mem_ker.1 hk, mul_one,
      mul_inv_cancel]
  rw [ker_detGU, Subgroup.mem_subgroupOf] at hc
  exact hc

private theorem rhoTOrderThree_piGU_conj_mem
    (w : GU0) {t : Equiv.Perm (Fin 693)} (ht : t ∈ T46) :
    piGU w * t * (piGU w)⁻¹ ∈ T46 := by
  rw [← range_piSU] at ht ⊢
  obtain ⟨s, rfl⟩ := ht
  have hmem := rhoTOrderThree_conj_mem_SU0 w s.2
  refine ⟨⟨_, hmem⟩, ?_⟩
  simp only [piSU, MonoidHom.comp_apply, ← map_inv, ← map_mul]
  rfl

theorem piGU_mem_autT
    (w : GU0) : piGU w ∈ autT := by
  unfold autT
  refine Subgroup.mem_normalizer_iff.2 fun t => ⟨fun ht => ?_, fun ht => ?_⟩
  · exact rhoTOrderThree_piGU_conj_mem w (show t ∈ T46 from ht)
  · have h2 := rhoTOrderThree_piGU_conj_mem w⁻¹ (show piGU w * t * (piGU w)⁻¹ ∈ T46 from ht)
    have e : (piGU w)⁻¹ * (piGU w * t * (piGU w)⁻¹) * (piGU w)⁻¹⁻¹ = t := by group
    rwa [map_inv, e] at h2

private theorem piGU_range_le_autT :
    piGU.range ≤ autT := by
  rintro _ ⟨g, rfl⟩
  exact piGU_mem_autT g

private theorem three_card_le_card_range :
    3 * 9196830720 ≤ Nat.card piGU.range := by
  have h2 : Nat.card SU0 = 9196830720 * Nat.card (Subgroup.center SU0) := by
    rw [card_SU0_eq, range_piSU, card_T46, ker_piSU]
  have h4 : Nat.card piGU.ker * Nat.card piGU.range = Nat.card GU0 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h6 : Nat.card piGU.ker * Nat.card piGU.range ≤ 3 * Nat.card piGU.range :=
    Nat.mul_le_mul_right _ card_piGU_ker_le
  have := card_SU0_mul_three_le
  have := three_le_card_center
  omega

theorem mem_range_piGU_of_pow_three_eq_one
    {y : Equiv.Perm (Fin 693)}
    (hy : y ∈ autT) (h3 : y ^ 3 = 1) : y ∈ piGU.range := by
  have hcardH : Nat.card (piGU.range.subgroupOf autT) = Nat.card piGU.range :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe piGU_range_le_autT).toEquiv
  have hmul := Subgroup.card_mul_index (piGU.range.subgroupOf autT)
  rw [hcardH, CFSG.EvenSmallLie.UnitarySix.YamadaHAut.card_autT] at hmul
  have hI0 : (piGU.range.subgroupOf autT).index ≠ 0 := fun h0 => by
    rw [h0, Nat.mul_zero] at hmul
    omega
  have hI2 : (piGU.range.subgroupOf autT).index ≤ 2 := by
    have h := Nat.mul_le_mul_right (piGU.range.subgroupOf autT).index three_card_le_card_range
    omega
  rcases (by omega : (piGU.range.subgroupOf autT).index = 1 ∨
      (piGU.range.subgroupOf autT).index = 2) with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    have hmem : (⟨y, hy⟩ : autT) ∈ piGU.range.subgroupOf autT := by
      rw [h1]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hmem
  · haveI : (piGU.range.subgroupOf autT).Normal := Subgroup.normal_of_index_eq_two h2
    have hcard : Nat.card (↥autT ⧸ piGU.range.subgroupOf autT) = 2 := h2
    have hyA3 : (⟨y, hy⟩ : autT) ^ 3 = 1 := Subtype.ext (by simpa using h3)
    have hq3 : (QuotientGroup.mk (⟨y, hy⟩ : autT) :
        ↥autT ⧸ piGU.range.subgroupOf autT) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, hyA3, QuotientGroup.mk_one]
    have hd2 := orderOf_dvd_natCard (QuotientGroup.mk (⟨y, hy⟩ : autT) :
        ↥autT ⧸ piGU.range.subgroupOf autT)
    rw [hcard] at hd2
    have hg := Nat.dvd_gcd hd2 (orderOf_dvd_of_pow_eq_one hq3)
    rw [show Nat.gcd 2 3 = 1 by norm_num, Nat.dvd_one] at hg
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 hg))

end CFSG.GGQ2Prime
