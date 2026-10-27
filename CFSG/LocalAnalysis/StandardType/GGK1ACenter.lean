module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.LocalAnalysis.StandardType.GGK1ACenterNoglue
public import CFSG.LocalAnalysis.StandardType.GGK1ACenterReduce
public import CFSG.LocalAnalysis.StandardType.GGK1ACenterCount
public import CFSG.LocalAnalysis.StandardType.GGK1ACenterSLSubOne
public import CFSG.LocalAnalysis.StandardType.GGK1ACenterSLAddOne
public import CFSG.LocalAnalysis.StandardType.GGK1ACenterSUAddOne
public import CFSG.LocalAnalysis.StandardType.GGK1ACenterSUSubOne
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniMat

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LieType.SemisimpleCentralizers.HeldLang

private theorem cenD_charP_two {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])

private theorem cenD_natCast_ne_zero {K : Type} [Field K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : (p : K) ≠ 0 := by
  intro h0
  have hdvd : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h0
  exact (hp.odd_of_ne_two hp2).not_two_dvd_nat hdvd

private theorem cenD_coe_pow {X : Type} [Group X] {H : Subgroup X} {x : H} {p : ℕ}
    (hxp : x ^ p = 1) : (x : X) ^ p = 1 := by
  rw [← Subgroup.coe_pow, hxp, Subgroup.coe_one]

private theorem cenD_mem_sl_conj {N : ℕ} {K : Type} [Field K] (A g : GL (Fin N) K)
    (hg : g ∈ LargeEvenSLGroup (Fin N) K) : A * g * A⁻¹ ∈ LargeEvenSLGroup (Fin N) K := by
  have hgd : Matrix.GeneralLinearGroup.det g = 1 := by
    rw [← Units.val_eq_one, Matrix.GeneralLinearGroup.val_det_apply]
    exact TypeA.mem_largeEvenSLGroup_iff.mp hg
  rw [TypeA.mem_largeEvenSLGroup_iff, ← Matrix.GeneralLinearGroup.val_det_apply,
    Units.val_eq_one, map_mul, map_mul, hgd, mul_one]
  exact mul_inv_cancel (Matrix.GeneralLinearGroup.det A)

private theorem cenD_su_subset_gu {N nf : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {A : GL (Fin N) K} (hA : A ∈ LargeEvenSUGroup (Fin N) K (2 ^ nf)) :
    A ∈ LargeEvenGUSet (Fin N) K (2 ^ nf) := by
  obtain ⟨-, hu⟩ := (CFSG.LocalAnalysis.GLTheoremA.FQ.mem_LargeEvenSU_iff (g := nf) A).mp hA
  exact ⟨1, one_ne_zero, by norm_num, by simpa using hu⟩

private theorem cenD_not_dvd_sub_one_of_dvd_add_one {p nf : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ 2 ^ nf + 1) : ¬ p ∣ 2 ^ nf - 1 := by
  intro h'
  have hpow : 1 ≤ 2 ^ nf := Nat.one_le_pow nf 2 (by norm_num)
  have hplus : ((p : ℤ)) ∣ (2 : ℤ) ^ nf + 1 := by
    have hZ : ((p : ℤ)) ∣ ((2 ^ nf + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
    simpa using hZ
  have hminus : ((p : ℤ)) ∣ (2 : ℤ) ^ nf - 1 := by
    have hZ : ((p : ℤ)) ∣ ((2 ^ nf - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h'
    rwa [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hZ
  have htwo : ((p : ℤ)) ∣ 2 := by
    have := dvd_sub hplus hminus
    rwa [show (2 : ℤ) ^ nf + 1 - ((2 : ℤ) ^ nf - 1) = 2 by ring] at this
  have hp2' : p ∣ 2 := Int.natCast_dvd_natCast.mp htwo
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2'
  exact hp2 (le_antisymm hle hp.two_le)

private theorem cenD_pair_ne_three_two {p nf N : ℕ} (hp : p.Prime)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (hRA : ¬ (p ∣ N ∧ p ∣ 2 ^ nf + 1)) :
    (N, 2 ^ nf) ≠ (3, 2) := by
  rintro h
  have hN : N = 3 := congrArg Prod.fst h
  have hq : 2 ^ nf = 2 := congrArg Prod.snd h
  rcases hdvd with h | h
  · rw [hq] at h
    norm_num at h
    exact hp.ne_one h
  · rw [hq] at h
    have hp3 : p = 3 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h with h1 | h1
      · exact absurd h1 hp.ne_one
      · exact h1
    exact hRA ⟨by simp [hN, hp3], by simpa [hq] using h⟩

private theorem cenD_linear_of_le {p nf N d : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hK : Nat.card K = 2 ^ nf)
    (hRA : ¬ (p ∣ N ∧ p ∣ 2 ^ nf - 1)) (hN : 3 ≤ N)
    {xhat : ↥(LargeEvenSLGroup (Fin N) K)} (hxp : xhat ^ p = 1)
    {m : List ℕ} {T : Subgroup (GL (Fin N) K)}
    (hTSL : T ≤ LargeEvenSLGroup (Fin N) K)
    (hTtors : T ≤ ggK1A_torsGL (xhat : GL (Fin N) K) p)
    (hTscal : T ⊓ LargeEvenScalars (Fin N) K = ⊥)
    (hcard : Nat.card T = p ^ (ggMultDatumA p nf d false m).rZ) :
    GGK1Center p (ggMultDatumA p nf d false m)
      (LargeEvenProj (LargeEvenSLGroup (Fin N) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (Set.univ : Set (GL (Fin N) K)))
      (MulAut.conj (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) xhat)) := by
  refine ggK1Center_of_le (G := LargeEvenSLGroup (Fin N) K) (S := Set.univ) (x := xhat)
    (D := ggMultDatumA p nf d false m) (T := T) (Set.subset_univ _) ?_ ?_ ?_ hTSL ?_
    hTscal hcard ?_
  · intro A _ g hg
    exact cenD_mem_sl_conj A g hg
  · exact center_largeEvenProj_largeEvenSLGroup_eq_bot hN
  · intro A _ hA
    exact ggK1A_commute_of_conj_mul_inv_mem_scalars hp hK hRA xhat.2
      (cenD_coe_pow hxp) hA
  · exact isElemAbelian_of_le_ggK1A_torsGL hTtors
  · intro t ht A hA
    exact commute_of_mem_ggK1A_torsGL (hTtors ht) hA

private theorem cenD_unitary_of_le {p nf N d : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hp : p.Prime) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hRA : ¬ (p ∣ N ∧ p ∣ 2 ^ nf + 1)) (hN : 3 ≤ N) (hdq : (N, 2 ^ nf) ≠ (3, 2))
    {xhat : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))} (hxp : xhat ^ p = 1)
    {m : List ℕ} {T : Subgroup (GL (Fin N) K)}
    (hTSU : T ≤ LargeEvenSUGroup (Fin N) K (2 ^ nf))
    (hTtors : T ≤ ggK1A_torsGL (xhat : GL (Fin N) K) p)
    (hTscal : T ⊓ LargeEvenScalars (Fin N) K = ⊥)
    (hcard : Nat.card T = p ^ (ggMultDatumA p nf d true m).rZ) :
    GGK1Center p (ggMultDatumA p nf d true m)
      (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ nf)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)))
        (LargeEvenGUSet (Fin N) K (2 ^ nf)))
      (MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)) xhat)) := by
  refine ggK1Center_of_le (G := LargeEvenSUGroup (Fin N) K (2 ^ nf))
    (S := LargeEvenGUSet (Fin N) K (2 ^ nf)) (x := xhat)
    (D := ggMultDatumA p nf d true m) (T := T) (fun A hA => cenD_su_subset_gu hA) ?_ ?_
    ?_ hTSU ?_ hTscal hcard ?_
  · intro A hA g hg
    exact CFSG.LocalAnalysis.GLTheoremA.T156.Uni.conj_mem_su hA hg
  · exact TableBUE.center_proj_eq_bot hK hN hdq
  · intro A hA hAx
    exact ggK1A_uni_commute_of_conj_mul_inv_mem_scalars hp hK hRA xhat.2
      (cenD_coe_pow hxp) hA hAx
  · exact isElemAbelian_of_le_ggK1A_torsGL hTtors
  · intro t ht A hA
    exact commute_of_mem_ggK1A_torsGL (hTtors ht) hA

theorem ggK1A_core_center {p nf N d : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (hRA : ¬ (p ∣ N ∧ p ∣ 2 ^ nf - 1))
    (hd : d = ggMultOrd p nf)
    {xhat : ↥(LargeEvenSLGroup (Fin N) K)} (hxp : xhat ^ p = 1) {m : List ℕ}
    (hm : GGK1AMultOf p nf N false K (xhat : GL (Fin N) K) m) :
    GGK1Center p (ggMultDatumA p nf d false m)
      (LargeEvenProj (LargeEvenSLGroup (Fin N) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (Set.univ : Set (GL (Fin N) K)))
      (MulAut.conj (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) xhat)) := by
  intro h2
  have : CharP K 2 := cenD_charP_two hK
  have hsq : Squarefree (minpoly K (ggK1A_glEnd (xhat : GL (Fin N) K))) :=
    squarefree_minpoly_ggK1A_glEnd (cenD_natCast_ne_zero hp hp2) (cenD_coe_pow hxp)
  have hN : 3 ≤ N := ggK1A_three_le_of_two_le_rZ hp hp2 hdvd hd hm h2
  rcases hdvd with hsub | hadd
  · have hord : ggMultOrd p nf = 1 := by rw [ggMultOrd, if_pos hsub]
    have hNp : ¬ p ∣ N := fun h => hRA ⟨h, hsub⟩
    obtain ⟨T, hTSL, hTtors, hTscal, hTcard⟩ :=
      ggK1A_exists_torsion_sl_of_dvd_sub_one hp hK hsub hNp (cenD_coe_pow hxp)
    have hcnt := ggK1A_rZ_eq_card_primaryFactors_sub_one hsq
      (Or.inl ⟨rfl, hd.trans hord⟩) hd hm
    have hcard : Nat.card T = p ^ (ggMultDatumA p nf d false m).rZ := by
      rw [hTcard, hcnt]
    exact cenD_linear_of_le hp hK hRA hN hxp hTSL hTtors hTscal hcard h2
  · have hnot : ¬ p ∣ 2 ^ nf - 1 := cenD_not_dvd_sub_one_of_dvd_add_one hp hp2 hadd
    have hord : ggMultOrd p nf = 2 := by rw [ggMultOrd, if_neg hnot, if_pos hadd]
    obtain ⟨T, hTSL, hTtors, hTscal, hTcard⟩ :=
      ggK1A_exists_torsion_sl_of_dvd_add_one hp hK hadd (cenD_coe_pow hxp)
    have hcnt := ggK1A_rZ_eq_card_selfDualFactors hd hord hm
    have hcard : Nat.card T = p ^ (ggMultDatumA p nf d false m).rZ := by
      rw [hTcard, hcnt]
    exact cenD_linear_of_le hp hK hRA hN hxp hTSL hTtors hTscal hcard h2

theorem ggK1A_uni_core_center {p nf N d : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (hRA : ¬ (p ∣ N ∧ p ∣ 2 ^ nf + 1))
    (hd : d = ggMultOrd p nf)
    {xhat : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))} (hxp : xhat ^ p = 1) {m : List ℕ}
    (hm : GGK1AMultOf p nf N true K (xhat : GL (Fin N) K) m) :
    GGK1Center p (ggMultDatumA p nf d true m)
      (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ nf)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)))
        (LargeEvenGUSet (Fin N) K (2 ^ nf)))
      (MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)) xhat)) := by
  intro h2
  have hK' : Nat.card K = 2 ^ (2 * nf) := by
    rw [hK, ← pow_mul]
    congr 1
    omega
  have : CharP K 2 := cenD_charP_two hK'
  have hsq : Squarefree (minpoly K (ggK1A_glEnd (xhat : GL (Fin N) K))) :=
    squarefree_minpoly_ggK1A_glEnd (cenD_natCast_ne_zero hp hp2) (cenD_coe_pow hxp)
  have hN : 3 ≤ N := ggK1A_three_le_of_two_le_rZ hp hp2 hdvd hd hm h2
  rcases hdvd with hsub | hadd
  · have hord : ggMultOrd p nf = 1 := by rw [ggMultOrd, if_pos hsub]
    obtain ⟨T, hTSU, hTtors, hTscal, hTcard⟩ :=
      ggK1A_exists_torsion_su_of_dvd_sub_one hp hp2 hK hsub xhat.2 (cenD_coe_pow hxp)
    have hcnt := ggK1A_uni_two_mul_rZ_eq_card_selfDualFactors hp hp2 hd hord hm
    have hk : (ggK1A_selfDualFactors (xhat : GL (Fin N) K)).card / 2 =
        (ggMultDatumA p nf d true m).rZ := by omega
    have hcard : Nat.card T = p ^ (ggMultDatumA p nf d true m).rZ := by
      rw [hTcard, hk]
    exact cenD_unitary_of_le hp hK hRA hN (cenD_pair_ne_three_two hp (Or.inl hsub) hRA)
      hxp hTSU hTtors hTscal hcard h2
  · have hnot : ¬ p ∣ 2 ^ nf - 1 := cenD_not_dvd_sub_one_of_dvd_add_one hp hp2 hadd
    have hord : ggMultOrd p nf = 2 := by rw [ggMultOrd, if_neg hnot, if_pos hadd]
    have hNp : ¬ p ∣ N := fun h => hRA ⟨h, hadd⟩
    obtain ⟨T, hTSU, hTtors, hTscal, hTcard⟩ :=
      ggK1A_exists_torsion_su_of_dvd_add_one hp hK hadd hNp xhat.2 (cenD_coe_pow hxp)
    have hcnt := ggK1A_rZ_eq_card_primaryFactors_sub_one hsq
      (Or.inr ⟨rfl, hd.trans hord⟩) hd hm
    have hcard : Nat.card T = p ^ (ggMultDatumA p nf d true m).rZ := by
      rw [hTcard, hcnt]
    exact cenD_unitary_of_le hp hK hRA hN (cenD_pair_ne_three_two hp (Or.inr hadd) hRA)
      hxp hTSU hTtors hTscal hcard h2

end CFSG.StandardType

end
