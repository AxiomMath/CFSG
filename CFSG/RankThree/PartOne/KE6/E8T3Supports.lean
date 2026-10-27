module

public import CFSG.RankThree.PartOne.KE6.E8T3Check
public import CFSG.RankThree.PartOne.KF4.KernelTools

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint

theorem mem_jlist {J : Finset (Fin Tag.E8.rank)} {j : Fin Tag.E8.rank} : j ∈ jlist J ↔ j ∈ J := by
  simp [jlist]

theorem nodup_jlist (J : Finset (Fin Tag.E8.rank)) : (jlist J).Nodup :=
  (List.nodup_finRange _).filter _

theorem ncard_parabolicRoots_E8 (J : Finset (Fin Tag.E8.rank)) :
    (parabolicRoots Tag.E8 (↑J : Set (Fin Tag.E8.rank))).ncard = e8PhiCard J := by
  have h := ncard_isRoot_and (τ := Tag.E8) (fun v => ∀ i, i ∉ J → v i = 0)
  have e : parabolicRoots Tag.E8 (↑J : Set (Fin Tag.E8.rank)) =
      {v | IsRoot Tag.E8 v ∧ ∀ i, i ∉ J → v i = 0} := by
    ext v
    simp [parabolicRoots]
  rw [e, h]
  rfl

theorem finite_parabolicRoots_E8 (J : Set (Fin Tag.E8.rank)) :
    (parabolicRoots Tag.E8 J).Finite := by
  refine ((Tag.E8.artifactRoots.map (toVec Tag.E8.rank)).toFinset.finite_toSet).subset ?_
  intro v hv
  obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hv.1
  simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
  exact ⟨l, hl, rfl⟩

theorem isRoot_ne_zero {v : V8} (hv : IsRoot Tag.E8 v) : v ≠ 0 := by
  intro h
  obtain ⟨j, hj⟩ := CFSG.LieType.Steinberg.Adjoint.iform_self_of_isRoot hv
  rw [h] at hj
  have : (0 : ℤ) < 2 * Tag.E8.symmetrizer j j := by
    have := CFSG.LieType.Chevalley.symmetrizer_pos Tag.E8 j
    omega
  simp [iform] at hj
  omega

theorem weylMatrix_sq_E8 {T : WeylGroup Tag.E8} (hrel : ∀ x : V8, T • T • x + T • x + x = 0) :
    weylMatrix T * weylMatrix T + weylMatrix T + 1 = 0 := by
  refine Matrix.ext_of_mulVec_single fun c => ?_
  have h := hrel (Pi.single c 1 : V8)
  rw [Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, weylMatrix_mulVec,
    weylMatrix_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec]
  exact h

theorem e8T3_supports {T : WeylGroup Tag.E8} {J : Finset (Fin Tag.E8.rank)}
    (hJ : J ≠ Finset.univ) (hrel : ∀ x : V8, T • T • x + T • x + x = 0)
    (hmaps : ∀ β ∈ parabolicRoots Tag.E8 (↑J : Set (Fin Tag.E8.rank)),
      T • β ∈ parabolicRoots Tag.E8 ↑J) : J ∈ e8T3Supports := by
  classical
  have hcols : ∀ j ∈ J, ∀ i, i ∉ J → colT T j i = 0 := fun j hj i hi => by
    have hmem : (Pi.single j 1 : V8) ∈ parabolicRoots Tag.E8 (↑J : Set (Fin Tag.E8.rank)) :=
      ⟨isRoot_single Tag.E8 j, fun i hi' => Pi.single_eq_of_ne
        (fun h : i = j => hi' (by rw [h]; exact Finset.mem_coe.2 hj)) 1⟩
    exact (hmaps _ hmem).2 i (by simpa using hi)
  have hM := weylMatrix_sq_E8 hrel
  have heven : J.card % 2 = 0 := by
    have := CFSG.RankThree.PartOne.KF4.even_card_of_sq_add_self_add_one hM J
      (fun a ha c hc => hcols c hc a ha)
    exact Nat.even_iff.1 this
  have hT3 : T ^ 3 = 1 := by
    apply weylMatrix_injective
    rw [weylMatrix_pow, weylMatrix_one]
    have h2 : weylMatrix T * weylMatrix T = -weylMatrix T - 1 := by
      rw [← sub_eq_zero, ← hM]; abel
    calc weylMatrix T ^ 3 = weylMatrix T * (weylMatrix T * weylMatrix T) := by
          rw [pow_succ, pow_two, mul_assoc]
      _ = 1 := by
          rw [h2, mul_sub, mul_neg, mul_one, h2]
          abel
  have h3 : 3 ∣ e8PhiCard J := by
    rw [← ncard_parabolicRoots_E8]
    refine CFSG.RankThree.PartOne.KF4.three_dvd_ncard_of_free (finite_parabolicRoots_E8 _) hT3 hmaps
      ?_
    intro x hx hxx
    have h1 := hrel x
    rw [hxx, hxx] at h1
    exact isRoot_ne_zero hx.1 (by
      funext i
      have := congrFun h1 i
      simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
      omega)
  rcases e8T3_finite_check J hJ heven h3 with h | h
  · exact h
  · exfalso
    refine not_of_noT hrel (jlist J) (nodup_jlist J) (fun j hj i hi => hcols j (mem_jlist.1 hj) i
      (fun h' => hi (mem_jlist.2 h'))) h

end CFSG.RankThree.PartOne.KE6
