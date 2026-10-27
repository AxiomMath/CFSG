module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmSmallBlock
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthKer

public section

namespace CFSG.StandardType.OrthTorusGen

open Module Multiplicative QuadraticMap Polynomial
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.LayerCores CFSG.StandardType.LayerFacts
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem fixedSpace_eq_suppPerp_frame (F : SevOm.Frame Q p E r)
    (s : Multiplicative (Fin r → ZMod p)) :
    fixedSpace (F.ι s) = suppPerp Q (⨆ j : {j : Fin r // toAdd s j ≠ 0}, F.U j) := by
  ext v
  rw [mem_fixedSpace, F.fix, mem_suppPerp]
  constructor
  · intro hv y hy
    exact Submodule.iSup_induction _ (motive := fun y => QuadraticMap.polar Q y v = 0) hy
      (fun j y hy => hv j.1 j.2 y hy) (by simp)
      (fun a b ha hb => by rw [QuadraticMap.polar_add_left, ha, hb, add_zero])
  · intro hv j hj u hu
    exact hv u (Submodule.mem_iSup_of_mem ⟨j, hj⟩ hu)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem iSupIndep_frame_pieces (F : SevOm.Frame Q p E r) (P : Fin r → Prop) :
    iSupIndep (fun j : {j : Fin r // P j} => F.U j.1) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro t v hv hsum i hi
  refine F.nondeg i.1 (v i) (hv i hi) fun u hu => ?_
  have h1 : ∑ j ∈ t, QuadraticMap.polar Q u (v j) = 0 := by
    change ∑ j ∈ t, (QuadraticMap.polarBilin Q u) (v j) = 0
    rw [← map_sum (QuadraticMap.polarBilin Q u), hsum, map_zero]
  have h2 : ∑ j ∈ t, QuadraticMap.polar Q u (v j) = QuadraticMap.polar Q u (v i) := by
    rw [Finset.sum_eq_single i]
    · intro j hj hji
      exact F.orth i.1 j.1 (fun h => hji (Subtype.ext h.symm)) u hu (v j) (hv j hj)
    · intro h
      exact absurd hi h
  rwa [h2] at h1

omit [Finite K] [CharP K 2] in
theorem finrank_iSup_frame_pieces (F : SevOm.Frame Q p E r)
    (hU : ∀ j, finrank K (F.U j) = 2) (P : Fin r → Prop) [DecidablePred P] :
    finrank K ((⨆ j : {j : Fin r // P j}, F.U j.1) : Submodule K V) =
      2 * Fintype.card {j : Fin r // P j} := by
  rw [TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep (iSupIndep_frame_pieces F P)]
  calc ∑ i : {j : Fin r // P j}, finrank K (F.U i)
      = ∑ _ : {j : Fin r // P j}, 2 := Finset.sum_congr rfl fun i _ => hU i
    _ = 2 * Fintype.card {j : Fin r // P j} := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        omega

omit [Finite K] [CharP K 2] in
theorem exists_coord_eq_zero (hQ : (polarBilin Q).Nondegenerate)
    (F : SevOm.Frame Q p E r) (hU : ∀ j, finrank K (F.U j) = 2)
    (hV : finrank K V ≤ 2 * r + 2) (s : Multiplicative (Fin r → ZMod p))
    (h4 : 4 ≤ finrank K (fixedSpace (F.ι s))) : ∃ k, toAdd s k = 0 := by
  classical
  by_contra h
  push Not at h
  have hdim : finrank K (fixedSpace (F.ι s)) =
      finrank K V - 2 * Fintype.card {j : Fin r // toAdd s j ≠ 0} := by
    rw [fixedSpace_eq_suppPerp_frame F s, suppPerp,
      LinearMap.BilinForm.finrank_orthogonal (B := polarBilin Q) hQ,
      finrank_iSup_frame_pieces F hU (fun j => toAdd s j ≠ 0)]
  rw [hdim] at h4
  have hcard : Fintype.card {j : Fin r // toAdd s j ≠ 0} = r := by
    simp [h]
  rw [hcard] at h4
  omega

omit [Finite K] in
theorem exists_mem_of_odd_mem (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (hU : ∀ j, finrank K (F.U j) = 2) (hV : finrank K V ≤ 2 * r + 2) {e : ℕ}
    (hz : ∀ k, ∃ z ∈ orthDerived Q, (∀ c ∈ E, z * c = c * z) ∧ orderOf z = p ^ e ∧
      ∀ v, (∀ u ∈ F.U k, polar Q u v = 0) → z v = v)
    (s : Multiplicative (Fin r → ZMod p)) {J : Subgroup (V ≃ₗ[K] V)}
    (h4 : 4 ≤ finrank K (fixedSpace (F.ι s)))
    (hodd : ∀ u ∈ supportedBlock Q (F.ι s) (X - 1), Odd (orderOf u) → u ∈ J) :
    ∃ y ∈ J, (∀ c ∈ E, y * c = c * y) ∧ orderOf y = p ^ e := by
  classical
  have hx : OddOrderIsometry Q p (F.ι s) := F.oddOrderIsometry hQ hp2 hp hEΩ s
  obtain ⟨k, hk⟩ := exists_coord_eq_zero hQ F hU hV s h4
  obtain ⟨z, hzO, hzE, hzord, hzfix⟩ := hz k
  have hzC : z ∈ isometryCentralizer Q (F.ι s) :=
    Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup hzO,
      Subgroup.mem_centralizer_singleton_iff.mpr (hzE _ (F.mem s))⟩
  have hperp : othersSpace (F.ι s).toLinearMap (X - 1) ≤ suppPerp Q (fixedSpace (F.ι s)) :=
    fun r hr => mem_suppPerp.mpr fun w hw => hx.fixed_others.2 w hw r hr
  have hzF : z ∈ supportedBlock Q (F.ι s) (X - 1) :=
    mem_supportedBlock.mpr ⟨hzC, fun v hv =>
      hzfix v fun u hu => mem_suppPerp.mp (hperp hv) u (F.le_fixedSpace hk hu)⟩
  refine ⟨z, hodd z hzF ?_, hzE, hzord⟩
  rw [hzord]
  exact Odd.pow (hp.odd_of_ne_two hp2)


end CFSG.StandardType.OrthTorusGen
