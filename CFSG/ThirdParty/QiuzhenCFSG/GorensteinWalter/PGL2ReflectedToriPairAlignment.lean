module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2ReflectedToriAligned
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Aligning an outer/inner involution pair in odd `PGL₂`

The fixed-Sylow reflected-torus theorem is most useful when the Sylow
subgroup is not chosen in advance.  A commuting outer/inner pair generates a
Klein four, hence lies in a common Sylow `2`-subgroup.  The derived subgroup
cuts this Sylow in an index-two subgroup; the dihedral index-two lemma then
identifies the inner involution with the central rotation.  This wrapper
supplies the common-Sylow and centrality steps before invoking the fixed-Sylow
alignment theorem.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- A commuting outer/inner involution pair in odd `PGL₂(K)` is simultaneously
conjugate to the pair in a low reflected-torus package. -/
public theorem pgl2_reflected_tori_pair_alignment
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (r0 t0 : PGL2 K)
    (hrI : IsInvolution r0) (htI : IsInvolution t0)
    (hrt : Commute r0 t0)
    (hrJ : r0 ∉ commutator (PGL2 K))
    (htJ : t0 ∈ commutator (PGL2 K)) :
    ∃ P : Sylow 2 (PGL2 K), ∃ m : ℕ,
      ∃ eP : P ≃* DihedralGroup (2 ^ m),
        ∃ T : PGL2LowReflectedToriData K P eP, ∃ a : PGL2 K,
          r0 = a * T.s * a⁻¹ ∧ t0 = a * T.t * a⁻¹ := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  have hrtne : r0 ≠ t0 := by
    intro h
    apply hrJ
    simpa [h] using htJ
  obtain ⟨V, hV, hrV, htV⟩ :=
    exists_kleinFour_of_commuting_involutions r0 t0 hrI htI hrtne hrt
  have hVp : IsPGroup 2 V := by
    apply IsPGroup.of_card (n := 2)
    rw [hV.card_four]
    norm_num
  obtain ⟨P, hVP⟩ :=
    IsPGroup.exists_le_sylow (G := PGL2 K) (p := 2) hVp
  have hrP : r0 ∈ (P : Subgroup (PGL2 K)) := hVP hrV
  have htP : t0 ∈ (P : Subgroup (PGL2 K)) := hVP htV
  obtain ⟨m, _hm, ⟨eP⟩⟩ :=
    pgl2_odd_hasDihedralSylowTwo_model K hK P
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  let H : Subgroup P := J.subgroupOf (P : Subgroup (PGL2 K))
  have hJnormal : J.Normal := by
    dsimp [J]
    infer_instance
  have hJindex : J.index = 2 := by
    dsimp [J]
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
    exact pgl2_psl2Range_index_eq_two K hK
  have hHindex : H.index = 2 := by
    have hdvd : H.index ∣ 2 := by
      change J.relIndex (P : Subgroup (PGL2 K)) ∣ 2
      simpa [hJindex] using
        (Subgroup.relIndex_dvd_index_of_normal J
          (P : Subgroup (PGL2 K)))
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo
    · exfalso
      have htop : H = ⊤ := Subgroup.index_eq_one.mp hone
      apply hrJ
      have hrH : (⟨r0, hrP⟩ : P) ∈ H := by
        rw [htop]
        trivial
      exact Subgroup.mem_subgroupOf.mp hrH
    · exact htwo
  have htH : (⟨t0, htP⟩ : P) ∈ H :=
    Subgroup.mem_subgroupOf.mpr htJ
  have hrnotH : (⟨r0, hrP⟩ : P) ∉ H := by
    intro h
    apply hrJ
    exact Subgroup.mem_subgroupOf.mp h
  have htscomm : Commute (⟨t0, htP⟩ : P) (⟨r0, hrP⟩ : P) := by
    change (⟨t0, htP⟩ : P) * (⟨r0, hrP⟩ : P) =
      (⟨r0, hrP⟩ : P) * (⟨t0, htP⟩ : P)
    apply Subtype.ext
    exact hrt.eq.symm
  have htcentralEq :
      (⟨t0, htP⟩ : P) = eP.symm
        (DihedralGroup.r (2 ^ (m - 1) : ZMod (2 ^ m))) := by
    apply eq_central_involution_of_mem_indexTwo_of_commuting_involution_not_mem
      (pgl2_dihedral_sylow_parameter_ge_two K hK P eP) eP H hHindex
      (⟨t0, htP⟩ : P) (⟨r0, hrP⟩ : P) htH hrnotH
    · intro h
      exact htI.1 (congrArg Subtype.val h)
    · intro h
      exact hrI.1 (congrArg Subtype.val h)
    · apply Subtype.ext
      simpa [pow_two] using htI.2
    · apply Subtype.ext
      simpa [pow_two] using hrI.2
    · exact htscomm
  have htcenter : (⟨t0, htP⟩ : P) ∈
      Subgroup.center (P : Subgroup (PGL2 K)) := by
    rw [htcentralEq]
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply eP.injective
    simpa only [map_mul, eP.apply_symm_apply] using
      (Subgroup.mem_center_iff.mp
        (central_rotation_mem_center_dihedral_two_pow
          (pgl2_dihedral_sylow_parameter_ge_two K hK P eP)) (eP x))
  obtain ⟨T, a, hra, hta⟩ :=
    pgl2_reflected_tori_aligned_of_outer_inner_pair
      K hK hcard P eP r0 t0 hrP htP hrI htI hrJ htJ htcenter
  exact ⟨P, m, eP, T, a, hra, hta⟩

end CFSG.GorensteinWalter
