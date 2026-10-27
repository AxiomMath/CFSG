module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2LowTorusFixedSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2LowReflectedToriCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralOuterInvolutionConjugacy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralIndexTwoCentralInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Aligning an outer/inner involution pair with the reflected-torus package

The outer-involution transport in Section 4 needs the same conjugator for an
outer involution and the distinguished inner involution.  This module proves
that alignment inside a fixed dihedral Sylow of `PGL₂`: the intersection with
the derived subgroup is a noncyclic index-two subgroup, so its complementary
involutions are conjugate, while the inner involution is the unique nontrivial
central involution.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- A commuting outer/inner involution pair in a Sylow `2`-subgroup of
`PGL₂(K)` is simultaneously conjugate to the pair in the low reflected-torus
package. -/
public theorem pgl2_reflected_tori_aligned_of_outer_inner_pair
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (P : Sylow 2 (PGL2 K)) {m : ℕ}
    (eP : P ≃* DihedralGroup (2 ^ m))
    (r0 t0 : PGL2 K)
    (hrP : r0 ∈ (P : Subgroup (PGL2 K)))
    (htP : t0 ∈ (P : Subgroup (PGL2 K)))
    (hrI : IsInvolution r0) (htI : IsInvolution t0)
    (hrJ : r0 ∉ commutator (PGL2 K))
    (htJ : t0 ∈ commutator (PGL2 K))
    (htcenter : (⟨t0, htP⟩ : P) ∈
      Subgroup.center (P : Subgroup (PGL2 K))) :
    ∃ T : PGL2LowReflectedToriData K P eP, ∃ a : PGL2 K,
      r0 = a * T.s * a⁻¹ ∧ t0 = a * T.t * a⁻¹ := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨T⟩ := pgl2_low_reflected_tori_card_four K hK hcard P eP
  let sp : P := ⟨T.g * T.s * T.g⁻¹, T.conj_s_mem_P⟩
  let tp : P := ⟨T.g * T.t * T.g⁻¹, by
    rw [T.conj_t_eq_central]
    exact (eP.symm (DihedralGroup.r
      (2 ^ (m - 1) : ZMod (2 ^ m)))).property⟩
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  let H : Subgroup P := J.subgroupOf (P : Subgroup (PGL2 K))
  have hJnormal : J.Normal := inferInstance
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
      apply T.s_not_mem_commutator
      have hsH : (⟨T.g * T.s * T.g⁻¹, T.conj_s_mem_P⟩ : P) ∈ H := by
        rw [htop]
        trivial
      have hsJ : T.g * T.s * T.g⁻¹ ∈ J := hsH
      have hback : T.s ∈ J := by
        have hconj := hJnormal.conj_mem (T.g * T.s * T.g⁻¹)
          hsJ T.g⁻¹
        have heq : T.g⁻¹ * (T.g * T.s * T.g⁻¹) *
            (T.g⁻¹)⁻¹ = T.s := by group
        rw [heq] at hconj
        exact hconj
      exact hback
    · exact htwo
  have hHnoncyclic : ¬ IsCyclic H := by
    intro hcyc
    let : J.Normal := hJnormal
    let Q : Sylow 2 J :=
      BenderSuzuki.External.hallSylowSubgroupOfNormal P J
    let eHQ : H ≃* Q :=
      { toFun := fun x =>
          ⟨⟨((x : P) : PGL2 K),
              (Subgroup.mem_subgroupOf.mp x.property)⟩, by
            rw [BenderSuzuki.External.hallSylowSubgroupOfNormal_coe]
            exact (x : P).property⟩
        invFun := fun y =>
          ⟨⟨((y : J) : PGL2 K), by
              let yJ : J := y
              have hyQ : yJ ∈ (Q : Subgroup J) := y.property
              rw [BenderSuzuki.External.hallSylowSubgroupOfNormal_coe] at hyQ
              exact hyQ⟩,
            (y : J).property⟩
        left_inv := by intro x; rfl
        right_inv := by intro y; rfl
        map_mul' := by intro x y; rfl }
    have hQcyc : IsCyclic Q := eHQ.isCyclic.mp hcyc
    let eJ : J ≃* PSL2 K :=
      (commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
        K hK hcard (MulEquiv.refl (PGL2 K))).some
    let Qmodel : Sylow 2 (PSL2 K) :=
      Q.mapSurjective (f := eJ.toMonoidHom) eJ.surjective
    have hQmodelcyc : IsCyclic Qmodel := by
      let eQmap : Q ≃* (Q : Subgroup J).map eJ.toMonoidHom :=
        Subgroup.equivMapOfInjective (Q : Subgroup J)
          eJ.toMonoidHom eJ.injective
      have hcoe : (Q : Subgroup J).map eJ.toMonoidHom =
          (Qmodel : Subgroup (PSL2 K)) := by
        symm
        exact Sylow.coe_mapSurjective
          (f := eJ.toMonoidHom) eJ.surjective Q
      let eQ : Q ≃* Qmodel :=
        eQmap.trans (MulEquiv.subgroupCongr hcoe)
      exact eQ.isCyclic.mp hQcyc
    obtain ⟨n, _hn, ⟨eD⟩⟩ :=
      psl2_odd_hasDihedralSylowTwo_model K hK Qmodel
    have hDcyc : IsCyclic (DihedralGroup (2 ^ n)) :=
      eD.isCyclic.mp hQmodelcyc
    apply DihedralGroup.not_isCyclic
      (show 2 ^ n ≠ 1 by
        exact ne_of_gt
          (Nat.one_lt_pow (by omega : n ≠ 0) (by norm_num : 1 < 2)))
    exact hDcyc
  have hspI : IsInvolution sp := by
    constructor
    · intro h
      apply T.s_involution.1
      have h' : T.g * T.s * T.g⁻¹ = 1 := congrArg Subtype.val h
      calc
        T.s = T.g⁻¹ * (T.g * T.s * T.g⁻¹) * (T.g⁻¹)⁻¹ := by group
        _ = 1 := by rw [h']; simp
    · apply Subtype.ext
      change (T.g * T.s * T.g⁻¹) ^ 2 = 1
      calc
        (T.g * T.s * T.g⁻¹) ^ 2 =
            T.g * (T.s ^ 2) * T.g⁻¹ := by
          simp only [pow_two]
          group
        _ = 1 := by simpa [pow_two] using T.s_involution.2
  have hspJ : (sp : P) ∉ H := by
    intro h
    apply T.s_not_mem_commutator
    have hsJ : T.g * T.s * T.g⁻¹ ∈ J :=
      Subgroup.mem_subgroupOf.mp h
    have hback := hJnormal.conj_mem (T.g * T.s * T.g⁻¹) hsJ T.g⁻¹
    have heq : T.g⁻¹ * (T.g * T.s * T.g⁻¹) *
        (T.g⁻¹)⁻¹ = T.s := by group
    rw [heq] at hback
    exact hback
  have htpJ : (tp : P) ∈ H := by
    change T.g * T.t * T.g⁻¹ ∈ J
    exact hJnormal.conj_mem T.t T.t_mem_commutator T.g
  have htp0eq : (tp : P) = ⟨t0, htP⟩ := by
    apply eP.injective
    have ht0central :=
      eq_central_involution_of_mem_indexTwo_of_commuting_involution_not_mem
        (pgl2_dihedral_sylow_parameter_ge_two K hK P eP) eP H hHindex
        (⟨t0, htP⟩ : P) (sp : P)
        (Subgroup.mem_subgroupOf.mpr htJ) hspJ
        (by intro h; exact htI.1 (congrArg Subtype.val h))
        (by intro h; exact hspI.1 h)
        (by
          apply Subtype.ext
          simpa [pow_two] using htI.2)
        (by simpa [pow_two] using hspI.2)
        (by
          show (⟨t0, htP⟩ : P) * sp = sp * ⟨t0, htP⟩
          exact (Subgroup.mem_center_iff.mp htcenter sp).symm)
    have htpcentral : (tp : P) =
        eP.symm (DihedralGroup.r
          (2 ^ (m - 1) : ZMod (2 ^ m))) := by
      apply Subtype.ext
      exact T.conj_t_eq_central
    rw [htpcentral, ht0central]
  have hconj : IsConj (sp : P) (⟨r0, hrP⟩ : P) :=
    dihedral_involutions_not_mem_noncyclic_index_two_isConj
      (pgl2_dihedral_sylow_parameter_ge_two K hK P eP)
      eP H hHindex hHnoncyclic hspI
      ⟨fun h => hrI.1 (congrArg Subtype.val h), by
        simpa [pow_two] using hrI.2⟩ hspJ (by
          intro h
          exact hrJ h)
  obtain ⟨b, hb⟩ := isConj_iff.mp hconj
  let a : PGL2 K := (b : PGL2 K) * T.g
  refine ⟨T, a, ?_, ?_⟩
  · symm
    calc
      a * T.s * a⁻¹ = (b : PGL2 K) *
          (T.g * T.s * T.g⁻¹) * (b : PGL2 K)⁻¹ := by
            simp [a]
            group
      _ = r0 := by simpa [sp] using congrArg Subtype.val hb
  · symm
    calc
      a * T.t * a⁻¹ = (b : PGL2 K) *
          (T.g * T.t * T.g⁻¹) * (b : PGL2 K)⁻¹ := by
            simp [a]
            group
      _ = t0 := by
        have htpcenter : tp ∈
            Subgroup.center (P : Subgroup (PGL2 K)) := by
          exact htp0eq ▸ htcenter
        have htpcent := Subgroup.mem_center_iff.mp htpcenter (b : P)
        have hbtp : (b : P) * tp = tp * (b : P) := htpcent
        have htpval : (tp : PGL2 K) = t0 := by
          exact congrArg Subtype.val htp0eq
        change (b : PGL2 K) * (tp : PGL2 K) *
          (b : PGL2 K)⁻¹ = t0
        calc
          (b : PGL2 K) * (tp : PGL2 K) * (b : PGL2 K)⁻¹ =
              (tp : PGL2 K) * (b : PGL2 K) * (b : PGL2 K)⁻¹ := by
                have hbtpG : (b : PGL2 K) * (tp : PGL2 K) =
                    (tp : PGL2 K) * (b : PGL2 K) := by
                  simpa using congrArg Subtype.val hbtp
                rw [hbtpG]
          _ = (tp : PGL2 K) := by simp
          _ = t0 := htpval

end CFSG.GorensteinWalter
