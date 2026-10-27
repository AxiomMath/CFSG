module


public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerNormalizerConjugateMap
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddSubgroupLeNormalIndexTwo
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2LowTorus
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvariantOddPSubgroupCentralized
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2LowDihedralOvergroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ReflectedCyclicIndexTwoSubgroup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Centralization of invariant odd-prime subgroups in odd PGL2

An inner involution reduces to the corresponding `PSL₂` endpoint.  An outer
involution is fused to the low-two-part torus involution.  Its reflected
torus subgroup forces the normalizer intersection with the derived `PSL₂`
subgroup to collapse under Dickson classification, placing the odd subgroup
inside the torus where it is centralized.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- If an odd-prime subgroup of odd `PGL₂(K)` is invariant under the
centralizer of an involution, then that involution centralizes the subgroup. -/
public theorem pgl2_invariant_oddP_subgroup_centralized
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Subgroup (PGL2 K)) (hPp : IsPGroup p P)
    {t : PGL2 K} (ht : IsInvolution t)
    (hPinv : Subgroup.centralizer ({t} : Set (PGL2 K)) ≤
      Subgroup.normalizer (P : Set (PGL2 K))) :
    P ≤ Subgroup.centralizer ({t} : Set (PGL2 K)) := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  rcases hK with ⟨r, f, hr, hrodd, hf, hKcard⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact p.Prime := ⟨hp⟩
  have hK' : IsOddPrimePower (Nat.card K) :=
    ⟨r, f, hr, hrodd, hf, hKcard⟩
  have hqOdd : Odd (Nat.card K) := by
    rw [hKcard]
    exact hrodd.pow
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  have hJindex : J.index = 2 := by
    dsimp [J]
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK' hcard]
    exact pgl2_psl2Range_index_eq_two K hK'
  have hPodd : Odd (Nat.card P) := by
    rcases hPp.exists_card_eq with ⟨a, ha⟩
    rw [ha]
    exact hpodd.pow
  have hPJ : P ≤ J :=
    odd_card_subgroup_le_normal_index_two J P (by infer_instance)
      hJindex hPodd
  let eJ : J ≃* PSL2 K :=
    (commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
      K hK' hcard (MulEquiv.refl (PGL2 K))).some
  by_cases htJ : t ∈ J
  · let PJ : Subgroup J := P.subgroupOf J
    let Q : Subgroup (PSL2 K) := PJ.map eJ.toMonoidHom
    have hPJp : IsPGroup p PJ :=
      hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPJ).symm
    have hQp : IsPGroup p Q := IsPGroup.map hPJp eJ.toMonoidHom
    let tJ : J := ⟨t, htJ⟩
    let t0 : PSL2 K := eJ tJ
    have ht0 : IsInvolution t0 := by
      constructor
      · intro ht0one
        apply ht.1
        have htJone : tJ = 1 := eJ.injective (by simpa [t0] using ht0one)
        exact congrArg Subtype.val htJone
      · have htJsq : tJ ^ 2 = 1 := by
          apply Subtype.ext
          exact ht.2
        simpa [t0] using congrArg eJ htJsq
    have hQinv : Subgroup.centralizer ({t0} : Set (PSL2 K)) ≤
        Subgroup.normalizer (Q : Set (PSL2 K)) := by
      intro c hc
      let cJ : J := eJ.symm c
      have hcJcent : cJ ∈ Subgroup.centralizer ({tJ} : Set J) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply eJ.injective
        simpa [cJ, t0] using
          (Subgroup.mem_centralizer_singleton_iff.mp hc)
      have hcAmbient : (cJ : PGL2 K) ∈
          Subgroup.centralizer ({t} : Set (PGL2 K)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val
          (Subgroup.mem_centralizer_singleton_iff.mp hcJcent)
      have hcNorm : (cJ : PGL2 K) ∈
          Subgroup.normalizer (P : Set (PGL2 K)) := hPinv hcAmbient
      have hcJNorm : cJ ∈ Subgroup.normalizer (PJ : Set J) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        change ((x : PGL2 K) ∈ P ↔
          (cJ : PGL2 K) * (x : PGL2 K) * (cJ : PGL2 K)⁻¹ ∈ P)
        exact (Subgroup.mem_normalizer_iff.mp hcNorm) (x : PGL2 K)
      have hmap : eJ cJ ∈
          (Subgroup.normalizer (PJ : Set J)).map eJ.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨cJ, hcJNorm, rfl⟩
      rw [Subgroup.map_equiv_normalizer_eq] at hmap
      simpa [cJ, Q] using hmap
    have hQcent : Q ≤ Subgroup.centralizer ({t0} : Set (PSL2 K)) :=
      psl2_invariant_oddP_subgroup_centralized
        hKcard hrodd hpodd Q hQp ht0 hQinv
    intro x hxP
    rw [Subgroup.mem_centralizer_singleton_iff]
    let xJ : J := ⟨x, hPJ hxP⟩
    have hxQ : eJ xJ ∈ Q :=
      Subgroup.mem_map.mpr ⟨xJ, hxP, rfl⟩
    have hxcomm : eJ xJ * t0 = t0 * eJ xJ :=
      Subgroup.mem_centralizer_singleton_iff.mp (hQcent hxQ)
    have hxcommJ : xJ * tJ = tJ * xJ := by
      apply eJ.injective
      simpa [t0] using hxcomm
    exact congrArg Subtype.val hxcommJ
  · obtain ⟨U, s, w, _w2, hUcyc, hUodd, hUorder, hsU, hsJ, hsne, hssq,
      hwJ, hwU, hwsq, hwinv, _htrel, _hwU2, _hwsq2, _hwinv2, _hcent⟩ :=
      pgl2_low_two_part_torus_reflection_data K hK' hcard
    have hsI : IsInvolution s := ⟨hsne, by simpa [pow_two] using hssq⟩
    have hconj : IsConj t s :=
      pgl2_outer_involutions_conjugate K hK' hcard ht hsI htJ hsJ
    obtain ⟨g, hgt⟩ := isConj_iff.mp hconj
    let e : PGL2 K ≃* PGL2 K := MulAut.conj g
    let P0 : Subgroup (PGL2 K) := P.map e.toMonoidHom
    have hP0p : IsPGroup p P0 := IsPGroup.map hPp e.toMonoidHom
    have hP0odd : Odd (Nat.card P0) := by
      rcases hP0p.exists_card_eq with ⟨a, ha⟩
      rw [ha]
      exact hpodd.pow
    have hP0J : P0 ≤ J :=
      odd_card_subgroup_le_normal_index_two J P0 (by infer_instance)
        hJindex hP0odd
    have hP0inv : Subgroup.centralizer ({s} : Set (PGL2 K)) ≤
        Subgroup.normalizer (P0 : Set (PGL2 K)) :=
      centralizer_le_normalizer_map_conj_of_eq_conj P hgt hPinv
    have hUtwo : Nat.card U = 2 * (Nat.card U / 2) := by
      rcases hUorder with hsub | hadd
      · rw [hsub]
        rcases hqOdd with ⟨a, ha⟩
        omega
      · rw [hadd]
        rcases hqOdd with ⟨a, ha⟩
        omega
    obtain ⟨D, hDeq, hDJ, hRDindex, hDcard, hDdih⟩ :=
      exists_dihedral_subgroup_le_index_two_of_reflected_cyclic
        J U hJindex hUcyc (Nat.card U / 2) hUtwo
          (fun hUJ => hsJ (hUJ hsU)) w hwJ hwU hwsq hwinv
    let : IsCyclic U := hUcyc
    let : CommGroup U := IsCyclic.commGroup
    have hDcent : D ≤ Subgroup.centralizer ({s} : Set (PGL2 K)) := by
      rw [hDeq]
      apply sup_le
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val
          (mul_comm (⟨x, hx.1⟩ : U) (⟨s, hsU⟩ : U))
      · apply Subgroup.zpowers_le.mpr
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hssq
        calc
          w * s = (w * s * w⁻¹) * w := by group
          _ = s⁻¹ * w := by rw [hwinv s hsU]
          _ = s * w := by rw [hsinv]
    let M : Subgroup (PGL2 K) :=
      Subgroup.normalizer (P0 : Set (PGL2 K)) ⊓ J
    have hDM : D ≤ M := by
      exact fun x hx => ⟨hP0inv (hDcent hx), hDJ hx⟩
    have hP0M : P0 ≤ M := by
      exact fun x hx => ⟨Subgroup.le_normalizer hx, hP0J hx⟩
    let DJ : Subgroup J := D.subgroupOf J
    let MJ : Subgroup J := M.subgroupOf J
    let P0J : Subgroup J := P0.subgroupOf J
    let D0 : Subgroup (PSL2 K) := DJ.map eJ.toMonoidHom
    let M0 : Subgroup (PSL2 K) := MJ.map eJ.toMonoidHom
    let Q0 : Subgroup (PSL2 K) := P0J.map eJ.toMonoidHom
    have hDJMJ : DJ ≤ MJ := by
      intro x hx
      exact hDM hx
    have hP0JMJ : P0J ≤ MJ := by
      intro x hx
      exact hP0M hx
    have hD0M0 : D0 ≤ M0 := Subgroup.map_mono hDJMJ
    have hQ0M0 : Q0 ≤ M0 := Subgroup.map_mono hP0JMJ
    have hP0Jp : IsPGroup p P0J :=
      hP0p.of_equiv (Subgroup.subgroupOfEquivOfLe hP0J).symm
    have hQ0p : IsPGroup p Q0 := IsPGroup.map hP0Jp eJ.toMonoidHom
    have hMJNormP0J : MJ ≤ Subgroup.normalizer (P0J : Set J) := by
      intro x hx
      have hxM : (x : PGL2 K) ∈ M := hx
      have hxNorm : (x : PGL2 K) ∈
          Subgroup.normalizer (P0 : Set (PGL2 K)) := hxM.1
      rw [Subgroup.mem_normalizer_iff]
      intro y
      change ((y : PGL2 K) ∈ P0 ↔
        (x : PGL2 K) * (y : PGL2 K) * (x : PGL2 K)⁻¹ ∈ P0)
      exact (Subgroup.mem_normalizer_iff.mp hxNorm) (y : PGL2 K)
    have hM0NormQ0 : M0 ≤ Subgroup.normalizer (Q0 : Set (PSL2 K)) := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨xJ, hxMJ, rfl⟩
      have hxN := hMJNormP0J hxMJ
      have hmap : eJ xJ ∈
          (Subgroup.normalizer (P0J : Set J)).map eJ.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨xJ, hxN, rfl⟩
      rw [Subgroup.map_equiv_normalizer_eq] at hmap
      exact hmap
    have hQ0normal : (Q0.subgroupOf M0).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0M0).mpr hM0NormQ0
    let eDJ : DJ ≃* D0 :=
      Subgroup.equivMapOfInjective DJ eJ.toMonoidHom eJ.injective
    let eD : D ≃* D0 :=
      (Subgroup.subgroupOfEquivOfLe hDJ).symm.trans eDJ
    have hD0card : Nat.card D0 = 2 * (Nat.card U / 2) := by
      calc
        Nat.card D0 = Nat.card D := Nat.card_congr eD.toEquiv.symm
        _ = Nat.card U := hDcard
        _ = 2 * (Nat.card U / 2) := hUtwo
    have hD0order : Nat.card D0 = Nat.card K - 1 ∨
        Nat.card D0 = Nat.card K + 1 := by
      rw [show Nat.card D0 = Nat.card U by
        calc
          Nat.card D0 = Nat.card D := Nat.card_congr eD.toEquiv.symm
          _ = Nat.card U := hDcard]
      exact hUorder
    have hD0dih : Nonempty (D0 ≃* DihedralGroup (Nat.card U / 2)) :=
      ⟨eD.symm.trans hDdih.some⟩
    have hP0cent : P0 ≤
        Subgroup.centralizer ({s} : Set (PGL2 K)) := by
      rcases psl2_normal_oddP_eq_bot_or_eq_low_dihedral_overgroup
          hKcard hrodd hpodd hcard hUodd D0 M0 Q0 hD0card hD0order
            hD0dih hD0M0 hQ0M0 hQ0normal hQ0p with hQ0bot | hM0D0
      · have hP0bot : P0 = ⊥ := by
          apply le_bot_iff.mp
          intro x hxP0
          let xJ : J := ⟨x, hP0J hxP0⟩
          have hxQ : eJ xJ ∈ Q0 :=
            Subgroup.mem_map.mpr ⟨xJ, hxP0, rfl⟩
          rw [hQ0bot] at hxQ
          have hxone : eJ xJ = 1 := Subgroup.mem_bot.mp hxQ
          have hxJone : xJ = 1 := eJ.injective (by simpa using hxone)
          exact congrArg Subtype.val hxJone
        intro x hx
        have hxone : x = 1 := by
          rw [hP0bot] at hx
          exact Subgroup.mem_bot.mp hx
        rw [Subgroup.mem_centralizer_singleton_iff, hxone]
        simp
      · have hMD : M = D := by
          apply le_antisymm
          · intro x hxM
            let xJ : J := ⟨x, hxM.2⟩
            have hxM0 : eJ xJ ∈ M0 :=
              Subgroup.mem_map.mpr ⟨xJ, hxM, rfl⟩
            rw [hM0D0] at hxM0
            rcases Subgroup.mem_map.mp hxM0 with ⟨dJ, hdD, hdx⟩
            have hxd : xJ = dJ := eJ.injective hdx.symm
            change (xJ : PGL2 K) ∈ D
            rw [hxd]
            exact hdD
          · exact hDM
        have hP0D : P0 ≤ D := by simpa [hMD] using hP0M
        let RD : Subgroup D := (U ⊓ J).subgroupOf D
        let PD : Subgroup D := P0.subgroupOf D
        have hPDodd : Odd (Nat.card PD) := by
          rw [show Nat.card PD = Nat.card P0 by
            exact Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe hP0D).toEquiv]
          exact hP0odd
        have hRDnormal : RD.Normal :=
          Subgroup.normal_of_index_eq_two (by simpa [RD] using hRDindex)
        have hPDRD : PD ≤ RD :=
          odd_card_subgroup_le_normal_index_two RD PD hRDnormal
            (by simpa [RD] using hRDindex) hPDodd
        have hP0U : P0 ≤ U := by
          intro x hxP0
          let xD : D := ⟨x, hP0D hxP0⟩
          have hxPD : xD ∈ PD := hxP0
          have hxRD := hPDRD hxPD
          exact hxRD.1
        intro x hxP0
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val
          (mul_comm (⟨x, hP0U hxP0⟩ : U) (⟨s, hsU⟩ : U))
    intro x hxP
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxP0 : e x ∈ P0 := Subgroup.mem_map.mpr ⟨x, hxP, rfl⟩
    have hxcomm : e x * s = s * e x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hP0cent hxP0)
    apply e.injective
    simpa [map_mul, e, hgt] using hxcomm

end CFSG.GorensteinWalter
