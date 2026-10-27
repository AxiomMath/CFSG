module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DicksonNormalOddPReduction
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupAlternating
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupAlternatingFour
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupPGL2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupPSL2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupSymmetricFour
import Mathlib.GroupTheory.Complement
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Dickson overgroups of a low-order dihedral subgroup

A subgroup of odd `PSL₂` which contains a dihedral subgroup of order
`q - 1` or `q + 1`, with the latter written as twice its rotation parameter,
has very few Dickson alternatives.  A normal odd-prime subgroup is trivial
unless the overgroup is exactly that supplied dihedral subgroup.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

open BenderSuzuki.MatrixGroups

universe u

/-- A normal odd-prime subgroup in an overgroup of a low-order dihedral
subgroup of odd `PSL₂(F)` is trivial unless the overgroup equals that
dihedral subgroup. -/
public theorem psl2_normal_oddP_eq_bot_or_eq_low_dihedral_overgroup
    {F : Type u} [Field F] [Finite F]
    {r f p m : ℕ} [Fact r.Prime] [Fact p.Prime]
    (hFcard : Nat.card F = r ^ f) (hrodd : Odd r)
    (hpodd : Odd p) (hcard : 3 < Nat.card F) (_hmOdd : Odd m)
    (D M P : Subgroup (PSL2MatrixGroup F))
    (hDcard : Nat.card D = 2 * m)
    (hDorder : Nat.card D = Nat.card F - 1 ∨
      Nat.card D = Nat.card F + 1)
    (hDdihedral : Nonempty (D ≃* DihedralGroup m))
    (hDM : D ≤ M) (hPM : P ≤ M)
    (hPnormal : (P.subgroupOf M).Normal) (hPp : IsPGroup p P) :
    P = ⊥ ∨ M = D := by
  classical
  have hf_ne_zero : f ≠ 0 := by
    intro hf_zero
    have hcard_one : Nat.card F = 1 := by
      simpa [hf_zero, pow_zero] using hFcard
    exact (Nat.ne_of_gt (Finite.one_lt_card (α := F))) hcard_one
  have hqOdd : Odd (Nat.card F) := by
    rw [hFcard]
    exact hrodd.pow
  have hm_ne_one : m ≠ 1 := by
    intro hm
    subst m
    rcases hDorder with hsub | hadd
    · rw [hDcard] at hsub
      omega
    · rw [hDcard] at hadd
      omega
  have hDnotcyclic : ¬ IsCyclic D := by
    intro hDcyclic
    have hmodelcyclic : IsCyclic (DihedralGroup m) :=
      hDdihedral.some.isCyclic.mp hDcyclic
    exact DihedralGroup.not_isCyclic hm_ne_one hmodelcyclic
  have hr_dvd_q : r ∣ Nat.card F := by
    rw [hFcard]
    exact dvd_pow_self r hf_ne_zero
  have hDcoprime_r : Nat.Coprime (Nat.card D) r := by
    rcases hDorder with hsub | hadd
    · rw [hsub]
      have hcop : Nat.Coprime (Nat.card F - 1) (Nat.card F) := by
        exact ((Nat.coprime_self_sub_right
          (by omega : 1 ≤ Nat.card F)).mpr
            (Nat.coprime_one_right _)).symm
      exact hcop.of_dvd_right hr_dvd_q
    · rw [hadd]
      have hcop : Nat.Coprime (Nat.card F + 1) (Nat.card F) := by
        exact ((Nat.coprime_self_add_right).mpr
          (Nat.coprime_one_right _)).symm
      exact hcop.of_dvd_right hr_dvd_q
  let PM : Subgroup M := P.subgroupOf M
  have hPMp : IsPGroup p PM :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
  have hPbot_of_PMbot : PM = ⊥ → P = ⊥ := by
    intro hPMbot
    apply le_bot_iff.mp
    intro x hx
    have hxPM : (⟨x, hPM hx⟩ : M) ∈ PM :=
      Subgroup.mem_subgroupOf.mpr hx
    have hxone : (⟨x, hPM hx⟩ : M) = 1 := by
      rw [hPMbot] at hxPM
      exact Subgroup.mem_bot.mp hxPM
    exact congrArg Subtype.val hxone
  rcases
      Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
        (p := r) (f := f) hFcard M with
    hElementary | hCyclic | hDihedral | hA4 | hS4 | hA5 |
      hSemidirect | hPSL | hPGL
  · exfalso
    have hMr : IsPGroup r M := IsElementaryAbelian.isPGroup r M
    let DM : Subgroup M := D.subgroupOf M
    have hDMr : IsPGroup r DM := hMr.to_subgroup DM
    have hDr : IsPGroup r D :=
      hDMr.of_equiv (Subgroup.subgroupOfEquivOfLe hDM)
    have hDodd : Odd (Nat.card D) := by
      rcases hDr.exists_card_eq with ⟨a, ha⟩
      rw [ha]
      exact hrodd.pow
    apply hDodd.not_two_dvd_nat
    rw [hDcard]
    exact ⟨m, by omega⟩
  · exfalso
    rcases hCyclic with ⟨_z, _hz, _hcard, hMcyclic⟩
    let : IsCyclic M := hMcyclic
    exact hDnotcyclic (Subgroup.isCyclic_of_le hDM)
  · right
    rcases hDihedral with ⟨z, hzdiv, hMcard, _hMequiv⟩
    have hDdvdM : Nat.card D ∣ Nat.card M :=
      Subgroup.card_dvd_of_le hDM
    have hm_dvd_z : m ∣ z := by
      rw [hDcard, hMcard] at hDdvdM
      exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).mp hDdvdM
    have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
      have htwo : 2 ∣ Nat.card F - 1 := by
        rcases hqOdd with ⟨a, ha⟩
        use a
        omega
      exact Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
        (Nat.dvd_gcd htwo (dvd_refl 2))
    rw [hgcd] at hzdiv
    have hz_eq : z = m := by
      rcases hDorder with hsub | hadd
      · have hhalf_sub : (Nat.card F - 1) / 2 = m := by
          rw [hDcard] at hsub
          omega
        have hhalf_add : (Nat.card F + 1) / 2 = m + 1 := by
          rw [hDcard] at hsub
          omega
        rcases hzdiv with hz | hz
        · rw [hhalf_sub] at hz
          exact Nat.dvd_antisymm hz hm_dvd_z
        · rw [hhalf_add] at hz
          exfalso
          have hm_one : m ∣ 1 := by
            apply (Nat.dvd_add_iff_right (dvd_refl m)).mpr
            simpa [add_comm] using hm_dvd_z.trans hz
          exact hm_ne_one (Nat.eq_one_of_dvd_one hm_one)
      · have hhalf_add : (Nat.card F + 1) / 2 = m := by
          rw [hDcard] at hadd
          omega
        have hhalf_sub : (Nat.card F - 1) / 2 = m - 1 := by
          rw [hDcard] at hadd
          omega
        rcases hzdiv with hz | hz
        · rw [hhalf_sub] at hz
          exfalso
          have hle : m ≤ m - 1 :=
            Nat.le_of_dvd (by omega : 0 < m - 1) (hm_dvd_z.trans hz)
          omega
        · rw [hhalf_add] at hz
          exact Nat.dvd_antisymm hz hm_dvd_z
    exact (Subgroup.eq_of_le_of_card_ge hDM (by
      rw [hMcard, hz_eq, hDcard])).symm
  · left
    have hPMbot : PM = ⊥ :=
      normal_pSubgroup_eq_bot_of_mulEquiv_alternatingGroup_four
        hA4.2 p Fact.out hpodd PM hPnormal hPMp
    exact hPbot_of_PMbot hPMbot
  · left
    have hPMbot : PM = ⊥ :=
      normal_pSubgroup_eq_bot_of_mulEquiv_perm_four
        hS4.2 p Fact.out hpodd PM hPnormal hPMp
    exact hPbot_of_PMbot hPMbot
  · left
    have hPMbot : PM = ⊥ :=
      normal_pSubgroup_eq_bot_of_mulEquiv_alternatingGroup
        (n := 5) (by norm_num) hA5.2 p Fact.out hpodd PM hPnormal hPMp
    exact hPbot_of_PMbot hPMbot
  · exfalso
    rcases hSemidirect with
      ⟨a, ccard, _hccard_dvd, _hccard_ambient, N, C,
        hNnormal, hNelem, hNcard, hCcyc, _hCcard, hdisj, hjoin⟩
    let : N.Normal := hNnormal
    have hcomp : N.IsComplement' C := by
      refine ⟨Subgroup.mul_injective_of_disjoint hdisj, ?_⟩
      intro g
      have hg : (g : M) ∈ (N : Set M) * (C : Set M) := by
        rw [← Subgroup.normal_mul N C, hjoin]
        trivial
      rcases hg with ⟨n, hn, c, hc, hnc⟩
      exact ⟨⟨⟨n, hn⟩, ⟨c, hc⟩⟩, hnc⟩
    let eQ : M ⧸ N ≃* C := hcomp.symm.QuotientMulEquiv
    let : IsCyclic (M ⧸ N) := eQ.isCyclic.mpr hCcyc
    let DM : Subgroup M := D.subgroupOf M
    have hDMcard : Nat.card DM = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM)
    have hcoprime : Nat.Coprime (Nat.card DM) (Nat.card N) := by
      rw [hDMcard, hNcard]
      exact hDcoprime_r.pow_right a
    have hinf : DM ⊓ N = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard hcoprime).eq_bot
    let q : M →* M ⧸ N := QuotientGroup.mk' N
    let qD : DM →* M ⧸ N := q.comp DM.subtype
    have hqDker : qD.ker = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hxq : q (x : M) = 1 := by
        simpa [qD] using hx
      have hxN : (x : M) ∈ N :=
        (QuotientGroup.eq_one_iff (N := N) (x : M)).mp hxq
      have hxinf : (x : M) ∈ DM ⊓ N := ⟨x.property, hxN⟩
      have hxone : (x : M) = 1 := by
        have hxbot : (x : M) ∈ (⊥ : Subgroup M) := by
          rw [← hinf]
          exact hxinf
        exact Subgroup.mem_bot.mp hxbot
      exact Subtype.ext hxone
    have hqDinj : Function.Injective qD :=
      (MonoidHom.ker_eq_bot_iff qD).mp hqDker
    have hDMcyclic : IsCyclic DM := isCyclic_of_injective qD hqDinj
    have hDcyclic : IsCyclic D :=
      (Subgroup.subgroupOfEquivOfLe hDM).isCyclic.mp hDMcyclic
    exact hDnotcyclic hDcyclic
  · left
    rcases hPSL with ⟨a, ha, _hadiv, ⟨eM⟩⟩
    let K := GaloisField r a
    have hKcard : Nat.card K = r ^ a := GaloisField.card r a ha
    have hKodd : IsOddPrimePower (Nat.card K) :=
      ⟨r, a, Fact.out, hrodd, Nat.one_le_iff_ne_zero.mpr ha, hKcard⟩
    let Q : Subgroup (PSL2 K) := PM.map eM.toMonoidHom
    have hQnormal : Q.Normal := hPnormal.map eM.toMonoidHom eM.surjective
    have hQp : IsPGroup p Q := IsPGroup.map hPMp eM.toMonoidHom
    have hQbot : Q = ⊥ :=
      normal_pSubgroup_eq_bot_of_psl2_odd
        K hKodd p Fact.out hpodd Q hQnormal hQp
    have hPMbot : PM = ⊥ := by
      apply (Subgroup.map_eq_bot_iff_of_injective
        (H := PM) (f := eM.toMonoidHom) eM.injective).mp
      simpa [Q] using hQbot
    exact hPbot_of_PMbot hPMbot
  · left
    rcases hPGL with ⟨a, ha, _hadiv, ⟨eM⟩⟩
    let K := GaloisField r a
    have hKcard : Nat.card K = r ^ a := GaloisField.card r a ha
    have hKodd : IsOddPrimePower (Nat.card K) :=
      ⟨r, a, Fact.out, hrodd, Nat.one_le_iff_ne_zero.mpr ha, hKcard⟩
    let Q : Subgroup (PGL2 K) := PM.map eM.toMonoidHom
    have hQnormal : Q.Normal := hPnormal.map eM.toMonoidHom eM.surjective
    have hQp : IsPGroup p Q := IsPGroup.map hPMp eM.toMonoidHom
    have hQbot : Q = ⊥ :=
      normal_pSubgroup_eq_bot_of_pgl2_odd
        K hKodd p Fact.out hpodd Q hQnormal hQp
    have hPMbot : PM = ⊥ := by
      apply (Subgroup.map_eq_bot_iff_of_injective
        (H := PM) (f := eM.toMonoidHom) eM.injective).mp
      simpa [Q] using hQbot
    exact hPbot_of_PMbot hPMbot

end CFSG.GorensteinWalter
