module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralRotationIndexTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddSubgroupLeNormalIndexTwo
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralUniqueCentralInvolution

namespace CFSG
end CFSG
open CFSG

/-!
# Odd subgroups and the central involution of a large dihedral subgroup

Suppose a subgroup `M` has a finite dihedral model and contains a dihedral
`2`-subgroup `S` of order at least eight.  The central involution of `S` lies
in `S'`, hence in `M'` and in the cyclic rotation subgroup of `M`.  Every
odd-order subgroup of `M` also lies in that rotation subgroup, so the central
involution centralizes it.
-/

namespace CFSG.GorensteinWalter

universe u

/-- An odd-order subgroup of a dihedral subgroup is centralized by the
central involution of every contained dihedral `2`-subgroup of order at least
eight. -/
public theorem odd_subgroup_le_centralizer_of_large_dihedral_sylow_in_dihedral_subgroup
    {G : Type u} [Group G] [Finite G]
    (S M P : Subgroup G) {m z : ℕ}
    (hm : 2 ≤ m)
    (eS : S ≃* DihedralGroup (2 ^ m))
    (eM : M ≃* DihedralGroup z)
    (hMcard : Nat.card M = 2 * z)
    (hSM : S ≤ M) (hPM : P ≤ M)
    (hPodd : Odd (Nat.card P))
    {t : G} (htS : t ∈ S)
    (htcenter : (⟨t, htS⟩ : S) ∈ Subgroup.center S)
    (ht : IsInvolution t) :
    P ≤ Subgroup.centralizer ({t} : Set G) := by
  classical
  let tS : S := ⟨t, htS⟩
  have hetcenter : eS tS ∈
      Subgroup.center (DihedralGroup (2 ^ m)) :=
    MulEquivClass.apply_mem_center eS htcenter
  have hetpow : (eS tS) ^ 2 = 1 := by
    calc
      (eS tS) ^ 2 = eS (tS ^ 2) :=
        (eS.toMonoidHom.map_pow tS 2).symm
      _ = 1 := by
        rw [show tS ^ 2 = 1 by
          apply Subtype.ext
          exact ht.2]
        simp
  have hetne : eS tS ≠ 1 := by
    intro hone
    apply ht.1
    exact congrArg Subtype.val (eS.injective (by simpa using hone))
  have heteq : eS tS = DihedralGroup.r
      (2 ^ (m - 1) : ZMod (2 ^ m)) :=
    unique_central_involution_of_dihedral_two_pow
      hm (eS tS) hetcenter hetpow hetne
  have hetrotation : eS tS ∈ dihedralRotationSubgroup m 0 := by
    rw [heteq, dihedralRotationSubgroup_def]
    simpa [show (2 ^ 0 : ZMod (2 ^ m)) = 1 by norm_num] using
      (r_mem_zpowers_r_one (2 ^ (m - 1) : ZMod (2 ^ m)))
  have heteven : eS tS ∈ dihedralRotationSubgroup m 1 :=
    central_rotation_mem_even hm (eS tS) hetrotation hetcenter
  have htScomm : tS ∈ commutator S := by
    rw [commutator_eq_dihedral_even_rotations_comap S eS]
    exact heteven
  let iSM : S →* M := Subgroup.inclusion hSM
  let tM : M := ⟨t, hSM htS⟩
  have htMcomm : tM ∈ commutator M := by
    have htmap : iSM tS ∈ (commutator S).map iSM :=
      Subgroup.mem_map.mpr ⟨tS, htScomm, rfl⟩
    have hmaple : (commutator S).map iSM ≤ commutator M := by
      rw [map_commutator_eq]
      exact Subgroup.commutator_mono le_top le_top
    have hit : iSM tS = tM := Subtype.ext rfl
    rw [← hit]
    exact hmaple htmap
  have hz : z ≠ 0 := by
    intro hz0
    have hMpos : 0 < Nat.card M := Nat.card_pos
    rw [hMcard, hz0] at hMpos
    simp at hMpos
  let : NeZero z := ⟨hz⟩
  let RD : Subgroup (DihedralGroup z) :=
    Subgroup.zpowers (DihedralGroup.r 1)
  let RM : Subgroup M := RD.comap eM.toMonoidHom
  have hRMindex : RM.index = 2 := by
    calc
      RM.index = RD.index :=
        Subgroup.index_comap_of_surjective RD eM.surjective
      _ = 2 := dihedral_rotation_index_two
  have hRMnormal : RM.Normal :=
    Subgroup.normal_of_index_eq_two hRMindex
  have hcommle : commutator M ≤ RM :=
    commutator_le_of_normal_index_two RM hRMnormal hRMindex
  have htRM : tM ∈ RM := hcommle htMcomm
  let PM : Subgroup M := P.subgroupOf M
  have hPModd : Odd (Nat.card PM) := by
    have hcard : Nat.card PM = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv
    rwa [hcard]
  have hPMleRM : PM ≤ RM :=
    odd_card_subgroup_le_normal_index_two
      RM PM hRMnormal hRMindex hPModd
  intro x hxP
  let xM : M := ⟨x, hPM hxP⟩
  have hxPM : xM ∈ PM := Subgroup.mem_subgroupOf.mpr hxP
  have hxRM : xM ∈ RM := hPMleRM hxPM
  have htRD : eM tM ∈ RD := htRM
  have hxRD : eM xM ∈ RD := hxRM
  let tR : RD := ⟨eM tM, htRD⟩
  let xR : RD := ⟨eM xM, hxRD⟩
  let : IsCyclic RD := by
    dsimp [RD]
    infer_instance
  have hcommR : tR * xR = xR * tR := mul_comm' tR xR
  have hcommM : (tM : M) * xM = xM * tM := by
    apply eM.injective
    simpa [tR, xR] using congrArg Subtype.val hcommR
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyt : y = t := Set.mem_singleton_iff.mp hy
  subst y
  exact congrArg Subtype.val hcommM

end CFSG.GorensteinWalter
