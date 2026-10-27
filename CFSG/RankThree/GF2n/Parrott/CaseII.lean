module

public import CFSG.RankThree.GF2n.Parrott.Section3Lift
public import CFSG.RankThree.GF2n.Parrott.Section1Extraspecial
public import CFSG.RankThree.GF2n.Parrott.Section3Commutator
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.GroupTheory.ExtraspecialOrderEight
public import CFSG.GroupTheory.Extraspecial2PG
public import CFSG.LinearAlgebra.F2OrderNineFixed
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.RankThree.GF2n.Parrott.CommutatorExtraspecial
public import CFSG.RankThree.GF2n.Parrott.FixDimBound

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

structure QuotientDataPSp (z : G) (hN : ((J z).subgroupOf (H z)).Normal) : Type 1 where
  X : Type
  instX : Group X
  lie : CFSG.Blueprint.LieModel X .PSp 2 3 1
  iso : letI := hN; (↥(H z) ⧸ (J z).subgroupOf (H z)) ≃* X

attribute [instance] QuotientDataPSp.instX

namespace QuotientDataPSp

noncomputable def toQP45
    {hN : ((J z).subgroupOf (H z)).Normal} (D : QuotientDataPSp z hN) :
    letI := hN; (↥(H z) ⧸ (J z).subgroupOf (H z)) ≃* QP45.originalSubgroup := by
  letI := hN
  exact D.iso.trans (Classical.choice (equiv_of_lieModel D.lie))

end QuotientDataPSp

end CFSG.RankThree.GF2n.Parrott

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.RankThree.GF2n.Parrott

structure ParrottHypA {G : Type} [Group G] [Finite G] (z : G) : Prop where
  extraspecial : CFSG.LargeExtraspecial.Timmesfeld.IsExtraspecial2 (Parrott.J z)
  card_J : Nat.card (Parrott.J z) = 2 ^ 9
  commutator : ⁅Parrott.J z, Parrott.J z⁆ = Subgroup.zpowers z
  centralizer_le : Parrott.H z ⊓ Subgroup.centralizer (Parrott.J z : Set G) ≤ Parrott.J z
  quotient : Nonempty (Parrott.QuotientData z (Parrott.J_subgroupOf_normal z))

structure ParrottHypA1 {G : Type} [Group G] [Finite G] (z : G) : Prop where
  extraspecial : CFSG.LargeExtraspecial.Timmesfeld.IsExtraspecial2 (Parrott.J z)
  card_J : Nat.card (Parrott.J z) = 2 ^ 9
  commutator : ⁅Parrott.J z, Parrott.J z⁆ = Subgroup.zpowers z
  centralizer_le : Parrott.H z ⊓ Subgroup.centralizer (Parrott.J z : Set G) ≤ Parrott.J z
  quotient : Nonempty (Parrott.QuotientDataPSp z (Parrott.J_subgroupOf_normal z))

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

noncomputable def quotientDataA (h : Tim79a.ParrottHypA z) :
    QuotientData (z := z) (J_subgroupOf_normal z) :=
  Classical.choice h.quotient

theorem card_J_A (h : Tim79a.ParrottHypA z) : Nat.card (J z) = 2 ^ 9 := h.card_J

noncomputable def quotientDataA1 (h : Tim79a.ParrottHypA1 z) :
    QuotientDataPSp (z := z) (J_subgroupOf_normal z) :=
  Classical.choice h.quotient

theorem z_mem_J_A (h : Tim79a.ParrottHypA z) : z ∈ J z := by
  have hz : z ∈ ⁅J z, J z⁆ := by
    rw [h.commutator]
    exact Subgroup.mem_zpowers z
  exact Subgroup.commutator_le_self (J z) hz

omit [Finite G] in
theorem z_centralizes_H_A : z ∈ Subgroup.centralizer (H z : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact Subgroup.mem_centralizer_singleton_iff.mp (by simpa [H] using hg)

theorem z_centralizes_J_A : z ∈ Subgroup.centralizer (J z : Set G) :=
  Subgroup.centralizer_le (J_le_H (z := z)) (z_centralizes_H_A (z := z))

theorem J_normal_A : ((J z).subgroupOf (H z)).Normal := J_subgroupOf_normal z

theorem J_le_normalizer_A : H z ≤ Subgroup.normalizer (J z : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp
    (J_normal_A (z := z))

theorem isPGroup_J_A (h : Tim79a.ParrottHypA z) : IsPGroup 2 (J z) :=
  IsPGroup.of_card (n := 9) h.card_J

theorem centerIn_J_eq_zpowers_A (h : Tim79a.ParrottHypA z) :
    centerIn (J z) = Subgroup.zpowers z := by
  rw [CFSG.centerIn_eq_map_center, ← h.extraspecial.2.1, h.commutator]

theorem orderOf_z_A (h : Tim79a.ParrottHypA z) : orderOf z = 2 := by
  have hcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [← h.commutator]
    exact h.extraspecial.2.2
  rwa [Nat.card_zpowers] at hcard

theorem centralizer_J_eq_centerIn_A (h : Tim79a.ParrottHypA z) :
    H z ⊓ Subgroup.centralizer (J z : Set G) = centerIn (J z) := by
  apply le_antisymm
  · intro x hx
    exact ⟨h.centralizer_le hx, hx.2⟩
  · intro x hx
    exact ⟨J_le_H hx.1, hx.2⟩

@[expose] noncomputable def conjVA (z : G) : H z →* MulAut (QuotientV.V z) :=
  (MulAut.congr (QuotientGroup.quotientMulEquivOfEq
    (QuotientV.centerIn_subgroupOf_eq_center (z := z)).symm)).toMonoidHom.comp
    ((centerQuotientAutHom (J z)).comp (conjJ' z))

theorem conjVA_mk (g : H z) (x : J z) :
    conjVA z g (QuotientV.pi z x) = QuotientV.pi z (conjJ' z g x) := by
  let M : Subgroup (J z) := (centerIn (J z)).subgroupOf (J z)
  let N : Subgroup (J z) := Subgroup.center (J z)
  let e : (J z ⧸ N) ≃* (J z ⧸ M) :=
    QuotientGroup.quotientMulEquivOfEq (QuotientV.centerIn_subgroupOf_eq_center (z := z)).symm
  have hMN : N = M := (QuotientV.centerIn_subgroupOf_eq_center (z := z)).symm
  have hsymm : e.symm (QuotientGroup.mk' M x) = QuotientGroup.mk' N x := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact (QuotientGroup.quotientMulEquivOfEq_mk hMN x).symm
  change e (quotientAut (conjJ' z g) (e.symm (QuotientGroup.mk' M x))) =
    QuotientGroup.mk' M (conjJ' z g x)
  rw [hsymm, quotientAut_mk]
  exact QuotientGroup.quotientMulEquivOfEq_mk hMN (conjJ' z g x)

theorem conjVA_eq_congr (x : H z) :
    conjVA z x = MulAut.congr
      (QuotientGroup.quotientMulEquivOfEq
        (QuotientV.centerIn_subgroupOf_eq_center (z := z)).symm)
      (quotientAut (conjJ' z x)) := rfl

theorem isMulCommutative_V_A (h : Tim79a.ParrottHypA z) :
    IsMulCommutative (QuotientV.V z) := by
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
  intro x hx
  apply Subgroup.mem_subgroupOf.mpr
  have hz_center : z ∈ centerIn (J z) := ⟨z_mem_J_A h, z_centralizes_J_A (z := z)⟩
  have hzp : Subgroup.zpowers z ≤ centerIn (J z) := Subgroup.zpowers_le_of_mem hz_center
  have hx' : (x : G) ∈ ⁅J z, J z⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨x, hx, rfl⟩
  rw [h.commutator] at hx'
  exact hzp hx'

theorem pow_two_eq_one_V_A (h : Tim79a.ParrottHypA z) (v : QuotientV.V z) : v ^ 2 = 1 := by
  obtain ⟨j, rfl⟩ := QuotientV.pi_surjective z v
  have hj : ((j : J z) : G) * ((j : J z) : G) ∈ centerIn (J z) := by
    rw [CFSG.centerIn_eq_map_center]
    exact CFSG.IsExtraspecial2.mul_self_mem_center_map h.extraspecial j.2
  have hker : j * j ∈ (QuotientV.pi z).ker := by
    rw [QuotientV.pi_ker]
    exact Subgroup.mem_subgroupOf.mpr hj
  have hmap : QuotientV.pi z (j * j) = 1 := MonoidHom.mem_ker.mp hker
  simpa [pow_two, map_mul] using hmap

@[expose, reducible] noncomputable def commGroupV_A (h : Tim79a.ParrottHypA z) :
    CommGroup (QuotientV.V z) :=
  { (inferInstance : Group (QuotientV.V z)) with
    mul_comm := (isMulCommutative_V_A h).is_comm.comm }

@[reducible] noncomputable def moduleV_A (h : Tim79a.ParrottHypA z) :
    letI : CommGroup (QuotientV.V z) := commGroupV_A h
    Module (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV_A h
  AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero, ← pow_two]
    exact pow_two_eq_one_V_A h x.toMul

@[expose] noncomputable def conjVLinearMap_A (h : Tim79a.ParrottHypA z) (x : H z) :
    letI : CommGroup (QuotientV.V z) := commGroupV_A h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV_A h
    Additive (QuotientV.V z) →ₗ[ZMod 2] Additive (QuotientV.V z) :=
  letI : CommGroup (QuotientV.V z) := commGroupV_A h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV_A h
  (addAutLinearEquivMonoidHom
    (MulAut.congr (mulEquivVAdd (z := z)) (conjVA z x))).toLinearMap

@[simp] theorem conjVLinearMap_A_apply (h : Tim79a.ParrottHypA z) (x : H z)
    (v : Additive (QuotientV.V z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV_A h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV_A h
    conjVLinearMap_A h x v = Additive.ofMul ((conjVA z x) (Additive.toMul v)) := by
  letI : CommGroup (QuotientV.V z) := commGroupV_A h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV_A h
  rw [conjVLinearMap_A, addAutLinearEquivMonoidHom_toLinearMap, mulAutToLinearMap_apply]
  rfl

@[expose] noncomputable def fixSubmodule_A (h : Tim79a.ParrottHypA z) (x : H z) :
    letI : CommGroup (QuotientV.V z) := commGroupV_A h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV_A h
    Submodule (ZMod 2) (Additive (QuotientV.V z)) :=
  letI : CommGroup (QuotientV.V z) := commGroupV_A h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV_A h
  AddSubgroup.toZModSubmodule (n := 2)
    (Subgroup.toAddSubgroup (autFixedSubgroup (conjVA z x)))

@[simp] theorem mem_fixSubmodule_A_iff (h : Tim79a.ParrottHypA z) (x : H z)
    (v : Additive (QuotientV.V z)) :
    v ∈ fixSubmodule_A h x ↔ Additive.toMul v ∈ autFixedSubgroup (conjVA z x) := by
  letI : CommGroup (QuotientV.V z) := commGroupV_A h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV_A h
  rw [fixSubmodule_A, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup]

theorem autFixedSubgroup_quotientAut_map_eq_autFixedSubgroup_conjVA (x : H z) :
    (autFixedSubgroup (quotientAut (conjJ' z x))).map
        (QuotientGroup.quotientMulEquivOfEq
          (QuotientV.centerIn_subgroupOf_eq_center (z := z)).symm).toMonoidHom =
      autFixedSubgroup (conjVA z x) := by
  rw [conjVA_eq_congr]
  rw [autFixedSubgroup_congr]

theorem card_autFixedSubgroup_quotientAut_eq_card_autFixedSubgroup_conjVA (x : H z) :
    Nat.card (autFixedSubgroup (quotientAut (conjJ' z x))) =
      Nat.card (autFixedSubgroup (conjVA z x)) := by
  rw [← autFixedSubgroup_quotientAut_map_eq_autFixedSubgroup_conjVA (z := z) (x := x)]
  rw [Subgroup.card_map_of_injective]
  exact (QuotientGroup.quotientMulEquivOfEq
    (QuotientV.centerIn_subgroupOf_eq_center (z := z)).symm).injective

omit [Finite G] in
theorem commute_z_sigma_A (x : H z) : Commute z (x : G) := by
  have h := Subgroup.mem_centralizer_iff.mp (z_centralizes_H_A (z := z)) (x : G) x.2
  exact h.symm

theorem zpowers_sq_eq_one_A (h : Tim79a.ParrottHypA z) {c : G}
    (hc : c ∈ Subgroup.zpowers z) : c * c = 1 := by
  have hcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, orderOf_z_A h]
  have h1 : (⟨c, hc⟩ : Subgroup.zpowers z) ^ Nat.card (Subgroup.zpowers z) = 1 :=
    pow_card_eq_one'
  rw [hcard] at h1
  have := congrArg Subtype.val h1
  simpa [pow_two] using this

end CFSG.RankThree.GF2n.Parrott
