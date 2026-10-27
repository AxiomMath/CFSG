module

public import CFSG.Quasithin.Background.Harris.Alt6.SpGroup
public import CFSG.Quasithin.Background.Sp4InfField
public import CFSG.Quasithin.Background.P4InspSpA6

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G11.Harris.Alt6

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspSp CFSG.Assembly.LowTwoRank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem commutator_le_self_of {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

@[expose] noncomputable def zmod2Equiv : ZMod 2 ≃ₐ[ZMod 2] GaloisField 2 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine AlgEquiv.ofBijective (Algebra.ofId (ZMod 2) (GaloisField 2 1)) ?_
  have hc : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 (by norm_num)
  have : Finite (GaloisField 2 1) := inferInstance
  refine (algebraMap (ZMod 2) (GaloisField 2 1)).injective.bijective_of_nat_card_le ?_
  rw [hc, Nat.card_zmod]; norm_num

theorem isNatural_of_symplectic [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} (h : IsSymplectic B)
    (hd : Module.finrank (ZMod 2) V = 4) {L : Subgroup (GLV V)} (hL : L = ⁅spSub B, spSub B⁆) :
    IsNaturalMatrixModule L ⁅StatedSp 2 (GaloisField 2 1), StatedSp 2 (GaloisField 2 1)⁆ := by
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨m, b, hm, hb⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis B h.1
      (p4inspsp_nondeg h)
  obtain rfl : m = 2 := by omega
  let r : ZMod 2 ≃+* GaloisField 2 1 := zmod2Equiv.toRingEquiv
  let c1 : ↥(spSub B) ≃* ↥(StatedSp 2 (ZMod 2)) :=
    ((MulEquiv.subgroupCongr (p4inspsp_spSub_eq B)).trans
      (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryMatrixEquiv b B hb)).trans
      (MulEquiv.subgroupCongr (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic
        (n := 2) (K := ZMod 2)).symm)
  let c2 := c1.trans (Sp4Inf.mapSp r)
  obtain ⟨φ, hφ⟩ := exists_commutator_equiv c2 hL
  let ψ : V ≃ₗ[ZMod 2] (Fin 2 ⊕ Fin 2 → GaloisField 2 1) :=
    b.equivFun.trans (LinearEquiv.piCongrRight fun _ => zmod2Equiv.toLinearEquiv)
  refine ⟨φ, ψ, fun l v => ?_⟩
  have hl : (l : GLV V) ∈ spSub B := (hL ▸ commutator_le_self_of (spSub B)) l.2
  have h1 := hφ l hl
  have h2 : (((c2 ⟨l, hl⟩ : ↥(StatedSp 2 (GaloisField 2 1))) :
      GL (Fin 2 ⊕ Fin 2) (GaloisField 2 1)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
        (GaloisField 2 1)) =
      (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv b
        (l : GLV V)).val.map r := rfl
  rw [show ((φ l : ↥⁅StatedSp 2 (GaloisField 2 1), StatedSp 2 (GaloisField 2 1)⁆) :
      GL (Fin 2 ⊕ Fin 2) (GaloisField 2 1)) = ((c2 ⟨l, hl⟩ : ↥(StatedSp 2 (GaloisField 2 1))) :
      GL (Fin 2 ⊕ Fin 2) (GaloisField 2 1)) from h1, h2]
  have h3 := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec b
    (l : GLV V) v
  funext i
  show r (b.equivFun ((l : GLV V) v) i) = _
  rw [← h3]
  exact (RingHom.map_mulVec r.toRingHom _ _ i)

theorem permCore_of_symplectic [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} (h : IsSymplectic B)
    (hd : Module.finrank (ZMod 2) V = 4) {L : Subgroup (GLV V)} (hL : L ≤ spSub B)
    (hirr : IsIrr L ⊤) (hperf : Group.IsPerfect ↥L) (hcard : Nat.card L = 360) :
    IsPermCoreModule L (alternatingGroup (Fin 6)) := by
  obtain ⟨-, hnorm⟩ := eq_commutator_spSub h hd hL (Subgroup.isPerfect_iff.1 hperf) hcard
  exact (p4inspsp_a6_case h hd (M := spSub B) (K := L) (commutator_le_self_of _) le_rfl hL hnorm
    hirr hperf).2

end CFSG.Quasithin.G11.Harris.Alt6
