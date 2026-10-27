module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoInnerQ

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

private noncomputable def centerQuotientEquiv {L : Type*} [Group L]
    (hZ : Subgroup.center L = ⊥) : L ≃* L ⧸ Subgroup.center L :=
  (QuotientGroup.quotientBot (G := L)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (G := L) hZ.symm)

private theorem centerQuotientEquiv_apply {L : Type*} [Group L]
    (hZ : Subgroup.center L = ⊥) (l : L) :
    centerQuotientEquiv hZ l = QuotientGroup.mk l := by
  simp [centerQuotientEquiv]

private theorem isPerfect_psuSix (hK : Nat.card K = 4) :
    Group.IsPerfect (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := 1) hK' (n := 6)
      (by norm_num) (by norm_num)
  exact Group.IsPerfect.ofSurjective
    (f := LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (QuotientGroup.mk'_surjective _)

theorem card_inf_eq_and_exists_map_eq_torU (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ : Subgroup.center L = ⊥) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hx : x ∈ Bs) (hx1 : x ≠ 1) (hLx : L ≤ Subgroup.centralizer {x})
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) :
    Nat.card ↥(Bs ⊓ L) = 3 ^ 4 ∧
      ∃ φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)),
        ((Bs ⊓ L).subgroupOf L).map φ.toMonoidHom = USixTwo.torU K := by
  let φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    (centerQuotientEquiv hZ).trans θ
  have hperf : commutator ↥L = ⊤ := by
    haveI : Group.IsPerfect (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
      isPerfect_psuSix hK
    haveI : Group.IsPerfect ↥L := Group.IsPerfect.ofSurjective
      (f := φ.symm.toMonoidHom) φ.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hZ2 : IsPGroup 2 (Subgroup.center L) := hZ ▸ IsPGroup.of_bot
  obtain ⟨hcardinf, θ', hθ'⟩ := card_inf_eq_and_exists_map_eq_torU_of_isPGroup hK θ hperf hZ2
    hBs hcard hx hx1 hBL hstar hNL hI
  refine ⟨hcardinf, (centerQuotientEquiv hZ).trans θ', ?_⟩
  have hcomp : ((centerQuotientEquiv hZ).trans θ').toMonoidHom =
      θ'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)) := by
    ext l
    simp [centerQuotientEquiv_apply]
  rw [hcomp]
  exact hθ'

end CFSG.StandardType.E6QTwo

end
