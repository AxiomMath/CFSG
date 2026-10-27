module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

@[expose] def Conc4_134 {W : Type} [CommGroup W] (A K : Subgroup (MulAut W)) (t : MulAut W) :
    Prop :=
  (((UC22.IsL3 ↥K 1 ∧ NatTensor (K ⊔ K.map (MulAut.conj t).toMonoidHom)
        (commSub ⊤ (K ⊔ K.map (MulAut.conj t).toMonoidHom)) ⊥ 3 1) ∨
      (UC22.IsL2 ↥K 2 ∧ NatTensor (K ⊔ K.map (MulAut.conj t).toMonoidHom)
        (commSub ⊤ (K ⊔ K.map (MulAut.conj t).toMonoidHom)) ⊥ 2 2) ∨
      (UC22.IsL2 ↥K 3 ∧ NatTensor (K ⊔ K.map (MulAut.conj t).toMonoidHom)
        (commSub ⊤ (K ⊔ K.map (MulAut.conj t).toMonoidHom)) ⊥ 2 3)) ∧
    ∀ g ∈ A, g ∉ normalizer ((K ⊔ K.map (MulAut.conj t).toMonoidHom : Subgroup (MulAut W)) :
        Set (MulAut W)) →
      commSub ((commSub ⊤ (K ⊔ K.map (MulAut.conj t).toMonoidHom)).map g.toMonoidHom)
        (K ⊔ K.map (MulAut.conj t).toMonoidHom) = ⊥) ∨
    (UC22.IsL3 ↥K 1 ∧ commSub ⊤ K ∈ irrSet K ∧
      (∀ g ∈ A, g ∉ normalizer (K : Set (MulAut W)) →
        commSub (commSub ⊤ K) (K.map (MulAut.conj g).toMonoidHom) = ⊥) ∧
      BinaryNaturalSL K (commSub ⊤ K) (commSub ⊤ K ⊓ fixV K) 3 1)

@[expose] def W4Lem13_4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y : Subgroup (MulAut W), CFSG.Open.IsKGroup ↥Y →
      (∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥) →
      ∀ t ∈ Y, orderOf t = 2 → rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 →
        ∀ K : Subgroup (MulAut W), IsComponentOf K Y →
          K.map (MulAut.conj t).toMonoidHom ≠ K → Conc4_134 Y K t

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
