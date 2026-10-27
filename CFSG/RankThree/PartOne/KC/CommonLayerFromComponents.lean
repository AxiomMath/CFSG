module

public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOneModel

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KCOrthogonalD4 CFSG.RankThree.PartOne.KCOrthogonalModel
  CFSG.ComponentClassification

theorem isComponent_subgroupOf_of_normal_le {M : Type*} [Group M] {H D : Subgroup M} [H.Normal]
    (hHD : H ≤ D) (a : M) {L : Subgroup M}
    (hL : L ≤ H ⊓ Subgroup.centralizer ({a} : Set M))
    (hc : IsComponent (L.subgroupOf (H ⊓ Subgroup.centralizer ({a} : Set M)))) :
    IsComponent (L.subgroupOf (D ⊓ Subgroup.centralizer ({a} : Set M))) := by
  set X : Subgroup M := H ⊓ Subgroup.centralizer ({a} : Set M) with hX
  set Y : Subgroup M := D ⊓ Subgroup.centralizer ({a} : Set M) with hY
  have hXY : X ≤ Y := inf_le_inf_right _ hHD
  have hnorm : (X.subgroupOf Y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : M) ∈ X := hn
    have hg : (g : M) ∈ Subgroup.centralizer ({a} : Set M) := g.2.2
    exact ⟨Subgroup.Normal.conj_mem inferInstance _ hn'.1 _,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hn'.2) (Subgroup.inv_mem _ hg)⟩
  let f : ↥(X.subgroupOf Y) →* ↥X :=
    { toFun := fun z => ⟨(z : Y), z.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hcomap : (L.subgroupOf X).comap f = (L.subgroupOf Y).subgroupOf (X.subgroupOf Y) := by
    ext z
    rfl
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((Subgroup.subgroupOfEquivOfLe hL).trans (Subgroup.subgroupOfEquivOfLe (hL.trans hXY)).symm)
    hc.1, ?_⟩
  have h1 : ((L.subgroupOf Y).subgroupOf (X.subgroupOf Y)).IsSubnormal :=
    hcomap ▸ hc.2.comap f
  exact Subgroup.IsSubnormal.trans (fun z hz => hL hz) h1 hnorm.isSubnormal

theorem commonLayerCentralizerTrivial_of_components_inner_aut {P : Type} [Group P] {p : ℕ}
    (h : ∀ A : Subgroup (MulAut P), A ≤ OuterAutomorphisms.inner P → IsElementaryAbelian p A →
      Nat.card A = p ^ 2 → ∀ α : MulAut P,
        (∀ a ∈ A, a ≠ 1 → ∀ L : Subgroup (MulAut P),
          L ≤ OuterAutomorphisms.inner P ⊓ Subgroup.centralizer ({a} : Set (MulAut P)) →
          IsComponent (L.subgroupOf (OuterAutomorphisms.inner P ⊓
            Subgroup.centralizer ({a} : Set (MulAut P)))) → ∀ d ∈ L, d * α = α * d) → α = 1) :
    CommonLayerCentralizerTrivial P p := by
  intro D hD A hAinner hA hAcard
  rw [iInf_centralizer_layerCentralizer_eq_bot_iff]
  intro α hα
  have : (OuterAutomorphisms.inner P).Normal := OuterAutomorphisms.inner_normal P
  refine h A hAinner hA hAcard α fun a haA ha1 L hL hc d hd => ?_
  have hLD : L ≤ D ⊓ Subgroup.centralizer ({a} : Set (MulAut P)) :=
    hL.trans (inf_le_inf_right _ hD)
  exact hα a haA ha1 d
    (le_layerCentralizer_of_isComponent hLD (isComponent_subgroupOf_of_normal_le hD a hL hc) hd)

end CFSG.RankThree.PartOne
