module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityExact
public import CFSG.RankThree.PartOne.KC.PlaneProductsTrivialOfRigidity

public section

namespace CFSG.RankThree.PartOne.KCUnitaryGlue

open Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCGeneric

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {Ahat : Subgroup (gramSU h (idGram K n))}

@[expose] noncomputable def goodJoin (h : UnitaryFieldData ℓ f K) (n : ℕ)
    (Ahat : Subgroup (gramSU h (idGram K n))) (a : MulAut (primeFormP h (idGram K n))) :
    Subgroup (MulAut (primeFormP h (idGram K n))) :=
  ⨆ (x : gramSU h (idGram K n)) (_ : x ∈ Ahat ∧ innerLift h n x = a ∧ x ≠ 1)
    (i : GoodBlockIdx h x), idBlockImage h x (i.1 : K[X])

theorem innerLift_eq_conjHom (x : gramSU h (idGram K n)) :
    innerLift h n x = primeFormConjHom h (idGram K n) (liftUnitary x) := by
  rw [primeFormConjHom_liftUnitary, innerLift_apply]

theorem plane_products_trivial_of_lift (S : PlaneSetup h n p Ahat)
    {A : Subgroup (MulAut (primeFormP h (idGram K n)))} (hAhat : IsPlaneLift h n p A Ahat)
    (B : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hcore : ∀ a ∈ A, a ≠ 1 → ∀ x ∈ Ahat, innerLift h n x = a → orderOf x = p →
      (∀ i : GoodBlockIdx h x, ∀ s ∈ idLocalCore h n p B a, ∀ j ∈ idBlockImage h x (i.1 : K[X]),
        s * j = j * s) ∧ ⁅idLocalCore h n p B a, A⁆ = ⊥)
    (hrig : ∀ β : MulAut (primeFormP h (idGram K n)),
      (∀ x ∈ Ahat, β * primeFormConjHom h (idGram K n) (liftUnitary x) =
        primeFormConjHom h (idGram K n) (liftUnitary x) * β) →
      (∀ x ∈ Ahat, x ≠ 1 → ∀ i : GoodBlockIdx h x, ∀ g ∈ idSpecialBlock h x (i.1 : K[X]),
        β * primeFormConjHom h (idGram K n) g = primeFormConjHom h (idGram K n) g * β) →
      β = 1) :
    autThetaT p B A = ⊥ ∧ ∀ t ∈ A, t ≠ 1 → autPlaneProduct p B A t = ⊥ := by
  classical
  have hn := S.three_le
  have hne := S.ne
  have : Fact p.Prime := ⟨S.prime⟩
  have hlift : ∀ a ∈ A, a ≠ 1 → ∃ x ∈ Ahat, innerLift h n x = a ∧ orderOf x = p := by
    intro a haA ha1
    obtain ⟨x, hx, hxa, hxp, -⟩ := planeLift_unique_lift hn hne S.prime S.noTorsion hAhat haA ha1
    exact ⟨x, hx, hxa, hxp⟩
  have hmemA : ∀ x ∈ Ahat, innerLift h n x ∈ A := fun x hx => by
    rw [← hAhat.2.2.1]
    exact Subgroup.mem_map_of_mem _ hx
  have hne1 : ∀ x ∈ Ahat, x ≠ 1 → innerLift h n x ≠ 1 := fun x hx hx1 h1 =>
    hx1 (hAhat.2.2.2 hx (Subgroup.one_mem _) (by rw [h1, map_one]))
  refine plane_products_trivial_of_rigidity (p := p) B A (goodJoin h n Ahat) ?_ ?_ ?_
  · intro a haA ha1
    obtain ⟨x, hx, hxa, hxp⟩ := hlift a haA ha1
    exact (hcore a haA ha1 x hx hxa hxp).2
  · intro a haA ha1 s hs j hj
    have hle : goodJoin h n Ahat a ≤ Subgroup.centralizer ({s} : Set _) := by
      refine iSup_le fun x => iSup_le fun hx => iSup_le fun i => ?_
      intro j' hj'
      rw [Subgroup.mem_centralizer_iff]
      intro s' hs'
      rw [Set.mem_singleton_iff] at hs'
      subst hs'
      have hxp : orderOf x = p := orderOf_eq_prime (S.pow_eq_one hx.1) hx.2.2
      exact (hcore a haA ha1 x hx.1 hx.2.1 hxp).1 i s' hs j' hj'
    have := hle hj
    rw [Subgroup.mem_centralizer_iff] at this
    exact this s rfl
  · intro β hβA hβJ
    refine hrig β (fun x hx => ?_) (fun x hx hx1 i g hg => ?_)
    · rw [← innerLift_eq_conjHom]
      exact hβA _ (hmemA x hx)
    · refine hβJ (innerLift h n x) (hmemA x hx) (hne1 x hx hx1) _ ?_
      exact Subgroup.mem_iSup_of_mem x (Subgroup.mem_iSup_of_mem ⟨hx, rfl, hx1⟩
        (Subgroup.mem_iSup_of_mem i (Subgroup.mem_map_of_mem _ hg)))

end CFSG.RankThree.PartOne.KCUnitaryGlue
