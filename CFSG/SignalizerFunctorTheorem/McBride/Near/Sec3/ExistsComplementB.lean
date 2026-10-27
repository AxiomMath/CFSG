module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm35Aux6

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem exists_complement_B'
    (hθ : NearFunctor p A θ) {D₂ : Subgroup G}
    (_hD₂ : D₂ ∈ dset p A θ) {X : Subgroup G} (hX : X ∈ cset p A θ D₂)
    [(D₂.subgroupOf (dsub A θ)).Normal] {N L R : Subgroup G}
    (hN : N ≤ X) (hL : L ≤ X) (hR : R ≤ X)
    (ha : IsNormalIn N (R ⊔ dsub A θ ⊔ A) ∧ IsNormalIn L (R ⊔ dsub A θ ⊔ A) ∧
      IsNormalIn R (R ⊔ dsub A θ ⊔ A))
    (hb : IsChiefFactorOf (R ⊔ dsub A θ ⊔ A) L N ∧ L ≤ R)
    (hc : A ⊔ R ≤ secCenIn (R ⊔ dsub A θ ⊔ A) L N)
    (hd : R ⊓ dsub A θ = fittingPre (dsub A θ) D₂ ∧ dsub A θ ⊓ N ≤ D₂ ∧
      IsDirectProductMod N (fittingPre (dsub A θ) D₂ ⊔ N) (D₂ ⊔ N) L) :
    ∃ B : Subgroup G, B ≤ R ∧ IsNormalIn B (R ⊔ dsub A θ ⊔ A) ∧ B ⊓ dsub A θ = D₂ ∧
      R = B ⊔ fittingPre (dsub A θ) D₂ := by
  have hXm : X ∈ mtil p A θ := hX.1
  have hact : NearAsolvAction p A X :=
    { prime := hθ.prime
      odd := hθ.odd
      elemAbelian := hθ.elemAbelian
      admits := hXm.1.1
      nearPSolvable := hXm.1.2.2.2.1
      solvable_cen := hXm.1.2.2.2.2 }
  have hpair : (iPairsY A X D₂).Nonempty := by
    rw [← pairsYX_eq_iPairsY (Y := D₂) hθ hXm]
    exact hX.2
  exact Thm35.thm35_below p (Nat.card ↥X + 1) G A X (dsub A θ) D₂ N L R (Nat.lt_succ_self _)
    ⟨hact, cenIn_eq_dsub_of_mem_mtil hθ hXm, hpair, hN, hL, hR, ha.1, ha.2.1, ha.2.2, hb.1,
      hb.2, hc, hd.1, hd.2.1, hd.2.2⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near
