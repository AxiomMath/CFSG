module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepPos
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrameK
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbr

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwoNodeIndepAtL_weyl (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {N : ℕ} (hN : 10 ≤ N) (hpN : p ∣ N)
    (hmove : ∃ t ∈ ggAutomizer K Bs, GGIsReflection p t ∧ t ⟨x, hx⟩ ≠ ⟨x, hx⟩)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (e : Fin (N - 1) ≃ Λ) (hML : ML = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCL : GGIntCartan ML CL) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h)
    (hpm1 : 5 ≤ p → GGIndepPm1 p N ι (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hp2 : p ≠ 2 := by omega
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have F := ggXDatumA_indep_frame hFix hp2 hH hx (by omega) hpN e hML hCL hφ hpair hAL hind
  exact ggIndep_pos_weyl hKG hp hN hH.2.2.2.1 hx
    (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top))
    (hOrb G p B Bs x L D J y K hH hx) hH.2.2.2.2.2.1 hmove e hφ hrefl hAL F hpm1

theorem ggTwoNodeIndepAtK_weyl (hKG : GGReflClassLargeInput') (hOrbK : GGResCentBoundNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y)
    (hLrefl : GGReflGenerated p (ggAutomizer L Bs)) {N : ℕ} (hN : 10 ≤ N) (hpN : p ∣ N)
    (hmove : ∃ t ∈ ggAutomizer L Bs, GGIsReflection p t ∧ t ⟨y, hy⟩ ≠ ⟨y, hy⟩)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ}
    (e : Fin (N - 1) ≃ Λ) (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h)
    (hpm1 : 5 ≤ p → GGIndepPm1 p N ι (ggAutomizer K Bs ⊔ ggAutomizer L Bs)) :
    GGWeylReflectionGroup p (ggAutomizer K Bs ⊔ ggAutomizer L Bs) := by
  have hp2 : p ≠ 2 := by omega
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have F := ggXDatumA_indep_frame_K hp2 hH hy hstrong (by omega) hpN e hMK hCK hφ hpair hAK hind
  have hstab : Nat.card ↥((ggAutomizer K Bs ⊔ ggAutomizer L Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ≤ (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
    rw [sup_comm]
    exact hOrbK G p B Bs x L D J y K hH hy
  exact ggIndep_pos_weyl hKG hp hN hH.2.2.2.1 hy
    (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top))
    hstab hLrefl hmove e hφ hrefl hAK F hpm1

end CFSG.StandardType

end
