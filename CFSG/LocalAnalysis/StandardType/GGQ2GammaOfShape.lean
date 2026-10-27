module

public import CFSG.LocalAnalysis.StandardType.GGQ2LDatumShapePm
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXDetCell
import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2gs_xV_ne_zero {G : Type} [Group G] {Bs X : Subgroup G} {u : G}
    (M : GGQ2LDatum 3 Bs X u) (hu : u ≠ 1) : M.xV ≠ 0 := by
  intro h
  apply hu
  have h1 : (⟨u, M.hx⟩ : ↥Bs) = 1 := by
    apply Additive.ofMul.injective
    apply M.model.injective
    change M.xV = M.model (Additive.ofMul 1)
    rw [h, ofMul_one, map_zero]
  exact congrArg Subtype.val h1

theorem ggQ2_gammaNbr_of_tableBShape (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) {y : G}
    {K : Subgroup G} (hnb : GGNbr 3 B x D J y K) (M : GGQ2LDatum 3 Bs K y) (hsh : M.Shape)
    (hinner : M.ShapeFull → ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 →
      ∃ (n : ℕ) (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ M.Λ),
        (∀ i j, M.cartan (e i) (e j) = C₀ i j) ∧ GGQ2WeylInner n C₀)
    (hheart : M.ShapeB → ∃ r, 4 ≤ r ∧ ∃ e : Fin r ≃ M.Λ,
      ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A r i j)
    {u : ↥Bs} (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers y) :
    GGGammaAt 3 B Bs x L D J u :=
  ggQ2_gammaNbr_of_datumPM hLB hP h5 hS rfl hI1 hnb
    (M.toNbrDatum (ggBarCentralizer_nbr_iff_of_K1 (ggQ2_K1_of_I1 hLB hP hS.1 hI1) hnb))
    (fun u₀ hu0 hfix hdim h4 hTF T hT =>
      M.pmW_of_shape hsh (ggQ2gs_xV_ne_zero M hnb.1.2.2.1) hinner hheart u₀ hu0 hfix hdim h4 hTF
        T hT) hu

theorem ggQ2_gammaX_of_tableBShape (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card (ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) (hsh : M.Shape)
    (hinner : M.ShapeFull → ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 →
      ∃ (n : ℕ) (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ M.Λ),
        (∀ i j, M.cartan (e i) (e j) = C₀ i j) ∧ GGQ2WeylInner n C₀)
    (hheart : M.ShapeB → ∃ r, 4 ≤ r ∧ ∃ e : Fin r ≃ M.Λ,
      ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A r i j) :
    GGQ2GammaX 3 B Bs x L D J :=
  ggQ2xd_gammaX_of_datumPM hLB hP hS rfl hCav M
    (fun u₀ hu0 hfix hdim h4 hTF T hT =>
      M.pmW_of_shape hsh (ggQ2gs_xV_ne_zero M hS.1.1.1.2.2.2.2.2.2.1.2.2.1) hinner hheart u₀ hu0
        hfix hdim h4 hTF T hT)

end CFSG.StandardType

end
