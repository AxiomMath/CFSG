module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixNbrB
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispO

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {G : Type} [Group G] [Finite G]


theorem ggQTwoDUnitSix_orthY_twD5
    (hRig : GGLabelRigidInput) (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type} [Group Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) {x : G} (hxBs : x ∈ Bs)
    {βL : Additive ↥Bs ≃+ DVec 6} (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1)
    {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    {a c : Fin 6} (hac : a ≠ c) {J₁ : Subgroup G}
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {N : Subgroup G}
    (hJ₂N : J₁.map (MulAut.conj g).toMonoidHom ≤ N) (hinner : GGInnerDiagOn Bs N)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N)) (hlab5 : lab = ⟨.twD, 5, 1⟩) :
    ∃ Φ : OrthTorus.OrthFrameCore 3 Bs N, Nat.card Φ.F = 2 ∧ Φ.r = 5 ∧
      Subgroup.center ↥N = ⊥ :=
  qtwoDB25_orthY_of hRig hBs hSC hinner hxBs
    (fun hx => ggQTwoDUnitSix_x_not_mem_centralizer_J₂ hK hD hψk hxBs hxcoord hω hind hac hJ₁ hα
      hgN hg (Subgroup.centralizer_le hJ₂N hx))
    hΛ hlab (Or.inr ⟨by decide, le_rfl, hlab5⟩)

end CFSG.StandardType.QTwo

end
