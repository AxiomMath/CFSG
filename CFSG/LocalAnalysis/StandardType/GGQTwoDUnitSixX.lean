module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitXFacts

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDUnitSix_X_frame (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type} [Group Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6))
    (hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)
    {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ}
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    {x : G} (hxBs : x ∈ Bs) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1) {a c : Fin 6} (hac : a ≠ c)
    {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {b' : ↥Bs} (hb' : βL (Additive.ofMul b') = Pi.single c 1)
    (hb'J : (b' : G) ∈ Subgroup.centralizer (J₁ : Set G)) {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {𝒦 : Finset (Subgroup G)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    {e' : Fin 6 ≃ ι}
    (hjoin : ∀ w ∈ dEven 6, ∃ a ∈ ggAutomizerJoin L Bs 𝒦,
      ∀ s : ↥Bs, βL (Additive.ofMul (a s)) = w (βL (Additive.ofMul s)))
    (hnode : ∃ c₀ : Fin 6, ∀ i : Fin 6, (i : ℕ) ≠ 0 → ∃ (sgn : Bool) (a b : Fin 6),
      a ≠ b ∧ a ≠ c₀ ∧ b ≠ c₀ ∧ ∀ s : ↥Bs,
        βL (Additive.ofMul ((((e (M.simple (e' i)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))
          s)) = dTau 6 sgn a b (βL (Additive.ofMul s))) :
    QTwoFrameAt Bs (J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom) M (ggAutomizerJoin L Bs 𝒦) e e' :=
  qtwoDB22_frame_of_weyl hjoin hnode fun _ _ _ hw hwc ha'w =>
    ggQTwoDUnitSix_weyl_X hK hD hψk hε hind hpermβ hxBs hxL hxcoord hac hJ₁L hJ₁Z hJ₁ hb' hb'J
      hα hgN hg hw hwc ha'w

end CFSG.StandardType.QTwo

end
