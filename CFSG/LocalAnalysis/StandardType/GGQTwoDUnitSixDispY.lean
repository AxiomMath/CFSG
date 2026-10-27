module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixDispBig
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixDispO
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixTableP
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixDispU
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixNbr
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixStd

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDUnitSix_orthY
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e)
    (hL : GGInnerDiagOn Bs L) (hcard : Nat.card ↥Bs = 3 ^ 6) (hK : Nat.card K = 4) {Q : Type}
    [Group Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψr : ψ.range = NsQuot.img (Subgroup.normalizer (L : Set G)) f L)
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6))
    (hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)
    (hxBs : x ∈ Bs) (hxord : orderOf x = 3) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    {βL : Additive ↥Bs ≃+ DVec 6} (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1)
    {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    (hjoin : ∀ w ∈ dEven 6, ∃ a ∈ ggAutomizerJoin L Bs 𝒦,
      ∀ s : ↥Bs, βL (Additive.ofMul (a s)) = w (βL (Additive.ofMul s)))
    {a c : Fin 6} (hac : a ≠ c) {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {b' : ↥Bs}
    (hb' : βL (Additive.ofMul b') = Pi.single c 1) (hb'B : (b' : G) ∈ B) :
    ∃ Y : Subgroup G, J₁ ≤ Y ∧ J₁.map (MulAut.conj g).toMonoidHom ≤ Y ∧
      ∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 ∧ Φ.r = 5 ∧
        Subgroup.center ↥Y = ⊥ := by
  classical
  have hThmI : GGThmIHyp 3 B x L := hcfg.1.1.1.1
  have hstar : GGBstar 3 B Bs := hcfg.1.1.1.2.1
  have hBsE := hstar.2.1
  have hSC := hstar.2.2.2
  have hBBs : B ≤ Bs := hstar.1
  have hxB : x ∈ B := hThmI.2.2.2.2.2.2.1.2.1
  obtain ⟨N, hN, hJ₁N, hJ₂N⟩ := ggQTwoDUnitSix_exists_N hLB hcfg hcard hK hD hψr hψk hε hxBs
    hxcoord hω hind hpermβ hac hJ₁L hJ₁Z hJ₁ hα hg hb'
  have hBsN : Bs ≤ Subgroup.normalizer (N : Set G) :=
    ggQTwoDUnitSix_normalizer_N hK hD hψk hBsE hind hJ₁L hJ₁Z hJ₁ b'.2 hN hJ₁N
  have hDJ := ggQTwoDUnitSix_stdSub hK hD hψr hψk hBsE hBBs hxB hxBs hxord hxL hxcoord hω hind
    hJ₁L hJ₁Z hJ₁ hb' hb'B
  have hnbr := ggQTwoDUnitSix_nbr hK hD hψr hψk hThmI hBsE hBBs hxB hxBs hxord hxL hxcoord hω
    hind hac hJ₁L hJ₁Z hJ₁ hα hgN hg hb' hb'B hN hJ₁N hJ₂N
  have hinner : GGInnerDiagOn Bs N := ggQTwoDUnitSix_innerDiag_N hThmI hDJ hnbr hBsN
    (ggQTwoDUnitSix_inner_N hK hD hψk hε hind hpermβ hac hJ₁L hJ₁Z hJ₁ hα hg hb' hN hJ₁N hJ₂N)
  have h5 : (Finset.univ.erase c).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  obtain ⟨θ, hθ, hθr, -⟩ := ggQTwoDUnitSix_chart hK hD hψk (Finset.univ.erase c) (by omega)
    hJ₁L hJ₁Z hJ₁
  obtain ⟨lab, hΛ, hlab, hcand⟩ := ggQTwoDUnitSix_candidate hLB ⟨hThmI, hstar, hDJ⟩ hL hinner
    hnbr (ggQTwoDUnitSix_cent_J hK hD hψk hxBs hxL hxcoord hω hind hJ₁L hJ₁Z hJ₁ hb').le hJ₁N
    (ggQTwoDUnitSix_three_dvd_card hK (by omega) hθ hθr) hcard
    (ggQTwoDUnitSix_label_J hK h5 hθ hθr)
  unfold QTwoDeletedUnitaryCandidate at hcand
  rcases hcand with h | ⟨-, h3⟩ | h | ⟨he, -⟩ | ⟨-, h | h⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h9, -⟩
  ·
    subst h
    exact (ggQTwoDUnitSix_not_unitary hK hD hψk hε hBsE hω hind hpermβ hac hJ₁L hJ₁Z hJ₁ hα hgN
      hg hJ₁N hJ₂N hlab).elim
  ·
    exact absurd h3 (by norm_num)
  ·
    subst h
    exact ggQTwoDUnitSix_orthY_symplectic hK hD hψk hε hBsE hSC hcard hω hind hpermβ hxBs hxL
      hxcoord hac hJ₁L hJ₁Z hJ₁ hα hgN hg hb' hN hJ₁N hJ₂N hBsN hjoin hlab
  ·
    obtain ⟨k, hk⟩ := he
    omega
  ·
    exact ⟨N, hJ₁N, hJ₂N, ggQTwoDUnitSix_orthY_twD5 hRig hK hD hψk hBsE hSC hxBs hxcoord hω hind
      hac hJ₁ hα hgN hg hJ₂N hinner hΛ hlab h⟩
  ·
    exact ggQTwoDUnitSix_orthY_twD6 hRig hK hD hψk hε hBsE hSC hcard hω hind hpermβ hxBs hxL
      hxcoord hac hJ₁L hJ₁Z hJ₁ hα hgN hg hb' hN hJ₁N hJ₂N hinner hjoin hΛ hlab h
  · exact absurd h6 (by norm_num)
  · exact absurd h7 (by norm_num)
  · exact absurd h9 (by norm_num)

end CFSG.StandardType.QTwo

end
