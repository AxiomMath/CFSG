module

public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRank
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Basic
import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankGeneral
public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankE8
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.RankThree.Chevalley.SteinbergCFOddInnerFieldLocalCore

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.SeitzGeneration CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.Open (IsElemAbelian)

namespace ExcFieldAutCentRankE8

section Assembly


private theorem exists_centralizing_elemAbelian_field_E8
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {n f : ℕ}
    {ψ : adjointGroup .E8 (GaloisField 2 f) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (ggU .E8 n f).D .E8 n f ψ)
    {y : G} (hyM : y ∈ Subgroup.normalizer (G₀ : Set G)) (hyp : orderOf y = p)
    (hni : ¬ GGPsiInnerDiag (ggU .E8 n f).D ψ y) :
    ∃ E₀ : Subgroup G, E₀ ≤ G₀ ∧ IsElemAbelian p E₀ ∧ (∀ x ∈ E₀, y * x = x * y) ∧
      Nat.card Bs ≤ p * Nat.card E₀ := by
  classical
  have hpp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpres : GGPresentsG0 G₀ (ggU .E8 n f).D .E8 n f ψ := hS.presents
  have hrange : ψ.range = G₀ := hS.range_eq
  have hf : 1 ≤ f := hpres.1.1.2.1
  have hker : ψ.ker ≤ Subgroup.center (ggU .E8 n f).K := hpres.2.1.2
  have hZ : Subgroup.center (ggU .E8 n f).K = ⊥ :=
    center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hBsr : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ :=
      ggPsiDiagInner_E8 G n f ψ G₀ hpres b (hS.bstar_le hb) (hS.innerDiag b hb)
    rw [hS.centralizer_eq_bot, Subgroup.mem_bot] at hbg
    rw [hrange, eq_inv_of_mul_eq_one_left hbg]
    exact G₀.inv_mem hg
  have hyM' : y ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hyM
  obtain ⟨α, hα⟩ :=
    CFSG.StandardType.ExcFieldAutCentRankF4.exists_aut_of_mem_normalizer ψ hinj hyM'
  have hαk : ∀ (k : ℕ) u, ψ ((α ^ k) u) = y ^ k * ψ u * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih => intro u; rw [pow_succ', MulAut.mul_apply, hα, ih]; group
  have hyp1 : y ^ p = 1 := by rw [← hyp]; exact pow_orderOf_eq_one y
  have hαp : α ^ p = 1 := by
    refine MulEquiv.ext fun u => hinj ?_
    rw [hαk, hyp1]
    simp
  have hnin : ∀ h : adjointGroup .E8 (GaloisField 2 f), α ≠ MulAut.conj h := by
    intro h hh
    apply hni
    refine ggPsiInnerDiag_of_mem_range _ ?_
    have hc : (ψ h)⁻¹ * y ∈ Subgroup.centralizer (G₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [← hrange] at hx
      obtain ⟨u, rfl⟩ := hx
      have e : y * ψ u * y⁻¹ = ψ h * ψ u * (ψ h)⁻¹ := by
        rw [← hα u, hh]
        simp [MulAut.conj_apply, map_mul, map_inv]
      calc ψ u * ((ψ h)⁻¹ * y) = (ψ h)⁻¹ * (ψ h * ψ u * (ψ h)⁻¹) * y := by group
        _ = (ψ h)⁻¹ * (y * ψ u * y⁻¹) * y := by rw [e]
        _ = (ψ h)⁻¹ * y * ψ u := by group
    rw [hS.centralizer_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hc
    rw [← hc]
    exact ⟨h, rfl⟩
  have hf0 : f ≠ 0 := by omega
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf0
  obtain ⟨hNFuniq, Θ, hΘ, -, hΘker, -⟩ :=
    CFSG.LieType.Chevalley.even_E7_E8_exact_inner_field_automorphism_normal_form hf
      (GaloisField 2 f) hK .E8 (Or.inr rfl)
  have hNF : ∀ α : MulAut (adjointGroup .E8 (GaloisField 2 f)), α ^ p = 1 →
      (∀ h : adjointGroup .E8 (GaloisField 2 f), α ≠ MulAut.conj h) →
      ∃ (x : adjointGroup .E8 (GaloisField 2 f)) (σ : GaloisField 2 f ≃+* GaloisField 2 f),
        σ ^ p = 1 ∧ σ ≠ 1 ∧ α = MulAut.conj x * entrywiseAdjointAut .E8 σ := by
    intro α hαp hnin
    obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNFuniq α
    have hα_eq : α = MulAut.conj x * entrywiseAdjointAut .E8 σ := by
      refine MulEquiv.ext fun h => Subtype.ext ?_
      rw [hxσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_entrywiseAdjointAut]
    have hα_ord : orderOf α = p := by
      refine orderOf_eq_prime hαp ?_
      intro h1
      exact hnin 1 (by rw [h1]; exact (map_one (MulAut.conj : adjointGroup .E8
        (GaloisField 2 f) →* MulAut (adjointGroup .E8 (GaloisField 2 f)))).symm)
    have hΘα : Θ α = σ := hΘ α x σ hxσ
    have hσp1 : σ ^ p = 1 := by rw [← hΘα, ← map_pow, hαp, map_one]
    have hσ1 : σ ≠ 1 := by
      intro h1
      have hmem : α ∈ Θ.ker := by
        rw [MonoidHom.mem_ker, hΘα, h1]
      rw [hΘker] at hmem
      obtain ⟨g, hg⟩ := hmem
      exact hnin g hg.symm
    exact ⟨x, σ, hσp1, hσ1, hα_eq⟩
  obtain ⟨hBel, hBcard⟩ :=
    CFSG.StandardType.ExcFieldAutCentRankF4.pullback_elemAbelian ψ hinj p Bs hBsr hS.elem
  set e : ℕ := orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)
  have hTransfer : GGFieldRankTransfer .E8 (GaloisField 2 f) p :=
    ggFieldRankTransfer_of_bounds hpp
      (fun E hE => rankLE_E8 (K := GaloisField 2 f) (p := p) (e := e) hpp hp2 rfl E hE)
      (fun σ hσp hσ1 => by
        haveI : Finite (fixSubfield σ) :=
          Finite.of_injective (Subtype.val : fixSubfield σ → GaloisField 2 f)
            Subtype.val_injective
        haveI : CharP (fixSubfield σ) 2 := Subfield.charP (fixSubfield σ) 2
        exact exists_E8 (K := fixSubfield σ) (e := e) hpp hp2
          (by rw [orderOf_card_fixSubfield_eq hpp hp2 σ hσ1 hσp]))
  exact exists_elemAbelian_centralizing_of_mulAut_field (τ := .E8) (K := GaloisField 2 f)
    (f := f) hpp hp2 hf hK hinj hrange hS.centralizer_eq_bot hBel
    (le_of_eq hBcard.symm) hyM hyp hNF hTransfer α hα hαp hnin

end Assembly

end ExcFieldAutCentRankE8

section Final


theorem ggExcFieldAutCentRank_E8 :
    GGExcFieldAutCentRank .E8 := by
  intro G _ _ p Bs G₀ n f ψ hS y hyM hyp _ hni
  exact ExcFieldAutCentRankE8.exists_centralizing_elemAbelian_field_E8 hS hyM hyp hni

end Final

end CFSG.StandardType
