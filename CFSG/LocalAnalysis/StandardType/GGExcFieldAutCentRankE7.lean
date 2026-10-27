module

public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRank
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Basic
import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankGeneral
public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankE7
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.RankThree.Chevalley.SteinbergCFOddInnerFieldLocalCore

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.SeitzGeneration CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.Open (IsElemAbelian)

namespace ExcFieldAutCentRankE7

section Assembly


private theorem exists_centralizing_elemAbelian_field_E7
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {n f : ℕ}
    {ψ : (ggU .E7 n f).K →* G}
    (hS : GGSixFusionSetting p Bs G₀ (ggU .E7 n f).D .E7 n f ψ)
    {y : G} (hyM : y ∈ Subgroup.normalizer (G₀ : Set G)) (hyp : orderOf y = p)
    (hni : ¬ GGPsiInnerDiag (ggU .E7 n f).D ψ y) :
    ∃ E₀ : Subgroup G, E₀ ≤ G₀ ∧ IsElemAbelian p E₀ ∧ (∀ x ∈ E₀, y * x = x * y) ∧
      Nat.card Bs ≤ p * Nat.card E₀ := by
  classical
  have hpp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpres : GGPresentsG0 G₀ (ggU .E7 n f).D .E7 n f ψ := hS.presents
  have hrange : ψ.range = G₀ := hS.range_eq
  have hf : 1 ≤ f := hpres.1.1.2.1
  have hker : ψ.ker ≤ Subgroup.center (ggU .E7 n f).K := hpres.2.1.2
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans
      (CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot (K := GaloisField 2 f)).le
  have hBsr : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ :=
      ggPsiDiagInner_E7 G n f ψ G₀ hpres b (hS.bstar_le hb) (hS.innerDiag b hb)
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
  have hnin : ∀ h : (ggU .E7 n f).K, α ≠ MulAut.conj h := by
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
  let ε : (ggU .E7 n f).K ≃* adjointGroup .E7 (GaloisField 2 f) :=
    CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 f)
  let α_ad : MulAut (adjointGroup .E7 (GaloisField 2 f)) := MulAut.congr ε α
  have hcongr : ∀ u : (ggU .E7 n f).K, α_ad (ε u) = ε (α u) := by
    intro u
    simp [α_ad, MulAut.congr, MulEquiv.trans_apply]
  have hαad_pow : α_ad ^ p = 1 := by
    have h1 : MulAut.congr ε (α ^ p) = (MulAut.congr ε α) ^ p := map_pow (MulAut.congr ε) α p
    rw [hαp, map_one] at h1
    exact h1.symm
  have hnin_ad : ∀ g : adjointGroup .E7 (GaloisField 2 f), α_ad ≠ MulAut.conj g := by
    intro g hg
    apply hnin (ε.symm g)
    ext u
    refine ε.injective ?_
    rw [← hcongr u, hg]
    simp [MulAut.conj_apply, map_mul, map_inv]
  have hf0 : f ≠ 0 := by omega
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf0
  obtain ⟨hNFuniq, Θ, hΘ, -, hΘker, -⟩ :=
    CFSG.LieType.Chevalley.even_E7_E8_exact_inner_field_automorphism_normal_form hf
      (GaloisField 2 f) hK .E7 (Or.inl rfl)
  have hNF : ∀ α : MulAut (adjointGroup .E7 (GaloisField 2 f)), α ^ p = 1 →
      (∀ h : adjointGroup .E7 (GaloisField 2 f), α ≠ MulAut.conj h) →
      ∃ (x : adjointGroup .E7 (GaloisField 2 f)) (σ : GaloisField 2 f ≃+* GaloisField 2 f),
        σ ^ p = 1 ∧ σ ≠ 1 ∧ α = MulAut.conj x * entrywiseAdjointAut .E7 σ := by
    intro α hαp hnin
    obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNFuniq α
    have hα_eq : α = MulAut.conj x * entrywiseAdjointAut .E7 σ := by
      refine MulEquiv.ext fun h => Subtype.ext ?_
      rw [hxσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_entrywiseAdjointAut]
    have hα_ord : orderOf α = p := by
      refine orderOf_eq_prime hαp ?_
      intro h1
      exact hnin 1 (by rw [h1]; exact (map_one (MulAut.conj : adjointGroup .E7
        (GaloisField 2 f) →* MulAut (adjointGroup .E7 (GaloisField 2 f)))).symm)
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
  let B : Subgroup (ggU .E7 n f).K := Bs.comap ψ
  let B_ad : Subgroup (adjointGroup .E7 (GaloisField 2 f)) := B.map ε.toMonoidHom
  have hBad : IsElemAbelian p B_ad := hBel.map ε.toMonoidHom
  have hBcard_ad : Nat.card B_ad = Nat.card B := Subgroup.card_map_of_injective ε.injective
  set e : ℕ := orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)
  have hTransfer : GGFieldRankTransfer .E7 (GaloisField 2 f) p :=
    ggFieldRankTransfer_of_bounds hpp
      (fun E hE => rankLE_E7 (K := GaloisField 2 f) (p := p) (e := e) hpp hp2 rfl E hE)
      (fun σ hσp hσ1 => by
        haveI : Finite (fixSubfield σ) :=
          Finite.of_injective (Subtype.val : fixSubfield σ → GaloisField 2 f)
            Subtype.val_injective
        haveI : CharP (fixSubfield σ) 2 := Subfield.charP (fixSubfield σ) 2
        exact exists_E7 (K := fixSubfield σ) (e := e) hpp hp2
          (by rw [orderOf_card_fixSubfield_eq hpp hp2 σ hσ1 hσp]))
  let ψ' : adjointGroup .E7 (GaloisField 2 f) →* G := ψ.comp ε.symm.toMonoidHom
  have hψ'inj : Function.Injective ψ' := hinj.comp ε.symm.injective
  have hrange' : ψ'.range = G₀ := by
    rw [← hrange]
    ext x
    exact ⟨fun ⟨u, hu⟩ => ⟨ε.symm u, by simpa [ψ'] using hu⟩,
      fun ⟨v, hv⟩ => ⟨ε v, by simpa [ψ'] using hv⟩⟩
  have hα' : ∀ u : adjointGroup .E7 (GaloisField 2 f), ψ' (α_ad u) = y * ψ' u * y⁻¹ := by
    intro u
    have h1 : α_ad u = ε (α (ε.symm u)) := by
      have h := hcongr (ε.symm u)
      simpa using h
    change ψ (ε.symm (α_ad u)) = y * ψ (ε.symm u) * y⁻¹
    rw [h1, MulEquiv.symm_apply_apply]
    exact hα (ε.symm u)
  exact exists_elemAbelian_centralizing_of_mulAut_field (τ := .E7) (K := GaloisField 2 f)
    (f := f) hpp hp2 hf hK hψ'inj hrange' hS.centralizer_eq_bot hBad
    (le_of_eq (hBcard_ad.trans hBcard).symm) hyM hyp hNF hTransfer α_ad hα' hαad_pow hnin_ad

end Assembly

end ExcFieldAutCentRankE7

section Final


theorem ggExcFieldAutCentRank_E7 :
    GGExcFieldAutCentRank .E7 := by
  intro G _ _ p Bs G₀ n f ψ hS y hyM hyp _ hni
  exact ExcFieldAutCentRankE7.exists_centralizing_elemAbelian_field_E7 hS hyM hyp hni

end Final

end CFSG.StandardType
