module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9LinearCover
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9LinearTorus
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9La
public import CFSG.LocalAnalysis.StandardType.GGAutomizerEquiv
import CFSG.GH74.Exceptional.LinearFourTwo
import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute
import CFSG.RankThree.PartTwo.Sec14.Ronan148JInner

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Multiplicative

variable {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {z : G}
  {F : Type} [Field F] [Finite F] {d : ℕ}

theorem center_eq_bot_of_native_linear_two (hF : Nat.card F = 2)
    (e : K ≃* projectiveSL d F) : Subgroup.center K = ⊥ := by
  let eSL := e.trans (LineL2.projEquivTwo hF).symm
  apply Subgroup.eq_bot_of_card_eq
  rw [Nat.card_congr (Subgroup.centerCongr eSL).toEquiv,
    LineL2.center_eq_bot_two hF, Subgroup.card_bot]

theorem bstar_eq_zpowers_sup_inf_of_linear_two (hF : Nat.card F = 2)
    (e : K ≃* projectiveSL d F) (hBs : IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hinner : ∀ α ∈ (ggGamma K hN).range,
      MulAut.congr e α ∈ Set.range (conjAut d F)) :
    Bs = Subgroup.zpowers z ⊔ Bs ⊓ K := by
  have hcenter := center_eq_bot_of_native_linear_two hF e
  have hKC : K ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    have hxZ : (⟨x, hx.1⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      exact fun y => Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx.2) y y.property)
    rw [hcenter, Subgroup.mem_bot] at hxZ
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxZ)
  let ρ : Matrix.GeneralLinearGroup (Fin d) F ≃* projectiveSL d F :=
    (LinTwoTB.glEquivSL hF).trans (LineL2.projEquivTwo hF)
  have hρconj : ∀ g : Matrix.GeneralLinearGroup (Fin d) F,
      conjAut d F g = MulAut.conj (ρ g) := by
    intro g
    have h := conjAut_toGL (n := d) (K := F) (TwoThree.toSLHom hF g)
    rw [TwoThree.toGL_toSLHom] at h
    exact h
  have hinnerG : ∀ b ∈ Bs, ∃ k ∈ K, ∀ x ∈ K, b * x * b⁻¹ = k * x * k⁻¹ := by
    intro b hb
    obtain ⟨g, hg⟩ := hinner (ggGamma K hN ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    let k : K := e.symm (ρ g)
    have hγ : ggGamma K hN ⟨b, hb⟩ = MulAut.conj k := by
      apply (MulAut.congr e).injective
      rw [← hg, hρconj]
      ext x
      simp [MulAut.congr_apply, MulAut.conj_apply, k]
    refine ⟨k, k.property, fun x hx => ?_⟩
    have h := congrArg (fun α : MulAut K => ((α ⟨x, hx⟩ : K) : G)) hγ
    simpa only [ggGamma_coe, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hsplit := CFSG.RankThree.PartTwo.Sec14.Ronan148J.sup_eq_of_forall_inner
    (fun b hb c hc => IsElemAbelian.comm hBs hb hc) hBs.2 hBstar hKC hN hinnerG
  rw [hker] at hsplit
  exact hsplit.symm

theorem native_linear_half_dim_eq_of_card_bstar {n : ℕ}
    (hF : Nat.card F = 2) (e : K ≃* projectiveSL d F)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hz : z ∈ Bs) (hz1 : z ≠ 1)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hinner : ∀ α ∈ (ggGamma K hN).range,
      MulAut.congr e α ∈ Set.range (conjAut d F)) : d / 2 = n - 1 := by
  have hsplit := bstar_eq_zpowers_sup_inf_of_linear_two hF e hBs hN hker hBstar hinner
  let V := Fin d → ZMod 2
  let ρ : Matrix.GeneralLinearGroup (Fin d) F ≃* projectiveSL d F :=
    (LinTwoTB.glEquivSL hF).trans (LineL2.projEquivTwo hF)
  let ξ : K ≃* (V ≃ₗ[ZMod 2] V) :=
    ((e.trans ρ.symm).trans (CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo hF d)).trans
      (Matrix.GeneralLinearGroup.toLin.trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V))
  let E := (Bs.subgroupOf K).map ξ.toMonoidHom
  have hcenter : Subgroup.center (V ≃ₗ[ZMod 2] V) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [Nat.card_congr (Subgroup.centerCongr ξ.symm).toEquiv,
      center_eq_bot_of_native_linear_two hF e, Subgroup.card_bot]
  have hAr := P9_Wa_card_range hBs hcard hz hz1 hN hker
  have hcardE : Nat.card E = 3 ^ (n - 1) := by
    have hc : Nat.card ((ggGamma K hN).range.map (MulAut.congr ξ).toMonoidHom) =
        3 ^ (n - 1) := by
      rw [Subgroup.card_map_of_injective (MulAut.congr ξ).injective, hAr]
    rw [map_range_ggGamma_of_split_model ξ hN hker hsplit,
      Subgroup.card_map_of_injective (CFSG.mulAut_conj_injective hcenter)] at hc
    exact hc
  have hsc := selfCentralizing_torus_of_split_model ξ hker hsplit hBstar
  obtain ⟨f, Φ, hf, -, hdim, -⟩ :=
    p9la_linear_position E ((hBs.subgroupOf K).map ξ.toMonoidHom) hcardE hsc
  have hd : d = 2 * (n - 1) + f := by
    simpa only [V, Module.finrank_fin_fun] using hdim
  omega

theorem exists_linear_torusData_of_innerDiagOnLabel
    {S : ℕ → LargeEvenLabel → Prop} {n : ℕ}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : n = 7 ∨ n = 8)
    (hz : z ∈ Bs) (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hS : ∀ lab, S 3 lab → lab.tag = .A ∧ lab.n = 1)
    (hK : GGInnerDiagOnLabel S 3 Bs K) :
    ∃ (s c : ℕ) (D : LinTwoTB.TorusData K s) (wt : K → ℕ),
      (∀ g h : K, MulAut.conj g = MulAut.conj h → g = h) ∧
      D.IsTorusAut (ggGamma K hN).range ∧ 0 < c ∧
      (∀ v, wt (D.el v) = c * LinTwoTv.hamWt v) ∧
      (∀ (α : MulAut K) k, wt (α k) = wt k) ∧ s + 1 = n := by
  obtain ⟨d, F, hfield, hfin, hchar, θ, e, hd, hF, he, hinner⟩ :=
    native_linear_equiv_of_innerDiagOnLabel hBs hcard hn hz hz1 hN hker hBstar hS hK
  letI : Field F := hfield
  letI : Finite F := hfin
  letI : CharP F 2 := hchar
  have hdim := native_linear_half_dim_eq_of_card_bstar hF e
    hBs hcard hz hz1 hN hker hBstar hinner
  have hAr := P9_Wa_card_range hBs hcard hz hz1 hN hker
  have hr : 3 ^ (d / 2) ≤ Nat.card (ggGamma K hN).range := by rw [hdim, hAr]
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.property b.property)
  have hBp : ∀ b : Bs, b ^ 3 = 1 := by
    intro b
    apply Subtype.ext
    simpa using hBs.2 b b.property
  have hA : IsElemAbelian 3 (ggGamma K hN).range :=
    isElemAbelian_range hBc hBp (ggGamma K hN)
  have hAI : ∀ α ∈ (ggGamma K hN).range, ∃ β ∈ Set.range (conjAut d F),
      ∀ k : K, β (ggQuotHom θ k) = ggQuotHom θ (α k) := by
    intro α hα
    refine ⟨MulAut.congr e α, hinner α hα, fun k => ?_⟩
    rw [← he, ← he]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hkerψ : (ggQuotHom θ).ker ≤ Subgroup.center K := by rw [ker_ggQuotHom]
  obtain ⟨s, c, D, wt, hZ, hTA, hc, hw, hwt⟩ := LinTwoTB.exists_data hF (by omega : 6 ≤ d)
    (ggQuotHom θ) (ggQuotHom_surjective θ) hkerψ hK.1 (ggGamma K hN).range hA hAI hr
  let t : Multiplicative (Fin s → ZMod 3) →* MulAut K :=
    (MulAut.conj : K →* MulAut K).comp D.ι
  have ht : Function.Injective t := fun v w h => D.inj (hZ _ _ h)
  have htr : t.range = (ggGamma K hN).range := by
    ext α
    rw [hTA]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨toAdd v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨ofAdd v, rfl⟩
  have hcs : Nat.card t.range = 3 ^ s := by
    rw [← Nat.card_congr (MonoidHom.ofInjective ht).toEquiv]
    change Nat.card (Fin s → ZMod 3) = _
    simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  rw [htr, hAr] at hcs
  have hs : n - 1 = s := Nat.pow_right_injective (by decide : 1 < 3) hcs
  exact ⟨s, c, D, wt, hZ, hTA, hc, hw, hwt, by rcases hn with rfl | rfl <;> omega⟩

end CFSG.StandardType.FrameRoute

end
