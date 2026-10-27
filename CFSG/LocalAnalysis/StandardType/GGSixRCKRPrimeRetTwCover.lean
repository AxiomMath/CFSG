module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTwStep
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover6Aux1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTwCoverAux

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.Timmesfeld
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped commutatorElement

theorem rckRet_tw_cover
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    {a : Fin τ.rank → GGLˣ} {i : KernelComponent (rootCharHom a)}
    {β : Fin 6 → Fin τ.rank → ℤ} (hβroot : ∀ b, IsRoot τ (β b))
    (hΨβ : componentRoots (rootCharHom a) i = rootsOfFam β Set.univ)
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    {θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL} (hθ : RetCompSpec β ι θ)
    (hRH : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ RetH τ β)
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hquasi : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {h : ℕ} (hh : 0 < h) (hq : S.D.q = 2 ^ h)
    {p₁ : ℕ} (SK : LangSetup Tag.E6 GGL p₁) (hSKq : SK.D.q = 2 ^ h)
    (hSKΦ : SK.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT h))
    (hρΨ : ∀ γ ∈ rootsOfFam β Set.univ, S.ρ γ ∈ rootsOfFam β Set.univ)
    (hρ : ∀ γ ∈ rootsOfFam β Set.univ, SK.ρ (ι γ) = ι (S.ρ γ)) :
    ∃ φ : twistedE6Group 2 h →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
      Function.Surjective φ ∧ φ.ker ≤ Subgroup.center (twistedE6Group 2 h) ∧
      ∀ x : twistedE6Group 2 h, rckRetKappa θ hRH (φ x) =
        SK.D.g0⁻¹ * (show ModGL Tag.E6 GGL from rckTw6_iota h (rckTw6_psi h hh x)) * SK.D.g0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPkg : GGLangPkg SK.D (rckTw6_iota h) := rckTw6_langPkg SK h hh hSKΦ
  have hΓSK : SK.D.Γ = (show Subgroup (ModGL Tag.E6 GGL) from (rckTw6_iota h).range).map
      (MulAut.conj SK.D.g0⁻¹).toMonoidHom := rckTw6_Gamma SK h hSKΦ hPkg
  have hqSK : SK.D.q = S.D.q := by rw [hSKq, ← hq]
  have hstepgen := rckRet_theta_step_gen S SK hqSK hι hθ hρΨ hρ
  have hHleadj : RetH τ β ≤ adjointGroup τ GGL := by
    rw [RetH]
    exact iSup₂_le fun γ _ => rootSubgroup_le_adjointGroup γ
  haveI hMperf : Group.IsPerfect (twistedE6Group 2 h) :=
    fixedGroup_isPerfect_of_four_le_card (frobQ 2 h) (frobQ_frobQ 2 h hh)
      (four_le_card_galoisField 2 h hh)
  have hψsurj : Function.Surjective (rckTw6_psi h hh) :=
    (MulEquiv.subgroupCongr (rckTw6_hRR h hh)).surjective.comp
      (twistedE6Isogeny_surjective 2 h hh)
  obtain ⟨φ₀, hφ₀mem, hθφ₀, hfix, hkerΨ⟩ :=
    rckTc_pack hτ S hβroot hΨβ hι hθ hh hq SK hSKq hSKΦ hρΨ hρ
  have hrange_model : φ₀.range ≤ S.D.model := by
    rintro y ⟨x, rfl⟩
    rw [S.D.mem_model]
    exact ⟨hHleadj (hφ₀mem x), hfix x⟩
  have hperfRange : ⁅φ₀.range, φ₀.range⁆ = φ₀.range := by
    apply Subgroup.isPerfect_iff.1
    refine Group.isPerfect_def.2 ?_
    have h1 := congrArg (Subgroup.map φ₀.rangeRestrict) hMperf.commutator_eq_top
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective φ₀.rangeRestrict φ₀.rangeRestrict_surjective] at h1
    rw [commutator_def]
    exact h1
  have hrange_le_Γ : φ₀.range ≤ S.D.Γ := by
    calc φ₀.range = ⁅φ₀.range, φ₀.range⁆ := hperfRange.symm
      _ ≤ ⁅S.D.model, S.D.model⁆ := Subgroup.commutator_mono hrange_model hrange_model
  have hratroots : rationalRoots S.ρ (rootCharHom a) i = rootsOfFam β Set.univ := by
    ext γ
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      induction k with
      | zero => simpa [hΨβ] using hδ
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hρΨ _ ih
    · intro hγ
      exact ⟨0, γ, by rwa [hΨβ], rfl⟩
  let Aspan : Subgroup (ModGL τ GGL) := rationalSpan S.ρ S.Γ (rootCharHom a) i
  have hAspan : Aspan = RetH τ β ⊓ S.Γ := by
    change rootSpan τ GGL (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.Γ =
      rootSpan τ GGL (rootsOfFam β Set.univ) ⊓ S.Γ
    rw [hratroots]
  have hAspan_le_H : Aspan ≤ RetH τ β := by
    rw [hAspan]
    exact inf_le_left
  let R : Subgroup (ModGL τ GGL) := rationalComponent S.ρ S.Γ (rootCharHom a) i
  have hcomm_le_H : ⁅Aspan, Aspan⁆ ≤ RetH τ β :=
    Subgroup.commutator_le.2 fun x hx y hy => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hAspan_le_H hx) (hAspan_le_H hy))
        (inv_mem (hAspan_le_H hx))) (inv_mem (hAspan_le_H hy))
  have hRperf : ⁅R, R⁆ = R := by
    have h := congrArg (Subgroup.map (Subgroup.subtype R)) hquasi.1.commutator_eq_top
    rwa [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      Subgroup.range_subtype] at h
  have hR_le_A : R ≤ Aspan := by
    change ⁅Aspan, Aspan⁆ ≤ Aspan
    exact Subgroup.commutator_le.2 fun x hx y hy => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hR_le_H : R ≤ RetH τ β := hR_le_A.trans hAspan_le_H
  have hrange_le_A : φ₀.range ≤ Aspan := by
    rw [hAspan]
    exact le_inf (fun y hy => by rcases hy with ⟨x, rfl⟩; exact hφ₀mem x) hrange_le_Γ
  have hrange_le_R : φ₀.range ≤ R := by
    change φ₀.range ≤ ⁅Aspan, Aspan⁆
    calc φ₀.range = ⁅φ₀.range, φ₀.range⁆ := hperfRange.symm
      _ ≤ _ := Subgroup.commutator_mono hrange_le_A hrange_le_A
  have hθA_model : (Aspan.subgroupOf (RetH τ β)).map θ ≤ SK.D.model := by
    rintro y ⟨a, ha, rfl⟩
    have haA : (a : ModGL τ GGL) ∈ Aspan := Subgroup.mem_subgroupOf.1 ha
    have haΓ : (a : ModGL τ GGL) ∈ S.D.Γ := (hAspan ▸ haA).2
    rw [SK.D.mem_model]
    refine ⟨?_, ?_⟩
    · rw [← hθ.2.1]
      exact ⟨a, rfl⟩
    · obtain ⟨hxmem, hxstep⟩ := hstepgen a
      have hfixa : S.D.step (a : ModGL τ GGL) = (a : ModGL τ GGL) :=
        ((S.D.mem_model).1 (LangSetup.Γ_le_model S haΓ)).2
      have h1 : SK.D.step (θ a) = θ a := by
        have h2 : SK.D.step (θ a) = θ ⟨S.D.step (a : ModGL τ GGL), hxmem⟩ := hxstep.symm
        have h3 : (⟨S.D.step (a : ModGL τ GGL), hxmem⟩ : ↥(RetH τ β)) = a := by
          apply Subtype.ext
          exact hfixa
        rw [h2, h3]
      exact h1
  have hsub : R.subgroupOf (RetH τ β) =
      ⁅Aspan.subgroupOf (RetH τ β), Aspan.subgroupOf (RetH τ β)⁆ := by
    change (⁅Aspan, Aspan⁆).subgroupOf (RetH τ β) = _
    apply Subgroup.map_injective (Subgroup.subtype_injective (RetH τ β))
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAspan_le_H,
      Subgroup.map_subgroupOf_eq_of_le hcomm_le_H]
  have hθR_le : (R.subgroupOf (RetH τ β)).map θ ≤ SK.D.Γ := by
    rw [hsub, Subgroup.map_commutator]
    calc ⁅(Aspan.subgroupOf (RetH τ β)).map θ, (Aspan.subgroupOf (RetH τ β)).map θ⁆
        ≤ ⁅SK.D.model, SK.D.model⁆ := Subgroup.commutator_mono hθA_model hθA_model
      _ = SK.D.Γ := rfl
  have key : ∀ r ∈ R, ∃ x : twistedE6Group 2 h,
      ∃ hm : r * (φ₀ x)⁻¹ ∈ RetH τ β, θ ⟨r * (φ₀ x)⁻¹, hm⟩ = 1 := by
    intro r hr
    have hrH : r ∈ RetH τ β := hR_le_H hr
    have hθrΓ : θ ⟨r, hrH⟩ ∈ SK.D.Γ :=
      hθR_le (Subgroup.mem_map_of_mem θ (Subgroup.mem_subgroupOf.2 hr))
    rw [hΓSK] at hθrΓ
    obtain ⟨c, hcrange, hceq⟩ := hθrΓ
    obtain ⟨y, rfl⟩ := hcrange
    obtain ⟨x, rfl⟩ := hψsurj y
    have hceq' : SK.D.g0⁻¹ * (show ModGL Tag.E6 GGL from
        rckTw6_iota h (rckTw6_psi h hh x)) * SK.D.g0 = θ ⟨r, hrH⟩ := by
      have hceq1 : (MulAut.conj SK.D.g0⁻¹).toMonoidHom
          (show ModGL Tag.E6 GGL from rckTw6_iota h (rckTw6_psi h hh x)) = θ ⟨r, hrH⟩ :=
        hceq
      change (MulAut.conj SK.D.g0⁻¹)
        (show ModGL Tag.E6 GGL from rckTw6_iota h (rckTw6_psi h hh x)) = θ ⟨r, hrH⟩ at hceq1
      rw [MulAut.conj_apply, inv_inv] at hceq1
      exact hceq1
    refine ⟨x, mul_mem hrH (inv_mem (hφ₀mem x)), ?_⟩
    have hr_eq : θ ⟨r, hrH⟩ = θ ⟨φ₀ x, hφ₀mem x⟩ := by
      rw [← hceq', ← hθφ₀ x]
    change θ (⟨r, hrH⟩ * ⟨φ₀ x, hφ₀mem x⟩⁻¹) = 1
    rw [map_mul, map_inv, hr_eq, mul_inv_cancel]
  have hR_le_range : R ≤ φ₀.range := by
    rw [← hRperf]
    refine Subgroup.commutator_le.2 ?_
    intro r₁ hr₁ r₂ hr₂
    obtain ⟨x₁, hm₁, heq₁⟩ := key r₁ hr₁
    obtain ⟨x₂, hm₂, heq₂⟩ := key r₂ hr₂
    have hc₁ : (⟨r₁ * (φ₀ x₁)⁻¹, hm₁⟩ : ↥(RetH τ β)) ∈
        Subgroup.center ↥(RetH τ β) := hθ.2.2.1 _ heq₁
    have hc₂ : (⟨r₂ * (φ₀ x₂)⁻¹, hm₂⟩ : ↥(RetH τ β)) ∈
        Subgroup.center ↥(RetH τ β) := hθ.2.2.1 _ heq₂
    have hr₁eq : (⟨r₁, hR_le_H hr₁⟩ : ↥(RetH τ β)) =
        (⟨φ₀ x₁, hφ₀mem x₁⟩ : ↥(RetH τ β)) * ⟨r₁ * (φ₀ x₁)⁻¹, hm₁⟩ := by
      apply Subtype.ext
      change r₁ = φ₀ x₁ * (r₁ * (φ₀ x₁)⁻¹)
      have hcomm1 := congrArg Subtype.val
        (Subgroup.mem_center_iff.1 hc₁ (⟨φ₀ x₁, hφ₀mem x₁⟩ : ↥(RetH τ β)))
      calc r₁ = (r₁ * (φ₀ x₁)⁻¹) * φ₀ x₁ := by group
        _ = φ₀ x₁ * (r₁ * (φ₀ x₁)⁻¹) := hcomm1.symm
    have hr₂eq : (⟨r₂, hR_le_H hr₂⟩ : ↥(RetH τ β)) =
        (⟨φ₀ x₂, hφ₀mem x₂⟩ : ↥(RetH τ β)) * ⟨r₂ * (φ₀ x₂)⁻¹, hm₂⟩ := by
      apply Subtype.ext
      change r₂ = φ₀ x₂ * (r₂ * (φ₀ x₂)⁻¹)
      have hcomm2 := congrArg Subtype.val
        (Subgroup.mem_center_iff.1 hc₂ (⟨φ₀ x₂, hφ₀mem x₂⟩ : ↥(RetH τ β)))
      calc r₂ = (r₂ * (φ₀ x₂)⁻¹) * φ₀ x₂ := by group
        _ = φ₀ x₂ * (r₂ * (φ₀ x₂)⁻¹) := hcomm2.symm
    have hcomm : (⁅(⟨r₁, hR_le_H hr₁⟩ : ↥(RetH τ β)), ⟨r₂, hR_le_H hr₂⟩⁆ :
        ↥(RetH τ β)) =
        ⁅(⟨φ₀ x₁, hφ₀mem x₁⟩ : ↥(RetH τ β)), ⟨φ₀ x₂, hφ₀mem x₂⟩⁆ := by
      rw [hr₁eq, hr₂eq]
      exact commutatorElement_mul_mul_of_mem_center _ _ hc₁ hc₂
    have hcomm' : ⁅r₁, r₂⁆ = ⁅φ₀ x₁, φ₀ x₂⁆ := by
      have h := congrArg (Subgroup.subtype (RetH τ β)) hcomm
      rw [map_commutatorElement, map_commutatorElement] at h
      change ⁅r₁, r₂⁆ = ⁅φ₀ x₁, φ₀ x₂⁆ at h
      exact h
    rw [hcomm']
    exact hperfRange ▸ Subgroup.commutator_mem_commutator
      (show φ₀ x₁ ∈ φ₀.range from ⟨x₁, rfl⟩)
      (show φ₀ x₂ ∈ φ₀.range from ⟨x₂, rfl⟩)
  let φ : twistedE6Group 2 h →* ↥R := φ₀.codRestrict R fun x => hrange_le_R ⟨x, rfl⟩
  have hφsurj : Function.Surjective φ := by
    rintro ⟨r, hr⟩
    obtain ⟨x, hx⟩ := hR_le_range hr
    exact ⟨x, Subtype.ext hx⟩
  have hφker : φ.ker ≤ Subgroup.center (twistedE6Group 2 h) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : φ₀ x = 1 := congrArg Subtype.val hx
    have hx1cen := hkerΨ x hx1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hx1cen y.1
  refine ⟨φ, hφsurj, hφker, ?_⟩
  intro x
  rw [rckRetKappa_apply]
  have h1 : (⟨φ₀ x, hφ₀mem x⟩ : ↥(RetH τ β)) = ⟨(φ x : ModGL τ GGL), hRH (φ x).2⟩ := by
    apply Subtype.ext
    rfl
  rw [← h1, hθφ₀ x]

end CFSG.StandardType.RCKRP

end
