module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcE6Inv
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E6GraphConj
import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcTwE6
import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcOuterR
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwKillsRoot
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcSixE
import CFSG.GH74.GLS.Stage1.Main.BrTwoClassE
import CFSG.RankThree.PartOne.CTP.StrongPG2
import CFSG.LocalAnalysis.SteinbergCEOddResidualE6GraphCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.Burgoyne.E2 (e6GraphSign)

private theorem fixed_of_conj_image {G : Type*} [Group G] (ψ β : MulAut G) {a : G}
    (h : (ψ * β * ψ⁻¹) a = a) : β (ψ.symm a) = ψ.symm a := by
  have h' : ψ (β (ψ.symm a)) = a := by
    simpa only [MulAut.mul_apply, MulAut.inv_apply] using h
  apply ψ.injective
  rw [h', ψ.apply_symm_apply]

private theorem fixed_of_generators_e6 {G : Type} [Group G] [Finite G] [Finite (MulAut G)]
    (E : Subgroup (MulAut G))
    {x : MulAut G} {h : G} (hxE : x ∈ E) (hhE : MulAut.conj h ∈ E)
    (hx2 : x * x = 1) (hconj2 : MulAut.conj h * MulAut.conj h = 1)
    (hcomm : x * MulAut.conj h = MulAut.conj h * x)
    (hxne : x ≠ 1) (hhne : MulAut.conj h ≠ 1) (hne : MulAut.conj h ≠ x)
    (h4 : Nat.card E = 4) {a : G} (hfixx : x a = a) (hfixh : MulAut.conj h a = a) :
    ∀ e ∈ E, e a = a := by
  obtain ⟨hmem, -, -, hcard⟩ :=
    CFSG.GH74.GLS.Stage1.Main.four_of_invols (u₁ := MulAut.conj h) (u₂ := x)
      hconj2 hx2 hcomm.symm hhne hxne hne
  have hEeq : zpowers (MulAut.conj h) ⊔ zpowers x = E :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (zpowers_le.2 hhE) (zpowers_le.2 hxE))
      (by rw [hcard, h4])
  intro e he
  rw [← hEeq] at he
  rcases hmem e he with rfl | rfl | rfl | rfl
  · rfl
  · exact hfixh
  · exact hfixx
  · rw [MulAut.mul_apply, hfixx, hfixh]


theorem exists_rElement_commute_involution_f4
    {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) {h : ↥(adjointGroup .F4 K)}
    (hh : h ^ 2 = 1) :
    ∃ u : ↥(adjointGroup .F4 K), u ≠ 1 ∧ (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧ Commute u h := by
  classical
  have : Fintype K := Fintype.ofFinite K
  by_cases h1 : h = 1
  · subst h
    let i : Fin Tag.F4.rank := ⟨0, by decide⟩
    have hu1 : (⟨xUnit .F4 K i 1, xUnit_mem_adjointGroup i 1⟩ : ↥(adjointGroup .F4 K)) ≠ 1 := by
      intro hc
      have hc' : (xUnit .F4 K i 1 : ModGL .F4 K) = 1 := congrArg Subtype.val hc
      have h2 : xOp .F4 K i (1 : K) = xOp .F4 K i (0 : K) := by
        have h3 := congrArg (fun z : ModGL .F4 K => (z : Module.End K (RootModule .F4 K))) hc'
        simpa only [coe_xUnit, xOp_zero, Units.val_one] using h3
      exact one_ne_zero (xOp_injective i h2)
    refine ⟨⟨xUnit .F4 K i 1, xUnit_mem_adjointGroup i 1⟩, hu1, ⟨1, ?_⟩, by simp⟩
    have : CharP K (ringChar K) := ringChar.charP K
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa using CFSG.RankThree.PartOne.StrongP.xUnit_pow_char (K := K) (p := ringChar K) .F4 i
  · have hh1 : orderOf h = 2 := orderOf_eq_prime hh h1
    have hq : CFSG.IsQuasisimple ↥(adjointGroup .F4 K) :=
      CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 K
    have : IsSimpleGroup ↥(adjointGroup .F4 K) :=
      CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
        ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
          QuotientGroup.quotientBot).symm
    have : Finite (ModGL .F4 K) := finite_modGL
    have : Finite ↥(adjointGroup .F4 K) := Subtype.finite
    have hnonab : ∃ a b : ↥(adjointGroup .F4 K), a * b ≠ b * a := by
      by_contra hc
      apply h1
      have hz : h ∈ Subgroup.center ↥(adjointGroup .F4 K) :=
        Subgroup.mem_center_iff.2 fun g => by_contra fun hne => hc ⟨g, h, hne⟩
      rwa [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
    exact exists_rElement_commute_involution_of_four hnonab
      (fun A hA hcard => exists_rElement_commute_four (Or.inl rfl) hK hA hcard) hh1

theorem exists_rElement_fixed_graph_inv
    {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) (h : ↥(adjointGroup TwistTag.E6.tag K))
    (hh : h ^ 2 = 1) (hγh : diagramConjAut TwistTag.E6 K h = h) :
    ∃ u : ↥(adjointGroup TwistTag.E6.tag K), u ≠ 1 ∧ (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧
      Commute u h ∧ diagramConjAut TwistTag.E6 K u = u := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hΓ : (h : ModGL TwistTag.E6.tag K) ∈
      twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
    rw [mem_twistedFixedGroup_iff_twistHom]
    refine ⟨h.2, ?_⟩
    rw [twistHom_apply]
    have h1m : Units.map (entrywiseHom (RingHom.id K)) (h : ModGL TwistTag.E6.tag K) =
        (h : ModGL TwistTag.E6.tag K) := Units.ext (entrywise_id _)
    rw [h1m]
    exact (coe_diagramConjAut TwistTag.E6 K h).symm.trans (congrArg Subtype.val hγh)
  let Ψ : twistedFixedGroup TwistTag.E6 K (RingHom.id K) ≃* adjointGroup Tag.F4 K :=
    CFSG.HardMathSupport.Lang.AnisoE6.e6FixedF4EquivAll K
  let hF : ↥(adjointGroup Tag.F4 K) := Ψ ⟨h, hΓ⟩
  have hF2 : hF ^ 2 = 1 := by
    have h1 : (⟨h, hΓ⟩ : twistedFixedGroup TwistTag.E6 K (RingHom.id K)) ^ 2 = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hh)
    rw [show hF = Ψ ⟨h, hΓ⟩ from rfl, ← map_pow, h1, map_one]
  obtain ⟨uF, huF1, ⟨n, huFn⟩, huFh⟩ :=
    exists_rElement_commute_involution_f4 hK hF2
  let v : twistedFixedGroup TwistTag.E6 K (RingHom.id K) := Ψ.symm uF
  let u : ↥(adjointGroup TwistTag.E6.tag K) :=
    ⟨v, ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K (RingHom.id K)).1 v.2).1⟩
  have hΨv : Ψ v = uF := Ψ.apply_symm_apply uF
  refine ⟨u, ?_, ⟨n, ?_⟩, ?_, ?_⟩
  · intro hu
    apply huF1
    rw [← hΨv]
    have hv : v = 1 := Subtype.ext (by simpa [u] using congrArg Subtype.val hu)
    rw [hv, map_one]
  · have h1 : v ^ (ringChar K ^ n) = 1 := by
      apply Ψ.injective
      rw [map_pow, hΨv, huFn, map_one]
    exact Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact congrArg Subtype.val h1)
  · have hcommv : Commute v (⟨h, hΓ⟩ : twistedFixedGroup TwistTag.E6 K (RingHom.id K)) := by
      have hsymm : Ψ.symm hF = ⟨h, hΓ⟩ := by
        rw [show hF = Ψ ⟨h, hΓ⟩ from rfl, MulEquiv.symm_apply_apply]
      have h := congrArg Ψ.symm huFh.eq
      rw [map_mul, map_mul, hsymm] at h
      exact h
    have hmul := congrArg Subtype.val hcommv.eq
    simp only [Subgroup.coe_mul] at hmul
    exact Subtype.ext hmul
  · have hfix : twistHom TwistTag.E6 K (RingHom.id K) (v : ModGL TwistTag.E6.tag K) =
        (v : ModGL TwistTag.E6.tag K) :=
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K (RingHom.id K)).1 v.2).2
    refine Subtype.ext ?_
    rw [coe_diagramConjAut]
    change diagramMap TwistTag.E6 K * (v : ModGL TwistTag.E6.tag K) *
      (diagramMap TwistTag.E6 K)⁻¹ = (v : ModGL TwistTag.E6.tag K)
    have h1m : Units.map (entrywiseHom (RingHom.id K)) (v : ModGL TwistTag.E6.tag K) =
        (v : ModGL TwistTag.E6.tag K) := Units.ext (entrywise_id _)
    rw [← h1m, ← twistHom_apply, h1m]
    exact hfix


theorem exists_rElement_fixed_graphField_inv {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (q : ℕ) (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (hK : ringChar K ≠ 2)
    (h : ↥(adjointGroup TwistTag.E6.tag K)) (hh : h ^ 2 = 1)
    (hρh : (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ) h = h) :
    ∃ u : ↥(adjointGroup TwistTag.E6.tag K), u ≠ 1 ∧ (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧
      Commute u h ∧
        (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ) u = u := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hρ : ∀ u : ↥(adjointGroup TwistTag.E6.tag K),
      (((diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ) u :
        adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) =
        diagramMap TwistTag.E6 K *
          Units.map (entrywiseHom σ.toRingHom) (u : ModGL TwistTag.E6.tag K) *
            (diagramMap TwistTag.E6 K)⁻¹ := by
    intro u
    rw [MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut]
  let e4 : Fin TwistTag.E6.tag.rank := CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset.e4
  let x₀ : ↥(adjointGroup TwistTag.E6.tag K) :=
    ⟨xUnit TwistTag.E6.tag K e4 1, xUnit_mem_adjointGroup e4 1⟩
  have hx₀ne : x₀ ≠ 1 := by
    intro hc
    have hc' : (xUnit TwistTag.E6.tag K e4 1 : ModGL TwistTag.E6.tag K) = 1 :=
      congrArg Subtype.val hc
    have h3 : (xOp TwistTag.E6.tag K e4 (1 : K) : Module.End K (RootModule TwistTag.E6.tag K)) =
        1 := by
      have h4 := congrArg (fun z : ModGL TwistTag.E6.tag K =>
        (z : Module.End K (RootModule TwistTag.E6.tag K))) hc'
      simpa only [coe_xUnit, Units.val_one] using h4
    have h2 : xOp TwistTag.E6.tag K e4 (1 : K) = xOp TwistTag.E6.tag K e4 (0 : K) := by
      rw [xOp_zero]; exact h3
    exact one_ne_zero (xOp_injective e4 h2)
  have hx₀pow : x₀ ^ (ringChar K ^ 1) = 1 := by
    have : CharP K (ringChar K) := ringChar.charP K
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa using CFSG.RankThree.PartOne.StrongP.xUnit_pow_char
      (K := K) (p := ringChar K) TwistTag.E6.tag e4
  have hx₀diag : diagramConjAut TwistTag.E6 K x₀ = x₀ := by
    refine Subtype.ext ?_
    rw [coe_diagramConjAut]
    simp only [x₀, e4]
    rw [← CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset.xUnit_e4_commute_diagramMap (K := K) 1]
    group
  have hx₀entry : ∀ (δ : K ≃+* K),
      entrywiseAdjointAut TwistTag.E6.tag δ x₀ = x₀ := by
    intro δ
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    refine Units.ext ?_
    change entrywise (τ := TwistTag.E6.tag) δ.toRingHom
        (↑(xUnit TwistTag.E6.tag K e4 1)) = ↑(xUnit TwistTag.E6.tag K e4 1)
    rw [coe_xUnit, entrywise_xOp, map_one]
  by_cases h1 : h = 1
  · subst h
    refine ⟨x₀, hx₀ne, ⟨1, hx₀pow⟩, by simp, ?_⟩
    rw [MulAut.mul_apply, hx₀entry σ, hx₀diag]
  ·
    have hq2 : 2 ≤ q := by
      have hK1 : 1 < Nat.card K := Finite.one_lt_card
      have h1q : 1 < q ^ 2 := by rwa [← hKq]
      nlinarith
    obtain ⟨hpr, f, hf1, hqf⟩ :=
      CFSG.LieType.SeitzGeneration.ExcHighThree.exists_pow_ringChar_of_card_sq K q hKq hq2
    set p := ringChar K with hp_def
    have : Fact p.Prime := ⟨hpr⟩
    have hcharL : CharP (AlgebraicClosure K) p :=
      charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
    let Fr : AlgebraicClosure K →+* AlgebraicClosure K :=
      iterateFrobenius (AlgebraicClosure K) p f
    have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => by rw [iterateFrobenius_def]
    have hσfix : twistHom TwistTag.E6 K σ.toRingHom (h : ModGL TwistTag.E6.tag K) = h := by
      rw [twistHom_apply]
      exact (hρ h).symm.trans (congrArg Subtype.val hρh)
    have hΓσ : (h : ModGL TwistTag.E6.tag K) ∈
        twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
      (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).2 ⟨h.2, hσfix⟩
    let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
    have hcomp : ι.comp σ.toRingHom = Fr.comp ι := by
      ext c
      simp [hσ c, hFr, hqf, map_pow]
    let x : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
      baseChangeGL ι (h : ModGL TwistTag.E6.tag K)
    have hxad : x ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
      baseChangeGL_mem_adjointGroup ι h.2
    have hxF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr x = x := by
      rw [show x = baseChangeGL ι (h : ModGL TwistTag.E6.tag K) from rfl,
        twistHom_baseChangeGL ι hcomp, hσfix]
    have hx2 : x ^ 2 = 1 := by
      have hh' : (h : ModGL TwistTag.E6.tag K) ^ 2 = 1 := by
        simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hh
      rw [show x = baseChangeGL ι (h : ModGL TwistTag.E6.tag K) from rfl, ← map_pow,
        hh', map_one]
    have hK' : Nat.card K = (p ^ f) ^ 2 := by rw [← hqf, hKq]
    have hσ' : ∀ c, σ c = c ^ (p ^ f) := by intro c; rw [hσ c, hqf]
    obtain ⟨u₀, hu₀C, hu₀x⟩ :=
      CFSG.LieType.SeitzGeneration.ExcHighThree.twisted_descent_E6 hpr hf1 K hK' σ hσ'
        Fr hFr Nat.prime_two (by norm_num) hxad hxF hx2
    have hu₀h : u₀ = (h : ModGL TwistTag.E6.tag K) := by
      apply baseChangeGL_injective (f := ι)
      rw [hu₀x]
    have hmemC0 : (h : ModGL TwistTag.E6.tag K) ∈ twistedE6RootGroup K σ := hu₀h ▸ hu₀C
    obtain ⟨hsimple, hnonabC0, -⟩ :=
      odd_diagram_field_fixed_p_components TwistTag.E6 K hK σ
    have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
    have : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
    have : IsSimpleGroup ↥(twistedE6RootGroup K σ) := hsimple
    let h₀ : ↥(twistedE6RootGroup K σ) := ⟨h, hmemC0⟩
    have hh₀ne : h₀ ≠ 1 := by
      intro hc
      exact h1 (Subtype.ext (by simpa [h₀] using congrArg Subtype.val hc))
    have hh₀2 : h₀ ^ 2 = 1 :=
      Subtype.ext (by simpa [h₀] using congrArg Subtype.val hh)
    have hh₀o : orderOf h₀ = 2 := orderOf_eq_prime hh₀2 hh₀ne
    have hfour : ∀ A : Subgroup ↥(twistedE6RootGroup K σ),
        (∀ x ∈ A, x ^ 2 = 1) → Nat.card A = 2 ^ 2 →
        ∃ u : ↥(twistedE6RootGroup K σ), u ≠ 1 ∧
          (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧ ∀ x ∈ A, Commute u x := by
      intro A hA hAcard
      let A' : Subgroup (ModGL TwistTag.E6.tag K) := A.map (twistedE6RootGroup K σ).subtype
      have hA'C : A' ≤ twistedE6RootGroup K σ := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      have hA'2 : ∀ x ∈ A', x ^ 2 = 1 := by
        rintro _ ⟨x, hx, rfl⟩
        simpa using congrArg Subtype.val (hA x hx)
      have hA'card : Nat.card A' = 2 ^ 2 := by
        rw [Subgroup.card_map_of_injective (twistedE6RootGroup K σ).subtype_injective,
          hAcard]
      obtain ⟨u, huC, hu1, hun, hucomm⟩ :=
        exists_rElement_commute_four_twistedE6 σ q hσ hKq hK hA'C hA'2 hA'card
      refine ⟨⟨u, huC⟩, ?_, ?_, ?_⟩
      · intro hc
        exact hu1 (congrArg Subtype.val hc)
      · obtain ⟨n, hn⟩ := hun
        exact ⟨n, Subtype.ext (by simpa using hn)⟩
      · intro y hy
        have hcomm := hucomm (y : ModGL TwistTag.E6.tag K)
          (Subgroup.mem_map_of_mem (twistedE6RootGroup K σ).subtype hy)
        exact Subtype.ext hcomm.eq
    obtain ⟨u', hu'1, ⟨n, hu'n⟩, hu'h⟩ :=
      exists_rElement_commute_involution_of_four hnonabC0 hfour hh₀o
    let u : ↥(adjointGroup TwistTag.E6.tag K) :=
      ⟨u', (twistedFixedGroup_le_adjointGroup TwistTag.E6 K σ.toRingHom)
        ((graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom) u'.2)⟩
    refine ⟨u, ?_, ⟨n, ?_⟩, ?_, ?_⟩
    · intro hc
      exact hu'1 (Subtype.ext (by simpa [u] using congrArg Subtype.val hc))
    · have hu'n' : (u' : ModGL TwistTag.E6.tag K) ^ (ringChar K ^ n) = 1 := by
        rw [← Subgroup.coe_pow]
        simpa only [Subgroup.coe_one] using congrArg Subtype.val hu'n
      exact Subtype.ext (by simpa [u, hp_def] using hu'n')
    · have hmul := congrArg Subtype.val hu'h.eq
      simp only [Subgroup.coe_mul] at hmul
      exact Subtype.ext hmul
    · refine Subtype.ext ?_
      rw [hρ u]
      rw [← twistHom_apply]
      exact CFSG.LieType.SeitzGeneration.ExcHighThree.twistedE6RootGroup_fix K σ
        (u' : ModGL TwistTag.E6.tag K) u'.2

theorem exists_fixed_rElement_four_e6_or_signedGraph
    {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (E : Subgroup (MulAut ↥(adjointGroup .E6 K)))
    (hE : CFSG.Open.IsElemAbelian 2 E) (h4 : Nat.card E = 4) :
    (∃ y : ↥(adjointGroup .E6 K), y ≠ 1 ∧ (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) ∧
      ∀ e ∈ E, e y = y) ∨
    ∃ (x : MulAut ↥(adjointGroup .E6 K)) (h : ↥(adjointGroup .E6 K))
      (δ δ' : MulAut ↥(adjointGroup .E6 K)),
      x ∈ E ∧ MulAut.conj h ∈ E ∧ h ≠ 1 ∧ h ^ 2 = 1 ∧ x h = h ∧
      δ * x * δ⁻¹ = rootDiagAut TwistTag.E6.tag K (e6GraphSign K) * diagramConjAut TwistTag.E6 K ∧
      δ' * (x * MulAut.conj h) * δ'⁻¹ =
        rootDiagAut TwistTag.E6.tag K (e6GraphSign K) * diagramConjAut TwistTag.E6 K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL .E6 K) := finite_modGL
  have : Finite ↥(adjointGroup .E6 K) := Subtype.finite
  have : Finite (MulAut ↥(adjointGroup .E6 K)) :=
    Finite.of_injective (fun e : MulAut ↥(adjointGroup .E6 K) => (e : _ → _))
      DFunLike.coe_injective
  have hZ : ∀ c : ↥(adjointGroup .E6 K), MulAut.conj c = 1 → c = 1 := by
    intro c hc
    have hcZ : c ∈ Subgroup.center ↥(adjointGroup .E6 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : c * g * c⁻¹ = g := by
        have := congrArg (fun φ : MulAut ↥(adjointGroup .E6 K) => φ g) hc
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      calc g * c = c * g * c⁻¹ * c := by rw [h1]
        _ = c * g := by group
    rwa [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hcZ
  have hconj : Function.Injective
      (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)) :=
    (injective_iff_map_eq_one _).2 hZ
  have hE2 : ∀ e ∈ E, e ^ 2 = 1 := hE.2
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h1m : ∀ x : ModGL .E6 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ0 : exactQ Tag.E6 K 0 = 1 := pow_zero _
  have hQ1 : exactQ Tag.E6 K 1 = diagramMap TwistTag.E6 K := pow_one _
  by_cases hin : ∀ e ∈ E, e ∈ (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut _).range
  ·
    set A := E.comap (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K))
    have hA2 : ∀ a ∈ A, a ^ 2 = 1 := fun a ha =>
      hconj (by rw [map_pow, map_one]; exact hE2 _ ha)
    have hAcard : Nat.card A = 2 ^ 2 := by
      have hmap : A.map (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut _) = E :=
        Subgroup.map_comap_eq_self fun e he => hin e he
      rw [← Subgroup.card_map_of_injective hconj, hmap, h4]
      norm_num
    obtain ⟨u, hu1, hun, hucomm⟩ := exists_rElement_commute_four (Or.inr (Or.inl rfl)) hK hA2 hAcard
    refine Or.inl ⟨u, hu1, hun, fun e he => ?_⟩
    obtain ⟨c, rfl⟩ := hin e he
    have hc : c ∈ A := he
    rw [MulAut.conj_apply, ← (hucomm c hc).eq, mul_inv_cancel_right]
  · obtain ⟨x, hxE, hx⟩ :
        ∃ x ∈ E, x ∉ (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut _).range := by
      by_contra hne
      exact hin fun e he => by_contra fun h => hne ⟨e, he, h⟩
    obtain ⟨-, -, hNF⟩ :=
      ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K
    obtain ⟨Θ, -, hΘ, hker, hsq, hquad⟩ :=
      ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
    have hInn_of_inndiag : ∀ e : MulAut ↥(adjointGroup .E6 K),
        e ∈ CFSG.StandardType.LayerSixE.inndiagAut .E6 K → e ∈ E →
          e ∈ (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut _).range := by
      intro e he hEe
      exact CFSG.StandardType.OrdPInnerExc.mem_inn_of_inndiag_E6 Nat.prime_two
        (Or.inl (by norm_num)) he (hE2 e hEe)
    have hkerInn : ∀ α : MulAut ↥(adjointGroup .E6 K), α ∈ Θ.ker →
        α ∈ CFSG.StandardType.LayerSixE.inndiagAut .E6 K := by
      intro α hα
      obtain ⟨g, a, hga⟩ := (hker α).1 hα
      have hαeq : α = MulAut.conj g * rootDiagAutHom .E6 K a := by
        refine MulEquiv.ext fun u => Subtype.ext ?_
        rw [MulAut.mul_apply, MulAut.conj_apply, hga u]
        change (↑g : ModGL .E6 K) * rootDiagUnit .E6 a * (↑u : ModGL .E6 K) *
            (rootDiagUnit .E6 a)⁻¹ * (↑g)⁻¹ =
          (↑g : ModGL .E6 K) * (↑((rootDiagAut .E6 K a) u) : ModGL .E6 K) * (↑g)⁻¹
        rw [coe_rootDiagAut]
        group
      rw [hαeq, CFSG.StandardType.LayerSixE.inndiagAut]
      exact Subgroup.mul_mem_sup (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
        (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
    by_cases hfield : ∃ y ∈ E, (Θ y).2 = 1 ∧ (Θ y).1 ≠ 1
    ·
      obtain ⟨y, hyE, hy2, hy1⟩ := hfield
      obtain ⟨g, a, σ, ε, hy⟩ := hNF y
      have hΘy := hΘ y g a σ ε hy
      have hε : (ε : ℕ) = 0 := by
        have h1 : ((ε : ℕ) : ZMod (exactE Tag.E6)) = 0 := by
          have h2 := hy2
          rw [hΘy] at h2
          simpa using h2
        fin_cases ε
        · rfl
        · exfalso
          have h2 : (((1 : ℕ) : ZMod 2) = 0) := h1
          exact (by decide : ¬ (((1 : ℕ) : ZMod 2) = 0)) h2
      have hσ1 : σ ≠ 1 := by
        have h2 := hy1
        rw [hΘy] at h2
        exact h2
      have hσ2 : σ ^ 2 = 1 := hsq y g a σ ε hy (hE2 y hyE)
      obtain ⟨f, hp, hKf⟩ := FiniteField.card K (ringChar K)
      have hKc : Nat.card K = ringChar K ^ (f : ℕ) := by
        rw [Nat.card_eq_fintype_card, hKf]
      have hf : 1 ≤ (f : ℕ) := f.pos
      obtain ⟨hev, hσc, -⟩ :=
        hquad (ringChar K) (f : ℕ) hp hf hKc σ hσ2 hσ1
      have he : 1 ≤ (f : ℕ) / 2 := by
        obtain ⟨m, hm⟩ := hev
        omega
      have hKe : Nat.card K = (ringChar K ^ ((f : ℕ) / 2)) ^ 2 := by
        rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hKc]
      obtain ⟨hfieldLang, -⟩ :=
        exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe σ.toRingHom hσc
      obtain ⟨β₀, -, hconjAll⟩ := hfieldLang Tag.E6
      obtain ⟨-, hyconj⟩ := hconjAll g a
      obtain ⟨ψ, hψ, -⟩ := hyconj y
        (fun u => by rw [hy u, hε, hQ0, mul_one, inv_one, mul_one])
        (by rw [← sq]; exact hE2 y hyE)
      have hψe : ψ * y * ψ⁻¹ = entrywiseAdjointAut .E6 σ := by
        refine MulEquiv.ext fun u => Subtype.ext ?_
        rw [coe_entrywiseAdjointAut]
        exact hψ u
      have hyne : y ≠ 1 := by
        rintro rfl
        exact hy1 (by simp)
      have hyorder : orderOf y = 2 := orderOf_eq_prime (hE2 y hyE) hyne
      obtain ⟨z, hzE, hzy⟩ : ∃ z ∈ E, z ∉ zpowers y := by
        by_contra hc
        push Not at hc
        have hle : E ≤ zpowers y := fun e' he' => hc e' he'
        have hcard_le : Nat.card ↥E ≤ Nat.card ↥(zpowers y) :=
          Nat.card_le_card_of_injective (Subgroup.inclusion hle)
            (Subgroup.inclusion_injective hle)
        have hzcard : Nat.card ↥(zpowers y) = 2 := by
          rw [Nat.card_zpowers]
          exact hyorder
        omega
      have hz2 : z ^ 2 = 1 := hE2 z hzE
      have hz1 : z ≠ 1 := by
        intro hc
        exact hzy (by rw [hc]; exact one_mem (zpowers y))
      have hyz : y * z = z * y := hEcomm y hyE z hzE
      have hyzne : y ≠ z := by
        intro hc
        apply hzy
        rw [hc]
        exact mem_zpowers z
      obtain ⟨hmemE, -, -, hcardE⟩ :=
        CFSG.GH74.GLS.Stage1.Main.four_of_invols (hE2 y hyE) hz2 hyz hyne hz1 hyzne
      have hEeq : zpowers y ⊔ zpowers z = E :=
        Subgroup.eq_of_le_of_card_ge
          (sup_le (zpowers_le.2 hyE) (zpowers_le.2 hzE))
          (by rw [hcardE, h4])
      let β : MulAut ↥(adjointGroup .E6 K) := ψ * z * ψ⁻¹
      have hβ2 : β ^ 2 = 1 := by
        have hzsq : z * z = 1 := by rw [← sq]; exact hz2
        change (ψ * z * ψ⁻¹) ^ 2 = 1
        rw [pow_two]
        calc (ψ * z * ψ⁻¹) * (ψ * z * ψ⁻¹) = ψ * (z * z) * ψ⁻¹ := by group
          _ = 1 := by rw [hzsq]; group
      have hβσ : β * entrywiseAdjointAut .E6 σ =
          entrywiseAdjointAut .E6 σ * β := by
        have hσeq : entrywiseAdjointAut .E6 σ = ψ * y * ψ⁻¹ := hψe.symm
        change (ψ * z * ψ⁻¹) * entrywiseAdjointAut .E6 σ =
          entrywiseAdjointAut .E6 σ * (ψ * z * ψ⁻¹)
        rw [hσeq]
        calc (ψ * z * ψ⁻¹) * (ψ * y * ψ⁻¹) = ψ * (z * y) * ψ⁻¹ := by group
          _ = ψ * (y * z) * ψ⁻¹ := by rw [← hyz]
          _ = (ψ * y * ψ⁻¹) * (ψ * z * ψ⁻¹) := by group
      obtain ⟨w, hw1, ⟨m, hwm⟩, hwσ, hwβ⟩ :=
        exists_fixed_rElement_field_comm_e6 hK σ hσ2 hβ2 hβσ
      have hfixy : y (ψ.symm w) = ψ.symm w := by
        apply fixed_of_conj_image ψ y
        rw [hψe]
        exact hwσ
      have hfixz : z (ψ.symm w) = ψ.symm w := by
        apply fixed_of_conj_image ψ z
        exact hwβ
      refine Or.inl ⟨ψ.symm w, ?_, ⟨m, ?_⟩, ?_⟩
      · intro hc
        have h := congrArg ψ hc
        rw [map_one, ψ.apply_symm_apply] at h
        exact hw1 h
      · apply ψ.injective
        rw [map_pow, ψ.apply_symm_apply, hwm, map_one]
      · intro e' he'
        rw [← hEeq] at he'
        rcases hmemE e' he' with rfl | rfl | rfl | rfl
        · rfl
        · exact hfixy
        · exact hfixz
        · rw [MulAut.mul_apply, hfixz, hfixy]
    ·
      obtain ⟨h, hhne, hhE, hh2, hxh⟩ : ∃ h : ↥(adjointGroup .E6 K),
          h ≠ 1 ∧ MulAut.conj h ∈ E ∧ h ^ 2 = 1 ∧ x h = h := by
        let θ : MulAut ↥(adjointGroup .E6 K) →* Multiplicative (ZMod 2) :=
          (MonoidHom.snd (K ≃+* K) (Multiplicative (ZMod 2))).comp Θ
        have hH : Nat.card {γ : Multiplicative (ZMod 2) // γ ^ 2 = 1} ≤ 2 := by
          rw [Nat.card_eq_fintype_card]
          decide
        obtain ⟨a, b, hab, hθab⟩ :=
          CFSG.HardMathSupport.Lang.E6Descent.exists_ne_map_eq_of_plane Nat.prime_two θ hH E
            hE2 (by rw [h4]; norm_num)
        let e : MulAut ↥(adjointGroup .E6 K) :=
          (a : MulAut ↥(adjointGroup .E6 K))⁻¹ * (b : MulAut ↥(adjointGroup .E6 K))
        have heE : e ∈ E := E.mul_mem (E.inv_mem a.2) b.2
        have hene : e ≠ 1 := by
          intro hc
          apply hab
          apply Subtype.ext
          have h1 : (a : MulAut ↥(adjointGroup .E6 K)) * e =
              (b : MulAut ↥(adjointGroup .E6 K)) := by
            change (a : MulAut ↥(adjointGroup .E6 K)) *
              ((a : MulAut ↥(adjointGroup .E6 K))⁻¹ * (b : MulAut ↥(adjointGroup .E6 K))) =
                (b : MulAut ↥(adjointGroup .E6 K))
            group
          rw [hc] at h1
          simpa using h1
        have hΘe2 : (Θ e).2 = 1 := by
          have h2 : (Θ e).2 = ((Θ (a : MulAut ↥(adjointGroup .E6 K))).2)⁻¹ *
            (Θ (b : MulAut ↥(adjointGroup .E6 K))).2 := by
            change (Θ ((a : MulAut ↥(adjointGroup .E6 K))⁻¹ *
              (b : MulAut ↥(adjointGroup .E6 K)))).2 = _
            rw [map_mul, map_inv]
            rfl
          rw [h2, show (Θ (a : MulAut ↥(adjointGroup .E6 K))).2 =
            (Θ (b : MulAut ↥(adjointGroup .E6 K))).2 from hθab,
            inv_mul_cancel]
        have hΘe : Θ e = 1 := by
          refine Prod.ext ?_ ?_
          · by_contra hne
            exact hfield ⟨e, heE, hΘe2, hne⟩
          · exact hΘe2
        have heker : e ∈ Θ.ker := MonoidHom.mem_ker.2 hΘe
        obtain ⟨h, hh⟩ := hInn_of_inndiag e (hkerInn e heker) heE
        have hh2 : h ^ 2 = 1 := by
          apply hconj
          rw [map_pow, hh, hE2 e heE, map_one]
        have hcomm : x * MulAut.conj h = MulAut.conj h * x := by
          rw [hh]
          exact hEcomm x hxE e heE
        have hxh : x h = h := by
          apply hconj
          have e1 : x * MulAut.conj h * x⁻¹ = MulAut.conj (x h) :=
            MulEquiv.ext fun u => by
              simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
                MulAut.apply_inv_self]
          rw [← e1, hcomm, mul_inv_cancel_right]
        refine ⟨h, ?_, ?_, hh2, hxh⟩
        · rintro rfl
          rw [map_one] at hh
          exact hene hh.symm
        · rw [hh]
          exact heE
      have hx2 : x ^ 2 = 1 := hE2 x hxE
      have hcomm : x * MulAut.conj h = MulAut.conj h * x :=
        hEcomm x hxE (MulAut.conj h) hhE
      obtain ⟨g, a, σ, ε, hxNF⟩ := hNF x
      have hΘx := hΘ x g a σ ε hxNF
      have hσ2 : σ ^ 2 = 1 := hsq x g a σ ε hxNF hx2
      have hεne : (ε : ℕ) ≠ 0 := by
        intro hε0
        by_cases hσ1 : σ = 1
        · have hxker : x ∈ Θ.ker := by
            rw [hker x]
            refine ⟨g, a, fun u => ?_⟩
            rw [hxNF u, hε0, hQ0, hσ1]
            simp only [mul_one, inv_one]
            rw [h1m u]
          exact hx (hInn_of_inndiag x (hkerInn x hxker) hxE)
        · apply hfield
          refine ⟨x, hxE, ?_, ?_⟩
          · rw [hΘx]; simp [hε0]
          · rw [hΘx]; exact hσ1
      have hε1 : (ε : ℕ) = 1 := by
        have hlt : (ε : ℕ) < 2 := ε.isLt
        omega
      have hx2' : x * x = 1 := by simpa [sq] using hx2
      by_cases hσ1 : σ = 1
      ·
        let P : ModGL .E6 K := diagramMap TwistTag.E6 K
        have hP1 : exactQ Tag.E6 K 1 = P := hQ1
        have hxgraph : ∀ u : ↥(adjointGroup .E6 K),
            (x u : ModGL .E6 K) = (g : ModGL .E6 K) * rootDiagUnit .E6 a * P *
              (u : ModGL .E6 K) * P⁻¹ * (rootDiagUnit .E6 a)⁻¹ * (g : ModGL .E6 K)⁻¹ := by
          intro u
          rw [hxNF u, hε1, hP1, hσ1]
          rw [h1m u]
        have hodd : Odd (Nat.card K) := by
          obtain ⟨f, hp, hKf⟩ := FiniteField.card K (ringChar K)
          rw [Nat.card_eq_fintype_card, hKf]
          exact (hp.eq_two_or_odd'.resolve_left hK).pow
        let x' : MulAut ↥(adjointGroup .E6 K) := x * MulAut.conj h
        have hx'E : x' ∈ E := E.mul_mem hxE hhE
        have hx'2 : x' ^ 2 = 1 := hE2 x' hx'E
        have hh2' : h * h = 1 := by rw [← sq]; exact hh2
        have hx'h : x' h = h := by
          change (x * MulAut.conj h) h = h
          rw [MulAut.mul_apply, MulAut.conj_apply]
          rw [show h * h * h⁻¹ = h by
            rw [hh2', one_mul, inv_eq_of_mul_eq_one_right hh2'], hxh]
        have hx'graph : ∀ u : ↥(adjointGroup .E6 K),
            (x' u : ModGL .E6 K) =
              (((h * g : ↥(adjointGroup .E6 K)) : ModGL .E6 K) * rootDiagUnit .E6 a * P *
                (u : ModGL .E6 K) * P⁻¹ * (rootDiagUnit .E6 a)⁻¹ *
                  (((h * g : ↥(adjointGroup .E6 K)) : ModGL .E6 K))⁻¹) := by
          intro u
          have hxu : x' u = h * x u * h⁻¹ := by
            change x ((MulAut.conj h) u) = h * x u * h⁻¹
            rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hxh]
          calc (x' u : ModGL .E6 K) = ((h * x u * h⁻¹ : ↥(adjointGroup .E6 K)) : ModGL .E6 K) :=
                congrArg Subtype.val hxu
            _ = (h : ModGL .E6 K) * (x u : ModGL .E6 K) * (h : ModGL .E6 K)⁻¹ := by
                rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
            _ = (h : ModGL .E6 K) * ((g : ModGL .E6 K) * rootDiagUnit .E6 a * P *
                (u : ModGL .E6 K) * P⁻¹ * (rootDiagUnit .E6 a)⁻¹ *
                  (g : ModGL .E6 K)⁻¹) * (h : ModGL .E6 K)⁻¹ := by rw [hxgraph u]
            _ = (((h * g : ↥(adjointGroup .E6 K)) : ModGL .E6 K) * rootDiagUnit .E6 a * P *
                (u : ModGL .E6 K) * P⁻¹ * (rootDiagUnit .E6 a)⁻¹ *
                  (((h * g : ↥(adjointGroup .E6 K)) : ModGL .E6 K))⁻¹) := by
                rw [Subgroup.coe_mul]
                group
        obtain ⟨ψ, hψγ | hψC4⟩ :=
          CFSG.ComponentClassification.Burgoyne.E2.exists_conj_eq_graph_of_graphCoset hodd
            (g := g) (a := a) (α := x) (by intro u; exact hxgraph u) hx2
        ·
          let ψT : MulAut ↥(adjointGroup .E6 K) := ψ
          have hψγT : ψT * x * ψT⁻¹ =
              (diagramConjAut TwistTag.E6 K : MulAut ↥(adjointGroup .E6 K)) := by
            exact hψγ
          have hγh' : (diagramConjAut TwistTag.E6 K : MulAut ↥(adjointGroup .E6 K))
              (ψT h) = ψT h := by
            rw [← hψγT]
            change (ψT * x * ψT⁻¹) (ψT h) = ψT h
            rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hxh]
          have hh'2 : (ψT h) ^ 2 = 1 := by
            rw [← map_pow ψT h 2, hh2, map_one]
          obtain ⟨u, hu1, ⟨m, hum⟩, huh, huγ⟩ :=
            exists_rElement_fixed_graph_inv hK (ψT h) hh'2 hγh'
          let uT : ↥(adjointGroup .E6 K) := u
          have huγT : (ψT * x * ψT⁻¹) uT = uT := by
            rw [hψγT]
            exact huγ
          have hx1 : x ≠ 1 := fun hxe => hx ⟨1, by rw [map_one, hxe]⟩
          have hch1 : MulAut.conj h ≠ 1 := fun hce => hhne (hZ h hce)
          have hne : MulAut.conj h ≠ x := fun hxe => hx ⟨h, hxe⟩
          have hconj2 : MulAut.conj h * MulAut.conj h = 1 := by
            rw [← sq, ← map_pow, hh2, map_one]
          have hfixx : x (ψT.symm uT) = ψT.symm uT := by
            exact fixed_of_conj_image ψT x huγT
          have huhT : Commute uT (ψT h) := huh
          have hfixh : MulAut.conj h (ψT.symm uT) = ψT.symm uT := by
            have hcomm' : Commute (ψT.symm uT) h := by
              have hmul := congrArg ψT.symm huhT.eq
              rw [map_mul, map_mul, ψT.symm_apply_apply] at hmul
              exact hmul
            change h * (ψT.symm uT) * h⁻¹ = ψT.symm uT
            rw [← hcomm'.eq, mul_inv_cancel_right]
          have hfixE := fixed_of_generators_e6 E hxE hhE (by rw [← sq]; exact hx2)
            hconj2 hcomm hx1 hch1 hne h4 hfixx hfixh
          refine Or.inl ⟨ψT.symm uT, ?_, ⟨m, ?_⟩, ?_⟩
          · intro hc
            have h := congrArg ψT hc
            rw [map_one, ψT.apply_symm_apply] at h
            exact hu1 h
          · apply ψT.injective
            rw [map_pow, ψT.apply_symm_apply]
            rw [show uT ^ (ringChar K ^ m) = 1 from hum, map_one]
          · exact hfixE
        · obtain ⟨ψ', hψ'γ | hψ'C4⟩ :=
            CFSG.ComponentClassification.Burgoyne.E2.exists_conj_eq_graph_of_graphCoset hodd
              (g := h * g) (a := a) (α := x') (by intro u; exact hx'graph u) hx'2
          ·
            let ψ'T : MulAut ↥(adjointGroup .E6 K) := ψ'
            have hψ'γT : ψ'T * x' * ψ'T⁻¹ =
                (diagramConjAut TwistTag.E6 K : MulAut ↥(adjointGroup .E6 K)) := by
              exact hψ'γ
            have hγh' : (diagramConjAut TwistTag.E6 K : MulAut ↥(adjointGroup .E6 K))
                (ψ'T h) = ψ'T h := by
              rw [← hψ'γT]
              change (ψ'T * x' * ψ'T⁻¹) (ψ'T h) = ψ'T h
              rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hx'h]
            have hh'2 : (ψ'T h) ^ 2 = 1 := by
              rw [← map_pow ψ'T h 2, hh2, map_one]
            obtain ⟨u, hu1, ⟨m, hum⟩, huh, huγ⟩ :=
              exists_rElement_fixed_graph_inv hK (ψ'T h) hh'2 hγh'
            let uT : ↥(adjointGroup .E6 K) := u
            have huγT : (ψ'T * x' * ψ'T⁻¹) uT = uT := by
              rw [hψ'γT]
              exact huγ
            have hx1 : x ≠ 1 := fun hxe => hx ⟨1, by rw [map_one, hxe]⟩
            have hch1 : MulAut.conj h ≠ 1 := fun hce => hhne (hZ h hce)
            have hconj2 : MulAut.conj h * MulAut.conj h = 1 := by
              rw [← sq, ← map_pow, hh2, map_one]
            have hx'1 : x' ≠ 1 := by
              intro hc
              have hxe : x = MulAut.conj h := by
                calc x = x * (MulAut.conj h * MulAut.conj h) := by rw [hconj2, mul_one]
                  _ = (x * MulAut.conj h) * MulAut.conj h := by group
                  _ = MulAut.conj h := by
                        rw [show x * MulAut.conj h = x' from rfl, hc, one_mul]
              exact hx ⟨h, hxe.symm⟩
            have hne' : MulAut.conj h ≠ x' := by
              intro hc
              apply hx1
              calc x = x * (MulAut.conj h * (MulAut.conj h)⁻¹) := by group
                _ = (x * MulAut.conj h) * (MulAut.conj h)⁻¹ := by group
                _ = x' * (MulAut.conj h)⁻¹ := by
                      rw [show x * MulAut.conj h = x' from rfl]
                _ = (MulAut.conj h) * (MulAut.conj h)⁻¹ := by rw [← hc]
                _ = 1 := by group
            have hcomm' : x' * MulAut.conj h = MulAut.conj h * x' :=
              hEcomm x' hx'E (MulAut.conj h) hhE
            have hfixx : x' (ψ'T.symm uT) = ψ'T.symm uT := by
              exact fixed_of_conj_image ψ'T x' huγT
            have huhT : Commute uT (ψ'T h) := huh
            have hfixh : MulAut.conj h (ψ'T.symm uT) = ψ'T.symm uT := by
              have hcomm'' : Commute (ψ'T.symm uT) h := by
                have hmul := congrArg ψ'T.symm huhT.eq
                rw [map_mul, map_mul, ψ'T.symm_apply_apply] at hmul
                exact hmul
              change h * (ψ'T.symm uT) * h⁻¹ = ψ'T.symm uT
              rw [← hcomm''.eq, mul_inv_cancel_right]
            have hfixE := fixed_of_generators_e6 E hx'E hhE (by rw [← sq]; exact hx'2)
              hconj2 hcomm' hx'1 hch1 hne' h4 hfixx hfixh
            refine Or.inl ⟨ψ'T.symm uT, ?_, ⟨m, ?_⟩, ?_⟩
            · intro hc
              have h := congrArg ψ'T hc
              rw [map_one, ψ'T.apply_symm_apply] at h
              exact hu1 h
            · apply ψ'T.injective
              rw [map_pow, ψ'T.apply_symm_apply]
              rw [show uT ^ (ringChar K ^ m) = 1 from hum, map_one]
            · exact hfixE
          ·
            refine Or.inr ⟨x, h, ψ, ψ', hxE, hhE, hhne, hh2, hxh, hψC4, ?_⟩
            exact hψ'C4
      ·
        obtain ⟨f, hp, hKf⟩ := FiniteField.card K (ringChar K)
        have hKc : Nat.card K = ringChar K ^ (f : ℕ) := by
          rw [Nat.card_eq_fintype_card, hKf]
        have hf : 1 ≤ (f : ℕ) := f.pos
        obtain ⟨hev, hσc, -⟩ :=
          hquad (ringChar K) (f : ℕ) hp hf hKc σ hσ2 hσ1
        have he : 1 ≤ (f : ℕ) / 2 := by
          obtain ⟨m, hm⟩ := hev
          omega
        have hKe : Nat.card K = (ringChar K ^ ((f : ℕ) / 2)) ^ 2 := by
          rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hKc]
        obtain ⟨-, ⟨β₀, -, hconjAll⟩⟩ :=
          exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe σ.toRingHom hσc
        obtain ⟨-, hconj⟩ := hconjAll g a
        let P : ModGL .E6 K := diagramMap TwistTag.E6 K
        have hP1 : exactQ Tag.E6 K 1 = P := hQ1
        have hxP : ∀ u : ↥(adjointGroup .E6 K), (x u : ModGL .E6 K) =
            (g : ModGL .E6 K) * rootDiagUnit .E6 a * P *
              Units.map (entrywiseHom σ.toRingHom) (u : ModGL .E6 K) *
                P⁻¹ * (rootDiagUnit .E6 a)⁻¹ * (g : ModGL .E6 K)⁻¹ := by
          intro u
          rw [hxNF u, hε1, hP1]
        obtain ⟨ψ, hψ, -⟩ := hconj x (by intro u; exact hxP u) hx2'
        have hρformula : ∀ u : ↥(adjointGroup TwistTag.E6.tag K),
            ((diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ) u :
              ModGL TwistTag.E6.tag K) = diagramMap TwistTag.E6 K *
                Units.map (entrywiseHom σ.toRingHom) (u : ModGL TwistTag.E6.tag K) *
                  (diagramMap TwistTag.E6 K)⁻¹ := by
          intro u
          rw [MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut]
        let ψT : MulAut ↥(adjointGroup .E6 K) := ψ
        have hψT : ∀ u : ↥(adjointGroup .E6 K),
            (ψT * x * ψT⁻¹) u = (diagramConjAut TwistTag.E6 K *
              entrywiseAdjointAut TwistTag.E6.tag σ) u := by
          intro u
          refine Subtype.ext ?_
          rw [hρformula u]
          exact hψ u
        let h' : ↥(adjointGroup .E6 K) := ψT h
        have hA : (ψT * x * ψT⁻¹) h' = h' := by
          change (ψT * x * ψT⁻¹) (ψT h) = ψT h
          rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hxh]
        have hρh' : (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ)
            h' = h' := by
          rw [← hψT h']
          exact hA
        have hh'2 : h' ^ 2 = 1 := by
          rw [show h' = ψT h from rfl, ← map_pow ψT h 2, hh2, map_one]
        obtain ⟨u, hu1, ⟨m, hum⟩, huh, huρ⟩ :=
          exists_rElement_fixed_graphField_inv σ (ringChar K ^ ((f : ℕ) / 2)) hσc hKe hK
            h' hh'2 hρh'
        let uT : ↥(adjointGroup .E6 K) := u
        have huρT : (ψT * x * ψT⁻¹) uT = uT := by
          rw [hψT uT]
          exact huρ
        have hx1 : x ≠ 1 := fun hxe => hx ⟨1, by rw [map_one, hxe]⟩
        have hch1 : MulAut.conj h ≠ 1 := fun hce => hhne (hZ h hce)
        have hne : MulAut.conj h ≠ x := fun hxe => hx ⟨h, hxe⟩
        have hconj2 : MulAut.conj h * MulAut.conj h = 1 := by
          rw [← sq, ← map_pow, hh2, map_one]
        have hfixx : x (ψT.symm uT) = ψT.symm uT :=
          fixed_of_conj_image ψT x huρT
        have huhT : Commute uT h' := huh
        have hfixh : MulAut.conj h (ψT.symm uT) = ψT.symm uT := by
          have hcomm' : Commute (ψT.symm uT) h := by
            have hmul := congrArg ψT.symm huhT.eq
            rw [map_mul, map_mul, ψT.symm_apply_apply] at hmul
            exact hmul
          change h * (ψT.symm uT) * h⁻¹ = ψT.symm uT
          rw [← hcomm'.eq, mul_inv_cancel_right]
        have hfixE := fixed_of_generators_e6 E hxE hhE (by rw [← sq]; exact hx2)
          hconj2 hcomm hx1 hch1 hne h4 hfixx hfixh
        refine Or.inl ⟨ψT.symm uT, ?_, ⟨m, ?_⟩, ?_⟩
        · intro hc
          have h := congrArg ψT hc
          rw [map_one, ψT.apply_symm_apply] at h
          exact hu1 h
        · apply ψT.injective
          rw [map_pow, ψT.apply_symm_apply]
          rw [show uT ^ (ringChar K ^ m) = 1 from hum, map_one]
        · exact hfixE
end CFSG.LocalAnalysis.WeakClosure81
