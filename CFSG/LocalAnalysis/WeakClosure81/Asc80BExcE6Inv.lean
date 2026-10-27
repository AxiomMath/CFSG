module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.FixedGroup
import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcOuterR
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E6GraphConj
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcSixE
import CFSG.LocalAnalysis.SteinbergCEOddResidualE6GraphCore
import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueFieldTorus
import CFSG.GH74.GLS.Stage1.Main.BrTwoClassE
import CFSG.RankThree.PartOne.CTP.StrongPG2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

theorem exists_rElement_commute_involution_of_four {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {r : ℕ}
    (hfour : ∀ A : Subgroup G, (∀ x ∈ A, x ^ 2 = 1) → Nat.card A = 2 ^ 2 →
      ∃ u : G, u ≠ 1 ∧ (∃ n : ℕ, u ^ (r ^ n) = 1) ∧ ∀ x ∈ A, Commute u x)
    {h : G} (hh : orderOf h = 2) :
    ∃ u : G, u ≠ 1 ∧ (∃ n : ℕ, u ^ (r ^ n) = 1) ∧ Commute u h := by
  classical
  have h1 : h ≠ 1 := by
    intro hc
    rw [hc, orderOf_one] at hh
    exact absurd hh (by decide)
  let e : Shrink.{0} G ≃* G := Shrink.mulEquiv
  have : Finite (Shrink.{0} G) := Finite.of_equiv G e.symm.toEquiv
  have : IsSimpleGroup (Shrink.{0} G) := e.isSimpleGroup
  have hnonab' : ∃ a b : Shrink.{0} G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩
  have hh' : orderOf (e.symm h) = 2 := by
    change orderOf (e.symm.toMonoidHom h) = 2
    rw [orderOf_injective e.symm.toMonoidHom e.symm.injective h, hh]
  obtain ⟨g', hg'ne, hg'c⟩ :=
    CFSG.SeitzReduction.F4Pilot.exists_conj_ne_commute_of_isSimpleGroup hnonab' hh'
  let h' : Shrink.{0} G := e.symm h
  let s' : Shrink.{0} G := g'⁻¹ * h' * g'
  let g : G := e g'
  let s : G := g⁻¹ * h * g
  have hsq : h * h = 1 := by rw [← sq, ← hh, pow_orderOf_eq_one]
  have hh'2 : h' * h' = 1 := by
    apply e.injective
    rw [map_mul, show e h' = h from e.apply_symm_apply h, hsq, map_one]
  have h2' : h' ≠ 1 := by
    intro hc
    apply h1
    rw [← e.apply_symm_apply h, show e.symm h = h' from rfl, hc, map_one]
  have hs'2 : s' * s' = 1 := by
    calc s' * s' = g'⁻¹ * (h' * h') * g' := by
          rw [show s' = g'⁻¹ * h' * g' from rfl]; group
      _ = 1 := by rw [hh'2]; group
  have hs : e s' = s := by simp [s', s, g, h']
  have hs'ne : s' ≠ 1 := by
    intro hc
    apply h2'
    calc h' = g' * s' * g'⁻¹ := by
          rw [show s' = g'⁻¹ * h' * g' from rfl]; group
      _ = 1 := by rw [hc]; group
  have h1' : s ≠ 1 := fun hc => hs'ne (e.injective (by rw [hs, hc, map_one]))
  have h4 := CFSG.GH74.GLS.Stage1.Main.four_of_invols hh'2 hs'2 hg'c.symm h2' hs'ne hg'ne.symm
  have hAmap : (zpowers h ⊔ zpowers s).map e.symm.toMonoidHom =
      zpowers h' ⊔ zpowers s' := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    simp [h', s', ← hs]
  have hA2 : ∀ x ∈ zpowers h ⊔ zpowers s, x ^ 2 = 1 := by
    intro x hx
    have hx' : e.symm x ∈ zpowers h' ⊔ zpowers s' := by
      rw [← hAmap]
      exact Subgroup.mem_map_of_mem e.symm.toMonoidHom hx
    have h2 : e.symm x * e.symm x = 1 := h4.2.1 _ hx'
    rw [sq]
    have := congrArg e h2
    rwa [map_mul, map_one, e.apply_symm_apply] at this
  have hcard : Nat.card ↥(zpowers h ⊔ zpowers s) = 2 ^ 2 := by
    have h := Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective
      (K := zpowers h ⊔ zpowers s)
    rw [hAmap] at h
    rw [← h, h4.2.2.2]
    norm_num
  obtain ⟨u, hu1, hun, hucomm⟩ := hfour _ hA2 hcard
  exact ⟨u, hu1, hun, hucomm h (mem_sup_left (mem_zpowers h))⟩


theorem exists_rElement_commute_involution_e6 {K : Type} [Field K]
    [Finite K] (hK : ringChar K ≠ 2) {h : ↥(adjointGroup .E6 K)} (hh : h ^ 2 = 1) :
    ∃ u : ↥(adjointGroup .E6 K), u ≠ 1 ∧ (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧ Commute u h := by
  classical
  have : Fintype K := Fintype.ofFinite K
  by_cases h1 : h = 1
  · subst h
    let i : Fin Tag.E6.rank := ⟨0, by decide⟩
    have hu1 : (⟨xUnit .E6 K i 1, xUnit_mem_adjointGroup i 1⟩ : ↥(adjointGroup .E6 K)) ≠ 1 := by
      intro hc
      have hc' : (xUnit .E6 K i 1 : ModGL .E6 K) = 1 := congrArg Subtype.val hc
      have h2 : xOp .E6 K i (1 : K) = xOp .E6 K i (0 : K) := by
        have h3 := congrArg (fun z : ModGL .E6 K => (z : Module.End K (RootModule .E6 K))) hc'
        simpa only [coe_xUnit, xOp_zero, Units.val_one] using h3
      exact one_ne_zero (xOp_injective i h2)
    refine ⟨⟨xUnit .E6 K i 1, xUnit_mem_adjointGroup i 1⟩, hu1, ⟨1, ?_⟩, by simp⟩
    have : CharP K (ringChar K) := ringChar.charP K
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa using CFSG.RankThree.PartOne.StrongP.xUnit_pow_char (K := K) (p := ringChar K) .E6 i
  · have hh1 : orderOf h = 2 := orderOf_eq_prime hh h1
    have hq : CFSG.IsQuasisimple ↥(adjointGroup .E6 K) :=
      CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K
    have : IsSimpleGroup ↥(adjointGroup .E6 K) :=
      CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
        ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
          QuotientGroup.quotientBot).symm
    have : Finite (ModGL .E6 K) := finite_modGL
    have : Finite ↥(adjointGroup .E6 K) := Subtype.finite
    have hnonab : ∃ a b : ↥(adjointGroup .E6 K), a * b ≠ b * a := by
      by_contra hc
      apply h1
      have hz : h ∈ Subgroup.center ↥(adjointGroup .E6 K) :=
        Subgroup.mem_center_iff.2 fun g => by_contra fun hne => hc ⟨g, h, hne⟩
      rwa [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
    exact exists_rElement_commute_involution_of_four hnonab
      (fun A hA hcard =>
        exists_rElement_commute_four (Or.inr (Or.inl rfl)) hK hA hcard) hh1

theorem exists_fixed_rElement_involution_e6 {K : Type} [Field K]
    [Finite K] (hK : ringChar K ≠ 2) {β : MulAut ↥(adjointGroup .E6 K)} (hβ : β ^ 2 = 1) :
    ∃ y : ↥(adjointGroup .E6 K), y ≠ 1 ∧ (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) ∧ β y = y := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨f, hp, hKf⟩ := FiniteField.card K (ringChar K)
  have hKcard : Nat.card K = ringChar K ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hKf]
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hodd : Odd (Nat.card K) := by
    rw [hKcard]
    exact (hp.eq_two_or_odd'.resolve_left hK).pow
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K
  obtain ⟨Θ, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF β
  have hσ2 := hsq β g a σ ε hgaσ hβ
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have h2 : (ε : ℕ) < 2 := ε.isLt
    omega
  have h1m : ∀ x : ModGL .E6 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ0 : exactQ Tag.E6 K 0 = 1 := pow_zero _
  have hQ1 : exactQ Tag.E6 K 1 = diagramMap TwistTag.E6 K := pow_one _
  have hne : ∀ (τ : Tag) (i : Fin τ.rank),
      (⟨xUnit τ K i 1, xUnit_mem_adjointGroup i 1⟩ : ↥(adjointGroup τ K)) ≠ 1 := by
    intro τ i hc
    have hc' : (xUnit τ K i 1 : ModGL τ K) = 1 := by
      simpa using congrArg Subtype.val hc
    have h3 : (xOp τ K i (1 : K) : Module.End K (RootModule τ K)) = 1 := by
      have h4 := congrArg (fun z : ModGL τ K => (z : Module.End K (RootModule τ K))) hc'
      simpa only [coe_xUnit, Units.val_one] using h4
    have h2 : xOp τ K i (1 : K) = xOp τ K i (0 : K) := by
      rw [xOp_zero]
      exact h3
    exact one_ne_zero (xOp_injective i h2)
  have hpow : ∀ (τ : Tag) (i : Fin τ.rank),
      (⟨xUnit τ K i 1, xUnit_mem_adjointGroup i 1⟩ : ↥(adjointGroup τ K)) ^
        (ringChar K ^ 1) = 1 := by
    intro τ i
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa using CFSG.RankThree.PartOne.StrongP.xUnit_pow_char (K := K) (p := ringChar K) τ i
  let e4 : Fin TwistTag.E6.tag.rank := CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset.e4
  let e4' : Fin Tag.E6.rank := ⟨3, by decide⟩
  let x₀ : ↥(adjointGroup TwistTag.E6.tag K) :=
    ⟨xUnit TwistTag.E6.tag K e4 1, xUnit_mem_adjointGroup e4 1⟩
  let y₀ : ↥(adjointGroup Tag.E6 K) := ⟨xUnit Tag.E6 K e4' 1, xUnit_mem_adjointGroup e4' 1⟩
  let βt : MulAut ↥(adjointGroup TwistTag.E6.tag K) := β
  have hx₀ne : x₀ ≠ 1 := hne TwistTag.E6.tag e4
  have hx₀pow : x₀ ^ (ringChar K ^ 1) = 1 := hpow TwistTag.E6.tag e4
  have hy₀ne : y₀ ≠ 1 := hne Tag.E6 e4'
  have hy₀pow : y₀ ^ (ringChar K ^ 1) = 1 := hpow Tag.E6 e4'
  have hx₀diag : diagramConjAut TwistTag.E6 K x₀ = x₀ := by
    refine Subtype.ext ?_
    rw [coe_diagramConjAut]
    simp only [x₀, e4]
    rw [← CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset.xUnit_e4_commute_diagramMap (K := K) 1]
    group
  have hsign : CFSG.ComponentClassification.Burgoyne.E2.e6GraphSign K =
      CFSG.LieType.Chevalley.E6SignedGraph.signTuple K := by
    funext i
    fin_cases i <;> rfl
  have hx₀sign : rootDiagAut TwistTag.E6.tag K
      (CFSG.ComponentClassification.Burgoyne.E2.e6GraphSign K) x₀ = x₀ := by
    refine Subtype.ext ?_
    rw [hsign, coe_rootDiagAut]
    simp only [x₀, e4]
    rw [← CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset.xUnit_e4_commute_signDiag (K := K) 1]
    group
  have hx₀field : ∀ (δ : K ≃+* K),
      Units.map (entrywiseHom δ.toRingHom) (x₀ : ModGL TwistTag.E6.tag K) =
        (x₀ : ModGL TwistTag.E6.tag K) := by
    intro δ
    refine Units.ext ?_
    change entrywise (τ := TwistTag.E6.tag) δ.toRingHom
        (↑(xUnit TwistTag.E6.tag K e4 1)) = ↑(xUnit TwistTag.E6.tag K e4 1)
    rw [coe_xUnit, entrywise_xOp, map_one]
  have hx₀entry : ∀ (δ : K ≃+* K), entrywiseAdjointAut TwistTag.E6.tag δ x₀ = x₀ := by
    intro δ
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact hx₀field δ
  have hy₀field : ∀ (δ : K ≃+* K),
      Units.map (entrywiseHom δ.toRingHom) (y₀ : ModGL Tag.E6 K) =
        (y₀ : ModGL Tag.E6 K) := by
    intro δ
    refine Units.ext ?_
    change entrywise (τ := Tag.E6) δ.toRingHom
        (↑(xUnit Tag.E6 K e4' 1)) = ↑(xUnit Tag.E6 K e4' 1)
    rw [coe_xUnit, entrywise_xOp, map_one]
  have key : ∀ {T : Type} [Group T] (ψ : MulAut T) (βk : MulAut T) {y : T},
      (ψ * βk * ψ⁻¹) y = y → y ≠ 1 → (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) →
      ∃ y' : T, y' ≠ 1 ∧ (∃ n : ℕ, y' ^ (ringChar K ^ n) = 1) ∧ βk y' = y' := by
    intro T _ ψ βk y hψ hyne hypow
    obtain ⟨n, hn⟩ := hypow
    refine ⟨ψ.symm y, ?_, ⟨n, ?_⟩, ?_⟩
    · intro h1
      apply hyne
      have h := congrArg ψ h1
      rw [map_one, ψ.apply_symm_apply] at h
      exact h
    · apply ψ.injective
      rw [map_pow, ψ.apply_symm_apply, hn, map_one]
    · apply ψ.injective
      rw [ψ.apply_symm_apply]
      exact hψ
  by_cases hσ1 : σ = 1
  · subst σ
    rcases hε with hε | hε
    ·
      have hβeq : β = MulAut.conj g * rootDiagAutHom .E6 K a := by
        refine MulEquiv.ext fun u => Subtype.ext ?_
        rw [MulAut.mul_apply, MulAut.conj_apply, hgaσ u, hε, hQ0, h1m]
        simp only [mul_one, inv_one]
        change (↑g : ModGL .E6 K) * rootDiagUnit .E6 a * (u : ModGL .E6 K) *
            (rootDiagUnit .E6 a)⁻¹ * (↑g)⁻¹ =
          (↑g : ModGL .E6 K) * (↑((rootDiagAut .E6 K a) u) : ModGL .E6 K) * (↑g)⁻¹
        rw [coe_rootDiagAut]
        group
      have hβmem : β ∈ CFSG.StandardType.LayerSixE.inndiagAut .E6 K := by
        rw [hβeq, CFSG.StandardType.LayerSixE.inndiagAut]
        exact Subgroup.mul_mem_sup (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
          (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
      obtain ⟨h, hh⟩ := CFSG.StandardType.OrdPInnerExc.mem_inn_of_inndiag_E6
        Nat.prime_two (Or.inl (by norm_num)) hβmem hβ
      have hZ : ∀ c : ↥(adjointGroup .E6 K), MulAut.conj c = 1 → c = 1 := by
        intro c hc
        have hcZ : c ∈ Subgroup.center ↥(adjointGroup .E6 K) := by
          rw [Subgroup.mem_center_iff]
          intro g'
          have h1 : c * g' * c⁻¹ = g' := by
            have := congrArg (fun φ : MulAut ↥(adjointGroup .E6 K) => φ g') hc
            simpa only [MulAut.conj_apply, MulAut.one_apply] using this
          calc g' * c = c * g' * c⁻¹ * c := by rw [h1]
            _ = c * g' := by group
        rwa [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hcZ
      have hconj : Function.Injective
          (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)) :=
        (injective_iff_map_eq_one _).2 hZ
      have hh2 : h ^ 2 = 1 := hconj (by rw [map_pow, hh, hβ, map_one])
      obtain ⟨u, hu1, hun, hcomm⟩ := exists_rElement_commute_involution_e6 hK hh2
      exact ⟨u, hu1, hun, by rw [← hh, MulAut.conj_apply, ← hcomm.eq, mul_inv_cancel_right]⟩
    ·
      obtain ⟨ψ, hψ | hψ⟩ :=
        CFSG.ComponentClassification.Burgoyne.E2.exists_conj_eq_graph_of_graphCoset hodd
          (g := g) (a := a) (α := β)
          (fun h => (hgaσ h).trans (by rw [hε, hQ1, h1m]; rfl)) hβ
      · have hfix : (ψ * βt * ψ⁻¹) x₀ = x₀ := by
          rw [show ψ * βt * ψ⁻¹ = diagramConjAut TwistTag.E6 K from hψ]
          exact hx₀diag
        exact key ψ βt hfix hx₀ne ⟨1, hx₀pow⟩
      · have hfix : (ψ * βt * ψ⁻¹) x₀ = x₀ := by
          rw [show ψ * βt * ψ⁻¹ =
            rootDiagAut TwistTag.E6.tag K (CFSG.ComponentClassification.Burgoyne.E2.e6GraphSign K) *
              diagramConjAut TwistTag.E6 K from hψ, MulAut.mul_apply, hx₀diag, hx₀sign]
        exact key ψ βt hfix hx₀ne ⟨1, hx₀pow⟩
  ·
    obtain ⟨hev, hσc, -⟩ := hquad (ringChar K) (f : ℕ) hp hf hKcard σ hσ2 hσ1
    have he : 1 ≤ (f : ℕ) / 2 := by
      obtain ⟨m, hm⟩ := hev
      omega
    have hKe : Nat.card K = (ringChar K ^ ((f : ℕ) / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hKcard]
    have hσσ : σ * σ = 1 := by rw [← sq]; exact hσ2
    obtain ⟨hfield, β', -, hβα'⟩ :=
      exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe σ.toRingHom hσc
    rcases hε with hε | hε
    ·
      obtain ⟨β₀, -, hβα⟩ := hfield Tag.E6
      obtain ⟨-, hconj⟩ := hβα g a
      obtain ⟨ψ, hψ, -⟩ := hconj β
        (fun h => by rw [hgaσ h, hε, hQ0, mul_one, inv_one, mul_one]) hβ
      have hfix : (ψ * β * ψ⁻¹) y₀ = y₀ :=
        Subtype.ext ((hψ y₀).trans (hy₀field σ))
      exact key ψ β hfix hy₀ne ⟨1, hy₀pow⟩
    ·
      let β'' : MulAut (adjointGroup TwistTag.E6.tag K) := β
      obtain ⟨-, hconj⟩ := hβα' g a
      obtain ⟨ψ, hψ, -⟩ := hconj β''
        (fun h => (hgaσ h).trans (by rw [hε, hQ1]; rfl)) hβ
      have hψe : ψ * β'' * ψ⁻¹ =
          diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ := by
        refine MulEquiv.ext fun u => Subtype.ext ((hψ u).trans ?_)
        rw [MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut]
      have hfix : (ψ * β'' * ψ⁻¹) x₀ = x₀ := by
        rw [hψe, MulAut.mul_apply, hx₀entry σ, hx₀diag]
      exact key ψ β'' hfix hx₀ne ⟨1, hx₀pow⟩

theorem exists_fixed_rElement_field_comm_e6
    {K : Type} [Field K]
    [Finite K] (hK : ringChar K ≠ 2) (σ : K ≃+* K) (hσ : σ ^ 2 = 1)
    {β : MulAut ↥(adjointGroup .E6 K)} (hβ : β ^ 2 = 1)
    (hβσ : β * entrywiseAdjointAut .E6 σ = entrywiseAdjointAut .E6 σ * β) :
    ∃ y : ↥(adjointGroup .E6 K), y ≠ 1 ∧ (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) ∧
      entrywiseAdjointAut .E6 σ y = y ∧ β y = y := by
  classical
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    have h := congrArg (fun φ : K ≃+* K => φ c) hσ
    simpa [sq] using h
  let J : Subgroup ↥(adjointGroup .E6 K) := fixedSubgroup (entrywiseAdjointAut .E6 σ)
  have hΓJ : entrywiseFixedGroup .E6 σ = fixedFieldImage .E6 σ :=
    CFSG.SeitzReduction.E6Pilot.entrywiseFixedGroup_eq_fixedFieldImage_E6 σ hσσ
  let φ : ↥J ≃* ↥(adjointGroup .E6 ↥(fixSubfield σ)) :=
    CFSG.LieType.SeitzGeneration.ExcOuterLeOne.fixedEquivOfEq σ hΓJ
  have hβJ : ∀ y ∈ J, β y ∈ J := by
    intro y hy
    have hy' : entrywiseAdjointAut .E6 σ y = y := hy
    have h : entrywiseAdjointAut .E6 σ (β y) = β y := by
      have h1 : β (entrywiseAdjointAut .E6 σ y) = entrywiseAdjointAut .E6 σ (β y) := by
        simpa only [MulAut.mul_apply] using congrArg (fun e => e y) hβσ
      rw [← h1, hy']
    exact h
  have hβσ' : β⁻¹ * entrywiseAdjointAut .E6 σ = entrywiseAdjointAut .E6 σ * β⁻¹ := by
    have h : entrywiseAdjointAut .E6 σ * β⁻¹ = β⁻¹ * entrywiseAdjointAut .E6 σ := by
      calc entrywiseAdjointAut .E6 σ * β⁻¹ = β⁻¹ * (β * entrywiseAdjointAut .E6 σ) * β⁻¹ :=
            by group
        _ = β⁻¹ * (entrywiseAdjointAut .E6 σ * β) * β⁻¹ := by rw [hβσ]
        _ = β⁻¹ * entrywiseAdjointAut .E6 σ := by group
    exact h.symm
  have hβJ' : ∀ y ∈ J, β⁻¹ y ∈ J := by
    intro y hy
    have hy' : entrywiseAdjointAut .E6 σ y = y := hy
    have h : entrywiseAdjointAut .E6 σ (β⁻¹ y) = β⁻¹ y := by
      have h1 : β⁻¹ (entrywiseAdjointAut .E6 σ y) = entrywiseAdjointAut .E6 σ (β⁻¹ y) := by
        simpa only [MulAut.mul_apply] using congrArg (fun e => e y) hβσ'
      rw [← h1, hy']
    exact h
  let βJ : MulAut ↥J :=
    { toFun := fun y => ⟨β y, hβJ y y.2⟩
      invFun := fun y => ⟨β⁻¹ y, hβJ' y y.2⟩
      left_inv := fun y => Subtype.ext (by
        change (β⁻¹ : MulAut ↥(adjointGroup .E6 K)) (β y.1) = y.1
        exact MulEquiv.symm_apply_apply β y.1)
      right_inv := fun y => Subtype.ext (by
        change β ((β⁻¹ : MulAut ↥(adjointGroup .E6 K)) y.1) = y.1
        exact MulEquiv.apply_symm_apply β y.1)
      map_mul' := fun a b => Subtype.ext (map_mul β a.1 b.1) }
  let β₀ : MulAut ↥(adjointGroup .E6 ↥(fixSubfield σ)) := φ.symm.trans (βJ.trans φ)
  have hβJ2 : βJ ^ 2 = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    change β (β (y : ↥(adjointGroup .E6 K))) = (y : ↥(adjointGroup .E6 K))
    have h := congrArg (fun e : MulAut ↥(adjointGroup .E6 K) =>
      e (y : ↥(adjointGroup .E6 K))) hβ
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
  have hβ₀2 : β₀ ^ 2 = 1 := by
    refine MulEquiv.ext fun x => ?_
    change φ (βJ (φ.symm (φ (βJ (φ.symm x))))) = x
    rw [MulEquiv.symm_apply_apply]
    have h := congrArg (fun e : MulAut ↥J => e (φ.symm x)) hβJ2
    simp only [pow_two, MulAut.mul_apply, MulAut.one_apply] at h
    calc φ (βJ (βJ (φ.symm x))) = φ (φ.symm x) := by rw [h]
      _ = x := φ.apply_symm_apply x
  have hchar : ringChar ↥(fixSubfield σ) = ringChar K := by
    have : CharP K (ringChar K) := ringChar.charP K
    have : CharP ↥(fixSubfield σ) (ringChar K) :=
      (RingHom.charP_iff (fixSubfield σ).subtype (fixSubfield σ).subtype.injective
        (ringChar K)).mpr inferInstance
    exact ringChar.eq _ _
  have : Finite ↥(fixSubfield σ) := Subtype.finite
  have : Finite (ModGL .E6 ↥(fixSubfield σ)) := finite_modGL
  have : Finite ↥(adjointGroup .E6 ↥(fixSubfield σ)) := Subtype.finite
  obtain ⟨y₀, hy₀1, ⟨n, hy₀n⟩, hy₀fix⟩ :=
    exists_fixed_rElement_involution_e6 (K := ↥(fixSubfield σ))
      (by rw [hchar]; exact hK) hβ₀2
  let z : ↥J := φ.symm y₀
  let y : ↥(adjointGroup .E6 K) := (z : ↥(adjointGroup .E6 K))
  have hz : βJ z = z := by
    have h := hy₀fix
    change φ (βJ (φ.symm y₀)) = y₀ at h
    have h2 := congrArg (fun w => φ.symm w) h
    rw [MulEquiv.symm_apply_apply] at h2
    exact h2
  have hyβ : β y = y := congrArg Subtype.val hz
  have hyfix : entrywiseAdjointAut .E6 σ y = y := z.2
  refine ⟨y, ?_, ⟨n, ?_⟩, hyfix, hyβ⟩
  · intro h
    apply hy₀1
    have h2 : z = 1 := Subtype.ext h
    calc y₀ = φ z := (φ.apply_symm_apply y₀).symm
      _ = φ 1 := by rw [h2]
      _ = 1 := map_one φ
  · have h2 : z ^ (ringChar K ^ n) = 1 := by
      apply φ.injective
      rw [map_pow, φ.apply_symm_apply, ← hchar, map_one]
      exact hy₀n
    exact congrArg Subtype.val h2

end CFSG.LocalAnalysis.WeakClosure81
