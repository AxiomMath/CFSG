module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UStd
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrameO
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6Disc
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UExc
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Exceptional
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley (Tag TwistTag ModGL adjointGroup)

private theorem w7A_exists_theta {n f : ℕ} (hf : 1 ≤ f)
    {X : Type} [Group X] {ψ : (ggU .twistedE6 n f).K →* X}
    {π : (ggU .twistedE6 n f).K →*
      ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf))}
    (hπ : Function.Surjective π)
    (hkerπ : π.ker = Subgroup.center (ggU .twistedE6 n f).K)
    (hker : ψ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K) :
    ∃ θ : (↥ψ.range ⧸ Subgroup.center ↥ψ.range) ≃*
        ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)),
      ∀ u : (ggU .twistedE6 n f).K, θ (QuotientGroup.mk (ψ.rangeRestrict u)) = π u := by
  classical
  have hkπ : ψ.ker ≤ π.ker := hker.trans hkerπ.ge
  have hC : Subgroup.center
      ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)) = ⊥ :=
    CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot (frobQEquiv hf).surjective
  have hψ' : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have hψ'ker : ψ.rangeRestrict.ker ≤ π.ker := by
    rw [ψ.ker_rangeRestrict]
    exact hkπ
  let ε : ↥ψ.range →* ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)) :=
    ψ.rangeRestrict.liftOfSurjective hψ' ⟨π, hψ'ker⟩
  have hε : ∀ u : (ggU .twistedE6 n f).K, ε (ψ.rangeRestrict u) = π u := fun u =>
    ψ.rangeRestrict.liftOfRightInverse_comp_apply _ _ ⟨π, hψ'ker⟩ u
  have hεsurj : Function.Surjective ε := by
    intro c
    obtain ⟨u, rfl⟩ := hπ c
    exact ⟨ψ.rangeRestrict u, hε u⟩
  have hεker : ε.ker = Subgroup.center ↥ψ.range := by
    ext y
    obtain ⟨u, rfl⟩ := hψ' y
    rw [MonoidHom.mem_ker, hε, Subgroup.mem_center_iff]
    constructor
    · intro h w
      obtain ⟨v, rfl⟩ := hψ' w
      have hu : u ∈ Subgroup.center (ggU .twistedE6 n f).K := by
        rw [← hkerπ]
        exact h
      have huv : v * u = u * v := (Subgroup.mem_center_iff.1 hu) v
      exact (map_mul ψ.rangeRestrict v u).symm.trans
        ((congrArg ψ.rangeRestrict huv).trans (map_mul ψ.rangeRestrict u v))
    · intro h
      have hcomm : ∀ v, π v * π u = π u * π v := by
        intro v
        have h1 := h (ψ.rangeRestrict v)
        have h1' : ψ.rangeRestrict (v * u) = ψ.rangeRestrict (u * v) := by
          rw [map_mul, map_mul]
          exact h1
        have h2 : (v * u) * (u * v)⁻¹ ∈ ψ.rangeRestrict.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, h1', mul_inv_cancel]
        have h3 : π (v * u) = π (u * v) := by
          have h4 := hψ'ker h2
          rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h4
          exact h4
        rw [map_mul, map_mul] at h3
        exact h3
      have hu : π u ∈ Subgroup.center
          ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)) := by
        rw [Subgroup.mem_center_iff]
        intro c
        obtain ⟨v, rfl⟩ := hπ c
        exact hcomm v
      rw [hC, Subgroup.mem_bot] at hu
      exact hu
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hεker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ε hεsurj), fun u => ?_⟩
  exact hε u

section Act

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

structure TwE6Act
    {X : Type} [Group X] (G₀ B : Subgroup X) {f : ℕ} (hf : 1 ≤ f) where
  θ : ↥G₀ ⧸ Subgroup.center ↥G₀ ≃* ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf))
  lam : ↥B →* ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f)) (frobQEquiv hf))
  lam_inj : Function.Injective lam
  act : ∀ (b : ↥B) (y y' : ↥G₀), (y' : X) = (b : X) * (y : X) * (b : X)⁻¹ →
    ((θ (QuotientGroup.mk y') : ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf))) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((lam b : ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f)) (frobQEquiv hf))) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
      ((θ (QuotientGroup.mk y) : ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf))) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
      ((lam b : ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f)) (frobQEquiv hf))) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))⁻¹

theorem exists_act_twE6_of_facts
    {ψ : (ggU .twistedE6 n f).K →* X}
    (hker : ψ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K) (hperf : commutator ↥G₀ = ⊤)
    (hrange : ψ.range = G₀) (hBfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥)
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hdiag : ∀ b ∈ B, GGPsiInnerDiag (ggU .twistedE6 n f).D ψ b) (hf : 1 ≤ f) :
    Nonempty (TwE6Act G₀ B hf) := by
  classical
  subst hrange
  obtain ⟨π, hπ, hkerπ, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  let πK : (ggU .twistedE6 n f).K →*
      ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)) := π
  have hπK : Function.Surjective πK := hπ
  have hkerπK : πK.ker = Subgroup.center (ggU .twistedE6 n f).K := hkerπ
  obtain ⟨θ, hθ⟩ := w7A_exists_theta hf hπK hkerπK hker
  have hkπ : ψ.ker ≤ π.ker := hker.trans hkerπ.ge
  have hex : ∀ b : ↥B, ∃ α : MulAut
        ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)),
      α ∈ LayerSixE.twInndiagAut f ∧ LayerSixE.GGInduces π ψ (b : X) α :=
    fun b => LayerSixE.exists_induces_twistedE6 hf hπval ψ hker hkπ (hBN b.2) (hdiag b b.2)
  choose αb hαbD hαb using hex
  have hαbD' : ∀ b : ↥B, αb b ∈ (RecipeExcLang.twConj (GaloisField 2 (2 * f))
      (frobQEquiv hf)).range := fun b => by
    rw [← twInndiagAut_eq_range_twConj hf]
    exact hαbD b
  choose w hw using hαbD'
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), show 2 * f = f * 2 by ring, pow_mul]
  have hσ : ∀ c : GaloisField 2 (2 * f), frobQEquiv hf c = c ^ 2 ^ f := fun c =>
    CFSG.LieType.Steinberg.Exceptional.frobQ_apply 2 f c
  have hmul : ∀ b b' : ↥B, w (b * b') = w b * w b' := by
    intro b b'
    apply NoOffTwE6Three.twConj_injective hf hK (frobQEquiv hf) hσ
    rw [map_mul, hw (b * b'), hw b, hw b']
    exact LayerSixE.GGInduces.unique hπ (hBN (b * b').2) (hαb (b * b'))
      ((hαb b).mul (hBN b'.2) (hαb b'))
  let lam : ↥B →* ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)) :=
    MonoidHom.mk' w hmul
  have hlam_inj : Function.Injective lam := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hm1 : w b = 1 := hb
    have hα1 : ∀ c : ↥(twistedE6RootGroup (GaloisField 2 (2 * f)) (frobQEquiv hf)),
        αb b c = c := fun c => by
      rw [← hw b, hm1, map_one, MulAut.one_apply]
    have hZ : ∀ j ∈ ψ.range, (b : X) * j * (b : X)⁻¹ * j⁻¹ ∈
        (Subgroup.center ↥ψ.range).map ψ.range.subtype := by
      intro j hj
      obtain ⟨u, rfl⟩ := hj
      obtain ⟨u', hu'⟩ := LayerSixE.exists_conj_eq (hBN b.2) u
      have hπ'' : πK u' = πK u := (hαb b u u' hu').trans (hα1 (πK u))
      have hc0 : πK (u' * u⁻¹) = 1 := by
        rw [map_mul, map_inv, hπ'']
        exact mul_inv_cancel (πK u)
      have hc : u' * u⁻¹ ∈ Subgroup.center (ggU .twistedE6 n f).K :=
        hkerπK.le (MonoidHom.mem_ker.mpr hc0)
      refine ⟨ψ.rangeRestrict (u' * u⁻¹), ?_, ?_⟩
      · show ψ.rangeRestrict (u' * u⁻¹) ∈ Subgroup.center ↥ψ.range
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨v, rfl⟩ := ψ.rangeRestrict_surjective g
        have hcv : v * (u' * u⁻¹) = (u' * u⁻¹) * v := (Subgroup.mem_center_iff.1 hc) v
        exact (map_mul ψ.rangeRestrict v (u' * u⁻¹)).symm.trans
          ((congrArg ψ.rangeRestrict hcv).trans
            (map_mul ψ.rangeRestrict (u' * u⁻¹) v))
      · show ψ (u' * u⁻¹) = (b : X) * ψ u * (b : X)⁻¹ * (ψ u)⁻¹
        rw [map_mul, map_inv, hu']
    have hZJ : ∀ z ∈ (Subgroup.center ↥ψ.range).map ψ.range.subtype, ∀ j ∈ ψ.range,
        z * j = j * z := by
      rintro _ ⟨c, hc, rfl⟩ j hj
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨j, hj⟩)).symm
    have hZZ : ∀ z ∈ (Subgroup.center ↥ψ.range).map ψ.range.subtype,
        ∀ z' ∈ (Subgroup.center ↥ψ.range).map ψ.range.subtype, z * z' = z' * z := by
      rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc c')).symm
    have hcomm := commute_of_central_commutator' hperf hZJ hZZ hZ
    have hbC : (b : X) ∈ Subgroup.centralizer (ψ.range : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact (hcomm j hj).symm
    have hbbot : (b : X) ∈ B ⊓ Subgroup.centralizer (ψ.range : Set X) :=
      Subgroup.mem_inf.2 ⟨b.2, hbC⟩
    rw [hBfaith, Subgroup.mem_bot] at hbbot
    exact Subtype.ext hbbot
  refine ⟨θ, lam, hlam_inj, ?_⟩
  intro b y y' hy'
  obtain ⟨u, rfl⟩ := ψ.rangeRestrict_surjective y
  obtain ⟨u', rfl⟩ := ψ.rangeRestrict_surjective y'
  have hψu : ψ u' = (b : X) * ψ u * (b : X)⁻¹ := hy'
  have h1 : πK u' = αb b (πK u) := hαb b u u' hψu
  change ((θ (QuotientGroup.mk (ψ.rangeRestrict u')) : ↥(twistedE6RootGroup
      (GaloisField 2 (2 * f)) (frobQEquiv hf))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
    ((lam b : ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f)) (frobQEquiv hf))) :
      ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
    ((θ (QuotientGroup.mk (ψ.rangeRestrict u)) : ↥(twistedE6RootGroup
      (GaloisField 2 (2 * f)) (frobQEquiv hf))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
    ((lam b : ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f)) (frobQEquiv hf))) :
      ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))⁻¹
  rw [hθ, hθ, h1, ← hw b]
  exact RecipeExcLang.coe_twConj (frobQEquiv hf) (w b) (πK u)

theorem GGTCHyp.exists_act_twE6
    {ψ : (ggU .twistedE6 n f).K →* X} (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x)
    (hf : 1 ≤ f) : Nonempty (TwE6Act G₀ B hf) :=
  exists_act_twE6_of_facts h.ker h.perfect h.range h.b_faithful h.b_norm h.b_diag hf

end Act

end CFSG.StandardType.TableCRes

end
