module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearModel
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearNormalizer
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gen
import CFSG.CGT.T75N.L29Transport
public import CFSG.LargeExtraspecial.SL4ModMain
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.Sporadic.Schreier.TitsIso

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open Module CFSG.LargeExtraspecial.SL4Mod CFSG.Quasithin CFSG.Open
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
  CFSG.LieType.SpecialLinear
open CFSG.Blueprint (LieModel)

@[expose] def slLinearHom {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
    {L : Subgroup (MulAut W)} (σ : SL4 ≃* ↥L) : SL4 →* (Additive W ≃ₗ[ZMod 2] Additive W) where
  toFun x := mulAutLinearEquiv ((σ x : ↥L) : MulAut W)
  map_one' := LinearEquiv.ext fun v => by
    show mulAutLinear ((σ 1 : ↥L) : MulAut W) v = v
    rw [map_one]
    rfl
  map_mul' x y := LinearEquiv.ext fun v => by
    show mulAutLinear ((σ (x * y) : ↥L) : MulAut W) v =
      mulAutLinear ((σ x : ↥L) : MulAut W) (mulAutLinear ((σ y : ↥L) : MulAut W) v)
    rw [map_mul]
    rfl

@[expose] def InnerRankFour (D : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V],
    finrank (ZMod 2) V = D → ∀ ρ : SL4 →* (V ≃ₗ[ZMod 2] V), IsIrredGen ρ →
      ∀ y : SL4, y * y = 1 → y ≠ 1 →
        4 ≤ finrank (ZMod 2) (LinearMap.range ((ρ y : V →ₗ[ZMod 2] V) - 1))

@[expose] def OuterRankFour (D : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V],
    finrank (ZMod 2) V = D → ∀ ρ : SL4 →* (V ≃ₗ[ZMod 2] V), IsIrredGen ρ →
      ∀ (B : GL (Fin 4) (ZMod 2)), IsUpperGL B → ∀ τ : ZMod 2 ≃+* ZMod 2,
        ∀ d : V ≃ₗ[ZMod 2] V, d * d = 1 →
          (∀ (y : SL4) (v : V), d (ρ y v) = ρ (borelStd 4 (ZMod 2) B τ 1 y) (d v)) →
            4 ≤ finrank (ZMod 2) (LinearMap.range ((d : V →ₗ[ZMod 2] V) - 1))

theorem isIrredGen_slLinearHom {W : Type} [CommGroup W] [Finite W]
    [Module (ZMod 2) (Additive W)] {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L)
    (σ : SL4 ≃* ↥L) : IsIrredGen (slLinearHom σ) := by
  have h := (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff _).1
    (isIrreducible_specialLinearRep hctx σ)
  intro W' hW'
  exact h.2 W' fun g u hu => forall_mem_of_gen (slLinearHom σ) hW' g u hu

theorem finRowStmt_psl_four_two_of_ranks
    (D : ℕ)
    (hinner : InnerRankFour D) (houter : OuterRankFour D) : FinRowStmt .PSL 4 1 D := by
  intro W _ _ hW Y L g hctx hgY hg2 hlie hcard
  obtain ⟨K, _, _, hK, ⟨σK⟩⟩ := exists_mulEquiv_specialLinear_of_lieModel hctx (by norm_num) hlie
  have hZ : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  let φ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (hK.trans hZ.symm)
  let σ : SL4 ≃* ↥L := (CFSG.CGT.T75N.slRingEquiv 4 φ.symm).trans σK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : ∀ a : Additive W, (2 : ℕ) • a = 0 := fun a => by
    apply Additive.toMul.injective
    show (Additive.toMul a) ^ 2 = 1
    exact hW _
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule hW2
  haveI : Finite (Additive W) := ‹Finite W›
  haveI : FiniteDimensional (ZMod 2) (Additive W) := Module.Finite.of_finite
  have hLY : L ≤ Y := hctx.2.2.1
  have hirr : IsIrredGen (slLinearHom σ) := isIrredGen_slLinearHom hctx σ
  have hcardA : Nat.card (Additive W) = 2 ^ D := by
    rw [← hcard]
    exact Nat.card_congr Additive.toMul
  have hfin : finrank (ZMod 2) (Additive W) = D := by
    haveI : Fintype (Additive W) := Fintype.ofFinite _
    have h1 : Fintype.card (Additive W) = 2 ^ finrank (ZMod 2) (Additive W) := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card 2]
    rw [Nat.card_eq_fintype_card, h1] at hcardA
    exact Nat.pow_right_injective le_rfl hcardA
  have hG : Subgroup.center SL4 = ⊥ := center_specialLinear_eq_bot_of_card_two hZ
  have hπ := slToY_injective hLY σ
  have hg2' : g * g = 1 := by
    have h : g ^ 2 = 1 := by rw [← hg2]; exact pow_orderOf_eq_one g
    simpa [pow_two] using h
  have hgY2 : (⟨g, hgY⟩ : ↥Y) * ⟨g, hgY⟩ = 1 := Subtype.ext hg2'
  obtain ⟨x, hx⟩ := exists_conj_mem_range_or_borelStd_one hZ (by norm_num) (slToY hLY σ) hπ
    (fun c hc => by rw [eq_one_of_mem_centralizer_slToY hctx σ hG hc]; simp)
    (slToY_mem_normalizer hctx σ hgY) hgY2
  set g' : ↥Y := (slToY hLY σ x)⁻¹ * ⟨g, hgY⟩ * slToY hLY σ x with hg'
  have hg'2 : g' * g' = 1 := by
    calc g' * g' = (slToY hLY σ x)⁻¹ * ((⟨g, hgY⟩ : ↥Y) * ⟨g, hgY⟩) * slToY hLY σ x := by
          rw [hg']; group
      _ = 1 := by rw [hgY2]; group
  have hconj : E3.mQuot ⊤ (fixV (Subgroup.zpowers (g' : MulAut W))) =
      E3.mQuot ⊤ (fixV (Subgroup.zpowers g)) := by
    have h := w135c2_mQuot_conj (((slToY hLY σ x : ↥Y) : MulAut W)⁻¹) g
    simpa [hg'] using h
  rw [← hconj, mQuot_fixV_zpowers_eq_finrank_range_sub_one]
  rcases hx with ⟨y, hy⟩ | ⟨B, hB, τ, hgraph⟩
  · have hy2 : y * y = 1 := by
      apply hπ
      rw [map_mul, hy, hg'2, map_one]
    have hy1 : y ≠ 1 := by
      rintro rfl
      have h1 : g' = 1 := by rw [← hy, map_one]
      have h2 : (⟨g, hgY⟩ : ↥Y) = 1 := by
        calc (⟨g, hgY⟩ : ↥Y) = slToY hLY σ x * g' * (slToY hLY σ x)⁻¹ := by rw [hg']; group
          _ = 1 := by rw [h1]; group
      have h3 : g = 1 := congrArg Subtype.val h2
      rw [h3, orderOf_one] at hg2
      omega
    have hrank := hinner (Additive W) hfin (slLinearHom σ) hirr y hy2 hy1
    have hmul : mulAutLinear (g' : MulAut W) = ((slLinearHom σ y : Additive W ≃ₗ[ZMod 2]
        Additive W) : Additive W →ₗ[ZMod 2] Additive W) := by
      apply LinearMap.ext
      intro v
      rw [← hy]
      rfl
    rw [hmul]
    exact hrank
  · have hgg : (g' : MulAut W) * (g' : MulAut W) = 1 := congrArg Subtype.val hg'2
    have hdd : mulAutLinearEquiv (g' : MulAut W) * mulAutLinearEquiv (g' : MulAut W) = 1 := by
      apply LinearEquiv.ext
      intro w
      show mulAutLinear (g' : MulAut W) (mulAutLinear (g' : MulAut W) w) = w
      rw [← Module.End.mul_apply, ← mulAutLinear_mul, hgg, mulAutLinear_one]
      rfl
    have hdy : ∀ (y : SL4) (w : Additive W), mulAutLinearEquiv (g' : MulAut W)
        (slLinearHom σ y w) = slLinearHom σ (borelStd 4 (ZMod 2) B τ 1 y)
          (mulAutLinearEquiv (g' : MulAut W) w) := by
      intro y w
      have h := congrArg (fun z : ↥Y => (z : MulAut W) (Additive.toMul w)) (hgraph y)
      exact congrArg Additive.ofMul h
    have hrank := houter (Additive W) hfin (slLinearHom σ) hirr B hB τ
      (mulAutLinearEquiv (g' : MulAut W)) hdd hdy
    exact hrank

end CFSG.LocalAnalysis.WeakClosure81
