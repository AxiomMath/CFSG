module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Split
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusFrameFusion
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnModel
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelE6Cover
import CFSG.LocalAnalysis.StandardType.GGF4NbrAutReflKGReduce

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem twm_two_le {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hpn : p ∣ 2 ^ n - 1) :
    2 ≤ n := by
  by_contra h
  have hn1 : n = 1 := by omega
  rw [hn1] at hpn
  have h1 : p ∣ 1 := by simpa using hpn
  exact hp.ne_one (Nat.dvd_one.mp h1)

theorem ggTwE6Split_model_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n - 1) (hZ : Subgroup.center ↥K = ⊥) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (F : Type) (_ : Field F) (_ : Finite F)
      (σ : F →+* F) (_ : Nat.card F = (2 ^ n) ^ 2) (_ : ∀ c, σ c = c ^ 2 ^ n)
      (ζ : Fˣ) (hζ : ζ ^ p = 1) (hζσ : σ (ζ : F) = ζ)
      (e : ↥K ≃* ↥(graphFixedRootGroup TwistTag.E6 F σ)),
      orderOf ζ = p ∧
      (ggGamma K hN).range.map (MulAut.congr e).toMonoidHom =
        (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range.map
          (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 F σ) →*
            MulAut ↥(graphFixedRootGroup TwistTag.E6 F σ)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hn2 : 2 ≤ n := twm_two_le hp hΛ.1 hpn
  have hn : 1 ≤ n := by omega
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hinnerDiag : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  obtain ⟨hKperf, lab, _hlab, hraw⟩ :=
    ggInnerDiagOn_relabel hRig hinnerDiag hΛ hK
  let Q : LargeEvenRawCont := fun R x I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : ↥K ⧸ Subgroup.center ↥K ≃* R,
        (fun lab' x x_1 I x_2 (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) =>
          lab' = { tag := LargeEvenLieTag.twE6, rank := 0, n := n } ∧
            Bs ≤ Subgroup.normalizer (K : Set G) ∧
            ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
        lab R x I F θ
  have hraw_canon : LargeEvenRawDatum lab Q := (largeEvenRawDatum_legacy lab Q).mpr hraw
  obtain ⟨R, _instR, I, F_set, hQ⟩ := largeEvenRawDatum_exists (Q := Q) hraw_canon
  obtain ⟨_hSimple0, _hNA0, _θ0, hP0⟩ := hQ
  obtain ⟨hlabeq, _hNmark0, _hBsI0⟩ := hP0
  have hlab_eq : lab = ⟨.twE6, 0, n⟩ := hlabeq
  obtain ⟨F, _instF, _finF, hFcard, hQF⟩ := (hlab_eq ▸ hraw)
  obtain ⟨_hSimple, _hNA, θ, hP⟩ := hQF
  obtain ⟨_hlabeq, hNmark, hBsI⟩ := hP
  let e1 : ↥K ≃* TwE6Delta.RecipeR F n :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ).symm).trans θ
  have hliftAll : LargeEvenLabelAll ⟨.twE6, 0, n⟩ fun R _ _ _ => GGTorusLift p 4 R :=
    largeEvenLabelAll_torusLift_twE6Dvd hp hp2 hΛ ⟨rfl, hpn⟩
  obtain ⟨R₀, _instR₀, _finR₀, _hR₀card, hQ₀⟩ := hliftAll _ (hlab_eq ▸ hraw)
  obtain ⟨⟨_, _, ⟨θ₀, _⟩⟩, hlift₀⟩ := hQ₀
  have hlift : GGTorusLift p 4 (TwE6Delta.RecipeR F n) :=
    TableBF4.ggTorusLift_of_mulEquiv (θ.symm.trans θ₀) hlift₀
  have hlb : p ^ 4 ≤ Nat.card (ggGamma K hNmark).range :=
    pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hnb hKperf θ hNmark hlift
  have hOut : GGOutdiagPrime p (TwE6Delta.RecipeR F n) (TwE6Delta.RecipeI F n) :=
    TwE6Delta.ggOutdiagPrime_twE6 hn hFcard hp hp3
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hinner : ∀ b ∈ Bs, ∃ x ∈ K, ∀ l ∈ K, b * l * b⁻¹ = x * l * x⁻¹ := by
    refine F4AutRefl.exists_conj_of_inn hKperf θ
      (I := Set.range (MulAut.conj : TwE6Delta.RecipeR F n →* MulAut (TwE6Delta.RecipeR F n)))
      Set.Subset.rfl hNmark ?_
    intro b hb
    obtain ⟨φ, hφI, hφ⟩ := hBsI b hb
    refine ⟨φ, hOut φ hφI ?_, hφ⟩
    rw [eq_ggLAut_of_induces K θ (hNmark hb) hφ, ← map_pow]
    have hb1 : (⟨b⁻¹, inv_mem (hNmark hb)⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 := by
      apply Subtype.ext
      simp [inv_pow, hBs.2 b hb]
    rw [hb1, map_one]
  haveI : CharP F 2 :=
    charP_two_of_card (K := F) (m := 2 * n) (by rw [hFcard, ← pow_mul, mul_comm])
  let σ : F →+* F := iterateFrobenius F 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have hpF : p ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hFcard]
    have h1 : 2 ^ n - 1 ∣ (2 ^ n) ^ 2 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2
    exact hpn.trans h1
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpF
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζσ : σ (ζ : F) = ζ := by
    obtain ⟨k, hk⟩ := id hpn
    have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    have hq : 2 ^ n = p * k + 1 := by omega
    rw [hσ, ← Units.val_pow_eq_pow_val, hq, pow_add, pow_mul, hζ, one_pow, one_mul, pow_one]
  obtain ⟨e2⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hn hFcard σ hσ
  let e0 : ↥K ≃* ↥(graphFixedRootGroup TwistTag.E6 F σ) := e1.trans e2
  obtain ⟨E', hE'el, -, hE'sc, hγ⟩ :=
    ggEnnAdjointModel (r := 4) hBs hSC e0 hZ hinner hNmark hlb
  have hT : SylowTorus ↥(graphFixedRootGroup TwistTag.E6 F σ) p 4 :=
    (sylowTorus_recipeR_split hn hFcard hp hp5 hpn).of_mulEquiv e2
  set ι := ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ with hιdef
  have hιinj : Function.Injective ι := ExcFrames.twE6SplitFrameHom_injective σ hp5 hζo hζ hζσ
  have hEl : IsElemAbelian p ι.range := by
    refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ?_⟩
    · obtain ⟨u, hu⟩ := a.2
      obtain ⟨v, hv⟩ := b.2
      change (a : ↥(graphFixedRootGroup TwistTag.E6 F σ)) * b = b * a
      rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨u, rfl⟩ := hx
      rw [← map_pow, ← ofAdd_toAdd u, ← ofAdd_nsmul, ZModModule.char_nsmul_eq_zero, ofAdd_zero,
        map_one]
  have hcard : Nat.card ι.range = p ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin Tag.F4.rank → ZMod p) ≃ _),
      Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  obtain ⟨c, hc⟩ := exists_conj_eq_of_selfCentralizing_of_sylowTorus hp hT hEl hcard hE'el hE'sc
  refine ⟨hNmark, F, inferInstance, inferInstance, σ, hFcard, hσ, ζ, hζ, hζσ,
    e0.trans (MulAut.conj c⁻¹), hζo, ?_⟩
  have hcomp : (MulAut.congr (e0.trans (MulAut.conj c⁻¹))).toMonoidHom =
      (MulAut.congr (MulAut.conj c⁻¹)).toMonoidHom.comp (MulAut.congr e0).toMonoidHom := by
    refine MonoidHom.ext fun a => MulEquiv.ext fun x => ?_
    simp [MulAut.congr_apply]
  have hconj : (MulAut.congr (MulAut.conj c⁻¹)).toMonoidHom.comp
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 F σ) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 F σ)) =
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 F σ) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 F σ)).comp (MulAut.conj c⁻¹).toMonoidHom := by
    refine MonoidHom.ext fun r => MulEquiv.ext fun x => ?_
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hE : E'.map (MulAut.conj c⁻¹).toMonoidHom = ι.range := by
    rw [hc, map_conj_map_conj_sylowTorusFusion, inv_mul_cancel]
    ext g
    simp
  rw [hcomp, ← Subgroup.map_map, hγ, Subgroup.map_map, hconj, ← Subgroup.map_map, hE]

end CFSG.StandardType

end
