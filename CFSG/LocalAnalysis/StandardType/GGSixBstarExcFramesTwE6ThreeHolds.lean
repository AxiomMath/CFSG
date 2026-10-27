module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeNormalizer
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6InnerForm
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6NonsplitThree
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeylTypes
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6Tools
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl
public import CFSG.HardMathSupport.Malle.E27Lie.ExcTwisted.SylowN
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestField
public import CFSG.LieType.Chevalley.DiagonalFieldActorData

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.CentralCover
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Malle.E27Lie CFSG.Timmesfeld.ExceptionalOrders CFSG.ClassicalInvolution
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.StandardType.NoOffE6Three

namespace ExcFrames

section Holds


private theorem isElemAbelian_top_f4 :
    IsElemAbelian 3 (⊤ : Subgroup (Multiplicative (Fin Tag.F4.rank → ZMod 3))) := by
  refine ⟨inferInstance, fun x _ => ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private theorem card_range_of_injective {f : ℕ}
    {ι : Multiplicative (Fin Tag.F4.rank → ZMod 3) →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hinj : Function.Injective ι) : Nat.card ι.range = 3 ^ 4 := by
  rw [← Subgroup.map_top ι, Subgroup.card_map_of_injective (f := ι) hinj,
    Subgroup.card_top, Nat.card_eq_fintype_card]
  change Fintype.card (Fin 4 → ZMod 3) = 3 ^ 4
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

theorem twistedE6ThreeRefFrame_holds : TwistedE6ThreeRefFrame := by
  intro f hf h3
  obtain ⟨ζ, hζ, ι, hζo, hinj, happly, hmem, hlast⟩ := exists_threeFrame hf h3
  have hιpoint : ∀ s : Multiplicative (Fin Tag.F4.rank → ZMod 3),
      ι s = twE6ThreeFrameHom hf h3 ζ hζ s := by
    intro s
    apply Subtype.ext
    rw [← ofAdd_toAdd s, happly (Multiplicative.toAdd s),
      twE6ThreeFrameHom_apply hf h3 hζ (Multiplicative.toAdd s)]
    rfl
  have hrange : (twE6ThreeFrameHom hf h3 ζ hζ).range = ι.range := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, hιpoint s⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s, (hιpoint s).symm⟩
  have hA₀ : IsElemAbelian 3 ι.range := by
    rw [← Subgroup.map_top ι]
    exact CFSG.Open.IsElemAbelian.map isElemAbelian_top_f4 ι
  have hA₀4 : 3 ^ 4 ≤ Nat.card ι.range := (card_range_of_injective hinj).ge
  have hA₀SC : ∀ c ∈ Subgroup.centralizer (ι.range : Set
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))), c ^ 3 = 1 →
        c ∈ ι.range := by
    intro c hc hc3
    have hcent : ∀ s : Multiplicative (Fin Tag.F4.rank → ZMod 3),
        c * twE6ThreeFrameHom hf h3 ζ hζ s =
          twE6ThreeFrameHom hf h3 ζ hζ s * c := by
      intro s
      have h1 := (Subgroup.mem_centralizer_iff.mp hc) _ (show ι s ∈ ι.range from ⟨s, rfl⟩)
      rw [hιpoint s] at h1
      exact h1.symm
    have hH : (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
        graphFixedRootTorus TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) :=
      mem_graphFixedRootTorus_of_centralizes_twE6ThreeFrame hf h3 hζo hζ hcent
    exact hlast c hH hc3
  refine ⟨ι.range, ι, hA₀, hA₀4, hA₀SC, hinj, rfl, ?_⟩
  intro β hβ hβA
  obtain ⟨x, δ, hδ, hβeq⟩ := exists_inner_normalForm_twistedE6 hf h3 β hβ
  have hδfix : δ ((ζ : (GaloisField 2 (2 * f))ˣ) : GaloisField 2 (2 * f)) =
      (ζ : GaloisField 2 (2 * f)) := by
    apply OrdPRest.ringAut_fix_of_pow_eq_one Nat.prime_three hδ
    have h := congrArg Units.val hζ
    simpa using h
  have hδfixU : Units.map δ.toRingHom.toMonoidHom ζ = ζ := Units.ext hδfix
  have hδpow : ∀ (u : (GaloisField 2 (2 * f))ˣ), (∃ m : ℕ, u = ζ ^ m) →
      Units.map δ.toRingHom.toMonoidHom u = u := by
    rintro u ⟨m, rfl⟩
    rw [map_pow, hδfixU]
  have hδι : ∀ s : Multiplicative (Fin Tag.F4.rank → ZMod 3),
      Units.map (entrywiseHom δ.toRingHom)
          ((ι s : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        ((ι s : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) := by
    intro s
    let b : Fin Tag.E6.rank → (GaloisField 2 (2 * f))ˣ :=
      TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame (Multiplicative.toAdd s))
    have hb : ((ι s : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        (show ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)) from rootDiagUnit Tag.E6 b) := by
      rw [hιpoint s]
      exact twE6ThreeFrameHom_apply hf h3 hζ (Multiplicative.toAdd s)
    rw [hb]
    change Units.map (entrywiseHom δ.toRingHom) (rootDiagUnit Tag.E6 b) =
      rootDiagUnit Tag.E6 b
    rw [units_map_entrywiseHom_rootDiagUnit_ringEquiv]
    congr 1
    funext i
    dsimp only [b]
    exact hδpow _ ⟨(twE6ThreeFrame (Multiplicative.toAdd s) i).val, by
      rw [TableBExc.E6Three.zetaVec_apply]⟩
  have hβι : ∀ s : Multiplicative (Fin Tag.F4.rank → ZMod 3),
      β (ι s) = x * ι s * x⁻¹ := by
    intro s
    have h := hβeq (ι s)
    rw [hδι s] at h
    exact Subtype.ext h
  have hxnorm : ∀ s : Multiplicative (Fin Tag.F4.rank → ZMod 3),
      x * ι s * x⁻¹ ∈ ι.range := by
    intro s
    rw [← hβι s]
    exact hβA _ ⟨s, rfl⟩
  have hxN : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      graphFixedRootMonomial TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) := by
    apply mem_graphFixedRootMonomial_of_normalizes_twE6ThreeFrame hf h3 hζo hζ
    intro s
    rw [← hιpoint s, hrange]
    exact hxnorm s
  refine ⟨foldedWeylEquiv TwistTag.E6
    ⟨graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
      ⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hxN⟩,
      (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f)).le (show _ ∈ (graphFixedRootWeylHom TwistTag.E6
          (GaloisField 2 (2 * f)) (frobQ 2 f)).range from
            ⟨⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hxN⟩, rfl⟩)⟩,
      fun s => ?_⟩
  apply Subtype.ext
  rw [hβι (Multiplicative.ofAdd s)]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hιpoint (Multiplicative.ofAdd s),
    hιpoint (Multiplicative.ofAdd (TableBExc.torusAct .F4 3
      (foldedWeylEquiv TwistTag.E6
        ⟨graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
          ⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hxN⟩,
          graphFixedRootWeylHom_mem_relWeylTwist x hxN⟩) s))]
  exact twE6ThreeFrameHom_conj hf h3 hζo hζ hxN s

theorem mem_range_twE6ThreeFrameHom_of_mem_torus
    {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {h : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hH : (h : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      graphFixedRootTorus TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))
    (h3h : h ^ 3 = 1) :
    h ∈ (twE6ThreeFrameHom hf h3 ζ hζ).range := by
  have hσsurj : Function.Surjective (frobQ 2 f) :=
    Function.RightInverse.surjective fun c => frobQ_frobQ 2 f hf c
  have hHc : (h : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      compatTorus (t := TwistTag.E6) (frobQ 2 f) := by
    rw [← graphFixedRootTorus_eq_compatTorus (t := TwistTag.E6)
      (K := GaloisField 2 (2 * f)) (σ := frobQ 2 f) hσsurj]
    exact hH
  obtain ⟨c, hc, hct⟩ :=
    (mem_compatTorus (t := TwistTag.E6) (K := GaloisField 2 (2 * f))
      (σ := frobQ 2 f)).1 hHc
  have hroot : (h : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      rootDiagUnit TwistTag.E6.tag (cartanChar (τ := TwistTag.E6.tag) c) := by
    rw [← hct, CFSG.RankThree.PartOne.TCX.Tri.torusCoordHom_eq_rootDiagUnit
      (τ := TwistTag.E6.tag) (K := GaloisField 2 (2 * f)) c]
    rfl
  have hv3 : (rootDiagUnit TwistTag.E6.tag
      (cartanChar (τ := TwistTag.E6.tag) c)) ^ 3 = 1 := by
    rw [← hroot]
    exact congrArg Subtype.val h3h
  have hcart3 : (cartanChar (τ := TwistTag.E6.tag) c) ^ 3 = 1 := by
    apply rootDiagUnit_injective
    simpa [rootDiagUnit_pow, rootDiagUnit_one] using hv3
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    TwE6Toral.card_galoisField_two_mul f hf
  have hg : Nat.gcd 3 (2 ^ f + 1) = 1 :=
    Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  have hc3 : c ^ 3 = 1 := by
    have hcart : cartanChar (τ := TwistTag.E6.tag) c =
        zpowMatrix (G := (GaloisField 2 (2 * f))ˣ) TwistTag.E6.tag.cartan c := rfl
    have hA : zpowMatrix (G := (GaloisField 2 (2 * f))ˣ) TwistTag.E6.tag.cartan (c ^ 3) = 1 := by
      have h1 : zpowMatrix (G := (GaloisField 2 (2 * f))ˣ) TwistTag.E6.tag.cartan (c ^ 3) =
          (zpowMatrix (G := (GaloisField 2 (2 * f))ˣ) TwistTag.E6.tag.cartan c) ^ 3 := by
        rw [map_pow]
      rw [h1, ← hcart]
      exact hcart3
    have hmem : c ^ 3 ∈
        compatSubgroup (t := TwistTag.E6) (frobQ 2 f) ⊓
          (zpowMatrix (G := (GaloisField 2 (2 * f))ˣ) TwistTag.E6.tag.cartan).ker :=
      ⟨pow_mem hc 3, hA⟩
    have hcard := card_compat_inf_ker_E6_of_card (K := GaloisField 2 (2 * f))
      (q := 2 ^ f) hK (frobQ_apply 2 f)
    have hcard1 : Nat.card ↥(compatSubgroup (t := TwistTag.E6) (frobQ 2 f) ⊓
        (zpowMatrix (G := (GaloisField 2 (2 * f))ˣ) TwistTag.E6.tag.cartan).ker) = 1 := by
      rw [hcard, hg]
    have hbot : compatSubgroup (t := TwistTag.E6) (frobQ 2 f) ⊓
        (zpowMatrix (G := (GaloisField 2 (2 * f))ˣ) TwistTag.E6.tag.cartan).ker = ⊥ :=
      Subgroup.card_eq_one.1 hcard1
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  obtain ⟨x, hx⟩ := TableBExc.E6Three.exists_zetaVec_eq hζo hζ hc3
  have hq : ζ ^ (2 ^ f) = ζ := zeta_pow_frobQ_eq_self hζ h3
  have hxfix : ∀ i, x (TwistTag.E6.perm i) = x i := by
    intro i
    have h1 : c (TwistTag.E6.perm i) = Units.map (frobQ 2 f).toMonoidHom (c i) := hc i
    rw [← hx] at h1
    have h2 : TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ x
        (TwistTag.E6.perm i) = TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ x i := by
      rw [h1]
      refine Units.ext ?_
      change (frobQ 2 f) ((TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ x i :
          GaloisField 2 (2 * f))) =
        (TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ x i :
          GaloisField 2 (2 * f))
      have hq' : (frobQ 2 f)
          ((TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ x i :
            GaloisField 2 (2 * f))) =
          ((TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ x i :
            GaloisField 2 (2 * f))) ^ (2 ^ f) := frobQ_apply 2 f _
      rw [hq']
      have hval : (TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ x i :
          GaloisField 2 (2 * f)) = ζ ^ (x i).val := by
        simp [TableBExc.E6Three.zetaVec_apply]
      rw [hval]
      have hζq : ((↑ζ : GaloisField 2 (2 * f)) ^ (2 ^ f)) = ↑ζ :=
        congrArg Units.val hq
      exact (calc
        ((↑ζ : GaloisField 2 (2 * f)) ^ (x i).val) ^ (2 ^ f)
            = (↑ζ : GaloisField 2 (2 * f)) ^ ((x i).val * 2 ^ f) :=
              (pow_mul _ _ _).symm
        _ = (↑ζ : GaloisField 2 (2 * f)) ^ (2 ^ f * (x i).val) := by ring
        _ = ((↑ζ : GaloisField 2 (2 * f)) ^ (2 ^ f)) ^ (x i).val := pow_mul _ _ _
        _ = (↑ζ : GaloisField 2 (2 * f)) ^ (x i).val := by rw [hζq])
    have hzi : zmodPowHom ζ hζ (Multiplicative.ofAdd (x (TwistTag.E6.perm i))) =
        zmodPowHom ζ hζ (Multiplicative.ofAdd (x i)) := h2
    exact Multiplicative.ofAdd.injective (zmodPowHom_injective hζo hζ hzi)
  have hx0 : x (e6Idx 0) = x e6Five := by
    have hp0 : e6Perm 0 = e6Five := by decide
    have h := hxfix 0
    rw [show TwistTag.E6.perm 0 = e6Perm 0 from rfl, hp0,
      show (0 : Fin TwistTag.E6.tag.rank) = e6Idx 0 from rfl] at h
    exact h.symm
  have hx2 : x (e6Idx 2) = x e6Four := by
    have hp2 : e6Perm 2 = e6Four := by decide
    have h := hxfix 2
    rw [show TwistTag.E6.perm 2 = e6Perm 2 from rfl, hp2,
      show (2 : Fin TwistTag.E6.tag.rank) = e6Idx 2 from rfl] at h
    exact h.symm
  obtain ⟨s, hs⟩ := exists_twE6ThreeTheta_eq x hx0 hx2
  refine ⟨Multiplicative.ofAdd s, ?_⟩
  apply Subtype.ext
  rw [show (twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) :
      ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      frameDiag (τ := TwistTag.E6.tag) ζ hζ
        (fun i : Fin TwistTag.E6.tag.rank => twE6ThreeTheta s i) from rfl]
  rw [show (fun i : Fin TwistTag.E6.tag.rank => twE6ThreeTheta s i) =
      (fun i : Fin TwistTag.E6.tag.rank => x i) from by
    funext i; rw [hs]]
  change rootDiagUnit TwistTag.E6.tag
      (TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ
        (frameCoord TwistTag.E6.tag 3 (fun i : Fin TwistTag.E6.tag.rank => x i))) = ↑h
  change rootDiagUnit TwistTag.E6.tag
      (TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζ hζ
        (frameCoord TwistTag.E6.tag 3 x)) = ↑h
  rw [← zetaVec_cartanChar hζ x, hx]
  exact hroot.symm

abbrev TwistedE6ThreeSCReference : Prop :=
  ∀ {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {A : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))},
    IsElemAbelian 3 A → 3 ^ 4 ≤ Nat.card A →
    (∀ c ∈ Subgroup.centralizer (A : Set
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))), c ^ 3 = 1 →
        c ∈ A) →
    ∃ c : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      A = (twE6ThreeFrameHom hf h3 ζ hζ).range.map (MulAut.conj c).toMonoidHom

theorem twistedE6ThreeSCUnique_of_scReference (hSC : TwistedE6ThreeSCReference) :
    TwistedE6ThreeSCUnique := by
  intro f hf h3 A A' hA hA4 hASC hA' hA'4 hA'SC
  obtain ⟨ζ, hζ, ι, hζo, hinj, happly, hmem, hlast⟩ := exists_threeFrame hf h3
  obtain ⟨c, hc⟩ := hSC hf h3 hζo hζ hA hA4 hASC
  obtain ⟨c', hc'⟩ := hSC hf h3 hζo hζ hA' hA'4 hA'SC
  refine ⟨c' * c⁻¹, ?_⟩
  have hcomp : (MulAut.conj (c' * c⁻¹)).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj c').toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  rw [hc', hc, Subgroup.map_map, hcomp]

end Holds

end ExcFrames

end CFSG.StandardType
