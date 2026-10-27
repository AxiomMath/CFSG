module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeHolds
public import CFSG.GroupTheory.GL52.Basic
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.CentralCover
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Malle.E27Lie CFSG.Timmesfeld.ExceptionalOrders CFSG.ClassicalInvolution
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.StandardType.NoOffE6Three

namespace ExcFrames

section GraphFixed


private abbrev TwE6GL (f : ℕ) : Type := ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))

private abbrev TwE6G (f : ℕ) : Subgroup (TwE6GL f) :=
  graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)

private abbrev TwE6C (f : ℕ) : Type := ↥(TwE6G f)

private abbrev TwE6N (f : ℕ) : Subgroup (TwE6GL f) :=
  graphFixedRootMonomial TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)

end GraphFixed

private theorem two_pow_mod_three_of_not_dvd_add_one {f : ℕ} (h3 : ¬ 3 ∣ 2 ^ f + 1) :
    2 ^ f % 3 = 1 := by
  have h := CFSG.Timmesfeld.ExceptionalOrders.two_pow_mod_three f
  by_cases hf : Even f
  · simpa [hf] using h
  · exfalso
    have hp : 2 ^ f % 3 = 2 := by simpa [hf] using h
    apply h3
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hp]

local instance threePrime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

section Transport


private theorem sc_map_conj {f : ℕ} {A : Subgroup (TwE6C f)}
    (hSC : ∀ y ∈ Subgroup.centralizer (A : Set (TwE6C f)), y ^ 3 = 1 → y ∈ A) (c : TwE6C f) :
    ∀ y ∈ Subgroup.centralizer
        ((A.map (MulAut.conj c).toMonoidHom : Subgroup (TwE6C f)) : Set (TwE6C f)), y ^ 3 = 1 →
      y ∈ A.map (MulAut.conj c).toMonoidHom := by
  intro y hy hy3
  rw [CFSG.GroupTheory.GL52.centralizer_map_conj c A] at hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨z, hSC z hz ?_, rfl⟩
  have h1 : MulAut.conj c (z ^ 3) = MulAut.conj c 1 := by
    rw [map_pow, map_one]
    exact hy3
  exact (MulAut.conj c).injective h1

private theorem sc_transport {f : ℕ} {A : Subgroup (TwE6C f)} (hA : IsElemAbelian 3 A)
    (hA4 : 3 ^ 4 ≤ Nat.card A)
    (hSC : ∀ y ∈ Subgroup.centralizer (A : Set (TwE6C f)), y ^ 3 = 1 → y ∈ A) (c : TwE6C f) :
    IsElemAbelian 3 (A.map (MulAut.conj c).toMonoidHom) ∧
      3 ^ 4 ≤ Nat.card (A.map (MulAut.conj c).toMonoidHom) ∧
      (∀ y ∈ Subgroup.centralizer
        ((A.map (MulAut.conj c).toMonoidHom : Subgroup (TwE6C f)) : Set (TwE6C f)), y ^ 3 = 1 →
          y ∈ A.map (MulAut.conj c).toMonoidHom) :=
  ⟨CFSG.Open.IsElemAbelian.map hA _, by
      rw [Subgroup.card_map_of_injective (K := A) (f := (MulAut.conj c).toMonoidHom)
        (MulAut.conj c).injective]
      exact hA4,
    sc_map_conj hSC c⟩

end Transport

section Sylow


private theorem exists_conj_map_le_monomial {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {A : Subgroup (TwE6C f)} (hA : IsPGroup 3 A) :
    ∃ c : TwE6C f, A.map (MulAut.conj c).toMonoidHom ≤ (TwE6N f).subgroupOf (TwE6G f) := by
  obtain ⟨P₀, hP₀⟩ := exists_sylow_three_le_graphFixedRootMonomial_E6
    (ℓ := 2) (f := f) Nat.prime_two hf (TwE6Toral.card_galoisField_two_mul f hf)
    (frobQ 2 f) (frobQ_apply 2 f) (two_pow_mod_three_of_not_dvd_add_one h3)
  obtain ⟨c, -, hc⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow (p := 3)
    (H := TwE6C f) ⊤ P₀ le_top A le_top hA
  exact ⟨c, hc.trans hP₀⟩

end Sylow

section Monomial


private noncomputable def frameWeylHom {f : ℕ} {A : Subgroup (TwE6C f)}
    (hN : ∀ a ∈ A, ((a : TwE6C f) : TwE6GL f) ∈ TwE6N f) :
    A →* WeylGroup Tag.F4 :=
  (foldedWeylEquiv TwistTag.E6).toMonoidHom.comp
    (MonoidHom.codRestrict
      ((graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).comp
        (MonoidHom.codRestrict
          ((Subgroup.subtype (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
            (frobQ 2 f))).comp (Subgroup.subtype A))
          (TwE6N f) (fun a => hN a a.2)))
      (relWeylTwist TwistTag.E6)
      (fun a => (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f)).le ⟨_, rfl⟩))

private theorem frameWeylHom_apply {f : ℕ} {A : Subgroup (TwE6C f)}
    (hN : ∀ a ∈ A, ((a : TwE6C f) : TwE6GL f) ∈ TwE6N f) (a : A) :
    frameWeylHom hN a =
      foldedWeylEquiv TwistTag.E6
        ⟨graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
          ⟨((a : TwE6C f) : TwE6GL f), hN a a.2⟩,
         (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f))
           (frobQ 2 f)).le ⟨⟨((a : TwE6C f) : TwE6GL f), hN a a.2⟩, rfl⟩⟩ := by
  rfl

private theorem frameWeylHom_conj {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {A : Subgroup (TwE6C f)}
    (hN : ∀ a ∈ A, ((a : TwE6C f) : TwE6GL f) ∈ TwE6N f)
    (a : A) (s : Fin Tag.F4.rank → ZMod 3) :
    (a : TwE6C f) * twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) *
        (a : TwE6C f)⁻¹ =
      twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd
        (TableBExc.torusAct .F4 3 (frameWeylHom hN a) s)) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, frameWeylHom_apply] using
    twE6ThreeFrameHom_conj hf h3 hζo hζ (x := (a : TwE6C f)) (hx := hN a a.2) s

end Monomial

section SC


private theorem mem_range_of_frameWeylHom_eq_one {f : ℕ} (hf : 1 ≤ f)
    (h3 : ¬ 3 ∣ 2 ^ f + 1) {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) {A : Subgroup (TwE6C f)}
    (hN : ∀ a ∈ A, ((a : TwE6C f) : TwE6GL f) ∈ TwE6N f)
    (hA : IsElemAbelian 3 A) {a : A} (ha : frameWeylHom hN a = 1) :
    (a : TwE6C f) ∈ (twE6ThreeFrameHom hf h3 ζ hζ).range := by
  have hw : graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
      ⟨((a : TwE6C f) : TwE6GL f), hN a a.2⟩ = 1 := by
    have h1 : foldedWeylEquiv TwistTag.E6
        ⟨graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
          ⟨((a : TwE6C f) : TwE6GL f), hN a a.2⟩,
         (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f))
           (frobQ 2 f)).le ⟨⟨((a : TwE6C f) : TwE6GL f), hN a a.2⟩, rfl⟩⟩ = 1 := by
      rw [← frameWeylHom_apply hN a]
      exact ha
    have h2 : (⟨graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
          ⟨((a : TwE6C f) : TwE6GL f), hN a a.2⟩,
         (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f))
           (frobQ 2 f)).le ⟨⟨((a : TwE6C f) : TwE6GL f), hN a a.2⟩, rfl⟩⟩ :
          relWeylTwist TwistTag.E6) = 1 :=
      (foldedWeylEquiv TwistTag.E6).injective (by rw [h1, map_one])
    simpa using congrArg Subtype.val h2
  have hker : (⟨((a : TwE6C f) : TwE6GL f), hN a a.2⟩ :
      ↥(TwE6N f)) ∈
        (graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).ker := by
    rw [MonoidHom.mem_ker]
    exact hw
  rw [graphFixedRootWeylHom_ker] at hker
  exact mem_range_twE6ThreeFrameHom_of_mem_torus hf h3 hζo hζ
    (Subgroup.mem_subgroupOf.mp hker) (hA.2 (a : TwE6C f) a.2)

private theorem range_eq_bot_of_card_ge {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {A : Subgroup (TwE6C f)}
    (hN : ∀ a ∈ A, ((a : TwE6C f) : TwE6GL f) ∈ TwE6N f)
    (hA : IsElemAbelian 3 A) (hA4 : 3 ^ 4 ≤ Nat.card A) :
    (frameWeylHom hN).range = ⊥ := by
  by_contra hne
  have hlt := card_lt_of_weylHom (τ := Tag.F4) (p := 3)
    (NoOffExc.ggWeylNoOffender_F4 Nat.prime_three (by norm_num))
    (twE6ThreeFrameHom hf h3 ζ hζ) (twE6ThreeFrameHom_injective hf h3 hζo hζ)
    (A := A) hA (frameWeylHom hN)
    (fun a s => frameWeylHom_conj hf h3 hζo hζ hN a s)
    (fun a ha => mem_range_of_frameWeylHom_eq_one hf h3 hζo hζ hN hA ha) hne
  change Nat.card A < 3 ^ 4 at hlt
  omega

private theorem eq_range_of_range_eq_bot {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {A : Subgroup (TwE6C f)}
    (hN : ∀ a ∈ A, ((a : TwE6C f) : TwE6GL f) ∈ TwE6N f)
    (hA : IsElemAbelian 3 A)
    (hSC : ∀ y ∈ Subgroup.centralizer (A : Set (TwE6C f)), y ^ 3 = 1 → y ∈ A)
    (hbot : (frameWeylHom hN).range = ⊥) :
    A = (twE6ThreeFrameHom hf h3 ζ hζ).range := by
  have hAle : A ≤ (twE6ThreeFrameHom hf h3 ζ hζ).range := by
    intro a ha
    refine mem_range_of_frameWeylHom_eq_one (a := ⟨a, ha⟩) hf h3 hζo hζ hN hA ?_
    have hmem : frameWeylHom hN ⟨a, ha⟩ ∈ (frameWeylHom hN).range := ⟨⟨a, ha⟩, rfl⟩
    rw [hbot] at hmem
    simpa using hmem
  have hcomm : ∀ x ∈ (twE6ThreeFrameHom hf h3 ζ hζ).range,
      ∀ y ∈ (twE6ThreeFrameHom hf h3 ζ hζ).range, x * y = y * x := by
    rintro x ⟨s, rfl⟩ y ⟨t, rfl⟩
    calc twE6ThreeFrameHom hf h3 ζ hζ s * twE6ThreeFrameHom hf h3 ζ hζ t
        = twE6ThreeFrameHom hf h3 ζ hζ (s * t) := (map_mul _ _ _).symm
      _ = twE6ThreeFrameHom hf h3 ζ hζ (t * s) :=
          congrArg (twE6ThreeFrameHom hf h3 ζ hζ) (mul_comm s t)
      _ = twE6ThreeFrameHom hf h3 ζ hζ t * twE6ThreeFrameHom hf h3 ζ hζ s :=
          map_mul _ _ _
  have hpow : ∀ x ∈ (twE6ThreeFrameHom hf h3 ζ hζ).range, x ^ 3 = 1 := by
    rintro x ⟨s, rfl⟩
    rw [← map_pow]
    have hs : s ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hs, map_one]
  have hrange_le : (twE6ThreeFrameHom hf h3 ζ hζ).range ≤ A := by
    intro x hx
    exact hSC x (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (hcomm x hx a (hAle ha)).symm) (hpow x hx)
  exact le_antisymm hAle hrange_le

theorem twistedE6ThreeSCReference_holds : TwistedE6ThreeSCReference := by
  intro f hf h3 ζ hζo hζ A hA hA4 hASC
  obtain ⟨c, hc⟩ := exists_conj_map_le_monomial hf h3
    (CFSG.Open.IsElemAbelian.isPGroup hA)
  obtain ⟨hA₁, hA₁4, hA₁SC⟩ := sc_transport hA hA4 hASC c
  have hN : ∀ a ∈ A.map (MulAut.conj c).toMonoidHom,
      ((a : TwE6C f) : TwE6GL f) ∈ TwE6N f :=
    fun a ha => hc ha
  have hbot := range_eq_bot_of_card_ge hf h3 hζo hζ hN hA₁ hA₁4
  have heq : A.map (MulAut.conj c).toMonoidHom = (twE6ThreeFrameHom hf h3 ζ hζ).range :=
    eq_range_of_range_eq_bot hf h3 hζo hζ hN hA₁ hA₁SC hbot
  refine ⟨c⁻¹, ?_⟩
  calc A = (A.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom := by
        rw [Subgroup.map_map]
        have hcomp : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
            MonoidHom.id (TwE6C f) := by
          refine MonoidHom.ext fun x => ?_
          show MulAut.conj c⁻¹ (MulAut.conj c x) = x
          rw [MulAut.conj_apply, MulAut.conj_apply]
          group
        rw [hcomp, Subgroup.map_id]
    _ = (twE6ThreeFrameHom hf h3 ζ hζ).range.map (MulAut.conj c⁻¹).toMonoidHom := by
        rw [heq]

theorem twistedE6ThreeSCUnique_holds : TwistedE6ThreeSCUnique :=
  twistedE6ThreeSCUnique_of_scReference twistedE6ThreeSCReference_holds

end SC

end ExcFrames

end CFSG.StandardType
