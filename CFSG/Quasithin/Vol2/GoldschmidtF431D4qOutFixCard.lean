module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixAct
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixField
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Cell

public section

namespace CFSG.Quasithin.H13.F431.D4q.Out

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.ComponentInitial

set_option linter.unusedSectionVars false

section Ug

variable {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K)

@[expose] noncomputable def Ug : Subgroup (Cm σ) :=
  Ust σ ⊓ (fieldActor σ δ).toMonoidHom.eqLocus (MonoidHom.id _)

variable [CharP K 2] {σ δ}

theorem d4coord_mem (hσ3 : σ.toRingHom ^ 3 = 1) {a b c d e f : K} (hb : σ b = b) (he : σ e = e)
    (hf : σ f = f) :
    d4x₁ K σ a * d4v K σ b c d e f ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
  obtain ⟨-, -, -, -, -, -, hB, -⟩ := even_triality_positive_orbit_parametrization K σ hσ3
  have h := hB.mapsTo (Set.mem_univ ((a, ⟨b, (mem_trialityFixedField).2 hb⟩, c, d,
    ⟨e, (mem_trialityFixedField).2 he⟩, ⟨f, (mem_trialityFixedField).2 hf⟩) :
      K × trialityFixedField K σ.toRingHom × K × K × trialityFixedField K σ.toRingHom ×
        trialityFixedField K σ.toRingHom))
  convert h using 1
  simp only [Subgroup.coe_mul, d4v, mul_assoc]
  rfl

@[expose] noncomputable def coordElt (hσ3 : σ.toRingHom ^ 3 = 1) {a b c d e f : K} (hb : σ b = b)
    (he : σ e = e) (hf : σ f = f) : Cm σ :=
  ⟨d4x₁ K σ a * d4v K σ b c d e f, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    (d4coord_mem hσ3 (a := a) (c := c) (d := d) hb he hf)⟩

theorem coe_coordElt (hσ3 : σ.toRingHom ^ 3 = 1) {a b c d e f : K} (hb : σ b = b)
    (he : σ e = e) (hf : σ f = f) :
    ((coordElt hσ3 (a := a) (c := c) (d := d) hb he hf : Cm σ) : ModGL TwistTag.D4.tag K) =
      d4x₁ K σ a * d4v K σ b c d e f := by
  unfold coordElt
  rfl

theorem coordElt_mem_Ust (hσ3 : σ.toRingHom ^ 3 = 1) {a b c d e f : K} (hb : σ b = b)
    (he : σ e = e) (hf : σ f = f) : coordElt hσ3 (a := a) (c := c) (d := d) hb he hf ∈ Ust σ :=
  Subgroup.mem_subgroupOf.2 (d4coord_mem hσ3 hb he hf)

end Ug

section Card

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ δ : K ≃+* K}

abbrev CoordTuples (σ δ : K ≃+* K) : Type :=
  {a : K // δ a = a} × {b : K // σ b = b ∧ δ b = b} × {c : K // δ c = c} × {d : K // δ d = d} ×
    {e : K // σ e = e ∧ δ e = e} × {f : K // σ f = f ∧ δ f = f}

theorem card_Ug_eq (hσ3 : σ.toRingHom ^ 3 = 1) :
    Nat.card (Ug σ δ) = Nat.card {a : K // δ a = a} ^ 3 *
      Nat.card {b : K // σ b = b ∧ δ b = b} ^ 3 := by
  let Φ : CoordTuples σ δ → Ug σ δ := fun p =>
    ⟨coordElt hσ3 (a := p.1.1) (b := p.2.1.1) (c := p.2.2.1.1) (d := p.2.2.2.1.1)
        (e := p.2.2.2.2.1.1) (f := p.2.2.2.2.2.1) p.2.1.2.1 p.2.2.2.2.1.2.1 p.2.2.2.2.2.2.1,
      coordElt_mem_Ust hσ3 p.2.1.2.1 p.2.2.2.2.1.2.1 p.2.2.2.2.2.2.1,
      (fieldActor_fix_iff σ δ _ (coe_coordElt hσ3 p.2.1.2.1 p.2.2.2.2.1.2.1
        p.2.2.2.2.2.2.1)).2 ⟨p.1.2, p.2.1.2.2, p.2.2.1.2, p.2.2.2.1.2, p.2.2.2.2.1.2.2,
          p.2.2.2.2.2.2.2⟩⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨e, he⟩, ⟨f, hf⟩⟩
        ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨c', hc'⟩, ⟨d', hd'⟩, ⟨e', he'⟩, ⟨f', hf'⟩⟩ h
      have h1 := congrArg (fun x : Ug σ δ => ((x.1 : Cm σ) : ModGL TwistTag.D4.tag K)) h
      simp only [Φ, coe_coordElt] at h1
      obtain ⟨r1, r2, r3, r4, r5, r6⟩ := d4coord_injective σ h1
      subst r1 r2 r3 r4 r5 r6
      rfl
    · rintro ⟨u, hu⟩
      obtain ⟨hu1, hu2⟩ := hu
      obtain ⟨a, b, c, d, e, f, hb, he, hf, hu'⟩ :=
        exists_d4coord σ hσ3 (Subgroup.mem_subgroupOf.1 hu1)
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (fieldActor_fix_iff σ δ u hu').1 hu2
      refine ⟨(⟨a, h1⟩, ⟨b, hb, h2⟩, ⟨c, h3⟩, ⟨d, h4⟩, ⟨e, he, h5⟩, ⟨f, hf, h6⟩), ?_⟩
      refine Subtype.ext (Subtype.ext ?_)
      exact (coe_coordElt hσ3 hb he hf).trans hu'.symm
  rw [← Nat.card_eq_of_bijective Φ hΦ]
  simp only [CoordTuples, Nat.card_prod]
  ring

end Card

section Std

variable {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K) {e : ℕ} (he : 1 ≤ e)
  (hK : Nat.card K = (2 ^ (2 * e)) ^ 3) (hσ : ∀ c, σ.toRingHom c = c ^ 2 ^ (2 * e))
  (hδ : ∀ c, δ c = c ^ 2 ^ (3 * e))

include he hK hσ hδ in
theorem card_Ug : Nat.card (Ug σ δ) = (2 ^ (2 * e)) ^ 6 := by
  have hK6 : Nat.card K = 2 ^ (6 * e) := by
    rw [hK, ← pow_mul]
    ring_nf
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK6
  have hσ3 : σ.toRingHom ^ 3 = 1 :=
    toRingHom_pow_three_d4 σ (sigma_three_of_card (σ := σ.toRingHom) hK hσ)
  rw [card_Ug_eq hσ3, card_fix_delta he hK6 hδ, card_fix_both he hK6 (fun c => hσ c) hδ,
    ← pow_mul, ← pow_mul, ← pow_mul]
  ring_nf

end Std

end CFSG.Quasithin.H13.F431.D4q.Out
