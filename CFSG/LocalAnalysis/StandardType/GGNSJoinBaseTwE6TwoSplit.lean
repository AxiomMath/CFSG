module

public import CFSG.Mathlib.GroupTheory.FixedInnerLift
public import CFSG.LocalAnalysis.StandardType.GGLtBstarOfInner
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadModel
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwE6TwoFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB


theorem GGConfig.bstar_eq_sup_of_e6Three_inner_model {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (Φ : (ggGamma L hN).range →* Multiplicative (Fin 6 → ZMod 3))
    (T : Subgroup L) (w : Fin 6 → L)
    (hM : GGE6ThreeData (Subgroup.center L) (ggGamma L hN).range Φ T w)
    (hH : ∀ v, Multiplicative.ofAdd v ∈ Φ.range ↔ v ∈ NoOffRest.hypE6) :
    Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L) := by
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  refine Subgroup.eq_sup_zpowers_inf_of_fixed_inner_lifts (fun a ha b hb => hBs.comm ha hb)
    hBs.2 hcfg.2.1.2.2.2
    hcfg.bstar_inf_centralizer_L ?_
  intro b hb
  let b' : Bs := ⟨b, hb⟩
  let aB : (ggGamma L hN).range := ⟨ggGamma L hN b', ⟨b', rfl⟩⟩
  let v := Multiplicative.toAdd (Φ aB)
  have hv : v ∈ NoOffRest.hypE6 := (hH v).1 ⟨aB, by simp [v]⟩
  obtain ⟨t, ht, ht3, a, hta, hav⟩ := hM.torus v hv
  have ha : a = aB := hM.injective (Multiplicative.ext hav)
  have htB : MulAut.conj t = ggGamma L hN b' := by simpa [ha, aB] using hta
  refine ⟨(t : G), t.2, congrArg (fun y : L => (y : G)) ht3, ?_, ?_⟩
  · intro c hc
    let c' : Bs := ⟨c, hc⟩
    have hfix := congrArg (fun y : L => (y : G))
      (hM.fixed (ggGamma L hN c') ⟨c', rfl⟩ t ht)
    rw [ggGamma_coe] at hfix
    change c * (t : G) * c⁻¹ = (t : G) at hfix
    have hmul := congrArg (fun y : G => y * c) hfix
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
  · intro l hl
    have he := congrArg (fun α : MulAut L => ((α ⟨l, hl⟩ : L) : G)) htB
    simpa only [MulAut.conj_apply, ggGamma_coe, Subgroup.coe_mul, Subgroup.coe_inv] using he.symm

theorem GGConfig.lt_bstar_of_twE6Two_inner_model {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) 3 Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (Φ : (ggGamma L hN).range →* Multiplicative (Fin 6 → ZMod 3))
    (T : Subgroup L) (w : Fin 6 → L)
    (hM : GGE6ThreeData (Subgroup.center L) (ggGamma L hN).range Φ T w)
    (hH : ∀ v, Multiplicative.ofAdd v ∈ Φ.range ↔ v ∈ NoOffRest.hypE6) :
    B < Bs :=
  GGConfig.lt_bstar_of_bstar_eq_sup hcfg (GGConfig.bstar_eq_sup_of_e6Three_inner_model hcfg hN Φ T w hM hH)
    fun U hUL hU2 hBsU =>
      le_centralizer_of_isPGroup_two_of_twE6Two_marking hcfg hmark hU2 hUL hBsU


theorem GGConfig.lt_bstar_or_card_eq_three_pow_seven_of_twE6Two
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs L) :
    B < Bs ∨ Nat.card Bs = 3 ^ 7 := by
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  obtain ⟨lab, -, -, -, -, -, -, -, ⟨⟨-, hdvd⟩, hn⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  have hp3 : p = 3 := by
    rw [hn] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
  subst hp3
  have hBad : GGInnerDiagOnLabel GGTwE6BadLabel 3 Bs L :=
    hmark.mono_label fun lab h => ⟨h.1.1, rfl, h.1.2⟩
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.marking_elim_const
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2.1) hmark)
  obtain ⟨Φ, T, w, hM⟩ := ggTwE6Bad_model_of_config hcfg hBad hN
  rcases hM.range with hFull | hHyp
  · right
    have hcard : Nat.card (ggGamma L hN).range = Nat.card Φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hM.injective).toEquiv
    have hA : Nat.card (ggGamma L hN).range = 3 ^ 6 := by
      rw [hcard, hFull, Subgroup.card_top]
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
    have hmul := card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hN
    calc Nat.card Bs = Nat.card (ggGamma L hN).range * 3 := hmul.symm
      _ = 3 ^ 7 := by rw [hA]; norm_num
  · exact Or.inl (GGConfig.lt_bstar_of_twE6Two_inner_model hcfg hmark hN Φ T w hM hHyp)

end CFSG.StandardType

end
