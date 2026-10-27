module

public import CFSG.LocalAnalysis.StandardType.GGSporKLieZReduce
public import CFSG.LocalAnalysis.StandardType.GGLayerAbelianOdd
public import CFSG.LocalAnalysis.StandardType.GGExcAdjOddLayerCentreHolds
public import CFSG.LocalAnalysis.StandardType.GGOddLayerCentreHolds
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZTwD4Core
public import CFSG.Adapters.TauCetiExceptional.TwistedTransfer
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem l937z_ex_centralizer_zpowers {R : Type} [Group R] (x : R) :
    Subgroup.centralizer (Subgroup.zpowers x : Set R) = Subgroup.centralizer ({x} : Set R) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

private theorem l937z_ex_zpowers_commute {R : Type} [Group R] (x : R) :
    ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
  intro a ha b hb
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← hm, ← hn]
  exact (Commute.zpow_zpow_self x m n).eq

private theorem l937z_ex_autFix_zpowers_conj {C : Type} [Group C] (x : C) :
    LayerSixE.autFix (Subgroup.zpowers (MulAut.conj x)) =
      Subgroup.centralizer ({x} : Set C) := by
  ext y
  rw [LayerSixE.mem_autFix, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have hconj : MulAut.conj x y = y := h (MulAut.conj x) (Subgroup.mem_zpowers _)
    rw [MulAut.conj_apply] at hconj
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [hconj]
  · intro h α hα
    have hxy : x * y = y * x := h x (Set.mem_singleton x)
    have hconj : MulAut.conj x y = y := by
      rw [MulAut.conj_apply]
      calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [hxy]
        _ = y := by group
    have hstab : MulAut.conj x ∈ MulAction.stabilizer (MulAut C) y := by
      rw [MulAction.mem_stabilizer_iff]
      exact hconj
    exact MulAction.mem_stabilizer_iff.mp ((Subgroup.zpowers_le.mpr hstab) hα)

private theorem l937z_ex_sigmaEquiv_pow_eq_one {K : Type} [Field K] [Fintype K]
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2) {n : ℕ} (hcard : Fintype.card K = 2 ^ n) :
    (TauCetiBridge.Twisted.sigmaEquiv σ) ^ n = 1 := by
  have hfun : ∀ x, (TauCetiBridge.Twisted.sigmaEquiv σ) x = σ x := fun x => by
    change (TauCetiBridge.Twisted.sigmaEquiv σ).toRingHom x = σ x
    rw [TauCetiBridge.Twisted.sigmaEquiv_toRingHom]
  apply RingEquiv.ext
  intro c
  have hiter : ∀ m, ((TauCetiBridge.Twisted.sigmaEquiv σ) ^ m) c = c ^ (2 ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ']
      change (TauCetiBridge.Twisted.sigmaEquiv σ)
        (((TauCetiBridge.Twisted.sigmaEquiv σ) ^ m) c) = c ^ 2 ^ (m + 1)
      rw [ih, map_pow, hfun c, hσ c]
      rw [← pow_mul]
      congr 1
      rw [pow_succ']
  rw [hiter n]
  show c ^ (2 ^ n) = c
  rw [← hcard, FiniteField.pow_card]

theorem layerCentreSeven_adjointGroup
    (τ : Tag) {K : Type} [Field K] [Finite K] [CharP K 2] :
    LayerCentreSeven ↥(adjointGroup τ K) := by
  intro x hx z hz hzc hz2
  have hodd : Odd (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers, hx]
    decide
  refine ggExcAdjOddLayerCentre_holds τ K (Subgroup.zpowers x) hodd
    (l937z_ex_zpowers_commute x) z ?_ ?_ hz2
  · rw [l937z_ex_centralizer_zpowers x]
    exact hz
  · intro y hy
    rw [l937z_ex_centralizer_zpowers x] at hy
    exact hzc y hy

theorem lieZRow_of_untwistedChevalleyModel_F4_two
    {G : Type} [Group G] (hG : UntwistedChevalleyModel G .F4 2) : LieZRow G := by
  obtain ⟨K, hField, hFinite, hcard, ⟨e⟩⟩ := hG
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    apply charP_of_card_eq_prime_pow (p := 2) (f := 1)
    rw [pow_one, ← Nat.card_eq_fintype_card]
    exact hcard
  haveI : Finite (ModGL Tag.F4 K) := finite_modGL
  have hZ : Subgroup.center ↥(adjointGroup .F4 K) = ⊥ := center_adjointGroup_eq_bot
  have heq : AdjointQuotient .F4 K ≃* ↥(adjointGroup .F4 K) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hrowC : LieZRow ↥(adjointGroup .F4 K) :=
    lieZRow_of_layerCentreSeven (layerCentreSeven_adjointGroup .F4)
  have hrowQ : LieZRow (AdjointQuotient .F4 K) := lieZRow_of_mulEquiv heq.symm hrowC
  exact lieZRow_of_mulEquiv e.symm hrowQ

theorem layerCentreSeven_graphFixedE6
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) :
    LayerCentreSeven ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  intro x hx z hz hzc hz2
  have hdvd : orderOf (MulAut.conj x) ∣ 7 := by
    have h := orderOf_map_dvd (MulAut.conj) x
    rwa [hx] at h
  have hodd : Odd (Nat.card (Subgroup.zpowers (MulAut.conj x))) := by
    rw [Nat.card_zpowers]
    exact (show Odd 7 by decide).of_dvd_nat hdvd
  have hAI : Subgroup.zpowers (MulAut.conj x) ≤
      MulAut.conj.range ⊔ (RootCentExc.compatParamAut σ.toRingHom).range :=
    (Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨x, rfl⟩)).trans le_sup_left
  have hfix := l937z_ex_autFix_zpowers_conj x
  refine OddLayerCentre.twE6OddLayerCentre_of_ringEquiv K σ.toRingHom σ rfl hσ
    (Subgroup.zpowers (MulAut.conj x)) hodd hAI z ?_ ?_ hz2
  · rwa [hfix]
  · intro y hy
    rw [hfix] at hy
    exact hzc y hy

theorem lieZRow_of_twistedChevalleyModel_E6_two
    {G : Type} [Group G] (hG : TwistedChevalleyModel G .E6 2) : LieZRow G := by
  obtain ⟨K, hField, hFinite, hcard, σ, hσc, ⟨e⟩⟩ := hG
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    apply charP_of_card_eq_prime_pow (p := 2) (f := TwistTag.E6.order)
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hcard' : Fintype.card K = 2 ^ TwistTag.E6.order := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hσe : (TauCetiBridge.Twisted.sigmaEquiv σ) ^ TwistTag.E6.order = 1 :=
    l937z_ex_sigmaEquiv_pow_eq_one σ hσc hcard'
  have heq : DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
    TauCetiBridge.Twisted.nativeEquiv (t := TwistTag.E6) (p := 2) (f := 1)
      Nat.prime_two (le_refl 1) (by rw [pow_one]; exact hcard) (by rw [pow_one]; exact hσc)
  have hlayer : LayerCentreSeven ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
    layerCentreSeven_graphFixedE6 (TauCetiBridge.Twisted.sigmaEquiv σ) hσe
  have hrowD : LieZRow (DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ)) :=
    lieZRow_of_mulEquiv heq.symm (lieZRow_of_layerCentreSeven hlayer)
  exact lieZRow_of_mulEquiv e.symm hrowD

theorem lieZRow_of_twistedChevalleyModel_D4_two
    {G : Type} [Group G] (hG : TwistedChevalleyModel G .D4 2) : LieZRow G := by
  obtain ⟨K, hField, hFinite, hcard, σ, hσc, ⟨e⟩⟩ := hG
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    apply charP_of_card_eq_prime_pow (p := 2) (f := TwistTag.D4.order)
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hcard' : Fintype.card K = 2 ^ TwistTag.D4.order := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hσe : (TauCetiBridge.Twisted.sigmaEquiv σ) ^ TwistTag.D4.order = 1 :=
    l937z_ex_sigmaEquiv_pow_eq_one σ hσc hcard'
  have heq : DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
    TauCetiBridge.Twisted.nativeEquiv (t := TwistTag.D4) (p := 2) (f := 1)
      Nat.prime_two (le_refl 1) (by rw [pow_one]; exact hcard) (by rw [pow_one]; exact hσc)
  have hlayer : LayerCentreSeven ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
    layerCentreSeven_graphFixedD4 (TauCetiBridge.Twisted.sigmaEquiv σ) hσe
  have hrowD : LieZRow (DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ)) :=
    lieZRow_of_mulEquiv heq.symm (lieZRow_of_layerCentreSeven hlayer)
  exact lieZRow_of_mulEquiv e.symm hrowD

end CFSG.StandardType.SporadicShape
