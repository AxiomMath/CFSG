module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2Neighbour

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift)

@[expose] def TwistedE6TwoDiagonalRigidity : Prop :=
  ∀ (k K : Type) [Field k] [Field K] [Algebra k K], Nat.card k = 2 ^ 1 →
    Nat.card K = (2 ^ 1) ^ 2 → ∀ σ : K →+* K, (∀ c, σ c = c ^ 2 ^ 1) →
    ∀ A : Subgroup (ModGL TwistTag.E6.tag K), A ≤ thetaRankOneGroup (algebraMap k K) →
      Nat.card A = 2 ^ 1 + 1 → IsCyclic A →
      ∀ β : MulAut (graphFixedRootGroup TwistTag.E6 K σ), Odd (orderOf β) →
        (∀ x ∈ A.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), β x = x) →
        (∀ x ∈ (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), β x = x) →
        β ∈ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ →*
          MulAut (graphFixedRootGroup TwistTag.E6 K σ)).range

section Rigidity

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem exists_eq_conj_of_fix_nonsplit_two (hR : TwistedE6TwoDiagonalRigidity)
    (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAJ : A ≤ thetaRankOneGroup (algebraMap k K)) (hA : Nat.card A = 2 ^ 1 + 1)
    (hcyc : IsCyclic A) (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hβX : ∀ x ∈ A.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), β x = x)
    (hβD : ∀ x ∈ (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), β x = x) :
    ∃ w ∈ A.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), β = MulAut.conj w := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (MulAut (graphFixedRootGroup TwistTag.E6 K σ)) := MulEquiv.finite_left
  have hpow : ∀ j : ℕ, (∀ x ∈ A.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ),
      (β ^ j) x = x) ∧
      ∀ x ∈ (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), (β ^ j) x = x := by
    intro j
    induction j with
    | zero => exact ⟨fun x _ => rfl, fun x _ => rfl⟩
    | succ j ih =>
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [pow_succ, MulAut.mul_apply, hβX x hx, ih.1 x hx]
      · rw [pow_succ, MulAut.mul_apply, hβD x hx, ih.2 x hx]
  obtain ⟨a, m, hm, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos β).ne'
  have hβm : β ^ m = 1 := by
    refine eq_one_of_fix_nonsplit_two hk hK hσ hAJ hA hcyc (β ^ m) (hpow m).1 (hpow m).2 a ?_
    rw [← pow_mul, mul_comm, ← hN, pow_orderOf_eq_one]
  have hodd : Odd (orderOf β) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hβm)
  obtain ⟨g, rfl⟩ := hR k K hk hK σ hσ A hAJ hA hcyc β hodd hβX hβD
  exact ⟨g, mem_of_conj_fix_nonsplit le_rfl hk hK hσ hAJ hA hcyc
    (fun x hx => by rw [← MulAut.conj_apply]; exact hβX x hx)
    (fun y hy => by rw [← MulAut.conj_apply]; exact hβD y hy), rfl⟩

end Rigidity

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {k K : Type} [Field k] [Field K]
  [Algebra k K]

theorem forall_odd_mem_2E6_nonsplit_two (hR : TwistedE6TwoDiagonalRigidity)
    (hset : SeitzSetting G L) (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAJ : A ≤ thetaRankOneGroup (algebraMap k K))
    (hA : Nat.card A = 2 ^ 1 + 1) (hcyc : IsCyclic A) {X : Subgroup G}
    (hX : X = ((A.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X := by
  have hf : 1 ≤ 1 := le_rfl
  have hLt := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  have hK' := inf_centralizer_eq_zpowers_twistedE6 hset hf hK hσ e htC ht
  have hAC := (centralizer_nonsplit_twistedE6 hf hk hK hσ hAJ hA hcyc).2.2.2
  have hXo : Odd (Nat.card X) := by
    rw [hX, card_map_symm_subgroupOf hAC, hA]
    decide
  intro c hc hco
  subst hX hDe
  exact mem_of_forall_fix_fix_eq_conj htC ht hLt hK' hXo
    (forall_eq_conj_map_symm e (exists_eq_conj_of_fix_nonsplit_two hR hk hK hσ hAJ hA hcyc))
    hc.1.1 hc.1.2 hc.2 hco

theorem hasBLift_sup_conj_2E6_nonsplit_two (hR : TwistedE6TwoDiagonalRigidity)
    (hset : SeitzSetting G L) (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAJ : A ≤ thetaRankOneGroup (algebraMap k K))
    (hA : Nat.card A = 2 ^ 1 + 1) (hcyc : IsCyclic A) {X : Subgroup G}
    (hX : X = ((A.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kb : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKb : ⁅Kb, Kb⁆ = Kb)
    (hcomm : ⁅Kb, Kb.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥) :
    HasBLift (Kb ⊔ Kb.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom) ∧
      HasBLift Kb := by
  obtain ⟨hD, hDq⟩ := neighbour_layer_2E6_nonsplit_two hk hK hσ e hAJ hA hcyc hX hDe
  exact LinearPilot.hasBLift_sup_conj_of_forall_odd_mem htC ht
    (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht)
    htX hD hDq (forall_odd_mem_2E6_nonsplit_two hR hset hk hK hσ e htC ht hAJ hA hcyc hX hDe)
    hKb hcomm

end Setting

end CFSG.SeitzReduction.TwistedE6Pilot
