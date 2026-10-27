module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreConj
public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreClause
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotNeighbourStandard
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType.TwE6CorootCore

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction
  CFSG.SeitzReduction.TwistedE6Pilot CFSG.RankThree.Chevalley


variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem exists_mul_eq_of_mem_twistedE6InndiagGL (σ : K ≃+* K) {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ twistedE6InndiagGL K σ) :
    ∃ c ∈ twistedE6RootGroup K σ, ∃ d ∈ twistedE6DiagGL K σ, x = c * d := by
  have hN : twistedE6DiagGL K σ ≤ Subgroup.normalizer
      (twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K)) :=
    (le_sup_right : twistedE6DiagGL K σ ≤ twistedE6InndiagGL K σ).trans
      (twistedE6InndiagGL_le_normalizer K σ)
  have key : ∀ y ∈ Subgroup.closure ((twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K)) ∪
      (twistedE6DiagGL K σ : Set (ModGL TwistTag.E6.tag K))),
      ∃ c ∈ twistedE6RootGroup K σ, ∃ d ∈ twistedE6DiagGL K σ, y = c * d := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with hz | hz
      · exact ⟨z, hz, 1, one_mem _, (mul_one z).symm⟩
      · exact ⟨1, one_mem _, z, hz, (one_mul z).symm⟩
    | one => exact ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
    | mul a b _ _ ha hb =>
      obtain ⟨c, hc, d, hd, rfl⟩ := ha
      obtain ⟨c', hc', d', hd', rfl⟩ := hb
      refine ⟨c * (d * c' * d⁻¹), mul_mem hc ?_, d * d', mul_mem hd hd', ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hN hd) c').1 hc'
      · group
    | inv a _ ha =>
      obtain ⟨c, hc, d, hd, rfl⟩ := ha
      refine ⟨d⁻¹ * c⁻¹ * d, ?_, d⁻¹, inv_mem hd, ?_⟩
      · have h' := (Subgroup.mem_normalizer_iff.1 (hN (inv_mem hd)) c⁻¹).1 (inv_mem hc)
        rwa [inv_inv] at h'
      · group
  exact key x (mem_twistedE6InndiagGL_iff.1 hx)

theorem exists_core_thetaSL2_pow (σ : K ≃+* K) (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (hk : Nat.card k = 2 ^ f) {A : SL2 k}
    (hA : orderOf A = Nat.card k + 1) {m : ℕ} (hm : A ^ m ≠ 1) :
    ∃ X D : Subgroup ↥(twistedE6RootGroup K σ),
      (centralizer ({(thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m)} :
          Set (ModGL TwistTag.E6.tag K))).subgroupOf (twistedE6RootGroup K σ) = X ⊔ D ∧
        IsCyclic X ∧ Odd (Nat.card X) ∧ X ≤ centralizer (D : Set _) ∧ CFSG.IsQuasisimple D ∧
        center D = ⊥ ∧ 7 ∣ Nat.card D ∧ (2 ^ f) ^ 15 ∣ Nat.card D ∧
        ∀ s ∈ twistedE6InndiagGL K σ,
          s * (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m) =
            (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m) * s →
          (∀ d ∈ D, s * (d : ModGL TwistTag.E6.tag K) = (d : ModGL TwistTag.E6.tag K) * s) →
            s ∈ X.map (twistedE6RootGroup K σ).subtype := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ f := hσ
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have h3 : 3 ≤ orderOf (A ^ m) := by
    have hd : orderOf (A ^ m) ∣ 2 ^ f + 1 := by
      rw [← hk, ← hA]
      exact orderOf_pow_dvd m
    have hodd : Odd (orderOf (A ^ m)) :=
      Odd.of_dvd_nat (Even.add_one ((Nat.even_pow' (by omega)).2 even_two)) hd
    have h1 : orderOf (A ^ m) ≠ 1 := fun h => hm (orderOf_eq_one_iff.1 h)
    have h0 : 0 < orderOf (A ^ m) := Nat.pos_of_dvd_of_pos hd (by positivity)
    obtain ⟨j, hj⟩ := hodd
    omega
  have hcen := centralizer_pow_inf_eq hf hk hK hσ' hA h3
  set ρ := (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) with hρdef
  have hρinj : Function.Injective ρ := injective_thetaSL2_comp_map hK2 (algebraMap k K)
  have hXJ : zpowers (ρ A) ≤ thetaRankOneGroup (algebraMap k K) := by
    rw [zpowers_le, thetaRankOneGroup_eq_range hK2]
    exact MonoidHom.mem_range.2 ⟨A, rfl⟩
  have hXC : zpowers (ρ A) ≤ twistedE6RootGroup K σ :=
    hXJ.trans (thetaRankOneGroup_le_C0 hf hk hK hσ')
  have hDC : su6Levi σ.toRingHom ≤ twistedE6RootGroup K σ :=
    su6Levi_le_graphFixedRootGroup σ.toRingHom
  have hcard : Nat.card ↥((su6Levi σ.toRingHom).subgroupOf (twistedE6RootGroup K σ)) =
      CFSG.Open.ordTwistedA 5 (2 ^ f) :=
    F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide)
      (lieModel_su6Levi_subgroupOf hf hk hK hσ')
  refine ⟨(zpowers (ρ A)).subgroupOf (twistedE6RootGroup K σ),
    (su6Levi σ.toRingHom).subgroupOf (twistedE6RootGroup K σ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← inf_subgroupOf_right, hcen, subgroupOf_sup hXC hDC]
  · have := Subgroup.isCyclic_zpowers (ρ A)
    exact isCyclic_of_surjective (subgroupOfEquivOfLe hXC).symm (MulEquiv.surjective _)
  · rw [Nat.card_congr (subgroupOfEquivOfLe hXC).toEquiv, Nat.card_zpowers,
      orderOf_injective ρ hρinj, hA, hk]
    exact Even.add_one ((Nat.even_pow' (by omega)).2 even_two)
  · exact CFSG.SeitzReduction.TwistedE6Pilot.subgroupOf_le_centralizer_subgroupOf
      (hXJ.trans (le_centralizer_iff.1 (su6Levi_facts hf hk hK hσ').1))
  · exact isQuasisimple_su6Levi_subgroupOf hf hk hK hσ'
  · have := isSimpleGroup_su6Levi hf hk hK hσ'
    have hnc : ∃ a b : su6Levi σ.toRingHom, a * b ≠ b * a := by
      by_contra hc
      push Not at hc
      have := isPerfect_su6Levi hf hk hK hσ'
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b => hc a b⟩⟩
    rw [← Subgroup.map_center_eq (subgroupOfEquivOfLe hDC).symm,
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).2, Subgroup.map_bot]
  · rw [hcard]
    exact (seven_and_pow_dvd_ordTwistedA_five hf).1
  · rw [hcard]
    exact (seven_and_pow_dvd_ordTwistedA_five hf).2
  · intro s hs hst hsD
    obtain ⟨c, hc, _, ⟨u, rfl⟩, rfl⟩ := exists_mul_eq_of_mem_twistedE6InndiagGL σ hs
    have hc' := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hc)
    have hz := mem_zpowers_of_commute_su6Levi hf hk hK hσ' hA hm hc'.1
      (compatDiag TwistTag.E6 σ.toRingHom u) rfl
      (by rw [map_mul, hc'.2, twistHom_rootDiagUnit fun i => compatDiag_perm u i]) hst
      (fun d hd => hsD ⟨d, hDC hd⟩ (Subgroup.mem_subgroupOf.2 hd))
    exact Subgroup.mem_map.2 ⟨⟨_, hXC hz⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩

theorem twE6CorootCore_of_fuse
    (hFuse : ∀ {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
      (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ f) {k : Type} [Field k]
      [Algebra k K] (hk : Nat.card k = 2 ^ f) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (hFr : ∀ c, Fr c = c ^ 2 ^ f) (v : WeylGroup TwistTag.E6.tag)
      (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
      (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
      (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
      (t : ModGL TwistTag.E6.tag K) (_ht : t ∈ twistedE6InndiagGL K σ)
      (γ : Fin TwistTag.E6.tag.rank → ℤ) (hγ : IsRoot TwistTag.E6.tag γ) (p : ℕ)
      (_hp : p.Prime) (hpq : p ∣ 2 ^ f + 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (hζ1 : ζ ≠ 1)
      (hcor : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g0 =
        rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ)),
      ∃ c ∈ twistedE6InndiagGL K σ, ∃ A : SL2 k, orderOf A = Nat.card k + 1 ∧ ∃ m : ℕ,
        A ^ m ≠ 1 ∧ c * t * c⁻¹ =
          (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m)) :
    TwE6RootAs.TwE6CorootCore := by
  intro K _ _ σ q hK hσ h2 p hp hpq Fr hFr v hv g0 hg0C hg0 t ht γ hγ ζ hζ hζ1 hcor
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := ringChar.of_eq h2
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hdvd : q ∣ 2 ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, h0] at h1
      norm_num at h1
    · exact h0
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ f := hσ
  have hσ2 : σ ^ 2 = 1 := by
    ext c
    rw [pow_two, RingAut.mul_apply, RingAut.one_apply]
    exact TwistedE6Pilot.apply_apply_eq hK hσ' c
  have hσ1 : σ ≠ 1 := fun h => by
    obtain ⟨c, hc⟩ := TwistedE6Pilot.exists_apply_ne hf hK hσ'
    exact hc (by rw [show σ.toRingHom c = σ c from rfl, h, RingAut.one_apply])
  have hk : Nat.card (fixSubfield σ) = 2 ^ f := by
    have h := (SteinbergBT.card_fixSubfield Nat.prime_two (by omega : 1 ≤ 2 * f)
      (by rw [hK, ← pow_mul, mul_comm]) σ).2
    rwa [orderOf_eq_prime hσ2 hσ1, Nat.mul_div_cancel_left f two_pos] at h
  obtain ⟨c, hc, A, hA, m, hm, hct⟩ :=
    hFuse σ hf hK hσ hk Fr hFr v hv g0 hg0C hg0 t ht γ hγ p hp hpq ζ hζ hζ1 hcor
  refine exists_core_of_conj hc (twistedE6InndiagConj K σ ⟨c, hc⟩⁻¹) (fun x => ?_) ?_
  · rw [twistedE6InndiagConj_apply, Subgroup.coe_inv, inv_inv]
  · rw [hct]
    exact exists_core_thetaSL2_pow σ hf hK hσ hk hA hm

end CFSG.StandardType.TwE6CorootCore

end
