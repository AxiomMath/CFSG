module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourCore
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphPiecesLift
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift)

section Generic

variable {G : Type} [Group G] [Finite G]

theorem exists_surjective_neighbourCore_of_bLift {X D : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htX : t ∈ centralizer (X : Set G)) (hDt : D ≤ centralizer ({t} : Set G))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hout : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hOut : Group.IsSolvable (Outer Kc)) (hB : HasBLift Kc) :
    perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) =
        Kc ∧
      ∃ q : centralizerPerfectCore X →* Kc, Function.Surjective q ∧
        q.ker ≤ center (centralizerPerfectCore X) ∧ Odd (Nat.card q.ker) ∧
        ∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
          oddCore (centralizer (X : Set G))) = QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
            ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩ := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hss : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ *
      QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 := Subtype.ext htt
    rw [this, map_one]
  have hsC : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
      centralizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    intro hc
    refine hout ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, F4Pilot.coe_normalizerMonoidHom_mk_apply Kc hsN,
      ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
  have hs1 : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ≠ 1 :=
    fun h => hsC (h ▸ one_mem _)
  have hs2 : orderOf (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have hsD : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      centralizer (((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hKc hDK hs2 hsD hsN hsC hsyl hOut
  obtain ⟨q, hqs, hqker, hqapp⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  have hle : centralizerPerfectCore X ≤ centralizer (X : Set G) :=
    F4Pilot.centralizerPerfectCore_le_centralizer X
  have hmemO : ∀ y : q.ker, (Subgroup.inclusion hle) (y : centralizerPerfectCore X) ∈
      oddCore (centralizer (X : Set G)) := by
    intro y
    have h1 := hqapp (y : centralizerPerfectCore X)
    rw [MonoidHom.mem_ker.1 y.2] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1.symm
  set φ : q.ker →* oddCore (centralizer (X : Set G)) :=
    ((Subgroup.inclusion hle).comp q.ker.subtype).codRestrict (oddCore (centralizer (X : Set G)))
      hmemO with hφ
  have hφinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg
      (fun z : oddCore (centralizer (X : Set G)) => ((z : centralizer (X : Set G)) : G)) hab))
  have hkodd : Odd (Nat.card q.ker) :=
    Odd.of_dvd_nat CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
      (Subgroup.card_dvd_of_injective φ hφinj)
  exact ⟨hcore, q, hqs, hqker, hkodd, hqapp⟩

end Generic

theorem commutator_eq_self_of_isQuasisimple' {Y : Type*} [Group Y] {D : Subgroup Y}
    (h : CFSG.Open.IsQuasisimple D) : ⁅D, D⁆ = D := by
  have h1 : commutator D = ⊤ := h.1
  have hD : (⊤ : Subgroup D).map D.subtype = D := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  calc ⁅D, D⁆ = ⁅(⊤ : Subgroup D).map D.subtype, (⊤ : Subgroup D).map D.subtype⁆ := by rw [hD]
    _ = (commutator D).map D.subtype := by rw [commutator_def, map_commutator]
    _ = D := by rw [h1, hD]

section Fused

variable {G : Type} [Group G]

theorem mem_conjugate_of_conj_eq_mul {L : Subgroup G} {t z g : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (hzL : z ∈ L)
    (hg : g⁻¹ * t * g = t * z)
    (hw : ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹)
    (hC0 : g * t * g⁻¹ ∉ L) : z ∈ CFSG.conjugate L g := by
  have hmem : ∀ w : G, w ∈ CFSG.conjugate L g ↔ g * w * g⁻¹ ∈ L := by
    intro w
    constructor
    · rintro ⟨l, hl, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hl
    · intro hw
      exact ⟨g * w * g⁻¹, hw, by simp [mul_assoc]⟩
  obtain ⟨w', hw'L, hw'⟩ := hw
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htz : t * z = z * t := (mem_centralizer_iff.1 htC z hzL).symm
  have htzC : ∀ l ∈ CFSG.conjugate L g, (t * z) * l = l * (t * z) := by
    intro l hl
    have h1 := mem_centralizer_iff.1 htC _ ((hmem l).1 hl)
    calc (t * z) * l = g⁻¹ * (t * (g * l * g⁻¹)) * g := by rw [← hg]; group
      _ = g⁻¹ * ((g * l * g⁻¹) * t) * g := by rw [h1]
      _ = l * (g⁻¹ * t * g) := by group
      _ = l * (t * z) := by rw [hg]
  set c := w'⁻¹ * z with hc
  have hcL : ∀ l ∈ CFSG.conjugate L g, c * l = l * c := by
    intro l hl
    have h1 := hw' l hl
    have h2 : z * l * z⁻¹ = t * l * t⁻¹ := by
      have h3 := htzC l hl
      calc z * l * z⁻¹ = t⁻¹ * ((t * z) * l) * z⁻¹ := by group
        _ = t⁻¹ * (l * (t * z)) * z⁻¹ := by rw [h3]
        _ = t * l * t⁻¹ := by rw [htinv]; group
    have h4 : z * l * z⁻¹ = w' * l * w'⁻¹ := h2.trans h1
    calc c * l = w'⁻¹ * (z * l * z⁻¹) * z := by rw [hc]; group
      _ = w'⁻¹ * (w' * l * w'⁻¹) * z := by rw [h4]
      _ = l * c := by rw [hc]; group
  have hcT : c * (t * z) = (t * z) * c := by
    have h1 : w' * (t * z) = (t * z) * w' := (htzC w' hw'L).symm
    have h2 : w'⁻¹ * (t * z) = (t * z) * w'⁻¹ := by
      calc w'⁻¹ * (t * z) = w'⁻¹ * ((t * z) * w') * w'⁻¹ := by group
        _ = w'⁻¹ * (w' * (t * z)) * w'⁻¹ := by rw [h1]
        _ = (t * z) * w'⁻¹ := by group
    have h3 : z * (t * z) = (t * z) * z := by rw [← mul_assoc, ← htz, mul_assoc]
    calc c * (t * z) = w'⁻¹ * (z * (t * z)) := by rw [hc, mul_assoc]
      _ = w'⁻¹ * ((t * z) * z) := by rw [h3]
      _ = (w'⁻¹ * (t * z)) * z := by group
      _ = ((t * z) * w'⁻¹) * z := by rw [h2]
      _ = (t * z) * c := by rw [hc]; group
  have hgc : g * c * g⁻¹ ∈ zpowers t := by
    rw [← hKt]
    refine ⟨mem_centralizer_iff.2 fun l hl => ?_, mem_centralizer_singleton_iff.2 ?_⟩
    · have hl' : g⁻¹ * l * g ∈ CFSG.conjugate L g := (hmem _).2 (by group; exact hl)
      have h1 := hcL _ hl'
      calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * l := by group
    · have ht' : g * (t * z) * g⁻¹ = t := by rw [← hg]; group
      calc g * c * g⁻¹ * t = g * c * g⁻¹ * (g * (t * z) * g⁻¹) := by rw [ht']
        _ = g * (c * (t * z)) * g⁻¹ := by group
        _ = g * ((t * z) * c) * g⁻¹ := by rw [hcT]
        _ = (g * (t * z) * g⁻¹) * (g * c * g⁻¹) := by group
        _ = t * (g * c * g⁻¹) := by rw [ht']
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hgc
  have hn' : t ^ (n % 2) = g * c * g⁻¹ := by
    have h2 := zpow_mod_orderOf t n
    rw [ht, Nat.cast_ofNat] at h2
    rw [h2, hn]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · rw [h0, zpow_zero] at hn'
    have hc1 : c = 1 := by
      have : c = g⁻¹ * (g * c * g⁻¹) * g := by group
      rw [this, ← hn']
      group
    have hzw : z = w' := by
      rw [hc] at hc1
      calc z = w' * (w'⁻¹ * z) := by group
        _ = w' := by rw [hc1, mul_one]
    rw [hzw]
    exact hw'L
  · rw [h1, zpow_one] at hn'
    exfalso
    apply hC0
    have hct : c = t * z := by
      calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
        _ = g⁻¹ * t * g := by rw [← hn']
        _ = t * z := hg
    have hw't : w' = t := by
      have h1 : w'⁻¹ * z = t * z := hct
      have h2 : w'⁻¹ = t := mul_right_cancel h1
      calc w' = (w'⁻¹)⁻¹ := (inv_inv w').symm
        _ = t⁻¹ := by rw [h2]
        _ = t := htinv
    rw [← hw't]
    exact (hmem w').1 hw'L

end Fused

section LiftX


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem exists_surjective_neighbourCore_2E6_X (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = (((E6GraphLevi.thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hov : UnitaryPilot.SUmOvergroup Kc (Kc.normalizerMonoidHom ⟨_, hsN⟩) 6 f) :
    perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) =
        Kc ∧ HasBLift Kc ∧
      ∃ q : centralizerPerfectCore X →* Kc, Function.Surjective q ∧
        q.ker ≤ center (centralizerPerfectCore X) ∧ Odd (Nat.card q.ker) ∧
        ∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
          oddCore (centralizer (X : Set G))) = QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
            ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩ := by
  obtain ⟨hD, hDq⟩ := neighbour_layer_2E6_X hf2 hk hK hσ e hX hDe
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_2E6_X hset hf2 hk hK hσ e htC ht hX htX hDe
  have hlist : LieModel (Kc ⧸ center Kc) .PSL 6 2 (2 * f) :=
    hov.2.2.resolve_right (UnitaryPilot.not_sumSmall_of_ne (six_ne_four_one f))
  have hOut := F4Pilot.isSolvable_outer_of_lieModel_PSL_quotient hKc.1.1 (by norm_num) hlist
  exact OmegaPilot.exists_surjective_neighbourCore_of_field htC ht
    (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht)
    htX hD hDq (forall_odd_mem_2E6_X hset hf2 hk hK hσ e htC ht hX hDe) hsyl hKc hDK hsN hov.1
    hOut

theorem hasBLift_neighbour_2E6_X (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = (((E6GraphLevi.thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (halt : UnitaryPilot.SUmNeighbourAlternative
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc 6 f) :
    HasBLift Kc ∧ HasBLift (Kc ⊔ Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom) := by
  obtain ⟨-, ⟨hKt, -, -, hsN, hout, -, -⟩ | ⟨-, hcomm, -, -⟩⟩ := halt
  · have hsC : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
        centralizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
      intro hc
      refine hout ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
      rw [map_one, MulAut.one_apply, F4Pilot.coe_normalizerMonoidHom_mk_apply Kc hsN,
        ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
    have hB := hasBLift_2E6_X hset hf2 hk hK hσ e htC ht hX htX hDe (isPerfect_iff.mp hKc.1.1)
      hsN (F4Pilot.le_commutator_zpowers_of_isQuasisimple hKc.1 hsN hsC)
    rw [hKt, sup_idem]
    exact ⟨hB, hB⟩
  · obtain ⟨h1, h2⟩ := hasBLift_sup_conj_2E6_X hset hf2 hk hK hσ e htC ht hX htX hDe
      (isPerfect_iff.mp hKc.1.1) hcomm
    exact ⟨h2, h1⟩

end LiftX

section LiftY


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem exists_surjective_neighbourCore_2E6_Y_of_le_centralizer (hset : SeitzSetting G L)
    (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (hDO : D.subgroupOf (centralizer (X : Set G)) ≤
      centralizer (oddCore (centralizer (X : Set G)) : Set (centralizer (X : Set G))))
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hout : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hmodel : LieModel Kc .POmegaPlus 4 2 (2 * f)) :
    perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) =
        Kc ∧ HasBLift Kc ∧
      ∃ q : centralizerPerfectCore X →* Kc, Function.Surjective q ∧
        q.ker ≤ center (centralizerPerfectCore X) ∧ Odd (Nat.card q.ker) ∧
        ∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
          oddCore (centralizer (X : Set G))) = QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
            ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩ := by
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_2E6_Y hset hf2 hk hK hσ e htC ht hX htX hDe
  have hcommK : ⁅Kc, (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))⁆ ≠ ⊥ := fun h => by
    apply ne_bot_of_isQuasisimple hcomp.2.2
    have h1 := commutator_mono hDK (le_refl ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))))
    rw [commutator_eq_self_of_isQuasisimple' hcomp.2.2, h] at h1
    exact le_bot_iff.1 h1
  obtain ⟨hB, -⟩ := LinearPilot.hasBLift_of_isComponent_of_le_centralizer hDO hKc hKc hcommK hcommK
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd => by
    rw [hDe] at hd
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  obtain ⟨hcore, hrest⟩ := exists_surjective_neighbourCore_of_bLift ht htX hDt hsyl hKc hDK hsN
    hout (OmegaPilot.isSolvable_outer_of_lieModel_POmegaPlus hmodel) hB
  exact ⟨hcore, hB, hrest⟩

theorem le_centralizer_oddCore_2E6_Y_of_layer (hset : SeitzSetting G L) [CharP K 2]
    (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    {X : Subgroup G} (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (hlayer : ∀ (κ : Fin 2) (g : G),
      g⁻¹ * t * g = t * (e.symm (repYC (apply_apply_eq hK hσ) κ) : G) →
      (e.symm (repYC (apply_apply_eq hK hσ) κ) : G) ∈ CFSG.conjugate L g →
      (e.symm (repYC (apply_apply_eq hK hσ) κ) : G) ∈
        inSubgroup layer (CFSG.conjugate L g ⊓ centralizer (X : Set G))) :
    D.subgroupOf (centralizer (X : Set G)) ≤
      centralizer (oddCore (centralizer (X : Set G)) : Set (centralizer (X : Set G))) := by
  have hf : 1 ≤ f := by omega
  have hKt := inf_centralizer_eq_zpowers_twistedE6 hset hf hK hσ e htC ht
  have hLt := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  have hXL : X ≤ L := hX ▸ map_subtype_le _
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  obtain ⟨hD, hDq⟩ := neighbour_layer_2E6_Y hf2 hk hK hσ e hX hDe
  obtain ⟨-, -, -, -, hZD, -⟩ := neighbour_data_2E6_Y hset hf2 hk hK hσ e htC ht hX hDe
  obtain ⟨κ, g, hg⟩ := exists_conj_eq_mul_repYC_twistedE6 hset.standardSetting hf hk hK σ hσ e
    (exists_perfect_le_of_mulEquiv_twistedE6 (k := k) hf2 hk hK hσ e) hξ ht hKt
  set z : G := (e.symm (repYC (apply_apply_eq hK hσ) κ) : G) with hz
  have hzD : z ∈ D := by
    rw [hDe]
    exact ⟨e.symm (repYC (apply_apply_eq hK hσ) κ),
      ⟨repYC (apply_apply_eq hK hσ) κ,
        mem_subgroupOf.2 (repY_mem_omegaMinusLevi (apply_apply_eq hK hσ) κ), rfl⟩, rfl⟩
  have hz2 : orderOf z = 2 := by
    rw [hz, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact orderOf_repY κ
  have hzL : z ∈ L := (e.symm (repYC (apply_apply_eq hK hσ) κ)).2
  have hC0 : g * t * g⁻¹ ∉ L := by
    have h := conj_not_mem_of_mulEquiv_twistedE6 hset.standardSetting hf2 hk hK hσ e htC ht g⁻¹
    rwa [inv_inv] at h
  have hzg : z ∈ CFSG.conjugate L g := mem_conjugate_of_conj_eq_mul htC ht hKt hzL hg
    (exists_inner_repYC_twistedE6 hset.standardSetting hf2 hk hK hσ e ht hKt hg) hC0
  have hmain := UnitaryPilot.le_centralizer_oddCore_of_fused_of_mem_layer htC ht hLt htX hD hDq
    (OmegaPilot.odd_card_center_of_center_eq_bot hZD) hzD hz2 hg hzg (hlayer κ g hg hzg)
  intro d hd
  rw [mem_centralizer_iff]
  intro c hc
  exact Subtype.ext (hmain c ⟨c, hc, rfl⟩ d (mem_subgroupOf.1 hd))

end LiftY

end CFSG.SeitzReduction.TwistedE6Pilot
