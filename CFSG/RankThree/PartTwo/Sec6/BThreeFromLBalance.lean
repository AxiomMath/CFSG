module

import CFSG.RankThree.PartTwo.Sec4.T444.Lift
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec6.Item65Tools

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

@[expose] def GWLBalanceStatement : Prop :=
  CFSG.Open.LBalanceStatement

namespace BThreeLBalance

theorem lBalanceIsKGroup_of_isKGroup {Q : Type} [Group Q] (hQ : CFSG.IsKGroup Q) :
    CFSG.Open.lBalanceIsKGroup Q :=
  CFSG.KCore.KGroupAllSimple.kGroupNonab hQ

theorem lBalancePrimeCore_top_quotient (Q : Type) [Group Q] [Finite Q] :
    CFSG.Open.lBalancePrimeCore 3 (⊤ : Subgroup (Q ⧸ CFSG.pPrimeCore 3 Q)) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.ComponentClassification.LBalance.primeCore_top]
  exact CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3

theorem le_theta_of_normal {Q : Type} [Group Q] [Finite Q] (hQp : Group.IsPerfect Q)
    (hQq : IsQuasisimple (Q ⧸ aschbacherSolvableCore 3 Q)) (hQ3 : 3 ∣ Nat.card Q)
    {D : Subgroup Q} (hD : D.Normal) (hD3 : ¬ 3 ∣ Nat.card D) :
    D ≤ aschbacherSolvableCore 3 Q := by
  have htop : (⊤ : Subgroup Q) ∈ thetaComponents 3 Q := by
    refine ⟨Group.IsPerfect.top_iff.mpr hQp, Subgroup.IsSubnormal.top, ?_⟩
    set e : Q ≃* (⊤ : Subgroup Q) := Subgroup.topEquiv.symm
    exact LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)) hQq
  have h := Sec4.inf_pPrimeCore_eq_of_mem_thetaComponents htop (by rwa [Subgroup.card_top])
  rw [top_inf_eq, inSubgroup_aschbacherSolvableCore_top Nat.prime_three] at h
  rw [← h]
  exact Sec4.le_pPrimeCore_of_normal hD hD3

theorem not_dvd_card_of_ker_range {A B : Type*} [Group A] [Group B] {p : ℕ} (hp : p.Prime)
    (f : A →* B) (hk : ¬ p ∣ Nat.card f.ker) (hr : ¬ p ∣ Nat.card f.range) :
    ¬ p ∣ Nat.card A := by
  rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker]
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact hk h
  · exact hr h

section Chains

variable {M : Type*} [Group M]

theorem isSubnormal_trans {A B C : Subgroup M} (h₁ : CFSG.Open.IsSubnormal A B)
    (h₂ : CFSG.Open.IsSubnormal B C) : CFSG.Open.IsSubnormal A C :=
  h₁.trans h₂

theorem isSubnormal_inf {A B : Subgroup M} (h : CFSG.Open.IsSubnormal A B) (K : Subgroup M) :
    CFSG.Open.IsSubnormal (A ⊓ K) (B ⊓ K) := by
  have h1 := CFSG.ComponentClassification.Components.chain_map K.subtype
    (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf h K)
  simpa only [Subgroup.subgroupOf_map_subtype] using h1

theorem centralizer_subgroupOf_normalizer_normal (P : Subgroup M) :
    ((Subgroup.centralizer (P : Set M)).subgroupOf (Subgroup.normalizer (P : Set M))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.centralizer_le_normalizer _)]
  intro c n hc hn
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro p hp
  have hp' : n⁻¹ * p * n⁻¹⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) p).mp hp
  rw [inv_inv] at hp'
  have h1 := hc _ hp'
  calc p * (n * c * n⁻¹) = n * ((n⁻¹ * p * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * p * n)) * n⁻¹ := by rw [h1]
    _ = n * c * n⁻¹ * p := by group

end Chains

theorem subgroupOf_inf_centralizer {G : Type} [Group G] {H : Subgroup G} {b : G} (hb : b ∈ H) :
    (H ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf H =
      Subgroup.centralizer ((Subgroup.zpowers (⟨b, hb⟩ : H) : Subgroup H) : Set H) := by
  rw [centralizer_zpowers_eq]
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, hx⟩
    exact Subtype.ext hx
  · intro hx
    exact ⟨x.2, congrArg Subtype.val hx⟩

theorem isPGroup_zpowers {Q : Type*} [Group Q] {x : Q} (hx : x ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hx, one_zpow, Subgroup.coe_one]

open CFSG.ComponentClassification CFSG.ComponentClassification.LBalance in
theorem map_theta_commute {M Q : Type} [Group M] [Finite M] [Group Q] [Finite Q]
    (N : Subgroup M) (ρ : Q →* M) (hsn : CFSG.Open.IsSubnormal ρ.range N)
    (hQp : Group.IsPerfect Q) (hQq : IsQuasisimple (Q ⧸ aschbacherSolvableCore 3 Q))
    (hQ3 : 3 ∣ Nat.card Q) (hker : ¬ 3 ∣ Nat.card ρ.ker)
    (hGW : ∀ a ∈ CFSG.Open.lBalancePLayer 3 N, ∀ c ∈ CFSG.Open.lBalancePrimeCore 3 N,
      a * c = c * a) :
    ∀ t ∈ aschbacherSolvableCore 3 Q, ∀ y : Q, ρ t * ρ y = ρ y * ρ t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hρN : ρ.range ≤ N := subnormal_le hsn
  set θQ := aschbacherSolvableCore 3 Q with hθQ
  set Tbar := θQ.map ρ with hTbar
  set O := CFSG.Open.lBalancePrimeCore 3 N with hO
  have hON : O ≤ N := primeCore_le 3 N
  have hNO : N ≤ Subgroup.normalizer (O : Set M) :=
    Sec4.le_normalizer_of_subgroupOf_normal hON (primeCore_normal 3 N)
  have hTY : Tbar ≤ ρ.range := Subgroup.map_le_range ρ θQ
  have hTsn : CFSG.Open.IsSubnormal Tbar N := by
    refine CFSG.Open.IsSubnormal.step hTY ?_ hsn
    rw [Subgroup.normal_subgroupOf_iff hTY]
    rintro _ _ ⟨t, ht, rfl⟩ ⟨q, rfl⟩
    exact ⟨q * t * q⁻¹, (inferInstance : θQ.Normal).conj_mem t ht q, by simp⟩
  have hTO : Tbar ≤ O := by
    have hTN : Tbar ≤ N := hTY.trans hρN
    have h1 : (Tbar.subgroupOf N).IsSubnormal :=
      Components.mathlib_subnormal_of_chain ((subnormal_subgroupOf_iff hTN).mpr hTsn)
        Subgroup.IsSubnormal.top
    have h2 : ¬ 3 ∣ Nat.card (Tbar.subgroupOf N) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv]
      exact fun h => (solvable_prime_complement_core_characterization (H := Q)
        Nat.prime_three).2.2.1 (h.trans (Subgroup.card_map_dvd θQ ρ))
    have h3 := Sec4.le_pPrimeCore_of_isSubnormal h1 h2
    rw [hO, primeCore_eq_map, ← Subgroup.map_subgroupOf_eq_of_le hTN]
    exact Subgroup.map_mono h3
  set D := O.comap ρ with hD
  have hDn : D.Normal := by
    refine ⟨fun d hd q => ?_⟩
    change ρ (q * d * q⁻¹) ∈ O
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hNO (hρN ⟨q, rfl⟩)) (ρ d)).mp hd
  have hD3 : ¬ 3 ∣ Nat.card D := by
    let f : D →* M := ρ.comp D.subtype
    refine not_dvd_card_of_ker_range Nat.prime_three f ?_ ?_
    · let ι : f.ker →* ρ.ker :=
        (D.subtype.comp f.ker.subtype).codRestrict ρ.ker fun x => by
          have hx := x.2
          rw [MonoidHom.mem_ker] at hx ⊢
          exact hx
      have hι : Function.Injective ι := fun x y hxy =>
        Subtype.ext (Subtype.ext (congrArg (fun z : ρ.ker => (z : Q)) hxy))
      exact fun h => hker (h.trans (Subgroup.card_dvd_of_injective ι hι))
    · intro h
      apply (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (primeCore_coprime 3 N)
      refine h.trans (Subgroup.card_dvd_of_le ?_)
      rintro _ ⟨d, rfl⟩
      exact d.2
  have hDθ : D = θQ :=
    le_antisymm (le_theta_of_normal hQp hQq hQ3 hDn hD3) fun t ht => hTO ⟨t, ht, rfl⟩
  have hρN' : ∀ q : Q, ρ q ∈ N := fun q => hρN ⟨q, rfl⟩
  let ρN : Q →* N := ρ.codRestrict N hρN'
  let ψ : Q →* (N ⧸ CFSG.pPrimeCore 3 N) := (QuotientGroup.mk' (CFSG.pPrimeCore 3 N)).comp ρN
  have hmemO : ∀ q : Q, ρN q ∈ CFSG.pPrimeCore 3 N ↔ ρ q ∈ O := by
    intro q
    rw [hO, primeCore_eq_map]
    constructor
    · intro h
      exact ⟨ρN q, h, rfl⟩
    · rintro ⟨n, hn, hnq⟩
      have hn' : n = ρN q := Subtype.ext hnq
      rwa [← hn']
  have hψker : ψ.ker = θQ := by
    rw [← hDθ]
    ext q
    rw [MonoidHom.mem_ker]
    simp only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hmemO q
  have hψrange : ψ.range = quotientImage 3 N ρ.range := by
    rw [MonoidHom.range_comp, quotientImage]
    congr 1
    ext n
    simp only [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q, rfl⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, Subtype.ext hq⟩
  let e : (Q ⧸ θQ) ≃* quotientImage 3 N ρ.range :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hψrange))
  have hOq : CFSG.Open.IsQuasisimple (Q ⧸ θQ) := ⟨hQq.1.commutator_eq_top, hQq.2.1⟩
  have hcomp : CFSG.Open.IsComponentOf (quotientImage 3 N ρ.range) ⊤ := by
    refine ⟨le_top, ?_, Components.quasisimple_of_equiv e.symm hOq⟩
    have hchain : CFSG.Open.IsSubnormal (ρ.range.subgroupOf N) ⊤ :=
      (subnormal_subgroupOf_iff hρN).mpr hsn
    have hmapped := Components.chain_map (QuotientGroup.mk' (CFSG.pPrimeCore 3 N)) hchain
    simpa only [quotientImage,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using hmapped
  obtain ⟨L, -, hLmin⟩ := Finite.exists_le_minimal
    (p := fun J : Subgroup M => J ≤ ρ.range ∧ CFSG.Open.IsSubnormal J N ∧ J ⊔ O = ρ.range ⊔ O)
    (a := ρ.range) ⟨le_rfl, hsn, rfl⟩
  obtain ⟨hLY, hLsn, hLO⟩ := hLmin.prop
  have hLN : L ≤ N := hLY.trans hρN
  have hLcomp : CFSG.Open.lBalanceIsPComponent 3 N L := by
    refine (pComponent_iff_minimal_image 3 N L hLN).mpr ⟨hLsn, ?_, ?_⟩
    · rw [(quotientImage_eq_iff 3 N hLN hρN).mpr hLO]
      exact hcomp
    · intro J hJL hJsn hJimg
      have hJO := (quotientImage_eq_iff 3 N (hJL.trans hLN) hLN).mp hJimg
      exact le_antisymm hJL (hLmin.2 ⟨hJL.trans hLY, hJsn, hJO.trans hLO⟩ hJL)
  have hLT : ∀ l ∈ L, ∀ t ∈ Tbar, l * t = t * l := fun l hl t ht =>
    hGW l ((le_sSup hLcomp : L ≤ CFSG.Open.lBalancePLayer 3 N) hl) t (hTO ht)
  have hYLT : ρ.range ≤ Tbar ⊔ L := by
    intro y hy
    have hy' : y ∈ L ⊔ O := by
      rw [hLO]
      exact Subgroup.mem_sup_left hy
    have hy'' : y ∈ ((L ⊔ O : Subgroup M) : Set M) := hy'
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L O (hLN.trans hNO)] at hy''
    obtain ⟨l, hl, o, ho, rfl⟩ := hy''
    have hoY : o ∈ ρ.range := by
      have := ρ.range.mul_mem (ρ.range.inv_mem (hLY hl)) hy
      simpa using this
    obtain ⟨q, rfl⟩ := hoY
    have hqθ : q ∈ θQ := hDθ ▸ (show q ∈ D from ho)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hl) (Subgroup.mem_sup_left ⟨q, hqθ, rfl⟩)
  have hYp : Group.IsPerfect ρ.range := by
    have := hQp
    exact Group.IsPerfect.ofSurjective (f := ρ.rangeRestrict) ρ.rangeRestrict_surjective
  have hTsol : Group.IsSolvable Tbar := by
    have := (solvable_prime_complement_core_characterization (H := Q) Nat.prime_three).1
    exact Group.isSolvable_of_surjective (f := ρ.subgroupMap θQ) (ρ.subgroupMap_surjective θQ)
  have hTL : Tbar ≤ Subgroup.centralizer (L : Set M) := fun t ht =>
    Subgroup.mem_centralizer_iff.mpr fun l hl => hLT l hl t ht
  have hle := le_perfectResidual_sup hYp (hTL.trans (Subgroup.centralizer_le_normalizer _)) hYLT
  have hres : inSubgroup perfectResidual Tbar = ⊥ := by
    rw [inSubgroup, (perfect_residual_characterization (G := Tbar)).2.2.2.2.2.mpr hTsol,
      Subgroup.map_bot]
  rw [hres, bot_sup_eq] at hle
  intro t ht y
  exact (hLT (ρ y) (hle ⟨y, rfl⟩) (ρ t) ⟨t, ht, rfl⟩).symm

end BThreeLBalance

open BThreeLBalance in
open CFSG.RankThreeEvenClassification.Helpers
  (centralizer_map_eq_of_pGroup_prime_complement_kernel) in
theorem bThreeProperty_of_three_dvd (hGW : GWLBalanceStatement) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} (hH : SectionFourHyp H) {X : Subgroup G} (hX : X ∈ thetaComponentsIn H)
    {b : G} (hbH : b ∈ H) (hb3 : b ^ 3 = 1) {Y : Subgroup G}
    (hYXC : Y ≤ X ⊓ Subgroup.centralizer {b}) (hYp : Group.IsPerfect Y)
    (hYsn : (Y.subgroupOf (X ⊓ Subgroup.centralizer {b})).IsSubnormal)
    (hYq : IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y)) (hY3 : 3 ∣ Nat.card Y) :
    ⁅inSubgroup (aschbacherSolvableCore 3) Y, Y⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXH, hX'⟩ := mem_thetaComponentsIn_iff.mp hX
  have hYX : Y ≤ X := hYXC.trans inf_le_left
  have hYH : Y ≤ H := hYX.trans hXH
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hch1 : CFSG.Open.IsSubnormal Y (X ⊓ C) :=
    (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hYXC).mp
      (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hYsn)
  have hch2 : CFSG.Open.IsSubnormal X H :=
    (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hXH).mp
      (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hX'.2.1)
  have hch3 : CFSG.Open.IsSubnormal Y (H ⊓ C) := isSubnormal_trans hch1 (isSubnormal_inf hch2 C)
  set π : H →* H ⧸ CFSG.pPrimeCore 3 H := QuotientGroup.mk' (CFSG.pPrimeCore 3 H) with hπ
  set b' : H := ⟨b, hbH⟩ with hb'
  set ρ : Y →* H ⧸ CFSG.pPrimeCore 3 H := π.comp (Subgroup.inclusion hYH) with hρ
  set P : Subgroup (H ⧸ CFSG.pPrimeCore 3 H) := Subgroup.zpowers (π b') with hP
  set N := Subgroup.normalizer (P : Set (H ⧸ CFSG.pPrimeCore 3 H)) with hN
  have hb'3 : b' ^ 3 = 1 := Subtype.ext (by simpa [b'] using hb3)
  have hP3 : IsPGroup 3 P := isPGroup_zpowers (by rw [← map_pow, hb'3, map_one])
  have hcen : (Subgroup.centralizer ((Subgroup.zpowers b' : Subgroup H) : Set H)).map π =
      Subgroup.centralizer (P : Set (H ⧸ CFSG.pPrimeCore 3 H)) := by
    rw [centralizer_map_eq_of_pGroup_prime_complement_kernel 3 Nat.prime_three π
      (QuotientGroup.mk'_surjective _) ?_ _ (isPGroup_zpowers hb'3), MonoidHom.map_zpowers]
    rw [hπ, QuotientGroup.ker_mk']
    exact Sec4.not_three_dvd_card_pPrimeCore
  have hsn : CFSG.Open.IsSubnormal ρ.range N := by
    have h1 := CFSG.ComponentClassification.Components.chain_map π
      (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf hch3 H)
    rw [subgroupOf_inf_centralizer hbH, hcen] at h1
    have h2 : ρ.range = (Y.subgroupOf H).map π := by
      rw [hρ, MonoidHom.range_comp, Subgroup.inclusion_range]
    rw [h2]
    exact isSubnormal_trans h1 (CFSG.Open.IsSubnormal.step
      (Subgroup.centralizer_le_normalizer _) (centralizer_subgroupOf_normalizer_normal P)
      (CFSG.Open.IsSubnormal.refl N))
  have hker : ¬ 3 ∣ Nat.card ρ.ker := by
    have hle : ρ.ker.map (Subgroup.inclusion hYH) ≤ CFSG.pPrimeCore 3 H := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : ρ y = 1 := hy
      rw [hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy'
      exact hy'
    intro h
    rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hYH)] at h
    exact Sec4.not_three_dvd_card_pPrimeCore (h.trans (Subgroup.card_dvd_of_le hle))
  have hK : CFSG.Open.lBalanceIsKGroup (H ⧸ CFSG.pPrimeCore 3 H) :=
    lBalanceIsKGroup_of_isKGroup
      (CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient hH.kGroup _)
  obtain ⟨-, -, hGW3⟩ := hGW (H ⧸ CFSG.pPrimeCore 3 H) hK 3 Nat.prime_three P hP3
  have hcomm := map_theta_commute N ρ hsn hYp hYq hY3 hker
    (hGW3 (lBalancePrimeCore_top_quotient H))
  have hθYO : ⁅inSubgroup (aschbacherSolvableCore 3) Y, Y⁆ ≤
      (CFSG.pPrimeCore 3 H).map H.subtype := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨t, ht, rfl⟩ y hy
    have h1 := hcomm t ht ⟨y, hy⟩
    refine ⟨⁅Subgroup.inclusion hYH t, Subgroup.inclusion hYH ⟨y, hy⟩⁆, ?_, ?_⟩
    · rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff]
      change π ⁅Subgroup.inclusion hYH t, Subgroup.inclusion hYH ⟨y, hy⟩⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h1
    · simp [commutatorElement_def]
  have hX3 : 3 ∣ Nat.card (X.subgroupOf H) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv]
    exact hY3.trans (Subgroup.card_dvd_of_le hYX)
  have hXθ := congrArg (Subgroup.map H.subtype)
    (Sec4.inf_pPrimeCore_eq_of_mem_thetaComponents hX' hX3)
  rw [Subgroup.map_inf_eq _ _ _ H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hXH,
    map_inSubgroup_theta_of_injective _ H.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hXH] at hXθ
  rw [← hXθ]
  exact le_inf ((Subgroup.commutator_mono ((Subgroup.map_subtype_le _).trans hYX) hYX).trans
    (Subgroup.commutator_le_self X)) hθYO

end CFSG.RankThree.PartTwo.Sec6
