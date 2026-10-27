module

public import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofPTools
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofX
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Tools
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartOne
import CFSG.RankThree.PartTwo.Sec10.Item109
import CFSG.GH74.GLS.LU.Local.FiveSL2
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.RankThree.PartTwo.Sec15.Item152StepsConf

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped MatrixGroups commutatorElement

namespace Proof152ConfA

section Transport

theorem characteristic_comap_mulEquiv {H K : Type*} [Group H] [Group K] (ψ : H ≃* K)
    {D : Subgroup K} (hD : D.Characteristic) : (D.comap ψ.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_eq]
  intro σ
  set τ : MulAut K := (ψ.symm.trans σ).trans ψ with hτ
  have h := Subgroup.characteristic_iff_comap_eq.mp hD τ
  ext x
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  have hx : τ (ψ x) = ψ (σ x) := by simp [hτ]
  rw [← hx]
  change ψ x ∈ D.comap τ.toMonoidHom ↔ ψ x ∈ D
  rw [h]

theorem pRank_congr {H K : Type*} [Group H] [Group K] (e : H ≃* K) (p : ℕ) :
    CFSG.pRank p H = CFSG.pRank p K := CFSG.pRank_congr_of_mulEquiv e p

end Transport

section Quotient

variable {Q : Type} [Group Q] [Finite Q]

theorem eq_oddCore_of_sl25 {N₀ : Subgroup Q} [N₀.Normal] (hle : N₀ ≤ CFSG.oddCore Q)
    (e : Q ⧸ N₀ ≃* SL(2, ZMod 5)) : N₀ = CFSG.oddCore Q := by
  refine le_antisymm hle ?_
  set M := (CFSG.oddCore Q).map (QuotientGroup.mk' N₀) with hM
  have hMn : M.Normal := (CFSG.oddCore_normal Q).map _ (QuotientGroup.mk'_surjective N₀)
  have hModd : Odd (Nat.card M) :=
    Odd.of_dvd_nat Sec10.odd_card_oddCore (Subgroup.card_map_dvd _ _)
  rcases CFSG.GH74.GLS.LU.Local.Five.sl2_five_normal_cases e.symm M with h | h | h
  · intro x hx
    have hmem : QuotientGroup.mk' N₀ x ∈ M := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff x).mp hmem
  · exfalso
    rw [h, CFSG.GH74.GLS.LU.Local.Five.sl2_five_center_card e.symm] at hModd
    exact (Nat.not_odd_iff_even.mpr even_two) hModd
  · exfalso
    rw [h, Subgroup.card_top, CFSG.GH74.GLS.LU.Local.Five.sl2_five_card e.symm] at hModd
    exact (Nat.not_odd_iff_even.mpr (by decide)) hModd

theorem exists_critical_data [Group.IsPerfect Q] (hO2 : CFSG.pCore 2 Q = ⊥)
    (e : Q ⧸ CFSG.oddCore Q ≃* SL(2, ZMod 5)) (hFfit : CFSG.oddCore Q ≤ fittingSubgroup Q)
    (hO3 : CFSG.pCore 3 Q = ⊥)
    (hrank : ∀ p : ℕ, p.Prime → 3 < p → ∀ D : Subgroup Q, CFSG.pRank p D ≤ 2) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (D₀ : Subgroup (CFSG.pCore p Q)), 3 < p ∧ D₀.Characteristic ∧
      IsPGroup p D₀ ∧ (∀ x : D₀, x ^ p = 1) ∧ commutator D₀ ≤ Subgroup.center D₀ ∧
      CFSG.pRank p D₀ = 2 ∧
      Subgroup.centralizer ((D₀.map (CFSG.pCore p Q).subtype : Subgroup Q) : Set Q) ≤
        CFSG.oddCore Q := by
  obtain ⟨p, hp, hCp⟩ := exists_prime_centralizer_pCore_le hO2 e hFfit
  have : Fact p.Prime := ⟨hp⟩
  have hFtop : CFSG.oddCore Q ≠ ⊤ := by
    intro htop
    have hnt : Nontrivial (Q ⧸ CFSG.oddCore Q) := by
      rw [← Finite.one_lt_card_iff_nontrivial,
        Nat.card_congr e.toEquiv, CFSG.GH74.GLS.LU.Local.Five.sl2_five_card (MulEquiv.refl _)]
      norm_num
    have : Subsingleton (Q ⧸ CFSG.oddCore Q) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    exact not_nontrivial_iff_subsingleton.mpr this hnt
  have hbot : ∀ N : Subgroup Q, N = ⊥ → ¬ Subgroup.centralizer (N : Set Q) ≤ CFSG.oddCore Q := by
    rintro N rfl hle
    apply hFtop
    rw [eq_top_iff, ← (Subgroup.centralizer_eq_top_iff_subset (s := ((⊥ : Subgroup Q) : Set Q))).mpr
      (by simp)]
    exact hle
  have hPne : CFSG.pCore p Q ≠ ⊥ := fun h => hbot _ h hCp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hPne hO2
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hPne hO3
  have hp3' : 3 < p := by
    have := hp.two_le
    omega
  have : Nontrivial (CFSG.pCore p Q) := (Subgroup.nontrivial_iff_ne_bot _).mpr hPne
  obtain ⟨D₀, hD₀c, hD₀1, hD₀comm, hD₀exp, hD₀fix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hp2
      (CFSG.pCore_isPGroup (p := p) (G := Q))
  have hDn : (D₀.map (CFSG.pCore p Q).subtype).Normal := inferInstance
  have hCD := centralizer_le_of_fixing e hp2 hCp hD₀fix hDn
  have hD₀p : IsPGroup p D₀ := (CFSG.pCore_isPGroup (p := p) (G := Q)).to_subgroup D₀
  have hexp : ∀ x : D₀, x ^ p = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, hD₀exp x x.2, Subgroup.coe_one])
  have hclass : commutator D₀ ≤ Subgroup.center D₀ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro d
    apply Subtype.ext
    have h1 : ⁅(a : CFSG.pCore p Q), (b : CFSG.pCore p Q)⁆ ∈ ⁅D₀, ⊤⁆ :=
      Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_top _)
    have h2 := Subgroup.mem_centralizer_iff.mp (hD₀comm h1).2 d d.2
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h2 ⊢
    exact h2
  set D := D₀.map (CFSG.pCore p Q).subtype with hD
  have eD : D₀ ≃* D := D₀.equivMapOfInjective _ (CFSG.pCore p Q).subtype_injective
  have hrk2 : CFSG.pRank p D₀ ≤ 2 := by
    rw [pRank_congr eD p]
    exact hrank p hp hp3' D
  have hcard : p < Nat.card D₀ := by
    by_contra hle
    push Not at hle
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hD₀p
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 1 with h | h
      · exfalso
        apply hD₀1
        apply Subgroup.eq_bot_of_card_eq
        rw [hk, show k = 0 by omega, pow_zero]
      · by_contra hk1
        have : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
        have : p < p ^ 2 := by nlinarith [hp.two_le]
        omega
    rw [hk1, pow_one] at hk
    have hDp : Nat.card D = p := by rw [← Nat.card_congr eD.toEquiv, hk]
    have : IsCyclic D := isCyclic_of_prime_card hDp
    set ρ : Q →* MulAut D := MulAut.conjNormal with hρ
    have hcomm : ∀ a b : MulAut D, a * b = b * a := fun a b =>
      (IsCyclic.mulAutMulEquiv D).injective (by rw [map_mul, map_mul, mul_comm])
    have : IsMulCommutative ρ.range := ⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩
    have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
    have : Subsingleton ρ.range := Group.IsPerfect.subsingleton_of_isMulCommutative
    apply hFtop
    rw [eq_top_iff]
    intro g _
    apply hCD
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 : ρ g = 1 := congrArg Subtype.val (Subsingleton.elim (⟨ρ g, g, rfl⟩ : ρ.range) 1)
    have h2 := congrArg (fun σ : MulAut D => ((σ ⟨d, hd⟩ : D) : Q)) h1
    simp only [hρ, MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc d * g = g * d * g⁻¹ * g := by rw [h2]
      _ = g * d := by group
  have hrk : CFSG.pRank p D₀ = 2 :=
    le_antisymm hrk2 (CFSG.RankThree.PartTwo.two_le_pRank hD₀p hexp hcard)
  exact ⟨p, inferInstance, D₀, hp3', hD₀c, hD₀p, hexp, hclass, hrk, hCD⟩

end Quotient

variable {G : Type} [Group G] [Finite G]

theorem sl25_data {X : Subgroup G} (hsl : IsSL25Case X) :
    Nonempty ((↥X ⧸ CFSG.pCore 2 ↥X) ⧸ CFSG.oddCore (↥X ⧸ CFSG.pCore 2 ↥X) ≃*
        SL(2, ZMod 5)) ∧
      CFSG.oddCore (↥X ⧸ CFSG.pCore 2 ↥X) ≤ fittingSubgroup (↥X ⧸ CFSG.pCore 2 ↥X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := ↥X ⧸ CFSG.pCore 2 ↥X with hQ
  have hO2 : CFSG.pCore 2 Q = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hpodd : ∀ p : ℕ, p.Prime → CFSG.pCore p Q ≤ CFSG.oddCore Q := by
    intro p hp
    by_cases hp2 : p = 2
    · subst hp2
      rw [hO2]
      exact bot_le
    · have : Fact p.Prime := ⟨hp⟩
      refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := p) (G := Q))
      rw [hk]
      exact (Nat.Prime.odd_of_ne_two hp hp2).pow
  have hfit : fittingSubgroup Q ≤ CFSG.oddCore Q := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    exact iSup_le fun p => hpodd p (Nat.prime_of_mem_primeFactors p.2)
  rcases hsl with he | he
  · obtain ⟨e⟩ := he
    have e' : Q ⧸ fittingSubgroup Q ≃* SL(2, ZMod 5) :=
      (Sec4.Census.quotientComapEquiv (CFSG.pCore 2 ↥X) (fittingSubgroup Q)).symm.trans e
    have heq := eq_oddCore_of_sl25 hfit e'
    exact ⟨⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans e'⟩, heq.symm.le⟩
  · obtain ⟨e⟩ := he
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have e' : Q ⧸ CFSG.pCore 5 Q ≃* SL(2, ZMod 5) :=
      (Sec4.Census.quotientComapEquiv (CFSG.pCore 2 ↥X) (CFSG.pCore 5 Q)).symm.trans e
    have heq := eq_oddCore_of_sl25 (hpodd 5 (by norm_num)) e'
    refine ⟨⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans e'⟩, ?_⟩
    rw [← heq]
    have : Group.IsNilpotent (CFSG.pCore 5 Q) :=
      (CFSG.pCore_isPGroup (p := 5) (G := Q)).isNilpotent
    exact le_sSup ⟨CFSG.pCore_normal, this⟩

theorem exists_pData152
    (hG : TheoremFourHyp G) {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y M X : Subgroup G} (hctx : Ctx152 A LB Y M X) (hA3 : IsPGroup 3 A) :
    ∃ (p : ℕ) (P : Subgroup G), PData152 A X p P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := ↥X ⧸ CFSG.pCore 2 ↥X with hQ
  set πt := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπt
  have hO2 : CFSG.pCore 2 Q = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  obtain ⟨⟨e⟩, hFfit⟩ := sl25_data hctx.sl25
  have hXp : Group.IsPerfect ↥X := isPerfect_of_mem_thetaComponentsIn hctx.mem_comp
  have hQp : Group.IsPerfect Q :=
    Group.IsPerfect.ofSurjective (f := πt) (QuotientGroup.mk'_surjective _)
  obtain ⟨hXs, hX60⟩ := Proof152Gen.isSimpleGroup_theta_quot_of_ctx152 hctx
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  obtain ⟨-, -, hθ3, -, -, -, hθO⟩ :=
    solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  have hθO2 : CFSG.pCore 2 ↥X ≤ θ := hθO 2 Nat.prime_two (by norm_num)
  have hO3 : CFSG.pCore 3 Q = ⊥ := by
    set Kt := θ.map πt with hKt
    have hKn : Kt.Normal := (aschbacherSolvableCore_normal 3 ↥X).map _
      (QuotientGroup.mk'_surjective _)
    have hKs : IsSimpleGroup (Q ⧸ Kt) :=
      (QuotientGroup.quotientQuotientEquivQuotient (CFSG.pCore 2 ↥X) θ hθO2).isSimpleGroup
    have hle : CFSG.pCore 3 Q ≤ Kt := Sec4.Census.pCore_le 3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 3) (G := Q))
    have hdvd : Nat.card (CFSG.pCore 3 Q) ∣ Nat.card θ :=
      (Subgroup.card_dvd_of_le hle).trans (Subgroup.card_map_dvd _ _)
    rw [hk] at hdvd
    apply Subgroup.eq_bot_of_card_eq
    rw [hk]
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, pow_zero]
    · exact absurd ((dvd_pow_self 3 hpos.ne').trans hdvd) hθ3
  have hXM : X ≤ M := le_of_mem_thetaComponentsIn hctx.mem_comp
  have hXtop : X ≠ ⊤ := fun h => hctx.mem_y2.1.1 (top_le_iff.mp (h ▸ hXM))
  have hS4 : SectionFourHyp ↥X := hG.sectionFourHyp hXtop
  have hX1 : X ≠ ⊥ := fun h => ne_bot_of_mem_scriptY4 hctx.mem_y4 (le_bot_iff.mp (h ▸ hctx.le_x))
  have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  have hO2X : CFSG.pCore 2 ↥X ≠ ⊥ :=
    pCore_ne_bot_of_isCharacteristicP (isCharacteristicP_of_mem_thetaComponentsIn hctx.fstar
      hctx.mem_comp)
  have hrank : ∀ p : ℕ, p.Prime → 3 < p → ∀ D : Subgroup Q, CFSG.pRank p D ≤ 2 := by
    intro p hp hp3 D
    have h1 := Sec4.Census.pRank_le_pRank_top hp D
    rw [Sec4.Census.pRank_quotient_pCore_two hO2X hp (by omega)] at h1
    have h2 := hS4.localRank_lt p hp hp3
    omega
  obtain ⟨p, hpF, D₀, hp3, hD₀c, hD₀p, hexp, hclass, hrk, hCD⟩ :=
    exists_critical_data hO2 e hFfit hO3 hrank
  have hp : p.Prime := hpF.out
  have hp2 : p ≠ 2 := by omega
  have hp3' : p ≠ 3 := by omega
  set O2p := (Sec4.oTwoP p ↥X).map X.subtype with hO2p
  have hO2pX : O2p ≤ X := Subgroup.map_subtype_le _
  have : (Sec4.oTwoP p ↥X).Characteristic := oTwoP_characteristic p
  have hAO2p : A ≤ Subgroup.normalizer (O2p : Set G) :=
    hctx.norm_x.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := X) _)
  have hO2p3 : ¬ 3 ∣ Nat.card O2p := by
    rw [hO2p, Subgroup.card_map_of_injective X.subtype_injective]
    exact (isPiSubgroup_piCompl_iff Nat.prime_three _).mp (isPiSubgroup_oTwoP hp hp3')
  obtain ⟨S, hS⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime 3 p
    hA3 hO2p3 (O2p.normalizerMonoidHom.comp (Subgroup.inclusion hAO2p))
  set R := (S : Subgroup O2p).map O2p.subtype with hR
  have hRO2p : R ≤ O2p := Subgroup.map_subtype_le _
  have hRX : R ≤ X := hRO2p.trans hO2pX
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    conv_rhs => rw [hR, ← hS ⟨a, ha⟩]
    rw [hR, Subgroup.map_map, Subgroup.map_map]
    rfl
  have hRp : IsPGroup p R := S.isPGroup'.map _
  set ψ₀ : R →* Q := πt.comp (Subgroup.inclusion hRX) with hψ₀
  have hψmem : ∀ r : R, ψ₀ r ∈ CFSG.pCore p Q := by
    intro r
    obtain ⟨y, hy, hyr⟩ := hRO2p r.2
    have hy' : y = Subgroup.inclusion hRX r := Subtype.ext hyr
    rw [hψ₀, MonoidHom.comp_apply, ← hy']
    exact hy
  have hψinj : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    have hr' : Subgroup.inclusion hRX r ∈ CFSG.pCore 2 ↥X := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥X)]
      exact hr
    obtain ⟨k, hk⟩ := hRp r
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ⟨_, hr'⟩
    have hj' : r ^ 2 ^ j = 1 := by
      apply Subtype.ext
      have := congrArg (fun t : CFSG.pCore 2 ↥X => ((t : ↥X) : G)) hj
      simpa using this
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hj')
    rw [(Nat.coprime_pow_primes k j hp Nat.prime_two hp2).gcd_eq_one, Nat.dvd_one,
      orderOf_eq_one_iff] at h1
    exact h1
  have hcardR : Nat.card R = Nat.card (CFSG.pCore p Q) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := p) (G := Q))
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥X))
    have hO2pcard : Nat.card O2p = 2 ^ m * p ^ n := by
      rw [hO2p, Subgroup.card_map_of_injective X.subtype_injective, ← hm, ← hn]
      exact QuotientGroup.card_preimage_mk (CFSG.pCore 2 ↥X)
        ((CFSG.pCore p Q : Subgroup Q) : Set Q)
    have hRcard : Nat.card R = Nat.card (S : Subgroup O2p) :=
      Subgroup.card_map_of_injective O2p.subtype_injective
    rw [hRcard, Sylow.card_eq_multiplicity, hO2pcard, hn,
      Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hp.ne_zero),
      Finsupp.add_apply, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun h => hp2
        ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))), zero_add]
  have hψsurj : ∀ y : CFSG.pCore p Q, ∃ r : R, ψ₀ r = y := by
    have hle : ψ₀.range ≤ CFSG.pCore p Q := by
      rintro _ ⟨r, rfl⟩
      exact hψmem r
    have heq : ψ₀.range = CFSG.pCore p Q := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψinj, Subgroup.card_top,
        hcardR]
    intro y
    have hy : (y : Q) ∈ ψ₀.range := by rw [heq]; exact y.2
    obtain ⟨r, hr⟩ := hy
    exact ⟨r, hr⟩
  set ψ : R ≃* CFSG.pCore p Q := MulEquiv.ofBijective (ψ₀.codRestrict _ hψmem)
    ⟨fun a b h => hψinj (congrArg Subtype.val h), fun y => by
      obtain ⟨r, hr⟩ := hψsurj y
      exact ⟨r, Subtype.ext hr⟩⟩ with hψ
  have hψapp : ∀ r : R, ((ψ r : CFSG.pCore p Q) : Q) = ψ₀ r := fun _ => rfl
  set P := (D₀.comap ψ.toMonoidHom).map R.subtype with hP
  have hPR : P ≤ R := Subgroup.map_subtype_le _
  have hPsub : P.subgroupOf R = D₀.comap ψ.toMonoidHom := by
    rw [hP, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective R.subtype_injective]
  have hPc : (D₀.comap ψ.toMonoidHom).Characteristic := characteristic_comap_mulEquiv ψ hD₀c
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    hAR.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := R) _)
  have eP : P ≃* D₀ :=
    ((D₀.comap ψ.toMonoidHom).equivMapOfInjective R.subtype R.subtype_injective).symm.trans
      ((ψ.subgroupMap (D₀.comap ψ.toMonoidHom)).trans (MulEquiv.subgroupCongr
        (Subgroup.map_comap_eq_self_of_surjective ψ.surjective D₀)))
  have hPp : IsPGroup p P := hD₀p.of_equiv eP.symm
  have hPexp : ∀ x : P, x ^ p = 1 := fun x => eP.injective (by rw [map_pow, hexp, map_one])
  have hPclass : commutator P ≤ Subgroup.center P := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro d
    apply eP.injective
    have h1 : ⁅eP a, eP b⁆ ∈ Subgroup.center D₀ := by
      refine hclass ?_
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [map_mul, map_mul, map_commutatorElement]
    exact Subgroup.mem_center_iff.mp h1 (eP d)
  have hPrk : CFSG.pRank p P = 2 := by rw [pRank_congr eP p, hrk]
  have htype := (rank3II_3_2 hPp hPexp hPclass).1 hPrk
  have hcent : X ⊓ Subgroup.centralizer (P : Set G) ≤ oTwoOddIn X := by
    intro y hy
    refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
    change πt ⟨y, hy.1⟩ ∈ CFSG.oddCore Q
    apply hCD
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    set r := ψ.symm d with hr
    have hrd : ψ r = d := by rw [hr, MulEquiv.apply_symm_apply]
    have hrP : (r : G) ∈ P := ⟨r, by
      change ψ r ∈ D₀
      rw [hrd]
      exact hd, rfl⟩
    have hyr : (r : G) * y = y * r := Subgroup.mem_centralizer_iff.mp hy.2 _ hrP
    have hdr : ((d : CFSG.pCore p Q) : Q) = πt (Subgroup.inclusion hRX r) := by
      rw [← hrd, hψapp]
      rfl
    rw [Subgroup.coe_subtype, hdr, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyr
  have hPc' : (P.subgroupOf R).Characteristic := by rw [hPsub]; exact hPc
  refine ⟨p, P, ⟨hp, hp2, hPR.trans hRX, ⟨R, ⟨S, rfl⟩, hPR, hPc'⟩, hAP, ?_, hcent⟩⟩
  rcases htype with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem step152ConfP_holds
    {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L) :
    Step152ConfP A (lB A) := fun _ _ _ _ _ hpt =>
  exists_pData152 hR.toTheoremFourHyp hpt.ctx
    (Late.isE27_of_mem_partTwoE hR.toSec13Data.mem_partTwoE).isPGroup

end Proof152ConfA

theorem step152ConfPR_of :
    Step152ConfPR :=
  fun _ _ _ _ _ _ hR => Proof152ConfA.step152ConfP_holds hR

end CFSG.RankThree.PartTwo.Sec15
