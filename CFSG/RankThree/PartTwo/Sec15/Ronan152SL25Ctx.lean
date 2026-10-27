module

public import CFSG.RankThree.PartTwo.Sec15.Item152StepsConf
import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofP
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofXTools
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Tools
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartOne
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Ctx152J (A : Subgroup G) (LB : Subgroup G → Subgroup G) (M X : Subgroup G) :
    Prop where
  mem_y2 : M ∈ scriptY2 A
  fstar : generalizedFitting ↥M = CFSG.pCore 2 ↥M
  mem_comp : X ∈ thetaComponentsIn M
  norm_x : A ≤ Subgroup.normalizer (X : Set G)
  delta_x : X = delta A LB X
  sl25 : IsSL25Case X

namespace Ronan152SL25

open Proof152ConfA Proof152Gen

theorem ne_bot_of_isSL25Case {X : Subgroup G} (hsl : IsSL25Case X) : X ≠ ⊥ := by
  intro hX
  have hsub : Subsingleton ↥X := by
    rw [hX]
    infer_instance
  have hne : ∀ (N : Subgroup ↥X), (↥X ⧸ N ≃* SL(2, ZMod 5)) → False := by
    intro N e
    have : Subsingleton (↥X ⧸ N) := by
      constructor
      intro a b
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N b
      rw [Subsingleton.elim a b]
    have h1 : (e.symm (-1) : ↥X ⧸ N) = e.symm 1 := Subsingleton.elim _ _
    have h2 : (-1 : SL(2, ZMod 5)) = 1 := e.symm.injective h1
    have h3 := congrArg (fun g : SL(2, ZMod 5) => (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0) h2
    revert h3
    decide
  rcases hsl with he | he
  · obtain ⟨e⟩ := he
    exact hne _ e
  · obtain ⟨e⟩ := he
    exact hne _ e

theorem _root_.CFSG.RankThree.PartTwo.Sec15.Ctx152J.ne_bot {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} {M X : Subgroup G} (hctx : Ctx152J A LB M X) : X ≠ ⊥ :=
  ne_bot_of_isSL25Case hctx.sl25

theorem isSimpleGroup_theta_quotJ
    {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {M X : Subgroup G} (hctx : Ctx152J A LB M X) :
    IsSimpleGroup (↥X ⧸ aschbacherSolvableCore 3 ↥X) ∧
      Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) = 60 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXq := isQuasisimple_theta_of_mem_thetaComponentsIn hctx.mem_comp
  have hθ : Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) = 60 ∧
      CFSG.pPrimeCore 3 ↥X = aschbacherSolvableCore 3 ↥X := by
    rcases hctx.sl25 with he | he
    · obtain ⟨e⟩ := he
      exact sl25_theta hXq e
    · obtain ⟨e⟩ := he
      exact sl25_theta hXq e
  obtain ⟨h60, hcore⟩ := hθ
  set θ := aschbacherSolvableCore 3 ↥X with hθdef
  have hθ3 := (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1
  have hQp : Group.IsPerfect (↥X ⧸ θ) := hXq.1
  have hZ : Subgroup.center (↥X ⧸ θ) = ⊥ := by
    by_cases h3 : 3 ∣ Nat.card (Subgroup.center (↥X ⧸ θ))
    · exfalso
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
      set T := Subgroup.zpowers (z : ↥X ⧸ θ) with hT
      have hTc : T ≤ Subgroup.center (↥X ⧸ θ) := Subgroup.zpowers_le.mpr z.2
      have : T.Normal := Subgroup.normal_of_le_center hTc
      have hT3 : Nat.card T = 3 := by
        rw [hT, Nat.card_zpowers, Subgroup.orderOf_coe, hz]
      have hperf : Group.IsPerfect ((↥X ⧸ θ) ⧸ T) :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' T) (QuotientGroup.mk'_surjective T)
      have h20 : Nat.card ((↥X ⧸ θ) ⧸ T) = 20 := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup T
        rw [h60, hT3] at h
        omega
      exact false_of_isPerfect_of_card_twenty hperf h20
    · set K := (Subgroup.center (↥X ⧸ θ)).comap (QuotientGroup.mk' θ) with hK
      have hKn : K.Normal := Subgroup.Normal.comap inferInstance _
      have hKcard : Nat.card K = Nat.card θ * Nat.card (Subgroup.center (↥X ⧸ θ)) :=
        QuotientGroup.card_preimage_mk θ (Subgroup.center (↥X ⧸ θ) : Set (↥X ⧸ θ))
      have hK3 : Nat.Coprime 3 (Nat.card K) := by
        rw [hKcard]
        exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
      have hKle : K ≤ CFSG.pPrimeCore 3 ↥X := le_sSup ⟨hKn, hK3⟩
      rw [hcore] at hKle
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ q
      rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hKle hq
  have : IsSimpleGroup ((↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ)) := hXq.2.1
  have e1 : (↥X ⧸ θ) ≃* (↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact ⟨e1.isSimpleGroup, h60⟩

theorem exists_pData152J
    (hG : TheoremFourHyp G) {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {M X : Subgroup G} (hctx : Ctx152J A LB M X) (hA3 : IsPGroup 3 A) :
    ∃ (p : ℕ) (P : Subgroup G), PData152 A X p P ∧ 3 < p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := ↥X ⧸ CFSG.pCore 2 ↥X with hQ
  set πt := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπt
  have hO2 : CFSG.pCore 2 Q = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  obtain ⟨⟨e⟩, hFfit⟩ := sl25_data hctx.sl25
  have hXp : Group.IsPerfect ↥X := isPerfect_of_mem_thetaComponentsIn hctx.mem_comp
  have hQp : Group.IsPerfect Q :=
    Group.IsPerfect.ofSurjective (f := πt) (QuotientGroup.mk'_surjective _)
  obtain ⟨hXs, hX60⟩ := isSimpleGroup_theta_quotJ hctx
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
  have hX1 : X ≠ ⊥ := hctx.ne_bot
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
  refine ⟨p, P, ⟨hp, hp2, hPR.trans hRX, ⟨R, ⟨S, rfl⟩, hPR, hPc'⟩, hAP, ?_, hcent⟩, hp3⟩
  rcases htype with h | h
  · exact Or.inr h
  · exact Or.inl h

end Ronan152SL25

end CFSG.RankThree.PartTwo.Sec15
