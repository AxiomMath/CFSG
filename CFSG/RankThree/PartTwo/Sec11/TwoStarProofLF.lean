module

public import CFSG.RankThree.PartTwo.Sec11.TwoStarProof
public import CFSG.RankThree.PartTwo.Sec11.TwoStarProofLFTools
public import CFSG.RankThree.PartTwo.KFacts.LandazuriSeitzProof
import CFSG.RankThree.PartTwo.Sec4.Item420
import CFSG.RankThree.PartOne.S11c.CentralWitness
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.FixedRank36 (fixedSub frattiniRep)
open CFSG.Assembly.RankThreeEven (projSL)
open scoped IsMulCommutative commutatorElement

@[expose] def LandazuriSeitzL2EvenSolvable : Prop :=
  ∀ (f : ℕ), 6 ≤ f → ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
    ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
      ∀ (N : Subgroup X) [N.Normal], Group.IsSolvable N → ¬ 3 ∣ Nat.card N →
        Nonempty (X ⧸ N ≃* projSL 2 (GaloisField 2 f)) →
      ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
        (ρ : X →* (V →ₗ[ZMod p] V)), ¬ N ≤ ρ.ker →
          ∃ t : X, ρ t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
            3 ≤ Module.finrank (ZMod p) (LinearMap.ker (ρ t - 1))

namespace TwoStarProof

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev twoQuotAction {H X : Subgroup G}
    (hXH : X ≤ Subgroup.normalizer (H : Set G)) : X →* MulAut (H ⧸ CFSG.pCore 2 H) :=
  (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (CFSG.pCore 2 H)).comp
    (H.normalizerMonoidHom.comp (Subgroup.inclusion hXH))

omit [Finite G] in
theorem twoQuotAction_mk {H X : Subgroup G} (hXH : X ≤ Subgroup.normalizer (H : Set G))
    (x : X) (h : H) :
    twoQuotAction hXH x (h : H ⧸ CFSG.pCore 2 H) =
      ((H.normalizerMonoidHom ⟨x, hXH x.2⟩ h : H) : H ⧸ CFSG.pCore 2 H) :=
  CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply _ _ h

theorem exists_pCore_moved {H X : Subgroup G} (hXH : X ≤ Subgroup.normalizer (H : Set G))
    (hnot : ¬ ⁅X, inSubgroup twoFitting H⁆ ≤ inSubgroup (CFSG.pCore 2) H) :
    ∃ p : ℕ, p.Prime ∧ ∃ x : X, ∃ z ∈ CFSG.pCore p (H ⧸ CFSG.pCore 2 H),
      twoQuotAction hXH x z ≠ z := by
  by_contra hall
  push Not at hall
  apply hnot
  rw [Subgroup.commutator_le]
  intro x hx v hv
  obtain ⟨h, hh, rfl⟩ := hv
  have hfit : CFSG.fittingSubgroup (H ⧸ CFSG.pCore 2 H) ≤
      fixedSub (twoQuotAction hXH ⟨x, hx⟩) := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    intro z hz
    exact hall q.1.1 (Nat.prime_of_mem_primeFactors q.1.2) ⟨x, hx⟩ z hz
  have h1 : twoQuotAction hXH ⟨x, hx⟩ (h : H ⧸ CFSG.pCore 2 H) =
      (h : H ⧸ CFSG.pCore 2 H) := hfit hh
  rw [twoQuotAction_mk, QuotientGroup.eq] at h1
  set w := H.normalizerMonoidHom ⟨x, hXH hx⟩ h with hw
  have hwv : (w : G) = x * h * x⁻¹ := rfl
  have h2 : w * h⁻¹ ∈ CFSG.pCore 2 H := by
    have h3 := (CFSG.pCore_normal (p := 2) (G := H)).conj_mem _ h1 w
    have e : w * (w⁻¹ * h) * w⁻¹ = h * w⁻¹ := by group
    rw [e] at h3
    have h4 := Subgroup.inv_mem _ h3
    rwa [mul_inv_rev, inv_inv] at h4
  refine ⟨_, h2, ?_⟩
  simp [hwv, commutatorElement_def]

theorem exists_involution_projSL (f : ℕ) :
    ∃ u : projSL 2 (GaloisField 2 f), u * u = 1 ∧ u ≠ 1 := by
  set E := KFacts.KS116Proof.projSLEquiv (GaloisField 2 f)
  refine ⟨E (KFacts.KS116Proof.uu 1), ?_, ?_⟩
  · rw [← map_mul, ← KFacts.KS116Proof.uu_add, CharTwo.add_self_eq_zero,
      KFacts.KS116Proof.uu_zero, map_one]
  · intro h1
    have h2 : KFacts.KS116Proof.uu (1 : GaloisField 2 f) = KFacts.KS116Proof.uu 0 := by
      rw [KFacts.KS116Proof.uu_zero]
      exact E.injective (h1.trans (map_one E).symm)
    exact one_ne_zero (KFacts.KS116Proof.uu_injective h2)

theorem exists_two_element_fixed_of_LS {X : Type} [Group X] [Finite X] {N : Subgroup X}
    [N.Normal] {m : ℕ} (hm : 2 ≤ m) (e : X ⧸ N ≃* projSL 2 (GaloisField 2 (3 * m))) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (ρ : X →* (V →ₗ[ZMod p] V)) (hN : N ≤ ρ.ker)
    (hρ : ∃ x, ρ x ≠ 1) :
    ∃ t : X, ρ t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
      3 ≤ Module.finrank (ZMod p) (LinearMap.ker (ρ t - 1)) := by
  set K := GaloisField 2 (3 * m)
  have hK4 : 4 ≤ Nat.card K := by
    rw [GaloisField.card 2 (3 * m) (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK4
  have hsimple : IsSimpleGroup (X ⧸ N) := MulEquiv.isSimpleGroup (e.trans (Sec4.projSLEquivPSL K))
  set ρbar := QuotientGroup.lift N ρ hN with hρbar
  have hinj : Function.Injective ρbar := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρbar.ker with hb | ht
    · exact hb
    · exfalso
      obtain ⟨x, hx⟩ := hρ
      apply hx
      have hmem : (x : X ⧸ N) ∈ ρbar.ker := ht ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hρbar, QuotientGroup.lift_mk] at hmem
      exact hmem
  set ρ' := ρbar.comp e.symm.toMonoidHom with hρ'
  have hρ'inj : Function.Injective ρ' := hinj.comp e.symm.injective
  have hLS := KFacts.landazuriSeitzL2Even (3 * m) (by omega) p hp2 V ρ' hρ'inj
  obtain ⟨u, hu2, hu1⟩ := exists_involution_projSL (3 * m)
  have hou : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have hfix := hLS.2 u hou
  obtain ⟨t, htu, k, htk⟩ := exists_two_element_lift (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (y := e.symm u) (by rw [← map_mul, hu2, map_one])
  have hρt : ρ t = ρ' u := by
    rw [hρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← htu, QuotientGroup.mk'_apply,
      hρbar, QuotientGroup.lift_mk]
  refine ⟨t, ?_, ⟨k, htk⟩, ?_⟩
  · rw [hρt]
    intro h1
    exact hu1 (hρ'inj (h1.trans (map_one ρ').symm))
  · rw [hρt]
    have h64 : 64 ≤ 2 ^ (3 * m) := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem exists_fixed_elemAbelian {H X : Subgroup G} (hXH : X ≤ Subgroup.normalizer (H : Set G))
    [Group.IsPerfect X] (h3 : ¬ 3 ∣ Nat.card H)
    (hnot : ¬ ⁅X, inSubgroup twoFitting H⁆ ≤ inSubgroup (CFSG.pCore 2) H)
    (hfix : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (V : Type) [AddCommGroup V]
      [Module (ZMod p) V] [Module.Finite (ZMod p) V] (ρ : X →* (V →ₗ[ZMod p] V)),
        (∃ x, ρ x ≠ 1) → ∃ t : X, ρ t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
          3 ≤ Module.finrank (ZMod p) (LinearMap.ker (ρ t - 1))) :
    ∃ (p : ℕ) (_ : Fact p.Prime), 5 ≤ p ∧ ∃ t : X, t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
      ∃ (EΘ : Subgroup (H ⧸ CFSG.pCore 2 H)) (r : ℕ), 3 ≤ r ∧ Nat.card EΘ = p ^ r ∧
        (∀ u ∈ EΘ, ∀ v ∈ EΘ, u * v = v * u) ∧ (∀ u ∈ EΘ, u ^ p = 1) ∧
        ∀ w ∈ EΘ, twoQuotAction hXH t w = w := by
  obtain ⟨p, hp, x₀, z, hz, hxz⟩ := exists_pCore_moved hXH hnot
  have : Fact p.Prime := ⟨hp⟩
  set ρ₁ := twoQuotAction hXH with hρ₁
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hxz (map_one _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, Subgroup.mem_bot] at hz
    exact hz1 hz
  have hp3 : p ≠ 3 := by
    rintro rfl
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 3) (G := H ⧸ CFSG.pCore 2 H)) ⟨z, hz⟩
    have hzn : z ^ 3 ^ n = 1 := by
      have := congrArg Subtype.val hn
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hzn)
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hz1 hj
    have h3' : 3 ∣ Nat.card (H ⧸ CFSG.pCore 2 H) := by
      have := orderOf_dvd_natCard z
      rw [hj] at this
      exact (dvd_pow_self 3 hj0).trans this
    exact h3 (h3'.trans (Subgroup.card_quotient_dvd_card _))
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by decide)
    omega
  set P := CFSG.pCore p (H ⧸ CFSG.pCore 2 H) with hP
  have hPp : IsPGroup p P := CFSG.pCore_isPGroup
  set ρ₂ : X →* MulAut P := (Sec3.restrictCharacteristic P).comp ρ₁ with hρ₂
  have hρ₂1 : ∃ x, ρ₂ x ≠ 1 := by
    refine ⟨x₀, fun h1 => hxz ?_⟩
    have := congrArg (fun φ : MulAut P => ((φ ⟨z, hz⟩ : P) : H ⧸ CFSG.pCore 2 H)) h1
    simpa [hρ₂, Sec3.restrictCharacteristic_apply_coe] using this
  obtain ⟨D, hDchar, hDp, hDexp, hDclass, hel, xD, hxD⟩ :=
    exists_critical_rep_ne_one hp2 hPp ρ₂ hρ₂1
  set ρD : X →* MulAut D := (Sec3.restrictCharacteristic D).comp ρ₂ with hρD
  have : Module.Finite (ZMod p) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
  obtain ⟨t, hρt, ⟨k, htk⟩, hdim⟩ :=
    hfix p hp5 (Additive (D ⧸ frattini D)) (frattiniRep p ρD) ⟨xD, hxD⟩
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hρt (map_one _)
  have hrank := three_le_pRank_fixed hp2 hDp hDexp hDclass ρD htk hdim
  obtain ⟨E, hE, hEcard⟩ :=
    CFSG.RankThree.PartOne.exists_isElementaryAbelian_card_pRank (p := p) hp.one_lt
      (H := fixedSub (ρD t))
  let ι : fixedSub (ρD t) →* H ⧸ CFSG.pCore 2 H :=
    P.subtype.comp (D.subtype.comp (fixedSub (ρD t)).subtype)
  have hιinj : Function.Injective ι :=
    Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective)
  refine ⟨p, inferInstance, hp5, t, ht1, ⟨k, htk⟩, E.map ι, _, hrank, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hιinj, hEcard]
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hE.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  · rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian u hu, map_one]
  · rintro _ ⟨y, -, rfl⟩
    have hy : ρD t y.1 = y.1 := y.2
    have h1 := congrArg (fun u : D => ((u : P) : H ⧸ CFSG.pCore 2 H)) hy
    simpa [hρD, hρ₂, Sec3.restrictCharacteristic_apply_coe, ι] using h1

theorem exists_twoLocal_elemAbelian {C H X : Subgroup G} (hHC : H ≤ C)
    (hO : inSubgroup (CFSG.pCore 2) H ≤ inSubgroup (CFSG.pCore 2) C)
    (hXH : X ≤ Subgroup.normalizer (H : Set G)) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {t : X} (ht1 : t ≠ 1) {k : ℕ} (htk : t ^ 2 ^ k = 1) {EΘ : Subgroup (H ⧸ CFSG.pCore 2 H)}
    {r : ℕ} (hEΘcard : Nat.card EΘ = p ^ r) (hEΘcomm : ∀ u ∈ EΘ, ∀ v ∈ EΘ, u * v = v * u)
    (hEΘexp : ∀ u ∈ EΘ, u ^ p = 1) (hEΘfix : ∀ w ∈ EΘ, twoQuotAction hXH t w = w) :
    ∃ X₂ : Subgroup G, CFSG.Assembly.IsTwoLocal X₂ ∧ ∃ R' : Subgroup G, R' ≤ X₂ ∧
      CFSG.Assembly.IsElemAbelian p R' ∧ Nat.card R' = p ^ r := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  have hEΘp : IsPGroup p EΘ := IsPGroup.of_card hEΘcard
  have hker : p.Coprime (Nat.card π.ker) := by
    rw [hπ, QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
  obtain ⟨Rl, hRl, hRinj⟩ :=
    Sec4.exists_lift_pGroup π (QuotientGroup.mk'_surjective _) hker EΘ hEΘp
  have hRπ : ∀ x ∈ Rl, π x ∈ EΘ := fun x hx => hRl ▸ Subgroup.mem_map_of_mem π hx
  have hRcard : Nat.card Rl = p ^ r := by
    have h1 := Nat.card_congr (MonoidHom.ofInjective hRinj).toEquiv
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hRl, hEΘcard] at h1
    exact h1
  have hR'elem : CFSG.Assembly.IsElemAbelian p (Rl.map H.subtype) := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
      apply Subtype.ext
      have h1 : (π.comp Rl.subtype) (⟨x, hx⟩ * ⟨y, hy⟩) =
          (π.comp Rl.subtype) (⟨y, hy⟩ * ⟨x, hx⟩) := by
        simp only [map_mul, MonoidHom.comp_apply, Subgroup.coe_subtype]
        exact hEΘcomm _ (hRπ x hx) _ (hRπ y hy)
      have h2 := congrArg (fun w : Rl => ((w : H) : G)) (hRinj h1)
      simpa using h2
    · rintro _ ⟨x, hx, rfl⟩
      have h1 : (π.comp Rl.subtype) (⟨x, hx⟩ ^ p) = (π.comp Rl.subtype) 1 := by
        rw [map_pow, map_one]
        exact hEΘexp _ (hRπ x hx)
      have h2 := congrArg (fun w : Rl => ((w : H) : G)) (hRinj h1)
      simpa using h2
  have hR'card : Nat.card (Rl.map H.subtype) = p ^ r := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hRcard]
  by_cases hPc : inSubgroup (CFSG.pCore 2) C = ⊥
  ·
    have hO1 : CFSG.pCore 2 H = ⊥ := by
      rw [hPc, le_bot_iff] at hO
      exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hO
    have hπinj : Function.Injective π := by
      rw [← MonoidHom.ker_eq_bot_iff, hπ, QuotientGroup.ker_mk', hO1]
    have hRt : Rl.map H.subtype ≤ Subgroup.centralizer ({(t : G)} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 := hEΘfix _ (hRπ x hx)
      rw [hπ, QuotientGroup.mk'_apply, twoQuotAction_mk] at h1
      have h3 : (t : G) * x * (t : G)⁻¹ = x := congrArg Subtype.val (hπinj h1)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ((H.subtype x : G)) * t = (t : G) * x * (t : G)⁻¹ * t := by rw [h3]; rfl
        _ = t * x := by group
    have ht1' : (t : G) ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
    have htk' : (t : G) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val htk
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    refine ⟨Subgroup.normalizer (Subgroup.zpowers (t : G) : Set G), ⟨_, ?_,
      isPGroup_zpowers_of_pow htk', rfl⟩, _, hRt.trans (centralizer_le_normalizer_zpowers _),
      hR'elem, hR'card⟩
    intro h1
    apply ht1'
    have : (t : G) ∈ Subgroup.zpowers (t : G) := Subgroup.mem_zpowers _
    rwa [h1, Subgroup.mem_bot] at this
  ·
    exact ⟨Subgroup.normalizer (inSubgroup (CFSG.pCore 2) C : Set G),
      ⟨_, hPc, SteinbergBY.isPGroup_inSubgroup_pCore 2 C, rfl⟩, _,
      (Subgroup.map_subtype_le Rl).trans (hHC.trans
        (SteinbergBY.le_normalizer_inSubgroup_pCore 2 C)), hR'elem, hR'card⟩

end TwoStarProof

section Certified


open TwoStarProof in
theorem lfAtC_of (hC2 : LandazuriSeitzL2EvenSolvable) : LFAtC := by
  intro G _ _ A c L a R Y d h hT m hm hL2
  obtain ⟨e⟩ := hL2
  have hm2 : 2 ≤ m := hm
  have hLC := le_centralizer_of_config h
  have hCH : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) : Set G) :=
    Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta _)
  have hLH := hLC.trans hCH
  have : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have := Sec4.aschbacherSolvableCore_characteristic L
  have hfix : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (V : Type) [AddCommGroup V]
      [Module (ZMod p) V] [Module.Finite (ZMod p) V] (ρ : L →* (V →ₗ[ZMod p] V)),
        (∃ x, ρ x ≠ 1) → ∃ t : L, ρ t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
          3 ≤ Module.finrank (ZMod p) (LinearMap.ker (ρ t - 1)) := by
    intro p _ hp5 V _ _ _ ρ hρ
    by_cases hθ : aschbacherSolvableCore 3 L ≤ ρ.ker
    · exact exists_two_element_fixed_of_LS hm2 e (by omega) ρ hθ hρ
    · have hθs : Group.IsSolvable (aschbacherSolvableCore 3 L) :=
        (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).1
      have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
        (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
      exact hC2 (3 * m) (by omega) p hp5 L inferInstance (aschbacherSolvableCore 3 L) hθs hθ3
        ⟨e⟩ V ρ hθ
  by_contra hnot
  obtain ⟨p, _, hp5, t, ht1, ⟨k, htk⟩, EΘ, r, hr, hEcard, hEcomm, hEexp, hEfix⟩ :=
    exists_fixed_elemAbelian hLH (not_three_dvd_card_inSubgroup_theta _) hnot hfix
  obtain ⟨X₂, hX₂, R', hR'X₂, hR'e, hR'card⟩ := exists_twoLocal_elemAbelian (Sec6.theta_le _)
    (pCore_theta_le_pCore _) hLH (by omega) ht1 htk hEcard hEcomm hEexp hEfix
  have h1 := Sec5.le_pRank_of_elemAbelian (Fact.out : p.Prime) hR'X₂ hR'e hR'card
  have h2 := CFSG.RankThree.Classical.pRank_le_localRank (Fact.out : p.Prime).one_lt hX₂
  have h3 := h.localRank_lt p Fact.out (by omega)
  omega

open TwoStarProof in
theorem twoStarAtC_of (h45 : Sec4.Item4_5) (hC2 : LandazuriSeitzL2EvenSolvable) : TwoStarAtC :=
  twoStarAtC_of_lf h45 (lfAtC_of hC2)

end Certified

end CFSG.RankThree.PartTwo.Sec11
