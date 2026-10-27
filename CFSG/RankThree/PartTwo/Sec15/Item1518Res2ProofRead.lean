module

public import CFSG.RankThree.PartTwo.Sec15.Item1518Res2ProofGen
import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofTools
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofArith
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec15.Item15Type

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def KS1518InvRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e →
    Sec4.IsoLThreePi X p e →
    ∃ t : X, orderOf t = 2 ∧ ∃ E : Subgroup X, E ≤ Subgroup.centralizer {t} ∧
      CFSG.Assembly.IsElemAbelian p E ∧ Nat.card E = p ^ e

@[expose] def KS1518PRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ) [Fact p.Prime], p ≠ 2 → 2 ≤ f →
    IsLThreeEpsAt X p f → ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian p E ∧ Nat.card E = p ^ 3

@[expose] def KS1518TwoLoc : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], p ≠ 2 → Sec4.IsoLThreePi X p 2 →
    ∀ N : Subgroup X, N ≠ ⊥ → IsPGroup 2 ↥N →
      ¬ p ^ 3 ∣ Nat.card (Subgroup.normalizer (N : Set X))

namespace Proof1518R2

theorem gcd_three_eq_one {x : ℕ} (h : x % 3 ≠ 0) : Nat.gcd 3 x = 1 := by
  rw [Nat.gcd_rec]
  have hx : x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases hx with h1 | h2
  · rw [h1]
    rfl
  · rw [h2]
    rfl

theorem gcd_three_eq_three {x : ℕ} (h : x % 3 = 0) : Nat.gcd 3 x = 3 :=
  Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero h)

theorem pow_three_dvd_card_of_isLThreeEpsAt_one {Z : Type} [Group Z] {p : ℕ} [Fact p.Prime]
    (hp3 : p ≠ 3) (hZ : IsLThreeEpsAt Z p 1) : p ^ 3 ∣ Nat.card Z := by
  have hp : p.Prime := Fact.out
  have hcop3 : Nat.Coprime (p ^ 3) 3 :=
    Nat.Coprime.pow_left 3 ((Nat.coprime_primes hp Nat.prime_three).mpr hp3)
  rcases hZ with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · rw [Nat.card_congr φ.toEquiv]
    have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p 1)
    rw [GaloisField.card p 1 (by norm_num), pow_one] at h
    have hd : p ^ 3 ∣ Nat.card ↥(projSL 3 (GaloisField p 1)) * Nat.gcd 3 (p - 1) :=
      h ▸ Dvd.intro _ rfl
    exact (hcop3.coprime_dvd_right (Nat.gcd_dvd_left 3 (p - 1))).dvd_of_dvd_mul_right hd
  · rw [Nat.card_congr φ.toEquiv]
    have h := KFacts.KS14.card_projSU_three_mul_gcd p 1 le_rfl
    rw [pow_one] at h
    have hd : p ^ 3 ∣ Nat.card ↥(projSU 3 p 1) * Nat.gcd 3 (p + 1) := h ▸ Dvd.intro _ rfl
    exact (hcop3.coprime_dvd_right (Nat.gcd_dvd_left 3 (p + 1))).dvd_of_dvd_mul_right hd

theorem mul_su_le_three_mul_sl {P x : ℕ} (hx : 2 ≤ x) :
    P * (x ^ 3 + 1) ≤ 3 * (P * (x ^ 3 - 1)) := by
  have h8 : 8 ≤ x ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
  have h : x ^ 3 + 1 ≤ 3 * (x ^ 3 - 1) := by omega
  calc P * (x ^ 3 + 1) ≤ P * (3 * (x ^ 3 - 1)) := Nat.mul_le_mul_left P h
    _ = 3 * (P * (x ^ 3 - 1)) := by ring

theorem mul_sl_le_mul_su (P x : ℕ) : P * (x ^ 3 - 1) ≤ P * (x ^ 3 + 1) :=
  Nat.mul_le_mul_left P (by omega)

theorem card_le_of_isLThreeEpsAt_one {X Z : Type} [Group X] [Group Z] {p : ℕ} [Fact p.Prime]
    (hp3 : 3 < p) (hX : Sec4.IsoLThreePi X p 1) (hZ : IsLThreeEpsAt Z p 1) :
    Nat.card X ≤ Nat.card Z := by
  have hSL := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p 1)
  rw [GaloisField.card p 1 (by norm_num), pow_one] at hSL
  have hSU := KFacts.KS14.card_projSU_three_mul_gcd p 1 le_rfl
  rw [pow_one] at hSU
  set a := Nat.card ↥(projSL 3 (GaloisField p 1)) with ha
  set b := Nat.card ↥(projSU 3 p 1) with hb
  set P := p ^ 3 * (p ^ 2 - 1) with hP
  have hSL' : a * Nat.gcd 3 (p - 1) = P * (p ^ 3 - 1) := by rw [hSL, hP, mul_assoc]
  have hSU' : b * Nat.gcd 3 (p + 1) = P * (p ^ 3 + 1) := by rw [hSU, hP, mul_assoc]
  rcases hX with ⟨hX1, ⟨φ⟩⟩ | ⟨hX2, ⟨φ⟩⟩
  · rcases hZ with ⟨⟨ψ⟩⟩ | ⟨-, ⟨ψ⟩⟩
    ·
      rw [Nat.card_congr φ.toEquiv, Nat.card_congr ψ.toEquiv]
    ·
      rw [Nat.card_congr φ.toEquiv, Nat.card_congr ψ.toEquiv]
      rw [pow_one] at hX1
      rw [gcd_three_eq_three (by omega)] at hSL'
      rw [gcd_three_eq_one (by omega), mul_one] at hSU'
      have h1 := mul_sl_le_mul_su P p
      rw [← hSL', ← hSU'] at h1
      omega
  · rcases hZ with ⟨⟨ψ⟩⟩ | ⟨-, ⟨ψ⟩⟩
    ·
      rw [Nat.card_congr φ.toEquiv, Nat.card_congr ψ.toEquiv]
      rw [pow_one] at hX2
      rw [gcd_three_eq_one (by omega), mul_one] at hSL'
      rw [gcd_three_eq_three (by omega)] at hSU'
      have h1 := mul_su_le_three_mul_sl (P := P) (by omega : 2 ≤ p)
      rw [← hSL', ← hSU'] at h1
      omega
    ·
      rw [Nat.card_congr φ.toEquiv, Nat.card_congr ψ.toEquiv]

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCore_iff' {Y : Subgroup G} {y : ↥Y} :
    y ∈ CFSG.pCore 2 ↥Y ↔ (y : G) ∈ CFSG.Open.pCoreOf 2 Y := (CFSG.mem_openPCoreOf_iff y).symm

theorem two_dvd_and_coprime_of_isPGroup_two {H : Subgroup G} (hH : IsPGroup 2 ↥H) (h1 : H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : 2 ∣ Nat.card ↥H ∧ Nat.Coprime p (Nat.card ↥H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH
  refine ⟨?_, ?_⟩
  · have hk0 : k ≠ 0 := by
      rintro rfl
      exact h1 ((Subgroup.card_eq_one).mp (by rw [hk, pow_zero]))
    rw [hk]
    exact dvd_pow_self 2 hk0
  · rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)

omit [Finite G] in
theorem surjective_inf_toQuot {L Y : Subgroup G}
    (hYL : Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y) :
    Function.Surjective ((QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp
      (Subgroup.inclusion (inf_le_right : L ⊓ Y ≤ Y))) := by
  intro z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ z
  have hy : (y : G) ∈ ((((L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G)) : Set G) := by
    rw [← hYL]
    exact y.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))] at hy
  obtain ⟨j, hj, q, hq, hjq⟩ := hy
  refine ⟨⟨j, hj⟩, ?_⟩
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq, mem_pCore_iff']
  have hval : (((Subgroup.inclusion (inf_le_right : L ⊓ Y ≤ Y) ⟨j, hj⟩)⁻¹ * y : ↥Y) : G) = q := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    rw [← hjq]
    group
  rw [hval]
  exact hq

end Proof1518R2

open Proof1518R2

theorem step1518Read_of (hK2 : KS1518InvRank) (hK3 : KS1518PRank) (hK4 : KS1518TwoLoc) :
    Step1518Read := by
  intro G _ _ A c L h Y hctx hno hs p e _ he hiso hp2
  have hpp : p.Prime := Fact.out
  obtain ⟨p₀, e₀, hp₀, he₀, hiso₀, -, hYL, ⟨n, f, hf, he₀nf, hYbar⟩, -⟩ := hctx.concl1515
  have hq : p ^ e = p₀ ^ e₀ := Sec19.Step1917EqProof.eq_of_isoLThreePi he he₀ hiso hiso₀
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  obtain ⟨e₀', rfl⟩ : ∃ e', e₀ = e' + 1 := ⟨e₀ - 1, by omega⟩
  obtain ⟨hpp₀, hee⟩ := Nat.Prime.pow_inj hpp hp₀.out hq
  subst hpp₀ hee
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h3 : 3 ^ (e' + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
    rcases hiso with ⟨h1, -⟩ | ⟨h2, -⟩ <;> omega
  have hp3' : 3 < p := by
    have := hpp.two_le
    omega
  have hlt := h.toTheoremFourHyp.localRank_lt p hpp hp3'
  have hθ := Proof1520.theta_eq_bot_of_isSimpleGroup h.mem_thetaComponentsAt hs
  have hisoL : Sec4.IsoLThreePi ↥L p (e' + 1) := Proof1520.isoLThreePi_of_theta_eq_bot hθ hiso
  have he2 : e' + 1 ≤ 2 := by
    obtain ⟨t, ht, E, hEt, hE, hEcard⟩ := hK2 ↥L p (e' + 1) hp2 (by omega) hisoL
    have hSD : E.map L.subtype ≤ Subgroup.normalizer (Subgroup.zpowers (t : G) : Set G) := by
      refine le_trans ?_ (centralizer_singleton_le_normalizer_zpowers (t : G))
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hEt hx))
    have hS : CFSG.Assembly.IsElemAbelian p (E.map L.subtype) :=
      let h' := CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map p L.subtype E
        ⟨hE.1, hE.2⟩
      ⟨h'.1, h'.2⟩
    have hScard : Nat.card ↥(E.map L.subtype) = p ^ (e' + 1) := by
      rw [Subgroup.card_map_of_injective L.subtype_injective, hEcard]
    have hD : Nat.card (Subgroup.zpowers (t : G)) = 2 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht]
    have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers (t : G))) := by
      rw [hD]
      exact (Nat.coprime_primes hpp Nat.prime_two).mpr hp2
    have hk := CFSG.RankThree.Classical2.le_localRank_of_normalizes hpp hSD hS hScard hcop
      (by rw [hD])
    omega
  have hY2 : Y ∈ scriptY2 A := hctx.mem_y0Star.prop.2
  have hQ2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 Y) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  obtain ⟨hQeven, hQcop⟩ := two_dvd_and_coprime_of_isPGroup_two hQ2 hY2.2 hpp hp2
  have hf1 : f = 1 := by
    by_contra hf1
    obtain ⟨Eb, hEb, hEbcard⟩ := hK3 _ p f hp2 (by omega) hYbar
    have hN : ¬ p ∣ Nat.card ↥(CFSG.pCore 2 ↥Y) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥Y))
      rw [hk]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hd))
    obtain ⟨S, -, hS, hScard⟩ :=
      CFSG.RankThree.Classical2.exists_elemAbelian_lift (CFSG.pCore 2 ↥Y) hN hEb
    have hSD : S.map Y.subtype ≤
        Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
      (Subgroup.map_subtype_le S).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
    have hS' : CFSG.Assembly.IsElemAbelian p (S.map Y.subtype) :=
      let h' := CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map p Y.subtype S
        ⟨hS.1, hS.2⟩
      ⟨h'.1, h'.2⟩
    have hS'card : Nat.card ↥(S.map Y.subtype) = p ^ 3 := by
      rw [Subgroup.card_map_of_injective Y.subtype_injective, hScard, hEbcard]
    have hk := CFSG.RankThree.Classical2.le_localRank_of_normalizes hpp hSD hS' hS'card hQcop
      hQeven
    omega
  subst hf1
  set φ := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp
    (Subgroup.inclusion (inf_le_right : L ⊓ Y ≤ Y)) with hφ
  have hYL' : Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y := hYL
  have hφs : Function.Surjective φ := surjective_inf_toQuot hYL'
  have hdvdJ : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ∣ Nat.card ↥(L ⊓ Y) :=
    Subgroup.card_dvd_of_surjective hφs
  have hJpos : 0 < Nat.card ↥(L ⊓ Y) := Nat.card_pos
  have he1 : e' + 1 ≠ 1 := by
    intro he1
    rw [he1] at hisoL
    have h1 := card_le_of_isLThreeEpsAt_one hp3' hisoL hYbar
    have h2 := Nat.le_of_dvd hJpos hdvdJ
    have hLY : L ⊓ Y = L := Subgroup.eq_of_le_of_card_ge inf_le_left (h1.trans h2)
    exact hno Y hY2 (hLY ▸ inf_le_right)
  have he' : e' + 1 = 2 := by omega
  rw [he'] at hisoL
  refine ⟨he', ?_⟩
  have hp3J : p ^ 3 ∣ Nat.card ↥(L ⊓ Y) :=
    (pow_three_dvd_card_of_isLThreeEpsAt_one hp3 hYbar).trans hdvdJ
  have hLQ : L ⊓ CFSG.Open.pCoreOf 2 Y = ⊥ := by
    by_contra hne
    set N := (L ⊓ CFSG.Open.pCoreOf 2 Y).subgroupOf L with hNdef
    have hN1 : N ≠ ⊥ := by
      intro h0
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, (Subgroup.mem_inf.mp hx).1⟩ : ↥L) ∈ N := Subgroup.mem_subgroupOf.mpr hx
      rw [h0, Subgroup.mem_bot] at hx'
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
    have hN2 : IsPGroup 2 ↥N :=
      (hQ2.to_le inf_le_right).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
    have hJN : (L ⊓ Y).subgroupOf L ≤ Subgroup.normalizer (N : Set ↥L) := by
      intro x hx
      have hxY : (x : G) ∈ Y := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
      have hxQ := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y hxY
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [hNdef, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        Subgroup.mem_inf]
      have hyL : (y : G) ∈ L := y.2
      have hxyL : ((x * y * x⁻¹ : ↥L) : G) ∈ L := (x * y * x⁻¹).2
      simp only [hyL, hxyL, true_and]
      simpa using Subgroup.mem_normalizer_iff.mp hxQ (y : G)
    have hcardJ : Nat.card ↥((L ⊓ Y).subgroupOf L) = Nat.card ↥(L ⊓ Y) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hdvd : p ^ 3 ∣ Nat.card (Subgroup.normalizer (N : Set ↥L)) :=
      (hcardJ ▸ hp3J).trans (Subgroup.card_dvd_of_le hJN)
    exact hK4 ↥L p hp2 hisoL N hN1 hN2 hdvd
  have hφi : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_pCore_iff'] at hx
    have hxL : (x : G) ∈ L ⊓ CFSG.Open.pCoreOf 2 Y :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp x.2).1, hx⟩
    rw [hLQ, Subgroup.mem_bot] at hxL
    exact Subtype.ext hxL
  exact IsLThreeEpsAt.of_mulEquiv (MulEquiv.ofBijective φ ⟨hφi, hφs⟩).symm hYbar

end CFSG.RankThree.PartTwo.Sec15
