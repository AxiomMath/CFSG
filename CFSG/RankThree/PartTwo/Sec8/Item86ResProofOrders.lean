module

public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofBridge
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.Timmesfeld.Orders.Distinct
import all CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Timmesfeld.Orders CFSG.Open
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem profile_congr {m N N' : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) (hN : N = N') :
    Profile m N' Z :=
  hN ▸ h

theorem profile_of_eq {m m' N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) (hm : m' = m) :
    Profile m' N Z :=
  hm ▸ h

theorem false_of_dvd_of_lt {k b : ℕ} (h : k ∣ b) (hb : 0 < b) (hk : b < k) : False :=
  absurd (Nat.le_of_dvd hb h) (by omega)

theorem profile_card_SU3 {g : ℕ} (hg : 1 ≤ g) :
    Profile ((2 ^ g) ^ 3 * ((2 ^ g) ^ 2 - 1) * ((2 ^ g) ^ 3 + 1)) (3 * g) (zU 2 g) := by
  have h1 : Odd ((2 ^ g) ^ 2 - 1) := odd_pow_sub_one hg (by norm_num)
  have h2 : Odd ((2 ^ g) ^ 3 + 1) := odd_pow_add_one hg (by norm_num)
  refine Profile.of_eq (r := ((2 ^ g) ^ 2 - 1) * ((2 ^ g) ^ 3 + 1))
    (by rw [mul_comm 3 g, pow_mul]; ring) (h1.mul h2) (fun p k hp hk => ?_)
  rw [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk, PrimDiv.dvd_pow_add_one_iff hp hk]
  constructor
  · rintro (h | h)
    · exact ⟨2, by simp, Or.inl ⟨even_two, h⟩⟩
    · exact ⟨3, by simp, Or.inr ⟨by decide, h⟩⟩
  · rintro ⟨i, hi, ⟨he, h⟩ | ⟨ho, h⟩⟩
    · simp only [Finset.mem_Icc] at hi
      obtain rfl : i = 2 := by
        rcases (show i = 2 ∨ i = 3 by omega) with rfl | rfl
        · rfl
        · exact absurd he (by decide)
      exact Or.inl h
    · simp only [Finset.mem_Icc] at hi
      obtain rfl : i = 3 := by
        rcases (show i = 2 ∨ i = 3 by omega) with rfl | rfl
        · exact absurd ho (by decide)
        · rfl
      exact Or.inr h

structure SigD4 (X : Type) [Group X] (p : ℕ) : Prop where
  profile : Profile (Nat.card X) (12 * p) (zD4 p)
  le : ∀ k, zD4 p k → k ≤ 12 * p
  not_four : ¬ zD4 p (4 * p)

structure SigG2 (X : Type) [Group X] (p : ℕ) : Prop where
  card : Nat.card X = ordG2 (2 ^ (3 * p))
  profile : Profile (Nat.card X) (18 * p) (zG2 (3 * p))
  le : ∀ k, zG2 (3 * p) k → k ≤ 18 * p
  six : zG2 (3 * p) (6 * p)
  nine : ∀ t, p = 2 * t → zG2 (3 * p) (9 * t)

structure SigF4 (X : Type) [Group X] (p : ℕ) : Prop where
  profile : Profile (Nat.card X) (36 * p) (z2F4 (3 * p))
  le : ∀ k, z2F4 (3 * p) k → k ≤ 36 * p
  twelve : z2F4 (3 * p) (12 * p)
  not_nine : ¬ z2F4 (3 * p) (9 * p)

structure SigU (X : Type) [Group X] (p : ℕ) : Prop where
  profile : Profile (Nat.card X) (9 * p) (zU 2 (3 * p))
  eighteen : zU 2 (3 * p) (18 * p)

structure SigSp4 (X : Type) [Group X] (p : ℕ) : Prop where
  card : Nat.card X = ordBC 2 (2 ^ (3 * p))
  profile : Profile (Nat.card X) (12 * p) (zBC 2 (3 * p))
  le : ∀ k, zBC 2 (3 * p) k → k ≤ 12 * p
  three : zBC 2 (3 * p) (3 * p)
  four : zBC 2 (3 * p) (4 * p)

structure UnitarySig (X : Type) [Group X] (g : ℕ) : Prop where
  profile : Profile (Nat.card X) (3 * g) (zU 2 g)
  top : zU 2 g (6 * g)

section Data

variable {X : Type} [Group X]

theorem zU_two_six {g : ℕ} (hg : 1 ≤ g) : zU 2 g (6 * g) := by
  have h := zU_top (n := 2) (g := g) (t := 1) (Or.inl rfl) le_rfl (by omega)
  rwa [show 2 * (g * (2 * 1 + 1)) = 6 * g by ring] at h

theorem unitarySig_of_projSU {g : ℕ} (hg : 1 ≤ g) (e : X ≃* projSU 3 2 g) : UnitarySig X g where
  profile := by
    refine profile_of_eq (profile_congr (profile_ordTwistedA (n := 2) le_rfl hg) (by ring)) ?_
    rw [Nat.card_congr e.toEquiv]
    exact KFacts.card_projSU_three_two hg
  top := zU_two_six hg

theorem unitarySig_of_isoSUThree {g : ℕ} (hg : 1 ≤ g) (h : IsoSUThree X (2 ^ g)) :
    UnitarySig X g where
  profile := by
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
    have hU : UnitaryFieldData 2 g K := ⟨Nat.prime_two, hg, by rw [hK, ← pow_mul, mul_comm]⟩
    refine profile_of_eq (profile_card_SU3 hg) ?_
    rw [Nat.card_congr e.toEquiv]
    exact KFacts.card_unitarySU_three hU
  top := zU_two_six hg

theorem sigU_of_unitarySig {p : ℕ} (h : UnitarySig X (3 * p)) : SigU X p where
  profile := profile_congr h.profile (by ring)
  eighteen := by
    have := h.top
    rwa [show 6 * (3 * p) = 18 * p by ring] at this

theorem sigD4_of_isoTrialityD4
    {p : ℕ} (hp : 1 ≤ p) (h : IsoTrialityD4 X p) : SigD4 X p where
  profile := by
    obtain ⟨q, hv, hq2, hqe, ⟨e⟩⟩ := h
    refine profile_of_eq (profile_congr (profile_ordTrialityD4 hp) (by ring)) ?_
    rw [Nat.card_congr e.toEquiv, Sec11.KSListsProof.card_trialityD4_carrier,
      TauCeti.PrimePower.card_def, hq2, hqe]
  le := fun k hk => (zD4_le (by omega) hk).trans (by omega)
  not_four := by
    rintro (⟨-, h⟩ | h | h)
    · exact h ⟨1, by ring⟩
    · rw [mul_comm p 6] at h
      exact false_of_dvd_of_lt (Nat.dvd_sub h (dvd_refl (4 * p))) (by omega) (by omega)
    · rw [mul_comm p 2] at h
      exact false_of_dvd_of_lt h (by omega) (by omega)

theorem sigG2_of_isoGTwo
    {p : ℕ} (hp : 1 ≤ p)
    (h : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 * p ∧ Sec4.IsoGTwo X q) :
    SigG2 X p := by
  obtain ⟨q, hq2, hqe, hv, ⟨e⟩⟩ := h
  have hcard : Nat.card X = ordG2 (2 ^ (3 * p)) := by
    rw [Nat.card_congr e.toEquiv, Sec11.KSListsProof.card_G2_carrier,
      TauCeti.PrimePower.card_def, hq2, hqe]
  have hL : ∀ a ∈ [6, 2], 0 < a ∧ a ≤ 6 := by simp
  refine ⟨hcard, profile_of_eq (profile_congr (profile_ordG2 (by omega)) (by ring)) hcard,
    fun k hk => (zList_le (by omega) hL hk).trans (by omega), ⟨6, by simp, ⟨3, by ring⟩⟩,
    fun t ht => ⟨6, by simp, ⟨4, by rw [ht]; ring⟩⟩⟩

theorem sigSp4_of_projSp {p : ℕ} (hp : 1 ≤ p) (e : X ≃* projSp 2 (GaloisField 2 (3 * p))) :
    SigSp4 X p := by
  have hcard : Nat.card X = ordBC 2 (2 ^ (3 * p)) := by
    rw [Nat.card_congr e.toEquiv, Sec19.Step1911Proof.card_projSp_two (by omega),
      ordBC_two_eq (by omega)]
  refine ⟨hcard, profile_of_eq (profile_congr (profile_ordBC (n := 2) (by omega)) (by ring))
    hcard, fun k hk => (zBC_le (by omega) hk).trans (by omega), zBC_two_iff.mpr ⟨4, by ring⟩,
    zBC_two_iff.mpr ⟨3, by ring⟩⟩

theorem ordTwistedF4_eq_factored' {q : ℕ} (hq : 2 ≤ q) :
    ordTwistedF4 q = q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
      (q ^ 4 - q ^ 2 + 1) := by
  have h1 : 1 ≤ q := by omega
  have h2 : q ≤ q ^ 2 := by nlinarith
  have h3 : q ^ 2 ≤ q ^ 4 := by nlinarith [Nat.mul_le_mul h2 h2]
  have h4 : 1 ≤ q ^ 4 := by nlinarith
  unfold ordTwistedF4
  zify [h1, h2, h3, h4]
  ring

theorem card_of_mulEquiv_reeGamma
    (a : ℕ) (K : Type) [Field K]
    [Finite K] [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) :
    Nat.card X = ordTwistedF4 (2 ^ (2 * a + 1)) := by
  rw [Nat.card_congr e.toEquiv,
    (LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).1,
    ordTwistedF4_eq_factored' (by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))]

theorem sigF4_of_reeF4 {p : ℕ} (hp : 1 ≤ p)
    (h : ∃ (k : ℕ) (hk : (TauCeti.LieTypeIndex.reeF4 k).Valid), 2 * k + 1 = 3 * p ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 k, hk⟩).Group)) :
    SigF4 X p := by
  obtain ⟨k, hk, hkp, ⟨e₀⟩⟩ := h
  have hRT : CFSG.Blueprint.ReeTitsModel X .twistedF4 2 (2 * k + 1) :=
    CFSG.SectionRank.reeTitsModel_of_mulEquiv e₀ (Sec4.Census.bridgeExceptional46.reeF4 k hk)
  obtain ⟨-, a, -, hka, K, _, _, _, hK, ⟨e⟩⟩ := Sec4.exists_mulEquiv_reeGamma hRT
  have hcard : Nat.card X = ordTwistedF4 (2 ^ (3 * p)) := by
    rw [card_of_mulEquiv_reeGamma a K hK e, ← hka, hkp]
  refine ⟨profile_of_eq (profile_congr (profile_ordTwistedF4 (by omega)) (by ring)) hcard,
    fun k hk => (z2F4_le (by omega) hk).trans (by omega), Or.inr (Or.inl ⟨1, by ring⟩), ?_⟩
  rintro (⟨-, h⟩ | h | ⟨-, h⟩ | h)
  · exact h ⟨2, by ring⟩
  · rw [show 3 * p * 4 = 12 * p by ring] at h
    exact false_of_dvd_of_lt (Nat.dvd_sub h (dvd_refl (9 * p))) (by omega) (by omega)
  · exact h ⟨1, by ring⟩
  · exact false_of_dvd_of_lt h (by omega) (by omega)

theorem sig_of_isGammaType {p : ℕ} (hp : 1 ≤ p) (h : IsGammaType X p) :
    SigF4 X p ∨ SigD4 X p ∨ SigG2 X p ∨ SigU X p ∨ SigSp4 X p := by
  rcases h with hF | hD | hG | hU | hS | hSp
  · exact Or.inl (sigF4_of_reeF4 hp hF)
  · exact Or.inr (Or.inl (sigD4_of_isoTrialityD4 hp hD))
  · exact Or.inr (Or.inr (Or.inl (sigG2_of_isoGTwo hp hG)))
  · obtain ⟨e⟩ := hU
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (sigU_of_unitarySig (unitarySig_of_projSU (by omega) e)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (sigU_of_unitarySig (unitarySig_of_isoSUThree (by omega) hS)))))
  · obtain ⟨e⟩ := hSp
    exact Or.inr (Or.inr (Or.inr (Or.inr (sigSp4_of_projSp hp e))))

end Data

section Compare

variable {X : Type} [Group X] {m n : ℕ}

omit [Group X] in
theorem two_eq {N N' : ℕ} {Z Z' : ℕ → Prop} (h : Profile (Nat.card X) N Z)
    (h' : Profile (Nat.card X) N' Z') : N = N' :=
  (h.transfer h').1

omit [Group X] in
theorem z_iff {N N' : ℕ} {Z Z' : ℕ → Prop} (h : Profile (Nat.card X) N Z)
    (h' : Profile (Nat.card X) N' Z') {k : ℕ} (hk : 2 ≤ k) (hk6 : k ≠ 6) : Z k ↔ Z' k :=
  (h.transfer h').2 k hk hk6

theorem SigF4.false_of_sigD4 (hF : SigF4 X n) (hD : SigD4 X m) (hn : 1 ≤ n) : False := by
  have hN := two_eq hF.profile hD.profile
  have h := (z_iff hF.profile hD.profile (k := 12 * n) (by omega) (by omega)).mp hF.twelve
  exact hD.not_four (by rwa [show 4 * m = 12 * n by omega])

theorem SigF4.false_of_sigG2 (hF : SigF4 X n) (hG : SigG2 X m) (hn : 1 ≤ n) : False := by
  have hN := two_eq hF.profile hG.profile
  have h := (z_iff hG.profile hF.profile (k := 9 * n) (by omega) (by omega)).mp
    (hG.nine n (by omega))
  exact hF.not_nine h

theorem SigF4.false_of_sigU (hF : SigF4 X n) (hU : SigU X m) (hn : 1 ≤ n) : False := by
  have hN := two_eq hF.profile hU.profile
  have h := (z_iff hU.profile hF.profile (k := 18 * m) (by omega) (by omega)).mp hU.eighteen
  have := hF.le _ h
  omega

theorem SigF4.false_of_sigSp4 (hF : SigF4 X n) (hS : SigSp4 X m) (hn : 1 ≤ n) : False := by
  have hN := two_eq hF.profile hS.profile
  have h := (z_iff hS.profile hF.profile (k := 3 * m) (by omega) (by omega)).mp hS.three
  exact hF.not_nine (by rwa [show 3 * m = 9 * n by omega] at h)

theorem SigD4.false_of_sigG2 (hD : SigD4 X n) (hG : SigG2 X m) (hn : 1 ≤ n) : False := by
  have hN := two_eq hD.profile hG.profile
  have h := (z_iff hG.profile hD.profile (k := 6 * m) (by omega) (by omega)).mp hG.six
  exact hD.not_four (by rwa [show 6 * m = 4 * n by omega] at h)

theorem SigD4.false_of_sigU (hD : SigD4 X n) (hU : SigU X m) (hn : 1 ≤ n) : False := by
  have hN := two_eq hD.profile hU.profile
  have h := (z_iff hU.profile hD.profile (k := 18 * m) (by omega) (by omega)).mp hU.eighteen
  have := hD.le _ h
  omega

theorem SigD4.false_of_sigSp4 (hD : SigD4 X n) (hS : SigSp4 X m) (hn : 1 ≤ n) : False := by
  have hN := two_eq hD.profile hS.profile
  have h := (z_iff hS.profile hD.profile (k := 4 * m) (by omega) (by omega)).mp hS.four
  exact hD.not_four (by rwa [show 4 * m = 4 * n by omega] at h)

theorem SigG2.false_of_sigU (hG : SigG2 X n) (hU : SigU X m) (hn : 1 ≤ n) : False := by
  have hN := two_eq hG.profile hU.profile
  have h := (z_iff hU.profile hG.profile (k := 18 * m) (by omega) (by omega)).mp hU.eighteen
  have := hG.le _ h
  omega

theorem SigG2.false_of_sigSp4 (hG : SigG2 X n) (hS : SigSp4 X m) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    False :=
  ordG2_ne_ordBC_two (f := 3 * n) (g := 3 * m) (by omega) (by omega) (hG.card.symm.trans hS.card)

theorem SigU.false_of_sigSp4 (hU : SigU X n) (hS : SigSp4 X m) (hn : 1 ≤ n) : False := by
  have hN := two_eq hU.profile hS.profile
  have h := (z_iff hU.profile hS.profile (k := 18 * n) (by omega) (by omega)).mp hU.eighteen
  have := hS.le _ h
  omega

theorem eq_of_isGammaType
    (hm : 1 ≤ m) (hn : 1 ≤ n) (h₁ : IsGammaType X m)
    (h₂ : IsGammaType X n) : m = n := by
  rcases sig_of_isGammaType hm h₁ with h₁ | h₁ | h₁ | h₁ | h₁ <;>
    rcases sig_of_isGammaType hn h₂ with h₂ | h₂ | h₂ | h₂ | h₂
  all_goals first
    | (have := two_eq h₁.profile h₂.profile; omega)
    | exact (h₁.false_of_sigD4 h₂ hm).elim
    | exact (h₂.false_of_sigD4 h₁ hn).elim
    | exact (h₁.false_of_sigG2 h₂ hm).elim
    | exact (h₂.false_of_sigG2 h₁ hn).elim
    | exact (h₁.false_of_sigU h₂ hm).elim
    | exact (h₂.false_of_sigU h₁ hn).elim
    | exact (h₁.false_of_sigSp4 h₂ hm hn).elim
    | exact (h₂.false_of_sigSp4 h₁ hn hm).elim
    | exact (h₁.false_of_sigSp4 h₂ hm).elim
    | exact (h₂.false_of_sigSp4 h₁ hn).elim

end Compare

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
