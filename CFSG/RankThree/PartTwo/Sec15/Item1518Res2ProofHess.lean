module

public import CFSG.RankThree.PartTwo.Sec15.Item1518Res2ProofCent

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KS1519HessCentAut : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), 1 ≤ f → Sec4.IsoLThreePi X 2 f →
    ¬ (2 ^ f % 9 = 1 ∨ 2 ^ f % 9 = 8) →
    ∀ x : X, orderOf x = 3 → ∀ r : ℕ, r.Prime → 3 < r →
      r ∣ Nat.card (Subgroup.centralizer ({MulAut.conj x} : Set (MulAut X))) →
        (2 : ZMod r) ^ f = sign1519 f r ∨ r ∣ f

@[expose] noncomputable def Step1519Y0E9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y → (∀ X ∈ scriptY2 A, ¬ L ≤ X) →
      IsSimpleGroup ↥L →
      ∀ m p : ℕ, Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m →
        (1 ≤ m → ¬ 3 ∣ m) → IsChoice1519 m p → 3 < p →
        ∀ Y₀ ∈ scriptY0 A (lB A), p ∣ Nat.card (MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) →
          ∃ f : ℕ, 1 ≤ f ∧ m = 2 * f ∧ Sec4.IsoLThreePi (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) 2 f ∧
            ∃ E : Subgroup G, E ≤ A ⊓ Y₀ ∧ Nat.card E = 9

namespace Proof1518R2

theorem not_modNine_of_not_three_dvd {f : ℕ} (h : ¬ 3 ∣ f) :
    ¬ (2 ^ f % 9 = 1 ∨ 2 ^ f % 9 = 8) := by
  have key : 2 ^ f % 9 = 2 ^ (f % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod f 6, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [key]
  have hf : f % 6 = 1 ∨ f % 6 = 2 ∨ f % 6 = 4 ∨ f % 6 = 5 := by omega
  rcases hf with h1 | h1 | h1 | h1 <;> rw [h1] <;> norm_num

theorem not_sign_or_dvd_of_isChoice1519 {m p f : ℕ} (hch : IsChoice1519 m p) (hp3 : 3 < p)
    (hf : 1 ≤ f) (hmf : m = 2 * f) : ¬ ((2 : ZMod p) ^ f = sign1519 f p ∨ p ∣ f) := by
  have hp : p.Prime := hch.1
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (2 < p) := ⟨by omega⟩
  have hfrob : ∀ t : ℕ, (2 : ZMod p) ^ (p * t) = (2 : ZMod p) ^ t := fun t => by
    rw [pow_mul, ZMod.pow_card]
  rcases hch.2.2 with ⟨k, hmk, hm4, hk, hmin⟩ | ⟨hm4, hmin⟩
  ·
    have hkf : k = f := by omega
    subst hkf
    have hodd : Odd k := by
      refine Nat.odd_iff.mpr ?_
      omega
    rw [sign1519_of_odd hodd]
    rintro (h | ⟨t, rfl⟩)
    · rw [hk] at h
      exact ZMod.neg_one_ne_one h.symm
    · have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · subst h0
          omega
        · exact h0
      have htk : t < p * t := by
        have := hp.two_le
        nlinarith
      exact hmin t (Dvd.intro_left p rfl) htk (by rw [← hfrob, hk])
  ·
    have hev : Even f := by
      refine Nat.even_iff.mpr ?_
      omega
    have hmev : Even m := ⟨f, by omega⟩
    rw [sign1519_of_even hev]
    have hsm := hch.2.1
    rw [sign1519_of_even hmev] at hsm hmin
    rintro (h | ⟨t, rfl⟩)
    · exact hmin f ⟨2, by rw [hmf]; ring⟩ (by omega) h
    · have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · subst h0
          omega
        · exact h0
      have h2t : 2 * t < m := by
        have := hp.two_le
        rw [hmf]
        nlinarith
      refine hmin (2 * t) ⟨p, by rw [hmf]; ring⟩ h2t ?_
      calc (2 : ZMod p) ^ (2 * t) = (2 : ZMod p) ^ (p * (2 * t)) := (hfrob _).symm
        _ = (2 : ZMod p) ^ m := by rw [hmf]; ring_nf
        _ = 1 := hsm

theorem autQuotTwo_eq_conj {G : Type} [Group G] {Y₀ : Subgroup G}
    (g : ↥(Subgroup.normalizer (Y₀ : Set G))) (hg : (g : G) ∈ Y₀) :
    autQuotTwo Y₀ g = MulAut.conj (((⟨g, hg⟩ : ↥Y₀) : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H y =>
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    change ((Y₀.normalizerMonoidHom g y : ↥Y₀) : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) = _
    congr 1

theorem orderOf_mk_eq_three {G : Type} [Group G] [Finite G] {Y₀ : Subgroup G} {e : ↥Y₀}
    (he3 : e ^ 3 = 1) (he1 : e ≠ 1) :
    orderOf ((e : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, he3, QuotientGroup.mk_one]) ?_
  intro h1
  rw [QuotientGroup.eq_one_iff] at h1
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥Y₀)) ⟨e, h1⟩
  have hk' : e ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h2 : orderOf e ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h3 : orderOf e ∣ 3 := orderOf_dvd_of_pow_eq_one he3
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  exact he1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h3))

end Proof1518R2

open Proof1518R2

theorem step1519HessE9_of (hD : Step1519Y0E9) (hK : KS1519HessCentAut) : Step1519HessE9 := by
  intro G _ _ A c L h Y hctx hno hs m p hiso h3m hch hp3 Y₀ hY₀ hdvd
  obtain ⟨f, hf, hmf, hisoY, E, hEAY, hE9⟩ :=
    hD G A c L h Y hctx hno hs m p hiso h3m hch hp3 Y₀ hY₀ hdvd
  refine ⟨E, hEAY.trans inf_le_left, hE9, fun e he he1 => ?_⟩
  have heY : (e : G) ∈ Y₀ := (Subgroup.mem_inf.mp (hEAY he)).2
  have he3 : (e : G) ^ 3 = 1 := h.toSec13Data.isElemAbelian.2 _ (Subgroup.mem_inf.mp (hEAY he)).1
  have hord : orderOf (((⟨e, heY⟩ : ↥Y₀) : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) = 3 :=
    orderOf_mk_eq_three (Subtype.ext he3) (fun h0 => he1 (congrArg Subtype.val h0))
  have h3f : ¬ 3 ∣ f := fun h3 => h3m (by omega) (by rw [hmf]; exact Dvd.dvd.mul_left h3 2)
  rw [autQuotTwo_eq_conj e heY]
  intro hp
  exact not_sign_or_dvd_of_isChoice1519 hch hp3 hf hmf
    (hK _ f hf hisoY (not_modNine_of_not_three_dvd h3f) _ hord p hch.1 hp3 hp)

theorem step1519CentAut_of_y0E9 (hD : Step1519Y0E9) (hK : KS1519HessCentAut) :
    Step1519CentAut :=
  step1519CentAut_of (step1519HessE9_of hD hK)

end CFSG.RankThree.PartTwo.Sec15
