module

public import CFSG.RankThree.PartTwo.Sec15.Item1518Res2ProofHess
public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofHess
import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofTools
import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofOut
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTen
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofTypes
import CFSG.RankThree.PartTwo.Sec12.Item125NonCentralTools
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofArith
import CFSG.RankThree.PartTwo.Sec21.Item223Of
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)

namespace Proof15Res9Y0

section Arith

theorem eq_one_or_eq_two_of_isChoice1519 {m p n f : ℕ} (hch : IsChoice1519 m p)
    (hp3 : 3 < p) (hm1 : 1 ≤ m) (h3m : ¬ 3 ∣ m) (hmnf : m = n * f) (hf1 : 1 ≤ f)
    (h : (2 : ZMod p) ^ (6 * f) = 1 ∨ p ∣ f) : n = 1 ∨ n = 2 := by
  have hp : p.Prime := hch.1
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).mp h0')
    omega
  have hm1' : (-1 : ZMod p) ≠ 1 := by
    have : Fact (2 < p) := ⟨by omega⟩
    exact ZMod.neg_one_ne_one
  have hferm : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at hmnf
      omega
    · exact hn
  have hfm : f ∣ m := ⟨n, by rw [hmnf, mul_comm]⟩
  have hfle : f ≤ m := Nat.le_of_dvd (by omega) hfm
  have hgcd : ∀ d e : ℕ, 1 ≤ d → (2 : ZMod p) ^ d = 1 →
      (∀ i : ℕ, i ∣ d → i < d → (2 : ZMod p) ^ i ≠ 1) → (2 : ZMod p) ^ e = 1 → d ∣ e := by
    intro d e hd1 hd hmin he
    have hg := pow_gcd_eq_one.mpr ⟨hd, he⟩
    by_contra hde
    have hlt : Nat.gcd d e < d := lt_of_le_of_ne (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left d e))
      fun heq => hde (heq ▸ Nat.gcd_dvd_right d e)
    exact hmin _ (Nat.gcd_dvd_left d e) hlt hg
  have hn_dvd : ∀ t : ℕ, m ∣ t * f → n ∣ t := by
    intro t ht
    rw [hmnf] at ht
    exact Nat.dvd_of_mul_dvd_mul_right (by omega) ht
  rcases hch.2.2 with ⟨k, hmk, hm4, hk, hmin⟩ | ⟨hm4, hmin⟩
  ·
    have hk1 : 1 ≤ k := by omega
    have hkodd : k % 2 = 1 := by omega
    have hk3 : ¬ 3 ∣ k := fun h3 => h3m (by rw [hmk]; exact Dvd.dvd.mul_left h3 2)
    have hk6 : Nat.Coprime k 6 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.coprime_mul_iff_right]
      refine ⟨Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hkodd), ?_⟩
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hk3).symm
    have hbig : k < f → f = m := by
      intro hkf
      obtain ⟨t, ht⟩ := hfm
      have ht1 : t = 1 := by
        rcases Nat.lt_or_ge t 2 with h2 | h2
        · have : t ≠ 0 := by rintro rfl; omega
          omega
        · exfalso
          have : f * 2 ≤ f * t := Nat.mul_le_mul_left f h2
          omega
      rw [ht, ht1, mul_one]
    rcases h with h6 | hpf
    · have hkf : k ∣ f := hk6.dvd_of_dvd_mul_left (hgcd k _ hk1 hk hmin h6)
      obtain ⟨t, rfl⟩ := hkf
      have ht : t ∣ 2 := by
        have : k * t ∣ k * 2 := by rw [mul_comm k 2, ← hmk]; exact hfm
        exact Nat.dvd_of_mul_dvd_mul_left (by omega) this
      rcases (Nat.dvd_prime Nat.prime_two).mp ht with rfl | rfl
      · right
        have : n * k = 2 * k := by rw [← hmk, hmnf, mul_one]
        exact Nat.eq_of_mul_eq_mul_right (by omega) this
      · left
        have : n * (k * 2) = 1 * (k * 2) := by rw [one_mul, ← hmnf, hmk, mul_comm]
        exact Nat.eq_of_mul_eq_mul_right (by omega) this
    · have hkp : k ∣ p - 1 := hgcd k _ hk1 hk hmin hferm
      have hkp' : k < p := by
        have := Nat.le_of_dvd (by omega) hkp
        omega
      have hpf' : p ≤ f := Nat.le_of_dvd (by omega) hpf
      have hfm' := hbig (by omega)
      left
      have : n * f = 1 * f := by rw [one_mul, ← hmnf, hfm']
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
  ·
    by_cases hme : m % 2 = 0
    ·
      have hsign : sign1519 m p = 1 := by
        have h' : 2 ^ m % 3 = 1 := Proof1514.two_pow_mod_three_of_even (Nat.even_iff.mpr hme)
        show (if 2 ^ m % 3 = 1 then (1 : ZMod p) else -1) = 1
        exact ite_eq_left_iff.mpr (fun hn => absurd h' hn)
      rw [hsign] at hmin
      have h2m : (2 : ZMod p) ^ m = 1 := by rw [hch.2.1, hsign]
      rcases h with h6 | hpf
      · have hn6 : n ∣ 6 := hn_dvd 6 (hgcd m _ hm1 h2m hmin h6)
        have hn3 : ¬ 3 ∣ n := fun h3 => h3m (hmnf ▸ Dvd.dvd.mul_right h3 f)
        have : n ≤ 6 := Nat.le_of_dvd (by norm_num) hn6
        interval_cases n <;> simp_all
      · have hmp : m ∣ p - 1 := hgcd m _ hm1 h2m hmin hferm
        have := Nat.le_of_dvd (by omega) hmp
        have := Nat.le_of_dvd (by omega) hpf
        omega
    ·
      have hsign : sign1519 m p = -1 := by
        have h' : 2 ^ m % 3 = 2 :=
          Proof1514.two_pow_mod_three_of_odd (Nat.odd_iff.mpr (by omega))
        show (if 2 ^ m % 3 = 1 then (1 : ZMod p) else -1) = -1
        exact ite_eq_right_iff.mpr (fun hn => absurd hn (by omega))
      rw [hsign] at hmin
      have h2m : (2 : ZMod p) ^ m = -1 := by rw [hch.2.1, hsign]
      have h22m : (2 : ZMod p) ^ (2 * m) = 1 := by
        rw [mul_comm, pow_mul, h2m]
        exact neg_one_sq
      have hdiv : ∀ e : ℕ, (2 : ZMod p) ^ e = 1 → 2 * m ∣ e := by
        intro e he
        set g := Nat.gcd (2 * m) e with hg
        have hg1 : (2 : ZMod p) ^ g = 1 := pow_gcd_eq_one.mpr ⟨h22m, he⟩
        have hg2m : g ∣ 2 * m := Nat.gcd_dvd_left _ _
        have hgm : ¬ g ∣ m := by
          rintro ⟨t, ht⟩
          apply hm1'
          rw [← h2m, ht, pow_mul, hg1, one_pow]
        have hgeven : g % 2 = 0 := by
          by_contra hodd
          apply hgm
          have hc : Nat.Coprime g 2 := Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by omega))
          exact hc.dvd_of_dvd_mul_left hg2m
        obtain ⟨g', hg'⟩ : ∃ g', g = 2 * g' := ⟨g / 2, by omega⟩
        have hg'm : g' ∣ m := by
          have : 2 * g' ∣ 2 * m := hg' ▸ hg2m
          exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
        have hsq : ((2 : ZMod p) ^ g') ^ 2 = 1 := by
          rw [← pow_mul, show g' * 2 = g by omega, hg1]
        have hg'1 : (2 : ZMod p) ^ g' = -1 := by
          rcases mul_self_eq_one_iff.mp
              (show (2 : ZMod p) ^ g' * (2 : ZMod p) ^ g' = 1 by rw [← sq]; exact hsq) with
            h1 | h1
          · exfalso
            obtain ⟨t, ht⟩ := hg'm
            apply hm1'
            rw [← h2m, ht, pow_mul, h1, one_pow]
          · exact h1
        have hg'eq : g' = m := by
          by_contra hne
          have hg'pos : 1 ≤ g' := by
            rcases Nat.eq_zero_or_pos g' with h0 | h0
            · rw [h0, pow_zero] at hg'1
              exact absurd hg'1.symm hm1'
            · exact h0
          exact hmin g' hg'm (lt_of_le_of_ne (Nat.le_of_dvd (by omega) hg'm) hne) hg'1
        rw [← hg'eq, ← hg']
        exact Nat.gcd_dvd_right _ _
      rcases h with h6 | hpf
      · have h1 := hdiv _ h6
        have hm3 : m ∣ 3 * f := by
          obtain ⟨t, ht⟩ := h1
          exact ⟨t, by linarith⟩
        have hn3 : n ∣ 3 := hn_dvd 3 hm3
        rcases (Nat.dvd_prime Nat.prime_three).mp hn3 with h | h
        · exact Or.inl h
        · exact absurd (hmnf ▸ Dvd.intro f (by rw [h]) : 3 ∣ m) h3m
      · have h1 := hdiv _ hferm
        have := Nat.le_of_dvd (by omega) h1
        have := Nat.le_of_dvd (by omega) hpf
        omega

theorem pow_six_eq_one_or_dvd {X : Type} [Group X] [Finite X] {f p : ℕ} (hf : 1 ≤ f)
    (hiso : Sec4.IsoLThreePi X 2 f) (hq2 : 2 < 2 ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hdvd : p ∣ Nat.card (MulAut X)) : (2 : ZMod p) ^ (6 * f) = 1 ∨ p ∣ f := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut X) := Finite.of_injective (fun α : MulAut X => (α : X → X))
    fun a b h => MulEquiv.ext (congrFun h)
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner X)
  have hinn : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner X) ∣ Nat.card X := by
    unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
    exact Subgroup.card_range_dvd _
  have hp2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hp3' : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hsub : ∀ n : ℕ, p ∣ (2 ^ f) ^ n - 1 → (2 : ZMod p) ^ (n * f) = 1 := by
    intro n h
    have h1 : 1 ≤ (2 ^ f) ^ n := Nat.one_le_pow _ _ (by omega)
    have h0 := (ZMod.natCast_eq_zero_iff _ p).mpr h
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      sub_eq_zero, ← pow_mul, mul_comm] at h0
    exact h0
  have hadd : ∀ n : ℕ, p ∣ (2 ^ f) ^ n + 1 → (2 : ZMod p) ^ (2 * (n * f)) = 1 := by
    intro n h
    have h0 := (ZMod.natCast_eq_zero_iff _ p).mpr h
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      add_eq_zero_iff_eq_neg, ← pow_mul, mul_comm f n] at h0
    rw [mul_comm, pow_mul, h0]
    exact neg_one_sq
  have hsix : ∀ n : ℕ, n ∣ 6 → (2 : ZMod p) ^ n = 1 → (2 : ZMod p) ^ 6 = 1 := by
    intro n hn h
    obtain ⟨t, ht⟩ := hn
    rw [ht, pow_mul, h, one_pow]
  have hsix' : ∀ n : ℕ, n ∣ 6 → (2 : ZMod p) ^ (n * f) = 1 → (2 : ZMod p) ^ (6 * f) = 1 := by
    intro n hn h
    obtain ⟨t, ht⟩ := hn
    rw [ht, mul_comm n t, mul_assoc, pow_mul', h, one_pow]
  have hX : p ∣ Nat.card X ∨
      p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
    rw [hcard] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact Or.inr h
    · exact Or.inl (h.trans hinn)
  rcases hiso with ⟨h31, ⟨φ⟩⟩ | ⟨h32, ⟨φ⟩⟩
  ·
    rcases hX with h | h
    · left
      have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 f)
      rw [GaloisField.card 2 f (by omega), ← Nat.card_congr φ.toEquiv] at hc
      have h' : p ∣ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) :=
        hc ▸ Dvd.dvd.mul_right h _
      rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
      · exact absurd (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h1)) hp2
      · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
        · exact hsix' 2 (by norm_num) (hsub 2 h2)
        · exact hsix' 3 (by norm_num) (hsub 3 h2)
    · have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ∣
          2 * f * Nat.gcd 3 (2 ^ f - 1) := by
        have e := φ.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 f))
        rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
        exact higher_linear_outer_order_divides_field_gcd_bound
          Nat.prime_two hf (le_refl 3) (GaloisField.card 2 f (by omega))
      have h' := h.trans hOut
      rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
      · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
        · exact absurd h2 hp2
        · exact Or.inr h2
      · exact absurd (h1.trans (Nat.gcd_dvd_left _ _)) hp3'
  ·
    rcases hX with h | h
    · left
      have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 f hf
      rw [← Nat.card_congr φ.toEquiv] at hc
      have h' : p ∣ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) :=
        hc ▸ Dvd.dvd.mul_right h _
      rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
      · exact absurd (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h1)) hp2
      · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
        · exact hsix' 2 (by norm_num) (hsub 2 h2)
        · exact hsix' 6 (by norm_num) (by rw [show 6 * f = 2 * (3 * f) by ring]; exact hadd 3 h2)
    · have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ∣
          2 * f * (2 ^ f + 1) := by
        rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ).toEquiv]
        refine Sec4.card_outer_projSU_dvd 3 2 f hf (le_refl 3) ?_
        rintro ⟨-, h2⟩
        omega
      have h' := h.trans hOut
      rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
      · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
        · exact absurd h2 hp2
        · exact Or.inr h2
      · left
        have h2 := hadd 1 (by rwa [pow_one])
        rw [one_mul] at h2
        exact hsix' 2 (by norm_num) h2

end Arith

section Structure

variable {G : Type} [Group G] [Finite G]

theorem nonempty_quot_pPrimeCore_equiv_a7 {A Y : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hY : Y ∈ scriptY4 A LB)
    (h7 : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))) :
    Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨e⟩ := h7
  have hq : IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.2.2.2
  have hO2 : CFSG.pCore 2 ↥Y ≤ CFSG.pPrimeCore 3 ↥Y := pCore_two_le_pPrimeCore_three
  set f := QuotientGroup.map (CFSG.pCore 2 ↥Y) (CFSG.pPrimeCore 3 ↥Y) (MonoidHom.id _)
    (by simpa using hO2) with hf
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨y, rfl⟩
  have hZ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ :=
    Proof1520.center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num))
  have hker : f.ker = ⊥ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq f.normal_ker with ht | hc
    · exfalso
      apply Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY
      refine eq_top_iff.mpr fun y _ => ?_
      have hy : (y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ f.ker := ht ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hf, QuotientGroup.map_mk, MonoidHom.id_apply,
        QuotientGroup.eq_one_iff] at hy
      exact hy
    · exact le_bot_iff.mp (hZ ▸ hc)
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm.trans e⟩

theorem card_quot_le_card_inf {L Y : Subgroup G}
    (hYeq : Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y) :
    Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ Nat.card ↥(L ⊓ Y) := by
  set ψ : ↥(L ⊓ Y) →* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion inf_le_right) with hψ
  have hψs : Function.Surjective ψ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : (y : G) ∈ (((L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := by
      rw [← hYeq]
      exact y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))] at hy
    obtain ⟨k, hk, o, ho, hko⟩ := hy
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Proof1520.mem_pCore_two_iff]
    show (k : G)⁻¹ * (y : G) ∈ CFSG.Open.pCoreOf 2 Y
    rw [← hko]
    simpa using ho
  exact Nat.card_le_card_of_surjective ψ hψs

theorem isoLThreePi_of_nine_dvd {X : Type} [Group X] {f : ℕ} (hf1 : 1 ≤ f) (h3f : ¬ 3 ∣ f)
    (hX : IsLThreeEpsAt X 2 f) (h9 : 9 ∣ Nat.card X) : Sec4.IsoLThreePi X 2 f ∧ 2 < 2 ^ f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hX with ⟨⟨φ⟩⟩ | ⟨hq2, ⟨φ⟩⟩
  · have hmod : 2 ^ f % 3 = 1 := by
      rcases Proof1520.two_pow_mod_nine_cases h3f with ⟨hodd, -⟩ | ⟨heven, -⟩
      · exact absurd (Nat.card_congr φ.toEquiv ▸ h9)
          (Proof1520.not_nine_dvd_card_projSL hf1 hodd h3f)
      · exact Proof1514.two_pow_mod_three_of_even (Nat.even_iff.mpr heven)
    refine ⟨Or.inl ⟨hmod, ⟨φ⟩⟩, ?_⟩
    have heven : f % 2 = 0 := by
      by_contra hodd
      rw [Proof1514.two_pow_mod_three_of_odd (Nat.odd_iff.mpr (by omega))] at hmod
      omega
    have : 2 ^ 1 < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
    simpa using this
  · have hmod : 2 ^ f % 3 = 2 := by
      rcases Proof1520.two_pow_mod_nine_cases h3f with ⟨hodd, -⟩ | ⟨heven, -⟩
      · exact Proof1514.two_pow_mod_three_of_odd (Nat.odd_iff.mpr hodd)
      · exact absurd (Nat.card_congr φ.toEquiv ▸ h9)
          (Proof1520.not_nine_dvd_card_projSU hf1 heven h3f)
    exact ⟨Or.inr ⟨hmod, ⟨φ⟩⟩, hq2⟩

end Structure

section A7

variable {G : Type} [Group G] [Finite G]

set_option maxHeartbeats 400000 in
theorem false_of_quot_a7 (h148 : Sec14.Item148R) (hbot : Sec14.Item145BotS14)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) (hΩ : omegaA A = {Subgroup.zpowers c})
    {m : ℕ} (hm1 : 1 ≤ m) (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m)
    {Y₀ : Subgroup G} (hY₀ : Y₀ ∈ scriptY4 A (lB A))
    (h7 : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 7))) : False := by
  have hD := h.toSec13Data
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_types148
    (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  have hpt : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      L' = L := by
    intro c' L' hc' hL'
    have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
      rw [hΩ] at hc'
      exact hc'
    exact Proof1515.eq_of_mem_lA_of_zpowers_eq h.toSec14Std h3L hcc hL'
  obtain ⟨e7⟩ := nonempty_quot_pPrimeCore_equiv_a7 hY₀ h7
  have hY2520 : Nat.card (↥Y₀ ⧸ CFSG.pPrimeCore 3 ↥Y₀) = 2520 := by
    rw [Nat.card_congr e7.toEquiv, card_alternatingGroup_seven]
  have hYΔ := Proof1515.eq_deltaZero_of_mem_scriptY4 hbot h hY₀
  rcases Proof1515.cases148_of_mem_scriptY4 (h148 G A c L h) h.isElemAbelian.1 hY₀ hYΔ with
    ⟨c', hc', -, L', hL', hcases⟩ | ⟨c', L', hc', hL', hJ, -⟩ |
      ⟨-, ⟨c', L', hc', hL', hL7⟩, -⟩ | ⟨c', L', n, m', hc', hL', -, -, hε, -⟩
  · have hL'L := hpt c' L' hc' hL'
    subst hL'L
    rcases hcases with hφ | ⟨hL, -⟩ | ⟨p', f', e', hp', -, -, -, hε'⟩ | ⟨hJ, -⟩
    · obtain ⟨φ⟩ := hφ
      have hL2520 : Nat.card (↥L' ⧸ aschbacherSolvableCore 3 ↥L') = 2520 := by
        rw [← Nat.card_congr φ.toEquiv, hY2520]
      exact Item148Rank.not_isoLThreePi_of_card_2520 hL2520 2 m hiso
    · rcases hL with hφ | ⟨h5, hφ⟩ | ⟨h5, hφ⟩
      · obtain ⟨φ⟩ := hφ
        exact KFacts.KS14.not_isoLThreePi_M22 2 m
          (Proof1520.isoLThreePi_of_mulEquiv φ.symm hiso)
      · obtain ⟨φ⟩ := hφ
        have h25 : Sec4.IsoLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') 5 2 :=
          Or.inl ⟨by norm_num, ⟨φ⟩⟩
        have hq := Sec19.Step1917EqProof.eq_of_isoLThreePi hm1 (by norm_num) hiso h25
        have h2 : 2 ∣ 5 ^ 2 := hq ▸ dvd_pow_self 2 (by omega)
        norm_num at h2
      · obtain ⟨φ⟩ := hφ
        have h51 : Sec4.IsoLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') 5 1 :=
          Or.inr ⟨by norm_num, ⟨φ⟩⟩
        have hq := Sec19.Step1917EqProof.eq_of_isoLThreePi hm1 le_rfl hiso h51
        have h2 : 2 ∣ 5 ^ 1 := hq ▸ dvd_pow_self 2 (by omega)
        norm_num at h2
    · exact Item148Rank.not_isLThreeEpsAt_of_card_2520 hY2520 p' f' hε'
    · obtain ⟨φJ⟩ := hJ
      exact Sec14.Item148PtRes2.not_isoLThreePi_J2 2 m
        (Proof1520.isoLThreePi_of_mulEquiv φJ.symm hiso)
  · have hL'L := hpt c' L' hc' hL'
    subst hL'L
    obtain ⟨φJ⟩ := hJ
    exact Sec14.Item148PtRes2.not_isoLThreePi_J2 2 m
      (Proof1520.isoLThreePi_of_mulEquiv φJ.symm hiso)
  · have hL'L := hpt c' L' hc' hL'
    subst hL'L
    obtain ⟨φ7⟩ := hL7
    have hL2520 : Nat.card (↥L' ⧸ aschbacherSolvableCore 3 ↥L') = 2520 := by
      rw [Nat.card_congr φ7.toEquiv, card_alternatingGroup_seven]
    exact Item148Rank.not_isoLThreePi_of_card_2520 hL2520 2 m hiso
  · exact Item148Rank.not_isoLThreePi_of_card_2520 hY2520 2 (3 * n) hε

end A7

section Hess

variable {G : Type} [Group G] [Finite G]

theorem inf_le_of_hessSub {A L Y₀ : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h9AL : Nat.card ↥(A ⊓ L) = 9) (hY₀A : A ≤ Subgroup.normalizer (Y₀ : Set G)) {m : ℕ}
    (hm1 : 1 ≤ m) (hisoL : Sec4.IsoLThreePi ↥L 2 m) (h9 : ¬ (2 ^ m % 9 = 1 ∨ 2 ^ m % 9 = 8))
    (hYeq : Y₀ = (L ⊓ Y₀) ⊔ CFSG.Open.pCoreOf 2 Y₀) {r f : ℕ} [Fact r.Prime]
    (hYiso : IsLThreeEpsAt (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) r f) : A ⊓ L ≤ A ⊓ Y₀ := by
  set E : Subgroup ↥L := A.subgroupOf L with hE
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := Proof1520.isElemAbelian_subgroupOf L hA
  have hE9 : Nat.card ↥E = 9 := by
    rw [hE, ← Subgroup.inf_subgroupOf_right, Proof1520.card_subgroupOf_inf, h9AL]
  set K : Subgroup ↥L := Y₀.subgroupOf L with hK
  have hEK : E ≤ Subgroup.normalizer (K : Set ↥L) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hK, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hY₀A (Subgroup.mem_subgroupOf.mp hx)) (y : G)
  have hKY : ∀ x : ↥K, ((x : ↥L) : G) ∈ Y₀ := fun x => Subgroup.mem_subgroupOf.mp x.2
  let ι : ↥K →* ↥Y₀ :=
    { toFun := fun x => ⟨((x : ↥L) : G), hKY x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun a b hab =>
    Subtype.ext (Subtype.ext (show ((a : ↥L) : G) = ((b : ↥L) : G) from
      congrArg (fun y : ↥Y₀ => (y : G)) hab))
  set ψ : ↥K →* ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)).comp ι with hψ
  have hψs : Function.Surjective ψ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : (y : G) ∈ (((L ⊓ Y₀) ⊔ CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G) := by
      rw [← hYeq]
      exact y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀))] at hy
    obtain ⟨k, hk, o, ho, hko⟩ := hy
    refine ⟨⟨⟨k, hk.1⟩, Subgroup.mem_subgroupOf.mpr hk.2⟩, ?_⟩
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Proof1520.mem_pCore_two_iff]
    show (k : G)⁻¹ * (y : G) ∈ CFSG.Open.pCoreOf 2 Y₀
    rw [← hko]
    simpa using ho
  have hN2 : IsPGroup 2 ↥ψ.ker := by
    rw [hψ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup.comap_of_injective _ hι
  have hKN : IsLThreeEpsAt (↥K ⧸ ψ.ker) r f :=
    IsLThreeEpsAt.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm hYiso
  have hEleK := ks1522HessSub ↥L m hm1 hisoL h9 E hEab hE9 K hEK ψ.ker hN2 r f hKN
  exact fun x hx => ⟨hx.1, Subgroup.mem_subgroupOf.mp
    (hEleK (Subgroup.mem_subgroupOf.mpr hx.1 : (⟨x, hx.2⟩ : ↥L) ∈ E))⟩

end Hess

end Proof15Res9Y0

open Proof15Res9Y0

theorem step1519Y0E9_of
    (h1511 : Item1511R) (hpt : Step1513MeetsPoint) (h148 : Sec14.Item148R)
    (hbot : Sec14.Item145BotS14) (h138 : Item138N) : Step1519Y0E9 := by
  classical
  intro G _ _ A c L h Y hctx hno hs m p hiso h3m hch hp3 Y₀ hY₀ hpdvd
  have hD := h.toSec13Data
  obtain ⟨-, h9AL, -⟩ := Proof1517.point_facts h hctx
  obtain ⟨-, -, -, -, -, hprod, -, -, hΩ⟩ := hctx.concl1515
  have hθL := Proof1520.theta_eq_bot_of_isSimpleGroup h.mem_thetaComponentsAt hs
  have hisoL : Sec4.IsoLThreePi ↥L 2 m := Proof1520.isoLThreePi_of_theta_eq_bot hθL hiso
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_types148
    (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exfalso
      rcases hisoL with ⟨-, ⟨φ⟩⟩ | ⟨h2, -⟩
      · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 0)
        rw [Sec21.natCard_galoisField_two_zero, ← Nat.card_congr φ.toEquiv] at hc
        norm_num at hc
        have h9 : 9 ∣ Nat.card L := h9AL ▸ Subgroup.card_dvd_of_le inf_le_right
        omega
      · norm_num at h2
    · exact hm
  have h3m' := h3m hm1
  have h9m : ¬ (2 ^ m % 9 = 1 ∨ 2 ^ m % 9 = 8) :=
    not_modNine_of_inner h h138 KFacts.kSL3PiOrder3TypeC hm1 hiso hprod
  have hptL : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      L' = L := by
    intro c' L' hc' hL'
    have hcc : Subgroup.zpowers c' = Subgroup.zpowers c := by
      rw [hΩ] at hc'
      exact hc'
    exact Proof1515.eq_of_mem_lA_of_zpowers_eq h.toSec14Std h3L hcc hL'
  have hnoJ : ∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) := by
    intro b Lb hb hLb
    have hLbL := hptL b Lb hb hLb
    subst hLbL
    exact ⟨fun φ => Sec14.Item148PtRes2.not_isoLThreePi_J2 2 m
      (Proof1520.isoLThreePi_of_mulEquiv φ.symm hiso)⟩
  obtain ⟨c', L', hc', hL', hmeet⟩ := hpt G A c L h hnoJ Y₀ hY₀
  have hL'L := hptL c' L' hc' hL'
  rw [hL'L] at hmeet
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  have hAH : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun a ha =>
    centralizer_singleton_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute ha hD.mem_A))
  have hY₀A : A ≤ Subgroup.normalizer (Y₀ : Set G) := hY₀.1.1.2
  obtain ⟨P, hP, hAP⟩ := Sec12.Gap125NonCentralBar.exists_isSylowOf_le (le_inf hAH hY₀A) hA3
  obtain ⟨-, -, hY₀eq, hcases, -⟩ := h1511 G A c L h 2 m hm1 hiso Y₀ hY₀ hmeet P hAP hP
  rcases hcases with ⟨n, f, hf1, hmnf, hY₀iso⟩ | h7
  swap
  · exact (false_of_quot_a7 h148 hbot h hΩ hm1 hiso hY₀.1 h7).elim
  have hALY := inf_le_of_hessSub hD.isElemAbelian h9AL hY₀A hm1 hisoL h9m hY₀eq hY₀iso
  have h9Y : 9 ∣ Nat.card (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) :=
    (h9AL ▸ Subgroup.card_dvd_of_le hALY).trans
      (Proof1520.card_inf_dvd_card_quot hD.isElemAbelian)
  have h3f : ¬ 3 ∣ f := fun h3 => h3m' (hmnf ▸ Dvd.dvd.mul_left h3 n)
  obtain ⟨hpi, hq2⟩ := isoLThreePi_of_nine_dvd hf1 h3f hY₀iso h9Y
  have hn := eq_one_or_eq_two_of_isChoice1519 hch hp3 hm1 h3m' hmnf hf1
    (pow_six_eq_one_or_dvd hf1 hpi hq2 hch.1 hp3 hpdvd)
  rcases hn with rfl | rfl
  ·
    exfalso
    rw [one_mul] at hmnf
    subst hmnf
    have hcardeq : Nat.card (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) = Nat.card L := by
      rcases hpi with ⟨h1, ⟨φ⟩⟩ | ⟨h1, ⟨φ⟩⟩ <;> rcases hisoL with ⟨h2, ⟨ψ⟩⟩ | ⟨h2, ⟨ψ⟩⟩
      · exact Nat.card_congr (φ.trans ψ.symm).toEquiv
      · omega
      · omega
      · exact Nat.card_congr (φ.trans ψ.symm).toEquiv
    have hle := card_quot_le_card_inf hY₀eq
    rw [hcardeq] at hle
    have hLY : L ⊓ Y₀ = L := Subgroup.eq_of_le_of_card_ge inf_le_left hle
    exact hno Y₀ hY₀.2 (hLY ▸ inf_le_right)
  · exact ⟨f, hf1, hmnf, hpi, A ⊓ L, hALY, h9AL⟩

end CFSG.RankThree.PartTwo.Sec15
