module

public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec19.Item19ResProofAutCent
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3K
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_with_same_image_of_trivial_quotient_action)

@[expose] def KS17L3AutCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], 3 < p →
    Sec4.IsoLThreePi X p 1 → p % 9 ≠ 1 → p % 9 ≠ 8 →
    ∀ B : Subgroup X, Nat.card B = 9 → ∀ α : MulAut X, (∀ b ∈ B, α b = b) →
      ∃ b ∈ B, α = MulAut.conj b

@[expose] def KS17L3TwoCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], 3 < p →
    Sec4.IsoLThreePi X p 1 → p % 9 ≠ 1 → p % 9 ≠ 8 →
    ∀ B : Subgroup X, Nat.card B = 9 →
      (∀ R : Subgroup X, IsPGroup 2 R → B ≤ Subgroup.normalizer (R : Set X) →
        ∃ b ∈ B, b ≠ 1 ∧ R ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer {b})) ∧
      ∃ R₀ : Subgroup X, IsPGroup 2 R₀ ∧ B ≤ Subgroup.normalizer (R₀ : Set X) ∧ R₀ ≠ ⊥

namespace Proof17Res7

section Abstract

variable {X : Type} [Group X]

theorem center_eq_bot_of_iso {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (hp : 3 < p)
    (hiso : Sec4.IsoLThreePi X p e) : Subgroup.center X = ⊥ := by
  rcases hiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · exact Sec19.Item19ResProof.center_eq_bot_of_mulEquiv φ
      (Sec13.isPerfect_center_projSL p e he hq).2
  · have hq2 : 2 < p ^ e := lt_of_lt_of_le (by omega : 2 < p) (Nat.le_self_pow (by omega) p)
    exact Sec19.Item19ResProof.center_eq_bot_of_mulEquiv φ
      (Sec13.isPerfect_center_projSU p e he hq hq2).2

theorem conj_injective_of_center {Y : Type*} [Group Y] (hZ : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz : g * z * g⁻¹ = z := by
      have := congrArg (fun φ : MulAut Y => φ z) hg
      simpa only [MulAut.conj_apply, MulAut.one_apply] using this
    calc z * g = g * z * g⁻¹ * g := by rw [hz]
      _ = g * z := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem conj_apply_eq {Y : Type*} [Group Y] (σ : MulAut Y) (x : Y) :
    MulAut.conj (σ x) = σ * MulAut.conj x * σ⁻¹ := by
  ext y
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem range_conj_normal (Y : Type*) [Group Y] :
    (MulAut.conj : Y →* MulAut Y).range.Normal := by
  refine ⟨fun n hn σ => ?_⟩
  obtain ⟨x, rfl⟩ := hn
  exact ⟨σ x, conj_apply_eq σ x⟩

theorem commute_of_card_nine {B : Subgroup X} (hB : Nat.card B = 9) {a b : X} (ha : a ∈ B)
    (hb : b ∈ B) : a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := B)
    (by rw [hB]; norm_num)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val h

variable [Finite X]

theorem centralizer_eq_of_autCent (hA : KS17L3AutCent) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hiso : Sec4.IsoLThreePi X p 1) (h91 : p % 9 ≠ 1) (h98 : p % 9 ≠ 8) {B : Subgroup X}
    (hB : Nat.card B = 9) : Subgroup.centralizer (B : Set X) = B := by
  have hZ := center_eq_bot_of_iso le_rfl hp hiso
  refine le_antisymm (fun g hg => ?_) (fun b hb => ?_)
  · obtain ⟨b, hb, hgb⟩ := hA X p hp hiso h91 h98 B hB (MulAut.conj g) fun x hx => by
      rw [MulAut.conj_apply, ← (Subgroup.mem_centralizer_iff.mp hg x hx), mul_inv_cancel_right]
    rw [conj_injective_of_center hZ hgb]
    exact hb
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact commute_of_card_nine hB hx hb

theorem le_range_of_autCent (hA : KS17L3AutCent) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hiso : Sec4.IsoLThreePi X p 1) (h91 : p % 9 ≠ 1) (h98 : p % 9 ≠ 8) {B : Subgroup X}
    (hB : Nat.card B = 9) {Q : Subgroup (MulAut X)} (hQ3 : ¬ 3 ∣ Nat.card Q)
    (hQN : B.map (MulAut.conj : X →* MulAut X) ≤ Subgroup.normalizer (Q : Set (MulAut X))) :
    Q ≤ (MulAut.conj : X →* MulAut X).range := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Sec19.Item19ResProof.finite_mulAut X
  have hZ := center_eq_bot_of_iso le_rfl hp hiso
  set I := (MulAut.conj : X →* MulAut X).range with hI
  have hIn : I.Normal := range_conj_normal X
  set P := B.map (MulAut.conj : X →* MulAut X) with hP
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB]; norm_num)
  have hP3 : IsPGroup 3 P := hB3.map _
  set f : Q →* MulAut X ⧸ I := (QuotientGroup.mk' I).comp Q.subtype with hf
  have hker : ¬ 3 ∣ Nat.card f.ker := fun h => hQ3 (h.trans (Subgroup.card_subgroup_dvd_card _))
  have htriv : ∀ (m : P) (q : Q), f ⟨m * q * (m : MulAut X)⁻¹,
      Subgroup.le_normalizer_iff.mp hQN m m.property q q.property⟩ = f q := by
    intro m q
    obtain ⟨b, -, hmb⟩ := m.2
    have hmI : (m : MulAut X) ∈ I := ⟨b, hmb⟩
    rw [hf, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq]
    have e : ((m : MulAut X) * q * (m : MulAut X)⁻¹)⁻¹ * q =
        (m : MulAut X) * ((q : MulAut X)⁻¹ * (m : MulAut X)⁻¹ * (q : MulAut X)) := by group
    change ((m : MulAut X) * q * (m : MulAut X)⁻¹)⁻¹ * q ∈ I
    rw [e]
    refine mul_mem hmI ?_
    have := hIn.conj_mem _ (inv_mem hmI) (q : MulAut X)⁻¹
    simpa using this
  intro q hq
  obtain ⟨q', hq'C, hq'e⟩ :=
    exists_centralizer_with_same_image_of_trivial_quotient_action 3 Nat.prime_three P Q hP3 hQN
      f hker htriv ⟨q, hq⟩
  have hfix : ∀ b ∈ B, (q' : MulAut X) b = b := by
    intro b hb
    have hc := Subgroup.mem_centralizer_iff.mp hq'C (MulAut.conj b) ⟨b, hb, rfl⟩
    apply conj_injective_of_center hZ
    rw [conj_apply_eq, ← hc, mul_inv_cancel_right]
  obtain ⟨b₀, -, hq'b⟩ := hA X p hp hiso h91 h98 B hB q' hfix
  have hq'I : (q' : MulAut X) ∈ I := ⟨b₀, hq'b.symm⟩
  have h1 : f q' = 1 := by
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hq'I
  rw [hq'e, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

omit [Finite X] in
theorem eq_bot_of_isPGroup_two_of_le {B R : Subgroup X} (hB : Nat.card B = 9)
    (hR2 : IsPGroup 2 R) (hRB : R ≤ B) : R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.eq_bot_iff_forall R).mpr fun r hr => ?_
  obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
  have h2 : orderOf r ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h9 : orderOf r ∣ 9 := by
    have := orderOf_dvd_natCard (⟨r, hRB hr⟩ : B)
    rwa [Subgroup.orderOf_mk, hB] at this
  have hcop : Nat.Coprime (2 ^ k) 9 := Nat.Coprime.pow_left _ (by norm_num)
  have h1 : orderOf r ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd h2 h9
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

theorem exists_not_mem_normalizer_of_two (hA : KS17L3AutCent) (hT : KS17L3TwoCent) {p : ℕ}
    [Fact p.Prime] (hp : 3 < p) (hiso : Sec4.IsoLThreePi X p 1) (h91 : p % 9 ≠ 1)
    (h98 : p % 9 ≠ 8) {B R : Subgroup X} (hB : Nat.card B = 9)
    (hR : R ∈ maxInvariantPiSubgroups ⊤ B (piOf 2)) :
    ∃ x ∈ Subgroup.normalizer (B : Set X), x ∉ Subgroup.normalizer (R : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hR.1.2.1
  have hBR : B ≤ Subgroup.normalizer (R : Set X) := hR.1.2.2
  obtain ⟨hT1, R₀, hR₀2, hBR₀, hR₀1⟩ := hT X p hp hiso h91 h98 B hB
  obtain ⟨b, hbB, hb1, hRO⟩ := hT1 R hR2 hBR
  have hR1 : R ≠ ⊥ := by
    intro hR1
    apply hR₀1
    have := hR.2 ⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two R₀).mpr hR₀2, hBR₀⟩
      (by rw [hR1]; exact bot_le)
    rw [hR1] at this
    exact le_bot_iff.mp this
  set D := B ⊓ Subgroup.centralizer (R : Set X) with hD
  have hbD : b ∈ D := by
    refine ⟨hbB, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    have hrC := CFSG.LieType.BorelTits.pCoreOf_le 2 _ (hRO hr)
    exact Subgroup.mem_centralizer_singleton_iff.mp hrC
  have hCB := centralizer_eq_of_autCent hA hp hiso h91 h98 hB
  have hDB : D ≠ B := by
    intro hDB
    apply hR1
    refine eq_bot_of_isPGroup_two_of_le hB hR2 ?_
    rw [← hCB]
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxD : x ∈ D := hDB ▸ hx
    exact (Subgroup.mem_centralizer_iff.mp hxD.2 r hr).symm
  have hDcard : Nat.card D = 3 := by
    have hd : Nat.card D ∣ 9 := hB ▸ Subgroup.card_dvd_of_le inf_le_left
    have hD1 : Nat.card D ≠ 1 := by
      intro h1
      rw [Subgroup.card_eq_one] at h1
      apply hb1
      have : b ∈ (⊥ : Subgroup X) := h1 ▸ hbD
      exact this
    have hD9 : Nat.card D ≠ 9 := fun h9 =>
      hDB (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h9, hB]))
    have : Nat.card D ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
    have h9d : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [h9d] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hob : orderOf b = 3 := by
    have h1 : orderOf b ∣ 3 := by
      have := orderOf_dvd_natCard (⟨b, hbD⟩ : D)
      rwa [Subgroup.orderOf_mk, hDcard] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  have hDz : D = Subgroup.zpowers b := (Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hbD) (by rw [Nat.card_zpowers, hob, hDcard])).symm
  have h9 : (Nat.card X).factorization 3 = 2 :=
    Sec13.Item138Proof.factorization_card_three_eq_two le_rfl hiso (by simp; omega)
  set S : Sylow 3 X := Sylow.ofCard B (by rw [hB, h9]; norm_num) with hS
  obtain ⟨g, hgN, hgb⟩ := Sec19.Step1915WProof.ks1917Lie3Fusion X p 1 le_rfl hiso
    (by simpa using h91) (by simpa using h98) S b hbB hb1
  by_contra hcon
  push Not at hcon
  have hgR := hcon g hgN
  apply hgb
  rw [← hDz]
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hgN b).mp hbB, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hr' : g⁻¹ * r * g⁻¹⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (inv_mem hgR) r).mp hr
  have hc := Subgroup.mem_centralizer_iff.mp hbD.2 _ hr'
  calc r * (g * b * g⁻¹) = g * ((g⁻¹ * r * g⁻¹⁻¹) * b) * g⁻¹ := by group
    _ = g * (b * (g⁻¹ * r * g⁻¹⁻¹)) * g⁻¹ := by rw [hc]
    _ = g * b * g⁻¹ * r := by group

end Abstract

end Proof17Res7

end CFSG.RankThree.PartTwo.Sec17
