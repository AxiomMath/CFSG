module

public import CFSG.RankThree.PartOne.S11d.Sec109Common
public import CFSG.RankThree.PartOne.S11d.Facts11

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.Blueprint
open scoped commutatorElement

theorem InducesFieldAut.mul_centralizer {G : Type} [Group G] {p : ℕ} {u z : G} {J : Subgroup G}
    (h : InducesFieldAut p u J) (hz : z ∈ centralizer (J : Set G))
    (hp : (u * z) ^ p ∈ J ⊔ centralizer (J : Set G)) : InducesFieldAut p (u * z) J := by
  obtain ⟨hN, hnot, -, t, n, f, hf, hmodel, hfix⟩ := h
  have hzN : z ∈ normalizer (J : Set G) := centralizer_le_normalizer _ hz
  have hzJ : z ∈ J ⊔ centralizer (J : Set G) := Subgroup.mem_sup_right hz
  have hEq : J ⊓ centralizer ({u * z} : Set G) = J ⊓ centralizer ({u} : Set G) := by
    ext g
    simp only [mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hg, hgc⟩
      refine ⟨hg, ?_⟩
      have hgz : g * z = z * g := mem_centralizer_iff.mp hz g hg
      have : g * u * z = u * g * z := by
        calc g * u * z = g * (u * z) := by rw [mul_assoc]
          _ = (u * z) * g := hgc
          _ = u * (z * g) := by rw [mul_assoc]
          _ = u * (g * z) := by rw [hgz]
          _ = u * g * z := by rw [mul_assoc]
      exact mul_right_cancel this
    · rintro ⟨hg, hgc⟩
      refine ⟨hg, ?_⟩
      have hgz : g * z = z * g := mem_centralizer_iff.mp hz g hg
      calc g * (u * z) = (g * u) * z := by rw [mul_assoc]
        _ = (u * g) * z := by rw [hgc]
        _ = u * (g * z) := by rw [mul_assoc]
        _ = u * (z * g) := by rw [hgz]
        _ = (u * z) * g := by rw [mul_assoc]
  refine ⟨(Subgroup.mul_mem _ hN hzN), ?_, hp, t, n, f, hf, hmodel, ?_⟩
  · intro hmem
    apply hnot
    have := Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hzJ)
    simpa using this
  · let P : Subgroup G → Prop := fun X =>
      LieModel (↥(inSubgroup perfectResidual X) ⧸ Subgroup.center ↥(inSubgroup perfectResidual X))
        t n 2 f ∨
      (t = .twistedF4 ∧ n = 0 ∧ f = 1 ∧
        LieModel (↥(inSubgroup perfectResidual X) ⧸
          Subgroup.center ↥(inSubgroup perfectResidual X)) .Tits 0 2 1)
    have key : ∀ X Y : Subgroup G, X = Y → P X → P Y := by
      intro X Y hXY
      subst hXY
      exact id
    exact key _ _ hEq.symm hfix

@[expose] def FieldAutCoset : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J : Subgroup G) (a d : G),
    p.Prime → 5 ≤ p → CFSG.IsQuasisimple ↥J → EvenLieType (↥J ⧸ Subgroup.center ↥J) →
    ¬ p ∣ Nat.card (Subgroup.center ↥J) → InducesFieldAut p a J → a ^ p = 1 →
    FieldAutRank p J a → d ∈ J → d ^ p = 1 →
    a * d = d * a → ∀ s : ℤ, ¬ (p : ℤ) ∣ s → InducesFieldAut p (a ^ s * d) J

@[expose] def FieldCaseTail : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L B : Subgroup G) (n : ℕ),
    Sec109.Config p A c L B n → ∀ (b : G) (S K : Subgroup G), Sec109.Witness A c B b S →
      K ∈ sectionTenAt p (sectionTenZeroStar p A) b → S ≤ K →
      EvenLieType (K ⧸ Subgroup.center K) → ¬ p ∣ Nat.card (Subgroup.center K) →
      ∀ a d : G, a ∈ A → d ∈ A → d ≠ 1 →
        A = zpowers a ⊔ zpowers b ⊔ zpowers d → zpowers d = A ⊓ K → InducesFieldAut p a K →
        c ∉ zpowers b ⊔ zpowers d → InducesFieldAut p c K → False

namespace Sec109

theorem fieldCaseImpossible_of (hLS : FieldAutCoset) (htail : FieldCaseTail) :
    FieldCaseImpossible := by
  intro G _ _ p A c L B n h b S K hW hK hSK hEven hZ a d haA hdA hd1 hAeq hdK hfa hc
  have hp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 : 3 < p := sectionTenSetup_three_lt h.setup
    by_contra hlt
    have : p = 4 := by omega
    exact absurd (this ▸ hp) (by decide)
  have hbB : b ∈ B := hW.b_mem
  have hbA : b ∈ A := h.B_le_A hbB
  have hKθ : K ∈ thetaComponentsAt p b := hK.2
  have hKF : K ≤ centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.mp hKθ).1
  have hdK' : d ∈ K := (mem_inf.mp (hdK ▸ mem_zpowers d)).2
  have hq : CFSG.IsQuasisimple ↥K :=
    S11d.isQuasisimple_of_evenLie (isPerfect_of_mem_thetaComponentsAt hKθ) hEven
  have hap : a ^ p = 1 := h.pow_p_eq_one haA
  have hdp : d ^ p = 1 := h.pow_p_eq_one hdA
  have hcA : c ∈ A := h.c_mem
  have hcomm_d : ∀ β ∈ zpowers a ⊔ zpowers b, Commute β d := by
    intro β hβ
    have hβA : β ∈ A := by
      rw [hAeq]
      exact Subgroup.mem_sup_left hβ
    exact h.A_comm β hβA d hdA
  have hcmem : c ∈ (zpowers a ⊔ zpowers b) ⊔ zpowers d := by rw [← hAeq]; exact hcA
  obtain ⟨β, hβ, k, hck⟩ := (S11d.mem_sup_zpowers_iff hcomm_d).mp hcmem
  obtain ⟨i, j, hij⟩ := (S11d.mem_zpowers_sup_zpowers_iff
    (show Commute a b from h.A_comm a haA b hbA)).mp hβ
  have hi : ¬ (p : ℤ) ∣ i := by
    intro hdiv
    obtain ⟨m, hm⟩ := hdiv
    apply hc
    have h1 : a ^ i = 1 := by rw [hm, zpow_mul, zpow_natCast, hap, one_zpow]
    have : c = b ^ j * d ^ k := by rw [hck, hij, h1, one_mul]
    rw [this]
    exact Subgroup.mul_mem_sup (zpow_mem (mem_zpowers b) j) (zpow_mem (mem_zpowers d) k)
  have hdkK : d ^ k ∈ K := zpow_mem hdK' k
  have hdkp : (d ^ k) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdp, one_zpow]
  have hadk : a * d ^ k = d ^ k * a :=
    (Commute.zpow_right (show Commute a d from h.A_comm a haA d hdA) k).eq
  have hbp : b ^ p = 1 := h.pow_p_eq_one hbA
  have hbC : b ∈ centralizer (K : Set G) := by
    rw [mem_centralizer_iff]
    intro g hg
    exact mem_centralizer_singleton_iff.mp (hKF hg)
  have hrank : FieldAutRank p K a :=
    ⟨(sectionTenSetup_evenRank_eq h.setup).le, b, hbC, hW.b_ne_one, hbp,
      h.A_comm a haA b hbA⟩
  have hind := hLS G p K a (d ^ k) hp hp5 hq hEven hZ hfa hap hrank hdkK hdkp hadk i hi
  have hz : b ^ j ∈ centralizer (K : Set G) := by
    rw [mem_centralizer_iff]
    intro g hg
    have hgb : g * b = b * g := mem_centralizer_singleton_iff.mp (hKF hg)
    exact ((Commute.zpow_right (show Commute g b from hgb) j).eq)
  have hbd : b ^ j * d ^ k = d ^ k * b ^ j :=
    ((show Commute b d from h.A_comm b hbA d hdA).zpow_zpow j k).eq
  have hceq : c = a ^ i * d ^ k * b ^ j := by
    rw [hck, hij, mul_assoc, hbd, ← mul_assoc]
  have hcp : c ^ p = 1 := h.pow_p_eq_one hcA
  have hcind : InducesFieldAut p c K := by
    rw [hceq]
    refine hind.mul_centralizer hz ?_
    rw [← hceq, hcp]
    exact Subgroup.one_mem _
  exact htail G p A c L B n h b S K hW hK hSK hEven hZ a d haA hdA hd1 hAeq hdK hfa hc hcind

end Sec109

end CFSG.RankThree.PartOne
