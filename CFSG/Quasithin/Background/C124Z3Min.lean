module

public import CFSG.Quasithin.Background.C124Z3Basic
public import CFSG.Quasithin.Background.C126A5Core2

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.Z3

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.LieType.BorelTits
  CFSG.Quasithin.C126.A5

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_two_of_card_dvd {P : Subgroup G} {a : ℕ} (h : Nat.card ↥P ∣ 2 ^ a * 3) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p P ≤ 2 := by
  intro p hp hp2
  unfold CFSG.Open.pRank
  refine csSup_le' fun b hb => ?_
  obtain ⟨E, hEP, -, hE⟩ := hb
  have hdvd : p ^ b ∣ 2 ^ a * 3 := by
    rw [← hE]
    exact (Subgroup.card_dvd_of_le hEP).trans h
  have hcop : Nat.Coprime (p ^ b) (2 ^ a) :=
    Nat.Coprime.pow b a ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have h3 : p ^ b ∣ 3 := hcop.dvd_of_dvd_mul_left hdvd
  have h4 : p ^ b ≤ 3 := Nat.le_of_dvd (by norm_num) h3
  by_contra hb2
  push Not at hb2
  have h8 : 2 ^ 3 ≤ p ^ b :=
    (Nat.pow_le_pow_left hp.two_le 3).trans (Nat.pow_le_pow_right hp.pos hb2)
  omega

namespace Setup

variable {X R Y : Subgroup G} (s : Setup X R Y)

include s

theorem exists_order_three : ∃ x ∈ Y, orderOf x = 3 := by
  have hdvd : 3 ∣ Nat.card Y := Dvd.intro _ s.card_Y.symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 hdvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem Y_not_mem_Q {x : G} (hx3 : orderOf x = 3) : x ∉ pCoreOf 2 X := by
  intro hx
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 X ⟨x, hx⟩
  have h1 : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h2 : 3 ∣ 2 ^ k := hx3 ▸ orderOf_dvd_of_pow_eq_one h1
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
  omega

theorem Y_eq_sup {x : G} (hx : x ∈ Y) (hx3 : orderOf x = 3) :
    Y = (Y ⊓ pCoreOf 2 X) ⊔ Subgroup.zpowers x := by
  have hle : (Y ⊓ pCoreOf 2 X) ⊔ Subgroup.zpowers x ≤ Y :=
    sup_le inf_le_left ((Subgroup.zpowers_le).2 hx)
  rcases s.sandwich_Y le_sup_left hle with h | h
  · exfalso
    apply s.Y_not_mem_Q hx3
    have : x ∈ (Y ⊓ pCoreOf 2 X) ⊔ Subgroup.zpowers x :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rw [h] at this
    exact this.2
  · exact h.symm

theorem isSolvable_Y : Group.IsSolvable ↥Y := by
  obtain ⟨x, hxY, hx3⟩ := s.exists_order_three
  have hN : Subgroup.zpowers x ≤ Subgroup.normalizer ((Y ⊓ pCoreOf 2 X : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hxY, le_normalizer_pCoreOf 2 X (s.Y_le hxY)⟩
  have h2 : Group.IsSolvable ↥(Y ⊓ pCoreOf 2 X) :=
    isSolvable_of_isPGroup_two ((pCoreOf_isPGroup 2 X).to_le inf_le_right)
  have h3 : Group.IsSolvable ↥(Subgroup.zpowers x) := inferInstance
  rw [s.Y_eq_sup hxY hx3]
  exact A3.isSolvable_sup_of_le_normalizer hN

theorem isSolvable_P₁ : Group.IsSolvable ↥(Y ⊔ R₁ X R) := by
  have h1 := s.isSolvable_Y
  have h2 := isSolvable_of_isPGroup_two s.R₁_pGroup
  exact A3.isSolvable_sup_of_le_normalizer s.R₁_le_normalizer

theorem charTwo_P₁ : CharTwo (Y ⊔ R₁ X R) :=
  charTwo_of_pCore_le s.charTwo (s.Q_le_R₁.trans le_sup_right) s.P₁_le

theorem twoResidual_P₁ : twoResidual (Y ⊔ R₁ X R) = Y := by
  refine le_antisymm (twoResidual_le_of_isTwoQuotient le_sup_left s.P₁_le_normalizer
    (isTwoQuotient_of_sup_eq s.R₁_pGroup s.P₁_le_normalizer (sup_comm _ _))) ?_
  have := twoResidual_mono (le_sup_left : Y ≤ Y ⊔ R₁ X R)
  rwa [s.Y_res] at this

theorem pRank_le_two_P₁ :
    ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (Y ⊔ R₁ X R) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 s.R₁_pGroup
  have h1 := Subgroup.relIndex_mul_card (R₁ X R) (Y ⊔ R₁ X R)
  rw [inf_eq_left.2 (le_sup_right : R₁ X R ≤ Y ⊔ R₁ X R), s.relIndex_R₁_P₁] at h1
  exact pRank_le_two_of_card_dvd (a := a) (by rw [← h1, ha, mul_comm])

theorem not_P₁_le_normalizer (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    ¬ Y ⊔ R₁ X R ≤ Subgroup.normalizer (R₁ X R : Set G) := by
  intro h
  apply hYS
  have h1 : Y ≤ Subgroup.normalizer (R₁ X R : Set G) := le_sup_left.trans h
  intro y hy
  have := normalizer_le_normalizer_baum (R₁ X R) (h1 hy)
  rwa [s.baum_R₁] at this

theorem R_lt_P₁ (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    R₁ X R < Y ⊔ R₁ X R := by
  refine lt_of_le_of_ne le_sup_right fun h => s.not_P₁_le_normalizer hYS ?_
  rw [← h]
  exact Subgroup.le_normalizer

theorem minParabolic_P₁ (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    MinParabolic (Y ⊔ R₁ X R) (R₁ X R) (R₁ X R) where
  isSylow := s.sylow_P₁
  not_normal := s.not_P₁_le_normalizer hYS
  uniqueMax := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨⟨s.R_lt_P₁ hYS, fun K hK hKP => ?_⟩, le_rfl⟩, ?_⟩
    · rcases s.sandwich_P₁ hK.le hKP with h | h
      · exact absurd h hK.ne'
      · exact h
    · rintro N ⟨⟨hlt, _⟩, hRN⟩
      rcases s.sandwich_P₁ hRN hlt.le with h | h
      · exact h
      · exact absurd h hlt.ne

end Setup

end CFSG.Quasithin.C124.Z3
