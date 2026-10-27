module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoRuPCover
public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoLeavesCent
public import CFSG.Quasithin.Vol2.Ch12Sec6L12A6Num
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Ru.Native (ruData)

@[expose] def NoBigGroup (A : Type*) [Group A] : Prop :=
  ∀ H : Subgroup A, H ≠ ⊤ → 2 ^ 13 ∣ Nat.card H → 9 ∣ Nat.card H → 5 ∣ Nat.card H → False

theorem NoBigGroup.of_mulEquiv {A A' : Type*} [Group A] [Group A'] (e : A ≃* A')
    (h : NoBigGroup A) : NoBigGroup A' := by
  intro H hH h13 h9 h5
  have hne : H.map e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hH
    have := congrArg (Subgroup.map e.toMonoidHom) htop
    rw [Subgroup.map_map, Subgroup.map_top_of_surjective _ e.surjective] at this
    rwa [show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id A' by ext; simp,
      Subgroup.map_id] at this
  have hc : Nat.card (H.map e.symm.toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective e.symm.injective
  exact h _ hne (hc ▸ h13) (hc ▸ h9) (hc ▸ h5)

theorem card_sup_eq_card_quotient_mul_card {G : Type*} [Group G] [Finite G] {P Y : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (Y : Set G)) :
    Nat.card ↥(P ⊔ Y) = Nat.card (P ⧸ Y.subgroupOf P) * Nat.card Y := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hPN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hPN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient P Y hPN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Y.subgroupOf (P ⊔ Y)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : Y ≤ P ⊔ Y)).toEquiv]

theorem a6PRu_holds :
    A6PRu := by
  intro X _ _ hX Y P hYY hYq hP hPN
  obtain ⟨eX⟩ := hX
  by_contra hlt
  have hP13 : 2 ^ 13 ≤ Nat.card ↥P := not_lt.mp hlt
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  have hRu : NoBigGroup ↥(J ruData) := fun H hH h13 h9 h5 => RuP.noBigGroup_Ru H hH h13 h9 h5
  have hRuN : NoBigGroup NativeSporadic.Ru :=
    NoBigGroup.of_mulEquiv (A := ↥(J ruData)) (A' := NativeSporadic.Ru)
      (seedEquiv hF.toBaseFacts).symm hRu
  have hno : NoBigGroup X :=
    NoBigGroup.of_mulEquiv (A := NativeSporadic.Ru) (A' := X) eX.symm hRuN
  have hcardX : Nat.card X = 145926144000 :=
    (Nat.card_congr eX.toEquiv).trans CFSG.Sporadic.Ru.card_Ru
  obtain ⟨j, hYj⟩ : ∃ j : ℕ, Nat.card ↥Y = 360 * 2 ^ j := by
    have hY := card_eq_pCore_mul_of_iso hYq
    have hQ : Nat.card ↥(pCoreOf 2 Y) = Nat.card ↥(pCore 2 ↥Y) := by
      rw [pCoreOf]
      exact Subgroup.card_map_of_injective Y.subtype_injective
    obtain ⟨j, hj⟩ := (CFSG.LargeExtraspecial.AS62.isPGroup_pCoreOf 2 Y).exists_card_eq
    exact ⟨j, by rw [hY, ← hQ, hj, mul_comm]⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk13 : 13 ≤ k := by
    have h : 2 ^ 13 ≤ 2 ^ k := hk ▸ hP13
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.card (↥P ⧸ Y.subgroupOf P) = 2 ^ m := by
    have h := Subgroup.card_quotient_dvd_card (Y.subgroupOf P)
    rw [hk] at h
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
    exact ⟨m, hm⟩
  have hH : Nat.card ↥(P ⊔ Y) = 2 ^ m * (360 * 2 ^ j) := by
    rw [card_sup_eq_card_quotient_mul_card hPN, hm, hYj]
  have h13 : 2 ^ 13 ∣ Nat.card ↥(P ⊔ Y) := by
    have h1 : Nat.card ↥P ∣ Nat.card ↥(P ⊔ Y) := Subgroup.card_dvd_of_le le_sup_left
    rw [hk] at h1
    exact (pow_dvd_pow 2 hk13).trans h1
  have h9 : 9 ∣ Nat.card ↥(P ⊔ Y) := by
    rw [hH]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (by norm_num) _) _
  have h5 : 5 ∣ Nat.card ↥(P ⊔ Y) := by
    rw [hH]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (by norm_num) _) _
  have hne : P ⊔ Y ≠ ⊤ := by
    intro htop
    have h7 : 7 ∣ Nat.card ↥(P ⊔ Y) := by
      rw [htop, Subgroup.card_top, hcardX]
      norm_num
    rw [hH] at h7
    have hcop : Nat.Coprime 7 (2 ^ m * (360 * 2 ^ j)) :=
      Nat.Coprime.mul_right (Nat.Coprime.pow_right m (by norm_num))
        (Nat.Coprime.mul_right (by norm_num) (Nat.Coprime.pow_right j (by norm_num)))
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h7) (by norm_num)
  exact hno _ hne h13 h9 h5

end CFSG.Quasithin.H13.K1262Two
