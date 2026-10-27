module

public import CFSG.Quasithin.EmptyFaithful.S1469Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

@[expose] def Input14610PermFixedA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ K : Subgroup G),
    Facts14610 T M H u I I₂ → Concl14610List T M I I₂ K →
    IsAlt 6 (OTwoQuot K) → Nat.card (wOf1469 K) = 2 ^ 5 →
    wOf1469 K ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥

@[expose] def Input14610PermFixedA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ K : Subgroup G),
    Facts14610 T M H u I I₂ → Concl14610List T M I I₂ K →
    IsAlt 7 (OTwoQuot K) → Nat.card (wOf1469 K) = 2 ^ 6 →
    ∀ X : Subgroup G, X ≤ K → ¬ 7 ∣ Nat.card X → wOf1469 K ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥

omit [Finite G] in
theorem lI_le_oTwoUpper (T M I : Subgroup G) : lI T M I ≤ oTwoUpper I :=
  oTwoUpper_mono inf_le_right

theorem Setting146.not_seven_dvd_card_lI (S : Setting146 G T M) (I : Subgroup G) :
    ¬ 7 ∣ Nat.card (lI T M I) := by
  obtain ⟨e⟩ := S.hyp1281.sThree
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(Open.pCore 2 ↥(yOfL22 T M ⊔ T)) :=
    CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(yOfL22 T M ⊔ T)) 2
  obtain ⟨a, ha⟩ := hp.exists_card_eq
  have hq : Nat.card (OTwoQuot (yOfL22 T M ⊔ T)) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hLT : Nat.card ↥(yOfL22 T M ⊔ T) = 6 * 2 ^ a := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.pCore 2 ↥(yOfL22 T M ⊔ T))
    rw [ha] at this
    have hq' : Nat.card (↥(yOfL22 T M ⊔ T) ⧸ Open.pCore 2 ↥(yOfL22 T M ⊔ T)) = 6 := hq
    rw [hq'] at this
    exact this
  have hdvd : Nat.card ↥(lI T M I) ∣ Nat.card ↥(yOfL22 T M ⊔ T) :=
    Subgroup.card_dvd_of_le (((oTwoUpper_le _).trans inf_le_left).trans le_sup_left)
  intro h7
  have h76 : 7 ∣ 6 * 2 ^ a := hLT ▸ h7.trans hdvd
  have hp7 : Nat.Prime 7 := by norm_num
  rcases (Nat.Prime.dvd_mul hp7).mp h76 with h | h
  · omega
  · have := (Nat.prime_dvd_prime_iff_eq hp7 Nat.prime_two).mp (hp7.dvd_of_dvd_pow h)
    omega

theorem input14610PermFixed_of_narrow (i6 : Input14610PermFixedA6) (i7 : Input14610PermFixedA7) :
    Input14610PermFixed := by
  intro G _ _ T M H u I I₂ K c hK hperm
  have hlK : lI T M I ≤ K := hK.eq_residual ▸ lI_le_oTwoUpper T M I
  rcases hperm with ⟨hA, hW⟩ | ⟨hA, hW⟩
  · intro hbot
    apply i6 G T M H u I I₂ K c hK hA hW
    rw [eq_bot_iff] at hbot ⊢
    exact fun x hx => hbot ⟨hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hlK) hx.2⟩
  · exact i7 G T M H u I I₂ K c hK hA hW (lI T M I) hlK
      (Setting146.not_seven_dvd_card_lI c.setting I)

end CFSG.Quasithin
