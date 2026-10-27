module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKU1
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Irr
public import CFSG.HardMathSupport.Cooperstein.Proving.EvenWeightCard

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem card_eq_sq_of_naturalSection_CentKU2 {A V Z : Subgroup G} {N : Subgroup ↥A}
    {F : Type} [Field F] [Fintype F] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)}
    (h : IsNaturalSection A V Z N Γ) (hZ : Z = ⊥) :
    Nat.card ↥V = Fintype.card F ^ 2 := by
  obtain ⟨-, -, -, -, β, hβ, hβker, -⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, hZ, Subgroup.bot_subgroupOf]
  rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hinj, hβ⟩).toEquiv]
  show Nat.card (Fin 2 → F) = Fintype.card F ^ 2
  simp [Nat.card_fun, Nat.card_eq_fintype_card]

omit [Finite G] in
private theorem card_eq_sixteen_of_altNaturalSection_CentKU2 {A V Z : Subgroup G}
    {N : Subgroup ↥A} (h : IsAltNaturalSection A V Z N 5) (hZ : Z = ⊥) :
    Nat.card ↥V = 16 := by
  obtain ⟨-, -, -, -, β, hβ, hβker, -⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, hZ, Subgroup.bot_subgroupOf]
  rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hinj, hβ⟩).toEquiv]
  show Nat.card (AltHeart 5) = 16
  rw [← Nat.card_congr (Equiv.ofBijective _
    (CFSG.Quasithin.altHeart_mk_bijective (by decide : Odd 5)))]
  rw [CFSG.HardMathSupport.Cooperstein.Proving.card_evenWeight 5 (by norm_num)] <;> norm_num

omit [Finite G] in
private theorem psl2_order_strictMono_CentKU2 {a b : ℕ} (hab : a < b) :
    2 ^ a * (4 ^ a - 1) < 2 ^ b * (4 ^ b - 1) := by
  have h1 : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  have h2 : 4 ^ a ≤ 4 ^ b := Nat.pow_le_pow_right (by norm_num) hab.le
  have h3 : 4 ^ a - 1 ≤ 4 ^ b - 1 := Nat.sub_le_sub_right h2 1
  have h4 : 4 ≤ 4 ^ b := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hpos : 0 < 2 ^ b * (4 ^ b - 1) := Nat.mul_pos (by positivity) (by omega)
    simpa using hpos
  · have h5 : 4 ≤ 4 ^ a := by
      calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    calc 2 ^ a * (4 ^ a - 1) < 2 ^ b * (4 ^ a - 1) :=
          Nat.mul_lt_mul_of_pos_right h1 (by omega)
      _ ≤ 2 ^ b * (4 ^ b - 1) := Nat.mul_le_mul_left _ h3

omit [Finite G] in
private theorem psl2_order_inj_CentKU2 {a b : ℕ}
    (h : 2 ^ a * (4 ^ a - 1) = 2 ^ b * (4 ^ b - 1)) : a = b := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact absurd h (ne_of_lt (psl2_order_strictMono_CentKU2 hab))
  · rfl
  · exact absurd h.symm (ne_of_lt (psl2_order_strictMono_CentKU2 hba))

theorem isC134Case2_of_conf (s : Setting28 T M L Mm I H K n)
    {H₁ K₁ : Subgroup G} (c₁ : Conf4212 G T M L I H₁ K₁)
    (hL₁ : perfectCore (L ⊓ H₁) = perfectCore (L ⊓ H)) :
    IsC134Case 2 (K₁ ⊔ pCoreOf 2 I) (pCoreOf 2 I) K₁ := by
  set LH := perfectCore (L ⊓ H)
  have hcases := c₁.cases
  rw [hL₁] at hcases
  have hV : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (LH : Set G) = ⊥ := by
    have h := c₁.inf_centralizer_eq
    rw [hL₁] at h
    rw [← h]
    exact s.hVL
  have hn2 : 2 ≤ n := by have := s.hn1; omega
  have hLie : CFSG.Blueprint.LieModel (ModO2 LH) .PSL 2 2 n :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], s.hn⟩
  have hinsp := inspC48L2_holds G H₁ (pCoreOf 2 I) (H₁ ⊓ M) LH
    ⁅reducedAggregate (L ⊔ T), L⁆ K₁ n hn2 hLie
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  ·
    obtain ⟨n', hpsl', hrest⟩ := h1
    have hnn : n' = n :=
      psl2_order_inj_CentKU2 ((F420.card_of_statedPSL_two_two hpsl').symm.trans
        (F420.card_of_statedPSL_two_two s.hn))
    rcases hrest with hA | hB | hC
    ·
      obtain ⟨F, _, _, hFcard, hnat⟩ := hA
      have hV' := card_eq_sq_of_naturalSection_CentKU2 hnat hV
      rw [hFcard, hnn, s.hVcard] at hV'
      have h2 : 2 ^ (4 * n) = 2 ^ (n * 2) := by rw [hV', ← pow_mul]
      have h3 : 4 * n = n * 2 := Nat.pow_right_injective (le_refl 2) h2
      exfalso
      omega
    ·
      obtain ⟨-, halt⟩ := hB
      have hV' := card_eq_sixteen_of_altNaturalSection_CentKU2 halt hV
      rw [s.hVcard] at hV'
      have h2 : 2 ^ (4 * n) = 2 ^ 4 := by rw [hV'] <;> norm_num
      have h3 : 4 * n = 4 := Nat.pow_right_injective (le_refl 2) h2
      exfalso
      omega
    ·
      exact hC.2.1
  · exact (hinsp (Or.inl h2)).elim
  · exact (hinsp (Or.inr <| Or.inl h3)).elim
  · exact (hinsp (Or.inr <| Or.inr <| Or.inl h4)).elim
  · exact (hinsp (Or.inr <| Or.inr <| Or.inr <| Or.inl h5)).elim
  · exact (hinsp (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h6)).elim
  · exact (hinsp (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h7)).elim
  · exact (hinsp (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h8)).elim
  · exact (hinsp (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr h9)).elim

end CFSG.Quasithin.H13.Ch4.CentK
