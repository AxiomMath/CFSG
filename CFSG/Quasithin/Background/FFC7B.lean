module

public import CFSG.Quasithin.Background.FFC4G2
public import CFSG.Quasithin.Background.FFC6G

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Equiv Equiv.Perm

namespace B510

section Dich

variable {W : Type} [CommGroup W] [Finite W]

theorem false_of_sl3_sym5' {H L : Subgroup (MulAut W)} {U Z : Subgroup W} {K : Type} [Field K]
    [Finite K] {ρ : ↥(Assembly.LowTwoRank.StatedSL 3 K) →* ↥L}
    (hρ : (FFModel.nat (Assembly.LowTwoRank.StatedSL 3 K)).RealizesVia L U Z ρ) {π : Perm (Fin 5) →* ↥H}
    (hπ : (FFModel.symDn 5).RealizesVia H U Z π) : False := by
  have h1 := card_eq_of_realizes (D := FFModel.nat (Assembly.LowTwoRank.StatedSL 3 K)) rfl hρ
  have h2 := card_eq_of_realizes (D := FFModel.symDn 5) symDn_ker_five hπ
  rw [card_sec_nat] at h1
  rw [show Nat.card ↥(FFModel.symDn 5).sec = 16 from card_coreMod_five] at h2
  have hZ : 0 < Nat.card ↥Z := Nat.card_pos
  have hK : 2 ≤ Nat.card K := Finite.one_lt_card
  have h : Nat.card ↥Z * Nat.card K ^ 3 = Nat.card ↥Z * 16 := by rw [← h1, ← h2]
  have h3 : Nat.card K ^ 3 = 16 := Nat.eq_of_mul_eq_mul_left hZ h
  rcases Nat.lt_or_ge (Nat.card K) 3 with hk | hk
  · have : Nat.card K = 2 := by omega
    rw [this] at h3
    norm_num at h3
  · have : 3 ^ 3 ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hk 3
    omega

theorem false_of_natural_sym5 {X K : Subgroup (MulAut W)} (hKX : K ≤ X) {U Z : Subgroup W}
    (hnat : (∃ n, BinaryNaturalSL K U Z 2 n) ∨ (∃ n, BinaryNaturalSL K U Z 3 n))
    (hS : SymmetricNatural X U Z 5) : False := by
  obtain ⟨π, hπ⟩ := hS
  rcases hnat with ⟨n, K', hK', hfin, hc, ρ, hρ⟩ | ⟨n, K', hK', hfin, hc, ρ, hρ⟩
  · have : CharP K' 2 := charP_two_of_card_pow hc
    exact false_of_sl2_sym5 hKX hρ hπ
  · exact false_of_sl3_sym5' (K := K') hρ hπ

theorem m_level_dich
    (hB51 : AsB51) (hM : ∀ v : W, v ^ 2 = 1) {X K : Subgroup (MulAut W)}
    (hb : B51Hyp X K) (hKX : K ≤ X) (hsq : ∀ y ∈ X, y ^ 2 ∈ K) (hne : X ≠ ⊥)
    (hno : ¬ ThreeRank2 ↥K) :
    X = K ∨ (X ≠ K ∧ commV K ⊔ fixV X = ⊤ ∧ fixV K ⊓ commV K = ⊥ ∧
      SymmetricNatural X (commV K) (fixV K ⊓ commV K) 5) := by
  obtain ⟨P1, P2, -, -, P5, -⟩ := hB51 W hM X K hb
  have hnoX : ¬ ThreeRank2 ↥X := fun h => hno (B59.threeRank2_sq hsq h)
  obtain ⟨-, hcases⟩ := P1
  rcases hcases with hi | hii | ⟨n, hiii⟩ | hiv
  · obtain ⟨-, hcl⟩ := B59.classify_i b58Inputs hb.2.2.2.2.2 hne hKX hsq hno P2 P5 hi
    rcases hcl with ⟨hXK, -⟩ | ⟨hXK, -⟩ | h
    · exact Or.inl hXK
    · exact Or.inl hXK
    · exact Or.inr h
  · exact Or.inl hii.1
  · exact (false_of_case_iii hKX hnoX hiii.2).elim
  · exact (false_of_case_iv hKX hnoX hiv.2).elim

theorem eq_of_natural
    (hB51 : AsB51) (hM : ∀ v : W, v ^ 2 = 1) {X K : Subgroup (MulAut W)}
    (hb : B51Hyp X K) (hKX : K ≤ X) (hsq : ∀ y ∈ X, y ^ 2 ∈ K) (hne : X ≠ ⊥)
    (hno : ¬ ThreeRank2 ↥K)
    (hnat : (∃ n, BinaryNaturalSL K (commV K) (fixV K ⊓ commV K) 2 n) ∨
      (∃ n, BinaryNaturalSL K (commV K) (fixV K ⊓ commV K) 3 n)) : X = K := by
  rcases m_level_dich hB51 hM hb hKX hsq hne hno with h | ⟨-, -, -, hS⟩
  · exact h
  · exact (false_of_natural_sym5 hKX hnat hS).elim

end Dich

end B510

end FFC

end CFSG.Quasithin
