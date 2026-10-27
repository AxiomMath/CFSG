module

public import CFSG.Quasithin.Background.FFC4CaseI
public import CFSG.Quasithin.Background.B5Irr

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique

namespace B59

variable {W : Type} [CommGroup W] [Finite W]

section Arith


theorem card_statedSL_two' (K : Type) [Field K] [Finite K] :
    Nat.card ↥(Assembly.LowTwoRank.StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two K


theorem false_of_sl2_sl3 {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} {n m : ℕ} (h2 : BinaryNaturalSL L U Z 2 n) (h3 : BinaryNaturalSL L U Z 3 m) :
    False := by
  obtain ⟨K₂, _, hf₂, hc₂, π₂, hπ₂⟩ := h2
  obtain ⟨K₃, _, hf₃, hc₃, π₃, hπ₃⟩ := h3
  have hZ : 0 < Nat.card Z := Nat.card_pos
  have e₂ := card_eq_of_realizes (D := FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K₂)) rfl hπ₂
  have e₃ := card_eq_of_realizes (D := FFModel.nat (Assembly.LowTwoRank.StatedSL 3 K₃)) rfl hπ₃
  rw [card_sec_nat] at e₂ e₃
  have hq : Nat.card K₂ ^ 2 = Nat.card K₃ ^ 3 := by
    have h : Nat.card Z * Nat.card K₂ ^ 2 = Nat.card Z * Nat.card K₃ ^ 3 := by rw [← e₂, ← e₃]
    exact Nat.eq_of_mul_eq_mul_left hZ h
  have hbij₂ : Nat.card ↥(Assembly.LowTwoRank.StatedSL 2 K₂) = Nat.card ↥L :=
    Nat.card_congr (MulEquiv.ofBijective π₂
      ⟨injective_of_faithful_sec (FFModel.nat_faithful _) hπ₂, hπ₂.1⟩).toEquiv
  have hbij₃ : Nat.card ↥(Assembly.LowTwoRank.StatedSL 3 K₃) = Nat.card ↥L :=
    Nat.card_congr (MulEquiv.ofBijective π₃
      ⟨injective_of_faithful_sec (FFModel.nat_faithful _) hπ₃, hπ₃.1⟩).toEquiv
  rw [card_statedSL_two'] at hbij₂
  rw [CFSG.SectionRank.OddCover.card_statedSL_three] at hbij₃
  have h2K : 2 ≤ Nat.card K₂ := Finite.one_lt_card
  have h3K : 2 ≤ Nat.card K₃ := Finite.one_lt_card
  set a := Nat.card K₂ with ha
  set b := Nat.card K₃ with hb
  have hc : a ^ 2 = b ^ 3 := hq
  have hord : a * (a ^ 2 - 1) = b ^ 3 * (b ^ 2 - 1) * (b ^ 3 - 1) := hbij₂.trans hbij₃.symm
  rw [← hc] at hord
  have hc1 : 0 < a ^ 2 - 1 := by
    have : 4 ≤ a ^ 2 := by nlinarith
    omega
  have h1 : a * (a ^ 2 - 1) = (a ^ 2 * (b ^ 2 - 1)) * (a ^ 2 - 1) := by
    exact hord
  have h2 : a = a ^ 2 * (b ^ 2 - 1) := Nat.eq_of_mul_eq_mul_right hc1 h1
  have hb3 : 3 ≤ b ^ 2 - 1 := by
    have : 4 ≤ b ^ 2 := by nlinarith
    omega
  nlinarith

omit [Finite W] in
theorem threeRank2_sq {Ω : Type*} [Group Ω] {K X : Subgroup Ω}
    (hsq : ∀ y ∈ X, y ^ 2 ∈ K) (h : ThreeRank2 ↥X) : ThreeRank2 ↥K := by
  obtain ⟨x, y, hx1, hx3, hy3, hxy, hy⟩ := h
  have hmem : ∀ z : ↥X, z ^ 3 = 1 → (z : Ω) ∈ K := by
    intro z hz
    have hz' : (z : Ω) ^ 3 = 1 := by simpa using congrArg Subtype.val hz
    have ho : Odd (orderOf (z : Ω)) := by
      have hd : orderOf (z : Ω) ∣ 3 := orderOf_dvd_of_pow_eq_one hz'
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1 <;> rw [h1] <;> decide
    exact B1Red.mem_of_sq_mem_of_odd (hsq z z.2) ho
  have hxK := hmem x hx3
  have hyK := hmem y hy3
  refine ⟨⟨x, hxK⟩, ⟨y, hyK⟩, fun h => hx1 (Subtype.ext (by simpa using congrArg Subtype.val h)),
    Subtype.ext (by simpa using congrArg Subtype.val hx3),
    Subtype.ext (by simpa using congrArg Subtype.val hy3),
    Subtype.ext (by simpa using congrArg Subtype.val hxy), fun hz => hy ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
  refine Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext ?_⟩
  have := congrArg (fun t : ↥K => ((t : Ω))) hk
  simpa using this

theorem classify_i (hI : B58Inputs) {M : Type} [CommGroup M] [Finite M] {X K : Subgroup (MulAut M)}
    (hJ : X = ffJ X) (hne : X ≠ ⊥) (hKX : K ≤ X) (hsq : ∀ y ∈ X, y ^ 2 ∈ K)
    (hnoK : ¬ ThreeRank2 ↥K) (P2 : B51Part2 K) (P5 : B51Part5 X K) (hi : B51Case1i X K) :
    commV K ∈ IrrPlus K ⊤ ∧
      ((X = K ∧ commV K ⊔ fixV K = ⊤ ∧
          ∃ n, BinaryNaturalSL K (commV K) (fixV K ⊓ commV K) 2 n) ∨
        (X = K ∧ ∃ m, Odd m ∧ BinaryNaturalSL K (commV K) (fixV K ⊓ commV K) 3 m) ∨
        (X ≠ K ∧ commV K ⊔ fixV X = ⊤ ∧ fixV K ⊓ commV K = ⊥ ∧
          SymmetricNatural X (commV K) (fixV K ⊓ commV K) 5)) := by
  have hnoX : ¬ ThreeRank2 ↥X := fun h => hnoK (threeRank2_sq hsq h)
  obtain ⟨hirr, hpair, hT⟩ := hi
  refine ⟨hirr, ?_⟩
  obtain ⟨T, hTsyl⟩ := B5.exists_isSylowTwoOf X
  by_cases hXK : X = K
  · subst hXK
    by_cases hα : commV X ⊔ fixV X = ⊤
    · rcases pairOK_of_pair hI hnoK hpair with hn2 | ⟨m, hm, hn3⟩ | h5
      · exact Or.inl ⟨rfl, hα, hn2⟩
      · exact Or.inr (Or.inl ⟨rfl, m, hm, hn3⟩)
      · exact (false_of_alt5 hJ hne hα (inf_comm _ _) h5).elim
    · obtain ⟨hirr', hlist5, hZ3⟩ := P5.resolve_left hα
      rcases hlist5 with ⟨n, hn⟩ | h6 | h8 | h3
      · exact (false_of_sp4 hnoK hn).elim
      · exact (false_of_alt_ge_six hnoK (by norm_num) h6).elim
      · exact (false_of_alt_ge_six hnoK (by norm_num) h8).elim
      · exact Or.inr (Or.inl ⟨rfl, 1, odd_one, h3⟩)
  · rcases (hT T hTsyl).resolve_left hXK with ⟨hXKT, hn⟩
    rcases hn with ⟨n, hn5, hn8, hsym⟩ | hg2
    · obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin n) →* ↥X,
          (FFModel.symDn n).RealizesVia X (commV K) (fixV K ⊓ commV K) π := hsym
      by_cases hn5' : n = 5
      · subst hn5'
        have hα : commV K ⊔ fixV X = ⊤ := by
          by_contra hα
          obtain ⟨hirr', hlist5, hZ3⟩ := P5.resolve_left hα
          rcases hlist5 with ⟨m, hm⟩ | h6 | h8 | h3
          · exact false_of_sp4 hnoK hm
          · exact false_of_alt_ge_six hnoK (by norm_num) h6
          · exact false_of_alt_ge_six hnoK (by norm_num) h8
          · obtain ⟨K', hK', hf, hc, ρ, hρ⟩ := h3
            exact false_of_sl3_sym5 (by simpa using hc) hρ hπ
        have hZ : fixV K ⊓ commV K = ⊥ := Z_eq_bot_of_s5 hI hKX hnoX hπ P2
        exact Or.inr (Or.inr ⟨hXK, hα, hZ, ⟨π, hπ⟩⟩)
      · exact (hnoX (threeRank2_of_realizes (symDn_faithful (by omega)) hπ
          (threeRank2_perm (by omega)))).elim
    · exact (false_of_g2 hI hnoX hg2).elim

end Arith

end B59

end FFC

end CFSG.Quasithin
