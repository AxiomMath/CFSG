module

public import CFSG.Quasithin.Background.F918Z4c1PSL
public import CFSG.Quasithin.Background.F918Z4c1Sz
public import CFSG.Quasithin.Background.F918Z4c1J1
public import CFSG.Quasithin.Background.F918Z4c2Main
public import CFSG.Quasithin.Background.F918Z4e
public import CFSG.Quasithin.Background.F918Z5A3
public import CFSG.Quasithin.Background.F918Z7aNum

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace Z7a

theorem two_le_of_isPSL_two_two {L : Type} [Group L] {n : ℕ} (h : IsPSL 2 2 n L) : 2 ≤ n := by
  obtain ⟨⟨-, hn1, -, hne, -⟩, -⟩ := h
  by_contra hlt
  have hn : n = 1 := by omega
  subst hn
  exact hne rfl

theorem three_le_of_isSz {L : Type} [Group L] {n : ℕ} (h : IsSz n L) : 3 ≤ n := by
  obtain ⟨-, a, ha, -, -, -, hna, -⟩ := h
  omega

theorem a38_cases {L : Type} [Group L] (h : A38Types L) :
    (∃ n, 2 ≤ n ∧ IsPSL 2 2 n L) ∨ (∃ n, 3 ≤ n ∧ IsSz n L) ∨ IsSporadic .J1 L ∨
      ∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ IsPSL 2 p 1 L := by
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, hp, hp3, hpsl⟩
  · exact Or.inl ⟨n, two_le_of_isPSL_two_two hn, hn⟩
  · exact Or.inr (Or.inl ⟨n, three_le_of_isSz hn, hn⟩)
  · exact Or.inr (Or.inr (Or.inl hJ))
  · rcases Z4e.eq_five_or_seven_le hp hp3 with rfl | h7
    · exact Or.inl ⟨2, le_rfl, Z4e.isPSL_two_two_two_of_isPSL_two_five hpsl⟩
    · exact Or.inr (Or.inr (Or.inr ⟨p, hp, h7, hpsl⟩))

theorem false_of_psl2_two {L : Type} [Group L] [Finite L] {n : ℕ} (hn : 2 ≤ n)
    (hL : IsPSL 2 2 n L) {F : Type} [Field F] [Finite F] {e d : ℕ} (hF : Nat.card F = 2 ^ e)
    (ρ : L →* Matrix.GeneralLinearGroup (Fin d) F) (hρ : Function.Injective ρ) (hd : 3 ≤ d)
    (hKI : d * (d - 1) * e ≤ 4 * n + 2) : False := by
  have hde : 2 * n ≤ d * e := by
    by_cases h3 : n = 3
    · subst h3
      have := Z4c2.six_le_of_psl2_eight hL hF ρ hρ
      omega
    · exact two_mul_le_of_psl2_two hn h3 hL hF ρ hρ
  obtain ⟨rfl, he⟩ := numeric_L2 hn hd hde hKI
  exact Z4c2.not_faithful_three hn hL hF he ρ hρ

theorem false_of_sz {L : Type} [Group L] [Finite L] {n : ℕ} (hn : 3 ≤ n) (hL : IsSz n L)
    {F : Type} [Field F] [Finite F] {e d : ℕ} (hF : Nat.card F = 2 ^ e)
    (ρ : L →* Matrix.GeneralLinearGroup (Fin d) F) (hρ : Function.Injective ρ) (hd : 3 ≤ d)
    (hKI : d * (d - 1) * e ≤ 4 * (2 * n - 1) + 2) : False :=
  numeric_Sz hn hd (four_mul_le_of_isSz hn hL hF ρ hρ) hKI

theorem false_of_j1 {L : Type} [Group L] [Finite L]
    (hL : IsSporadic .J1 L) {F : Type} [Field F] [Finite F] {e d : ℕ} (hF : Nat.card F = 2 ^ e)
    (ρ : L →* Matrix.GeneralLinearGroup (Fin d) F) (hρ : Function.Injective ρ) (hd : 3 ≤ d)
    (hKI : d * (d - 1) * e ≤ 4 * 3 + 2) : False :=
  numeric_J1 hd (eighteen_le_of_j1 hL hF ρ hρ) hKI

theorem isPSL_three_two_of_bijective {G : Type} [Group G] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) (ρ : G →* Matrix.GeneralLinearGroup (Fin 3) F)
    (hρ : Function.Bijective ρ) : IsPSL 3 2 1 G := by
  have hu := subsingleton_units_of_card_two hF
  have hsc : StatedScalars (Fin 3) F = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro _ ⟨c, rfl⟩
    rw [Subsingleton.elim c 1, map_one]
  have hN : (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F) = ⊥ := by
    rw [hsc, Subgroup.bot_subgroupOf]
  have hSL : StatedSL 3 F = ⊤ := statedSL_eq_top_of_card_two hF 3
  let e1 : G ≃* Matrix.GeneralLinearGroup (Fin 3) F := MulEquiv.ofBijective ρ hρ
  let e2 : Matrix.GeneralLinearGroup (Fin 3) F ≃* ↥(StatedSL 3 F) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hSL.symm)
  let e3 : ↥(StatedSL 3 F) ≃* StatedProj (StatedSL 3 F) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hN.symm)
  refine ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, F, inferInstance,
    inferInstance, by simpa using hF, ⟨(e1.trans e2).trans e3⟩⟩

theorem isPSL_three_two_of_psl2_prime {L : Type} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (h7 : 7 ≤ p) (hL : IsPSL 2 p 1 L) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (ρ : L →* Matrix.GeneralLinearGroup (Fin 3) F) (hρ : Function.Injective ρ) :
    IsPSL 3 2 1 L := by
  have h2 := Z4e.two_mul_card_of_isPSL_two_odd hp (by omega) hL
  have hle : Nat.card L ≤ 168 := by
    rw [← card_gl_three_of_card_two hF]
    exact Nat.card_le_card_of_injective ρ hρ
  have hp7 : p = 7 := eq_seven_of_card_le h7 (by omega)
  subst hp7
  have hcard : Nat.card L = 168 := by
    norm_num at h2
    omega
  exact isPSL_three_two_of_bijective hF ρ
    (hρ.bijective_of_nat_card_le (by rw [card_gl_three_of_card_two hF, hcard]))

end Z7a

end CFSG.Quasithin
