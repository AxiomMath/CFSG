module

public import CFSG.RankThree.GF2n.Smith81.Lin31Two

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

theorem lin28a_three (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : n = 3) {X : Subgroup G} {x : G}
    (hs : Sit M Q Z X x) : Q ⊓ QB X ≠ ⊥ := by
  intro hQX
  have hF : LinSwapStatement := linSwapStatement_holds
  have hN : LinNonswapStatement := linNonswapStatement_holds
  have hΓ : LinGammaStatement := linGammaStatement_holds
  have hRB : LinRankBoundStatement := linRankBoundStatement_holds
  obtain ⟨W₁, W₂, hS', -, h31'⟩ := lin31Statement_holds G M Q Z B n V₁ V₂ hb hc hS (by omega)
  have S := OddSetup.of_linSetup hc hS' h31'
  have hn' : n = 2 * 1 + 1 := by omega
  have H := hc.hyp
  have h12 := smith_1_12 hs
  have hn3 : 3 ≤ n := by omega
  have hX4 : 4 ≤ Nat.card X := by
    rw [IsZConjugate.card_eq (Z := Z) hs.conj]; exact H.q4
  obtain ⟨x₀, hx₀X, hx₀1, hx₀V₁, -⟩ := exists_nonswap hX4 hs.X_sq
    (fun t ht => hF G M Q Z B n W₁ W₂ hc hS' hn3 t (h12.1 ht))
  have hs0 : Sit M Q Z X x₀ :=
    ⟨hs.hyp, hs.conj, hx₀X, hx₀1, (h12.1 hx₀X).1, fun hxQ => hx₀1 (by
      have : x₀ ∈ X ⊓ Q := ⟨hx₀X, hxQ⟩
      rw [h12.2, Subgroup.mem_bot] at this
      exact this)⟩
  have hx₀L : x₀ ∈ Lgen M (LB M Q B) :=
    hN G M Q Z B n W₁ W₂ hc hS' hn3 x₀ (h12.1 hx₀X) (by rw [hs0.x_sq]; exact Q.one_mem) hx₀V₁
  obtain ⟨hKx, -⟩ :=
    hΓ G M Q Z B X x₀ n 1 W₁ W₂ hc hS' hn' le_rfl S.sqV S.sqV' hs0 hx₀L hQX
  obtain ⟨g, hg⟩ := hs.conj
  obtain ⟨y₁, hsY, hQY⟩ := exists_sit_Y hs hQX hg
  have hQXg : QB X = conjSubgroup g Q := by rw [hg]; exact QB_conj_eq H g
  have hnormX : Subgroup.normalizer (X : Set G) = conjSubgroup g M := by
    rw [hg]; exact normalizer_conj_eq H g
  have hQYg : QB (conjSubgroup g⁻¹ Z) = conjSubgroup g⁻¹ Q := QB_conj_eq H g⁻¹
  have hLx : Lx M (conjSubgroup g⁻¹ Z) = conjSubgroup g⁻¹ (Kx Q X) := by
    unfold Lx Kx
    rw [conjSubgroup_inf, hnormX, conjSubgroup_inv_conj, hQYg]
  have hcardT : Nat.card ↥(Lx M (conjSubgroup g⁻¹ Z)) = Nat.card Z ^ (n + 1) := by
    rw [hLx, card_conjSubgroup, hKx]
  have hsq : ∀ t ∈ Lx M (conjSubgroup g⁻¹ Z), t * t = 1 := fun t ht => by
    rw [← pow_two]; exact Lx_sq_eq_one hsY hQY ht
  refine step6 hF hN hΓ hc hS' S hn' le_rfl hsY hQY _ le_rfl ?_ ?_
  · intro t ht ht1 htL
    have htQ : t ∉ Q := by
      intro htQ
      have : t ∈ Q ⊓ QB (conjSubgroup g⁻¹ Z) := ⟨htQ, ht.1⟩
      rw [hQY, Subgroup.mem_bot] at this
      exact ht1 this
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hRB G M Q Z B n W₁ W₂ hc hS' t htL htQ
      (by rw [hsq t ht]; exact Q.one_mem)
    have hk : k = 1 := by omega
    rw [hk] at hk3 hk4
    exact ⟨hk3, hk4⟩
  · rw [hcardT]
    exact Nat.pow_lt_pow_right (by have := H.q4; omega) (by omega)

end CFSG.RankThree.GF2n.Smith81
