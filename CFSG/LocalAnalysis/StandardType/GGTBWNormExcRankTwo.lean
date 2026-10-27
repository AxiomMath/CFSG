module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormLowRank
public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankE6
public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankE7
public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankE8
public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration

namespace ExcRankTwoWNorm

theorem not_orderOf_dvd {p q k : ℕ} (hq : 0 < q) (h : ¬ p ∣ q ^ k - 1) :
    ¬ orderOf ((q : ℕ) : ZMod p) ∣ k := by
  intro hd
  apply h
  have h1 : ((q : ZMod p)) ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, h1,
    Nat.cast_one, sub_self]

theorem not_orderOf_dvd_six_of_not_dvd_cube_add_one {p q : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ q ^ 3 + 1) :
    ¬ (orderOf ((q : ℕ) : ZMod p) ∣ 6 ∧ ¬ orderOf ((q : ℕ) : ZMod p) ∣ 3) := by
  have : Fact p.Prime := ⟨hp⟩
  rintro ⟨h6, h3⟩
  apply h
  have h6' : ((q : ZMod p)) ^ 6 = 1 := orderOf_dvd_iff_pow_eq_one.mp h6
  have h3' : ((q : ZMod p)) ^ 3 ≠ 1 := fun h3' => h3 (orderOf_dvd_iff_pow_eq_one.mpr h3')
  have hm : ((q : ZMod p) ^ 3 - 1) * ((q : ZMod p) ^ 3 + 1) = 0 := by linear_combination h6'
  have hz : (q : ZMod p) ^ 3 + 1 = 0 := (mul_eq_zero.1 hm).resolve_left (sub_ne_zero.2 h3')
  exact (ZMod.natCast_eq_zero_iff (q ^ 3 + 1) p).1 (by push_cast; exact hz)

theorem three_dvd_two_pow_sq_sub_one (n : ℕ) : 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have e : (2 ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have h : 1 ≡ 4 ^ n [MOD 3] := by
    have h4 := (show 4 ≡ 1 [MOD 3] by decide).pow n
    rw [one_pow] at h4
    exact h4.symm
  rw [e]
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h

theorem degCount_E8_le_two {e : ℕ} (h4 : ¬ e ∣ 4) (h6 : ¬ e ∣ 6) : degCount .E8 e ≤ 2 := by
  by_cases h30 : e ≤ 30
  · have key : ∀ e ≤ 30, ¬ e ∣ 4 → ¬ e ∣ 6 → degCount .E8 e ≤ 2 := by decide
    exact key e h30 h4 h6
  · have h0 : degCount .E8 e = 0 := by
      by_contra hne
      exact h30 (le_thirty_of_degCount_pos (by simp) (Nat.pos_of_ne_zero hne))
    omega

theorem degCount_E7_le_two {e : ℕ} (h6 : ¬ e ∣ 6) : degCount .E7 e ≤ 2 := by
  by_cases h30 : e ≤ 30
  · have key : ∀ e ≤ 30, ¬ e ∣ 6 → degCount .E7 e ≤ 2 := by decide
    exact key e h30 h6
  · have h0 : degCount .E7 e = 0 := by
      by_contra hne
      exact h30 (le_thirty_of_degCount_pos (by simp) (Nat.pos_of_ne_zero hne))
    omega

theorem degCount_E6_le_two {e : ℕ} (h2 : ¬ e ∣ 2) (h3 : ¬ e ∣ 3) : degCount .E6 e ≤ 2 := by
  by_cases h30 : e ≤ 30
  · have key : ∀ e ≤ 30, ¬ e ∣ 2 → ¬ e ∣ 3 → degCount .E6 e ≤ 2 := by decide
    exact key e h30 h2 h3
  · have h0 : degCount .E6 e = 0 := by
      by_contra hne
      exact h30 (le_thirty_of_degCount_pos (by simp) (Nat.pos_of_ne_zero hne))
    omega

theorem degCountTw_le_two {e : ℕ} (h2 : ¬ e ∣ 2) (h6 : ¬ (e ∣ 6 ∧ ¬ e ∣ 3)) :
    degCountTw e ≤ 2 := by
  by_cases h60 : e ≤ 60
  · have key : ∀ e ≤ 60, ¬ e ∣ 2 → ¬ (e ∣ 6 ∧ ¬ e ∣ 3) → degCountTw e ≤ 2 := by decide
    exact key e h60 h2 h6
  · have h0 : degCountTw e = 0 := by
      by_contra hne
      exact h60 (le_sixty_of_degCountTw_pos (Nat.pos_of_ne_zero hne))
    omega

theorem ggTorusWNormSC_of_outdiagPrime_rankLE {p : ℕ} (hp : p.Prime) {R G : Type} [Group R]
    [Group G] {I : Set (MulAut R)} (hZ : Subgroup.center R = ⊥) (hI : GGOutdiagPrime p R I)
    (e : R ≃* G) (hrank : GGElemAbelianRankLE G p 2) : GGTorusWNormSC p R I := by
  apply ggTorusWNormSC_of_card_lt
  intro X hXI hX
  let j : R →* MulAut R := MulAut.conj
  have hj : Function.Injective j := by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : a * g * a⁻¹ = b * g * b⁻¹ := congrArg (fun f : MulAut R => f g) hab
      calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
        _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [hg]
        _ = a⁻¹ * b * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact inv_mul_eq_one.mp hc
  have hXj : X ≤ j.range := fun x hx => hI x (hXI hx) (hX.2 x hx)
  let E : Subgroup R := X.comap j
  have hEX : E.map j = X := Subgroup.map_comap_eq_self hXj
  have hE : IsElemAbelian p E := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hj ?_)⟩⟩, fun x hx => hj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hX x.2 y.2
    · rw [map_pow, map_one]
      exact hX.2 _ hx
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card X := by
    rw [Subgroup.card_map_of_injective e.injective, ← hEX, Subgroup.card_map_of_injective hj]
  have h2 := hrank _ (TableB.isElemAbelian_map hE e.toMonoidHom)
  rw [hcard] at h2
  exact h2.trans_lt (Nat.pow_lt_pow_right hp.one_lt (by norm_num))


theorem ggTorusWNormSC_recipe_E8_rankTwo {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (h2 : degCount .E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 2) :
    GGTorusWNormSC p (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) :=
  ggTorusWNormSC_of_outdiagPrime_rankLE hp (TableBExc.center_recipeGroup_eq_bot .E8 K)
    (fun φ hφ _ => by
      obtain ⟨x, rfl⟩ := TableBExc.idImage_subset_inn_E8 K hφ
      exact ⟨x, rfl⟩)
    (TableBExc.recipeEquiv .E8 K)
    (fun E hE => (rankLE_E8 hp hp2 rfl E hE).trans (Nat.pow_le_pow_right hp.pos h2))

theorem ggTorusWNormSC_recipe_E7_rankTwo {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (h2 : degCount .E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 2) :
    GGTorusWNormSC p (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) :=
  ggTorusWNormSC_of_outdiagPrime_rankLE hp (TableBExc.center_recipeGroup_eq_bot .E7 K)
    (fun φ hφ _ => by
      obtain ⟨x, rfl⟩ := TableBExc.idImage_subset_inn_E7 K hφ
      exact ⟨x, rfl⟩)
    (TableBExc.recipeEquiv .E7 K)
    (fun E hE => (rankLE_E7 hp hp2 rfl E hE).trans (Nat.pow_le_pow_right hp.pos h2))

theorem ggTorusWNormSC_recipe_E6_rankTwo {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h2 : degCount .E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 2) :
    GGTorusWNormSC p (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) :=
  ggTorusWNormSC_of_outdiagPrime_rankLE hp (TableBExc.center_recipeGroup_eq_bot .E6 K)
    (TableBExc.ggOutdiagPrime_E6 (K := K) hp hp3) (TableBExc.recipeEquiv .E6 K)
    (fun E hE => (rankLE_E6 hp hp2 rfl E hE).trans (Nat.pow_le_pow_right hp.pos h2))

theorem ggTorusWNormSC_recipe_twE6_rankTwo {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h2 : degCountTw (orderOf (((2 ^ n : ℕ)) : ZMod p)) ≤ 2) :
    GGTorusWNormSC p (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobeniusEquiv_def K 2 n c
  obtain ⟨ε, -⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  exact ggTorusWNormSC_of_outdiagPrime_rankLE hp (TwE6Delta.center_recipeR_eq_bot hn hK)
    (TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3) ε.symm
    (fun E hE => (rankLE_twistedE6 Nat.prime_two hn K hK σ hσ hp hp2 rfl E hE).trans
      (Nat.pow_le_pow_right hp.pos h2))

theorem largeEvenLabelAll_wnorm_E8_rankTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (htag : lab.tag = .E8) (h4 : ¬ p ∣ (2 ^ lab.n) ^ 4 - 1)
    (h6 : ¬ p ∣ (2 ^ lab.n) ^ 6 - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag h4 h6 ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  refine ggTorusWNormSC_recipe_E8_rankTwo hp hp2 (degCount_E8_le_two ?_ ?_) <;> rw [hK]
  · exact not_orderOf_dvd (by positivity) h4
  · exact not_orderOf_dvd (by positivity) h6

theorem largeEvenLabelAll_wnorm_E7_rankTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (htag : lab.tag = .E7) (h6 : ¬ p ∣ (2 ^ lab.n) ^ 6 - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag h6 ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  refine ggTorusWNormSC_recipe_E7_rankTwo hp hp2 (degCount_E7_le_two ?_)
  rw [hK]
  exact not_orderOf_dvd (by positivity) h6

theorem largeEvenLabelAll_wnorm_E6_rankTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (htag : lab.tag = .E6) (h2 : ¬ p ∣ (2 ^ lab.n) ^ 2 - 1)
    (h3 : ¬ p ∣ (2 ^ lab.n) ^ 3 - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact h2 (three_dvd_two_pow_sq_sub_one lab.n)
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag h2 h3 ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  refine ggTorusWNormSC_recipe_E6_rankTwo hp hp2 hp3 (degCount_E6_le_two ?_ ?_) <;> rw [hK]
  · exact not_orderOf_dvd (by positivity) h2
  · exact not_orderOf_dvd (by positivity) h3

theorem largeEvenLabelAll_wnorm_twE6_rankTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (htag : lab.tag = .twE6) (hn : 1 ≤ lab.n)
    (h2 : ¬ p ∣ (2 ^ lab.n) ^ 2 - 1) (h3 : ¬ p ∣ (2 ^ lab.n) ^ 3 + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact h2 (three_dvd_two_pow_sq_sub_one lab.n)
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag hn h2 h3 ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  exact ggTorusWNormSC_recipe_twE6_rankTwo hn hK hp hp2 hp3
    (degCountTw_le_two (not_orderOf_dvd (by positivity) h2)
      (not_orderOf_dvd_six_of_not_dvd_cube_add_one hp h3))

theorem largeEvenLabelAll_wnorm_exc_rankTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : (lab.tag = .E8 ∧ ¬ p ∣ (2 ^ lab.n) ^ 4 - 1 ∧ ¬ p ∣ (2 ^ lab.n) ^ 6 - 1) ∨
      (lab.tag = .E7 ∧ ¬ p ∣ (2 ^ lab.n) ^ 6 - 1) ∨
      (lab.tag = .E6 ∧ ¬ p ∣ (2 ^ lab.n) ^ 2 - 1 ∧ ¬ p ∣ (2 ^ lab.n) ^ 3 - 1) ∨
      (lab.tag = .twE6 ∧ ¬ p ∣ (2 ^ lab.n) ^ 2 - 1 ∧ ¬ p ∣ (2 ^ lab.n) ^ 3 + 1)) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases h with ⟨ht, h4, h6⟩ | ⟨ht, h6⟩ | ⟨ht, h2, h3⟩ | ⟨ht, h2, h3⟩
  · exact largeEvenLabelAll_wnorm_E8_rankTwo hp hp2 ht h4 h6
  · exact largeEvenLabelAll_wnorm_E7_rankTwo hp hp2 ht h6
  · exact largeEvenLabelAll_wnorm_E6_rankTwo hp hp2 ht h2 h3
  · exact largeEvenLabelAll_wnorm_twE6_rankTwo hp hp2 ht hlab.1 h2 h3

end ExcRankTwoWNorm

end CFSG.StandardType

end
