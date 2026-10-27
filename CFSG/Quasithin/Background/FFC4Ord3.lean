module

public import CFSG.Quasithin.Background.FFC4Rank
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven Matrix

theorem exists_order_three_statedSL {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] :
    ∃ x : ↥(StatedSL n K), x ≠ 1 ∧ x ^ 3 = 1 := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := fun h => by
    have := congrArg Fin.val h
    simp at this
  refine ⟨⟨rotGL (K := K) ⟨0, by omega⟩ ⟨1, by omega⟩, Subgroup.subset_closure (det_rotMatrix _ _)⟩,
    fun h => rotGL_ne_one h01 (congrArg Subtype.val h), Subtype.ext (rotGL_pow_three _ _)⟩

theorem exists_order_three_perm5 : ∃ x : Equiv.Perm (Fin 5), x ≠ 1 ∧ x ^ 3 = 1 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide, by decide⟩

theorem exists_order_three_of_factorList {X : Type} [Group X] (h : B56FactorList X) :
    ∃ x : X, x ≠ 1 ∧ x ^ 3 = 1 := by
  rcases h with h | h | h
  · obtain ⟨n, K, hK, hf, hn, hc, ⟨e⟩⟩ := h
    obtain ⟨x, hx1, hx3⟩ := exists_order_three_statedSL (n := 2) (by norm_num) (K := K)
    exact ⟨e.symm x, fun h => hx1 (e.symm.injective (h.trans (map_one _).symm)),
      by rw [← map_pow, hx3, map_one]⟩
  · obtain ⟨e⟩ := h
    obtain ⟨x, hx1, hx3⟩ := exists_order_three_perm5
    exact ⟨e.symm x, fun h => hx1 (e.symm.injective (h.trans (map_one _).symm)),
      by rw [← map_pow, hx3, map_one]⟩
  · obtain ⟨m, K, hK, hf, hm, hodd, hc, ⟨e⟩⟩ := h
    obtain ⟨x, hx1, hx3⟩ := exists_order_three_statedSL (n := 3) (by norm_num) (K := K)
    exact ⟨e.symm x, fun h => hx1 (e.symm.injective (h.trans (map_one _).symm)),
      by rw [← map_pow, hx3, map_one]⟩


section Cases

variable {W : Type} [CommGroup W]

theorem threeRank2_of_orders {H G₁ G₂ : Subgroup (MulAut W)} (h1 : G₁ ≤ H) (h2 : G₂ ≤ H)
    (hinf : G₁ ⊓ G₂ = ⊥) (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    {x : ↥G₁} {y : ↥G₂} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1) :
    ThreeRank2 ↥H :=
  ThreeRank2.of_commuting_subgroups h1 h2 hinf hcomm (x := (x : MulAut W)) (y := (y : MulAut W))
    x.2 y.2 (fun h => hx1 (Subtype.ext h)) (fun h => hy1 (Subtype.ext h))
    (by simpa using congrArg Subtype.val hx3) (by simpa using congrArg Subtype.val hy3)

theorem threeRank2_of_case3 {H : Subgroup (MulAut W)} (h : B56Case3 H) : ThreeRank2 ↥H := by
  obtain ⟨G₁, G₂, hsup, hinf, hcomm, hF₁, hF₂, -⟩ := h
  obtain ⟨x, hx1, hx3⟩ := exists_order_three_of_factorList hF₁
  obtain ⟨y, hy1, hy3⟩ := exists_order_three_of_factorList hF₂
  exact threeRank2_of_orders (hsup ▸ le_sup_left) (hsup ▸ le_sup_right) hinf hcomm hx1 hx3 hy1 hy3

theorem threeRank2_of_case4 {H : Subgroup (MulAut W)} (h : B56Case4 H) : ThreeRank2 ↥H := by
  obtain ⟨G₁, G₂, t, hH, hinf, hcomm, ⟨e⟩, hc3, -⟩ := h
  obtain ⟨x', y', hx1', hx3', -⟩ := threeRank2_alt (n := 6) le_rfl
  have hfin : Finite ↥G₂ := Nat.finite_of_card_ne_zero (by omega)
  have hnt : Nontrivial ↥G₂ := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨y, hy1⟩ := exists_ne (1 : ↥G₂)
  have hy3 : y ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥G₂) (x := y)
    rwa [hc3] at this
  refine threeRank2_of_orders (G₁ := G₁) (G₂ := G₂) ?_ ?_ hinf hcomm (x := e.symm x') (y := y)
    ?_ ?_ hy1 hy3
  · rw [hH]; exact le_sup_left.trans le_sup_left
  · rw [hH]; exact le_sup_right.trans le_sup_left
  · exact fun h => hx1' (e.symm.injective (h.trans (map_one _).symm))
  · rw [← map_pow, hx3', map_one]

theorem threeRank2_of_case5 {H : Subgroup (MulAut W)} (h : B56Case5 H) : ThreeRank2 ↥H := by
  obtain ⟨G₁, G₂, hsup, hinf, hcomm, -, ⟨e⟩, -, -, hG₂⟩ := h
  obtain ⟨x', hx1, hx3⟩ := exists_order_three_statedSL (n := 3) (by norm_num) (K := ZMod 2)
  have hy : ∃ y : ↥G₂, y ≠ 1 ∧ y ^ 3 = 1 := by
    rcases hG₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, K, hK, hf, hc, π, hπ⟩
    · obtain ⟨y', hy1, hy3⟩ := exists_order_three_statedSL (n := 3) (by norm_num) (K := ZMod 2)
      exact ⟨e₂.symm y', fun h => hy1 (e₂.symm.injective (h.trans (map_one _).symm)),
        by rw [← map_pow, hy3, map_one]⟩
    · obtain ⟨y', hy1, hy3⟩ := exists_order_three_statedSL (n := 2) (by norm_num) (K := K)
      have hinj := injective_of_faithful_sec (FFModel.nat_faithful _) hπ
      let π' : ↥(StatedSL 2 K) →* ↥G₂ := π
      have hinj' : Function.Injective π' := hinj
      exact ⟨π' y', fun h => hy1 (hinj' (h.trans (map_one π').symm)),
        by rw [← map_pow, hy3, map_one]⟩
  obtain ⟨y, hy1, hy3⟩ := hy
  exact threeRank2_of_orders (hsup ▸ le_sup_left) (hsup ▸ le_sup_right) hinf hcomm (x := e.symm x')
    (fun h => hx1 (e.symm.injective (h.trans (map_one _).symm))) (by rw [← map_pow, hx3, map_one])
    hy1 hy3

end Cases

end FFC

end CFSG.Quasithin
