module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.LocalTypes2
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneFactsL2
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneFactsSz
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneFactsU3
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneFactsU3Torus

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

private theorem exists_neighbor_ne_of_one_lt_card {z : V}
    (h : 1 < Nat.card {w : V // Γ.Adj z w}) :
    ∀ w, Γ.Adj z w → ∃ w', Γ.Adj z w' ∧ w' ≠ w := by
  classical
  haveI : Finite {w : V // Γ.Adj z w} :=
    Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype {w : V // Γ.Adj z w} := Fintype.ofFinite _
  have h' : 1 < Fintype.card {w : V // Γ.Adj z w} := by
    simpa [Nat.card_eq_fintype_card] using h
  intro w hw
  obtain ⟨w', hw'⟩ := Fintype.exists_ne_of_one_lt_card h' (⟨w, hw⟩ : {w : V // Γ.Adj z w})
  exact ⟨w'.1, w'.2, fun hEq => hw' (Subtype.ext hEq)⟩

theorem vertexFacts_of_isLocalL2 [Finite H] {z : V} {m : ℕ} (hm : 2 ≤ m)
    (hK : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) (h : IsLocalL2 H Γ z m) :
    LocalFacts H Γ z ∧ ZassenhausFacts H Γ z ∧ CenterFacts H Γ z 1 ∧ TransitiveFacts H Γ z := by
  classical
  obtain ⟨hcard, h2, N, hN, ⟨e⟩⟩ := h
  haveI : Finite {w : V // Γ.Adj z w} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.succ_ne_zero _)
  letI : Fintype {w : V // Γ.Adj z w} := Fintype.ofFinite _
  have hΩ : Fintype.card {w : V // Γ.Adj z w} = 2 ^ m + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hlt : 1 < Nat.card {w : V // Γ.Adj z w} := by
    rw [hcard]
    have : 0 < 2 ^ m := Nat.two_pow_pos m
    omega
  let X := ↥(localGroup H Γ z)
  let π : ↥(MulAction.stabilizer H z) →* X := (localPermHom (H := H) Γ z).rangeRestrict
  haveI : Finite X := Finite.of_surjective π (MonoidHom.rangeRestrict_surjective _)
  have hπ : Function.Surjective π := MonoidHom.rangeRestrict_surjective _
  have hact : ∀ (g : ↥(MulAction.stabilizer H z)) (w : {w : V // Γ.Adj z w}),
      ((π g • w : {w : V // Γ.Adj z w}) : V) = (g : H) • (w : V) := fun _ _ => rfl
  let hL : RankOneLocal X {w : V // Γ.Adj z w} N :=
    rankOneLocal_psl2 h2 m hm N hN e hΩ
  have hZ : RankOneZassenhaus X {w : V // Γ.Adj z w} N :=
    rankOneZassenhaus_psl2 h2 m hm N hN e hΩ
  have hC : RankOneCenter X {w : V // Γ.Adj z w} N 1 :=
    rankOneCenter_psl2 h2 m hm N hN e hΩ
  have hT : RankOneTransitive X {w : V // Γ.Adj z w} N :=
    rankOneTransitive_psl2 h2 m hm N hN e hΩ
  have hR : RankOneRoot X {w : V // Γ.Adj z w} N := RankOneLocal.rankOneRoot_of_zassenhaus hL hZ
  exact ⟨localFacts_of_rankOneLocal π hπ hact hK
      (exists_neighbor_ne_of_one_lt_card hlt) hL,
    zassenhausFacts_of_rankOneZassenhaus π hπ hact hK hL hZ,
    centerFacts_of_rankOneCenter π hπ hact hK hL hR hC,
    transitiveFacts_of_rankOneTransitive π hπ hact hK hL hT⟩

theorem vertexFacts_of_isLocalSz [Finite H] {z : V} {a : ℕ}
    (ha : 1 ≤ a) (hK : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z)
    (h : IsLocalSz H Γ z a) :
    LocalFacts H Γ z ∧ ZassenhausFacts H Γ z ∧ CenterFacts H Γ z 1 := by
  classical
  obtain ⟨hcard, h2, N, hN, ⟨e⟩⟩ := h
  haveI : Finite {w : V // Γ.Adj z w} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.succ_ne_zero _)
  letI : Fintype {w : V // Γ.Adj z w} := Fintype.ofFinite _
  have hΩ : Fintype.card {w : V // Γ.Adj z w} = 2 ^ (2 * (2 * a + 1)) + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hlt : 1 < Nat.card {w : V // Γ.Adj z w} := by
    rw [hcard]
    have : 0 < 2 ^ (2 * (2 * a + 1)) := Nat.two_pow_pos _
    omega
  let X := ↥(localGroup H Γ z)
  let π : ↥(MulAction.stabilizer H z) →* X := (localPermHom (H := H) Γ z).rangeRestrict
  haveI : Finite X := Finite.of_surjective π (MonoidHom.rangeRestrict_surjective _)
  have hπ : Function.Surjective π := MonoidHom.rangeRestrict_surjective _
  have hact : ∀ (g : ↥(MulAction.stabilizer H z)) (w : {w : V // Γ.Adj z w}),
      ((π g • w : {w : V // Γ.Adj z w}) : V) = (g : H) • (w : V) := fun _ _ => rfl
  let hL : RankOneLocal X {w : V // Γ.Adj z w} N :=
    rankOneLocal_sz h2 a ha N hN e hΩ
  have hZ : RankOneZassenhaus X {w : V // Γ.Adj z w} N :=
    rankOneZassenhaus_sz h2 a ha N hN e hΩ
  have hC : RankOneCenter X {w : V // Γ.Adj z w} N 1 :=
    rankOneCenter_sz h2 a ha N hN e hΩ
  have hR : RankOneRoot X {w : V // Γ.Adj z w} N := RankOneLocal.rankOneRoot_of_zassenhaus hL hZ
  exact ⟨localFacts_of_rankOneLocal π hπ hact hK
      (exists_neighbor_ne_of_one_lt_card hlt) hL,
    zassenhausFacts_of_rankOneZassenhaus π hπ hact hK hL hZ,
    centerFacts_of_rankOneCenter π hπ hact hK hL hR hC⟩

theorem vertexFacts_of_isLocalU3 [Finite H] {z : V} {k : ℕ} (hk : 2 ≤ k) (F : Type) [Field F]
    [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2)
    (hK : FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z) (h : IsLocalU3 H Γ z k F) :
    LocalFacts H Γ z ∧ CenterFacts H Γ z (2 ^ k + 1) ∧ UnitaryFacts H Γ z (2 ^ k) := by
  classical
  obtain ⟨hcard, h2, N, hN, ⟨e⟩⟩ := h
  haveI : Finite {w : V // Γ.Adj z w} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.succ_ne_zero _)
  letI : Fintype {w : V // Γ.Adj z w} := Fintype.ofFinite _
  have hΩ : Fintype.card {w : V // Γ.Adj z w} = 2 ^ (3 * k) + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hlt : 1 < Nat.card {w : V // Γ.Adj z w} := by
    rw [hcard]
    have : 0 < 2 ^ (3 * k) := Nat.two_pow_pos _
    omega
  let X := ↥(localGroup H Γ z)
  let π : ↥(MulAction.stabilizer H z) →* X := (localPermHom (H := H) Γ z).rangeRestrict
  haveI : Finite X := Finite.of_surjective π (MonoidHom.rangeRestrict_surjective _)
  have hπ : Function.Surjective π := MonoidHom.rangeRestrict_surjective _
  have hact : ∀ (g : ↥(MulAction.stabilizer H z)) (w : {w : V // Γ.Adj z w}),
      ((π g • w : {w : V // Γ.Adj z w}) : V) = (g : H) • (w : V) := fun _ _ => rfl
  let hL : RankOneLocal X {w : V // Γ.Adj z w} N :=
    rankOneLocal_psu3 h2 k hk F hF N hN e hΩ
  have hR : RankOneRoot X {w : V // Γ.Adj z w} N :=
    rankOneRoot_psu3 h2 k hk F hF N hN e hΩ
  have hC : RankOneCenter X {w : V // Γ.Adj z w} N (2 ^ k + 1) :=
    rankOneCenter_psu3 h2 k hk F hF N hN e hΩ
  have hU : RankOneUnitary X {w : V // Γ.Adj z w} N (2 ^ k) :=
    rankOneUnitary_psu3 h2 k hk F hF N hN e hΩ
  exact ⟨localFacts_of_rankOneLocal π hπ hact hK
      (exists_neighbor_ne_of_one_lt_card hlt) hL,
    centerFacts_of_rankOneCenter π hπ hact hK hL hR hC,
    unitaryFacts_of_rankOneUnitary π hπ hact hK hL hU⟩

end CFSG.Quasithin.Stroth.WeissDelta

end
