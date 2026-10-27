module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem6Comp
public import CFSG.LieType.Chevalley.ChevalleySplitBN

public section

namespace CFSG.Quasithin.H13.NQCat.G24

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {K : Type} [Field K] [Finite K]

theorem not_dvd_card_torusGroup_of
    (τ : Tag) {p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ Nat.card K - 1) :
    ¬ p ∣ Nat.card (torusGroup τ K) := by
  intro h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h
  apply hp
  rw [← hx, ← Subgroup.orderOf_coe]
  exact orderOf_dvd_of_pow_eq_one
    (pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup x.2))

theorem not_seven_dvd_card_parabolicSubgroup
    (hK : Nat.card K = 4) (j : Fin (Tag.rank .G2)) :
    ¬ 7 ∣ Nat.card (parabolicSubgroup .G2 K {j}) := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcard := (standard_parabolic_cells .G2 K).2.2.2.2.2.2 {j}
  have hs : simple Tag.G2 j ∈ parabolicWeylGroup Tag.G2 {j} :=
    subset_closure ⟨j, rfl, rfl⟩
  have hne : (1 : WeylGroup Tag.G2) ≠ simple Tag.G2 j :=
    fun h => (coxeterSystem Tag.G2).simple_ne_one j h.symm
  have : Fintype ↥(parabolicWeylGroup Tag.G2 {j}) := Fintype.ofFinite _
  have huniv : (Finset.univ : Finset ↥(parabolicWeylGroup Tag.G2 {j})) =
      {1, ⟨simple Tag.G2 j, hs⟩} := by
    ext w
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    rcases mem_parabolicWeylGroup_singleton w.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hsum : ∑ᶠ w : ↥(parabolicWeylGroup Tag.G2 {j}),
      Nat.card K ^ (coxeterSystem Tag.G2).length w = 5 := by
    rw [finsum_eq_sum_of_fintype, huniv,
      Finset.sum_pair (fun h => hne (congrArg Subtype.val h)), hK]
    simp [CoxeterSystem.length_one, CoxeterSystem.length_simple]
  rw [hcard, hsum]
  intro h7
  rcases (Nat.Prime.dvd_mul Fact.out).1 h7 with h | h
  · rcases (Nat.Prime.dvd_mul Fact.out).1 h with h | h
    · exact not_dvd_card_torusGroup_of (K := K) Tag.G2 (p := 7) (by rw [hK]; norm_num) h
    · rw [hK] at h
      have := (Nat.Prime.dvd_of_dvd_pow Fact.out h)
      norm_num at this
  · norm_num at h

theorem not_seven_dvd_card_of_normalizer_le
    (hK : Nat.card K = 4) {P : Subgroup (adjointGroup .G2 K)} (hP : P ≠ ⊤)
    (S₀ : Sylow 2 (adjointGroup .G2 K))
    (hS₀ : normalizer ((S₀ : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K)) ≤ P) :
    ¬ 7 ∣ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 2) (by norm_num) (by rw [hK]; norm_num)
  have := finite_modGL (τ := Tag.G2) (K := K)
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 (posUnipotent_le_adjointGroup (K := K))
    (card_posUnipotent (τ := Tag.G2) (K := K))
  set U := (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) with hU
  have hBC : borelGroup Tag.G2 K ≤ adjointGroup Tag.G2 K :=
    borelGroup_le_adjointGroup' (τ := Tag.G2) (K := K)
  have hBN : (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) ≤
      normalizer (U : Set (adjointGroup Tag.G2 K)) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro u
    rw [hU, mem_subgroupOf, mem_subgroupOf]
    simp only [coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (sup_le (torusGroup_le_normalizer_posUnipotent)
      le_normalizer (mem_subgroupOf.mp hb)) u
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup Tag.G2 K) (hUp.toSylow hUi) S₀
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hS₀U : (S₀ : Subgroup (adjointGroup Tag.G2 K)) = U.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hBP' : (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) ≤ P' := by
    intro b hb
    have hgb : g * b * g⁻¹ ∈ P := by
      apply hS₀
      rw [hS₀U, ← map_equiv_normalizer_eq]
      exact ⟨b, hBN hb, rfl⟩
    refine ⟨g * b * g⁻¹, hgb, ?_⟩
    change g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b
    group
  have hid : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id (adjointGroup Tag.G2 K) := by
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  have hP'ne : P' ≠ ⊤ := by
    intro h
    apply hP
    have h1 := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h
    rwa [hP', Subgroup.map_map, hid, Subgroup.map_id,
      map_top_of_surjective _ (MulAut.conj g).surjective] at h1
  have hcardP : Nat.card P' = Nat.card P := by
    rw [hP', MulEquiv.toMonoidHom_eq_coe, Subgroup.card_map_of_injective
      (MulAut.conj g⁻¹).injective]
  set A := P'.map (adjointGroup Tag.G2 K).subtype with hA
  have hBA : borelGroup Tag.G2 K ≤ A := fun b hb =>
    ⟨⟨b, hBC hb⟩, hBP' (mem_subgroupOf.mpr hb), rfl⟩
  have hAC : A ≤ adjointGroup Tag.G2 K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hAne : A ≠ adjointGroup Tag.G2 K := by
    intro h
    apply hP'ne
    rw [eq_top_iff]
    intro x _
    have hx : (x : ModGL Tag.G2 K) ∈ A := by
      rw [h]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← Subtype.ext hyx]
  have hAeq := (borel_overgroup_classification Tag.G2 K).1 A hBA hAC
  set J := {i | weylElt Tag.G2 K i 1 ∈ A} with hJ
  have hJne : J ≠ Set.univ := by
    intro h
    apply hAne
    rw [hAeq, h, (standard_parabolic_cells Tag.G2 K).2.2.2.2.2.1]
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJne
  have hcases : ∀ k : Fin (Tag.rank .G2), k = ⟨0, by decide⟩ ∨ k = ⟨1, by decide⟩ := fun k => by
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨j, hj⟩ : ∃ j : Fin (Tag.rank .G2), J ⊆ {j} := by
    rcases hcases i with rfl | rfl
    · refine ⟨⟨1, by decide⟩, fun k hk => ?_⟩
      rcases hcases k with rfl | rfl
      · exact absurd hk hi
      · rfl
    · refine ⟨⟨0, by decide⟩, fun k hk => ?_⟩
      rcases hcases k with rfl | rfl
      · rfl
      · exact absurd hk hi
  have hAle : A ≤ parabolicSubgroup Tag.G2 K {j} := by
    rw [hAeq]
    exact ((standard_parabolic_cells Tag.G2 K).2.2.2.1 J {j}).2 hj
  have hdvd : Nat.card A ∣ Nat.card (parabolicSubgroup Tag.G2 K {j}) :=
    Subgroup.card_dvd_of_le hAle
  have hcardA : Nat.card A = Nat.card P' := by
    rw [hA, Subgroup.card_map_of_injective (adjointGroup Tag.G2 K).subtype_injective]
  intro h7
  apply not_seven_dvd_card_parabolicSubgroup hK j
  rw [← hcardP, ← hcardA] at h7
  exact h7.trans hdvd

theorem lemCompG24_holds :
    LemCompG24 := by
  intro X _ _ hX S E hS hE hES hSE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHolds := holds_of_chevalleyExceptionalModel_untwisted hX (by decide) (by decide)
  obtain ⟨S₀, P, hP, hNP, -, -, hS₀P⟩ := hHolds E hE (hS.2.1.to_le hES)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hZ : center (adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  set ψ : X ≃* adjointGroup Tag.G2 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) with hψ
  have hPne : P.map ψ.toMonoidHom ≠ ⊤ := by
    intro h
    apply hP
    have h1 := congrArg (Subgroup.map ψ.symm.toMonoidHom) h
    rw [Subgroup.map_map, map_top_of_surjective _ ψ.symm.surjective] at h1
    rw [← h1]
    ext x
    simp
  set S₁ : Sylow 2 (adjointGroup Tag.G2 K) :=
    Sylow.mapSurjective (f := ψ.toMonoidHom)
      (show Function.Surjective ψ.toMonoidHom from ψ.surjective) S₀ with hS₁
  have hN : normalizer ((S₁ : Subgroup (adjointGroup Tag.G2 K)) : Set (adjointGroup Tag.G2 K)) ≤
      P.map ψ.toMonoidHom := by
    rw [hS₁, Sylow.coe_mapSurjective, ← map_equiv_normalizer_eq]
    exact map_mono hS₀P
  have h7 := not_seven_dvd_card_of_normalizer_le hK4 hPne S₁ hN
  rw [MulEquiv.toMonoidHom_eq_coe, Subgroup.card_map_of_injective ψ.injective] at h7
  exact fun h => h7 (h.trans (Subgroup.card_dvd_of_le hNP))

end CFSG.Quasithin.H13.NQCat.G24
