module

public import CFSG.Quasithin.EmptyFaithful.A38c5FmDefs
public import CFSG.Quasithin.Background.A3StructureDefs

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace CFSG.Quasithin.A38c5.Fm

theorem coatom_of_isMaxParabolic2 {G : Type} [Group G] {L K : Subgroup G}
    (h : IsMaxParabolic2 L K) :
    K ≤ L ∧ K ≠ L ∧ (∀ H : Subgroup G, K ≤ H → H ≤ L → H ≠ L → H = K) ∧
      ∃ S : Subgroup G, IsSylowTwoOf S L ∧ S ≤ K := by
  obtain ⟨⟨hKL, S, hS, hSK⟩, hne, hmax⟩ := h
  refine ⟨hKL, hne, fun H hKH hHL hHne => hmax H ⟨hHL, S, hS, hSK.trans hKH⟩ hHne hKH,
    S, hS, ?_⟩
  exact fun x hx => hSK ⟨hS.1 hx, Subgroup.le_normalizer hx⟩

theorem ne_bot_of_isMaxParabolic2 {G : Type} [Group G] {L K : Subgroup G} (hL : L ≠ ⊥)
    (h : IsMaxParabolic2 L K) : K ≠ ⊥ := by
  obtain ⟨⟨hKL, S, hS, hSK⟩, -, -⟩ := h
  intro hK
  have hS1 : S = ⊥ := le_bot_iff.mp (hK ▸ fun x hx => hSK ⟨hS.1 hx, Subgroup.le_normalizer hx⟩)
  apply hL
  have hN : Subgroup.normalizer (S : Set G) = ⊤ := by
    rw [hS1]
    exact Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot
  rw [hN, inf_top_eq, hK] at hSK
  exact le_bot_iff.mp hSK

theorem alt8_sup_ne_top {K T : Subgroup P8} (hK : K ≤ alternatingGroup (Fin 8)) (hK1 : K ≠ ⊥)
    (hK2 : K ≠ alternatingGroup (Fin 8)) (hT : T ≤ Subgroup.normalizer (K : Set P8)) :
    K ⊔ T ≠ ⊤ := by
  intro htop
  have hN : Subgroup.normalizer (K : Set P8) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer hT
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hKnorm : K.Normal := Subgroup.normalizer_eq_top_iff.mp hN
  have hKn : (K.subgroupOf (alternatingGroup (Fin 8))).Normal := hKnorm.subgroupOf _
  rcases hsimple.eq_bot_or_eq_top_of_normal (K.subgroupOf (alternatingGroup (Fin 8))) with
    h | h
  · apply hK1
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hK hx⟩ : ↥(alternatingGroup (Fin 8))) ∈
        K.subgroupOf (alternatingGroup (Fin 8)) := hx
    rw [h, Subgroup.mem_bot] at hx'
    have := congrArg Subtype.val hx'
    simpa using this
  · exact hK2 (le_antisymm hK (Subgroup.subgroupOf_eq_top.mp h))

theorem card_p8 : Nat.card P8 = 40320 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_isSylowTwoOf {T : Subgroup P8} (hT : IsSylowTwoOf T ⊤) : Nat.card T = 2 ^ 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hT.2.1
  have hidx : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at this
  have hmul := Subgroup.card_mul_index T
  rw [hk, card_p8] at hmul
  have hk7 : k ≤ 7 := by
    by_contra hlt
    push Not at hlt
    have h1 : 2 ^ 8 ∣ 2 ^ k * T.index := Dvd.dvd.mul_right (pow_dvd_pow 2 hlt) _
    rw [hmul] at h1
    omega
  have hk7' : 7 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k <;> omega
  rw [hk, show k = 7 by omega]

theorem isSylowTwoOf_transitive {T : Subgroup P8} (hT : IsSylowTwoOf T ⊤) (x y : Fin 8) :
    ∃ g ∈ T, g x = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := card_isSylowTwoOf hT
  have hst : Nat.card (MulAction.stabilizer P8 x) = 5040 := by
    have h1 := Subgroup.card_mul_index (MulAction.stabilizer P8 x)
    have h8 : Nat.card (Fin 8) = 8 := by simp
    rw [MulAction.index_stabilizer_of_transitive, card_p8, h8] at h1
    omega
  let φ : MulAction.stabilizer ↥T x →* MulAction.stabilizer P8 x :=
    { toFun := fun g => ⟨(g.1 : P8), g.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : MulAction.stabilizer P8 x => (z : P8)) h))
  have hdvd : Nat.card (MulAction.stabilizer ↥T x) ∣ 5040 :=
    hst ▸ Subgroup.card_dvd_of_injective φ hφ
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 (hT.2.1.to_subgroup (MulAction.stabilizer ↥T x))
  have hj4 : j ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have h1 : 2 ^ 5 ∣ 5040 := by
      rw [hj] at hdvd
      exact (pow_dvd_pow 2 hlt).trans hdvd
    omega
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer ↥T x)
  rw [MulAction.index_stabilizer, hcard, hj] at h2
  have hge : 8 ≤ (MulAction.orbit ↥T x).ncard := by
    interval_cases j <;> omega
  have huniv : MulAction.orbit ↥T x = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      (by rw [Set.ncard_univ]; simpa using hge)
      (Set.toFinite _)
  have hy : y ∈ MulAction.orbit ↥T x := by rw [huniv]; trivial
  obtain ⟨⟨g, hg⟩, hgx⟩ := hy
  exact ⟨g, hg, hgx⟩

end CFSG.Quasithin.A38c5.Fm
