module

public import CFSG.RankThree.PartTwo.Sec20.Contra
import CFSG.RankThree.PartTwo.Sec18.Item181b

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

structure Ctx20One (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G)
    (T : Subgroup G) : Prop extends Ctx20 G A M L N c T where
  one : ∃ H ∈ scriptHStar A M, CFSG.Open.pCoreOf 2 H ≠ ⊥ ∧ L = inSubgroup perfectResidual H ∧
    N = Subgroup.normalizer (L : Set G) ∧
    (CFSG.Open.pCoreOf 2 (Subgroup.centralizer {c}) ≠ ⊥ →
      Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ N)

@[expose] def Item204One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M}

@[expose] def Item205One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T →
      ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ ∧
      (∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
        ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G)) ∧
      (∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))) ∧
      ¬ 2 ∣ (M ⊓ N).relIndex M ∧
      ∃ T' : Subgroup G, Ctx20One G A M L N c T' ∧ T' ≤ N

@[expose] def Item208One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
      IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
        ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n

@[expose] def Item209One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N → ⁅L, vTwenty M c T⁆ = ⊥

theorem item204One_of (h : Item204) : Item204One :=
  fun G _ _ A M L N c T hT => h G A M L N c T hT.toCtx20

theorem item205One_of (h : Item205) : Item205One := by
  intro G _ _ A M L N c T hT
  obtain ⟨h1, h2, h3, h4, T', hT', hT'N⟩ := h G A M L N c T hT.toCtx20
  exact ⟨h1, h2, h3, h4, T', ⟨hT', hT.one⟩, hT'N⟩

theorem item208One_of (h : Item208) : Item208One :=
  fun G _ _ A M L N c T hT => h G A M L N c T hT.toCtx20

theorem item209One_of (h : Item209) : Item209One :=
  fun G _ _ A M L N c T hT => h G A M L N c T hT.toCtx20

variable {G : Type} [Group G] [Finite G]

theorem rank3II_20_1_contra_one (h204 : Item204One) (h205 : Item205One) (h208 : Item208One)
    (h209 : Item209One) : Item201Contra1 := by
  rintro G _ _ A M L N c ⟨h, hone⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, hH, -, hL, -, -⟩ := id hone
  have h18 : Sec18Std G A M := ⟨h.toPartTwoStanding, h.partTwoS_eq, h.mem_partTwoE,
    h.mem_scriptM⟩
  obtain ⟨T₀, hT₀⟩ := exists_ctx20 h
  obtain ⟨-, -, -, -, T, hT, hTN⟩ := h205 G A M L N c T₀ ⟨hT₀, hone⟩
  obtain ⟨-, hVeq, n, -, -, F, _, _, hF, -, -, -, β, -⟩ := h208 G A M L N c T hT hTN
  have h209' := h209 G A M L N c T hT hTN
  have hV2 : IsPGroup 2 (vTwenty M c T) :=
    hVeq ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kTwenty M c)
  have hV1 : vTwenty M c T ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (Multiplicative (Fin 3 → F)) = Nat.card (vTwenty M c T) :=
      Nat.card_congr β.symm.toEquiv
    rw [hbot, Subgroup.card_bot] at hcard
    have h3 : Nat.card (Multiplicative (Fin 3 → F)) = (2 ^ n) ^ 3 := by
      rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_eq_fintype_card,
        Fintype.card_fun, Fintype.card_fin, hF]
    rw [h3] at hcard
    have h1 : 1 < (2 ^ n) ^ 3 :=
      Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow_iff.mpr (by
        rintro rfl
        have : Fintype.card F = 1 := by rw [hF, pow_zero]
        exact absurd this (Fintype.one_lt_card).ne'))
    omega
  have hKT : kTwenty M c ⊔ T ≤ Subgroup.normalizer (vTwenty M c T : Set G) := by
    rw [hVeq]
    refine (sup_le ?_ (hT.sylow.le.trans (le_normalizer_normalClosureIn M c))).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    exact Subgroup.le_normalizer
  obtain ⟨M', hM', hNM'⟩ := exists_mem_scriptM_of_isTwoLocal (X := ((kTwenty M c ⊔ T :
    Subgroup G) : Set G)) ⟨_, hV1, hV2, rfl⟩ hKT
  have hM'M : M' = M := by
    have := h204 G A M L N c T hT
    rw [this] at hM'
    exact hM'
  have hLN : L ≤ Subgroup.normalizer (vTwenty M c T : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h209').trans
      (Subgroup.centralizer_le_normalizer _)
  apply Sec18.perfectResidual_not_le_of_mem_scriptH h18 (scriptHStar_subset A M hH)
  rw [← hL, ← hM'M]
  exact hLN.trans hNM'

theorem isSylowOf_top_of_normalizer_le {T M : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hN : Subgroup.normalizer (T : Set G) ≤ M) : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hTS⟩ := hT.isPGroup.exists_le_sylow
  have hTS' : T = S := by
    by_contra hne
    obtain ⟨y, hyS, hyT, hyN⟩ :=
      exists_mem_normalizer_not_mem_of_lt S.isPGroup' (lt_of_le_of_ne hTS hne)
    have hQ : T ⊔ Subgroup.zpowers y = T :=
      hT.eq_of_le le_sup_left (sup_le hT.le (Subgroup.zpowers_le.mpr (hN hyN)))
        (S.isPGroup'.to_le (sup_le hTS (Subgroup.zpowers_le.mpr hyS)))
    exact hyT (hQ ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, hT.isPGroup, ?_⟩
  rw [Subgroup.relIndex_top_right, hTS']
  exact S.not_dvd_index

theorem rank3II_20_5_2_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (h204 : scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M})
    (h1 : ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) :
    ∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
      ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G) := by
  intro C hC hC1 hCN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C' := C.map T.subtype with hC'
  have hC'1 : C' ≠ ⊥ := fun h => hC1 ((Subgroup.map_eq_bot_iff_of_injective C
    T.subtype_injective).mp h)
  have hC'2 : IsPGroup 2 C' := (hT.sylow.isPGroup.to_le (Subgroup.map_subtype_le C))
  obtain ⟨M', hM', hNM'⟩ := exists_mem_scriptM_of_isTwoLocal
    (X := ((kTwenty M c ⊔ T : Subgroup G) : Set G)) ⟨C', hC'1, hC'2, rfl⟩ hCN
  have hM'M : M' = M := by
    rw [h204] at hM'
    exact hM'
  have hTC : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C' : Set G) := by
    intro g hg
    have hTg : T.map (MulAut.conj g).toMonoidHom = T := map_conj_eq_of_mem_normalizer hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    set φ : T ≃* T := ((MulAut.conj g).subgroupMap T).trans (MulEquiv.subgroupCongr hTg)
      with hφ
    have hCφ : C.map φ.toMonoidHom = C := Subgroup.characteristic_iff_map_eq.mp hC φ
    have h1 : C'.map (MulAut.conj g).toMonoidHom = (C.map φ.toMonoidHom).map T.subtype := by
      rw [hC', Subgroup.map_map, Subgroup.map_map]
      congr 1
    have key : C'.map (MulAut.conj g).toMonoidHom = C' := by
      rw [h1, hCφ]
    exact key
  exact h1 (isSylowOf_top_of_normalizer_le hT.sylow (hTC.trans (hM'M ▸ hNM')))

theorem rank3II_20_5_2_of (h204 : Item204One) {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20One G A M L N c T) (h1 : ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) :
    ∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
      ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G) :=
  rank3II_20_5_2_core hT.toCtx20 (h204 G A M L N c T hT) h1

@[expose] def Step2051 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤

@[expose] def Step2053 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T →
    (∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
      ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G)) →
      ∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))

@[expose] def Step2054 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T →
    (∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
      ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G)) →
    (∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))) →
      ¬ 2 ∣ (M ⊓ N).relIndex M ∧ ∃ T' : Subgroup G, Ctx20One G A M L N c T' ∧ T' ≤ N

theorem rank3II_20_5_of (h204 : Item204One) (h1 : Step2051) (h3 : Step2053) (h4 : Step2054) :
    Item205One := by
  intro G _ _ A M L N c T hT
  have hT1 := h1 G A M L N c T hT
  have hT2 := rank3II_20_5_2_of h204 hT hT1
  have hT3 := h3 G A M L N c T hT hT2
  exact ⟨hT1, hT2, hT3, h4 G A M L N c T hT hT2 hT3⟩

end CFSG.RankThree.PartTwo.Sec20
