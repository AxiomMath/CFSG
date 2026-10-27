module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.G6Basic

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Quasithin CFSG.Quasithin.G6

variable {V : Type} [CommGroup V] [Finite V] {X : Subgroup (MulAut V)} {a : MulAut V}

@[expose] def G64Out : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (X : Subgroup (MulAut V)) (a : MulAut V)
    (h : Hypothesis61 X a), Nat.card (commV (Subgroup.zpowers a)) = 2 →
    (∃ T : Subgroup (MulAut V), CFSG.QuasithinUnique.IsSylowTwoOf T X ∧ a ∈ T ∧
      ∀ t ∈ T, t * a = a * t) →
    X = classClosure X a ∧ commV X = ⊤ ∧
      ((∃ n, 2 ≤ n ∧ n ≤ 5 ∧ Nat.card V = 2 ^ n ∧
          Nonempty (X ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 2))) ∨
        ∃ n, (n = 6 ∨ n = 7) ∧ ∃ θ : X ≃* Equiv.Perm (Fin n), (θ ⟨a, h.mem⟩).IsSwap)

omit [Finite V] in
theorem not_two_dvd_index_map {Y : Type} [Group Y] (ρ : Y →* MulAut V) {T : Subgroup Y}
    (hT : ¬ 2 ∣ T.index) : ¬ 2 ∣ ((T.map ρ).subgroupOf ρ.range).index := by
  have heq : (T.map ρ).subgroupOf ρ.range = T.map ρ.rangeRestrict := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, Subtype.ext hyx⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [heq]
  exact fun h => hT (h.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective))

theorem transvection_outcome_hom (hG : G64Out) (hV : ∀ v : V, v ^ 2 = 1) {Y : Type} [Group Y]
    (ρ : Y →* MulAut V) (hSQ : IsQuotientOfSQTK Y)
    (hO2 : ∀ P : Subgroup Y, P.Normal → (∀ p ∈ P, ∃ k : ℕ, ρ p ^ 2 ^ k = 1) → P ≤ ρ.ker)
    {a : Y} (ha2 : ρ a * ρ a = 1) (ha1 : ρ a ≠ 1)
    (htr : Nat.card (commV (Subgroup.zpowers (ρ a))) = 2)
    (hspan : submoduleClosure ρ.range (commV (Subgroup.zpowers (ρ a))) = ⊤)
    {T : Subgroup Y} (hT : IsPGroup 2 T ∧ ¬ 2 ∣ T.index) (haT : a ∈ T)
    (hcent : ∀ t ∈ T, ρ t * ρ a = ρ a * ρ t) :
    ρ.range = classClosure ρ.range (ρ a) ∧ commV ρ.range = ⊤ ∧
      ((∃ n, 2 ≤ n ∧ n ≤ 5 ∧ Nat.card V = 2 ^ n ∧
          Nonempty (ρ.range ≃* Matrix.GeneralLinearGroup (Fin n) (ZMod 2))) ∨
        ∃ n, (n = 6 ∨ n = 7) ∧ ∃ θ : ρ.range ≃* Equiv.Perm (Fin n),
          (θ ⟨ρ a, ⟨a, rfl⟩⟩).IsSwap) := by
  have hX : Hypothesis61 ρ.range (ρ a) :=
    { sq_eq_one := hV
      pCoreOf_eq_bot := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hNc : (CFSG.Open.pCore 2 ↥ρ.range).Characteristic :=
          CFSG.LieType.BorelTits.pCore_characteristic (G := ↥ρ.range) 2
        have hNn : (CFSG.Open.pCore 2 ↥ρ.range).Normal := inferInstance
        have hNp : IsPGroup 2 (CFSG.Open.pCore 2 ↥ρ.range) :=
          CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥ρ.range) 2
        have hP : (CFSG.Open.pCore 2 ↥ρ.range).comap ρ.rangeRestrict ≤ ρ.ker := by
          refine hO2 _ (hNn.comap _) fun p hp => ?_
          obtain ⟨k, hk⟩ := hNp ⟨_, hp⟩
          refine ⟨k, ?_⟩
          have h1 : (ρ.rangeRestrict p) ^ 2 ^ k = 1 := by
            have := congrArg Subtype.val hk
            simpa using this
          have h2 := congrArg (fun z : ↥ρ.range => (z : MulAut V)) h1
          simpa using h2
        have hcore : CFSG.Open.pCore 2 ↥ρ.range = ⊥ := by
          rw [eq_bot_iff]
          intro n hn
          obtain ⟨y, rfl⟩ := ρ.rangeRestrict_surjective n
          have hy : y ∈ ρ.ker := hP hn
          rw [Subgroup.mem_bot]
          exact Subtype.ext (by simpa using hy)
        simp only [CFSG.Open.pCoreOf, hcore, Subgroup.map_bot]
      isQuotientOfSQTK := by
        obtain ⟨S, _, _, hS, φ, hφ⟩ := hSQ
        exact ⟨S, inferInstance, inferInstance, hS, ρ.rangeRestrict.comp φ,
          ρ.rangeRestrict_surjective.comp hφ⟩
      mem := ⟨a, rfl⟩
      ne_one := ha1
      mul_self := ha2
      card_commV_le := by rw [htr]; norm_num
      span := hspan }
  have hTX : CFSG.QuasithinUnique.IsSylowTwoOf (T.map ρ) ρ.range ∧ ρ a ∈ T.map ρ ∧
      ∀ t ∈ T.map ρ, t * ρ a = ρ a * t := by
    refine ⟨⟨Subgroup.map_le_range ρ T, hT.1.map ρ, not_two_dvd_index_map ρ hT.2⟩,
      ⟨a, haT, rfl⟩, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hcent t ht
  obtain ⟨hXc, hcomm, hcase⟩ :=
    hG _ _ _ hX htr ⟨T.map ρ, hTX.1, hTX.2.1, hTX.2.2⟩
  exact ⟨hXc, hcomm, hcase⟩

end CFSG.Quasithin.H13.GM22
