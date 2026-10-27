module

public import CFSG.Quasithin.Vol2.E2SevenKG
public import CFSG.Quasithin.Vol2.Ch3E213MP3A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

open CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts

@[expose] def KGL2OddPrime : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M K V : Subgroup G) (p : ℕ), MinParabolic X T M →
    kerIn M X = ⊥ → K ≤ X → X ≤ Subgroup.normalizer (K : Set G) →
    X ⊓ Subgroup.centralizer (K : Set G) = ⊥ → K ⊔ T = X → p.Prime → 3 < p →
    (p % 8 = 1 ∨ p % 8 = 7) → IsPSL 2 p 1 ↥K →
    M ⊓ K = K ⊓ Subgroup.centralizer
      ((T ⊓ K ⊓ Subgroup.centralizer ((T ⊓ K : Subgroup G) : Set G) : Subgroup G) : Set G) →
    8 < autCard T K → V ≤ pCoreOf 2 M → IsElemAbelian 2 V → T ≤ Subgroup.normalizer (V : Set G) →
    Nat.card V ≤ 2

@[expose] def KGL2OddSq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M K V : Subgroup G) (p : ℕ), MinParabolic X T M →
    kerIn M X = ⊥ → K ≤ X → X ≤ Subgroup.normalizer (K : Set G) →
    X ⊓ Subgroup.centralizer (K : Set G) = ⊥ → K ⊔ T = X → p.Prime → 3 < p →
    (p ^ 2 % 8 = 1 ∨ p ^ 2 % 8 = 7) → IsPSL 2 p 2 ↥K →
    M ⊓ K = K ⊓ Subgroup.centralizer
      ((T ⊓ K ⊓ Subgroup.centralizer ((T ⊓ K : Subgroup G) : Set G) : Subgroup G) : Set G) →
    8 < autCard T K → V ≤ pCoreOf 2 M → IsElemAbelian 2 V → T ≤ Subgroup.normalizer (V : Set G) →
    Nat.card V ≤ 2

theorem kgL2Odd_of_parts (h1 : KGL2OddPrime) (h2 : KGL2OddSq) : KGL2Odd := by
  intro G _ _ X T M K V p e hP hJ hKX hXN hC hKT hp hp3 he hpe hK hMK haut hVO hVab hTV
  rcases he with rfl | rfl
  · exact h1 G X T M K V p hP hJ hKX hXN hC hKT hp hp3 (by simpa using hpe) hK hMK haut hVO hVab
      hTV
  · exact h2 G X T M K V p hP hJ hKX hXN hC hKT hp hp3 hpe hK hMK haut hVO hVab hTV

theorem kgL2OddPrime_holds :
    KGL2OddPrime := by
  intro G _ _ X T M K V p hP _ hKX hXN hC _ hp hp3 _ hK _ haut hVO hVab hTV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hK
  have hF' : Nat.card F = p := by simpa using hF
  set θ : ↥K ≃* PSL2 F :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  obtain ⟨hMmax, -⟩ : IsMaxSubgroupIn X M ∧ T ≤ M := by
    have : M ∈ maxOver X T := by rw [hP.uniqueMax]; exact rfl
    exact this
  have hVX : V ≤ X := (hVO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 M)).trans hMmax.1.le
  have hVN : V ≤ Subgroup.normalizer (K : Set G) := hVX.trans hXN
  set W := Ch3E213M.P3.autSub θ V with hW
  have hWcard : Nat.card W = Nat.card V := by
    rw [hW, Ch3E213M.P3.card_autSub, autCard, inf_eq_left.mpr hVN]
    have h1 : V ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
      rw [eq_bot_iff, ← hC]
      exact inf_le_inf_right _ hVX
    rw [h1, Subgroup.relIndex_bot_left]
  have hW2 : ∀ w ∈ W, w * w = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul]
    have : v * v = 1 := Subtype.ext (by
      have := hVab.2 _ (Subgroup.mem_subgroupOf.mp hv)
      simpa [sq] using this)
    rw [this, map_one]
  have hW4 : Nat.card W ≤ 4 := pGammaL2_card_le_four_of_sq_of_prime hp hp2 hF' W hW2
  by_contra hV2
  push Not at hV2
  have hV4 : Nat.card W = 4 := by
    have hVp : IsPGroup 2 V := B6.isPGroup_of_isElemAbelian hVab
    obtain ⟨k, hk⟩ := hVp.exists_card_eq
    rw [hWcard, hk] at hW4 ⊢
    rw [hk] at hV2
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> simp at hV2
    · rcases Nat.lt_or_ge k 3 with h' | h'
      · interval_cases k
        rfl
      · have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h'
        omega
  have hWC := Ch3E213M.P3.centralizer_eq_self hp hp2 hF' hV4 hW2
  have hTW : Ch3E213M.P3.autSub θ T ≤ Subgroup.normalizer (W : Set (PGammaL2 F)) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hsV : (s : G) ∈ Subgroup.normalizer (V : Set G) := hTV (Subgroup.mem_subgroupOf.mp hs)
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
      have h1 : (s : G) * v * (s : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hsV _).mp hv'
      refine ⟨s * v * s⁻¹, Subgroup.mem_subgroupOf.mpr h1, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · rintro ⟨v, hv, hvw⟩
      have hv' : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
      have h1 : (s : G)⁻¹ * v * (s : G)⁻¹⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsV) _).mp hv'
      rw [inv_inv] at h1
      refine ⟨s⁻¹ * v * s, Subgroup.mem_subgroupOf.mpr (by simpa using h1), ?_⟩
      rw [map_mul, map_mul, map_inv, hvw]
      group
  have hT2 : IsPGroup 2 (Ch3E213M.P3.autSub θ T) := by
    have hT2' : IsPGroup 2 (T.subgroupOf (Subgroup.normalizer (K : Set G))) :=
      (hP.isSylow.2.1).of_equiv (Subgroup.subgroupOfEquivOfLe (hP.isSylow.1.trans hXN)).symm
    exact hT2'.map _
  have h8 := Ch3E213M.P3.card_le_eight_of_le_normalizer hV4 hW2 hWC.le hT2 hTW
  rw [Ch3E213M.P3.card_autSub] at h8
  omega

end E2

end CFSG.Quasithin
