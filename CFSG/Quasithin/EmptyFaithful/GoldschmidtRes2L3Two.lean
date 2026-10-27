module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3Sel
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLiftBasic

public section

namespace CFSG.Quasithin.Gap6R2.L3

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem odd_mem_of_sup {K0 T : Subgroup G} (hT : IsPGroup 2 T)
    (hTK : T ≤ Subgroup.normalizer (K0 : Set G)) {a : G} (ha : a ∈ K0 ⊔ T)
    (hodd : Odd (orderOf a)) : a ∈ K0 := by
  have hnorm : K0 ⊔ T ≤ Subgroup.normalizer (K0 : Set G) := sup_le Subgroup.le_normalizer hTK
  have h1 : K0.relIndex (T ⊔ K0) = K0.relIndex T :=
    A4.relIndex_sup_eq_of_le_normalizer' hTK
  obtain ⟨k, hk⟩ : ∃ k : ℕ, K0.relIndex (K0 ⊔ T) = 2 ^ k := by
    have h2 : K0.relIndex T ∣ Nat.card T := Subgroup.relIndex_dvd_card _ _
    obtain ⟨n, hn⟩ := hT.exists_card_eq
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hn ▸ h2)
    refine ⟨k, ?_⟩
    rw [sup_comm, h1, hk]
  have hC : Subgroup.zpowers a ≤ K0 ⊔ T := (Subgroup.zpowers_le).mpr ha
  have hCodd : Odd (Nat.card (Subgroup.zpowers a)) := by
    rw [Nat.card_zpowers]
    exact hodd
  exact E2.BorelLift.le_of_odd le_sup_left hnorm hk hC hCodd (Subgroup.mem_zpowers a)

theorem oddComm_of_case_two_of_odd_mem {K T N K0 : Subgroup G} (hmin : MinParabolic K T N)
    (hKK0 : K = K0 ⊔ T) (hTK : T ≤ Subgroup.normalizer (K0 : Set G))
    (hker : ∀ x : G, x ∈ kerIn N K ↔ x ∈ K0 ⊔ pCoreOf 2 K ∧
      ∀ y ∈ K0 ⊔ pCoreOf 2 K, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 K)
    (hJ : ∀ a ∈ N ⊓ K0, Odd (orderOf a) → a ∈ kerIn N K) :
    ∀ a ∈ N, Odd (orderOf a) → ∀ b ∈ N, Odd (orderOf b) →
      a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : IsSylowTwoOf T K := hmin.isSylow
  have hNK : N ≤ K := hmin.maximal.1.le
  have hTN : T ≤ N := hmin.le
  have hQT : pCoreOf 2 K ≤ T := CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hsyl
  have hQN : pCoreOf 2 K ≤ pCoreOf 2 N :=
    le_pCoreOf_of_le_normalizer 2 (hQT.trans hTN)
      (fun x hx => le_normalizer_pCoreOf 2 K (hNK hx)) (pCoreOf_isPGroup 2 K)
  intro a ha hoa b hb hob
  have haK0 : a ∈ K0 := odd_mem_of_sup hsyl.2.1 hTK (hKK0 ▸ hNK ha) hoa
  have hbK0 : b ∈ K0 := odd_mem_of_sup hsyl.2.1 hTK (hKK0 ▸ hNK hb) hob
  have haJ := (hker a).mp (hJ a ⟨ha, haK0⟩ hoa)
  exact hQN (haJ.2 b (Subgroup.mem_sup_left hbK0))


omit [Finite G] in
theorem odd_mem_kerIn_of_normalizerTwoGroup {K N K0 : Subgroup G} (hK0K : K0 ≤ K)
    (hbor : E2.IsBorelIn (E2.star N K K0) (E2.star N K (N ⊓ K0)))
    (hN2 : NormalizerTwoGroup ↥(E2.star N K K0)) :
    ∀ a ∈ N ⊓ K0, Odd (orderOf a) → a ∈ kerIn N K := by
  obtain ⟨S, hS, hMS⟩ := hbor
  intro a ha hoa
  have haK : a ∈ K := hK0K ha.2
  set π : ↥K →* E2.StarQuot N K := QuotientGroup.mk' ((kerIn N K).subgroupOf K) with hπ
  have hxM : π ⟨a, haK⟩ ∈ E2.star N K (N ⊓ K0) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
  rw [hMS] at hxM
  obtain ⟨hxKs, hxN⟩ := hxM
  have hS' : IsPGroup 2 ↥(S.subgroupOf (E2.star N K K0)) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hxn : (⟨π ⟨a, haK⟩, hxKs⟩ : ↥(E2.star N K K0)) ∈
      Subgroup.normalizer ((S.subgroupOf (E2.star N K K0) : Subgroup ↥(E2.star N K K0)) :
        Set ↥(E2.star N K K0)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := (Subgroup.mem_normalizer_iff.mp hxN) (y : E2.StarQuot N K)
    simpa [Subgroup.mem_subgroupOf] using this
  have hodd : Odd (orderOf (⟨π ⟨a, haK⟩, hxKs⟩ : ↥(E2.star N K K0))) := by
    rw [← Subgroup.orderOf_coe]
    refine Odd.of_dvd_nat (n := orderOf (⟨a, haK⟩ : ↥K)) ?_ (orderOf_map_dvd π _)
    rw [Subgroup.orderOf_mk]
    exact hoa
  have h1 := hN2 _ hS' hS.2.2 _ hxn hodd
  have h2 : π ⟨a, haK⟩ = 1 := congrArg Subtype.val h1
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)

theorem oddComm_of_two_b_one {K T N K0 : Subgroup G} (hmin : MinParabolic K T N)
    (hK0 : K0 ∈ cComp K) (hKK0 : K = K0 ⊔ T) (hTK : T ≤ Subgroup.normalizer (K0 : Set G))
    (hker : ∀ x : G, x ∈ kerIn N K ↔ x ∈ K0 ⊔ pCoreOf 2 K ∧
      ∀ y ∈ K0 ⊔ pCoreOf 2 K, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 K)
    (hty : IsPSL 3 2 1 ↥(E2.star N K K0) ∨ E2.IsSp4Prime 1 ↥(E2.star N K K0))
    (hbor : E2.IsBorelIn (E2.star N K K0) (E2.star N K (N ⊓ K0))) :
    ∀ a ∈ N, Odd (orderOf a) → ∀ b ∈ N, Odd (orderOf b) →
      a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 N := by
  have : Finite (E2.StarQuot N K) := inferInstance
  have hN2 : NormalizerTwoGroup ↥(E2.star N K K0) := by
    rcases hty with h | h
    · exact normalizerTwoGroup_psl_three_two h
    · simp only [E2.IsSp4Prime, ↓reduceIte] at h
      exact normalizerTwoGroup_alt_six h
  exact oddComm_of_case_two_of_odd_mem hmin hKK0 hTK hker
    (odd_mem_kerIn_of_normalizerTwoGroup (le_of_mem_cComp hK0) hbor hN2)

end CFSG.Quasithin.Gap6R2.L3
