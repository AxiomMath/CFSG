module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

namespace S126T2

theorem map_eq_bot_of_perfect {Γ Δ : Type*} [Group Γ] [Group Δ] [Finite Δ] {A : Subgroup Γ}
    (hA : ⁅A, A⁆ = A) (f : Γ →* Δ) (hs : Group.IsSolvable ↥(A.map f)) : A.map f = ⊥ := by
  have hB : ⁅A.map f, A.map f⁆ = A.map f := by rw [← Subgroup.map_commutator, hA]
  rw [← perfectCore_eq_self_of_perfect hB]
  exact (isSolvable_iff_perfectCore_eq_bot _).1 hs

variable {G : Type*} [Group G]

theorem perfect_subgroupOf {K W : Subgroup G} (hK : ⁅K, K⁆ = K) (hKW : K ≤ W) :
    ⁅K.subgroupOf W, K.subgroupOf W⁆ = K.subgroupOf W := by
  apply Subgroup.map_injective W.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKW, hK]

theorem isSolvable_of_isPGroup {Δ : Type*} [Group Δ] [Finite Δ] {B : Subgroup Δ}
    (hB : IsPGroup 2 B) : Group.IsSolvable B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hB.isNilpotent
  infer_instance

theorem le_of_two_mod [Finite G] {K N : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hKN : K ≤ Subgroup.normalizer (N : Set G))
    (h2 : ∀ k ∈ K, ∃ n ∈ N, ∃ q : G, k = n * q ∧ q ∈ Subgroup.normalizer (N : Set G) ∧
      ∃ m : ℕ, q ^ 2 ^ m = 1) : K ≤ N := by
  set W := Subgroup.normalizer (N : Set G) with hW
  have hNW : N ≤ W := Subgroup.le_normalizer
  have : (N.subgroupOf W).Normal := Subgroup.normal_in_normalizer
  set φ := QuotientGroup.mk' (N.subgroupOf W) with hφ
  have hp : IsPGroup 2 ↥((K.subgroupOf W).map φ) := by
    rintro ⟨_, ⟨k, hk, rfl⟩⟩
    obtain ⟨n, hn, q, hkq, hqW, m, hm⟩ := h2 k hk
    refine ⟨m, Subtype.ext ?_⟩
    have hφk : φ k = φ ⟨q, hqW⟩ := by
      have e : k = (⟨n, hNW hn⟩ : ↥W) * ⟨q, hqW⟩ := Subtype.ext hkq
      rw [e, map_mul]
      have h1 : φ ⟨n, hNW hn⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hn
      rw [h1, one_mul]
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [hφk, ← map_pow]
    have : (⟨q, hqW⟩ : ↥W) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm)
    rw [this, map_one]
  have hbot := map_eq_bot_of_perfect (perfect_subgroupOf hK hKN) φ (isSolvable_of_isPGroup hp)
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  intro k hk
  exact hbot (show (⟨k, hKN hk⟩ : ↥W) ∈ K.subgroupOf W from hk)

theorem le_normalizer_of_relIndex_le_four [Finite G] {K P : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hKP : K ≤ Subgroup.normalizer (P : Set G)) (hP : IsPGroup 2 P)
    (h4 : (P ⊓ Subgroup.normalizer (K : Set G)).relIndex P ≤ 4) :
    P ≤ Subgroup.normalizer (K : Set G) := by
  classical
  set X := K ⊔ P with hX
  have hKX : K ≤ X := le_sup_left
  have hPX : P ≤ X := le_sup_right
  set N' : Subgroup ↥X := (Subgroup.normalizer (K : Set G)).subgroupOf X with hN'
  have hidx : Nat.card (↥X ⧸ N') ≤ 4 := by
    set Q' : Subgroup ↥P := (Subgroup.normalizer (K : Set G)).subgroupOf P with hQ'
    have hQ : Nat.card (↥P ⧸ Q') ≤ 4 := by
      have e : (P ⊓ Subgroup.normalizer (K : Set G)).relIndex P = Q'.index := by
        rw [Subgroup.relIndex, Subgroup.inf_subgroupOf_left]
      rw [e] at h4
      exact h4
    let f : ↥P ⧸ Q' → ↥X ⧸ N' := Quotient.map' (fun p => (⟨p, hPX p.2⟩ : ↥X)) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      exact hab)
    have hf : Function.Surjective f := by
      intro y
      induction y using QuotientGroup.induction_on with
      | H x =>
        have hx : (x : G) ∈ ((P ⊔ K : Subgroup G) : Set G) := by
          rw [sup_comm]
          exact x.2
        rw [Subgroup.coe_mul_of_right_le_normalizer_left P K hKP] at hx
        obtain ⟨p, hp, k, hk, hpk⟩ := hx
        refine ⟨(⟨p, hp⟩ : ↥P), ?_⟩
        change ((⟨p, hPX hp⟩ : ↥X) : ↥X ⧸ N') = (x : ↥X ⧸ N')
        rw [QuotientGroup.eq]
        change (p⁻¹ * (x : G)) ∈ Subgroup.normalizer (K : Set G)
        rw [← hpk, inv_mul_cancel_left]
        exact Subgroup.le_normalizer hk
    exact (Nat.card_le_card_of_surjective f hf).trans hQ
  have hcore : K.subgroupOf X ≤ N'.normalCore := by
    have : Group.IsSolvable (Equiv.Perm (↥X ⧸ N')) := Equiv.Perm.isSolvable hidx
    rw [Subgroup.normalCore_eq_ker]
    have h := map_eq_bot_of_perfect (perfect_subgroupOf hK hKX)
      (MulAction.toPermHom ↥X (↥X ⧸ N')) inferInstance
    rwa [Subgroup.map_eq_bot_iff] at h
  have h3 : ∀ p ∈ P, ∀ k ∈ K, p⁻¹ * k * p ∈ Subgroup.normalizer (K : Set G) := by
    intro p hp k hk
    have hk' := hcore (show (⟨k, hKX hk⟩ : ↥X) ∈ K.subgroupOf X from hk) (⟨p, hPX hp⟩ : ↥X)⁻¹
    have e : (((⟨p, hPX hp⟩ : ↥X)⁻¹ * ⟨k, hKX hk⟩ * (⟨p, hPX hp⟩ : ↥X)⁻¹⁻¹ : ↥X) : G) =
        p⁻¹ * k * p := by simp
    rw [hN', Subgroup.mem_subgroupOf, e] at hk'
    exact hk'
  have h4' : ∀ p ∈ P, ∀ k ∈ K, p⁻¹ * k * p ∈ K := by
    intro p hp
    set L' : Subgroup G := K.comap (MulAut.conj p⁻¹).toMonoidHom with hL'
    have hmemL : ∀ x, x ∈ L' ↔ p⁻¹ * x * p ∈ K := fun x => by
      rw [hL', Subgroup.mem_comap]
      simp
    have hKL : K ≤ Subgroup.normalizer (L' : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hn := h3 p hp k hk
      rw [hmemL, hmemL]
      have e : p⁻¹ * (k * x * k⁻¹) * p = (p⁻¹ * k * p) * (p⁻¹ * x * p) * (p⁻¹ * k * p)⁻¹ := by
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 hn _)
    have hle := le_of_two_mod (N := L') hK hKL (by
      intro k hk
      have hkL : p * k * p⁻¹ ∈ L' := (hmemL _).2
        (by rw [show p⁻¹ * (p * k * p⁻¹) * p = k by group]; exact hk)
      refine ⟨p * k * p⁻¹, hkL, p * k⁻¹ * p⁻¹ * k, by group, ?_, ?_⟩
      · have e : p * k⁻¹ * p⁻¹ * k = (p * k * p⁻¹)⁻¹ * k := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hkL)) (hKL hk)
      · have hq : p * k⁻¹ * p⁻¹ * k ∈ P := by
          have h1 : k⁻¹ * p⁻¹ * k ∈ P := by
            have := (Subgroup.mem_normalizer_iff.1 (hKP (K.inv_mem hk)) p⁻¹).1 (P.inv_mem hp)
            simpa using this
          have e : p * k⁻¹ * p⁻¹ * k = p * (k⁻¹ * p⁻¹ * k) := by group
          rw [e]
          exact P.mul_mem hp h1
        obtain ⟨m, hm⟩ := hP ⟨_, hq⟩
        exact ⟨m, by simpa using congrArg Subtype.val hm⟩)
    intro k hk
    exact (hmemL k).1 (hle hk)
  intro p hp
  have := A4.mem_normalizer_of_conj_mem (K := K) (m := p⁻¹) (fun k hk => by
    simpa using h4' p hp k hk)
  simpa using Subgroup.inv_mem _ this

theorem perfectCore_sup_eq [Finite G] {K P : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) (hP : IsPGroup 2 P) :
    perfectCore (K ⊔ P) = K := by
  refine le_antisymm ?_ (le_perfectCore_of_perfect le_sup_left hK)
  have hW : K ⊔ P ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hPK
  refine le_of_two_mod (perfectCore_perfect _) ((perfectCore_le _).trans hW) ?_
  intro w hw
  have hw' : w ∈ ((K ⊔ P : Subgroup G) : Set G) := perfectCore_le _ hw
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K P hPK] at hw'
  obtain ⟨k, hk, q, hq, rfl⟩ := hw'
  obtain ⟨m, hm⟩ := hP ⟨q, hq⟩
  exact ⟨k, hk, q, rfl, hPK hq, m, by simpa using congrArg Subtype.val hm⟩

end S126T2

end CFSG.Quasithin.H13
