module

public import CFSG.Quasithin.Background.E1Sec6
public import CFSG.Quasithin.Background.F1Basic

import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.Quasithin

open scoped commutatorElement

namespace F112T

section General

variable {L : Type*} [Group L]

theorem comm_sup_inf_centralizer_eq_of_coprime [Finite L] {X A : Subgroup L}
    (hAX : A ≤ Subgroup.normalizer (X : Set L)) (hcop : Nat.Coprime (Nat.card A) (Nat.card X))
    (hX : Group.IsSolvable X) :
    ⁅X, A⁆ ⊔ (X ⊓ Subgroup.centralizer (A : Set L)) = X := by
  let : MulDistribMulAction ↥A ↥X := Subgroup.conjMulDistribMulActionOfLeNormalizer A X hAX
  have hX₀X : ⁅X, A⁆ ≤ X := E1.commutator_le_of_le_normalizer hAX
  have hAX₀ := E1.le_normalizer_commutator_right hAX
  have hN₀n : ((⁅X, A⁆).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX₀X).mpr E1.le_normalizer_commutator_left
  have hN₀inv : ∀ a : ↥A, ∀ x ∈ (⁅X, A⁆).subgroupOf X, a • x ∈ (⁅X, A⁆).subgroupOf X := by
    intro a x hx
    exact (Subgroup.mem_normalizer_iff.mp (hAX₀ a.2) (x : L)).mp hx
  have hinv : CFSG.IsInvariant ↥A ↥X ((⁅X, A⁆).subgroupOf X) :=
    CFSG.SolvableHall.isInvariant_of_forall_smul_mem hN₀inv
  have hNsolv : Group.IsSolvable ((⁅X, A⁆).subgroupOf X) := inferInstance
  have hcopN : Nat.Coprime (Nat.card ↥A) (Nat.card ((⁅X, A⁆).subgroupOf X)) := by
    refine Nat.Coprime.coprime_dvd_right ?_ hcop
    exact Subgroup.card_subgroup_dvd_card _
  refine le_antisymm (sup_le hX₀X inf_le_left) fun g hg => ?_
  have hg' : ∀ b : ↥A, (⟨g, hg⟩ : ↥X)⁻¹ * (b • (⟨g, hg⟩ : ↥X)) ∈ (⁅X, A⁆).subgroupOf X := by
    intro b
    show (g⁻¹ * ((b : L) * g * (b : L)⁻¹) : L) ∈ ⁅X, A⁆
    have h1 := Subgroup.commutator_mem_commutator (X.inv_mem hg) b.2
    have e : ⁅g⁻¹, (b : L)⁆ = g⁻¹ * ((b : L) * g * (b : L)⁻¹) := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h1
  obtain ⟨c, hc, hcg⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed
    ((⁅X, A⁆).subgroupOf X) hinv hNsolv hcopN ⟨g, hg⟩ hg'
  have hcg' : (c : L)⁻¹ * g ∈ ⁅X, A⁆ := hcg
  have hcC : (c : L) ∈ X ⊓ Subgroup.centralizer (A : Set L) := by
    refine Subgroup.mem_inf.mpr ⟨c.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : ((⟨a, ha⟩ : ↥A) • c : ↥X) = c := hc ⟨a, ha⟩
    have h2 : (a * (c : L) * a⁻¹) = (c : L) := congrArg Subtype.val h1
    calc a * (c : L) = (a * (c : L) * a⁻¹) * a := by group
      _ = (c : L) * a := by rw [h2]
  have e : g = (c : L) * ((c : L)⁻¹ * g) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcC) (Subgroup.mem_sup_left hcg')

end General

section S3

open Equiv

theorem s3_exists_ne (τ : Perm (Fin 3)) : ∃ s : Perm (Fin 3), s ≠ 1 ∧ s ≠ τ := by
  revert τ; decide +kernel

theorem s3_conj_third (τ s : Perm (Fin 3)) (hτ : τ * τ = 1) (hτ1 : τ ≠ 1) (hs1 : s ≠ 1) (hsτ : s ≠ τ) :
    τ * (s * τ * s⁻¹) * τ ≠ 1 ∧ τ * (s * τ * s⁻¹) * τ ≠ τ := by
  have key : ∀ τ s : Perm (Fin 3), (τ * τ = 1 ∧ τ ≠ 1 ∧ s ≠ 1 ∧ s ≠ τ) →
      (τ * (s * τ * s⁻¹) * τ ≠ 1 ∧ τ * (s * τ * s⁻¹) * τ ≠ τ) := by decide +kernel
  exact key τ s ⟨hτ, hτ1, hs1, hsτ⟩

theorem s3_conj_ne (τ ε : Perm (Fin 3)) (hτ : τ * τ = 1) (hτ1 : τ ≠ 1) (hε : ε * ε = 1) (hε1 : ε ≠ 1)
    (hετ : ε ≠ τ) : ε * τ * ε⁻¹ ≠ 1 ∧ ε * τ * ε⁻¹ ≠ τ := by
  have key : ∀ τ ε : Perm (Fin 3), (τ * τ = 1 ∧ τ ≠ 1 ∧ ε * ε = 1 ∧ ε ≠ 1 ∧ ε ≠ τ) →
      (ε * τ * ε⁻¹ ≠ 1 ∧ ε * τ * ε⁻¹ ≠ τ) := by decide +kernel
  exact key τ ε ⟨hτ, hτ1, hε, hε1, hετ⟩

theorem s3_prod_three (τ σ : Perm (Fin 3)) (hτ : τ * τ = 1) (hσ : σ * σ = 1) (hτ1 : τ ≠ 1) (hσ1 : σ ≠ 1)
    (hne : τ ≠ σ) : (τ * σ) ^ 3 = 1 ∧ τ * σ ≠ 1 := by
  have key : ∀ τ σ : Perm (Fin 3), (τ * τ = 1 ∧ σ * σ = 1 ∧ τ ≠ 1 ∧ σ ≠ 1 ∧ τ ≠ σ) →
      ((τ * σ) ^ 3 = 1 ∧ τ * σ ≠ 1) := by decide +kernel
  exact key τ σ ⟨hτ, hσ, hτ1, hσ1, hne⟩

theorem s3_gen_two (τ σ x : Perm (Fin 3)) (hτ : τ * τ = 1) (hσ : σ * σ = 1) (hτ1 : τ ≠ 1) (hσ1 : σ ≠ 1)
    (hne : τ ≠ σ) : x = 1 ∨ x = τ ∨ x = σ ∨ x = τ * σ ∨ x = σ * τ ∨ x = τ * σ * τ := by
  have key : ∀ τ σ x : Perm (Fin 3), (τ * τ = 1 ∧ σ * σ = 1 ∧ τ ≠ 1 ∧ σ ≠ 1 ∧ τ ≠ σ) →
      (x = 1 ∨ x = τ ∨ x = σ ∨ x = τ * σ ∨ x = σ * τ ∨ x = τ * σ * τ) := by
    set_option synthInstance.maxSize 2048 in decide +kernel
  exact key τ σ x ⟨hτ, hσ, hτ1, hσ1, hne⟩

theorem s3_gen_three (c τ x : Perm (Fin 3)) (hc : c ^ 3 = 1) (hc1 : c ≠ 1) (hτ : τ * τ = 1) (hτ1 : τ ≠ 1) :
    x = 1 ∨ x = c ∨ x = c * c ∨ x = τ ∨ x = c * τ ∨ x = c * c * τ := by
  have key : ∀ c τ x : Perm (Fin 3), (c ^ 3 = 1 ∧ c ≠ 1 ∧ τ * τ = 1 ∧ τ ≠ 1) →
      (x = 1 ∨ x = c ∨ x = c * c ∨ x = τ ∨ x = c * τ ∨ x = c * c * τ) := by decide +kernel
  exact key c τ x ⟨hc, hc1, hτ, hτ1⟩

end S3

section Data

open Equiv

variable {L : Type*} [Group L] (π : L →* Perm (Fin 3))

theorem pi_mem_of_card_two [Finite L] {T : Subgroup L} (hπT : Nat.card (T.map π) = 2) {u : L} (huT : u ∈ T)
    (hu2 : u * u = 1) (hu1 : π u ≠ 1) {t : L} (ht : t ∈ T) : π t = 1 ∨ π t = π u := by
  have hτ : π u * π u = 1 := by rw [← map_mul, hu2, map_one]
  have hord : orderOf (π u) = 2 := orderOf_eq_prime (by rw [sq]; exact hτ) hu1
  have hle : Subgroup.zpowers (π u) ≤ T.map π :=
    (Subgroup.zpowers_le).mpr (Subgroup.mem_map_of_mem π huT)
  have hcard : Nat.card (T.map π) ≤ Nat.card (Subgroup.zpowers (π u)) := by
    rw [Nat.card_zpowers, hord, hπT]
  have heq : Subgroup.zpowers (π u) = T.map π := Subgroup.eq_of_le_of_card_ge hle hcard
  have hmem : π t ∈ Subgroup.zpowers (π u) := heq ▸ Subgroup.mem_map_of_mem π ht
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h2 : (π u) ^ k = (π u) ^ (k % 2) := by
    have := zpow_mod_orderOf (π u) k
    rw [hord] at this
    exact_mod_cast this.symm
  rw [← hk, h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

theorem mem_of_pi_eq {K : Subgroup L} (hker : π.ker ≤ K) {x w : L} (hw : w ∈ K) (h : π x = π w) : x ∈ K := by
  have h1 : x * w⁻¹ ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h]; simp
  have : x = (x * w⁻¹) * w := by group
  rw [this]
  exact K.mul_mem (hker h1) hw

theorem exists_data [Finite L] (hπ : Function.Surjective π) {T : Subgroup L} (hT2 : IsPGroup 2 T)
    (hRT : π.ker ≤ T) {u : L} (hu2 : u * u = 1) (hu1 : π u ≠ 1) :
    ∃ y d : L, y * y = 1 ∧ π y ≠ 1 ∧ π y ≠ π u ∧ π (y * u * y⁻¹) ≠ 1 ∧ π (y * u * y⁻¹) ≠ π u ∧
      d ^ 3 = 1 ∧ π d ≠ 1 ∧ d ∈ Subgroup.closure ({u, y * u * y⁻¹} : Set L) ∧ u * d * u⁻¹ = d⁻¹ ∧
      π.ker ⊔ Subgroup.closure ({u, y * u * y⁻¹} : Set L) = ⊤ ∧
      π.ker ⊔ Subgroup.closure ({u, d} : Set L) = ⊤ := by
  have hτ : π u * π u = 1 := by rw [← map_mul, hu2, map_one]
  obtain ⟨s, hs1, hsτ⟩ := s3_exists_ne (π u)
  obtain ⟨g, hg⟩ := hπ s
  set u₃ : L := g * u * g⁻¹ with hu₃
  have hu₃2 : u₃ * u₃ = 1 := by
    rw [hu₃]
    calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hπu₃ : π u₃ = s * π u * s⁻¹ := by rw [hu₃, map_mul, map_mul, map_inv, hg]
  set y : L := u * u₃ * u with hy
  have hy2 : y * y = 1 := by
    rw [hy]
    calc u * u₃ * u * (u * u₃ * u) = u * u₃ * (u * u) * u₃ * u := by group
      _ = u * (u₃ * u₃) * u := by rw [hu2]; group
      _ = 1 := by rw [hu₃2, mul_one, hu2]
  have hπy : π y = π u * (s * π u * s⁻¹) * π u := by
    rw [hy, map_mul, map_mul, hπu₃]
  obtain ⟨hπy1, hπyτ⟩ := s3_conj_third (π u) s hτ hu1 hs1 hsτ
  rw [← hπy] at hπy1 hπyτ
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hπyy : π y * π y = 1 := by rw [← map_mul, hy2, map_one]
  set u₂ : L := y * u * y⁻¹ with hu₂
  have hu₂2 : u₂ * u₂ = 1 := by
    rw [hu₂]
    calc y * u * y⁻¹ * (y * u * y⁻¹) = y * (u * u) * y⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hπu₂ : π u₂ = π y * π u * (π y)⁻¹ := by rw [hu₂, map_mul, map_mul, map_inv]
  obtain ⟨hπu₂1, hπu₂τ⟩ := s3_conj_ne (π u) (π y) hτ hu1 hπyy hπy1 hπyτ
  rw [← hπu₂] at hπu₂1 hπu₂τ
  have hπu₂2 : π u₂ * π u₂ = 1 := by rw [← map_mul, hu₂2, map_one]
  obtain ⟨hρ3, hρ1⟩ := s3_prod_three (π u) (π u₂) hτ hπu₂2 hu1 hπu₂1 (Ne.symm hπu₂τ)
  set ρ : L := u * u₂ with hρ
  have hπρ : π ρ = π u * π u₂ := by rw [hρ, map_mul]
  rw [← hπρ] at hρ3 hρ1
  have hρ3R : ρ ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hρ3]
  obtain ⟨c, hc⟩ := hT2 ⟨ρ ^ 3, hRT hρ3R⟩
  have hc' : (ρ ^ 3) ^ (2 ^ c) = 1 := by
    have := congrArg Subtype.val hc
    simpa using this
  set d : L := ρ ^ (2 ^ c) with hd
  have hd3 : d ^ 3 = 1 := by
    rw [hd, ← pow_mul, mul_comm, pow_mul]; exact hc'
  have hπd : π d ≠ 1 := by
    intro h
    rw [hd, map_pow] at h
    have hord : orderOf (π ρ) = 3 := orderOf_eq_prime hρ3 hρ1
    have := orderOf_dvd_of_pow_eq_one h
    rw [hord] at this
    have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    omega
  have hρinv : u * ρ * u⁻¹ = ρ⁻¹ := by
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    have hu₂i : u₂⁻¹ = u₂ := inv_eq_of_mul_eq_one_right hu₂2
    rw [hρ, mul_inv_rev, hu₂i, hui]
    calc u * (u * u₂) * u = (u * u) * u₂ * u := by group
      _ = u₂ * u := by rw [hu2]; group
  have hdinv : u * d * u⁻¹ = d⁻¹ := by
    rw [hd, show u * ρ ^ (2 ^ c) * u⁻¹ = (u * ρ * u⁻¹) ^ (2 ^ c) from (conj_pow).symm, hρinv, inv_pow]
  refine ⟨y, d, hy2, hπy1, hπyτ, hπu₂1, hπu₂τ, hd3, hπd, ?_, hdinv, ?_, ?_⟩
  · rw [hd]
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (by simp [hu₂]))) _
  ·
    rw [eq_top_iff]
    intro x _
    set K : Subgroup L := π.ker ⊔ Subgroup.closure ({u, u₂} : Set L) with hK
    have huK : u ∈ K := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hu₂K : u₂ ∈ K := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hkerK : π.ker ≤ K := le_sup_left
    rcases s3_gen_two (π u) (π u₂) (π x) hτ hπu₂2 hu1 hπu₂1 (Ne.symm hπu₂τ) with h | h | h | h | h | h
    · exact hkerK (show x ∈ π.ker from h)
    · exact mem_of_pi_eq π hkerK huK h
    · exact mem_of_pi_eq π hkerK hu₂K h
    · exact mem_of_pi_eq π hkerK (K.mul_mem huK hu₂K) (h.trans (map_mul π u u₂).symm)
    · exact mem_of_pi_eq π hkerK (K.mul_mem hu₂K huK) (h.trans (map_mul π u₂ u).symm)
    · exact mem_of_pi_eq π hkerK (K.mul_mem (K.mul_mem huK hu₂K) huK)
        (h.trans (((congrArg (· * π u) (map_mul π u u₂)).symm).trans (map_mul π (u * u₂) u).symm))
  ·
    rw [eq_top_iff]
    intro x _
    set K : Subgroup L := π.ker ⊔ Subgroup.closure ({u, d} : Set L) with hK
    have huK : u ∈ K := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hdK : d ∈ K := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hkerK : π.ker ≤ K := le_sup_left
    have hπd3 : (π d) ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
    rcases s3_gen_three (π d) (π u) (π x) hπd3 hπd hτ hu1 with h | h | h | h | h | h
    · exact hkerK (show x ∈ π.ker from h)
    · exact mem_of_pi_eq π hkerK hdK h
    · exact mem_of_pi_eq π hkerK (K.mul_mem hdK hdK) (h.trans (map_mul π d d).symm)
    · exact mem_of_pi_eq π hkerK huK h
    · exact mem_of_pi_eq π hkerK (K.mul_mem hdK huK) (h.trans (map_mul π d u).symm)
    · exact mem_of_pi_eq π hkerK (K.mul_mem (K.mul_mem hdK hdK) huK)
        (h.trans (((congrArg (· * π u) (map_mul π d d)).symm).trans (map_mul π (d * d) u).symm))

end Data

section Index

variable {L : Type*} [Group L]

theorem comm_mem_of_relIndex_le_two [Finite L] {X N : Subgroup L} (h2 : X.relIndex N ≤ 2) {r : L}
    (hrX : ∀ x ∈ X, r * x * r⁻¹ ∈ X) (hr'X : ∀ x ∈ X, r⁻¹ * x * r ∈ X) (hrN : ∀ x ∈ N, r * x * r⁻¹ ∈ N)
    {x : L} (hx : x ∈ N) : r * x * r⁻¹ * x⁻¹ ∈ X := by
  by_cases hxX : x ∈ X
  · exact X.mul_mem (hrX x hxX) (X.inv_mem hxX)
  · have hz : r * x * r⁻¹ ∉ X := by
      intro hz
      apply hxX
      have := hr'X _ hz
      simpa [mul_assoc] using this
    have hpos : 0 < X.relIndex N := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h2' : X.relIndex N = 2 := by
      rcases (show X.relIndex N = 1 ∨ X.relIndex N = 2 by omega) with h | h
      · exact absurd (Subgroup.relIndex_eq_one.mp h hx) hxX
      · exact h
    have hidx : (X.subgroupOf N).index = 2 := h2'
    have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨r * x * r⁻¹, hrN x hx⟩ : N))
      (b := (⟨x, hx⟩ : N)⁻¹)).mpr (by
        simp only [Subgroup.mem_subgroupOf, Subgroup.coe_inv]
        constructor
        · intro h; exact absurd h hz
        · intro h; exact absurd (X.inv_mem_iff.mp h) hxX)
    simpa [Subgroup.mem_subgroupOf] using key

end Index

section Hyp

open Equiv

variable {L : Type*} [Group L]

structure B2Hyp (π : L →* Perm (Fin 3)) (T Q U V Z : Subgroup L) : Prop where
  hT2 : IsPGroup 2 T
  hRT : π.ker ≤ T
  hπT : Nat.card (T.map π) = 2
  hQT : Q ≤ T
  hUQ : U ≤ Q
  hVU : V ≤ U
  hZV : Z ≤ V
  hTQ : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q
  hTU : ∀ t ∈ T, ∀ x ∈ U, t * x * t⁻¹ ∈ U
  hVn : ∀ l : L, ∀ v ∈ V, l * v * l⁻¹ ∈ V
  hVsq : ∀ v ∈ V, v * v = 1
  hV4 : Nat.card V = 4
  hRV : ∀ r ∈ π.ker, ∀ v ∈ V, r * v = v * r
  hCV : ∀ l : L, (∀ v ∈ V, l * v = v * l) → l ∈ π.ker
  hVmin : ∀ N : Subgroup L, N ≤ T → N ≠ ⊥ → (∀ l : L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) → V ≤ N
  hUsq : ∀ x ∈ U, x * x ∈ Z
  hUQ' : ∀ x ∈ U, ∀ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∈ Z
  hCyc : ∀ X : Subgroup L, X ≤ T → (∀ x ∈ X, x * x ∈ Q) → (Q ⊓ X).relIndex X ≤ 2

structure B2Data (π : L →* Perm (Fin 3)) (U : Subgroup L) (u y d : L) : Prop where
  huU : u ∈ U
  hu2 : u * u = 1
  hu1 : π u ≠ 1
  hy2 : y * y = 1
  hy1 : π y ≠ 1
  hyu : π y ≠ π u
  hu₂1 : π (y * u * y⁻¹) ≠ 1
  hu₂u : π (y * u * y⁻¹) ≠ π u
  hd3 : d ^ 3 = 1
  hd1 : π d ≠ 1
  hd : d ∈ Subgroup.closure ({u, y * u * y⁻¹} : Set L)
  hdu : u * d * u⁻¹ = d⁻¹
  hgen : π.ker ⊔ Subgroup.closure ({u, y * u * y⁻¹} : Set L) = ⊤
  hgen' : π.ker ⊔ Subgroup.closure ({u, d} : Set L) = ⊤

variable {π : L →* Perm (Fin 3)} {T Q U V Z : Subgroup L} {u y d : L}

theorem B2Data.inv_y (D : B2Data π U u y d) : y⁻¹ = y := inv_eq_of_mul_eq_one_right D.hy2

theorem B2Data.conj_conj (D : B2Data π U u y d) (x : L) : y * (y * x * y⁻¹) * y⁻¹ = x := by
  calc y * (y * x * y⁻¹) * y⁻¹ = (y * y) * x * (y⁻¹ * y⁻¹) := by group
    _ = x := by rw [D.hy2, D.inv_y, D.hy2]; group

end Hyp

section Stage

open Equiv

variable {L : Type*} [Group L] [Finite L] {π : L →* Perm (Fin 3)} {T Q U V Z : Subgroup L} {u y d : L}

omit [Finite L] in
theorem B2Hyp.u_mem_T (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) : u ∈ T :=
  H.hQT (H.hUQ D.huU)

theorem B2Hyp.pi_T (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {t : L} (ht : t ∈ T) :
    π t = 1 ∨ π t = π u :=
  pi_mem_of_card_two π H.hπT (H.u_mem_T D) D.hu2 D.hu1 ht

theorem B2Hyp.pi_eq_one_of_conj (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {x : L} (hx : x ∈ T)
    (hyx : y * x * y⁻¹ ∈ T) : π x = 1 := by
  rcases H.pi_T D hx with h | h
  · exact h
  · exfalso
    have h2 := H.pi_T D hyx
    have hτ : π u * π u = 1 := by rw [← map_mul, D.hu2, map_one]
    have hε : π y * π y = 1 := by rw [← map_mul, D.hy2, map_one]
    obtain ⟨h1, h1'⟩ := s3_conj_ne (π u) (π y) hτ D.hu1 hε D.hy1 D.hyu
    have e : π (y * x * y⁻¹) = π y * π u * (π y)⁻¹ := by rw [map_mul, map_mul, map_inv, h]
    rcases h2 with h2 | h2
    · exact h1 (e ▸ h2)
    · exact h1' (e ▸ h2)

omit [Finite L] in
theorem B2Hyp.comm_V_left (H : B2Hyp π T Q U V Z) {g x : L} (hg : g ∈ U) (hx : x ∈ Q) :
    g * x * g⁻¹ * x⁻¹ ∈ V :=
  H.hZV (H.hUQ' g hg x hx)

omit [Finite L] in
theorem B2Hyp.comm_V_right (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {g x : L}
    (hg : y * g * y⁻¹ ∈ U) (hx : y * x * y⁻¹ ∈ Q) : g * x * g⁻¹ * x⁻¹ ∈ V := by
  have h1 := H.hZV (H.hUQ' _ hg _ hx)
  have h2 := H.hVn y _ h1
  have e : y * ((y * g * y⁻¹) * (y * x * y⁻¹) * (y * g * y⁻¹)⁻¹ * (y * x * y⁻¹)⁻¹) * y⁻¹ =
      g * x * g⁻¹ * x⁻¹ := by
    calc y * ((y * g * y⁻¹) * (y * x * y⁻¹) * (y * g * y⁻¹)⁻¹ * (y * x * y⁻¹)⁻¹) * y⁻¹
        = (y * y) * (g * x * g⁻¹ * x⁻¹) * (y⁻¹ * y⁻¹) := by group
      _ = g * x * g⁻¹ * x⁻¹ := by rw [D.hy2, D.inv_y, D.hy2]; group
  rw [← e]
  exact h2

def Xsub (Q U : Subgroup L) (y : L) : Subgroup L := U ⊓ Q.comap (MulAut.conj y).toMonoidHom

omit [Finite L] in
theorem mem_Xsub {Q U : Subgroup L} {y x : L} : x ∈ Xsub Q U y ↔ x ∈ U ∧ y * x * y⁻¹ ∈ Q := by
  simp [Xsub]

omit [Finite L] in
theorem B2Hyp.V_le_X (H : B2Hyp π T Q U V Z) : V ≤ Xsub Q U y := by
  intro v hv
  rw [mem_Xsub]
  exact ⟨H.hVU hv, H.hUQ (H.hVU (H.hVn y v hv))⟩

theorem B2Hyp.pi_X (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {x : L} (hx : x ∈ Xsub Q U y) :
    π x = 1 := by
  rw [mem_Xsub] at hx
  exact H.pi_eq_one_of_conj D (H.hQT (H.hUQ hx.1)) (H.hQT hx.2)

theorem B2Hyp.X_le_ker (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) : Xsub Q U y ≤ π.ker :=
  fun _ hx => H.pi_X D hx

theorem B2Hyp.mem_normalizer_X_U (H : B2Hyp π T Q U V Z) {g : L} (hg : g ∈ U) :
    g ∈ Subgroup.normalizer (Xsub Q U y : Set L) := by
  apply E1.mem_normalizer_of_conj_mem
  intro x hx
  have hx' := mem_Xsub.mp hx
  have h1 := H.comm_V_left hg (H.hUQ hx'.1)
  have h2 : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
  rw [h2]
  exact Subgroup.mul_mem _ (H.V_le_X h1) hx

theorem B2Hyp.mem_normalizer_X_Uy (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {g : L}
    (hg : y * g * y⁻¹ ∈ U) : g ∈ Subgroup.normalizer (Xsub Q U y : Set L) := by
  apply E1.mem_normalizer_of_conj_mem
  intro x hx
  have hx' := mem_Xsub.mp hx
  have h1 := H.comm_V_right D hg hx'.2
  have h2 : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
  rw [h2]
  exact Subgroup.mul_mem _ (H.V_le_X h1) hx

theorem B2Hyp.mem_normalizer_X_ker (H : B2Hyp π T Q U V Z) {g : L} (hg : g ∈ π.ker) :
    g ∈ Subgroup.normalizer (Xsub Q U y : Set L) := by
  apply E1.mem_normalizer_of_conj_mem
  intro x hx
  have hx' := mem_Xsub.mp hx
  rw [mem_Xsub]
  refine ⟨H.hTU g (H.hRT hg) x hx'.1, ?_⟩
  have hyg : y * g * y⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [map_mul, map_mul, hg]; simp
  have h1 := H.hTQ _ (H.hRT hyg) _ hx'.2
  have e : y * (g * x * g⁻¹) * y⁻¹ = (y * g * y⁻¹) * (y * x * y⁻¹) * (y * g * y⁻¹)⁻¹ := by group
  rw [e]
  exact h1

theorem B2Hyp.X_normal (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) (l : L) :
    l ∈ Subgroup.normalizer (Xsub Q U y : Set L) := by
  have hle : π.ker ⊔ Subgroup.closure ({u, y * u * y⁻¹} : Set L) ≤
      Subgroup.normalizer (Xsub Q U y : Set L) := by
    refine sup_le (fun g hg => H.mem_normalizer_X_ker hg) ?_
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact H.mem_normalizer_X_U D.huU
    · exact H.mem_normalizer_X_Uy D (by rw [D.conj_conj]; exact D.huU)
  rw [D.hgen] at hle
  exact hle (Subgroup.mem_top l)

theorem B2Hyp.X_conj (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) (l : L) {x : L}
    (hx : x ∈ Xsub Q U y) : l * x * l⁻¹ ∈ Xsub Q U y :=
  (Subgroup.mem_normalizer_iff.mp (H.X_normal D l) x).mp hx

theorem B2Hyp.mem_X_iff (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {x : L} :
    x ∈ Xsub Q U y ↔ x ∈ U ∧ y * x * y⁻¹ ∈ U := by
  constructor
  · intro hx
    exact ⟨(mem_Xsub.mp hx).1, (mem_Xsub.mp (H.X_conj D y hx)).1⟩
  · rintro ⟨h1, h2⟩
    exact mem_Xsub.mpr ⟨h1, H.hUQ h2⟩

def conjc (y : L) (S : Subgroup L) : Subgroup L := S.comap (MulAut.conj y).toMonoidHom

omit [Finite L] in
theorem mem_conjc {y x : L} {S : Subgroup L} : x ∈ conjc y S ↔ y * x * y⁻¹ ∈ S := by
  simp [conjc]

theorem B2Hyp.inf_N₁_eq (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) :
    Q ⊓ (conjc y U ⊓ π.ker) = Xsub Q U y := by
  ext x
  simp only [Subgroup.mem_inf, mem_conjc]
  constructor
  · rintro ⟨hxQ, hxU, hxker⟩
    have h1 : y * x * y⁻¹ ∈ Xsub Q U y := by
      rw [mem_Xsub]
      refine ⟨hxU, ?_⟩
      have : y * (y * x * y⁻¹) * y⁻¹ = x := D.conj_conj x
      rw [this]; exact hxQ
    have := H.X_conj D y h1
    rwa [D.conj_conj] at this
  · intro hx
    have hx' := (H.mem_X_iff D).mp hx
    exact ⟨H.hUQ hx'.1, hx'.2, H.X_le_ker D hx⟩

theorem B2Hyp.X_le_N₁ (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) :
    Xsub Q U y ≤ conjc y U ⊓ π.ker :=
  fun _ hx => ⟨mem_conjc.mpr ((H.mem_X_iff D).mp hx).2, H.X_le_ker D hx⟩

theorem B2Hyp.relIndex_N₁ (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) :
    (Xsub Q U y).relIndex (conjc y U ⊓ π.ker) ≤ 2 := by
  have h := H.hCyc (conjc y U ⊓ π.ker) (fun x hx => H.hRT hx.2) (by
    rintro x ⟨hxU, -⟩
    have h1 := H.hUsq _ (mem_conjc.mp hxU)
    have h2 := H.hVn y _ (H.hZV h1)
    have e : y * (y * x * y⁻¹ * (y * x * y⁻¹)) * y⁻¹ = x * x := by
      calc y * (y * x * y⁻¹ * (y * x * y⁻¹)) * y⁻¹ = (y * y) * (x * x) * (y⁻¹ * y⁻¹) := by group
        _ = x * x := by rw [D.hy2, D.inv_y, D.hy2]; group
    rw [← e]
    exact H.hUQ (H.hVU h2))
  rwa [H.inf_N₁_eq D] at h

theorem B2Hyp.relIndex_N₀ (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) :
    (Xsub Q U y).relIndex (U ⊓ π.ker) ≤ 2 := by
  have h := H.relIndex_N₁ D
  let f : L →* L := (MulAut.conj y).toMonoidHom
  have hinj : Function.Injective f := (MulAut.conj y).injective
  have hN : (conjc y U ⊓ π.ker).map f = U ⊓ π.ker := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_conjc, f, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨n, ⟨hn1, hn2⟩, rfl⟩
      refine ⟨hn1, ?_⟩
      rw [MonoidHom.mem_ker] at hn2 ⊢
      rw [map_mul, map_mul, hn2]; simp
    · rintro ⟨hx1, hx2⟩
      refine ⟨y * x * y⁻¹, ⟨?_, ?_⟩, D.conj_conj x⟩
      · rw [D.conj_conj]; exact hx1
      · rw [MonoidHom.mem_ker] at hx2 ⊢
        rw [map_mul, map_mul, hx2]; simp
  have hX : (Xsub Q U y).map f = Xsub Q U y := by
    ext x
    simp only [Subgroup.mem_map, f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact H.X_conj D y hn
    · intro hx
      exact ⟨y * x * y⁻¹, H.X_conj D y hx, D.conj_conj x⟩
  rw [← Subgroup.relIndex_map_map_of_injective _ _ hinj, hX, hN] at h
  exact h

omit [Finite L] in
theorem ker_conj (π : L →* Perm (Fin 3)) {g : L} (hg : g ∈ π.ker) (l : L) : l * g * l⁻¹ ∈ π.ker :=
  π.normal_ker.conj_mem g hg l

omit [Finite L] in
theorem B2Hyp.sq_N₀ (H : B2Hyp π T Q U V Z) {a : L} (ha : a ∈ U) : a * a ∈ V := H.hZV (H.hUsq a ha)

omit [Finite L] in
theorem B2Hyp.sq_N₁ (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {b : L} (hb : b ∈ conjc y U) :
    b * b ∈ V := by
  have h1 := H.hUsq _ (mem_conjc.mp hb)
  have h2 := H.hVn y _ (H.hZV h1)
  have e : y * (y * b * y⁻¹ * (y * b * y⁻¹)) * y⁻¹ = b * b := by
    calc y * (y * b * y⁻¹ * (y * b * y⁻¹)) * y⁻¹ = (y * y) * (b * b) * (y⁻¹ * y⁻¹) := by group
      _ = b * b := by rw [D.hy2, D.inv_y, D.hy2]; group
  rw [← e]
  exact h2

theorem B2Hyp.comm_N₀ (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {r x : L} (hr : r ∈ π.ker)
    (hx : x ∈ U ⊓ π.ker) : r * x * r⁻¹ * x⁻¹ ∈ Xsub Q U y := by
  refine comm_mem_of_relIndex_le_two (H.relIndex_N₀ D) (r := r)
    (fun z hz => H.X_conj D r hz) (fun z hz => by simpa using H.X_conj D r⁻¹ hz) ?_ hx
  intro z hz
  exact ⟨H.hTU r (H.hRT hr) z hz.1, π.normal_ker.conj_mem z hz.2 r⟩

theorem B2Hyp.comm_N₁ (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {r x : L} (hr : r ∈ π.ker)
    (hx : x ∈ conjc y U ⊓ π.ker) : r * x * r⁻¹ * x⁻¹ ∈ Xsub Q U y := by
  refine comm_mem_of_relIndex_le_two (H.relIndex_N₁ D) (r := r)
    (fun z hz => H.X_conj D r hz) (fun z hz => by simpa using H.X_conj D r⁻¹ hz) ?_ hx
  intro z hz
  refine ⟨mem_conjc.mpr ?_, π.normal_ker.conj_mem z hz.2 r⟩
  have hyr : y * r * y⁻¹ ∈ π.ker := π.normal_ker.conj_mem r hr y
  have h1 := H.hTU _ (H.hRT hyr) _ (mem_conjc.mp hz.1)
  have e : y * (r * z * r⁻¹) * y⁻¹ = (y * r * y⁻¹) * (y * z * y⁻¹) * (y * r * y⁻¹)⁻¹ := by group
  rw [e]
  exact h1

def Wsub (π : L →* Perm (Fin 3)) (U : Subgroup L) (y : L) : Subgroup L :=
  (U ⊓ π.ker) ⊔ (conjc y U ⊓ π.ker)

theorem B2Hyp.N₀_le_normalizer_N₁ (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) :
    (U ⊓ π.ker) ≤ Subgroup.normalizer ((conjc y U ⊓ π.ker : Subgroup L) : Set L) := by
  intro a ha
  apply E1.mem_normalizer_of_conj_mem
  intro b hb
  have h1 := H.comm_N₁ D ha.2 hb
  have h2 : a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b := by group
  rw [h2]
  exact Subgroup.mul_mem _ (H.X_le_N₁ D h1) hb

theorem B2Hyp.mem_W (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {w : L} :
    w ∈ Wsub π U y ↔ ∃ a ∈ U ⊓ π.ker, ∃ b ∈ conjc y U ⊓ π.ker, w = a * b :=
  F1.mem_sup_iff_exists_mul_of_le_normalizer (H.N₀_le_normalizer_N₁ D)

theorem B2Hyp.W_sq (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {w : L} (hw : w ∈ Wsub π U y) :
    w * w ∈ Xsub Q U y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (H.mem_W D).mp hw
  have hc : b * a * b⁻¹ * a⁻¹ ∈ Xsub Q U y := H.comm_N₀ D hb.2 ha
  have e : a * b * (a * b) = (a * (b * a * b⁻¹ * a⁻¹) * a⁻¹) * (a * a) * (b * b) := by group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ (H.V_le_X (H.sq_N₀ ha.1))) (H.V_le_X (H.sq_N₁ D hb.1))
  exact H.X_conj D a hc

theorem B2Hyp.W_comm (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {r w : L} (hr : r ∈ π.ker)
    (hw : w ∈ Wsub π U y) : r * w * r⁻¹ * w⁻¹ ∈ Xsub Q U y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (H.mem_W D).mp hw
  have h1 : r * a * r⁻¹ * a⁻¹ ∈ Xsub Q U y := H.comm_N₀ D hr ha
  have h2 : r * b * r⁻¹ * b⁻¹ ∈ Xsub Q U y := H.comm_N₁ D hr hb
  have e : r * (a * b) * r⁻¹ * (a * b)⁻¹ =
      (r * a * r⁻¹ * a⁻¹) * (a * (r * b * r⁻¹ * b⁻¹) * a⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ h1 (H.X_conj D a h2)

theorem B2Hyp.W_conj_y (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {w : L} (hw : w ∈ Wsub π U y) :
    y * w * y⁻¹ ∈ Wsub π U y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (H.mem_W D).mp hw
  have ha' : y * a * y⁻¹ ∈ conjc y U ⊓ π.ker :=
    ⟨mem_conjc.mpr (by rw [D.conj_conj]; exact ha.1), ker_conj π ha.2 y⟩
  have hb' : y * b * y⁻¹ ∈ U ⊓ π.ker := ⟨mem_conjc.mp hb.1, ker_conj π hb.2 y⟩
  have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ha') (Subgroup.mem_sup_left hb')

theorem B2Hyp.u_conj_W (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {w : L} (hw : w ∈ Wsub π U y) :
    u * w * u⁻¹ ∈ Wsub π U y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (H.mem_W D).mp hw
  have h1 : u * a * u⁻¹ ∈ U ⊓ π.ker :=
    ⟨U.mul_mem (U.mul_mem D.huU ha.1) (U.inv_mem D.huU), ker_conj π ha.2 u⟩
  have h2 : u * b * u⁻¹ * b⁻¹ ∈ U ⊓ π.ker := by
    refine ⟨?_, π.ker.mul_mem (ker_conj π hb.2 u) (π.ker.inv_mem hb.2)⟩
    have := H.hTU b (H.hRT hb.2) u⁻¹ (U.inv_mem D.huU)
    have e : u * b * u⁻¹ * b⁻¹ = u * (b * u⁻¹ * b⁻¹) := by group
    rw [e]
    exact U.mul_mem D.huU this
  have e : u * (a * b) * u⁻¹ = (u * a * u⁻¹) * ((u * b * u⁻¹ * b⁻¹) * b) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mul_mem _ (Subgroup.mem_sup_left h2)
    (Subgroup.mem_sup_right hb))

theorem B2Hyp.u₂_conj_W (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {w : L} (hw : w ∈ Wsub π U y) :
    (y * u * y⁻¹) * w * (y * u * y⁻¹)⁻¹ ∈ Wsub π U y := by
  have h1 := H.W_conj_y D (H.u_conj_W D (H.W_conj_y D hw))
  have e : (y * u * y⁻¹) * w * (y * u * y⁻¹)⁻¹ = y * (u * (y * w * y⁻¹) * u⁻¹) * y⁻¹ := by
    simp only [D.inv_y, mul_inv_rev, mul_assoc]
  rw [e]
  exact h1

omit [Finite L] in
theorem B2Hyp.conj_y_N₀ (D : B2Data π U u y d) {x : L} (hx : x ∈ U ⊓ π.ker) :
    y * x * y⁻¹ ∈ conjc y U ⊓ π.ker :=
  ⟨mem_conjc.mpr (by rw [D.conj_conj]; exact hx.1), ker_conj π hx.2 y⟩

omit [Finite L] in
theorem B2Hyp.comm_u_mem (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {r : L} (hr : r ∈ π.ker) :
    r * u * r⁻¹ * u⁻¹ ∈ U ⊓ π.ker := by
  refine ⟨?_, ?_⟩
  · exact U.mul_mem (H.hTU r (H.hRT hr) u D.huU) (U.inv_mem D.huU)
  · have e : r * u * r⁻¹ * u⁻¹ = r * (u * r⁻¹ * u⁻¹) := by group
    rw [e]
    exact π.ker.mul_mem hr (ker_conj π (π.ker.inv_mem hr) u)

theorem B2Hyp.closure_prop (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {g : L}
    (hg : g ∈ Subgroup.closure ({u, y * u * y⁻¹} : Set L)) :
    g ∈ Subgroup.normalizer ((Wsub π U y : Subgroup L) : Set L) ∧
      ∀ r ∈ π.ker, r * g * r⁻¹ * g⁻¹ ∈ Wsub π U y := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨E1.mem_normalizer_of_conj_mem fun w hw => H.u_conj_W D hw,
        fun r hr => Subgroup.mem_sup_left (H.comm_u_mem D hr)⟩
    · refine ⟨E1.mem_normalizer_of_conj_mem fun w hw => H.u₂_conj_W D hw, fun r hr => ?_⟩
      have h1 : y⁻¹ * r * y ∈ π.ker := by simpa using ker_conj π hr y⁻¹
      have h2 := B2Hyp.conj_y_N₀ D (H.comm_u_mem D h1)
      have e : r * (y * u * y⁻¹) * r⁻¹ * (y * u * y⁻¹)⁻¹ =
          y * ((y⁻¹ * r * y) * u * (y⁻¹ * r * y)⁻¹ * u⁻¹) * y⁻¹ := by group
      rw [e]
      exact Subgroup.mem_sup_right h2
  | one => exact ⟨Subgroup.one_mem _, fun r hr => by simp⟩
  | mul x z hx hz ihx ihz =>
    refine ⟨Subgroup.mul_mem _ ihx.1 ihz.1, fun r hr => ?_⟩
    have e : r * (x * z) * r⁻¹ * (x * z)⁻¹ = (r * x * r⁻¹ * x⁻¹) * (x * (r * z * r⁻¹ * z⁻¹) * x⁻¹) := by
      group
    rw [e]
    exact Subgroup.mul_mem _ (ihx.2 r hr) ((Subgroup.mem_normalizer_iff.mp ihx.1 _).mp (ihz.2 r hr))
  | inv x hx ihx =>
    refine ⟨Subgroup.inv_mem _ ihx.1, fun r hr => ?_⟩
    have e : r * x⁻¹ * r⁻¹ * x⁻¹⁻¹ = x⁻¹ * (r * x * r⁻¹ * x⁻¹)⁻¹ * x := by group
    rw [e]
    have hx' : x⁻¹ ∈ Subgroup.normalizer ((Wsub π U y : Subgroup L) : Set L) := Subgroup.inv_mem _ ihx.1
    simpa using (Subgroup.mem_normalizer_iff.mp hx' _).mp (Subgroup.inv_mem _ (ihx.2 r hr))

theorem card_modEq_card_inf_centralizer_prime {p : ℕ} [Fact p.Prime] {P X : Subgroup L}
    (hP : Nat.card P = p) (hPX : P ≤ Subgroup.normalizer (X : Set L)) :
    Nat.card X ≡ Nat.card ↥(X ⊓ Subgroup.centralizer (P : Set L)) [MOD p] := by
  have hPp : IsPGroup p P := IsPGroup.of_card (n := 1) (by simpa using hP)
  let _ : MulDistribMulAction P X := Subgroup.conjMulDistribMulActionOfLeNormalizer P X hPX
  have h := hPp.card_modEq_card_fixedPoints X
  have heq : Nat.card (MulAction.fixedPoints P X) =
      Nat.card ↥(X ⊓ Subgroup.centralizer (P : Set L)) := by
    refine Nat.card_congr
      { toFun := fun v => ⟨v.1.1, Subgroup.mem_inf.mpr ⟨v.1.2, ?_⟩⟩
        invFun := fun v => ⟨⟨v.1, (Subgroup.mem_inf.mp v.2).1⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 : (⟨g, hg⟩ : P) • (v.1 : X) = v.1 := v.2 ⟨g, hg⟩
      have h2 := congrArg Subtype.val h1
      have h3 : g * (v.1 : L) * g⁻¹ = (v.1 : L) := h2
      calc g * (v.1 : L) = g * v.1 * g⁻¹ * g := by group
        _ = v.1 * g := by rw [h3]
    · intro g
      apply Subtype.ext
      have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp v.2).2 (g : L) g.2
      show (g : L) * (v : L) * (g : L)⁻¹ = (v : L)
      rw [h1]
      group
  rwa [heq] at h

theorem B2Hyp.V_cent_d (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {v : L} (hv : v ∈ V)
    (hvd : d * v = v * d) : v = 1 := by
  have h3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hd1 : d ≠ 1 := fun h => D.hd1 (by rw [h, map_one])
  have hord : orderOf d = 3 := orderOf_eq_prime D.hd3 hd1
  have hP : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hord]
  have hPN : Subgroup.zpowers d ≤ Subgroup.normalizer (V : Set L) := by
    rw [Subgroup.zpowers_le]
    exact E1.mem_normalizer_of_conj_mem fun x hx => H.hVn d x hx
  have hmod := card_modEq_card_inf_centralizer_prime hP hPN
  rw [H.hV4] at hmod
  set C : Subgroup L := V ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set L) with hC
  have hCd : Nat.card C ∣ 4 := H.hV4 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hCle : Nat.card C ≤ 4 := Nat.le_of_dvd (by norm_num) hCd
  have hk : Nat.card C = 1 ∨ Nat.card C = 4 := by
    unfold Nat.ModEq at hmod
    interval_cases h : Nat.card C <;> simp_all
  rcases hk with h1 | h4
  · have hC1 : C = ⊥ := Subgroup.eq_bot_of_card_eq C h1
    have hvC : v ∈ C := by
      refine ⟨hv, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact ((Commute.zpow_left (show Commute d v from hvd) k).eq)
    rw [hC1, Subgroup.mem_bot] at hvC
    exact hvC
  · exfalso
    have hCV : C = V := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, H.hV4])
    have hcomm : ∀ w ∈ V, d * w = w * d := by
      intro w hw
      have hwC : w ∈ C := hCV ▸ hw
      exact Subgroup.mem_centralizer_iff.mp hwC.2 d (Subgroup.mem_zpowers d)
    exact D.hd1 (by
      have := H.hCV d (fun w hw => hcomm w hw)
      exact MonoidHom.mem_ker.mp this)

def Hc (π : L →* Perm (Fin 3)) (d : L) : Subgroup L :=
  π.ker ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set L)

omit [Finite L] in
theorem mem_Hc {π : L →* Perm (Fin 3)} {d x : L} : x ∈ Hc π d ↔ x ∈ π.ker ∧ d * x = x * d := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Subgroup.mem_centralizer_iff.mp h2 d (Subgroup.mem_zpowers d)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute d x from h2) k).eq

theorem B2Hyp.comm_zpowers_le_W (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) :
    ⁅π.ker, Subgroup.zpowers d⁆ ≤ Wsub π U y := by
  rw [Subgroup.commutator_le]
  intro r hr g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hdk : d ^ k ∈ Subgroup.closure ({u, y * u * y⁻¹} : Set L) := Subgroup.zpow_mem _ D.hd k
  exact (H.closure_prop D hdk).2 r hr

theorem B2Hyp.coprime_ker (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {X : Subgroup L}
    (hX : X ≤ π.ker) :
    Nat.Coprime (Nat.card (Subgroup.zpowers d)) (Nat.card X) ∧ Group.IsSolvable X := by
  have hd1 : d ≠ 1 := fun h => D.hd1 (by rw [h, map_one])
  have hord : orderOf d = 3 := orderOf_eq_prime D.hd3 hd1
  have hP : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hord]
  have hX2 : IsPGroup 2 X := (H.hT2.to_le H.hRT).to_le hX
  obtain ⟨k, hk⟩ := hX2.exists_card_eq
  refine ⟨by rw [hP, hk]; exact Nat.Coprime.pow_right k (by norm_num), ?_⟩
  have : Group.IsNilpotent X := hX2.isNilpotent
  infer_instance

theorem B2Hyp.ker_eq_Hc_W (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {r : L} (hr : r ∈ π.ker) :
    ∃ c ∈ Hc π d, ∃ w ∈ Wsub π U y, r = c * w := by
  have hA : Subgroup.zpowers d ≤ Subgroup.normalizer ((π.ker : Subgroup L) : Set L) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨hcop, hsolv⟩ := H.coprime_ker D (le_refl π.ker)
  have hdec := comm_sup_inf_centralizer_eq_of_coprime hA hcop hsolv
  have hr' : r ∈ (π.ker ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set L)) ⊔ ⁅π.ker, Subgroup.zpowers d⁆ := by
    rw [sup_comm, hdec]; exact hr
  have hnorm : (π.ker ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set L)) ≤
      Subgroup.normalizer ((⁅π.ker, Subgroup.zpowers d⁆ : Subgroup L) : Set L) :=
    inf_le_left.trans E1.le_normalizer_commutator_left
  obtain ⟨c, hc, a, ha, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hnorm).mp hr'
  exact ⟨c, hc, a, H.comm_zpowers_le_W D ha, rfl⟩

omit [Finite L] in
theorem B2Hyp.comm_X_closure (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {g : L}
    (hg : g ∈ Subgroup.closure ({u, y * u * y⁻¹} : Set L)) :
    ∀ x ∈ Xsub Q U y, x * g * x⁻¹ * g⁻¹ ∈ V := by
  induction hg using Subgroup.closure_induction with
  | mem g₀ hg₀ =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg₀
    rcases hg₀ with rfl | rfl
    · intro x hx
      have hx' := mem_Xsub.mp hx
      have h := H.comm_V_left D.huU (H.hUQ hx'.1)
      have e : x * g₀ * x⁻¹ * g₀⁻¹ = (g₀ * x * g₀⁻¹ * x⁻¹)⁻¹ := by group
      rw [e]; exact V.inv_mem h
    · intro x hx
      have hx' := mem_Xsub.mp hx
      have h := H.comm_V_right D (g := y * u * y⁻¹) (x := x) (by rw [D.conj_conj]; exact D.huU) hx'.2
      have e : x * (y * u * y⁻¹) * x⁻¹ * (y * u * y⁻¹)⁻¹ =
          ((y * u * y⁻¹) * x * (y * u * y⁻¹)⁻¹ * x⁻¹)⁻¹ := by group
      rw [e]; exact V.inv_mem h
  | one => intro x _; simp
  | mul g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
    intro x hx
    have e : x * (g₁ * g₂) * x⁻¹ * (g₁ * g₂)⁻¹ =
        (x * g₁ * x⁻¹ * g₁⁻¹) * (g₁ * (x * g₂ * x⁻¹ * g₂⁻¹) * g₁⁻¹) := by group
    rw [e]
    exact V.mul_mem (ih₁ x hx) (H.hVn g₁ _ (ih₂ x hx))
  | inv g₁ hg₁ ih₁ =>
    intro x hx
    have e : x * g₁⁻¹ * x⁻¹ * g₁⁻¹⁻¹ = g₁⁻¹ * (x * g₁ * x⁻¹ * g₁⁻¹)⁻¹ * g₁ := by group
    rw [e]
    simpa using H.hVn g₁⁻¹ _ (V.inv_mem (ih₁ x hx))

theorem B2Hyp.X_mem_Hc_V (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {x : L}
    (hx : x ∈ Xsub Q U y) : ∃ c ∈ Hc π d, ∃ v ∈ V, x = c * v := by
  have hA : Subgroup.zpowers d ≤ Subgroup.normalizer ((Xsub Q U y : Subgroup L) : Set L) :=
    fun g _ => H.X_normal D g
  obtain ⟨hcop, hsolv⟩ := H.coprime_ker D (X := Xsub Q U y) (H.X_le_ker D)
  have hdec := comm_sup_inf_centralizer_eq_of_coprime hA hcop hsolv
  have hx' : x ∈ (Xsub Q U y ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set L)) ⊔
      ⁅Xsub Q U y, Subgroup.zpowers d⁆ := by
    rw [sup_comm, hdec]; exact hx
  have hnorm : (Xsub Q U y ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set L)) ≤
      Subgroup.normalizer ((⁅Xsub Q U y, Subgroup.zpowers d⁆ : Subgroup L) : Set L) :=
    inf_le_left.trans E1.le_normalizer_commutator_left
  obtain ⟨c, hc, a, ha, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hnorm).mp hx'
  have hle : ⁅Xsub Q U y, Subgroup.zpowers d⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro x₀ hx₀ g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact H.comm_X_closure D (Subgroup.zpow_mem _ D.hd k) x₀ hx₀
  exact ⟨c, mem_Hc.mpr ⟨H.X_le_ker D hc.1,
    Subgroup.mem_centralizer_iff.mp hc.2 d (Subgroup.mem_zpowers d)⟩, a, hle ha, rfl⟩

omit [Finite L] in
theorem B2Data.inv_u (D : B2Data π U u y d) : u⁻¹ = u := inv_eq_of_mul_eq_one_right D.hu2

def Nn (π : L →* Perm (Fin 3)) (d : L) (V : Subgroup L) : Subgroup L := Hc π d ⊔ V

theorem B2Hyp.mem_Nn (H : B2Hyp π T Q U V Z) {n : L} :
    n ∈ Nn π d V ↔ ∃ c ∈ Hc π d, ∃ v ∈ V, n = c * v := by
  refine F1.mem_sup_iff_exists_mul_of_le_normalizer (fun g _ => ?_)
  exact E1.mem_normalizer_of_conj_mem fun x hx => H.hVn g x hx

omit [Finite L] in
theorem B2Hyp.Hc_le_ker (π : L →* Perm (Fin 3)) (d : L) : Hc π d ≤ π.ker := inf_le_left

omit [Finite L] in
theorem B2Hyp.Hc_conj_u (D : B2Data π U u y d) {c : L} (hc : c ∈ Hc π d) : u * c * u⁻¹ ∈ Hc π d := by
  rw [mem_Hc] at hc ⊢
  refine ⟨ker_conj π hc.1 u, ?_⟩
  have hdu' : u⁻¹ * d * u = d⁻¹ := by
    have h := D.hdu
    rw [D.inv_u] at h ⊢
    exact h
  have hdi : d⁻¹ * c = c * d⁻¹ := by
    have := (Commute.inv_left (show Commute d c from hc.2)).eq
    exact this
  have hdu2 : u * d⁻¹ * u⁻¹ = d := by
    calc u * d⁻¹ * u⁻¹ = (u * d * u⁻¹)⁻¹ := by group
      _ = d := by rw [D.hdu, inv_inv]
  calc d * (u * c * u⁻¹) = u * (u⁻¹ * d * u) * c * u⁻¹ := by group
    _ = u * d⁻¹ * c * u⁻¹ := by rw [hdu']
    _ = u * (c * d⁻¹) * u⁻¹ := by rw [mul_assoc u d⁻¹ c, hdi, ← mul_assoc]
    _ = (u * c * u⁻¹) * (u * d⁻¹ * u⁻¹) := by group
    _ = (u * c * u⁻¹) * d := by rw [hdu2]

theorem B2Hyp.W_conj_Nn (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {w n : L}
    (hw : w ∈ Wsub π U y) (hn : n ∈ Nn π d V) : w * n * w⁻¹ ∈ Nn π d V := by
  obtain ⟨c, hc, v, hv, rfl⟩ := (H.mem_Nn).mp hn
  have hcomm : c * w * c⁻¹ * w⁻¹ ∈ Xsub Q U y := H.W_comm D (B2Hyp.Hc_le_ker π d hc) hw
  have e : w * (c * v) * w⁻¹ = (c * w * c⁻¹ * w⁻¹)⁻¹ * c * (w * v * w⁻¹) := by group
  rw [e]
  obtain ⟨c₁, hc₁, v₁, hv₁, hx'⟩ := H.X_mem_Hc_V D (Subgroup.inv_mem _ hcomm)
  rw [hx']
  refine (H.mem_Nn).mpr ⟨c₁ * c, Subgroup.mul_mem _ hc₁ hc, v₁ * (w * v * w⁻¹),
    V.mul_mem hv₁ (H.hVn w v hv), ?_⟩
  have hcv : c * v₁ = v₁ * c := H.hRV c (B2Hyp.Hc_le_ker π d hc) v₁ hv₁
  calc c₁ * v₁ * c * (w * v * w⁻¹) = c₁ * (v₁ * c) * (w * v * w⁻¹) := by group
    _ = c₁ * (c * v₁) * (w * v * w⁻¹) := by rw [hcv]
    _ = c₁ * c * (v₁ * (w * v * w⁻¹)) := by group

theorem B2Hyp.Hc_conj_Nn (H : B2Hyp π T Q U V Z) {c' n : L} (hc' : c' ∈ Hc π d) (hn : n ∈ Nn π d V) :
    c' * n * c'⁻¹ ∈ Nn π d V := by
  obtain ⟨c, hc, v, hv, rfl⟩ := (H.mem_Nn).mp hn
  have hcv : c' * v = v * c' := H.hRV c' (B2Hyp.Hc_le_ker π d hc') v hv
  have e : c' * (c * v) * c'⁻¹ = (c' * c * c'⁻¹) * v := by
    calc c' * (c * v) * c'⁻¹ = (c' * c) * (v * c'⁻¹) := by group
      _ = (c' * c) * (c'⁻¹ * v) := by
        rw [show v * c'⁻¹ = c'⁻¹ * v from by
          calc v * c'⁻¹ = c'⁻¹ * (c' * v) * c'⁻¹ := by group
            _ = c'⁻¹ * (v * c') * c'⁻¹ := by rw [hcv]
            _ = c'⁻¹ * v := by group]
      _ = (c' * c * c'⁻¹) * v := by group
  rw [e]
  exact (H.mem_Nn).mpr ⟨c' * c * c'⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hc' hc) (Subgroup.inv_mem _ hc'),
    v, hv, rfl⟩

theorem B2Hyp.ker_conj_Nn (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {r n : L} (hr : r ∈ π.ker)
    (hn : n ∈ Nn π d V) : r * n * r⁻¹ ∈ Nn π d V := by
  obtain ⟨c, hc, w, hw, rfl⟩ := H.ker_eq_Hc_W D hr
  have e : c * w * n * (c * w)⁻¹ = c * (w * n * w⁻¹) * c⁻¹ := by group
  rw [e]
  exact H.Hc_conj_Nn hc (H.W_conj_Nn D hw hn)

theorem B2Hyp.u_conj_Nn (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {n : L} (hn : n ∈ Nn π d V) :
    u * n * u⁻¹ ∈ Nn π d V := by
  obtain ⟨c, hc, v, hv, rfl⟩ := (H.mem_Nn).mp hn
  have e : u * (c * v) * u⁻¹ = (u * c * u⁻¹) * (u * v * u⁻¹) := by group
  rw [e]
  exact (H.mem_Nn).mpr ⟨u * c * u⁻¹, B2Hyp.Hc_conj_u D hc, u * v * u⁻¹, H.hVn u v hv, rfl⟩

theorem B2Hyp.d_conj_Nn (H : B2Hyp π T Q U V Z) {n : L} (hn : n ∈ Nn π d V) :
    d * n * d⁻¹ ∈ Nn π d V := by
  obtain ⟨c, hc, v, hv, rfl⟩ := (H.mem_Nn).mp hn
  have hdc : d * c = c * d := (mem_Hc.mp hc).2
  have e : d * (c * v) * d⁻¹ = c * (d * v * d⁻¹) := by
    calc d * (c * v) * d⁻¹ = (d * c) * v * d⁻¹ := by group
      _ = (c * d) * v * d⁻¹ := by rw [hdc]
      _ = c * (d * v * d⁻¹) := by group
  rw [e]
  exact (H.mem_Nn).mpr ⟨c, hc, d * v * d⁻¹, H.hVn d v hv, rfl⟩

theorem B2Hyp.Nn_normal (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) (l : L) :
    l ∈ Subgroup.normalizer ((Nn π d V : Subgroup L) : Set L) := by
  have hle : π.ker ⊔ Subgroup.closure ({u, d} : Set L) ≤
      Subgroup.normalizer ((Nn π d V : Subgroup L) : Set L) := by
    refine sup_le (fun g hg => E1.mem_normalizer_of_conj_mem fun n hn => H.ker_conj_Nn D hg hn) ?_
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact E1.mem_normalizer_of_conj_mem fun n hn => H.u_conj_Nn D hn
    · exact E1.mem_normalizer_of_conj_mem fun n hn => H.d_conj_Nn hn
  rw [D.hgen'] at hle
  exact hle (Subgroup.mem_top l)

theorem B2Hyp.sq_mem_Hc (H : B2Hyp π T Q U V Z) {n : L} (hn : n ∈ Nn π d V) : n * n ∈ Hc π d := by
  obtain ⟨c, hc, v, hv, rfl⟩ := (H.mem_Nn).mp hn
  have hcv : c * v = v * c := H.hRV c (B2Hyp.Hc_le_ker π d hc) v hv
  have e : c * v * (c * v) = (c * c) * (v * v) := by
    calc c * v * (c * v) = c * (v * c) * v := by group
      _ = c * (c * v) * v := by rw [hcv]
      _ = (c * c) * (v * v) := by group
  rw [e, H.hVsq v hv, mul_one]
  exact Subgroup.mul_mem _ hc hc

theorem B2Hyp.Nn_conj (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) (l : L) {n : L}
    (hn : n ∈ Nn π d V) : l * n * l⁻¹ ∈ Nn π d V :=
  (Subgroup.mem_normalizer_iff.mp (H.Nn_normal D l) n).mp hn

def NnSq (π : L →* Perm (Fin 3)) (d : L) (V : Subgroup L) : Subgroup L :=
  Subgroup.closure {x | ∃ a ∈ Nn π d V, x = a * a}

theorem B2Hyp.NnSq_le_Hc (H : B2Hyp π T Q U V Z) : NnSq π d V ≤ Hc π d := by
  rw [NnSq, Subgroup.closure_le]
  rintro _ ⟨a, ha, rfl⟩
  exact H.sq_mem_Hc ha

theorem B2Hyp.NnSq_conj (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) (l : L) {x : L}
    (hx : x ∈ NnSq π d V) : l * x * l⁻¹ ∈ NnSq π d V := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    have e : l * (a * a) * l⁻¹ = (l * a * l⁻¹) * (l * a * l⁻¹) := by group
    rw [e]
    exact Subgroup.subset_closure ⟨l * a * l⁻¹, H.Nn_conj D l ha, rfl⟩
  | one => simp
  | mul x z hx hz ihx ihz =>
    have e : l * (x * z) * l⁻¹ = (l * x * l⁻¹) * (l * z * l⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ihx ihz
  | inv x hx ihx =>
    have e : l * x⁻¹ * l⁻¹ = (l * x * l⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ihx

theorem B2Hyp.Hc_sq (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {c : L} (hc : c ∈ Hc π d) :
    c * c = 1 := by
  have hcN : c ∈ Nn π d V := Subgroup.mem_sup_left hc
  have hcc : c * c ∈ NnSq π d V := Subgroup.subset_closure ⟨c, hcN, rfl⟩
  by_contra hne
  have hE : NnSq π d V ≠ ⊥ := fun h => hne (by rw [h] at hcc; exact Subgroup.mem_bot.mp hcc)
  have hET : NnSq π d V ≤ T := (H.NnSq_le_Hc).trans ((B2Hyp.Hc_le_ker π d).trans H.hRT)
  have hVE := H.hVmin _ hET hE (fun l n hn => H.NnSq_conj D l hn)
  have hVH : V ≤ Hc π d := hVE.trans H.NnSq_le_Hc
  have hV1 : V = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact Subgroup.mem_bot.mpr (H.V_cent_d D hv (mem_Hc.mp (hVH hv)).2)
  have h4 := H.hV4
  rw [hV1, Subgroup.card_bot] at h4
  omega

theorem B2Hyp.sq_mem_X (H : B2Hyp π T Q U V Z) (D : B2Data π U u y d) {r : L} (hr : r ∈ π.ker) :
    r * r ∈ Xsub Q U y := by
  obtain ⟨c, hc, w, hw, rfl⟩ := H.ker_eq_Hc_W D hr
  have hcc : c * c = 1 := H.Hc_sq D hc
  have hcomm : c * w * c⁻¹ * w⁻¹ ∈ Xsub Q U y := H.W_comm D (B2Hyp.Hc_le_ker π d hc) hw
  have hww : w * w ∈ Xsub Q U y := H.W_sq D hw
  have e : c * w * (c * w) = (c * w * c⁻¹ * w⁻¹) * (w * (c * c) * w) := by group
  rw [e, hcc, mul_one]
  exact Subgroup.mul_mem _ hcomm hww

theorem B2Hyp.sq_mem_Q (H : B2Hyp π T Q U V Z) (hπ : Function.Surjective π) {u : L} (huU : u ∈ U)
    (hu2 : u * u = 1) (hu1 : π u ≠ 1) {r : L} (hr : r ∈ π.ker) : r * r ∈ Q := by
  obtain ⟨y, d, hy2, hy1, hyu, hu₂1, hu₂u, hd3, hd1, hd, hdu, hgen, hgen'⟩ :=
    exists_data π hπ H.hT2 H.hRT hu2 hu1
  have D : B2Data π U u y d :=
    ⟨huU, hu2, hu1, hy2, hy1, hyu, hu₂1, hu₂u, hd3, hd1, hd, hdu, hgen, hgen'⟩
  exact H.hUQ (mem_Xsub.mp (H.sq_mem_X D hr)).1

end Stage

end F112T

end CFSG.Quasithin
