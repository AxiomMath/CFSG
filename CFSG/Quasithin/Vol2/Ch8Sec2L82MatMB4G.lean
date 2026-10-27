module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13.Mat

open scoped Pointwise

section Sylow

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem exists_conj_mem_sylow_mb4 {N S : Subgroup Γ} {t : Γ} (htN : t ∈ N) (ht : t ^ 2 = 1)
    (hSN : S ≤ N) (hS : IsPGroup 2 ↥S) (hidx : ¬ 2 ∣ (S.subgroupOf N).index) :
    ∃ n ∈ N, n * t * n⁻¹ ∈ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let t' : ↥N := ⟨t, htN⟩
  have ht' : t' ^ 2 = 1 := Subtype.ext (by simpa using ht)
  have hT : IsPGroup 2 ↥(Subgroup.zpowers t') := by
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨x, n, rfl⟩ := x
    apply Subtype.ext
    show (t' ^ n) ^ (2 ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [← pow_two, ht']
  obtain ⟨P, hP⟩ := hT.exists_le_sylow
  have hS' : IsPGroup 2 ↥(S.subgroupOf N) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm
  let P' : Sylow 2 ↥N := hS'.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥N P P'
  have hconj : (P' : Subgroup ↥N) = (P : Subgroup ↥N).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have htP : t' ∈ (P : Subgroup ↥N) := hP (Subgroup.mem_zpowers t')
  have h1 : g * t' * g⁻¹ ∈ (P' : Subgroup ↥N) := by
    rw [hconj]
    exact ⟨t', htP, rfl⟩
  have h2 : g * t' * g⁻¹ ∈ S.subgroupOf N := h1
  refine ⟨(g : Γ), g.2, ?_⟩
  exact Subgroup.mem_subgroupOf.1 h2

end Sylow

section Quot

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem normal_subgroupOf_mb4 {C K : Subgroup Γ} (hKn : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) :
    (K.subgroupOf C).Normal where
  conj_mem := by
    intro k hk c
    exact Subgroup.mem_subgroupOf.2 (hKn c c.2 k (Subgroup.mem_subgroupOf.1 hk))

theorem card_quot_mb4 {C K : Subgroup Γ} (hKC : K ≤ C) [(K.subgroupOf C).Normal]
    (hcard : Nat.card C = 3 * Nat.card K) : Nat.card (↥C ⧸ K.subgroupOf C) = 3 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf C)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv, hcard] at h
  exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h).symm

theorem eq_of_le_of_isPGroup_mb4 {C K X : Subgroup Γ} (hKC : K ≤ C)
    (hKn : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) (hcard : Nat.card C = 3 * Nat.card K)
    (hXC : X ≤ C) (hX : IsPGroup 2 ↥X) (hXc : Nat.card X = Nat.card K) : X = K := by
  haveI := normal_subgroupOf_mb4 hKn
  have hQ := card_quot_mb4 hKC hcard
  have hKX : X ≤ K := by
    intro x hx
    obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
    have hk' : (⟨x, hXC hx⟩ : ↥C) ^ (2 ^ k) = 1 := Subtype.ext (by
      have := congrArg Subtype.val hk
      simpa using this)
    set q : ↥C ⧸ K.subgroupOf C := QuotientGroup.mk (⟨x, hXC hx⟩ : ↥C) with hq
    have h1 : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
      rw [hq, ← QuotientGroup.mk_pow, hk']; rfl)
    have h2 : orderOf q ∣ 3 := hQ ▸ orderOf_dvd_natCard q
    have h3 : orderOf q = 1 := by
      have hc : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
      exact Nat.eq_one_of_dvd_one (hc ▸ Nat.dvd_gcd h1 h2)
    have h4 : q = 1 := orderOf_eq_one_iff.1 h3
    have h5 := (QuotientGroup.eq_one_iff (N := K.subgroupOf C) (⟨x, hXC hx⟩ : ↥C)).1 h4
    exact Subgroup.mem_subgroupOf.1 h5
  exact Subgroup.eq_of_le_of_card_ge hKX (le_of_eq hXc.symm)

theorem inv_mod_of_generator_mb4 {C K : Subgroup Γ} {t z : Γ} (hKC : K ≤ C)
    (hcard : Nat.card C = 3 * Nat.card K) (hKn : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K) (htC : ∀ c ∈ C, t * c * t⁻¹ ∈ C) (hzC : z ∈ C)
    (hz3 : z ^ 3 = 1) (hzK : z ∉ K) (hinv : t * z * t⁻¹ * z ∈ K) :
    ∀ c ∈ C, t * c * t⁻¹ * c ∈ K := by
  haveI := normal_subgroupOf_mb4 hKn
  have hQ := card_quot_mb4 hKC hcard
  let α : ↥C →* ↥C := MonoidHom.codRestrict
    (((MulAut.conj t).toMonoidHom).comp C.subtype) C (fun c => by
      show t * (c : Γ) * t⁻¹ ∈ C
      exact htC c c.2)
  have hα : K.subgroupOf C ≤ (K.subgroupOf C).comap α := by
    intro k hk
    exact Subgroup.mem_subgroupOf.2 (htK k (Subgroup.mem_subgroupOf.1 hk))
  let ᾱ : (↥C ⧸ K.subgroupOf C) →* (↥C ⧸ K.subgroupOf C) :=
    QuotientGroup.map (K.subgroupOf C) (K.subgroupOf C) α hα
  set zb : ↥C ⧸ K.subgroupOf C := QuotientGroup.mk (⟨z, hzC⟩ : ↥C) with hzb
  have hzb3 : zb ^ 3 = 1 := by
    rw [hzb, ← QuotientGroup.mk_pow]
    have : (⟨z, hzC⟩ : ↥C) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [this]; rfl
  have hzb1 : zb ≠ 1 := by
    intro h
    exact hzK (Subgroup.mem_subgroupOf.1
      ((QuotientGroup.eq_one_iff (N := K.subgroupOf C) (⟨z, hzC⟩ : ↥C)).1 h))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf zb = 3 := orderOf_eq_prime hzb3 hzb1
  have htop : Subgroup.zpowers zb = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hQ]
  have hαz : ᾱ zb = zb⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    show QuotientGroup.map _ _ α hα (QuotientGroup.mk ⟨z, hzC⟩) * QuotientGroup.mk ⟨z, hzC⟩ = 1
    rw [QuotientGroup.map_mk, ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hinv)
  intro c hc
  have hcz : (QuotientGroup.mk (⟨c, hc⟩ : ↥C) : ↥C ⧸ K.subgroupOf C) ∈ Subgroup.zpowers zb := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hcz
  have h1 : ᾱ (QuotientGroup.mk (⟨c, hc⟩ : ↥C)) = (QuotientGroup.mk (⟨c, hc⟩ : ↥C))⁻¹ := by
    rw [← hj, map_zpow, hαz, inv_zpow]
  have h2 : (QuotientGroup.mk (α ⟨c, hc⟩) : ↥C ⧸ K.subgroupOf C) *
      QuotientGroup.mk (⟨c, hc⟩ : ↥C) = 1 := by
    rw [← QuotientGroup.map_mk (K.subgroupOf C) (K.subgroupOf C) α hα, h1]
    exact inv_mul_cancel _
  rw [← QuotientGroup.mk_mul] at h2
  have h3 := (QuotientGroup.eq_one_iff _).1 h2
  exact Subgroup.mem_subgroupOf.1 h3

end Quot

end CFSG.Quasithin.H13.Mat
