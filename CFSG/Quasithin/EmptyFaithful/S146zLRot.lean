module

public import CFSG.Quasithin.EmptyFaithful.S146zHDih

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section Rot

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.pq_le_rot (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) (φ₁ : ↥H₁ →* DihedralGroup p)
    (hker₁ : ∀ y : ↥H₁, φ₁ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₁ : ↥H₁}
    (ha₁ : φ₁ a₁ = DihedralGroup.r 1) (φ₂ : ↥H₂ →* DihedralGroup p)
    (hker₂ : ∀ y : ↥H₂, φ₂ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₂ : ↥H₂}
    (ha₂ : φ₂ a₂ = DihedralGroup.r 1) :
    PQ ≤ Subgroup.zpowers (a₁ : G) ⊔ Subgroup.zpowers (a₂ : G) ⊔ pCoreOf 2 H := by
  have hp : p.Prime := hred.prime
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hred.odd
  have hpq : PQ ≤ H₀ := h.pq_le_gen S hred
  intro y hy
  have hyH₀ : y ∈ H₁ ⊔ H₂ := by rw [← h.sup]; exact hpq hy
  have hmul : (↑(H₁ ⊔ H₂) : Set G) = ↑H₁ * ↑H₂ :=
    Subgroup.coe_mul_of_left_le_normalizer_right H₁ H₂ h.H₁_le_normalizer_H₂
  have hy' : y ∈ (↑(H₁ ⊔ H₂) : Set G) := hyH₀
  rw [hmul] at hy'
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy'
  obtain ⟨k, hk⟩ := hred.pSec (y₁ * y₂) hy
  set Q := pCoreOf 2 H with hQ
  have hQn : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 H)).mpr (le_normalizer_pCoreOf 2 H)
  have hy₁H : y₁ ∈ H := h.le (h.le₁ hy₁)
  have hy₂H : y₂ ∈ H := h.le (h.le₂ hy₂)
  let π : ↥H →* ↥H ⧸ Q.subgroupOf H := QuotientGroup.mk' (Q.subgroupOf H)
  have hπ1 : ∀ z : ↥H, π z = 1 ↔ (z : G) ∈ Q := fun z => by
    show (QuotientGroup.mk z : ↥H ⧸ Q.subgroupOf H) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcomm : Commute (π ⟨y₁, hy₁H⟩) (π ⟨y₂, hy₂H⟩) := by
    have h1 : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ Q := h.comm (Subgroup.commutator_mem_commutator hy₁ hy₂)
    have h2 : π (⟨y₁, hy₁H⟩ * ⟨y₂, hy₂H⟩ * ⟨y₁, hy₁H⟩⁻¹ * ⟨y₂, hy₂H⟩⁻¹) = 1 := (hπ1 _).mpr h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    exact (commutatorElement_eq_one_iff_mul_comm).mp h2
  have hn : π ⟨y₁, hy₁H⟩ ^ (p ^ k) * π ⟨y₂, hy₂H⟩ ^ (p ^ k) = 1 := by
    rw [← hcomm.mul_pow, ← map_mul, ← map_pow]
    exact (hπ1 _).mpr (by simpa using hk)
  have hn' : y₁ ^ (p ^ k) * y₂ ^ (p ^ k) ∈ Q := by
    rw [← map_pow, ← map_pow, ← map_mul] at hn
    exact (hπ1 _).mp hn
  have hy₁n : y₁ ^ (p ^ k) ∈ Q := by
    have hy₂n : y₂ ^ (p ^ k) ∈ H₂ := H₂.pow_mem hy₂ _
    have h3 : y₁ ^ (p ^ k) ∈ H₂ := by
      have e : y₁ ^ (p ^ k) = (y₁ ^ (p ^ k) * y₂ ^ (p ^ k)) * (y₂ ^ (p ^ k))⁻¹ := by group
      rw [e]
      exact H₂.mul_mem (h.Q₂ hn') (H₂.inv_mem hy₂n)
    have h4 : y₁ ^ (p ^ k) ∈ H₁ ⊓ H₂ := ⟨H₁.pow_mem hy₁ _, h3⟩
    rwa [h.inf] at h4
  have hy₂n : y₂ ^ (p ^ k) ∈ Q := by
    have h3 : y₂ ^ (p ^ k) ∈ H₁ := by
      have e : y₂ ^ (p ^ k) = (y₁ ^ (p ^ k))⁻¹ * (y₁ ^ (p ^ k) * y₂ ^ (p ^ k)) := by group
      rw [e]
      exact H₁.mul_mem (H₁.inv_mem (H₁.pow_mem hy₁ _)) (h.Q₁ hn')
    have h4 : y₂ ^ (p ^ k) ∈ H₁ ⊓ H₂ := ⟨h3, H₂.pow_mem hy₂ _⟩
    rwa [h.inf] at h4
  have hφ₁n : φ₁ ⟨y₁, hy₁⟩ ^ (p ^ k) = 1 := by
    rw [← map_pow]
    exact (hker₁ _).mpr (by simpa using hy₁n)
  obtain ⟨j, hj⟩ := dih_rot_of_pow (hodd.pow) hφ₁n
  have hq₁ : φ₁ (⟨y₁, hy₁⟩ * (a₁ ^ j.val)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, ha₁, hj, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val,
      mul_inv_cancel]
  have hq₁Q : y₁ * ((a₁ : G) ^ j.val)⁻¹ ∈ Q := by simpa using (hker₁ _).mp hq₁
  have hφ₂n : φ₂ ⟨y₂, hy₂⟩ ^ (p ^ k) = 1 := by
    rw [← map_pow]
    exact (hker₂ _).mpr (by simpa using hy₂n)
  obtain ⟨j', hj'⟩ := dih_rot_of_pow (hodd.pow) hφ₂n
  have hq₂ : φ₂ (⟨y₂, hy₂⟩ * (a₂ ^ j'.val)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, ha₂, hj', DihedralGroup.r_one_pow, ZMod.natCast_zmod_val,
      mul_inv_cancel]
  have hq₂Q : y₂ * ((a₂ : G) ^ j'.val)⁻¹ ∈ Q := by simpa using (hker₂ _).mp hq₂
  have e : y₁ * y₂ = (y₁ * ((a₁ : G) ^ j.val)⁻¹) * (a₁ : G) ^ j.val *
      ((y₂ * ((a₂ : G) ^ j'.val)⁻¹) * (a₂ : G) ^ j'.val) := by group
  show y₁ * y₂ ∈ Subgroup.zpowers (a₁ : G) ⊔ Subgroup.zpowers (a₂ : G) ⊔ Q
  rw [e]
  have hQ1 : ∀ z ∈ Q, z ∈ Subgroup.zpowers (a₁ : G) ⊔ Subgroup.zpowers (a₂ : G) ⊔ Q :=
    fun z hz => Subgroup.mem_sup_right hz
  have hA1 : (a₁ : G) ^ j.val ∈ Subgroup.zpowers (a₁ : G) ⊔ Subgroup.zpowers (a₂ : G) ⊔ Q :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
  have hA2 : (a₂ : G) ^ j'.val ∈ Subgroup.zpowers (a₁ : G) ⊔ Subgroup.zpowers (a₂ : G) ⊔ Q :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hQ1 _ hq₁Q) hA1)
    (Subgroup.mul_mem _ (hQ1 _ hq₂Q) hA2)


theorem IsDecP.pq_rot_K (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) (φ₁ : ↥H₁ →* DihedralGroup p)
    (hker₁ : ∀ y : ↥H₁, φ₁ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₁ : ↥H₁}
    (ha₁ : φ₁ a₁ = DihedralGroup.r 1) (φ₂ : ↥H₂ →* DihedralGroup p)
    (hker₂ : ∀ y : ↥H₂, φ₂ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₂ : ↥H₂}
    (ha₂ : φ₂ a₂ = DihedralGroup.r 1) :
    ∀ y (hy : y ∈ PQ), ∃ i j : ℕ,
      (QuotientGroup.mk ⟨y, hred.le hy⟩ : ↥H ⧸ (pCoreOf 2 H).subgroupOf H) =
        (QuotientGroup.mk ⟨(a₁ : G), h.le (h.le₁ a₁.2)⟩ : ↥H ⧸ (pCoreOf 2 H).subgroupOf H) ^ i *
          (QuotientGroup.mk ⟨(a₂ : G), h.le (h.le₂ a₂.2)⟩ : ↥H ⧸ (pCoreOf 2 H).subgroupOf H) ^ j := by
  have hp : p.Prime := hred.prime
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hred.odd
  have hpq : PQ ≤ H₀ := h.pq_le_gen S hred
  intro y hy
  have hyH₀ : y ∈ H₁ ⊔ H₂ := by rw [← h.sup]; exact hpq hy
  have hmul : (↑(H₁ ⊔ H₂) : Set G) = ↑H₁ * ↑H₂ :=
    Subgroup.coe_mul_of_left_le_normalizer_right H₁ H₂ h.H₁_le_normalizer_H₂
  have hy' : y ∈ (↑(H₁ ⊔ H₂) : Set G) := hyH₀
  rw [hmul] at hy'
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy'
  obtain ⟨k, hk⟩ := hred.pSec (y₁ * y₂) hy
  set Q := pCoreOf 2 H with hQ
  have hQn : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 H)).mpr (le_normalizer_pCoreOf 2 H)
  have hy₁H : y₁ ∈ H := h.le (h.le₁ hy₁)
  have hy₂H : y₂ ∈ H := h.le (h.le₂ hy₂)
  let π : ↥H →* ↥H ⧸ Q.subgroupOf H := QuotientGroup.mk' (Q.subgroupOf H)
  have hπ1 : ∀ z : ↥H, π z = 1 ↔ (z : G) ∈ Q := fun z => by
    show (QuotientGroup.mk z : ↥H ⧸ Q.subgroupOf H) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcomm : Commute (π ⟨y₁, hy₁H⟩) (π ⟨y₂, hy₂H⟩) := by
    have h1 : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ Q := h.comm (Subgroup.commutator_mem_commutator hy₁ hy₂)
    have h2 : π (⟨y₁, hy₁H⟩ * ⟨y₂, hy₂H⟩ * ⟨y₁, hy₁H⟩⁻¹ * ⟨y₂, hy₂H⟩⁻¹) = 1 := (hπ1 _).mpr h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    exact (commutatorElement_eq_one_iff_mul_comm).mp h2
  have hn : π ⟨y₁, hy₁H⟩ ^ (p ^ k) * π ⟨y₂, hy₂H⟩ ^ (p ^ k) = 1 := by
    rw [← hcomm.mul_pow, ← map_mul, ← map_pow]
    exact (hπ1 _).mpr (by simpa using hk)
  have hn' : y₁ ^ (p ^ k) * y₂ ^ (p ^ k) ∈ Q := by
    rw [← map_pow, ← map_pow, ← map_mul] at hn
    exact (hπ1 _).mp hn
  have hy₁n : y₁ ^ (p ^ k) ∈ Q := by
    have hy₂n : y₂ ^ (p ^ k) ∈ H₂ := H₂.pow_mem hy₂ _
    have h3 : y₁ ^ (p ^ k) ∈ H₂ := by
      have e : y₁ ^ (p ^ k) = (y₁ ^ (p ^ k) * y₂ ^ (p ^ k)) * (y₂ ^ (p ^ k))⁻¹ := by group
      rw [e]
      exact H₂.mul_mem (h.Q₂ hn') (H₂.inv_mem hy₂n)
    have h4 : y₁ ^ (p ^ k) ∈ H₁ ⊓ H₂ := ⟨H₁.pow_mem hy₁ _, h3⟩
    rwa [h.inf] at h4
  have hy₂n : y₂ ^ (p ^ k) ∈ Q := by
    have h3 : y₂ ^ (p ^ k) ∈ H₁ := by
      have e : y₂ ^ (p ^ k) = (y₁ ^ (p ^ k))⁻¹ * (y₁ ^ (p ^ k) * y₂ ^ (p ^ k)) := by group
      rw [e]
      exact H₁.mul_mem (H₁.inv_mem (H₁.pow_mem hy₁ _)) (h.Q₁ hn')
    have h4 : y₂ ^ (p ^ k) ∈ H₁ ⊓ H₂ := ⟨h3, H₂.pow_mem hy₂ _⟩
    rwa [h.inf] at h4
  have hφ₁n : φ₁ ⟨y₁, hy₁⟩ ^ (p ^ k) = 1 := by
    rw [← map_pow]
    exact (hker₁ _).mpr (by simpa using hy₁n)
  obtain ⟨j, hj⟩ := dih_rot_of_pow (hodd.pow) hφ₁n
  have hq₁ : φ₁ (⟨y₁, hy₁⟩ * (a₁ ^ j.val)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, ha₁, hj, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val,
      mul_inv_cancel]
  have hq₁Q : y₁ * ((a₁ : G) ^ j.val)⁻¹ ∈ Q := by simpa using (hker₁ _).mp hq₁
  have hφ₂n : φ₂ ⟨y₂, hy₂⟩ ^ (p ^ k) = 1 := by
    rw [← map_pow]
    exact (hker₂ _).mpr (by simpa using hy₂n)
  obtain ⟨j', hj'⟩ := dih_rot_of_pow (hodd.pow) hφ₂n
  have hq₂ : φ₂ (⟨y₂, hy₂⟩ * (a₂ ^ j'.val)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, ha₂, hj', DihedralGroup.r_one_pow, ZMod.natCast_zmod_val,
      mul_inv_cancel]
  have hq₂Q : y₂ * ((a₂ : G) ^ j'.val)⁻¹ ∈ Q := by simpa using (hker₂ _).mp hq₂
  refine ⟨j.val, j'.val, ?_⟩
  have e1 : π ⟨y₁, hy₁H⟩ = π ⟨(a₁ : G), h.le (h.le₁ a₁.2)⟩ ^ j.val := by
    have h1 : π ((⟨y₁, hy₁H⟩ : ↥H) * (⟨(a₁ : G), h.le (h.le₁ a₁.2)⟩ ^ j.val)⁻¹) = 1 :=
      (hπ1 _).mpr (by simpa using hq₁Q)
    rw [map_mul, map_inv, map_pow] at h1
    exact mul_inv_eq_one.mp h1
  have e2 : π ⟨y₂, hy₂H⟩ = π ⟨(a₂ : G), h.le (h.le₂ a₂.2)⟩ ^ j'.val := by
    have h1 : π ((⟨y₂, hy₂H⟩ : ↥H) * (⟨(a₂ : G), h.le (h.le₂ a₂.2)⟩ ^ j'.val)⁻¹) = 1 :=
      (hπ1 _).mpr (by simpa using hq₂Q)
    rw [map_mul, map_inv, map_pow] at h1
    exact mul_inv_eq_one.mp h1
  have e3 : (⟨y₁ * y₂, hred.le hy⟩ : ↥H) = ⟨y₁, hy₁H⟩ * ⟨y₂, hy₂H⟩ := rfl
  show π ⟨y₁ * y₂, hred.le hy⟩ = _
  rw [e3, map_mul, e1, e2]
  rfl

end Rot

end CFSG.Quasithin
