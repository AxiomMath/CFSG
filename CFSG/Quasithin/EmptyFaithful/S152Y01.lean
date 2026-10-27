module

public import CFSG.Quasithin.EmptyFaithful.S14117Coprime

public section

namespace CFSG.Quasithin

open scoped commutatorElement Pointwise

variable {A : Type*} [Group A]

theorem oTwoUpper_commutator_sup_le {B P : Subgroup A} (hP : IsPGroup 2 P)
    (hPB : P ≤ Subgroup.normalizer (B : Set A)) :
    oTwoUpper (⁅B, P⁆ ⊔ P) ≤ ⁅B, P⁆ := by
  have hnormK : P ≤ Subgroup.normalizer ((⁅B, P⁆ : Subgroup A) : Set A) :=
    le_normalizer_commutator_of_le hPB Subgroup.le_normalizer
  have hmul : ((⁅B, P⁆ ⊔ P : Subgroup A) : Set A) = ((⁅B, P⁆ : Subgroup A) : Set A) * (P : Set A) :=
    Subgroup.coe_mul_of_right_le_normalizer_left ⁅B, P⁆ P hnormK
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hx' : x ∈ ((⁅B, P⁆ : Subgroup A) : Set A) * (P : Set A) := by rw [← hmul]; exact hx
  obtain ⟨c, hc, p, hp, rfl⟩ := hx'
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨x', hx', hxe⟩ := A4.exists_pow_mul_eq hc (hnormK hp) (2 ^ k)
  exact ⟨k, by rw [hxe, hk', mul_one]; exact hx'⟩

section Reduction

variable {X N R : Subgroup A}

theorem le_sup_inf_centralizer_of_inverts (hN : N ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set A))
    (hRN : ∀ ρ ∈ R, ∀ n ∈ N, ρ * n = n * ρ) {r : A} (hr : r ∈ R)
    (hinv : ∀ x ∈ X, r * x * r⁻¹ * x ∈ N) (hodd : Odd (N.relIndex X)) :
    X ≤ N ⊔ (X ⊓ Subgroup.centralizer (N : Set A)) := by
  intro x hx
  set D := X ⊓ Subgroup.centralizer (N : Set A) with hD
  have hxn : ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun n hn =>
    (Subgroup.mem_normalizer_iff.mp (hXN hx) n).mp hn
  set m := r * x * r⁻¹ * x with hm
  have hmN : m ∈ N := hinv x hx
  have hr1 : ∀ n ∈ N, r * n * r⁻¹ = n := fun n hn => by
    rw [hRN r hr n hn]; group
  have hr2 : ∀ n ∈ N, r⁻¹ * n * r = n := fun n hn => by
    rw [hRN r⁻¹ (R.inv_mem hr) n hn]; group
  have key : ∀ n ∈ N, x * n * x⁻¹ = m * (x⁻¹ * n * x) * m⁻¹ := by
    intro n hn
    have h1 : r * x * r⁻¹ * n * (r * x * r⁻¹)⁻¹ = x * n * x⁻¹ := by
      have e : r * x * r⁻¹ * n * (r * x * r⁻¹)⁻¹ = r * (x * (r⁻¹ * n * r) * x⁻¹) * r⁻¹ := by group
      rw [e, hr2 n hn]
      exact hr1 _ (hxn n hn)
    have h2 : r * x * r⁻¹ = m * x⁻¹ := by rw [hm]; group
    rw [h2] at h1
    rw [← h1]
    group
  have hy : m⁻¹ * x ^ 2 ∈ Subgroup.centralizer (N : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have h3 := key (x * n * x⁻¹) (hxn n hn)
    have e1 : x * (x * n * x⁻¹) * x⁻¹ = x ^ 2 * n * (x ^ 2)⁻¹ := by rw [sq]; group
    have e2 : m * (x⁻¹ * (x * n * x⁻¹) * x) * m⁻¹ = m * n * m⁻¹ := by group
    rw [e1, e2] at h3
    have h4 : (m⁻¹ * x ^ 2) * n * (m⁻¹ * x ^ 2)⁻¹ = n := by
      have e3 : (m⁻¹ * x ^ 2) * n * (m⁻¹ * x ^ 2)⁻¹ = m⁻¹ * (x ^ 2 * n * (x ^ 2)⁻¹) * m := by group
      rw [e3, h3]; group
    calc n * (m⁻¹ * x ^ 2) = ((m⁻¹ * x ^ 2) * n * (m⁻¹ * x ^ 2)⁻¹) * (m⁻¹ * x ^ 2) := by rw [h4]
      _ = (m⁻¹ * x ^ 2) * n := by group
  have hyD : m⁻¹ * x ^ 2 ∈ D := ⟨X.mul_mem (X.inv_mem (hN hmN)) (X.pow_mem hx 2), hy⟩
  have hsq : x ^ 2 ∈ N ⊔ D := by
    have : x ^ 2 = m * (m⁻¹ * x ^ 2) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hmN hyD
  have hpow : x ^ N.relIndex X ∈ N := by
    have : (N.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr hXN
    have := Subgroup.pow_index_mem (N.subgroupOf X) (⟨x, hx⟩ : X)
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨k, hk⟩ := hodd
  have hxk : x = ((x ^ 2) ^ k)⁻¹ * x ^ N.relIndex X := by
    rw [hk, ← pow_mul, pow_succ]
    group
  rw [hxk]
  exact (N ⊔ D).mul_mem ((N ⊔ D).inv_mem ((N ⊔ D).pow_mem hsq k))
    (Subgroup.mem_sup_left hpow)

theorem commutator_eq_of_le_sup_inf_centralizer (hXN : X ≤ Subgroup.normalizer (N : Set A))
    (hRN : ∀ ρ ∈ R, ∀ n ∈ N, ρ * n = n * ρ)
    (hX : X ≤ N ⊔ (X ⊓ Subgroup.centralizer (N : Set A))) :
    ⁅X, R⁆ = ⁅X ⊓ Subgroup.centralizer (N : Set A), R⁆ := by
  set D := X ⊓ Subgroup.centralizer (N : Set A) with hD
  apply le_antisymm _ (Subgroup.commutator_mono inf_le_left le_rfl)
  rw [Subgroup.commutator_le]
  intro x hx ρ hρ
  have hDN : D ≤ Subgroup.normalizer (N : Set A) := inf_le_left.trans hXN
  have hmul : ((N ⊔ D : Subgroup A) : Set A) = (N : Set A) * (D : Set A) :=
    Subgroup.coe_mul_of_right_le_normalizer_left N D hDN
  have hx' : x ∈ (N : Set A) * (D : Set A) := by rw [← hmul]; exact hX hx
  obtain ⟨n, hn, d, hd, rfl⟩ := hx'
  have hnρ : Commute n ρ := by
    unfold Commute SemiconjBy
    exact (hRN ρ hρ n hn).symm
  have hnd : Commute n d := by
    unfold Commute SemiconjBy
    exact Subgroup.mem_centralizer_iff.mp hd.2 n hn
  have hcomm : Commute n (d * (ρ * d⁻¹ * ρ⁻¹)) :=
    hnd.mul_right ((hnρ.mul_right hnd.inv_right).mul_right hnρ.inv_right)
  have h1 : n⁻¹ * ρ⁻¹ = ρ⁻¹ * n⁻¹ := hnρ.inv_inv.eq
  have e : ⁅n * d, ρ⁆ = n * (d * (ρ * d⁻¹ * ρ⁻¹)) * n⁻¹ := by
    simp only [commutatorElement_def]
    calc n * d * ρ * (n * d)⁻¹ * ρ⁻¹ = n * d * ρ * d⁻¹ * (n⁻¹ * ρ⁻¹) := by group
      _ = n * d * ρ * d⁻¹ * (ρ⁻¹ * n⁻¹) := by rw [h1]
      _ = n * (d * (ρ * d⁻¹ * ρ⁻¹)) * n⁻¹ := by group
  have e2 : n * (d * (ρ * d⁻¹ * ρ⁻¹)) * n⁻¹ = ⁅d, ρ⁆ := by
    have := hcomm.eq
    simp only [commutatorElement_def]
    calc n * (d * (ρ * d⁻¹ * ρ⁻¹)) * n⁻¹ = (d * (ρ * d⁻¹ * ρ⁻¹) * n) * n⁻¹ := by rw [this]
      _ = d * ρ * d⁻¹ * ρ⁻¹ := by group
  rw [e, e2]
  exact Subgroup.commutator_mem_commutator hd hρ

end Reduction

end CFSG.Quasithin
