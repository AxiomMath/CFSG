module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.StandardType

namespace GGL48

open Subgroup MulAction

section Transfer

variable {N : Type*} [Group N]

theorem inv_mul_pow_mul_eq (n g : N) (k : ℕ) : n⁻¹ * g ^ k * n = (n⁻¹ * g * n) ^ k := by
  have h := conj_pow (a := n⁻¹) (b := g) (i := k)
  rw [inv_inv] at h
  exact h.symm

theorem transfer_eq_pow_of_forall_conj {K : Subgroup N} [K.FiniteIndex] {A : Type*}
    [CommGroup A] (ϕ : K →* A) {g : N} (hg : g ∈ K)
    (hconj : ∀ n : N, ∃ h : n⁻¹ * g * n ∈ K, ϕ ⟨n⁻¹ * g * n, h⟩ = ϕ ⟨g, hg⟩) :
    ϕ.transfer g = ϕ ⟨g, hg⟩ ^ K.index := by
  classical
  have : Fintype (Quotient (MulAction.orbitRel (zpowers g) (N ⧸ K))) := Fintype.ofFinite _
  rw [index_eq_sum_minimalPeriod K g, ← Finset.prod_pow_eq_pow_sum,
    MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  refine Finset.prod_congr rfl fun q _ => ?_
  obtain ⟨h, hϕ⟩ := hconj q.out.out
  have e : (⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
      QuotientGroup.out_conj_pow_minimalPeriod_mem K g q.out⟩ : K) =
      ⟨q.out.out⁻¹ * g * q.out.out, h⟩ ^ Function.minimalPeriod (g • ·) q.out := by
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow]
    exact inv_mul_pow_mul_eq _ _ _
  rw [e, map_pow, hϕ]

noncomputable abbrev abQuotMap (K C : Subgroup N) :
    K →* Abelianization K ⧸ (C.subgroupOf K).map Abelianization.of :=
  (QuotientGroup.mk' _).comp Abelianization.of

theorem abQuotMap_eq_one {K C : Subgroup N} {c : K} (hc : (c : N) ∈ C) :
    abQuotMap K C c = 1 := by
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact ⟨c, Subgroup.mem_subgroupOf.mpr hc, rfl⟩

theorem mem_commutator_sup_of_abQuotMap_eq_one {K C : Subgroup N} {x : K}
    (h : abQuotMap K C x = 1) : (x : N) ∈ ⁅K, K⁆ ⊔ C := by
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  obtain ⟨c, hc, hcx⟩ := h
  have hk : c⁻¹ * x ∈ commutator K := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
  have hk' : (c : N)⁻¹ * x ∈ ⁅K, K⁆ := by
    rw [← K.map_subtype_commutator]
    exact ⟨_, hk, rfl⟩
  have e : (x : N) = (c : N) * ((c : N)⁻¹ * x) := by group
  rw [e]
  exact mul_mem (mem_sup_right (Subgroup.mem_subgroupOf.mp hc)) (mem_sup_left hk')

theorem pow_ne_one_of_not_dvd {A : Type*} [Group A] {p : ℕ} [hp : Fact p.Prime] {a : A}
    (ha : a ≠ 1) (hap : a ^ p = 1) {m : ℕ} (hm : ¬ p ∣ m) : a ^ m ≠ 1 := by
  intro h
  have hord : orderOf a = p := orderOf_eq_prime hap ha
  exact hm (hord ▸ orderOf_dvd_of_pow_eq_one h)

theorem not_mem_commutator_of_not_dvd_index [Finite N] {p : ℕ} [Fact p.Prime]
    {K C : Subgroup N} (hCK : C ≤ K) {x : N} (hxK : x ∈ K) (hxp : x ^ p = 1)
    (hconj : ∀ n : N, n⁻¹ * x * n * x⁻¹ ∈ C) (hind : ¬ p ∣ K.index)
    (hx : x ∉ ⁅K, K⁆ ⊔ C) : x ∉ commutator N := by
  classical
  set ϕ := abQuotMap K C with hϕ
  have hϕx : ϕ ⟨x, hxK⟩ ≠ 1 := fun h1 => hx (mem_commutator_sup_of_abQuotMap_eq_one h1)
  have hϕp : ϕ ⟨x, hxK⟩ ^ p = 1 := by
    rw [← map_pow]
    have : (⟨x, hxK⟩ : K) ^ p = 1 := Subtype.ext (by simp [hxp])
    rw [this, map_one]
  have hconj' : ∀ n : N, ∃ h : n⁻¹ * x * n ∈ K, ϕ ⟨n⁻¹ * x * n, h⟩ = ϕ ⟨x, hxK⟩ := by
    intro n
    have hc := hconj n
    have hmem : n⁻¹ * x * n ∈ K := by
      have e : n⁻¹ * x * n = (n⁻¹ * x * n * x⁻¹) * x := by group
      rw [e]
      exact K.mul_mem (hCK hc) hxK
    refine ⟨hmem, ?_⟩
    have e : (⟨n⁻¹ * x * n, hmem⟩ : K) = ⟨n⁻¹ * x * n * x⁻¹, hCK hc⟩ * ⟨x, hxK⟩ :=
      Subtype.ext (by simp)
    rw [e, map_mul, hϕ, abQuotMap_eq_one (c := ⟨_, hCK hc⟩) hc, one_mul]
  have htr := transfer_eq_pow_of_forall_conj ϕ hxK hconj'
  intro hxN
  have h1 : ϕ.transfer x = 1 := Abelianization.commutator_subset_ker ϕ.transfer hxN
  rw [htr] at h1
  exact pow_ne_one_of_not_dvd hϕx hϕp hind h1

theorem not_mem_commutator_sup_of_sylow [Finite N] {p : ℕ} [Fact p.Prime] (P : Sylow p N)
    {Q : Subgroup N} [hQn : Q.Normal] {x : N} (hxc : ∀ n : N, n * x = x * n)
    (hxP : x ∈ (P : Subgroup N)) (hxp : x ^ p = 1)
    (hx : x ∉ ⁅(P : Subgroup N), (P : Subgroup N)⁆ ⊔ Q) :
    x ∉ commutator N ⊔ Q := by
  classical
  set ϕ := abQuotMap (P : Subgroup N) Q with hϕ
  have hϕx : ϕ ⟨x, hxP⟩ ≠ 1 := fun h1 => hx (mem_commutator_sup_of_abQuotMap_eq_one h1)
  have hϕp : ϕ ⟨x, hxP⟩ ^ p = 1 := by
    rw [← map_pow]
    have : (⟨x, hxP⟩ : (P : Subgroup N)) ^ p = 1 := Subtype.ext (by simp [hxp])
    rw [this, map_one]
  have hconj' : ∀ n : N, ∃ h : n⁻¹ * x * n ∈ (P : Subgroup N),
      ϕ ⟨n⁻¹ * x * n, h⟩ = ϕ ⟨x, hxP⟩ := by
    intro n
    have e : n⁻¹ * x * n = x := by
      rw [mul_assoc, ← hxc n, ← mul_assoc, inv_mul_cancel, one_mul]
    have hmem : n⁻¹ * x * n ∈ (P : Subgroup N) := by rw [e]; exact hxP
    refine ⟨hmem, ?_⟩
    rw [show (⟨n⁻¹ * x * n, hmem⟩ : (P : Subgroup N)) = ⟨x, hxP⟩ from Subtype.ext e]
  have htr := transfer_eq_pow_of_forall_conj ϕ hxP hconj'
  have hQ : ∀ q ∈ Q, ϕ.transfer q = 1 := by
    intro q hq
    have : Fintype (Quotient (MulAction.orbitRel (zpowers q) (N ⧸ (P : Subgroup N)))) :=
      Fintype.ofFinite _
    rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
    refine Finset.prod_eq_one fun r _ => ?_
    rw [hϕ]
    apply abQuotMap_eq_one
    have hqm := Q.pow_mem hq (Function.minimalPeriod (q • ·) r.out)
    have h2 := hQn.conj_mem _ hqm r.out.out⁻¹
    simpa using h2
  intro hxN
  rw [Subgroup.mem_sup_of_normal_right] at hxN
  obtain ⟨c, hc, q, hq, rfl⟩ := hxN
  have h1 : ϕ.transfer (c * q) = 1 := by
    rw [map_mul, MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker ϕ.transfer hc),
      hQ q hq, one_mul]
  rw [htr] at h1
  exact pow_ne_one_of_not_dvd hϕx hϕp P.not_dvd_index h1

end Transfer

section Ambient

variable {G : Type*} [Group G]

@[expose] def sylowSubgroupOf {p : ℕ} {H₀ P : Subgroup G} (hPp : IsPGroup p P) (hPH : P ≤ H₀)
    (hPmax : ∀ R : Subgroup G, R ≤ H₀ → IsPGroup p R → P ≤ R → R = P) : Sylow p H₀ :=
  ⟨P.subgroupOf H₀, hPp.comap_of_injective H₀.subtype H₀.subtype_injective, fun {R} hR hPR => by
    have hRm : IsPGroup p (R.map H₀.subtype) := hR.map H₀.subtype
    have hPRm : P ≤ R.map H₀.subtype := fun s hs =>
      ⟨⟨s, hPH hs⟩, hPR (by rw [Subgroup.mem_subgroupOf]; exact hs), rfl⟩
    have heq := hPmax _ (Subgroup.map_subtype_le R) hRm hPRm
    ext g
    rw [Subgroup.mem_subgroupOf, ← heq]
    constructor
    · intro hgR
      exact ⟨g, hgR, rfl⟩
    · rintro ⟨g', hg'R, hgg⟩
      have : g' = g := Subtype.ext hgg
      rw [← this]
      exact hg'R⟩

@[simp]
theorem coe_sylowSubgroupOf {p : ℕ} {H₀ P : Subgroup G} (hPp : IsPGroup p P) (hPH : P ≤ H₀)
    (hPmax : ∀ R : Subgroup G, R ≤ H₀ → IsPGroup p R → P ≤ R → R = P) :
    (sylowSubgroupOf hPp hPH hPmax : Subgroup H₀) = P.subgroupOf H₀ :=
  rfl

theorem not_mem_commutator_sup_of_le_sylow [Finite G] {p : ℕ} [Fact p.Prime]
    {H₀ P Q : Subgroup G} {x : G} (hPp : IsPGroup p P) (hPH : P ≤ H₀)
    (hPmax : ∀ R : Subgroup G, R ≤ H₀ → IsPGroup p R → P ≤ R → R = P)
    (hxc : H₀ ≤ Subgroup.centralizer ({x} : Set G)) (hxP : x ∈ P) (hxp : x ^ p = 1)
    (hQ : H₀ ≤ Subgroup.normalizer (Q : Set G)) (hx : x ∉ ⁅P, P⁆ ⊔ Q) :
    x ∉ ⁅H₀, H₀⁆ ⊔ Q := by
  have hxH : x ∈ H₀ := hPH hxP
  set S : Sylow p H₀ := sylowSubgroupOf hPp hPH hPmax with hS
  have hQn : (Q.subgroupOf H₀).Normal := ⟨fun q hq g => by
    rw [Subgroup.mem_subgroupOf] at hq ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hQ g.2) q).mp hq⟩
  have hxS : (⟨x, hxH⟩ : H₀) ∈ (S : Subgroup H₀) := by
    rw [hS]
    change (⟨x, hxH⟩ : H₀) ∈ P.subgroupOf H₀
    rw [Subgroup.mem_subgroupOf]
    exact hxP
  have hxc' : ∀ n : H₀, n * ⟨x, hxH⟩ = ⟨x, hxH⟩ * n := fun n =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hxc n.2))
  have hxp' : (⟨x, hxH⟩ : H₀) ^ p = 1 := Subtype.ext (by simp [hxp])
  have hx' : (⟨x, hxH⟩ : H₀) ∉ ⁅(S : Subgroup H₀), (S : Subgroup H₀)⁆ ⊔ Q.subgroupOf H₀ := by
    intro h
    apply hx
    have hmap := Subgroup.mem_map_of_mem H₀.subtype h
    rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype] at hmap
    have hSP : (S : Subgroup H₀).map H₀.subtype = P := by
      rw [hS]
      exact Subgroup.map_subgroupOf_eq_of_le hPH
    rw [hSP] at hmap
    exact (sup_le_sup_left (inf_le_left : Q ⊓ H₀ ≤ Q) ⁅P, P⁆) hmap
  have hmain := not_mem_commutator_sup_of_sylow S hxc' hxS hxp' hx'
  intro hxG
  have hkn : ⁅H₀, H₀⁆ ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.commutator_le_self H₀).trans hQ
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hkn] at hxG
  obtain ⟨k, hk, q, hq, hkq⟩ := hxG
  dsimp only at hkq
  have hkH : k ∈ H₀ := Subgroup.commutator_le_self H₀ hk
  have hqH : q ∈ H₀ := by
    have : q = k⁻¹ * x := by rw [← hkq]; group
    rw [this]
    exact H₀.mul_mem (H₀.inv_mem hkH) hxH
  apply hmain
  have hk' : (⟨k, hkH⟩ : H₀) ∈ commutator H₀ := by
    rw [← H₀.map_subtype_commutator] at hk
    obtain ⟨k', hk', hkk'⟩ := hk
    have : k' = ⟨k, hkH⟩ := Subtype.ext hkk'
    rw [← this]
    exact hk'
  have e : (⟨x, hxH⟩ : H₀) = ⟨k, hkH⟩ * ⟨q, hqH⟩ := Subtype.ext hkq.symm
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk')
    (Subgroup.mem_sup_right (by rw [Subgroup.mem_subgroupOf]; exact hq))

end Ambient

end GGL48

end CFSG.StandardType

end
