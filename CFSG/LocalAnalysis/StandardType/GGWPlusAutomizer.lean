module

public import CFSG.LocalAnalysis.StandardType.GGWPlusDefs
public import Mathlib.GroupTheory.Nilpotent
public import TauCeti.Algebra.Group.Coprime

public section

namespace CFSG.StandardType

private lemma mem_sup_decomp {G : Type*} [Group G] {H D A N0 : Subgroup G} [H.Normal]
    (hD : D ≤ N0) (hA : A ≤ N0) (hX : H ⊓ N0 ≤ A) {a : G} (ha : a ∈ A)
    (ha' : a ∈ H ⊔ D) : ∃ x ∈ H ⊓ N0, ∃ c ∈ A ⊓ D, a = x * c := by
  obtain ⟨x, hxH, c, hcD, hxc⟩ := (Subgroup.mem_sup_of_normal_left (s := H) (t := D)).mp ha'
  have hxN0 : x ∈ N0 := by
    have hx : x = a * c⁻¹ := by
      calc x = x * c * c⁻¹ := (mul_inv_cancel_right x c).symm
        _ = a * c⁻¹ := by rw [hxc]
    rw [hx]
    exact N0.mul_mem (hA ha) (N0.inv_mem (hD hcD))
  have hxA : x ∈ A := hX ⟨hxH, hxN0⟩
  have hcA : c ∈ A := by
    have hc : c = x⁻¹ * a := by
      calc c = x⁻¹ * (x * c) := (inv_mul_cancel_left x c).symm
        _ = x⁻¹ * a := by rw [hxc]
    rw [hc]
    exact A.mul_mem (A.inv_mem hxA) ha
  exact ⟨x, ⟨hxH, hxN0⟩, c, ⟨hcA, hcD⟩, hxc.symm⟩

private lemma mem_of_coprime_pow_pow {G : Type*} [Group G] {M : Subgroup G} {e : G} {u v : ℕ}
    (hu : e ^ u ∈ M) (hv : e ^ v ∈ M) (hcop : Nat.Coprime u v) : e ∈ M := by
  obtain ⟨i, j, hij⟩ := TauCeti.exists_zpow_mul_zpow_eq_of_coprime (G := G) hcop
  rw [← hij e]
  exact M.mul_mem (M.zpow_mem hu i) (M.zpow_mem hv j)

theorem wplus_of_automizer {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Inn Eb : Subgroup G) [Inn.Normal]
    (hX : GGSolvQuotLeTwo (Inn ⊓ Subgroup.normalizer (Eb : Set G))
      (Subgroup.centralizer (Eb : Set G)))
    (A M₁ E₁ : Subgroup G) :
    Inn ⊓ Subgroup.normalizer (Eb : Set G) ≤ A → A ≤ Subgroup.normalizer (Eb : Set G) →
    (∀ a ∈ A, (∃ k : ℕ, a ^ p ^ k = 1) → a ∈ Inn ⊔ Subgroup.centralizer (Eb : Set G)) →
    M₁ ≤ E₁ → E₁ ≤ A → A ⊓ Subgroup.centralizer (Eb : Set G) ≤ M₁ →
    A ≤ Subgroup.normalizer (M₁ : Set G) → A ≤ Subgroup.normalizer (E₁ : Set G) →
    (∀ e ∈ E₁, ∃ k : ℕ, e ^ p ^ k ∈ M₁) → ∀ h : G, h ∈ A → A ≤ E₁ ⊔ Subgroup.zpowers h →
    E₁ ≤ M₁ := by
  intro hXA hAN0 hpA hM1E1 hE1A hK hNM1 hNE1 hpE1 h hhA hcyc
  let N0 : Subgroup G := Subgroup.normalizer (Eb : Set G)
  let C : Subgroup G := Subgroup.centralizer (Eb : Set G)
  let X : Subgroup G := Inn ⊓ N0
  let K : Subgroup G := A ⊓ C
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hE1A_normal : (E₁.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE1A).mpr hNE1
  have step1 : ∀ a ∈ A, (∃ k : ℕ, a ^ p ^ k = 1) → ∃ x ∈ X, ∃ c ∈ K, a = x * c := by
    intro a ha hap
    have hsup : a ∈ Inn ⊔ C := hpA a ha hap
    obtain ⟨x, hxX, c, hcK, hac⟩ :=
      mem_sup_decomp (H := Inn) (D := C) (A := A) (N0 := N0)
        (Subgroup.centralizer_le_normalizer (Eb : Set G)) hAN0 hXA ha hsup
    exact ⟨x, hxX, c, hcK, hac⟩
  have step2 : X ⊓ E₁ ≤ M₁ → E₁ ≤ M₁ := by
    intro hXin e heE1
    have hn : orderOf e ≠ 0 := (orderOf_pos e).ne'
    obtain ⟨q, m, hm, hnq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
    have he_m_pelem : (e ^ m) ^ p ^ q = 1 := by
      rw [← pow_mul, mul_comm, ← hnq, pow_orderOf_eq_one]
    have he_m_mem : e ^ m ∈ M₁ := by
      obtain ⟨x, hxX, c, hcK, hxc⟩ := step1 (e ^ m) (hE1A (E₁.pow_mem heE1 m)) ⟨q, he_m_pelem⟩
      have hcM1 : c ∈ M₁ := hK hcK
      have hcE1 : c ∈ E₁ := hM1E1 hcM1
      have hxE1 : x ∈ E₁ := by
        have hx' : x = e ^ m * c⁻¹ := by
          calc x = x * c * c⁻¹ := (mul_inv_cancel_right x c).symm
            _ = e ^ m * c⁻¹ := by rw [← hxc]
        rw [hx']
        exact E₁.mul_mem (E₁.pow_mem heE1 m) (E₁.inv_mem hcE1)
      have hxM1 : x ∈ M₁ := hXin ⟨hxX, hxE1⟩
      rw [hxc]
      exact M₁.mul_mem hxM1 hcM1
    obtain ⟨k, hk⟩ := hpE1 e heE1
    exact mem_of_coprime_pow_pow he_m_mem hk (Nat.Prime.coprime_pow_of_not_dvd hp hm)
  by_contra hnot
  have hXnot : ¬ X ⊓ E₁ ≤ M₁ := fun hle => hnot (step2 hle)
  have hXnot' : ∃ x0, x0 ∈ X ⊓ E₁ ∧ x0 ∉ M₁ := by
    rw [SetLike.le_def] at hXnot
    push Not at hXnot
    exact hXnot
  obtain ⟨x0, hx0XE1, hx0M1⟩ := hXnot'
  have hx0X : x0 ∈ X := hx0XE1.1
  have hx0E1 : x0 ∈ E₁ := hx0XE1.2
  let K₁ : Subgroup X := M₁.subgroupOf X
  let K₂ : Subgroup X := E₁.subgroupOf X
  have hK12 : K₁ ≤ K₂ := by
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hM1E1 (Subgroup.mem_subgroupOf.mp hy))
  have hK12ne : K₁ ≠ K₂ := by
    intro hEq
    have hmem : (⟨x0, hx0X⟩ : X) ∈ K₁ := by
      rw [hEq]
      exact Subgroup.mem_subgroupOf.mpr hx0E1
    exact hx0M1 (Subgroup.mem_subgroupOf.mp hmem)
  haveI hK1normal : K₁.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgnorm : (g : G) ∈ Subgroup.normalizer (M₁ : Set G) := hNM1 (hXA g.2)
    have hnM1 : (n : G) ∈ M₁ := hn
    have hgoal : (g : G) * (n : G) * (g : G)⁻¹ ∈ M₁ :=
      (Subgroup.mem_normalizer_iff.mp hgnorm (n : G)).mp hnM1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hgoal
  have hC_le_K1 : C.subgroupOf X ≤ K₁ := by
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr
      (hK (Subgroup.mem_inf.mpr ⟨hXA y.2, Subgroup.mem_subgroupOf.mp hy⟩))
  let H : Subgroup (X ⧸ K₁) := K₂.map (QuotientGroup.mk' K₁)
  have hHp : IsPGroup p H := by
    intro y
    obtain ⟨x, hxK2, hxy⟩ := Subgroup.mem_map.mp y.2
    have hxE1 : (x : G) ∈ E₁ := Subgroup.mem_subgroupOf.mp hxK2
    obtain ⟨n, hn⟩ := hpE1 (x : G) hxE1
    refine ⟨n, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    have hker : QuotientGroup.mk' K₁ (x ^ p ^ n) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
      exact hn
    rw [← hxy, ← map_pow]
    exact hker
  have hHne : H ≠ ⊥ := by
    intro hbot
    apply hK12ne
    have hle : K₂ ≤ K₁ := by
      have hker := (Subgroup.map_eq_bot_iff K₂ (f := QuotientGroup.mk' K₁)).mp hbot
      rwa [QuotientGroup.ker_mk'] at hker
    exact (le_antisymm hle hK12).symm
  haveI : IsCyclic (A ⧸ E₁.subgroupOf A) := by
    refine IsCyclic.mk ⟨QuotientGroup.mk' (E₁.subgroupOf A) ⟨h, hhA⟩, ?_⟩
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (E₁.subgroupOf A) y
    have hle : Subgroup.zpowers h ≤ Subgroup.normalizer (E₁ : Set G) :=
      Subgroup.zpowers_le.mpr (hNE1 hhA)
    have hasup : (a : G) ∈ E₁ ⊔ Subgroup.zpowers h := hcyc a.2
    obtain ⟨e, heE1, t, ht, haet⟩ : ∃ e ∈ E₁, ∃ t ∈ Subgroup.zpowers h, e * t = (a : G) := by
      have hset : (a : G) ∈ (↑(E₁ ⊔ Subgroup.zpowers h) : Set G) := hasup
      rw [Subgroup.coe_mul_of_right_le_normalizer_left E₁ (Subgroup.zpowers h) hle] at hset
      exact Set.mem_mul.mp hset
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ht
    refine ⟨i, ?_⟩
    change (QuotientGroup.mk' (E₁.subgroupOf A) ⟨h, hhA⟩) ^ i
      = QuotientGroup.mk' (E₁.subgroupOf A) a
    have heA : e ∈ A := hE1A heE1
    have htA : t ∈ A := Subgroup.zpowers_le.mpr hhA ht
    have hmk : QuotientGroup.mk' (E₁.subgroupOf A) a
        = QuotientGroup.mk' (E₁.subgroupOf A) (⟨t, htA⟩ : A) := by
      have ha : a = (⟨e, heA⟩ : A) * ⟨t, htA⟩ := by
        apply Subtype.ext
        simpa only [Subgroup.coe_mul] using haet.symm
      rw [ha, map_mul]
      have he1 : QuotientGroup.mk' (E₁.subgroupOf A) (⟨e, heA⟩ : A) = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact heE1
      rw [he1, one_mul]
    rw [hmk, ← MonoidHom.map_zpow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hi
  let fX : X →* A := Subgroup.inclusion hXA
  have hfXmono : K₁ ≤ (E₁.subgroupOf A).comap fX := by
    intro y hy
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    exact hM1E1 (Subgroup.mem_subgroupOf.mp hy)
  let g : X ⧸ K₁ →* A ⧸ E₁.subgroupOf A :=
    QuotientGroup.map K₁ (E₁.subgroupOf A) fX hfXmono
  have hcomap : (E₁.subgroupOf A).comap fX = K₂ := by
    ext y
    simp only [fX, K₂, Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hgker : g.ker = H := by
    rw [QuotientGroup.ker_map, hcomap]
  have hsolv : Group.IsSolvable (X ⧸ K₁) := by
    have hpker : IsPGroup p g.ker := hgker.symm ▸ hHp
    haveI hnil : Group.IsNilpotent ↥g.ker := IsPGroup.isNilpotent (p := p) hpker
    haveI : Group.IsSolvable ↥g.ker := IsNilpotent.to_isSolvable
    haveI : Group.IsSolvable ↥g.range := by
      haveI : IsCyclic ↥g.range := Subgroup.isCyclic g.range
      exact Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup).mul_comm a b
    haveI : Group.IsSolvable ((X ⧸ K₁) ⧸ g.ker) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (QuotientGroup.quotientKerEquivRange g).toMonoidHom)
        (QuotientGroup.quotientKerEquivRange g).injective
    exact Group.isSolvable_of_subgroup_quotient g.ker
  have hcardX_ge : 3 ≤ Nat.card (X ⧸ K₁) := by
    have hpdvd : p ∣ Nat.card H := by
      rcases IsPGroup.card_eq_or_dvd hHp with h1 | hpd
      · exfalso
        exact hHne (Subgroup.card_eq_one.mp h1)
      · exact hpd
    have hpH : p ≤ Nat.card H := Nat.le_of_dvd Nat.card_pos hpdvd
    have hleH : Nat.card H ≤ Nat.card (X ⧸ K₁) := Subgroup.card_le_card_group H
    have hp3 : 3 ≤ p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    omega
  have hle2 : Nat.card (X ⧸ K₁) ≤ 2 := hX K₁ hC_le_K1 hsolv
  omega

end CFSG.StandardType
