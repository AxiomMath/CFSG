module

public import CFSG.RankThree.PartTwo.Sec16.Kcd166.FixRank
import CFSG.RankThree.PartTwo.Sec16.Kcd166.A6Fixed
import CFSG.GroupTheory.SectionLemmas
public import CFSG.GroupTheory.ABGLocalTools.PStabilityModule

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open Subgroup
open CFSG.ABGLocalTools
open scoped commutatorElement IsMulCommutative

private lemma conj_mem_of_normal_subgroupOf {G : Type*} [Group G] {N M : Subgroup G}
    (hNM : N ≤ M) (hNn : (N.subgroupOf M).Normal) {m n : G} (hm : m ∈ M) (hn : n ∈ N) :
    m * n * m⁻¹ ∈ N := by
  have h := hNn.conj_mem ⟨n, hNM hn⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨m, hm⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

private def fixedPointsSubgroup {G : Type*} [Group G] (M N : Subgroup G) (t : G)
    (htN : t ∈ Subgroup.normalizer (N : Set G)) (hNM : N ≤ M)
    (hNn : (N.subgroupOf M).Normal) : Subgroup G where
  carrier := {x : G | x ∈ M ∧ t * x * t⁻¹ * x⁻¹ ∈ N}
  one_mem' := by
    refine ⟨M.one_mem, ?_⟩
    simp
  mul_mem' := by
    intro x y hx hy
    obtain ⟨hxM, hxN⟩ := hx
    obtain ⟨hyM, hyN⟩ := hy
    refine ⟨M.mul_mem hxM hyM, ?_⟩
    have h2 : x * (t * y * t⁻¹ * y⁻¹) * x⁻¹ ∈ N :=
      conj_mem_of_normal_subgroupOf hNM hNn hxM hyN
    have hcalc : t * (x * y) * t⁻¹ * (x * y)⁻¹ =
        (t * x * t⁻¹ * x⁻¹) * (x * (t * y * t⁻¹ * y⁻¹) * x⁻¹) := by
      group
    rw [hcalc]
    exact N.mul_mem hxN h2
  inv_mem' := by
    intro x hx
    obtain ⟨hxM, hxN⟩ := hx
    refine ⟨M.inv_mem hxM, ?_⟩
    have h2 : x⁻¹ * (t * x * t⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ ∈ N :=
      conj_mem_of_normal_subgroupOf hNM hNn (M.inv_mem hxM) (N.inv_mem hxN)
    have hcalc : t * x⁻¹ * t⁻¹ * x⁻¹⁻¹ =
        x⁻¹ * (t * x * t⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by
      group
    rw [hcalc]
    exact h2

private lemma mem_fixedPointsSubgroup {G : Type*} [Group G] {M N : Subgroup G} {t : G}
    (htN : t ∈ Subgroup.normalizer (N : Set G)) (hNM : N ≤ M)
    (hNn : (N.subgroupOf M).Normal) {x : G} :
    x ∈ fixedPointsSubgroup M N t htN hNM hNn ↔
      x ∈ M ∧ t * x * t⁻¹ * x⁻¹ ∈ N := Iff.rfl

private lemma fixedPointsSubgroup_le {G : Type*} [Group G] {M N : Subgroup G} {t : G}
    (htN : t ∈ Subgroup.normalizer (N : Set G)) (hNM : N ≤ M)
    (hNn : (N.subgroupOf M).Normal) :
    fixedPointsSubgroup M N t htN hNM hNn ≤ M := fun _ hx => hx.1

private lemma le_fixedPointsSubgroup {G : Type*} [Group G] {M N : Subgroup G} {t : G}
    (htN : t ∈ Subgroup.normalizer (N : Set G)) (hNM : N ≤ M)
    (hNn : (N.subgroupOf M).Normal) :
    N ≤ fixedPointsSubgroup M N t htN hNM hNn := by
  intro n hn
  refine ⟨hNM hn, ?_⟩
  exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp htN n).mp hn) (N.inv_mem hn)

private lemma fixedPointsSubgroup_normalizer {G : Type*} [Group G] [Finite G]
    {M N : Subgroup G} {t σ : G}
    (htN : t ∈ Subgroup.normalizer (N : Set G)) (hNM : N ≤ M)
    (hNn : (N.subgroupOf M).Normal) (hσM : σ ∈ Subgroup.normalizer (M : Set G))
    (hσN : σ ∈ Subgroup.normalizer (N : Set G)) (hσt : σ * t = t * σ) :
    σ ∈ Subgroup.normalizer
      (fixedPointsSubgroup M N t htN hNM hNn : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, ⟨hxM, hxN⟩, rfl⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hσM x).mp hxM, ?_⟩
    have hconj : σ * (t * x * t⁻¹ * x⁻¹) * σ⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp hσN _).mp hxN
    have hconj_mul : MulAut.conj t * MulAut.conj σ = MulAut.conj σ * MulAut.conj t := by
      calc MulAut.conj t * MulAut.conj σ = MulAut.conj (t * σ) := (map_mul _ t σ).symm
        _ = MulAut.conj (σ * t) := by rw [hσt]
        _ = MulAut.conj σ * MulAut.conj t := map_mul _ σ t
    have hcomm : (MulAut.conj t) ((MulAut.conj σ) x) =
        (MulAut.conj σ) ((MulAut.conj t) x) := by
      have := congrArg (fun e : MulAut G => e x) hconj_mul
      simpa [MulAut.mul_apply] using this
    have hcomm' : t * (σ * x * σ⁻¹) * t⁻¹ = σ * (t * x * t⁻¹) * σ⁻¹ := by
      simpa only [MulAut.conj_apply] using hcomm
    have hcalc : t * (σ * x * σ⁻¹) * t⁻¹ * (σ * x * σ⁻¹)⁻¹ =
        σ * (t * x * t⁻¹ * x⁻¹) * σ⁻¹ := by
      rw [hcomm']
      group
    change t * (σ * x * σ⁻¹) * t⁻¹ * (σ * x * σ⁻¹)⁻¹ ∈ N
    rw [hcalc]
    exact hconj
  · rw [Subgroup.card_map_of_injective (MulAut.conj σ).injective]

private lemma exists_twoElement_lift {G : Type*} [Group G] [Finite G] {J : Subgroup G}
    (π : ↥J →* alternatingGroup (Fin 6)) (j₀ : ↥J) {t₀ : alternatingGroup (Fin 6)}
    (hπj₀ : π j₀ = t₀) (ht₀_sq : t₀ * t₀ = 1) (ht₀_ne : t₀ ≠ 1) :
    ∃ (b : ℕ) (t : G) (htJ : t ∈ J),
      Odd b ∧ t = (j₀ : G) ^ b ∧ π (j₀ ^ b) = t₀ ∧
        IsPGroup 2 (Subgroup.zpowers t) ∧ t ≠ 1 := by
  obtain ⟨k, b, hbodd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos j₀).ne'
  let t : G := (j₀ : G) ^ b
  have htpow : t ^ (2 ^ k) = 1 := by
    have hG : ((j₀ : G) ^ orderOf j₀) = 1 := by
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
        congrArg (fun x : ↥J => (x : G)) (pow_orderOf_eq_one j₀)
    dsimp only [t]
    rw [← pow_mul, mul_comm b (2 ^ k), ← hord]
    exact hG
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) := by
    apply IsPGroup.of_card_dvd_pow (n := k)
    rw [Nat.card_zpowers, orderOf_dvd_iff_pow_eq_one]
    exact htpow
  have ht0pow : t₀ ^ b = t₀ := by
    obtain ⟨l, rfl⟩ := hbodd
    rw [pow_succ, pow_mul, pow_two, ht₀_sq, one_pow, one_mul]
  have hπjb : π (j₀ ^ b) = t₀ := by
    rw [map_pow, hπj₀, ht0pow]
  have htJ : t ∈ J := by
    dsimp only [t]
    exact J.pow_mem j₀.2 b
  have ht1 : t ≠ 1 := by
    intro ht
    have hsub : (j₀ ^ b : ↥J) = 1 := by
      apply Subtype.ext
      simpa [t] using ht
    have hπ1 : π (j₀ ^ b) = 1 := by rw [hsub, map_one]
    rw [hπjb] at hπ1
    exact ht₀_ne hπ1
  exact ⟨b, t, htJ, hbodd, rfl, hπjb, ht2, ht1⟩

private lemma exists_involution_data {G : Type*} [Group G] [Finite G] {J : Subgroup G}
    (π : ↥J →* alternatingGroup (Fin 6)) (hπ : Function.Surjective π) :
    ∃ (t₀ : alternatingGroup (Fin 6)) (j₀ : ↥J) (b : ℕ) (t : G) (htJ : t ∈ J),
      t₀ * t₀ = 1 ∧ t₀ ≠ 1 ∧ π j₀ = t₀ ∧ Odd b ∧ t = (j₀ : G) ^ b ∧
        π (j₀ ^ b) = t₀ ∧ IsPGroup 2 (Subgroup.zpowers t) ∧ t ≠ 1 := by
  let t₀ : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
      exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
        (Equiv.Perm.swap_isSwap_iff.mpr (by decide))⟩
  have ht₀_sq : t₀ * t₀ = 1 := by decide
  have ht₀_ne : t₀ ≠ 1 := by decide
  obtain ⟨j₀, hπj₀⟩ := hπ t₀
  obtain ⟨b, t, htJ, hbodd, ht_eq, hπj₀b, ht2, ht1⟩ :=
    exists_twoElement_lift π j₀ hπj₀ ht₀_sq ht₀_ne
  exact ⟨t₀, j₀, b, t, htJ, ht₀_sq, ht₀_ne, hπj₀, hbodd, ht_eq, hπj₀b, ht2, ht1⟩

private lemma mk_conj_eq_mk_iff {G : Type*} [Group G] {M N : Subgroup G}
    [hNn : (N.subgroupOf M).Normal] {t : G}
    (htM : t ∈ Subgroup.normalizer (M : Set G)) {m : G} (hm : m ∈ M) :
    ((⟨t * m * t⁻¹, (Subgroup.mem_normalizer_iff.mp htM m).mp hm⟩ : ↥M) :
        ↥M ⧸ N.subgroupOf M) = (⟨m, hm⟩ : ↥M) ↔
      t * m * t⁻¹ * m⁻¹ ∈ N := by
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
  simp [div_eq_mul_inv]

private lemma relIndex_eq_card_range_mk {G : Type*} [Group G] [Finite G]
    {M N F : Subgroup G} [hNn : (N.subgroupOf M).Normal] (hFM : F ≤ M) :
    N.relIndex F = Nat.card
      (((QuotientGroup.mk' (N.subgroupOf M)).comp (Subgroup.inclusion hFM)).range) := by
  let q : ↥F →* ↥M ⧸ N.subgroupOf M :=
    (QuotientGroup.mk' (N.subgroupOf M)).comp (Subgroup.inclusion hFM)
  have hkerq : q.ker = N.subgroupOf F := by
    ext f
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change ((Subgroup.inclusion hFM f : ↥M) : ↥M ⧸ N.subgroupOf M) = 1 ↔
      (f : G) ∈ N
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simp
  have h1 : N.relIndex F = (N.subgroupOf F).index := rfl
  rw [h1, ← Subgroup.relIndex_top_right (H := N.subgroupOf F), ← hkerq,
    Subgroup.relIndex_ker, ← MonoidHom.range_eq_map q]

private lemma ker_subset_ofMul_range {G H : Type*} [Group G] [Group H]
    {p : ℕ} [Fact p.Prime] {M N F : Subgroup G} {t : G}
    [hNn : (N.subgroupOf M).Normal]
    [IsElementaryAbelian p (↥M ⧸ N.subgroupOf M)]
    (htM : t ∈ Subgroup.normalizer (M : Set G)) (hFM : F ≤ M)
    (hmemF : ∀ x : G, x ∈ F ↔ x ∈ M ∧ t * x * t⁻¹ * x⁻¹ ∈ N)
    (ρ : H →* Additive (↥M ⧸ N.subgroupOf M) →ₗ[ZMod p]
      Additive (↥M ⧸ N.subgroupOf M)) (t₀ : H)
    (ha : ∀ m : ↥M,
      ρ t₀ (Additive.ofMul ((m : ↥M) : ↥M ⧸ N.subgroupOf M)) =
        Additive.ofMul ((QuotientGroup.mk' (N.subgroupOf M))
          ⟨t * (m : G) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htM (m : G)).mp m.2⟩)) :
    (LinearMap.ker (ρ t₀ - 1) : Set (Additive (↥M ⧸ N.subgroupOf M))) ⊆
      Additive.ofMul '' (((QuotientGroup.mk' (N.subgroupOf M)).comp
        (Subgroup.inclusion hFM)).range : Set (↥M ⧸ N.subgroupOf M)) := by
  let Q := ↥M ⧸ N.subgroupOf M
  let V := Additive Q
  intro v hv
  have hvfix : ρ t₀ v = v := by
    change v ∈ LinearMap.ker ((ρ t₀ : V →ₗ[ZMod p] V) - 1) at hv
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
  obtain ⟨m, hm⟩ := exists_ofMul_mk (W₁ := M) (W₂ := N) v
  have hm' : v = Additive.ofMul ((m : ↥M) : Q) := hm
  have hclass : ((⟨t * (m : G) * t⁻¹,
      (Subgroup.mem_normalizer_iff.mp htM (m : G)).mp m.2⟩ : ↥M) : Q) = (m : Q) := by
    have h1 := ha m
    rw [hm'] at hvfix
    rw [h1] at hvfix
    exact Additive.ofMul.injective hvfix
  have hmN : t * (m : G) * t⁻¹ * (m : G)⁻¹ ∈ N :=
    (mk_conj_eq_mk_iff htM m.2).mp hclass
  have hmF : (m : G) ∈ F := (hmemF _).mpr ⟨m.2, hmN⟩
  let f : ↥F := ⟨(m : G), hmF⟩
  let q : ↥F →* Q :=
    (QuotientGroup.mk' (N.subgroupOf M)).comp (Subgroup.inclusion hFM)
  refine ⟨q f, MonoidHom.mem_range.mpr ⟨f, rfl⟩, ?_⟩
  rw [hm']
  apply congrArg Additive.ofMul
  change ((⟨(m : G), hFM hmF⟩ : ↥M) : Q) = (m : Q)
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
  simp

private lemma ofMul_range_subset_ker {G H : Type*} [Group G] [Group H]
    {p : ℕ} [Fact p.Prime] {M N F : Subgroup G} {t : G}
    [hNn : (N.subgroupOf M).Normal]
    [IsElementaryAbelian p (↥M ⧸ N.subgroupOf M)]
    (htM : t ∈ Subgroup.normalizer (M : Set G)) (hFM : F ≤ M)
    (hmemF : ∀ x : G, x ∈ F ↔ x ∈ M ∧ t * x * t⁻¹ * x⁻¹ ∈ N)
    (ρ : H →* Additive (↥M ⧸ N.subgroupOf M) →ₗ[ZMod p]
      Additive (↥M ⧸ N.subgroupOf M)) (t₀ : H)
    (ha : ∀ m : ↥M,
      ρ t₀ (Additive.ofMul ((m : ↥M) : ↥M ⧸ N.subgroupOf M)) =
        Additive.ofMul ((QuotientGroup.mk' (N.subgroupOf M))
          ⟨t * (m : G) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htM (m : G)).mp m.2⟩)) :
    Additive.ofMul '' (((QuotientGroup.mk' (N.subgroupOf M)).comp
      (Subgroup.inclusion hFM)).range : Set (↥M ⧸ N.subgroupOf M)) ⊆
      (LinearMap.ker (ρ t₀ - 1) : Set (Additive (↥M ⧸ N.subgroupOf M))) := by
  let Q := ↥M ⧸ N.subgroupOf M
  let V := Additive Q
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hy
  have hfN : t * (f : G) * t⁻¹ * (f : G)⁻¹ ∈ N := ((hmemF _).mp f.2).2
  have hclass : ((⟨t * (f : G) * t⁻¹,
      (Subgroup.mem_normalizer_iff.mp htM (f : G)).mp (hFM f.2)⟩ : ↥M) : Q) =
      ((⟨(f : G), hFM f.2⟩ : ↥M) : Q) :=
    (mk_conj_eq_mk_iff (m := (f : G)) htM (hFM f.2)).mpr hfN
  have h1 := ha ⟨(f : G), hFM f.2⟩
  change (ρ t₀) (Additive.ofMul ((⟨(f : G), hFM f.2⟩ : ↥M) : Q)) =
    Additive.ofMul ((⟨t * (f : G) * t⁻¹,
      (Subgroup.mem_normalizer_iff.mp htM (f : G)).mp (hFM f.2)⟩ : ↥M) : Q) at h1
  rw [hclass] at h1
  let q : ↥F →* Q :=
    (QuotientGroup.mk' (N.subgroupOf M)).comp (Subgroup.inclusion hFM)
  change Additive.ofMul (q f) ∈ LinearMap.ker ((ρ t₀ : V →ₗ[ZMod p] V) - 1)
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  change (ρ t₀) (Additive.ofMul ((⟨(f : G), hFM f.2⟩ : ↥M) : Q)) =
    Additive.ofMul ((⟨(f : G), hFM f.2⟩ : ↥M) : Q)
  exact h1

private lemma relIndex_fixedPointsSubgroup_eq_card_ker {G H : Type*} [Group G] [Finite G]
    [Group H] {p : ℕ} [Fact p.Prime]
    {M N F : Subgroup G} {t : G}
    [hNn : (N.subgroupOf M).Normal]
    [IsElementaryAbelian p (↥M ⧸ N.subgroupOf M)]
    (htM : t ∈ Subgroup.normalizer (M : Set G))
    (htN : t ∈ Subgroup.normalizer (N : Set G))
    (hNM : N ≤ M)
    (hF : F = fixedPointsSubgroup M N t htN hNM hNn)
    (ρ : H →* Additive (↥M ⧸ N.subgroupOf M) →ₗ[ZMod p]
      Additive (↥M ⧸ N.subgroupOf M)) (t₀ : H)
    (ha : ∀ m : ↥M,
      ρ t₀ (Additive.ofMul ((m : ↥M) : ↥M ⧸ N.subgroupOf M)) =
        Additive.ofMul ((QuotientGroup.mk' (N.subgroupOf M))
          ⟨t * (m : G) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htM (m : G)).mp m.2⟩)) :
    N.relIndex F = Nat.card (LinearMap.ker (ρ t₀ - 1)) := by
  classical
  have hmemF : ∀ x : G, x ∈ F ↔ x ∈ M ∧ t * x * t⁻¹ * x⁻¹ ∈ N := by
    intro x
    rw [hF, mem_fixedPointsSubgroup]
  have hFM : F ≤ M := fun x hx => ((hmemF x).mp hx).1
  let Q := ↥M ⧸ N.subgroupOf M
  let q : ↥F →* Q :=
    (QuotientGroup.mk' (N.subgroupOf M)).comp (Subgroup.inclusion hFM)
  have hrelq : N.relIndex F = Nat.card q.range := by
    simpa only [q, QuotientGroup.mk'_apply] using relIndex_eq_card_range_mk (G := G) hFM
  have hsub : (LinearMap.ker (ρ t₀ - 1) : Set (Additive Q)) ⊆
      Additive.ofMul '' (q.range : Set Q) := by
    simpa [q] using ker_subset_ofMul_range htM hFM hmemF ρ t₀ ha
  have hsup : Additive.ofMul '' (q.range : Set Q) ⊆
      (LinearMap.ker (ρ t₀ - 1) : Set (Additive Q)) := by
    simpa [q] using ofMul_range_subset_ker htM hFM hmemF ρ t₀ ha
  have hsetK : (LinearMap.ker (ρ t₀ - 1) : Set (Additive Q)) =
      Additive.ofMul '' (q.range : Set Q) :=
    le_antisymm hsub hsup
  have hcardK : Nat.card (LinearMap.ker (ρ t₀ - 1)) = Nat.card q.range := by
    calc Nat.card (LinearMap.ker (ρ t₀ - 1))
        = Nat.card (Additive.ofMul '' (q.range : Set Q)) :=
          Nat.card_congr (Set.equivOfEq hsetK)
      _ = Nat.card q.range :=
          (Nat.card_congr (Equiv.Set.image Additive.ofMul (q.range : Set Q)
            Additive.ofMul.injective)).symm
  rw [hrelq, ← hcardK]

private lemma action_formula {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {M N J : Subgroup G} [hNn : (N.subgroupOf M).Normal]
    [IsElementaryAbelian p (↥M ⧸ N.subgroupOf M)]
    (hJM : J ≤ Subgroup.normalizer (M : Set G))
    (hJN : J ≤ Subgroup.normalizer (N : Set G))
    {π : ↥J →* ↥(alternatingGroup (Fin 6))}
    {ρ : Representation (ZMod p) (↥(alternatingGroup (Fin 6)))
      (Additive (↥M ⧸ N.subgroupOf M))}
    (hρ : ∀ j : ↥J, ρ (π j) =
      ((chiefRep (p := p) hJM hJN j : LinearMap.GeneralLinearGroup (ZMod p)
        (Additive (↥M ⧸ N.subgroupOf M))) :
        Additive (↥M ⧸ N.subgroupOf M) →ₗ[ZMod p] Additive (↥M ⧸ N.subgroupOf M)))
    {j₀ : ↥J} {b : ℕ} {t : G} {t₀ : ↥(alternatingGroup (Fin 6))}
    (hπj₀b : π (j₀ ^ b) = t₀) (ht_eq : t = (j₀ : G) ^ b)
    (htM : t ∈ Subgroup.normalizer (M : Set G)) :
    ∀ m : ↥M,
      ρ t₀ (Additive.ofMul ((m : ↥M) : ↥M ⧸ N.subgroupOf M)) =
        Additive.ofMul ((QuotientGroup.mk' (N.subgroupOf M))
          ⟨t * (m : G) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htM (m : G)).mp m.2⟩) := by
  intro m
  have hρt0 : ρ t₀ = ((chiefRep (p := p) hJM hJN (j₀ ^ b) :
      LinearMap.GeneralLinearGroup (ZMod p) (Additive (↥M ⧸ N.subgroupOf M))) :
      Additive (↥M ⧸ N.subgroupOf M) →ₗ[ZMod p] Additive (↥M ⧸ N.subgroupOf M)) := by
    rw [← hπj₀b]
    exact hρ (j₀ ^ b)
  rw [hρt0]
  have hc : chiefConj hJM (j₀ ^ b) m =
      ⟨t * (m : G) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htM (m : G)).mp m.2⟩ := by
    apply Subtype.ext
    rw [chiefConj_apply_coe]
    simp [ht_eq]
  have h := chiefRep_apply_mk (p := p) hJM hJN (j₀ ^ b) m
  rw [hc] at h
  simpa using h

private lemma exists_representation_lift {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {M N J : Subgroup G} [hNn : (N.subgroupOf M).Normal]
    [IsElementaryAbelian p (↥M ⧸ N.subgroupOf M)]
    (hJM : J ≤ Subgroup.normalizer (M : Set G))
    (hJN : J ≤ Subgroup.normalizer (N : Set G))
    (π : ↥J →* ↥(alternatingGroup (Fin 6))) (hπ : Function.Surjective π)
    (hker : ∀ k : ↥J, π k = 1 → ∀ m ∈ M, (k : G) * m * (k : G)⁻¹ * m⁻¹ ∈ N) :
    ∃ ρ : Representation (ZMod p) (↥(alternatingGroup (Fin 6)))
      (Additive (↥M ⧸ N.subgroupOf M)),
      ∀ j : ↥J, ρ (π j) =
        ((chiefRep (p := p) hJM hJN j : LinearMap.GeneralLinearGroup (ZMod p)
          (Additive (↥M ⧸ N.subgroupOf M))) :
          Additive (↥M ⧸ N.subgroupOf M) →ₗ[ZMod p] Additive (↥M ⧸ N.subgroupOf M)) := by
  classical
  let V := Additive (↥M ⧸ N.subgroupOf M)
  let ρJ : ↥J →* LinearMap.GeneralLinearGroup (ZMod p) V := chiefRep (p := p) hJM hJN
  have hker_le : π.ker ≤ ρJ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    change chiefRep (p := p) hJM hJN k = 1
    rw [chiefRep_eq_one_iff]
    intro m hm
    have h' : m * (k : G) * m⁻¹ * (k : G)⁻¹ ∈ N := by
      have h := N.inv_mem (hker k hk m hm)
      rwa [show ((k : G) * m * (k : G)⁻¹ * m⁻¹)⁻¹ =
          m * (k : G) * m⁻¹ * (k : G)⁻¹ by group] at h
    rw [commutatorElement_def]
    exact h'
  let ρGL : ↥(alternatingGroup (Fin 6)) →* LinearMap.GeneralLinearGroup (ZMod p) V :=
    MonoidHom.liftOfRightInverse π (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
      ⟨ρJ, hker_le⟩
  have hρGL_comp : ∀ j : ↥J, ρGL (π j) = ρJ j := fun j =>
    MonoidHom.liftOfRightInverse_comp_apply (f := π) (f_inv := Function.surjInv hπ)
      (hf := Function.rightInverse_surjInv hπ) (g := ⟨ρJ, hker_le⟩) (x := j)
  let ρ : Representation (ZMod p) (↥(alternatingGroup (Fin 6))) V :=
    (Units.coeHom (Module.End (ZMod p) V)).comp ρGL
  refine ⟨ρ, ?_⟩
  intro j
  change (ρGL (π j) : V →ₗ[ZMod p] V) = _
  rw [hρGL_comp]

private lemma false_of_relIndex_le_sq {G V : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] (hp5 : 5 ≤ p) {N F : Subgroup G}
    (ρ : Representation (ZMod p) (↥(alternatingGroup (Fin 6))) V)
    (t₀ : ↥(alternatingGroup (Fin 6))) (hρ : ρ ≠ 1)
    (ht₀_sq : t₀ * t₀ = 1) (ht₀_ne : t₀ ≠ 1)
    (hrel_le : N.relIndex F ≤ p ^ 2)
    (hrel_eq : N.relIndex F = Nat.card (LinearMap.ker (ρ t₀ - 1))) : False := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hfin : 3 ≤ Module.finrank (ZMod p) (LinearMap.ker (ρ t₀ - 1)) :=
    three_le_finrank_ker_sub_one_of_alternatingGroup_six h2 h3 ρ hρ ht₀_sq ht₀_ne
  have hcard : Nat.card (LinearMap.ker (ρ t₀ - 1)) =
      p ^ Module.finrank (ZMod p) (LinearMap.ker (ρ t₀ - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hbig : p ^ 3 ≤ N.relIndex F := by
    rw [hrel_eq, hcard]
    exact Nat.pow_le_pow_right (by omega : 0 < p) hfin
  have hp2lt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right (by omega : 1 < p) (by norm_num)
  omega

private lemma contradiction_of_data {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {M N F : Subgroup G} {t : G} [hNn : (N.subgroupOf M).Normal]
    [IsElementaryAbelian p (↥M ⧸ N.subgroupOf M)]
    (htM : t ∈ Subgroup.normalizer (M : Set G))
    (htN : t ∈ Subgroup.normalizer (N : Set G))
    (hNM : N ≤ M)
    (hF : F = fixedPointsSubgroup M N t htN hNM hNn)
    {J : Subgroup G} (hJM : J ≤ Subgroup.normalizer (M : Set G))
    (hJN : J ≤ Subgroup.normalizer (N : Set G))
    {π : ↥J →* ↥(alternatingGroup (Fin 6))}
    {ρ : Representation (ZMod p) (↥(alternatingGroup (Fin 6)))
      (Additive (↥M ⧸ N.subgroupOf M))}
    (hρ_comp : ∀ j : ↥J, ρ (π j) =
      ((chiefRep (p := p) hJM hJN j : LinearMap.GeneralLinearGroup (ZMod p)
        (Additive (↥M ⧸ N.subgroupOf M))) :
        Additive (↥M ⧸ N.subgroupOf M) →ₗ[ZMod p]
          Additive (↥M ⧸ N.subgroupOf M)))
    (hρ : ρ ≠ 1)
    {j₀ : ↥J} {b : ℕ} {t₀ : ↥(alternatingGroup (Fin 6))}
    (hπj₀b : π (j₀ ^ b) = t₀) (ht_eq : t = (j₀ : G) ^ b)
    (ht₀_sq : t₀ * t₀ = 1) (ht₀_ne : t₀ ≠ 1)
    (hrel_le : N.relIndex F ≤ p ^ 2) : False := by
  have htM_conj : ∀ m : ↥M, t * (m : G) * t⁻¹ ∈ M := fun m =>
    (Subgroup.mem_normalizer_iff.mp htM (m : G)).mp m.2
  have hρt0 : ρ t₀ = ((chiefRep (p := p) hJM hJN (j₀ ^ b) :
      LinearMap.GeneralLinearGroup (ZMod p) (Additive (↥M ⧸ N.subgroupOf M))) :
      Additive (↥M ⧸ N.subgroupOf M) →ₗ[ZMod p]
        Additive (↥M ⧸ N.subgroupOf M)) := by
    rw [← hπj₀b]
    exact hρ_comp (j₀ ^ b)
  have hρt_apply : ∀ m : ↥M,
      ρ t₀ (Additive.ofMul ((m : ↥M) : ↥M ⧸ N.subgroupOf M)) =
        Additive.ofMul ((QuotientGroup.mk' (N.subgroupOf M))
          ⟨t * (m : G) * t⁻¹, htM_conj m⟩) :=
    action_formula hJM hJN hρ_comp hπj₀b ht_eq htM
  have hrel_eq : N.relIndex F = Nat.card (LinearMap.ker (ρ t₀ - 1)) :=
    relIndex_fixedPointsSubgroup_eq_card_ker (hNn := hNn) htM htN hNM hF ρ t₀ hρt_apply
  exact false_of_relIndex_le_sq hp5 ρ t₀ hρ ht₀_sq ht₀_ne hrel_le hrel_eq

theorem commutator_le_of_surjective_alternatingGroup_six
    (hK1 : CFSG.RankThree.PartTwo.KFacts.BlackburnScalarAut)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hloc : ∀ S E : Subgroup G, S ≠ ⊥ → IsPGroup 2 S → E ≤ Subgroup.normalizer (S : Set G) →
      IsMulCommutative E → (∀ e ∈ E, e ^ p = 1) → Nat.card E ≤ p ^ 2)
    {M N : Subgroup G} (hMp : IsPGroup p M) (hNM : N ≤ M) (hNn : (N.subgroupOf M).Normal)
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hexp : ∀ x ∈ M, x ^ p ∈ N)
    {J : Subgroup G} (hJM : J ≤ Subgroup.normalizer (M : Set G))
    (hJN : J ≤ Subgroup.normalizer (N : Set G))
    (π : ↥J →* ↥(alternatingGroup (Fin 6))) (hπ : Function.Surjective π)
    (hker : ∀ k : ↥J, π k = 1 → ∀ m ∈ M, (k : G) * m * (k : G)⁻¹ * m⁻¹ ∈ N)
    {σ : G} (hσ3 : σ ^ 3 = 1) (hσJ : J ≤ Subgroup.centralizer ({σ} : Set G))
    (hσM : σ ∈ Subgroup.normalizer (M : Set G)) (hσN : σ ∈ Subgroup.normalizer (N : Set G))
    (hfpf : ∀ m ∈ M, σ * m * σ⁻¹ * m⁻¹ ∈ N → m ∈ N)
    (hsc : p % 3 = 1 → ∃ w : ℕ, ∀ m ∈ M, σ * m * σ⁻¹ * (m ^ w)⁻¹ ∈ N) :
    ⁅M, J⁆ ≤ N := by
  classical
  haveI hNnormal : (N.subgroupOf M).Normal := hNn
  let Q := ↥M ⧸ N.subgroupOf M
  haveI hEA : IsElementaryAbelian p Q :=
    CFSG.GroupTheory.isElementaryAbelian_quotient_of_commutator_pow (p := p) hab hexp le_rfl
  let V := Additive Q
  haveI hVfin : Finite V := by
    dsimp only [V, Q]
    infer_instance
  haveI hVfd : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  let ρJ : ↥J →* LinearMap.GeneralLinearGroup (ZMod p) V :=
    chiefRep (p := p) hJM hJN
  obtain ⟨ρ, hρ_comp⟩ := exists_representation_lift (p := p) hJM hJN π hπ hker
  by_contra hcon
  rw [Subgroup.commutator_le] at hcon
  push Not at hcon
  obtain ⟨m, hmM, j, hjJ, hmj⟩ := hcon
  let jJ : ↥J := ⟨j, hjJ⟩
  have hρJj : ρJ jJ ≠ 1 := by
    intro h1
    exact hmj ((chiefRep_eq_one_iff (p := p) hJM hJN jJ).mp h1 m hmM)
  have hρ : ρ ≠ 1 := by
    intro h1
    apply hρJj
    apply Units.ext
    rw [← hρ_comp jJ, h1]
    rfl
  obtain ⟨t₀, j₀, b, t, htJ, ht₀_sq, ht₀_ne, _, _, ht_eq, hπj₀b, ht2, ht1⟩ :=
    exists_involution_data π hπ
  have htM : t ∈ Subgroup.normalizer (M : Set G) := hJM htJ
  have htN : t ∈ Subgroup.normalizer (N : Set G) := hJN htJ
  have hσj : σ * (j₀ : G) = (j₀ : G) * σ :=
    (Subgroup.mem_centralizer_iff.mp (hσJ j₀.2)) σ (by simp)
  have hσt : σ * t = t * σ := by
    rw [ht_eq]
    exact (Commute.pow_right hσj b).eq
  let F : Subgroup G := fixedPointsSubgroup M N t htN hNM hNn
  have hσF : σ ∈ Subgroup.normalizer (F : Set G) :=
    fixedPointsSubgroup_normalizer htN hNM hNn hσM hσN hσt
  have hFt : ∀ f ∈ F, t * f * t⁻¹ * f⁻¹ ∈ N := fun _ hf => hf.2
  have hrel_le : N.relIndex F ≤ p ^ 2 :=
    relIndex_le_sq_of_order_three hK1 hp5 hloc hMp hNM hNn hab hexp ht2 ht1 htN
      hσ3 hσt hσN hfpf hsc (le_fixedPointsSubgroup htN hNM hNn)
      (fixedPointsSubgroup_le htN hNM hNn) hσF hFt
  exact contradiction_of_data hp5 htM htN hNM rfl hJM hJN hρ_comp hρ
    hπj₀b ht_eq ht₀_sq ht₀_ne hrel_le

end CFSG.RankThree.PartTwo.Sec16.Kcd166
