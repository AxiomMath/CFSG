module

public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartOne.S12.Equivariance
import CFSG.GroupTheory.LocalCores.Components
import CFSG.Timmesfeld.Final.Simple

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace S11d

variable {G : Type} [Group G]

def zpowersMul (u v : G) (h : Commute u v) : Subgroup G where
  carrier := {x | ∃ s t : ℤ, x = u ^ s * v ^ t}
  mul_mem' := by
    rintro _ _ ⟨s, t, rfl⟩ ⟨s', t', rfl⟩
    refine ⟨s + s', t + t', ?_⟩
    have h1 : Commute (v ^ t) (u ^ s') := (h.symm.zpow_zpow t s')
    calc u ^ s * v ^ t * (u ^ s' * v ^ t') = u ^ s * (v ^ t * u ^ s') * v ^ t' := by group
      _ = u ^ s * (u ^ s' * v ^ t) * v ^ t' := by rw [h1.eq]
      _ = u ^ (s + s') * v ^ (t + t') := by rw [zpow_add, zpow_add]; group
  one_mem' := ⟨0, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨s, t, rfl⟩
    refine ⟨-s, -t, ?_⟩
    have h1 : Commute (u ^ s) (v ^ t) := h.zpow_zpow s t
    calc (u ^ s * v ^ t)⁻¹ = (v ^ t)⁻¹ * (u ^ s)⁻¹ := by group
      _ = (u ^ s)⁻¹ * (v ^ t)⁻¹ := (h1.symm.inv_inv.eq)
      _ = u ^ (-s) * v ^ (-t) := by rw [zpow_neg, zpow_neg]

theorem mem_zpowers_sup_zpowers_iff {u v : G} (h : Commute u v) {x : G} :
    x ∈ zpowers u ⊔ zpowers v ↔ ∃ s t : ℤ, x = u ^ s * v ^ t := by
  constructor
  · intro hx
    have hle : zpowers u ⊔ zpowers v ≤ zpowersMul u v h := by
      refine sup_le ?_ ?_
      · rw [zpowers_le]
        exact ⟨1, 0, by simp⟩
      · rw [zpowers_le]
        exact ⟨0, 1, by simp⟩
    exact hle hx
  · rintro ⟨s, t, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (zpow_mem (mem_zpowers u) s))
      (Subgroup.mem_sup_right (zpow_mem (mem_zpowers v) t))

def mulZpowers (B : Subgroup G) (c : G) (h : ∀ β ∈ B, Commute β c) : Subgroup G where
  carrier := {x | ∃ β ∈ B, ∃ j : ℤ, x = β * c ^ j}
  mul_mem' := by
    rintro _ _ ⟨β, hβ, j, rfl⟩ ⟨β', hβ', j', rfl⟩
    refine ⟨β * β', B.mul_mem hβ hβ', j + j', ?_⟩
    have h1 : Commute (c ^ j) β' := ((h β' hβ').symm.zpow_left j)
    calc β * c ^ j * (β' * c ^ j') = β * (c ^ j * β') * c ^ j' := by group
      _ = β * (β' * c ^ j) * c ^ j' := by rw [h1.eq]
      _ = β * β' * c ^ (j + j') := by rw [zpow_add]; group
  one_mem' := ⟨1, B.one_mem, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨β, hβ, j, rfl⟩
    refine ⟨β⁻¹, B.inv_mem hβ, -j, ?_⟩
    have h1 : Commute (c ^ j) β := ((h β hβ).symm.zpow_left j)
    calc (β * c ^ j)⁻¹ = (c ^ j)⁻¹ * β⁻¹ := by group
      _ = β⁻¹ * (c ^ j)⁻¹ := (h1.inv_inv.eq)
      _ = β⁻¹ * c ^ (-j) := by rw [zpow_neg]

theorem mem_sup_zpowers_iff {B : Subgroup G} {c : G} (h : ∀ β ∈ B, Commute β c) {a : G} :
    a ∈ B ⊔ zpowers c ↔ ∃ β ∈ B, ∃ j : ℤ, a = β * c ^ j := by
  constructor
  · intro ha
    have hle : B ⊔ zpowers c ≤ mulZpowers B c h := by
      refine sup_le ?_ ?_
      · intro β hβ
        exact ⟨β, hβ, 0, by simp⟩
      · rw [zpowers_le]
        exact ⟨1, B.one_mem, 1, by simp⟩
    exact hle ha
  · rintro ⟨β, hβ, j, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hβ)
      (Subgroup.mem_sup_right (zpow_mem (mem_zpowers c) j))

theorem conj_mem_of_mem_normalizer {H : Subgroup G} {x a : G} (hx : x ∈ normalizer (H : Set G))
    (ha : a ∈ H) : x * a * x⁻¹ ∈ H :=
  (mem_normalizer_iff.mp hx a).mp ha

theorem centralizer_zpow_eq {p : ℕ} (hp : p.Prime) {b : G} (hb : b ^ p = 1) {lam : ℤ}
    (hlam : ¬ (p : ℤ) ∣ lam) :
    Subgroup.centralizer ({b ^ lam} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime (p : ℤ) lam := (Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr hlam
  obtain ⟨v, u, huv⟩ := hcop
  have hbexp : b = (b ^ lam) ^ u := by
    have h1 : b ^ (v * (p : ℤ) + u * lam) = b := by rw [huv, zpow_one]
    have h2 : b ^ (v * (p : ℤ)) = 1 := by
      rw [mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]
    calc b = b ^ (v * (p : ℤ) + u * lam) := h1.symm
      _ = b ^ (v * (p : ℤ)) * b ^ (u * lam) := zpow_add _ _ _
      _ = (b ^ lam) ^ u := by rw [h2, one_mul, mul_comm, zpow_mul]
  apply le_antisymm
  · intro g hg
    rw [mem_centralizer_singleton_iff] at hg ⊢
    have hc : Commute g (b ^ lam) := hg
    have : Commute g ((b ^ lam) ^ u) := hc.zpow_right u
    rw [← hbexp] at this
    exact this.eq
  · intro g hg
    rw [mem_centralizer_singleton_iff] at hg ⊢
    have hc : Commute g b := hg
    exact (hc.zpow_right lam).eq

theorem thetaComponentsAt_congr {p : ℕ} {a a' : G}
    (h : Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({a'} : Set G)) :
    thetaComponentsAt p a = thetaComponentsAt p a' := by
  ext L
  rw [mem_thetaComponentsAt_iff, mem_thetaComponentsAt_iff, h]

theorem conjBy_mem_thetaComponentsAt_of_zpow [Finite G] {p : ℕ} (hp : p.Prime) {b x : G}
    {lam : ℤ} {K : Subgroup G} (hK : K ∈ thetaComponentsAt p b) (hb : b ^ p = 1)
    (hlam : ¬ (p : ℤ) ∣ lam) (hx : x * b * x⁻¹ = b ^ lam) :
    conjBy x K ∈ thetaComponentsAt p b := by
  have h := conjBy_mem_thetaComponentsAt hp x b hK
  rw [hx] at h
  rwa [thetaComponentsAt_congr (p := p) (centralizer_zpow_eq hp hb hlam)] at h

theorem commutator_mem_theta_of_ne [Finite G] {p : ℕ} (hp : p.Prime) {b : G} {K K' : Subgroup G}
    (hK : K ∈ thetaComponentsAt p b) (hK' : K' ∈ thetaComponentsAt p b) (hne : K ≠ K') :
    ∀ k ∈ K, ∀ k' ∈ K', k * k' * k⁻¹ * k'⁻¹ ∈
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G)) := by
  intro k hk k' hk'
  set F := Subgroup.centralizer ({b} : Set G) with hF
  obtain ⟨hKF, hK1⟩ := mem_thetaComponentsAt_iff.mp hK
  obtain ⟨hK'F, hK1'⟩ := mem_thetaComponentsAt_iff.mp hK'
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := F) hp
  set N := aschbacherSolvableCore p F with hN
  set π := QuotientGroup.mk' N with hπ
  have hc₁ := isComponent_map_of_mem_thetaComponents hp hK1
  have hc₂ := isComponent_map_of_mem_thetaComponents hp hK1'
  have hne' : K.subgroupOf F ≠ K'.subgroupOf F := fun h => hne (by
    rw [← Subgroup.map_subgroupOf_eq_of_le hKF, ← Subgroup.map_subgroupOf_eq_of_le hK'F, h])
  have hne'' : (K.subgroupOf F).map π ≠ (K'.subgroupOf F).map π := fun h =>
    hne' (hbij.injOn hK1 hK1' h)
  have hcomm := (CFSG.LocalCores.distinct_components_commute hc₁ hc₂).resolve_left hne''
  have hkF : k ∈ F := hKF hk
  have hk'F : k' ∈ F := hK'F hk'
  have h1 : π ⟨k, hkF⟩ ∈ (K.subgroupOf F).map π :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hk)
  have h2 : π ⟨k', hk'F⟩ ∈ (K'.subgroupOf F).map π :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hk')
  have h3 : ⁅π ⟨k, hkF⟩, π ⟨k', hk'F⟩⁆ ∈ ⁅(K.subgroupOf F).map π, (K'.subgroupOf F).map π⁆ :=
    Subgroup.commutator_mem_commutator h1 h2
  rw [hcomm, Subgroup.mem_bot, commutatorElement_def] at h3
  have h4 : (⟨k, hkF⟩ * ⟨k', hk'F⟩ * ⟨k, hkF⟩⁻¹ * ⟨k', hk'F⟩⁻¹ : F) ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    change π (⟨k, hkF⟩ * ⟨k', hk'F⟩ * ⟨k, hkF⟩⁻¹ * ⟨k', hk'F⟩⁻¹ : F) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact h3
  exact ⟨_, h4, rfl⟩

theorem isQuasisimple_of_perfect_of_simple {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) : CFSG.IsQuasisimple Q := by
  refine ⟨hperf, hs, ?_⟩
  by_contra hno
  push Not at hno
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [commutatorElement_def, ← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm]
    exact hno _ _
  rw [hperf.commutator_eq_top, top_le_iff] at hle
  have := hs
  obtain ⟨y, hy⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective y
  apply hy
  rw [QuotientGroup.eq_one_iff, hle]
  exact Subgroup.mem_top y0

theorem isQuasisimple_of_evenLie {K : Subgroup G} (hperf : Group.IsPerfect K)
    (hE : CFSG.Blueprint.EvenLieType (↥K ⧸ Subgroup.center ↥K)) : CFSG.IsQuasisimple ↥K := by
  obtain ⟨t, n, f, -, hL⟩ := hE
  exact isQuasisimple_of_perfect_of_simple hperf (CFSG.Timmesfeld.isSimpleGroup_of_lieModel hL)

theorem mem_center_of_commutators_mem_center {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {v : Q} (hv : ∀ k : Q, v * k * v⁻¹ * k⁻¹ ∈ Subgroup.center Q) : v ∈ Subgroup.center Q := by
  set Z := Subgroup.center Q with hZ
  obtain ⟨hperf, hsimple, a, b, hab⟩ := hQ
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Q ⧸ Z)) with h | h
  · have hmem : (QuotientGroup.mk v : Q ⧸ Z) ∈ Subgroup.center (Q ⧸ Z) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
      have h1 : ((v * k * v⁻¹ * k⁻¹ : Q) : Q ⧸ Z) = 1 := (QuotientGroup.eq_one_iff _).mpr (hv k)
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
      rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    rw [h, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff v).mp hmem
  · exfalso
    have ha : a ∈ Subgroup.center (Q ⧸ Z) := by
      rw [h]
      exact Subgroup.mem_top _
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem eq_one_of_mem_center_of_pow {p : ℕ} (hp : p.Prime) {Q : Type*} [Group Q] [Finite Q]
    (hZ : ¬ p ∣ Nat.card (Subgroup.center Q)) {v : Q} (hv : v ∈ Subgroup.center Q)
    (hvp : v ^ p = 1) : v = 1 := by
  have h1 : orderOf (⟨v, hv⟩ : Subgroup.center Q) ∣ Nat.card (Subgroup.center Q) :=
    orderOf_dvd_natCard _
  have h2 : orderOf (⟨v, hv⟩ : Subgroup.center Q) ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext hvp
  rcases (Nat.dvd_prime hp).mp h2 with h3 | h3
  · have := orderOf_eq_one_iff.mp h3
    exact congrArg Subtype.val this
  · rw [h3] at h1
    exact absurd h1 hZ

end S11d

end CFSG.RankThree.PartOne
