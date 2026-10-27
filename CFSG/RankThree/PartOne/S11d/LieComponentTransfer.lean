module

public import CFSG.RankThree.PartOne.S11d.Facts5
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_centralizer_of_map_mem_centralizer {J : Subgroup G} {T : Type*} [Group T]
    (π : ↥J →* T) (hker : π.ker ≤ Subgroup.center ↥J) {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥J)) {dJ : ↥J} (hdp : dJ ^ p = 1) {g : ↥J}
    (hg : π g ∈ Subgroup.centralizer ({π dJ} : Set T)) :
    g ∈ Subgroup.centralizer ({dJ} : Set ↥J) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
  set z : ↥J := g * dJ * g⁻¹ * dJ⁻¹ with hz
  have hzk : z ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    have : π z = ⁅π g, π dJ⁆ := by
      rw [hz, ← commutatorElement_def, map_commutatorElement]
    rw [this, commutatorElement_eq_one_iff_mul_comm]
    exact hg
  have hzc : z ∈ Subgroup.center ↥J := hker hzk
  have hzd : g * dJ * g⁻¹ = z * dJ := by rw [hz]; group
  have h1 : (g * dJ * g⁻¹) ^ p = 1 := by rw [conj_pow, hdp]; simp
  have hcomm : Commute z dJ := (Subgroup.mem_center_iff.mp hzc dJ).symm
  have h2 : z ^ p = 1 := by
    rw [hzd, hcomm.mul_pow, hdp, mul_one] at h1
    exact h1
  have h3 : orderOf (⟨z, hzc⟩ : Subgroup.center ↥J) ∣ p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_dvd_of_pow_eq_one h2
  have h4 : orderOf (⟨z, hzc⟩ : Subgroup.center ↥J) ∣ Nat.card (Subgroup.center ↥J) :=
    _root_.orderOf_dvd_natCard _
  have hz1 : z = 1 := by
    rcases (Nat.dvd_prime hp).mp h3 with h | h
    · rw [Subgroup.orderOf_mk] at h
      exact orderOf_eq_one_iff.mp h
    · rw [h] at h4
      exact absurd h4 hZ
  rw [hz1] at hzd
  calc g * dJ = (g * dJ * g⁻¹) * g := by group
    _ = dJ * g := by rw [hzd, one_mul]

theorem exists_isComponentOf_of_quotient {J : Subgroup G} {T : Type*} [Group T] (π : ↥J →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥J) {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥J)) {d : G} (hdJ : d ∈ J) (hdp : d ^ p = 1)
    {D₀ : Subgroup T} (hq : CFSG.IsQuasisimple ↥D₀)
    (hcent : D₀ ≤ Subgroup.centralizer ({π ⟨d, hdJ⟩} : Set T))
    (hsub : (D₀.subgroupOf (Subgroup.centralizer ({π ⟨d, hdJ⟩} : Set T))).IsSubnormal) :
    ∃ D : Subgroup G, IsComponentOf (J ⊓ Subgroup.centralizer ({d} : Set G)) D := by
  set dJ : ↥J := ⟨d, hdJ⟩ with hdJdef
  have hdJp : dJ ^ p = 1 := Subtype.ext hdp
  set Cj : Subgroup ↥J := Subgroup.centralizer ({dJ} : Set ↥J) with hCj
  set Ct : Subgroup T := Subgroup.centralizer ({π dJ} : Set T) with hCt
  set Pj : Subgroup ↥J := D₀.comap π with hPj
  have key : ∀ g : ↥J, π g ∈ Ct → g ∈ Cj := fun g hg =>
    mem_centralizer_of_map_mem_centralizer π hker hp hZ hdJp hg
  have hPC : Pj ≤ Cj := fun g hg => key g (hcent hg)
  let f : ↥Pj →* ↥D₀ := (π.comp Pj.subtype).codRestrict D₀ fun g => g.2
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, hg⟩ := hπ (x : T)
    refine ⟨⟨g, by rw [hPj, Subgroup.mem_comap, hg]; exact x.2⟩, Subtype.ext hg⟩
  have hfker : f.ker ≤ Subgroup.center ↥Pj := by
    intro g hg
    have hg1 : π (g : ↥J) = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
      exact h
    have hgc : (g : ↥J) ∈ Subgroup.center ↥J := hker (MonoidHom.mem_ker.mpr hg1)
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (Subgroup.mem_center_iff.mp hgc (h : ↥J))
  have hquasi : CFSG.IsQuasisimple ↥(commutator ↥Pj) :=
    CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective f hf hfker hq
  set D' : Subgroup ↥J := (commutator ↥Pj).map Pj.subtype with hD'
  set ρ : ↥Pj →* G := J.subtype.comp Pj.subtype with hρ
  have hρinj : Function.Injective ρ := J.subtype_injective.comp Pj.subtype_injective
  set D : Subgroup G := (commutator ↥Pj).map ρ with hD
  have hDeq : D = D'.map J.subtype := by
    rw [hD, hD', Subgroup.map_map]
  have hD'Pj : D' ≤ Pj := Subgroup.map_subtype_le _
  refine ⟨D, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(y : ↥J).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hyC : (y : ↥J) ∈ Cj := hPC y.2
    rw [hCj, Subgroup.mem_centralizer_singleton_iff] at hyC
    exact congrArg Subtype.val hyC
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.equivMapOfInjective _ ρ hρinj) hquasi
  · set X : Subgroup G := J ⊓ Subgroup.centralizer ({d} : Set G) with hX
    have hXCj : ∀ x : ↥X, Subgroup.inclusion (inf_le_left : X ≤ J) x ∈ Cj := by
      intro x
      rw [hCj, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2.2)
    let jX : ↥X →* ↥Cj := (Subgroup.inclusion (inf_le_left : X ≤ J)).codRestrict Cj hXCj
    have hH : D.subgroupOf X = (D'.subgroupOf Cj).comap jX := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, hDeq, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = Subgroup.inclusion (inf_le_left : X ≤ J) x := Subtype.ext hyx
        change Subgroup.inclusion (inf_le_left : X ≤ J) x ∈ D'
        rw [← this]
        exact hy
      · intro hx
        exact ⟨Subgroup.inclusion (inf_le_left : X ≤ J) x, hx, rfl⟩
    rw [hH]
    refine Subgroup.IsSubnormal.comap jX ?_
    have hnorm : ∀ g ∈ Pj, ∀ y ∈ D', g * y * g⁻¹ ∈ D' := by
      rintro g hg _ ⟨y₀, hy₀, rfl⟩
      have hn : (commutator ↥Pj).Normal := inferInstance
      exact ⟨⟨g, hg⟩ * y₀ * ⟨g, hg⟩⁻¹, hn.conj_mem y₀ hy₀ ⟨g, hg⟩, rfl⟩
    let π' : ↥Cj →* ↥Ct := (π.comp Cj.subtype).codRestrict Ct fun g => by
      rw [hCt, Subgroup.mem_centralizer_singleton_iff]
      have hg : (g : ↥J) * dJ = dJ * (g : ↥J) := Subgroup.mem_centralizer_singleton_iff.mp g.2
      change π g * π dJ = π dJ * π g
      rw [← map_mul, ← map_mul]
      exact congrArg π hg
    have hP1 : Pj.subgroupOf Cj = (D₀.subgroupOf Ct).comap π' := by
      ext g
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, hPj, Subgroup.mem_comap]
      rfl
    have hP1sub : (Pj.subgroupOf Cj).IsSubnormal := by
      rw [hP1]
      exact hsub.comap π'
    have hD1P1 : D'.subgroupOf Cj ≤ Pj.subgroupOf Cj := fun g hg => hD'Pj hg
    have hnormal : ((D'.subgroupOf Cj).subgroupOf (Pj.subgroupOf Cj)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hD1P1]
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hgP : (g : ↥J) ∈ Pj := hg
      constructor
      · intro hh
        exact hnorm _ hgP _ hh
      · intro hh
        have := hnorm _ (Pj.inv_mem hgP) _ hh
        exact Subgroup.mem_subgroupOf.mpr (by simpa [mul_assoc] using this)
    exact Subgroup.IsSubnormal.trans hD1P1 hnormal.isSubnormal hP1sub

end CFSG.RankThree.PartOne
