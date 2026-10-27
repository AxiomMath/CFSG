module

public import CFSG.RankThree.PartOne.S11d.BenderLemma
public import CFSG.RankThree.PartOne.S11d.Facts
public import CFSG.RankThree.PartOne.S11d.InnerBasic

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace S11d

section Lift

variable {C : Type*} [Group C] [Finite C] {p : ℕ} [Fact p.Prime]

theorem exists_pSubgroup_lift (N : Subgroup C) [N.Normal] {A₀ : Subgroup C} (hA₀ : IsPGroup p A₀)
    {E : Subgroup (C ⧸ N)} (hE : IsPGroup p E) (hAE : A₀.map (QuotientGroup.mk' N) ≤ E) :
    ∃ P : Subgroup C, IsPGroup p P ∧ A₀ ≤ P ∧ P.map (QuotientGroup.mk' N) = E := by
  classical
  set π := QuotientGroup.mk' N with hπ
  set M : Subgroup C := E.comap π with hM
  have hA₀M : A₀ ≤ M := fun a ha => hAE ⟨a, ha, rfl⟩
  let f : ↥M →* C ⧸ N := π.comp M.subtype
  have hfrange : f.range = E := by
    ext e
    constructor
    · rintro ⟨m, rfl⟩
      exact m.2
    · intro he
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective e
      exact ⟨⟨c, he⟩, rfl⟩
  have hA₀' : IsPGroup p (A₀.subgroupOf M) := hA₀.comap_subtype
  obtain ⟨P₀, hP₀⟩ := hA₀'.exists_le_sylow
  set Q₀ : Subgroup ↥M := (P₀ : Subgroup ↥M) with hQ₀
  refine ⟨Q₀.map M.subtype, P₀.2.map _, ?_, ?_⟩
  · intro a ha
    exact ⟨⟨a, hA₀M ha⟩, hP₀ (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  · have hpf : IsPGroup p f.range := by
      intro x
      obtain ⟨k, hk⟩ := hE ⟨x.1, by rw [← hfrange]; exact x.2⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have hf' : Function.Surjective f.rangeRestrict := MonoidHom.rangeRestrict_surjective f
    have hT := (P₀.mapSurjective hf').is_maximal' (Q := ⊤) (hpf.to_subgroup ⊤) le_top
    have hmap : Q₀.map f.rangeRestrict = ⊤ := hT.symm
    have hf'' : f = f.range.subtype.comp f.rangeRestrict := by ext; rfl
    have key : Q₀.map f = f.range := by
      calc Q₀.map f = (Q₀.map f.rangeRestrict).map f.range.subtype := by
            rw [Subgroup.map_map, ← hf'']
        _ = (⊤ : Subgroup f.range).map f.range.subtype := by rw [hmap]
        _ = f.range := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc (Q₀.map M.subtype).map π = Q₀.map f := by rw [Subgroup.map_map]
      _ = f.range := key
      _ = E := hfrange

end Lift

section F3

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem mem_image_of_centralizes {C : Subgroup G} (N : Subgroup ↥C) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {A : Subgroup G} (hAC : A ≤ C) [hA : IsElementaryAbelian p A]
    (hF3 : ∀ u : G, u ∈ centralizer (A : Set G) → u ^ p = 1 → u ∈ A) {d : ↥C ⧸ N}
    (hd : d ^ p = 1)
    (hcomm : ∀ a ∈ (A.subgroupOf C).map (QuotientGroup.mk' N), a * d = d * a) :
    d ∈ (A.subgroupOf C).map (QuotientGroup.mk' N) := by
  classical
  set π := QuotientGroup.mk' N with hπ
  set AC : Subgroup ↥C := A.subgroupOf C with hAC'
  set AX : Subgroup (↥C ⧸ N) := AC.map π with hAX
  have hACcomm : ∀ x ∈ AC, ∀ y ∈ AC, x * y = y * x := by
    intro x hx y hy
    have h := congrArg Subtype.val (hA.is_comm.comm
      (⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩ : A) ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩)
    exact Subtype.ext h
  have hApow : ∀ x ∈ AC, x ^ p = 1 := by
    intro x hx
    have h := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) (x : G)
      (Subgroup.mem_subgroupOf.mp hx)
    exact Subtype.ext (by simpa using h)
  have hAXcomm : ∀ β ∈ AX, ∀ β' ∈ AX, β * β' = β' * β := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hACcomm x hx y hy]
  have hAXpow : ∀ β ∈ AX, β ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hApow x hx, map_one]
  have hAXd : ∀ β ∈ AX, Commute β d := fun β hβ => hcomm β hβ
  set E : Subgroup (↥C ⧸ N) := AX ⊔ Subgroup.zpowers d with hE
  have hEel : ∀ e ∈ E, ∃ β ∈ AX, ∃ j : ℤ, e = β * d ^ j := fun e he =>
    (mem_sup_zpowers_iff hAXd).mp he
  have hEcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := by
    intro e he e' he'
    obtain ⟨β, hβ, j, rfl⟩ := hEel e he
    obtain ⟨β', hβ', j', rfl⟩ := hEel e' he'
    have h1 : Commute β β' := hAXcomm β hβ β' hβ'
    have h2 : Commute β (d ^ j') := (hAXd β hβ).zpow_right j'
    have h3 : Commute (d ^ j) β' := ((hAXd β' hβ').symm).zpow_left j
    have h4 : Commute (d ^ j) (d ^ j') := Commute.zpow_zpow_self d j j'
    exact ((h1.mul_left h3).mul_right (h2.mul_left h4)).eq
  have hEpow : ∀ e ∈ E, e ^ p = 1 := by
    intro e he
    obtain ⟨β, hβ, j, rfl⟩ := hEel e he
    have hc : Commute β (d ^ j) := (hAXd β hβ).zpow_right j
    have hdj : (d ^ j) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd, one_zpow]
    rw [hc.mul_pow, hAXpow β hβ, hdj, one_mul]
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hEpow x x.2)⟩
  have hACp : IsPGroup p AC := (IsElementaryAbelian.isPGroup p A).comap_subtype
  obtain ⟨P, hPp, hAP, hPE⟩ := exists_pSubgroup_lift N hACp hEp (le_sup_left : AX ≤ E)
  have hinj : ∀ x ∈ P, π x = 1 → x = 1 := by
    intro x hx h1
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).mp h1
    obtain ⟨k, hk⟩ := hPp ⟨x, hx⟩
    have h2 : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h3 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one h2
    have h4 : orderOf x ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (p ^ k) (Nat.card N) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN)
    have h5 : orderOf x ∣ Nat.gcd (p ^ k) (Nat.card N) := Nat.dvd_gcd h3 h4
    rw [hcop.gcd_eq_one] at h5
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)
  have hπP : ∀ x ∈ P, π x ∈ E := fun x hx => hPE ▸ Subgroup.mem_map_of_mem π hx
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have hz : x * y * (y * x)⁻¹ ∈ P := P.mul_mem (P.mul_mem hx hy) (P.inv_mem (P.mul_mem hy hx))
    have h1 : π (x * y * (y * x)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul, hEcomm _ (hπP x hx) _ (hπP y hy), mul_inv_cancel]
    have := hinj _ hz h1
    exact mul_inv_eq_one.mp this
  have hPpow : ∀ x ∈ P, x ^ p = 1 := by
    intro x hx
    apply hinj _ (P.pow_mem hx p)
    rw [map_pow, hEpow _ (hπP x hx)]
  have hPA : P ≤ AC := by
    intro x hx
    rw [hAC', Subgroup.mem_subgroupOf]
    apply hF3
    · rw [mem_centralizer_iff]
      intro a ha
      have hmem : (⟨a, hAC ha⟩ : ↥C) ∈ P := hAP (Subgroup.mem_subgroupOf.mpr ha)
      exact congrArg Subtype.val (hPcomm _ hmem x hx)
    · simpa using congrArg Subtype.val (hPpow x hx)
  have hEA : E ≤ AX := by
    rw [← hPE]
    exact Subgroup.map_mono hPA
  exact hEA (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))

end F3

end S11d

theorem benderPCore : BenderPCore := by
  intro G _ _ p A c L B n h b S hW
  have hp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := sectionTenSetup_three_lt h.setup
  have : IsElementaryAbelian p A := h.A_elem
  set C := centralizer ({b} : Set G) with hC
  set N := aschbacherSolvableCore p ↥C with hN
  have hpN : ¬ p ∣ Nat.card N :=
    (solvable_prime_complement_core_characterization (H := ↥C) hp).2.2.1
  have hbA : b ∈ A := h.B_le_A hW.b_mem
  have hAC : A ≤ C := fun x hx => mem_centralizer_singleton_iff.mpr (h.A_comm x hx b hbA)
  have hAS' : A.subgroupOf C ≤ normalizer ((S.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hW.S_norm (Subgroup.mem_subgroupOf.mp hx)) (g : G)
  refine S11d.bender_abstract (X := ↥C ⧸ N) hp (by omega)
    (A := (A.subgroupOf C).map (QuotientGroup.mk' N))
    (S := (S.subgroupOf C).map (QuotientGroup.mk' N)) ?_ ?_ ?_ ?_
  · exact ((IsElementaryAbelian.isPGroup p A).comap_subtype).map _
  · exact (hW.S_two.comap_subtype).map _
  · exact (Subgroup.map_mono hAS').trans (Subgroup.le_normalizer_map _)
  · intro d hd hcomm
    exact S11d.mem_image_of_centralizes N hpN hAC
      (fun u hu hup => h.mem_of_mem_centralizer hu hup) hd hcomm

end CFSG.RankThree.PartOne
