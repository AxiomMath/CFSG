module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Simple

import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartOne.Q1327T

section CoverCentralizer

variable {M Q : Type} [Group M] [Group Q]

theorem centralizer_map_eq [Finite M] {p : ℕ} (hp : p.Prime) (π : M →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center M) (hpk : ¬ p ∣ Nat.card π.ker)
    {ct : M} (hc : ct ^ p = 1) :
    Subgroup.centralizer ({π ct} : Set Q) = (Subgroup.centralizer ({ct} : Set M)).map π := by
  ext y
  constructor
  · intro hy
    obtain ⟨g, rfl⟩ := hπ y
    refine ⟨g, ?_, rfl⟩
    have hy' : π g * π ct = π ct * π g := Subgroup.mem_centralizer_singleton_iff.1 hy
    set z : M := g * ct * g⁻¹ * ct⁻¹ with hz
    have hzk : z ∈ π.ker := by
      rw [MonoidHom.mem_ker, hz]
      simp only [map_mul, map_inv]
      rw [hy']
      group
    have hzc : z ∈ Subgroup.center M := hker hzk
    have hzct : g * ct * g⁻¹ = z * ct := by rw [hz]; group
    have hzp : z ^ p = 1 := by
      have h1 : (g * ct * g⁻¹) ^ p = 1 := by
        rw [conj_pow, hc]
        group
      have h2 : (z * ct) ^ p = z ^ p * ct ^ p :=
        (Commute.mul_pow (Subgroup.mem_center_iff.1 hzc ct).symm p)
      rw [hzct, h2, hc, mul_one] at h1
      exact h1
    have hz1 : z = 1 := by
      have hord : orderOf (⟨z, hzk⟩ : π.ker) ∣ p := by
        apply orderOf_dvd_of_pow_eq_one
        exact Subtype.ext (by simpa using hzp)
      have hord2 : orderOf (⟨z, hzk⟩ : π.ker) ∣ Nat.card π.ker := orderOf_dvd_natCard _
      have hcop : Nat.Coprime p (Nat.card π.ker) := (Nat.Prime.coprime_iff_not_dvd hp).2 hpk
      have h0 : orderOf (⟨z, hzk⟩ : π.ker) ∣ Nat.gcd p (Nat.card π.ker) := Nat.dvd_gcd hord hord2
      rw [hcop.gcd_eq_one] at h0
      have := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h0)
      exact congrArg Subtype.val this
    rw [hz1] at hzct
    show g ∈ Subgroup.centralizer ({ct} : Set M)
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [one_mul] at hzct
    exact mul_inv_eq_iff_eq_mul.1 hzct
  · rintro ⟨g, hg, rfl⟩
    have hg' : g ∈ Subgroup.centralizer ({ct} : Set M) := hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg' ⊢
    rw [← map_mul, ← map_mul, hg']

theorem false_of_commutative_centralizer [Finite M] {p : ℕ} (hp : p.Prime) (π : M →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center M) (hpk : ¬ p ∣ Nat.card π.ker)
    {ct : M} (hc : ct ^ p = 1) {Kb : Subgroup Q}
    (hKbc : Kb ≤ Subgroup.centralizer ({π ct} : Set Q)) (hKbp : ⁅Kb, Kb⁆ = Kb) (hKb1 : Kb ≠ ⊥)
    (hcomm : ∀ a ∈ Subgroup.centralizer ({ct} : Set M), ∀ b ∈ Subgroup.centralizer ({ct} : Set M),
      a * b = b * a) : False := by
  have hmap := centralizer_map_eq hp π hπ hker hpk hc
  apply hKb1
  rw [← hKbp, eq_bot_iff]
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  have ha' := hKbc ha
  have hb' := hKbc hb
  rw [hmap] at ha' hb'
  obtain ⟨a', ha'C, rfl⟩ := ha'
  obtain ⟨b', hb'C, rfl⟩ := hb'
  rw [Subgroup.mem_bot, commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
    ← map_mul]
  have := hcomm a' ha'C b' hb'C
  have h1 : a' * b' * a'⁻¹ * b'⁻¹ = 1 := by
    rw [this]
    group
  rw [h1, map_one]

theorem card_eq_of_component [Finite M] {p : ℕ} (hp : p.Prime) (π : M →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center M) (hpk : ¬ p ∣ Nat.card π.ker)
    {ct : M} (hc : ct ^ p = 1) {C : Subgroup M} (hC : C = Subgroup.centralizer ({ct} : Set M))
    {CQ : Subgroup Q} (hCQ : CQ = Subgroup.centralizer ({π ct} : Set Q)) {Kb : Subgroup Q}
    (hKbc : Kb ≤ CQ) (hKbN : (Kb.subgroupOf CQ).Normal) (hKbp : ⁅Kb, Kb⁆ = Kb) (hKb1 : Kb ≠ ⊥)
    (L : Subgroup M) (hLC : L ≤ C) (hLs : IsSimpleGroup L) (hLinj : ∀ g ∈ L, π g = 1 → g = 1)
    {A : Type} [CommGroup A] (χ : C →* A) (hχ : ∀ g : C, χ g = 1 → (g : M) ∈ L) :
    Nat.card Kb = Nat.card L := by
  classical
  have hmap : CQ = C.map π := by
    rw [hC, hCQ]
    exact centralizer_map_eq hp π hπ hker hpk hc
  let θ : C →* CQ := (π.comp C.subtype).codRestrict CQ fun g => by
    rw [hmap]
    exact ⟨g, g.2, rfl⟩
  have hθ : Function.Surjective θ := by
    intro y
    have hy : (y : Q) ∈ C.map π := by
      rw [← hmap]
      exact y.2
    obtain ⟨g, hg, hgy⟩ := hy
    exact ⟨⟨g, hg⟩, Subtype.ext hgy⟩
  set Kb' : Subgroup CQ := Kb.subgroupOf CQ with hKb'
  have hKb'N : Kb'.Normal := hKbN
  set Kt : Subgroup C := Kb'.comap θ with hKt
  have hKtN : Kt.Normal := hKb'N.comap θ
  set Km : Subgroup C := ⁅Kt, Kt⁆ with hKm
  have hKmN : Km.Normal := Subgroup.commutator_normal Kt Kt
  have hθKt : Kt.map θ = Kb' := Subgroup.map_comap_eq_self_of_surjective hθ Kb'
  have hKb'p : ⁅Kb', Kb'⁆ = Kb' := by
    apply Subgroup.map_injective (f := CQ.subtype) CQ.subtype_injective
    rw [Subgroup.map_commutator, hKb', Subgroup.map_subgroupOf_eq_of_le hKbc, hKbp]
  have hθKm : Km.map θ = Kb' := by
    rw [hKm, Subgroup.map_commutator, hθKt, hKb'p]
  have hKmχ : Km ≤ χ.ker := by
    rw [hKm]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)
  let KmM : Subgroup M := Km.map C.subtype
  have hKmML : KmM ≤ L := by
    rintro _ ⟨g, hg, rfl⟩
    exact hχ g (MonoidHom.mem_ker.1 (hKmχ hg))
  have hKmMN : (KmM.subgroupOf L).Normal := by
    refine ⟨fun n hn l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk, hkn⟩ := hn
    have hl : ((l : L) : M) ∈ C := hLC l.2
    refine ⟨⟨(l : M), hl⟩ * k * ⟨(l : M), hl⟩⁻¹, hKmN.conj_mem k hk _, ?_⟩
    have hkn' : (k : M) = (n : M) := hkn
    simp [Subgroup.coe_mul, hkn']
  have hπKm : KmM.map π = Kb := by
    have h1 : KmM.map π = (Km.map θ).map CQ.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h1, hθKm, hKb', Subgroup.map_subgroupOf_eq_of_le hKbc]
  have := hKmMN
  rcases hLs.eq_bot_or_eq_top_of_normal (KmM.subgroupOf L) with hbot | htop
  · exfalso
    apply hKb1
    rw [← hπKm]
    have : KmM = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxL : x ∈ L := hKmML hx
      have : (⟨x, hxL⟩ : L) ∈ KmM.subgroupOf L := hx
      rw [hbot, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    rw [this, Subgroup.map_bot]
  · have hLK : L ≤ KmM := by
      intro l hl
      have : (⟨l, hl⟩ : L) ∈ KmM.subgroupOf L := by rw [htop]; trivial
      exact this
    have hKmM_eq : KmM = L := le_antisymm hKmML hLK
    rw [← hπKm, hKmM_eq]
    have hinj : Function.Injective (π.comp L.subtype) := by
      rw [injective_iff_map_eq_one]
      intro l hl
      exact Subtype.ext (hLinj l l.2 hl)
    have hrange : (π.comp L.subtype).range = L.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end CoverCentralizer

end CFSG.RankThree.PartOne.Q1327T
