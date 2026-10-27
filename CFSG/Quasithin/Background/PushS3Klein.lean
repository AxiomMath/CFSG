module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathPlaneSL
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin.F6.PushS3

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Wreath
open scoped commutatorElement

section Klein

variable {G : Type*} [Group G]

noncomputable def actOn (U P : Subgroup G) (hPU : P ≤ Subgroup.normalizer (U : Set G)) :
    ↥P →* MulAut ↥U :=
  (U.normalizerMonoidHom).comp (Subgroup.inclusion hPU)

theorem actOn_apply_coe {U P : Subgroup G} (hPU : P ≤ Subgroup.normalizer (U : Set G)) (p : ↥P)
    (u : ↥U) : ((actOn U P hPU p u : ↥U) : G) = (p : G) * (u : G) * (p : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe U (Subgroup.inclusion hPU p) u

theorem actOn_eq_one_iff {U P : Subgroup G} (hPU : P ≤ Subgroup.normalizer (U : Set G)) (p : ↥P) :
    actOn U P hPU p = 1 ↔ ∀ u : ↥U, (p : G) * u = u * p := by
  constructor
  · intro h u
    have h2 := congrArg (fun a : MulAut ↥U => ((a u : ↥U) : G)) h
    simp only [actOn_apply_coe, MulAut.one_apply] at h2
    calc (p : G) * u = ((p : G) * u * (p : G)⁻¹) * p := by group
      _ = u * p := by rw [h2]
  · intro hp
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [actOn_apply_coe]
    show (p : G) * u * (p : G)⁻¹ = u
    calc (p : G) * u * (p : G)⁻¹ = (u * p) * (p : G)⁻¹ := by rw [hp u]
      _ = u := by group

theorem exists_induce_of_orders {U P : Subgroup G} [IsKleinFour ↥U]
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) {p₁ p₂ : ↥P}
    (h3 : actOn U P hPU p₁ ^ 3 = 1) (h31 : actOn U P hPU p₁ ≠ 1) {k : ℕ}
    (h2 : actOn U P hPU p₂ ^ 2 ^ k = 1) (h21 : actOn U P hPU p₂ ≠ 1) :
    ∀ σ : MulAut ↥U, ∃ p : ↥P, ∀ u : ↥U, ((σ u : ↥U) : G) = (p : G) * (u : G) * (p : G)⁻¹ := by
  classical
  set act := actOn U P hPU with hact
  have ho3 : orderOf (act p₁) = 3 := orderOf_eq_prime h3 h31
  have ho2 : 2 ∣ orderOf (act p₂) := by
    have hd : orderOf (act p₂) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
    obtain ⟨j, hj, hj2⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    rw [hj2]
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hj2
      exact h21 (orderOf_eq_one_iff.1 hj2)
    · exact dvd_pow_self 2 h0.ne'
  have hR3 : 3 ∣ Nat.card act.range := by
    have : orderOf (⟨act p₁, (MonoidHom.mem_range.2 ⟨p₁, rfl⟩)⟩ : act.range) = 3 := by
      rw [Subgroup.orderOf_mk, ho3]
    rw [← this]
    exact orderOf_dvd_natCard _
  have hR2 : 2 ∣ Nat.card act.range := by
    have e : orderOf (⟨act p₂, (MonoidHom.mem_range.2 ⟨p₂, rfl⟩)⟩ : act.range) =
        orderOf (act p₂) := Subgroup.orderOf_mk _ _
    exact (ho2.trans (dvd_of_eq e.symm)).trans (orderOf_dvd_natCard _)
  have hdvd : Nat.card act.range ∣ 6 := by
    have := Subgroup.card_subgroup_dvd_card act.range
    rwa [card_mulAut] at this
  have h6 : Nat.card act.range = 6 := by
    have : 2 * 3 ∣ Nat.card act.range :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hR2 hR3
    exact Nat.dvd_antisymm hdvd this
  have htop : act.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [h6, card_mulAut]
  intro σ
  have hσ : σ ∈ act.range := by rw [htop]; exact Subgroup.mem_top σ
  obtain ⟨p, rfl⟩ := hσ
  exact ⟨p, fun u => actOn_apply_coe hPU p u⟩

theorem isTwoReduced_of_induce {U P : Subgroup G} [IsKleinFour ↥U] (hUP : U ≤ P)
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) (helem : IsElemAbelian 2 U)
    (hind : ∀ σ : MulAut ↥U, ∃ p : ↥P,
      ∀ u : ↥U, ((σ u : ↥U) : G) = (p : G) * (u : G) * (p : G)⁻¹) :
    IsTwoReducedIn P U := by
  refine ⟨hUP, hPU, helem, ?_⟩
  intro D hDP hDn hDpow
  set act := actOn U P hPU with hact
  have hsurj : Function.Surjective act := by
    intro σ
    obtain ⟨p, hp⟩ := hind σ
    refine ⟨p, MulEquiv.ext fun u => Subtype.ext ?_⟩
    rw [hact, actOn_apply_coe, hp u]
  have hDnorm : (D.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDP).mpr hDn
  have hDb : ((D.subgroupOf P).map act).Normal := hDnorm.map act hsurj
  have hp : IsPGroup 2 ↥((D.subgroupOf P).map act) := by
    rintro ⟨g, q, hq, rfl⟩
    obtain ⟨k, hk⟩ := hDpow (q : G) hq
    refine ⟨k, Subtype.ext ?_⟩
    show act q ^ 2 ^ k = 1
    rw [← map_pow]
    refine (actOn_eq_one_iff hPU _).mpr fun u => ?_
    have := Subgroup.mem_centralizer_iff.mp hk (u : G) u.2
    exact this.symm
  have hbot := eq_bot_of_normal_isPGroup _ hp
  intro d hd
  have h1 : act ⟨d, hDP hd⟩ = 1 := by
    have : act ⟨d, hDP hd⟩ ∈ (D.subgroupOf P).map act := ⟨⟨d, hDP hd⟩, hd, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact ((actOn_eq_one_iff hPU _).mp h1 ⟨u, hu⟩).symm

end Klein

end CFSG.Quasithin.F6.PushS3
