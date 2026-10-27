module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.RankThree.PerfectCover

open Subgroup
open scoped Pointwise

variable {R T : Type*} [Group R] [Group T]

theorem surjective_comp_subtype_of_map_eq_top (ρ : R →* T) {Y : Subgroup R}
    (hY : Y.map ρ = ⊤) : Function.Surjective (ρ.comp Y.subtype) := by
  rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype, hY]

theorem card_eq_card_mul_card_ker_of_map_eq_top (ρ : R →* T) {Y : Subgroup R}
    (hY : Y.map ρ = ⊤) : Nat.card Y = Nat.card T * Nat.card (ρ.comp Y.subtype).ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (ρ.comp Y.subtype).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (surjective_comp_subtype_of_map_eq_top ρ hY)).toEquiv]

theorem card_ker_comp_subtype_dvd (ρ : R →* T) (Y : Subgroup R) :
    Nat.card (ρ.comp Y.subtype).ker ∣ Nat.card ρ.ker := by
  let f : (ρ.comp Y.subtype).ker →* ρ.ker :=
    { toFun := fun y => ⟨((y : Y) : R), y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Subgroup.card_dvd_of_injective f fun x y hxy => ?_
  have h : ((x : Y) : R) = ((y : Y) : R) := congrArg (fun z : ρ.ker => (z : R)) hxy
  exact Subtype.ext (Subtype.ext h)

theorem factorization_card_of_map_eq_top [Finite R] (ρ : R →* T) (hρ : Function.Surjective ρ)
    {p : ℕ} (hker : ¬ p ∣ Nat.card ρ.ker) {Y : Subgroup R} (hY : Y.map ρ = ⊤) :
    (Nat.card Y).factorization p = (Nat.card R).factorization p := by
  have : Finite T := Finite.of_surjective ρ hρ
  have hY' := card_eq_card_mul_card_ker_of_map_eq_top ρ hY
  have hR' := card_eq_card_mul_card_ker_of_map_eq_top ρ (Y := ⊤)
    (by rw [map_top_of_surjective ρ hρ])
  rw [Subgroup.card_top] at hR'
  have hdY : ¬ p ∣ Nat.card (ρ.comp Y.subtype).ker := fun h =>
    hker (h.trans (card_ker_comp_subtype_dvd ρ Y))
  have hdR : ¬ p ∣ Nat.card (ρ.comp (⊤ : Subgroup R).subtype).ker := fun h =>
    hker (h.trans (card_ker_comp_subtype_dvd ρ ⊤))
  rw [hY', hR', Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hdY,
    Nat.factorization_eq_zero_of_not_dvd hdR]

theorem eq_one_of_mem_of_isPGroup_of_not_dvd [Finite R] {p : ℕ} [Fact p.Prime]
    {U K : Subgroup R} (hU : IsPGroup p U) (hK : ¬ p ∣ Nat.card K) {u : R} (hu : u ∈ U)
    (huK : u ∈ K) : u = 1 := by
  obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
  have h1 : orderOf u ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf u ∣ Nat.card K := by
    rw [← Subgroup.orderOf_mk u huK]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ k) (Nat.card K) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hK)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem prime_complement_minimal_cover_preserving_prime_subgroup [Finite R] [Finite T] {p : ℕ}
    (hp : p.Prime) (ρ : R →* T) (hρ : Function.Surjective ρ) (hker : ¬ p ∣ Nat.card ρ.ker)
    (U : Subgroup R) (hU : IsPGroup p U) :
    ∃ Γ : Subgroup R, U ≤ Γ ∧ Γ.map ρ = ⊤ ∧ (∀ Y : Subgroup R, Y < Γ → Y.map ρ ≠ ⊤) ∧
      Function.Surjective (ρ.comp Γ.subtype) ∧
      (ρ.comp Γ.subtype).ker.map Γ.subtype = Γ ⊓ ρ.ker ∧
      Group.IsNilpotent (ρ.comp Γ.subtype).ker ∧ ¬ p ∣ Nat.card (ρ.comp Γ.subtype).ker ∧
      (∀ (q : ℕ) [Fact q.Prime] (Q : Sylow q (ρ.comp Γ.subtype).ker),
        ((Q : Subgroup (ρ.comp Γ.subtype).ker).map (ρ.comp Γ.subtype).ker.subtype).Normal) ∧
      (∃ e : Γ ⧸ (ρ.comp Γ.subtype).ker ≃* T, ∀ γ : Γ, e (QuotientGroup.mk γ) = ρ γ) ∧
      Function.Injective (ρ.comp U.subtype) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hex : ∃ n, ∃ Y : Subgroup R, Y.map ρ = ⊤ ∧ Nat.card Y = n :=
    ⟨_, ⊤, map_top_of_surjective ρ hρ, rfl⟩
  obtain ⟨Γ₀, hΓ₀, hΓ₀card⟩ := Nat.find_spec hex
  have hmin : ∀ Y : Subgroup R, Y.map ρ = ⊤ → Nat.find hex ≤ Nat.card Y :=
    fun Y hY => Nat.find_min' hex ⟨Y, hY, rfl⟩
  obtain P₀ : Sylow p Γ₀ := default
  have hP₀card : Nat.card ((P₀ : Subgroup Γ₀).map Γ₀.subtype) =
      p ^ (Nat.card R).factorization p := by
    rw [Subgroup.card_map_of_injective Γ₀.subtype_injective, Sylow.card_eq_multiplicity,
      factorization_card_of_map_eq_top ρ hρ hker hΓ₀]
  let P₁ : Sylow p R := Sylow.ofCard _ hP₀card
  obtain ⟨P, hUP⟩ := hU.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R P₁ P
  set Γ : Subgroup R := MulAut.conj g • Γ₀ with hΓdef
  have hconj_mem : ∀ x ∈ Γ₀, g * x * g⁻¹ ∈ Γ := fun x hx => by
    have := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) Γ₀ hx
    rwa [MulAut.smul_def, MulAut.conj_apply] at this
  have hUΓ : U ≤ Γ := by
    refine hUP.trans ?_
    rw [← hg, Sylow.coe_subgroup_smul]
    exact (Subgroup.pointwise_smul_le_pointwise_smul_iff).mpr (Subgroup.map_subtype_le _)
  have hΓmap : Γ.map ρ = ⊤ := by
    rw [eq_top_iff]
    intro t _
    have ht : ρ g⁻¹ * t * ρ g ∈ Γ₀.map ρ := by
      rw [hΓ₀]
      exact mem_top _
    obtain ⟨x, hx, hxt⟩ := Subgroup.mem_map.mp ht
    refine Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hconj_mem x hx, ?_⟩
    rw [map_mul, map_mul, hxt, map_inv]
    group
  have hΓcard : Nat.card Γ = Nat.find hex := by
    rw [← hΓ₀card]
    exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) Γ₀).toEquiv).symm
  have hΓmin : ∀ Y : Subgroup R, Y < Γ → Y.map ρ ≠ ⊤ := by
    intro Y hY hYmap
    have h1 := hmin Y hYmap
    have h2 := Subgroup.card_lt_of_lt hY
    omega
  set σ : Γ →* T := ρ.comp Γ.subtype with hσ
  have hσs : Function.Surjective σ := surjective_comp_subtype_of_map_eq_top ρ hΓmap
  have hCmap : σ.ker.map Γ.subtype = Γ ⊓ ρ.ker := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hxΓ, hxk⟩
      exact ⟨⟨x, hxΓ⟩, hxk, rfl⟩
  have hCp : ¬ p ∣ Nat.card σ.ker := fun h => hker (h.trans (card_ker_comp_subtype_dvd ρ Γ))
  have hsyl : ∀ (q : ℕ) [Fact q.Prime] (Q : Sylow q σ.ker),
      ((Q : Subgroup σ.ker).map σ.ker.subtype).Normal := by
    intro q _ Q
    set Nq := normalizer (((Q : Subgroup σ.ker).map σ.ker.subtype : Subgroup Γ) : Set Γ)
    have hF := congrArg (map σ) (Sylow.normalizer_sup_eq_top Q)
    rw [Subgroup.map_sup, map_top_of_surjective σ hσs] at hF
    have hker' : σ.ker.map σ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨y, hy, rfl⟩
      exact hy
    rw [hker', sup_bot_eq] at hF
    have hNmap : (Nq.map Γ.subtype).map ρ = ⊤ := by
      rw [Subgroup.map_map]
      exact hF
    have hNle : Nq.map Γ.subtype ≤ Γ := Subgroup.map_subtype_le _
    have hNeq : Nq.map Γ.subtype = Γ := by
      by_contra hne
      exact hΓmin _ (lt_of_le_of_ne hNle hne) hNmap
    have hNtop : Nq = ⊤ := by
      apply Subgroup.map_injective Γ.subtype_injective
      rw [hNeq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact normalizer_eq_top_iff.mp hNtop
  have hnil : Group.IsNilpotent σ.ker := by
    refine ((Group.isNilpotent_of_finite_tfae (G := σ.ker)).out 4 1).mp ?_
    intro q _ Q
    have hQ := (hsyl q Q).subgroupOf σ.ker
    rwa [subgroupOf, comap_map_eq_self_of_injective (subtype_injective _)] at hQ
  have hinj : Function.Injective (ρ.comp U.subtype) := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hu1 : (u : R) = 1 :=
      eq_one_of_mem_of_isPGroup_of_not_dvd hU hker u.2 (MonoidHom.mem_ker.mpr hu)
    exact Subtype.ext hu1
  exact ⟨Γ, hUΓ, hΓmap, hΓmin, hσs, hCmap, hnil, hCp, hsyl,
    ⟨QuotientGroup.quotientKerEquivOfSurjective σ hσs, fun _ => rfl⟩, hinj⟩

end CFSG.RankThree.PerfectCover
