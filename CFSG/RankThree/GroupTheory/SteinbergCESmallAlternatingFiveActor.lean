module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingPlaneCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix

public section

namespace CFSG.RankThree.GroupTheory

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms

theorem card_le_eight_of_commute_orderOf_five {n : ℕ} (hn : n ≤ 12) {σ : Perm (Fin n)}
    (hσ : orderOf σ = 5) {U : Subgroup (Perm (Fin n))} (hU2 : IsPGroup 2 U)
    (hUA : U ≤ alternatingGroup (Fin n)) (hUσ : ∀ u ∈ U, Commute u σ) : Nat.card U ≤ 8 := by
  have h5 : Nat.Prime 5 := by norm_num
  have hcop : ∀ u ∈ U, ¬ 5 ∣ orderOf u := fun u hu h => by
    have h1 := hU2.orderOf_coprime (n := 5) (by norm_num) ⟨u, hu⟩
    rw [Subgroup.orderOf_mk] at h1
    have h2 := Nat.dvd_gcd h (dvd_refl 5)
    rw [h1] at h2
    omega
  have hcf : ∀ c ∈ σ.cycleFactorsFinset, orderOf c = 5 := fun c hc =>
    orderOf_eq_of_mem_cycleFactorsFinset h5 hσ hc
  have hfixsupp : ∀ u ∈ U, (∀ c ∈ σ.cycleFactorsFinset, Commute u c) →
      ∀ x, σ x ≠ x → u x = x := by
    intro u hu hc x hx
    have hxs : x ∈ σ.support := mem_support.mpr hx
    have hcx : σ.cycleOf x ∈ σ.cycleFactorsFinset := cycleOf_mem_cycleFactorsFinset_iff.mpr hxs
    exact apply_eq_self_of_commute_isCycle h5 (mem_cycleFactorsFinset_iff.mp hcx).1 (hcf _ hcx)
      (hc _ hcx) (hcop u hu) (mem_support_cycleOf_iff.mpr ⟨SameCycle.refl _ _, hxs⟩)
  have hct : ∀ m ∈ σ.cycleType, m = 5 := fun m hm => by
    have h1 := dvd_of_mem_cycleType hm
    rw [hσ] at h1
    have h2 := two_le_of_mem_cycleType hm
    rcases (Nat.dvd_prime h5).mp h1 with h | h <;> omega
  have hrep : σ.cycleType = Multiset.replicate σ.cycleType.card 5 :=
    Multiset.eq_replicate_card.mpr hct
  have hsupp : σ.support.card = 5 * σ.cycleType.card := by
    rw [← sum_cycleType, hrep, Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate,
      mul_comm]
  have hsuppn : σ.support.card ≤ n := by
    have := σ.support.card_le_univ
    rwa [Fintype.card_fin] at this
  have hk0 : σ.cycleType.card ≠ 0 := by
    intro h
    rw [Multiset.card_eq_zero, cycleType_eq_zero] at h
    rw [h, orderOf_one] at hσ
    omega
  have hkcf : σ.cycleFactorsFinset.card = σ.cycleType.card := by
    rw [cycleType_def, Multiset.card_map]
    rfl
  set F := Finset.univ.filter fun x => σ x = x
  have hFcard : F.card = n - σ.support.card := by
    have h : F.card + (Finset.univ.filter fun x : Fin n => ¬ σ x = x).card =
        Finset.univ.card := Finset.card_filter_add_card_filter_not _
    have hs : (Finset.univ.filter fun x : Fin n => ¬ σ x = x) = σ.support := by
      ext x
      simp [mem_support]
    rw [hs, Finset.card_univ, Fintype.card_fin] at h
    omega
  have hmemF : ∀ x, x ∈ F ↔ σ x = x := fun x => by simp [F]
  have hUF : ∀ u ∈ U, (∀ c ∈ σ.cycleFactorsFinset, Commute u c) → u ∈ alternatingOn F := by
    intro u hu hc
    refine mem_alternatingOn_iff.mpr ⟨hUA hu, fun x hx => hfixsupp u hu hc x ?_⟩
    rwa [hmemF] at hx
  have hk : σ.cycleType.card = 1 ∨ σ.cycleType.card = 2 := by omega
  rcases hk with hk | hk
  ·
    have hcyc : σ.IsCycle := card_cycleType_eq_one.mp hk
    have hle : U ≤ alternatingOn F := fun u hu => hUF u hu fun c hc => by
      rw [hcyc.cycleFactorsFinset_eq_singleton, Finset.mem_singleton] at hc
      rw [hc]
      exact hUσ u hu
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [← Nat.card_congr (alternatingOnEquiv F).toEquiv] at hdvd
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hU2
    rw [ha] at hdvd ⊢
    by_cases hF2 : 2 ≤ F.card
    · have : Nontrivial {x // x ∈ F} := by
        rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe]
        omega
      have h2 := two_mul_nat_card_alternatingGroup (α := {x // x ∈ F})
      rw [Nat.card_perm, Nat.card_eq_finsetCard] at h2
      have h3 : 2 ^ (a + 1) ∣ 5040 := by
        have h4 : 2 ^ (a + 1) ∣ F.card.factorial := by
          rw [← h2, pow_succ, mul_comm]
          exact Nat.mul_dvd_mul_left 2 hdvd
        exact h4.trans ((Nat.factorial_dvd_factorial (by omega : F.card ≤ 7)).trans
          (by decide))
      by_contra hlt
      have ha4 : 4 ≤ a := by
        by_contra h
        have : 2 ^ a ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have h5' : 2 ^ 5 ∣ 2 ^ (a + 1) := Nat.pow_dvd_pow 2 (by omega)
      exact absurd (h5'.trans h3) (by decide)
    · have : Subsingleton {x // x ∈ F} := by
        rw [← Finset.card_le_one_iff_subsingleton_coe]
        omega
      have h1 : Nat.card (alternatingGroup {x // x ∈ F}) = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨inferInstance, inferInstance⟩
      rw [h1] at hdvd
      exact (Nat.le_of_dvd one_pos hdvd).trans (by norm_num)
  ·
    obtain ⟨c₁, c₂, hne, hcf2⟩ := Finset.card_eq_two.mp (hkcf.trans hk)
    have hc₁ : c₁ ∈ σ.cycleFactorsFinset := by rw [hcf2]; simp
    have hFle : F.card ≤ 2 := by omega
    have hconj : ∀ u ∈ U, ∀ c ∈ σ.cycleFactorsFinset, u * c * u⁻¹ ∈ σ.cycleFactorsFinset := by
      intro u hu c hc
      have h := (mem_cycleFactorsFinset_conj σ u c).mpr hc
      rwa [(hUσ u hu).eq, mul_inv_cancel_right] at h
    have htriv : ∀ u ∈ U, u * c₁ * u⁻¹ = c₁ → u = 1 := by
      intro u hu h1
      have hall : ∀ c ∈ σ.cycleFactorsFinset, Commute u c := by
        intro c hc
        have hc' : c = c₁ ∨ c = c₂ := by rw [hcf2] at hc; simpa using hc
        have hcomm : ∀ d, u * d * u⁻¹ = d → Commute u d := fun d h => by
          rw [Commute, SemiconjBy]
          calc u * d = u * d * u⁻¹ * u := by group
            _ = d * u := by rw [h]
        rcases hc' with hc' | hc'
        · rw [hc']
          exact hcomm _ h1
        · rw [hc']
          apply hcomm
          have h2 := hconj u hu c₂ (by rw [hcf2]; simp)
          rw [hcf2, Finset.mem_insert, Finset.mem_singleton] at h2
          rcases h2 with h2 | h2
          · exfalso
            apply hne
            have h3 : u * c₁ * u⁻¹ = u * c₂ * u⁻¹ := h1.trans h2.symm
            simpa using h3
          · exact h2
      have hfix : ∀ x, x ∉ F → u x = x := fun x hx =>
        hfixsupp u hu hall x (by rwa [hmemF] at hx)
      have hsupp : u.support ⊆ F := fun x hx => by
        by_contra h
        exact (mem_support.mp hx) (hfix x h)
      have hcard : u.support.card ≤ 2 := (Finset.card_le_card hsupp).trans hFle
      rcases Nat.lt_or_eq_of_le hcard with h | h
      · exact card_support_le_one.mp (by omega)
      · exfalso
        have hsign := (card_support_eq_two.mp h).sign_eq
        rw [mem_alternatingGroup.mp (hUA hu)] at hsign
        exact absurd hsign (by decide)
    by_cases hU : U = ⊥
    · rw [hU, Subgroup.card_bot]
      norm_num
    obtain ⟨⟨u₀, hu₀⟩, hu₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
    have hu₀1 : u₀ ≠ 1 := fun h => hu₀1' (Subtype.ext h)
    have hswap : ∀ u ∈ U, u ≠ 1 → u * c₁ * u⁻¹ = c₂ := by
      intro u hu hu1
      have h2 := hconj u hu c₁ hc₁
      rw [hcf2, Finset.mem_insert, Finset.mem_singleton] at h2
      exact h2.resolve_left fun h => hu1 (htriv u hu h)
    have hsub : (U : Set (Perm (Fin n))) ⊆ {1, u₀} := by
      intro u hu
      by_cases hu1 : u = 1
      · exact Or.inl hu1
      · right
        have hw := htriv (u₀⁻¹ * u) (U.mul_mem (U.inv_mem hu₀) hu) (by
          rw [show u₀⁻¹ * u * c₁ * (u₀⁻¹ * u)⁻¹ = u₀⁻¹ * (u * c₁ * u⁻¹) * u₀ by group,
            hswap u hu hu1, ← hswap u₀ hu₀ hu₀1]
          group)
        rw [mul_eq_one_iff_eq_inv] at hw
        exact (inv_injective hw).symm
    have h := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq] at h
    exact h.trans ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]; norm_num))

theorem mem_inner_of_pow_five_eq_one {T : Type*} [Group T] [Finite T]
    (hout : Nat.card (Outer T) ≤ 4) {α : MulAut T} (hα : α ^ 5 = 1) : α ∈ inner T := by
  set q := QuotientGroup.mk' (inner T) α
  have hq5 : orderOf q ∣ 5 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hα, map_one])
  have hqle : orderOf q ≤ 4 :=
    (Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard q)).trans hout
  have hq1 : orderOf q = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hq5 with h | h
    · exact h
    · omega
  exact (QuotientGroup.eq_one_iff α).mp (orderOf_eq_one_iff.mp hq1)

theorem small_alternating_five_fixed_two_subgroups_have_no_moving_five_actor {T : Type*}
    [Group T] [Finite T] {n : ℕ} (hn5 : 5 ≤ n) (hn12 : n ≤ 12)
    (e : T ≃* alternatingGroup (Fin n)) {β γ : MulAut T} (hβ : orderOf β = 5)
    (hγ : orderOf γ = 5) {U : Subgroup T} (hU : IsPGroup 2 U) (hβU : ∀ u ∈ U, β u = u)
    (hγU : U.map γ.toMonoidHom = U) : ∀ u ∈ U, γ u = u := by
  have hout : Nat.card (Outer T) ≤ 4 := by
    by_cases h6 : n = 6
    · subst h6
      exact CatalogueSchreierAlternating.DegreeSix.outer_card_le_four_of_equiv e
    · exact (Nat.le_of_dvd (by norm_num)
        (CatalogueSchreierAlternating.outer_card_dvd_two_of_equiv_outside_six (by omega) e)).trans
        (by norm_num)
  obtain ⟨b, hb⟩ := mem_inner_of_pow_five_eq_one hout (by rw [← hβ, pow_orderOf_eq_one])
  have hcenter : Subgroup.center T = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hcen : e z ∈ Subgroup.center (alternatingGroup (Fin n)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    have h4 : 4 ≤ Nat.card (Fin n) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    rw [alternatingGroup.center_eq_bot h4] at hcen
    rw [Subgroup.mem_bot] at hcen ⊢
    exact e.injective (hcen.trans (map_one e).symm)
  have hconj_inj : Function.Injective (MulAut.conj : T →* MulAut T) := by
    intro a c hac
    have hz : c⁻¹ * a ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h : a * x * a⁻¹ = c * x * c⁻¹ := by
        simpa only [MulAut.conj_apply] using congrArg (fun φ : MulAut T => φ x) hac
      calc x * (c⁻¹ * a) = c⁻¹ * (c * x * c⁻¹) * a := by group
        _ = c⁻¹ * (a * x * a⁻¹) * a := by rw [h]
        _ = c⁻¹ * a * x := by group
    rw [hcenter, Subgroup.mem_bot, inv_mul_eq_one] at hz
    exact hz.symm
  have hb5 : orderOf b = 5 := by
    rw [← orderOf_injective _ hconj_inj b, hb, hβ]
  have hUb : ∀ u ∈ U, b * u = u * b := by
    intro u hu
    have h := hβU u hu
    rw [← hb, MulAut.conj_apply] at h
    calc b * u = b * u * b⁻¹ * b := by group
      _ = u * b := by rw [h]
  have hU8 : Nat.card U ≤ 8 := by
    set ι : T →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
    have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
    have hσ : orderOf (ι b) = 5 := by rw [orderOf_injective ι hι b, hb5]
    have h := card_le_eight_of_commute_orderOf_five hn12 hσ (hU.map ι)
      (by rintro _ ⟨u, -, rfl⟩; exact (e u).2)
      (by
        rintro _ ⟨u, hu, rfl⟩
        rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hUb u hu])
    rwa [Subgroup.card_map_of_injective hι] at h
  set φ : MulAut U := (γ.subgroupMap U).trans (MulEquiv.subgroupCongr hγU)
  have hφ : ∀ u : U, ((φ u : U) : T) = γ u := fun _ => rfl
  have hφpow : ∀ k : ℕ, ∀ u : U, (((φ ^ k) u : U) : T) = (γ ^ k) u := by
    intro k
    induction k with
    | zero => intro u; rfl
    | succ k ih =>
      intro u
      rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
  have hφ5 : φ ^ 5 = 1 := by
    ext u
    rw [hφpow, ← hγ, pow_orderOf_eq_one]
    rfl
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set P := Subgroup.zpowers φ
  have hP : IsPGroup 5 P := by
    have hdvd : orderOf φ ∣ 5 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one hφ5
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (show Nat.Prime 5 by norm_num)).mp hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hmod := hP.card_modEq_card_fixedPoints U
  set C : Subgroup U := (φ.toMonoidHom).eqLocus (MonoidHom.id U)
  have hfixC : MulAction.fixedPoints P U = (C : Set U) := by
    ext u
    rw [MulAction.mem_fixedPoints]
    change (∀ g : P, g • u = u) ↔ φ u = u
    constructor
    · intro h
      exact h ⟨φ, Subgroup.mem_zpowers φ⟩
    · intro h g
      obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr g.2)
      have hku : ∀ k : ℕ, (φ ^ k) u = u := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => rw [pow_succ', MulAut.mul_apply, ih]; exact h
      change (g : MulAut U) u = u
      rw [← hk]
      exact hku k
  have hCcard : Nat.card (MulAction.fixedPoints P U) = Nat.card C := by
    rw [hfixC]
    rfl
  rw [hCcard] at hmod
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hU
  obtain ⟨c, hc, hc'⟩ := (Nat.dvd_prime_pow (show Nat.Prime 2 by norm_num)).mp
    (ha ▸ Subgroup.card_subgroup_dvd_card C)
  have ha3 : a ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [ha, hc'] at hmod
  have hca : c = a := by
    interval_cases a <;> interval_cases c <;> simp_all [Nat.ModEq]
  have htop : C = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, hc', hca, ha]
  intro u hu
  have h : (⟨u, hu⟩ : U) ∈ C := by
    rw [htop]
    exact Subgroup.mem_top _
  change φ ⟨u, hu⟩ = ⟨u, hu⟩ at h
  exact (hφ ⟨u, hu⟩).symm.trans (congrArg Subtype.val h)

end CFSG.RankThree.GroupTheory
