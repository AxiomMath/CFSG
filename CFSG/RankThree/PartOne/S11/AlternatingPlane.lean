module

public import CFSG.RankThree.PartOne.S11.CatalogLeaves
public import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingDegreeThirteen
public import CFSG.RankThree.GroupTheory.SteinbergCESmallAlternatingFiveActor
public import CFSG.RankThree.GroupTheory.SteinbergBMMovingPlaneTwoSubgroupObstruction
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.ComponentClassification CFSG.RankThree.GroupTheory

theorem mem_inner_of_pow_prime_eq_one {T : Type*} [Group T] [Finite T]
    (hout : Nat.card (OuterAutomorphisms.Outer T) ≤ 4) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {α : MulAut T} (hα : α ^ p = 1) : α ∈ OuterAutomorphisms.inner T := by
  set q := QuotientGroup.mk' (OuterAutomorphisms.inner T) α
  have hqp : orderOf q ∣ p := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hα, map_one])
  have hqle : orderOf q ≤ 4 :=
    (Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard q)).trans hout
  have hq1 : orderOf q = 1 := by
    rcases (Nat.dvd_prime hp).mp hqp with h | h
    · exact h
    · omega
  exact (QuotientGroup.eq_one_iff α).mp (orderOf_eq_one_iff.mp hq1)

theorem actualCoverAlternatingPlaneCentralization : ActualCoverAlternatingPlaneCentralization := by
  classical
  intro H _ _ he X n hn5 ⟨e⟩ p E U hpl
  have hp : p.Prime := hpl.prime
  have hp3 : 3 < p := hpl.three_lt
  have := hpl.elementary
  have hp5' : 5 ≤ p := by
    by_contra h
    have h4 : p = 4 := by omega
    rw [h4] at hp
    norm_num at hp
  set T := X ⧸ Subgroup.center X with hT
  have hn12 : n ≤ 12 := by
    let π : X →* alternatingGroup (Fin n) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
    have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker ≤ Subgroup.center X := by
      intro x hx
      have h1 : e (x : T) = 1 := hx
      have h2 : (x : T) = 1 := e.injective (h1.trans (map_one e).symm)
      exact (QuotientGroup.eq_one_iff x).mp h2
    exact (alternating_central_covers_degree_thirteen_force_two_local_three_rank_four π hπ
      hker).2.2.1 he
  have hout : Nat.card (OuterAutomorphisms.Outer T) ≤ 4 := by
    by_cases h6 : n = 6
    · subst h6
      exact CatalogueSchreierAlternating.DegreeSix.outer_card_le_four_of_equiv e
    · exact (Nat.le_of_dvd (by norm_num)
        (CatalogueSchreierAlternating.outer_card_dvd_two_of_equiv_outside_six (by omega) e)).trans
        (by norm_num)
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
  have hEinner : E ≤ OuterAutomorphisms.inner T := fun α hα =>
    mem_inner_of_pow_prime_eq_one hout hp hp5' (elemPow_eq_one_of_isElementaryAbelian α hα)
  have hdvd : p ^ 2 ∣ Nat.card T := by
    have h1 := Subgroup.card_dvd_of_le hEinner
    rw [hpl.card] at h1
    have h2 : Nat.card (OuterAutomorphisms.inner T) = Nat.card T :=
      Nat.card_congr (MonoidHom.ofInjective hconj_inj).symm.toEquiv
    rwa [h2] at h1
  have hp5 : p = 5 := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have h2 : 2 * Nat.card T = n.factorial := by
      rw [Nat.card_congr e.toEquiv, two_mul_nat_card_alternatingGroup, Nat.card_perm,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    have h3 : p ^ 2 ∣ (12).factorial := by
      refine (hdvd.trans ?_).trans (Nat.factorial_dvd_factorial hn12)
      rw [← h2]
      exact Dvd.intro_left 2 rfl
    have hp12 : p ≤ 12 :=
      (Nat.Prime.dvd_factorial hp).mp ((Dvd.intro_left p (sq p).symm).trans h3)
    interval_cases p
    all_goals first
      | rfl
      | (exfalso; norm_num at hp; done)
      | (exfalso; norm_num [Nat.factorial] at h3)
  subst hp5
  by_contra hnc
  have hmove : ∃ α ∈ E, ∃ u ∈ U, α u ≠ u := by
    by_contra h
    push Not at h
    exact hnc fun α hα u hu => h α hα u hu
  obtain ⟨α₀, hα₀, u₀, hu₀, hne⟩ := hmove
  have hinv : CFSG.IsInvariant E T U :=
    ⟨fun a g => ⟨fun hg => hpl.normalized a a.2 g hg, fun hg => by
      have h1 := hpl.normalized (a⁻¹ : E) (a⁻¹).2 ((a : MulAut T) g) hg
      have h2 : ((a⁻¹ : E) : MulAut T) ((a : MulAut T) g) = g := by
        change ((a : MulAut T)⁻¹ * (a : MulAut T)) g = g
        rw [inv_mul_cancel]
        rfl
      rwa [h2] at h1⟩⟩
  have hcomm : commutatorAction ↥E ↥U ≠ ⊥ := by
    intro h0
    have hmem : (⟨u₀, hu₀⟩ : U)⁻¹ * ((⟨α₀, hα₀⟩ : E) • (⟨u₀, hu₀⟩ : U)) ∈
        commutatorAction ↥E ↥U :=
      Subgroup.subset_closure ⟨⟨α₀, hα₀⟩, ⟨u₀, hu₀⟩, Subgroup.mem_top _, rfl⟩
    rw [h0, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hne (congrArg Subtype.val hmem.symm)
  obtain ⟨R, hR, D, hDcard, -, -, -, -, -, -, -, -, -, -, hβfix, hγmove⟩ :=
    SteinbergBM.moving_large_prime_plane_two_subgroup_fixed_line_and_small_order_obstruction hp
      (by norm_num) hpl.card hpl.two_group hcomm
  have hord5 : ∀ α : E, α ≠ 1 → orderOf (α : MulAut T) = 5 := by
    intro α hα1
    have hα5 : (α : MulAut T) ^ 5 = 1 := elemPow_eq_one_of_isElementaryAbelian _ α.2
    have hdvd5 : orderOf (α : MulAut T) ∣ 5 := orderOf_dvd_of_pow_eq_one hα5
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd5 with h | h
    · exact absurd (Subtype.ext (orderOf_eq_one_iff.mp h)) hα1
    · exact h
  obtain ⟨β, hβD, hβ1⟩ : ∃ b ∈ D, b ≠ 1 := by
    by_contra h
    push Not at h
    have hD : D = ⊥ := (Subgroup.eq_bot_iff_forall D).mpr h
    rw [hD, Subgroup.card_bot] at hDcard
    omega
  obtain ⟨γ, hγD⟩ : ∃ g : E, g ∉ D := by
    by_contra h
    push Not at h
    have hD : D = ⊤ := (Subgroup.eq_top_iff' D).mpr h
    rw [hD, Subgroup.card_top, hpl.card] at hDcard
    omega
  have hγ1 : γ ≠ 1 := fun h => hγD (h ▸ D.one_mem)
  set R' : Subgroup T := R.map U.subtype with hR'
  have hR'2 : IsPGroup 2 R' := hpl.two_group.to_le (Subgroup.map_subtype_le R)
  have hβR : ∀ u ∈ R', (β : MulAut T) u = u := by
    rintro _ ⟨r, hr, rfl⟩
    exact congrArg Subtype.val (hβfix β hβD hβ1 r hr)
  have hγR : R'.map (γ : MulAut T).toMonoidHom = R' := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨γ • r, hR γ r hr, rfl⟩
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := hx
      exact ⟨_, ⟨γ⁻¹ • r, hR γ⁻¹ r hr, rfl⟩, congrArg Subtype.val (smul_inv_smul γ r)⟩
  have hfix := small_alternating_five_fixed_two_subgroups_have_no_moving_five_actor (by omega)
    hn12 e (hord5 β hβ1) (hord5 γ hγ1) hR'2 hβR hγR
  obtain ⟨r, hr, hrne⟩ := hγmove γ hγD
  exact hrne (Subtype.ext (hfix r (Subgroup.mem_map_of_mem _ hr)))

end CFSG.RankThree.PartOne
