module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section AltTwo

open Equiv Equiv.Perm

variable {V : Type} [DecidableEq V] [Fintype V]

@[expose] def GGAltCoreConclusionTwo (p : ℕ) (M : Subgroup (Perm V)) : Prop :=
  (p = 3 ∧ Fintype.card V = 6 ∧ ∀ C : Subgroup (Perm V), ¬ CFSG.Assembly.IsComponentOf C M) ∨
  (p = 5 ∧ ∃ C₁ C₂ : Subgroup (Perm V), C₁ ≠ C₂ ∧ CFSG.Assembly.IsComponentOf C₁ M ∧
      CFSG.Assembly.IsComponentOf C₂ M ∧ Nonempty (↥C₁ ≃* ↥(alternatingGroup (Fin 5))) ∧
      Nonempty (↥C₂ ≃* ↥(alternatingGroup (Fin 5)))) ∨
  (∃ C : Subgroup (Perm V), CFSG.Assembly.IsComponentOf C M ∧
    ∃ m : ℕ, 7 ≤ m ∧ m ≠ 8 ∧ Nonempty (↥C ≃* ↥(alternatingGroup (Fin m))))

private theorem ggAC2_of_absorbing {p : ℕ} {M : Subgroup (Perm V)} {X : Finset V}
    (hX : GGAbsorbing M X) (h7 : 7 ≤ X.card) (h8 : X.card ≠ 8) :
    GGAltCoreConclusionTwo p M :=
  Or.inr (Or.inr ⟨GGAltOn X, ggIsComponentOf_altOn hX (by omega), X.card, h7, h8,
    ⟨ggAltOnMulEquiv X⟩⟩)

theorem ggAltCoreTwo {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {M E : Subgroup (Perm V)}
    (hMtop : ¬ alternatingGroup V ≤ M) (hEM : E ≤ M)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hEcard : Nat.card E = p ^ 2)
    (hctl : ∀ g ∈ alternatingGroup V, ∀ x ∈ E, x ≠ 1 → g⁻¹ * x * g ∈ M → g ∈ M) :
    GGAltCoreConclusionTwo p M := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hC : ∀ x ∈ E, x ≠ 1 → ∀ k ∈ alternatingGroup V, k * x = x * k → k ∈ M := by
    intro x hx hx1 k hk hkx
    refine hctl k hk x hx hx1 ?_
    have : k⁻¹ * x * k = x := by
      rw [mul_assoc, ← hkx, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact hEM hx
  obtain ⟨x₀, hx₀, hx₀1⟩ : ∃ x ∈ E, x ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr h
    rw [hbot, Subgroup.card_bot] at hEcard
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  obtain ⟨ω₀, -⟩ : ∃ v, x₀ v ≠ v := by
    by_contra h
    push Not at h
    exact hx₀1 (Perm.ext h)
  by_cases hG : ∃ x ∈ E, x ≠ 1 ∧ ∃ β : ZMod p → V, (∀ i, x (β i) ≠ β i) ∧
      ∀ i i' (k : ℕ), (x ^ k) (β i) = β i' → i = i'
  · obtain ⟨x, hx, hx1, β, hβ, horb⟩ := hG
    obtain ⟨Y, hY, hYalt⟩ := ggAltIn_grid hp2 (hEp x hx) hβ horb (hC x hx hx1)
      (fun g hg hgm => hctl g hg x hx hx1 hgm)
    have h9 : 9 ≤ p ^ 2 := by nlinarith
    obtain ⟨X, hYX, hX⟩ := ggExists_absorbing (by omega) hYalt
    have hXc : p ^ 2 ≤ X.card := hY.trans (Finset.card_le_card hYX)
    exact ggAC2_of_absorbing hX (by omega) (by omega)
  have hfixset : ∀ ω, Nat.card (ggStab E ω) = p → ∃ x ∈ E, x ≠ 1 ∧ x ω = ω := by
    intro ω h
    by_contra hcon
    push Not at hcon
    have hbot : ggStab E ω = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun x hx => by
      by_contra hx1
      exact hcon x (ggMem_stab.mp hx).1 hx1 (ggMem_stab.mp hx).2
    rw [hbot, Subgroup.card_bot] at h
    exact hp.one_lt.ne h
  have hFalt : ∀ x ∈ E, x ≠ 1 → GGAltIn M (Finset.univ.filter fun v => x v = v) :=
    fun x hx hx1 => ggAltIn_of_commute (hC x hx hx1) (fun v hv => by simpa using hv)
  have hFcard : ∀ ω x, Nat.card (ggStab E ω) = p → x ∈ E → x ω = ω →
      p ≤ (Finset.univ.filter fun v => x v = v).card := by
    intro ω x h hx hxω
    rw [← ggCard_orb_of_stab hp hEcard h]
    refine Finset.card_le_card fun v hv => ?_
    simpa using ggFix_orb_of_mem_stab hEab (ggMem_stab.mpr ⟨hx, hxω⟩) hv
  have hnoreg : ∀ ω, Nat.card (ggStab E ω) ≠ 1 := fun ω h =>
    hG (ggExists_grid_of_regular hEab hEp hEcard h)
  have hnofix : ∀ ω, Nat.card (ggStab E ω) ≠ p ^ 2 := by
    intro ω₁ h₁
    have hfix₁ := ggFixed_of_card_stab hEcard h₁
    obtain ⟨ω₂, hω₂⟩ : ∃ ω₂, Nat.card (ggStab E ω₂) = p := by
      by_contra hcon
      push Not at hcon
      have hall : ∀ ω, ∀ x ∈ E, x ω = ω := fun ω => ggFixed_of_card_stab hEcard (by
        rcases ggCard_stab_cases hp hEcard ω with h | h | h
        · exact absurd h (hnoreg ω)
        · exact absurd h (hcon ω)
        · exact h)
      exact hx₀1 (Perm.ext fun ω => hall ω x₀ hx₀)
    obtain ⟨x₂, hx₂, hx₂1, hx₂ω⟩ := hfixset ω₂ hω₂
    obtain ⟨X, hFX, hX⟩ := ggExists_absorbing (hp3.trans (hFcard ω₂ x₂ hω₂ hx₂ hx₂ω))
      (hFalt x₂ hx₂ hx₂1)
    apply ggAbsorbing_ne_univ hMtop hX
    rw [Finset.eq_univ_iff_forall]
    intro ω
    rcases ggCard_stab_cases hp hEcard ω with h | h | h
    · exact absurd h (hnoreg ω)
    · obtain ⟨x, hx, hx1, hxω⟩ := hfixset ω h
      have hsub := hX.2.2 _ (hp3.trans (hFcard ω x h hx hxω)) (hFalt x hx hx1)
        ⟨ω₁, Finset.mem_inter.mpr ⟨hFX (by simpa using hfix₁ x₂ hx₂), by simpa using hfix₁ x hx⟩⟩
      exact hsub (by simpa using hxω)
    · exact hFX (by simpa using ggFixed_of_card_stab hEcard h x₂ hx₂)
  have hstab : ∀ ω, Nat.card (ggStab E ω) = p := fun ω => by
    rcases ggCard_stab_cases hp hEcard ω with h | h | h
    · exact absurd h (hnoreg ω)
    · exact h
    · exact absurd h (hnofix ω)
  have horbcard : ∀ ω, (ggOrb E ω).card = p := fun ω => ggCard_orb_of_stab hp hEcard (hstab ω)
  have horbalt : ∀ ω, GGAltIn M (ggOrb E ω) := by
    intro ω
    obtain ⟨x, hx, hx1, hxω⟩ := hfixset ω (hstab ω)
    exact ggAltIn_of_commute (hC x hx hx1)
      (fun v hv => ggFix_orb_of_mem_stab hEab (ggMem_stab.mpr ⟨hx, hxω⟩) hv)
  have hn : Fintype.card V < p ^ 2 := by
    by_contra hn
    push Not at hn
    obtain ⟨x, hx, hx1, hsupp⟩ := ggExists_large_support hp hEcard hstab hn
    have hSinv : ∀ ω ∈ Finset.univ.filter (fun v => x v ≠ v),
        ggOrb E ω ⊆ Finset.univ.filter (fun v => x v ≠ v) := by
      intro ω hω v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      intro hxv
      have hmem : x ∈ ggStab E v := ggMem_stab.mpr ⟨hx, hxv⟩
      rw [ggStab_eq_of_mem hEab hv] at hmem
      exact hω (ggMem_stab.mp hmem).2
    obtain ⟨β', hβ'S, hβ'⟩ := ggExists_distinct_orbits hp hEcard hstab (p - 1) _ hSinv hsupp
    have e : ZMod p ≃ Fin (p - 1 + 1) :=
      Fintype.equivFinOfCardEq (by rw [ZMod.card]; omega)
    apply hG
    refine ⟨x, hx, hx1, fun i => β' (e i), fun i => ?_, fun i i' k h => ?_⟩
    · have := hβ'S (e i)
      simpa using this
    · have hmem : β' (e i') ∈ ggOrb E (β' (e i)) :=
        ggMem_orb.mpr ⟨x ^ k, E.pow_mem hx k, h⟩
      exact e.injective (hβ' _ _ hmem)
  have habs_orb : ∀ X, GGAbsorbing M X → ∀ ω ∈ X, ggOrb E ω ⊆ X := fun X hX ω hω =>
    hX.2.2 _ (by rw [horbcard]; exact hp3) (horbalt ω)
      ⟨ω, Finset.mem_inter.mpr ⟨hω, ggMem_orb_self ω⟩⟩
  have hdvdX : ∀ X, GGAbsorbing M X → p ∣ X.card := fun X hX =>
    ggDvd_card_of_invariant hp hEcard hstab X (habs_orb X hX)
  have hdvdn : p ∣ Fintype.card V := by
    have := ggDvd_card_of_invariant hp hEcard hstab Finset.univ
      (fun _ _ => Finset.subset_univ _)
    rwa [Finset.card_univ] at this
  have hnp : Fintype.card V ≠ p := ggCard_ne_of_stab hp hEab hEcard hstab
  have hnpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨ω₀⟩
  obtain ⟨X₀, hOX₀, hX₀⟩ := ggExists_absorbing (by rw [horbcard]; exact hp3) (horbalt ω₀)
  have hX₀p : p ≤ X₀.card := (horbcard ω₀) ▸ Finset.card_le_card hOX₀
  have hsmall : ∀ X, GGAbsorbing M X → X.card < 2 * p → ∀ ω ∈ X, X = ggOrb E ω := by
    intro X hX hXc ω hω
    have hOX := habs_orb X hX ω hω
    have hge : p ≤ X.card := (horbcard ω) ▸ Finset.card_le_card hOX
    obtain ⟨t, ht⟩ := hdvdX X hX
    have hXp : X.card = p := by
      rcases t with _ | _ | t
      · omega
      · omega
      · have h2 : p * 2 ≤ p * (t + 1 + 1) := Nat.mul_le_mul_left p (by omega)
        omega
    exact (Finset.eq_of_subset_of_card_le hOX (by rw [hXp, horbcard])).symm
  rcases ggPrime_cases hp hp2 with rfl | rfl | hp7
  ·
    left
    have hn6 : Fintype.card V = 6 := by
      obtain ⟨t, ht⟩ := hdvdn
      have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
      rcases t with _ | _ | _ | t <;> omega
    have hOabs : ∀ ω, GGAbsorbing M (ggOrb E ω) := by
      intro ω
      obtain ⟨X, hOX, hX⟩ := ggExists_absorbing (by rw [horbcard]) (horbalt ω)
      have hXne := ggAbsorbing_ne_univ hMtop hX
      have hXc : X.card < 2 * 3 := by
        have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ X, hXne⟩)
        rw [Finset.card_univ, hn6] at this
        omega
      rw [← hsmall X hX hXc ω (hOX (ggMem_orb_self ω))]
      exact hX
    have himg : ∀ g ∈ M, ∀ u w, w ∈ ggOrb E u → g w ∈ ggOrb E (g u) := by
      intro g hg u w hw
      rcases GGAbsorbing.eq_or_disjoint ((hOabs u).image hg) (hOabs (g u)) with h | h
      · rw [← h]
        exact Finset.mem_image_of_mem g hw
      · exact absurd (ggMem_orb_self (g u))
          (Finset.disjoint_left.mp h (Finset.mem_image_of_mem g (ggMem_orb_self u)))
    have hsame : ∀ v w, (v ∈ ggOrb E ω₀ ↔ w ∈ ggOrb E ω₀) → w ∈ ggOrb E v := by
      intro v w hvw
      by_cases hv : v ∈ ggOrb E ω₀
      · rw [ggOrb_eq_of_mem hv]
        exact hvw.mp hv
      · have hw : w ∉ ggOrb E ω₀ := fun h => hv (hvw.mpr h)
        have hsub : ggOrb E v ⊆ Finset.univ \ ggOrb E ω₀ := by
          intro u hu
          rw [Finset.mem_sdiff]
          exact ⟨Finset.mem_univ u, fun hu' => hv (ggOrb_trans hu' (ggOrb_symm hu))⟩
        have heq : ggOrb E v = Finset.univ \ ggOrb E ω₀ :=
          Finset.eq_of_subset_of_card_le hsub (by
            rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hn6,
              horbcard, horbcard])
        rw [heq, Finset.mem_sdiff]
        exact ⟨Finset.mem_univ w, hw⟩
    refine ⟨rfl, hn6, ggNoComponent_of_blocks (O := ggOrb E ω₀) (horbcard ω₀) hn6 ?_⟩
    intro g hg v w hvw
    have h1 := himg g hg v w (hsame v w hvw)
    constructor
    · intro hgv
      rw [ggOrb_eq_of_mem hgv] at h1
      exact h1
    · intro hgw
      have h2 : g v ∈ ggOrb E (g w) := ggOrb_symm h1
      rw [ggOrb_eq_of_mem hgw] at h2
      exact h2
  ·
    by_cases hbig : ∃ X, GGAbsorbing M X ∧ 10 ≤ X.card
    · obtain ⟨X, hX, hX10⟩ := hbig
      refine ggAC2_of_absorbing hX (by omega) fun h8 => ?_
      have hd := hdvdX X hX
      rw [h8] at hd
      norm_num at hd
    · push Not at hbig
      right
      left
      have hOabs : ∀ ω, GGAbsorbing M (ggOrb E ω) := by
        intro ω
        obtain ⟨X, hOX, hX⟩ := ggExists_absorbing (by rw [horbcard]; norm_num) (horbalt ω)
        rw [← hsmall X hX (by have := hbig X hX; omega) ω (hOX (ggMem_orb_self ω))]
        exact hX
      obtain ⟨t, ht⟩ := hdvdn
      have ht2 : 2 ≤ t := by omega
      have hV10 : 10 ≤ Fintype.card V := by
        rw [ht]
        omega
      obtain ⟨v, -, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := ggOrb E ω₀) (t := Finset.univ)
        (by rw [Finset.card_univ, horbcard]; omega)
      refine ⟨rfl, ?_⟩
      refine ⟨GGAltOn (ggOrb E ω₀), GGAltOn (ggOrb E v), ?_, ?_, ?_, ?_, ?_⟩
      ·
        intro hEq
        have hfix : ∀ c ∈ GGAltOn (ggOrb E ω₀), c v = v := by
          intro c hc
          by_contra hcv
          exact hv ((ggMem_altOn_iff.mp hc).2 v hcv)
        obtain ⟨a, ha, hav, -⟩ := ggExists_mem_ne_ne (X := ggOrb E v)
          (by rw [horbcard]; norm_num) v v
        obtain ⟨b, hb, hbv, hba⟩ := ggExists_mem_ne_ne (X := ggOrb E v)
          (by rw [horbcard]; norm_num) v a
        have hc3 : swap v a * swap a b ∈ GGAltOn (ggOrb E v) :=
          ggSwap_mul_swap_mem_altOn (ggMem_orb_self v) ha hb (Ne.symm hav) (Ne.symm hba)
            (Ne.symm hbv)
        have hc3v : (swap v a * swap a b) v ≠ v := by
          rw [Perm.coe_mul, Function.comp_apply,
            swap_apply_of_ne_of_ne (Ne.symm hav) (Ne.symm hbv), swap_apply_left]
          exact hav
        exact hc3v (hfix _ (le_of_eq hEq.symm hc3))
      · exact ggIsComponentOf_altOn (hOabs ω₀) (horbcard ω₀).ge
      · exact ggIsComponentOf_altOn (hOabs v) (horbcard v).ge
      · exact ⟨(ggAltOnMulEquiv (ggOrb E ω₀)).trans
          (Equiv.altCongrHom (finCongr (horbcard ω₀)))⟩
      · exact ⟨(ggAltOnMulEquiv (ggOrb E v)).trans
          (Equiv.altCongrHom (finCongr (horbcard v)))⟩
  ·
    refine ggAC2_of_absorbing hX₀ (hp7.trans hX₀p) fun h8 => ?_
    have hd := hdvdX X₀ hX₀
    rw [h8] at hd
    have hd' : p ∣ 2 ^ 3 := by norm_num; exact hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd'))

end AltTwo

end CFSG.StandardType
