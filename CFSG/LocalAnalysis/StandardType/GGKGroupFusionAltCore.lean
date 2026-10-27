module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltComp
public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenFourteen

public section

namespace CFSG.StandardType

open Equiv Equiv.Perm

section Core

variable {V : Type} [DecidableEq V] [Fintype V]

@[expose] def GGAltCoreConclusion (p : ℕ) (M : Subgroup (Perm V)) : Prop :=
  (p = 3 ∧ Fintype.card V = 6 ∧ ∀ C : Subgroup (Perm V), ¬ CFSG.Assembly.IsComponentOf C M) ∨
  (p = 5 ∧ (∃ k : ℕ, 2 ≤ k ∧ k ≤ 4 ∧ Fintype.card V = 5 * k) ∧
    ∀ C : Subgroup (Perm V), CFSG.Assembly.IsComponentOf C M →
      Nonempty (↥C ≃* ↥(alternatingGroup (Fin 5)))) ∨
  (∃ C : Subgroup (Perm V), CFSG.Assembly.IsComponentOf C M ∧
    ∃ m : ℕ, 7 ≤ m ∧ m ≠ 8 ∧ Nonempty (↥C ≃* ↥(alternatingGroup (Fin m))))

theorem ggAltCore_of_absorbing {p : ℕ} {M : Subgroup (Perm V)} {X : Finset V}
    (hX : GGAbsorbing M X) (h7 : 7 ≤ X.card) (h8 : X.card ≠ 8) : GGAltCoreConclusion p M :=
  Or.inr (Or.inr ⟨GGAltOn X, ggIsComponentOf_altOn hX (by omega), X.card, h7, h8,
    ⟨ggAltOnMulEquiv X⟩⟩)

theorem ggAbsorbing_ne_univ {M : Subgroup (Perm V)} (hMtop : ¬ alternatingGroup V ≤ M)
    {X : Finset V} (hX : GGAbsorbing M X) : X ≠ Finset.univ := by
  rintro rfl
  exact hMtop (ggAlternatingGroup_le_of_altIn hX.2.1)

theorem ggComponent_eq_altOn_orb {M E : Subgroup (Perm V)}
    (hOabs : ∀ ω, GGAbsorbing M (ggOrb E ω)) (hO5 : ∀ ω, 5 ≤ (ggOrb E ω).card)
    {C : Subgroup (Perm V)} (hC : CFSG.Assembly.IsComponentOf C M) :
    ∃ ω, C = GGAltOn (ggOrb E ω) := by
  have hCne := ggComponent_ne_bot hC
  obtain ⟨ω, hω⟩ : ∃ ω, C ≤ GGAltOn (ggOrb E ω) := by
    by_contra hcon
    push Not at hcon
    apply hCne
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    ext v
    rw [Perm.one_apply]
    have hle : GGAltOn (ggOrb E v) ≤ M := ggAltOn_le_of_altIn (hOabs v).2.1
    have hsub : ((GGAltOn (ggOrb E v)).subgroupOf M).IsSubnormal :=
      (ggAssemblyIsSubnormal_iff hle).mp (ggIsSubnormal_altOn (hOabs v))
    have hcomm := (ggComponent_le_or_commute hC hsub).resolve_left (hcon v)
    exact ggFix_of_commute_altOn (hO5 v) (fun σ hσ => hcomm c hc σ ⟨hle hσ, hσ⟩) v
      (ggMem_orb_self v)
  refine ⟨ω, le_antisymm hω ?_⟩
  have hS := ggIsComponentOf_altOn (hOabs ω) (hO5 ω)
  have hCsub : (C.subgroupOf M).IsSubnormal := (ggAssemblyIsSubnormal_iff hC.1).mp hC.2.1
  rcases ggComponent_le_or_commute hS hCsub with h | hcomm
  · exact h
  · exfalso
    apply hCne
    have : IsSimpleGroup ↥(GGAltOn (ggOrb E ω)) := ggAltOn_isSimpleGroup (hO5 ω)
    have hZ := ggCenter_eq_bot_of_simple (ggAltOn_nonabelian (X := ggOrb E ω) (by
      have := hO5 ω
      omega))
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    have hcS := hω hc
    have hcZ : (⟨c, hcS⟩ : ↥(GGAltOn (ggOrb E ω))) ∈ Subgroup.center ↥(GGAltOn (ggOrb E ω)) := by
      rw [Subgroup.mem_center_iff]
      intro s
      exact Subtype.ext (hcomm s s.2 c ⟨hC.1 hc, hc⟩)
    rw [hZ, Subgroup.mem_bot] at hcZ
    exact congrArg Subtype.val hcZ

@[expose] def ggRestrictHom (C : Subgroup (Perm V)) (P : V → Prop) [DecidablePred P]
    (h : ∀ c ∈ C, ∀ x, P (c x) ↔ P x) : ↥C →* Perm {x // P x} where
  toFun c := (c : Perm V).subtypePerm (h c c.2)
  map_one' := rfl
  map_mul' _ _ := rfl

omit [DecidableEq V] in
theorem ggFix_of_perfect {C : Subgroup (Perm V)} (hperf : commutator ↥C = ⊤) (P : V → Prop)
    [DecidablePred P] (h : ∀ c ∈ C, ∀ x, P (c x) ↔ P x) (hP : Nat.card {x // P x} ≤ 4) :
    ∀ c ∈ C, ∀ x, P x → c x = x := by
  have : Group.IsSolvable (Perm {x // P x}) := Equiv.Perm.isSolvable hP
  have hker := CFSG.SeitzReduction.perfect_le_ker (ggRestrictHom C P h) (P := ⊤)
    (by rw [← commutator_def]; exact hperf)
  intro c hc x hx
  have h1 := hker (Subgroup.mem_top ⟨c, hc⟩)
  rw [MonoidHom.mem_ker] at h1
  have h2 : ((ggRestrictHom C P h ⟨c, hc⟩) ⟨x, hx⟩ : V) = x := by
    rw [h1]
    rfl
  exact h2

open scoped commutatorElement in
theorem ggNoComponent_of_blocks {M : Subgroup (Perm V)} {O : Finset V} (hO : O.card = 3)
    (hn : Fintype.card V = 6)
    (hblock : ∀ g ∈ M, ∀ v w, (v ∈ O ↔ w ∈ O) → (g v ∈ O ↔ g w ∈ O)) (C : Subgroup (Perm V)) :
    ¬ CFSG.Assembly.IsComponentOf C M := by
  intro hC
  obtain ⟨ω₀, hω₀⟩ : O.Nonempty := Finset.card_pos.mp (by omega)
  have hOc : (Finset.univ \ O).card = 3 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ O), Finset.card_univ, hn, hO]
  have hdiff : ∀ g ∈ M, ∀ v w, v ∈ O → w ∉ O → (g v ∈ O ↔ g w ∉ O) := by
    intro g hg v w hv hw
    have hcard : ((insert w O).image g).card = 4 := by
      rw [Finset.card_image_of_injective _ g.injective, Finset.card_insert_of_notMem hw, hO]
    constructor
    · intro hgv hgw
      have hsub : (insert w O).image g ⊆ O := by
        intro z hz
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact hgw
        · exact (hblock g hg u v (by simp [hu, hv])).mpr hgv
      have := Finset.card_le_card hsub
      omega
    · intro hgw
      by_contra hgv
      have hsub : (insert w O).image g ⊆ Finset.univ \ O := by
        intro z hz
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact hgw
        · exact fun h => hgv ((hblock g hg u v (by simp [hu, hv])).mp h)
      have h1 := Finset.card_le_card hsub
      omega
  let χ : ↥M →* ℤˣ :=
    { toFun := fun g => if (g : Perm V) ω₀ ∈ O then 1 else -1
      map_one' := by simp [hω₀]
      map_mul' := fun g h => by
        simp only [Subgroup.coe_mul, Perm.coe_mul, Function.comp_apply]
        by_cases hh : (h : Perm V) ω₀ ∈ O
        · have e := hblock g g.2 _ _ (show (h : Perm V) ω₀ ∈ O ↔ ω₀ ∈ O by simp [hh, hω₀])
          by_cases hg : (g : Perm V) ω₀ ∈ O
          · simp [hh, hg, e.mpr hg]
          · have : (g : Perm V) ((h : Perm V) ω₀) ∉ O := fun h' => hg (e.mp h')
            simp [hh, hg, this]
        · have e := hdiff g g.2 _ _ hω₀ hh
          by_cases hg : (g : Perm V) ω₀ ∈ O
          · have : (g : Perm V) ((h : Perm V) ω₀) ∉ O := e.mp hg
            simp [hh, hg, this]
          · have : (g : Perm V) ((h : Perm V) ω₀) ∈ O := by
              by_contra h'
              exact hg (e.mpr h')
            simp [hh, hg, this] }
  have hpres : ∀ c ∈ C, (c : Perm V) ω₀ ∈ O := by
    have hle : ⁅C, C⁆ ≤ χ.ker.map M.subtype := by
      rw [Subgroup.commutator_le]
      intro g₁ h₁ g₂ h₂
      refine ⟨⁅(⟨g₁, hC.1 h₁⟩ : ↥M), ⟨g₂, hC.1 h₂⟩⁆, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    intro c hc
    rw [← ggComponent_perfect hC] at hc
    obtain ⟨k, hk, rfl⟩ := hle hc
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hk
    by_contra h
    have hχk : χ k = if (k : Perm V) ω₀ ∈ O then 1 else -1 := rfl
    rw [hχk] at hk
    have h' : ¬ ((k : Perm V) ω₀ ∈ O) := h
    simp only [h', ↓reduceIte] at hk
    exact absurd hk (by decide)
  have hinv : ∀ c ∈ C, ∀ x, (c x ∈ O ↔ x ∈ O) := by
    intro c hc x
    by_cases hx : x ∈ O
    · simp only [hx, iff_true]
      exact (hblock c (hC.1 hc) x ω₀ (by simp [hx, hω₀])).mpr (hpres c hc)
    · simp only [hx, iff_false]
      exact (hdiff c (hC.1 hc) ω₀ x hω₀ hx).mp (hpres c hc)
  have hperf : commutator ↥C = ⊤ := hC.2.2.1
  have hfix1 := ggFix_of_perfect hperf (· ∈ O) hinv (by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp [hO])
  have hfix2 := ggFix_of_perfect hperf (· ∉ O) (fun c hc x => not_congr (hinv c hc x)) (by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have : (Finset.univ.filter fun x => x ∉ O) = Finset.univ \ O := by
      ext x
      simp
    rw [this, hOc]
    norm_num)
  apply ggComponent_ne_bot hC
  rw [Subgroup.eq_bot_iff_forall]
  intro c hc
  ext x
  rw [Perm.one_apply]
  by_cases hx : x ∈ O
  · exact hfix1 c hc x hx
  · exact hfix2 c hc x hx

theorem ggPrime_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p = 3 ∨ p = 5 ∨ 7 ≤ p := by
  have h2 := hp.two_le
  by_contra h
  push Not at h
  obtain ⟨h3, h5, h7⟩ := h
  interval_cases p <;> norm_num at hp <;> omega

theorem ggAltCore {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {M E : Subgroup (Perm V)}
    (hMtop : ¬ alternatingGroup V ≤ M) (hEM : E ≤ M)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hEcard : Nat.card E = p ^ 2)
    (hctl : ∀ g ∈ alternatingGroup V, ∀ x ∈ E, x ≠ 1 → g⁻¹ * x * g ∈ M → g ∈ M) :
    GGAltCoreConclusion p M := by
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
    exact ggAltCore_of_absorbing hX (by omega) (by omega)
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
      refine ggAltCore_of_absorbing hX (by omega) fun h8 => ?_
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
      refine ⟨rfl, ?_, fun C hC => ?_⟩
      · obtain ⟨t, ht⟩ := hdvdn
        have h25 : (5 : ℕ) ^ 2 = 25 := by norm_num
        exact ⟨t, by omega, by omega, ht⟩
      · obtain ⟨ω, rfl⟩ := ggComponent_eq_altOn_orb hOabs (fun ω => (horbcard ω).ge) hC
        exact ⟨(ggAltOnMulEquiv _).trans (Equiv.altCongrHom (finCongr (horbcard ω)))⟩
  ·
    refine ggAltCore_of_absorbing hX₀ (hp7.trans hX₀p) fun h8 => ?_
    have hd := hdvdX X₀ hX₀
    rw [h8] at hd
    have hd' : p ∣ 2 ^ 3 := by norm_num; exact hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd'))

end Core

end CFSG.StandardType
