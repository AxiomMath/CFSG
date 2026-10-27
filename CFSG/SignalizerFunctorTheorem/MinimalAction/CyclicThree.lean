module

public import CFSG.LocalAnalysis.SignalizerFunctor.Coprime
public import CFSG.SignalizerFunctorTheorem.MinimalAction.ElemAbelian
public import CFSG.SignalizerFunctorTheorem.MinimalAction.Orbits
public import CFSG.SignalizerFunctorTheorem.MinimalAction.SpecialTwo

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.MinimalAction

variable {G : Type*} [Group G] [Finite G]

namespace CyclicThree

variable {P : Subgroup G} {x : G}

omit [Finite G] in
theorem ne_bot (h : MinimalThree P x) : P ≠ ⊥ := by
  rintro rfl
  obtain ⟨g, hg, hne⟩ := h.nontrivial
  rw [Subgroup.mem_bot] at hg
  exact hne (by rw [hg, mul_one, one_mul])

omit [Finite G] in
theorem isElemAbelian_commutator (hcentral : ∀ z ∈ ⁅P, P⁆, ∀ c ∈ P, z * c = c * z)
    (hsq : ∀ z ∈ ⁅P, P⁆, z ^ 2 = 1) : IsElemAbelian 2 ⁅P, P⁆ :=
  ⟨IsMulCommutative.of_comm fun a b =>
    Subtype.ext (hcentral a a.2 b (Subgroup.commutator_le_self P b.2)), hsq⟩

theorem false_of_commutator_eq_bot (h : MinimalThree P x)
    (hrank : ∀ E : Subgroup G, E ≤ P → IsElemAbelian 2 E → Nat.card E ≤ 4)
    (hbot : ⁅P, P⁆ = ⊥) : False := by
  have hmod := h.card_modEq_nine
  rw [hbot, Subgroup.card_bot] at hmod
  have hel : IsElemAbelian 2 P :=
    ⟨Subgroup.commutator_self_eq_bot_iff.mp hbot, fun g hg => by
      have hg2 := h.sq_mem_commutator hg
      rwa [hbot, Subgroup.mem_bot] at hg2⟩
  have h4 := hrank P le_rfl hel
  have hpos : 0 < Nat.card P := Nat.card_pos
  have h1 : Nat.card P = 1 := by
    unfold Nat.ModEq at hmod
    omega
  exact ne_bot h (Subgroup.eq_bot_of_card_eq P h1)

theorem card_commutator_eq_four (h : MinimalThree P x) (hel : IsElemAbelian 2 ⁅P, P⁆)
    (hfpf : ∀ g ∈ P, x * g = g * x → g = 1)
    (hrank : ∀ E : Subgroup G, E ≤ P → IsElemAbelian 2 E → Nat.card E ≤ 4)
    (hP' : ⁅P, P⁆ ≠ ⊥) : Nat.card (⁅P, P⁆ : Subgroup G) = 4 := by
  have hle : ⁅P, P⁆ ≤ P := Subgroup.commutator_le_self P
  have h4 : Nat.card (⁅P, P⁆ : Subgroup G) ≤ 4 := hrank _ hle hel
  have hne1 : Nat.card (⁅P, P⁆ : Subgroup G) ≠ 1 := fun h1 =>
    hP' (Subgroup.eq_bot_of_card_eq _ h1)
  have hne2 : Nat.card (⁅P, P⁆ : Subgroup G) ≠ 2 := by
    intro h2
    have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer ((⁅P, P⁆ : Subgroup G) : Set G) :=
      CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer _ P P
        (Subgroup.zpowers_le.mpr h.normalizes) (Subgroup.zpowers_le.mpr h.normalizes)
    have hmod := CFSG.SignalizerFunctor.Helpers.centralizer_card_modEq 3 Nat.prime_three
      (Subgroup.zpowers x) ⁅P, P⁆ h.threeGroup hnorm
    have hbot : (⁅P, P⁆ : Subgroup G) ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      exact hfpf g (hle hg.1)
        (Subgroup.mem_centralizer_iff.mp hg.2 x (Subgroup.mem_zpowers x))
    rw [hbot, Subgroup.card_bot, h2] at hmod
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨j, hj⟩ := (h.pgroup.to_le hle).exists_card_eq
  have hj3 : j < 3 := by
    by_contra hcon
    have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hcon)
    omega
  interval_cases j <;> omega

theorem mem_commutator_of_sq_eq_one (h : MinimalThree P x) (hel : IsElemAbelian 2 ⁅P, P⁆)
    (hrank : ∀ E : Subgroup G, E ≤ P → IsElemAbelian 2 E → Nat.card E ≤ 4)
    (hcard : Nat.card (⁅P, P⁆ : Subgroup G) = 4) {g : G} (hg : g ∈ P) (hg2 : g ^ 2 = 1) :
    g ∈ ⁅P, P⁆ := by
  by_contra hgP'
  have hle : ⁅P, P⁆ ≤ P := Subgroup.commutator_le_self P
  have hgle : Subgroup.zpowers g ≤ P := Subgroup.zpowers_le.mpr hg
  have hEel : IsElemAbelian 2 (Subgroup.zpowers g ⊔ ⁅P, P⁆) :=
    isElemAbelian_sup (isElemAbelian_zpowers hg2) hel fun a ha b hb =>
      (h.commutator_central hb (hgle ha)).symm
  have hlt : ⁅P, P⁆ < Subgroup.zpowers g ⊔ ⁅P, P⁆ := by
    refine lt_of_le_of_ne le_sup_right fun heq => hgP' ?_
    rw [heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
  have h1 := CFSG.natCard_lt_of_subgroup_lt hlt
  have h2 := hrank _ (sup_le hgle hle) hEel
  omega

theorem card_le_of_commutator_ne_bot (h : MinimalThree P x) (hel : IsElemAbelian 2 ⁅P, P⁆)
    (hrank : ∀ E : Subgroup G, E ≤ P → IsElemAbelian 2 E → Nat.card E ≤ 4)
    (hP' : ⁅P, P⁆ ≠ ⊥) (hcard : Nat.card (⁅P, P⁆ : Subgroup G) = 4) : Nat.card P ≤ 128 := by
  have hle : ⁅P, P⁆ ≤ P := Subgroup.commutator_le_self P
  have hmemZ : ∀ z : P, z ∈ Subgroup.center P ↔ (z : G) ∈ (⁅P, P⁆ : Subgroup G) := fun z => by
    rw [Subgroup.mem_center_iff]
    constructor
    · intro hz
      exact h.center_le_commutator hP' z.2 fun c hc => congrArg Subtype.val (hz ⟨c, hc⟩).symm
    · intro hz c
      exact Subtype.ext (h.commutator_central hz c.2).symm
  have hZeq : Subgroup.center P = (⁅P, P⁆ : Subgroup G).subgroupOf P := by
    ext z
    rw [Subgroup.mem_subgroupOf]
    exact hmemZ z
  refine card_le_of_special_two ?_ (fun a b => ?_) (fun g => ?_) (fun z hz => ?_)
    (fun g hg2 => ?_)
  · rw [hZeq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard]
  · exact (hmemZ _).2 (Subgroup.commutator_mem_commutator a.2 b.2)
  · exact (hmemZ _).2 (h.sq_mem_commutator g.2)
  · exact Subtype.ext (h.sq_eq_one_of_mem_commutator ((hmemZ z).1 hz))
  · exact (hmemZ g).2 (mem_commutator_of_sq_eq_one h hel hrank hcard g.2 (Subtype.ext_iff.mp hg2))

theorem false_of_commutator_ne_bot (h : MinimalThree P x)
    (hfpf : ∀ g ∈ P, x * g = g * x → g = 1)
    (hrank : ∀ E : Subgroup G, E ≤ P → IsElemAbelian 2 E → Nat.card E ≤ 4)
    (hP' : ⁅P, P⁆ ≠ ⊥) : False := by
  have hel : IsElemAbelian 2 ⁅P, P⁆ :=
    isElemAbelian_commutator (fun _ hz _ hc => h.commutator_central hz hc)
      fun _ hz => h.sq_eq_one_of_mem_commutator hz
  have hcard := card_commutator_eq_four h hel hfpf hrank hP'
  have h128 := card_le_of_commutator_ne_bot h hel hrank hP' hcard
  have hlt : ⁅P, P⁆ < P := CFSG.GorensteinWalter.SchurZassenhaus.commutator_lt_of_pGroups P P
    h.pgroup h.pgroup Subgroup.le_normalizer (ne_bot h)
  have h4P := CFSG.natCard_lt_of_subgroup_lt hlt
  obtain ⟨k, hk⟩ := h.pgroup.exists_card_eq
  have hmod := h.card_modEq_nine
  rw [hcard, hk] at hmod
  have hk8 : k < 8 := by
    by_contra hcon
    have : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hcon)
    omega
  unfold Nat.ModEq at hmod
  interval_cases k <;> omega

end CyclicThree

theorem MinimalThree.false_of_fixedPointFree {P : Subgroup G} {x : G} (h : MinimalThree P x)
    (hfpf : ∀ g ∈ P, x * g = g * x → g = 1)
    (hrank : ∀ E : Subgroup G, E ≤ P → IsElemAbelian 2 E → Nat.card E ≤ 4) : False := by
  by_cases hP' : ⁅P, P⁆ = ⊥
  · exact CyclicThree.false_of_commutator_eq_bot h hrank hP'
  · exact CyclicThree.false_of_commutator_ne_bot h hfpf hrank hP'

theorem cube_centralizes {P : Subgroup G} {x : G} (hP : IsPGroup 2 P)
    (hx : x ∈ Subgroup.normalizer (P : Set G)) (hx3 : IsPGroup 3 (Subgroup.zpowers x))
    (hfpf : ∀ g ∈ P, x * g = g * x → g = 1)
    (hrank : ∀ E : Subgroup G, E ≤ P → IsElemAbelian 2 E → Nat.card E ≤ 4) :
    ∀ g ∈ P, x ^ 3 * g = g * x ^ 3 := by
  suffices key : ∀ n : ℕ, ∀ P : Subgroup G, Nat.card P = n → IsPGroup 2 P →
      x ∈ Subgroup.normalizer (P : Set G) → (∀ g ∈ P, x * g = g * x → g = 1) →
      (∀ E : Subgroup G, E ≤ P → IsElemAbelian 2 E → Nat.card E ≤ 4) →
      ∀ g ∈ P, x ^ 3 * g = g * x ^ 3 from key _ P rfl hP hx hfpf hrank
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hn hP hx hfpf hrank
    by_contra hcon
    push Not at hcon
    have hmin : MinimalThree P x :=
      { pgroup := hP
        normalizes := hx
        threeGroup := hx3
        nontrivial := hcon
        minimal := fun R hRP hxR =>
          ih (Nat.card R) (hn ▸ CFSG.natCard_lt_of_subgroup_lt hRP) R rfl (hP.to_le hRP.le) hxR
            (fun g hg => hfpf g (hRP.le hg)) (fun E hE => hrank E (hE.trans hRP.le)) }
    exact hmin.false_of_fixedPointFree hfpf hrank

end CFSG.SignalizerFunctorTheorem.MinimalAction
