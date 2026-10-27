module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderUOMono

public section

namespace CFSG.StandardType

namespace NoOffUO

open MulAction

section HomCount

variable {Γ : Type*} [Group Γ] {p : ℕ}

@[expose] def homVanish (p : ℕ) (K : Subgroup Γ) : Set (Γ → ZMod p) :=
  {c | (∀ a b, c (a * b) = c a + c b) ∧ ∀ k ∈ K, c k = 0}

@[expose] def zeroSub {c : Γ → ZMod p} (hc : ∀ a b, c (a * b) = c a + c b) : Subgroup Γ where
  carrier := {a | c a = 0}
  mul_mem' {a b} ha hb := by
    change c (a * b) = 0
    rw [hc, ha, hb, add_zero]
  one_mem' := by
    change c 1 = 0
    have h := hc 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  inv_mem' {a} ha := by
    change c a⁻¹ = 0
    have h1 := hc a⁻¹ a
    have h2 := hc 1 1
    rw [mul_one] at h2
    rw [inv_mul_cancel, left_eq_add.mp h2, ha, add_zero] at h1
    exact h1.symm

theorem homVanish_sub {K : Subgroup Γ} {c c' : Γ → ZMod p} (hc : c ∈ homVanish p K)
    (hc' : c' ∈ homVanish p K) : c - c' ∈ homVanish p K := by
  refine ⟨fun a b => ?_, fun k hk => ?_⟩
  · simp only [Pi.sub_apply, hc.1, hc'.1]
    ring
  · simp only [Pi.sub_apply, hc.2 k hk, hc'.2 k hk, sub_zero]

theorem mem_homVanish_sup {K : Subgroup Γ} {g : Γ} {c : Γ → ZMod p} (hc : c ∈ homVanish p K)
    (hg : c g = 0) : c ∈ homVanish p (K ⊔ Subgroup.zpowers g) := by
  refine ⟨hc.1, fun k hk => ?_⟩
  have hle : K ⊔ Subgroup.zpowers g ≤ zeroSub hc.1 :=
    sup_le (fun k hk => hc.2 k hk) ((Subgroup.zpowers_le).mpr hg)
  exact hle hk

theorem homVanish_top_subsingleton : (homVanish p (⊤ : Subgroup Γ)).Subsingleton := by
  intro c hc c' hc'
  funext a
  rw [hc.2 a trivial, hc'.2 a trivial]

theorem card_homVanish_le [Finite Γ] [Fact p.Prime] (hexp : ∀ a : Γ, a ^ p = 1)
    (K : Subgroup Γ) : Nat.card (homVanish p K) ≤ K.index := by
  have hpG : IsPGroup p Γ := fun a => ⟨1, by rw [pow_one, hexp]⟩
  induction hm : K.index using Nat.strong_induction_on generalizing K with
  | _ m ih =>
  by_cases hK : K = ⊤
  · subst hK
    rw [← hm, Subgroup.index_top]
    exact Finite.card_le_one_iff_subsingleton.mpr homVanish_top_subsingleton.coe_sort
  obtain ⟨g, hg⟩ : ∃ g, g ∉ K := by
    by_contra h
    push Not at h
    exact hK (eq_top_iff.mpr fun g _ => h g)
  set K' := K ⊔ Subgroup.zpowers g with hK'
  have hKK' : K ≤ K' := le_sup_left
  have hidx : K.relIndex K' * K'.index = K.index := Subgroup.relIndex_mul_index hKK'
  have hrel : p ≤ K.relIndex K' := by
    obtain ⟨j, hj⟩ := (hpG.to_subgroup K').index (K.subgroupOf K')
    have hne : K.relIndex K' ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact fun h => hg (h (le_sup_right (a := K) (Subgroup.mem_zpowers g)))
    rw [Subgroup.relIndex, hj] at hne ⊢
    rcases j with _ | j
    · exact absurd (pow_zero p) hne
    · exact (Nat.le_self_pow (Nat.succ_ne_zero j) p)
  have hK'pos : 0 < K'.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hlt : K'.index < m := by
    rw [← hm, ← hidx]
    nlinarith
  have ih' := ih _ hlt K' rfl
  have hex : ∀ t : ZMod p, ∃ c : Γ → ZMod p,
      (∃ c' ∈ homVanish p K, c' g = t) → c ∈ homVanish p K ∧ c g = t := fun t => by
    by_cases h : ∃ c' ∈ homVanish p K, c' g = t
    · obtain ⟨c', hc', hc'g⟩ := h
      exact ⟨c', fun _ => ⟨hc', hc'g⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose rep hrep0 using hex
  have hrep : ∀ c ∈ homVanish p K, rep (c g) ∈ homVanish p K ∧ rep (c g) g = c g :=
    fun c hc => hrep0 _ ⟨c, hc, rfl⟩
  have hfib : Nat.card (homVanish p K) ≤ p * Nat.card (homVanish p K') := by
    let Φ : homVanish p K → ZMod p × homVanish p K' := fun c =>
      ((c : Γ → ZMod p) g, ⟨(c : Γ → ZMod p) - rep ((c : Γ → ZMod p) g),
        mem_homVanish_sup (homVanish_sub c.2 (hrep c c.2).1)
          (by rw [Pi.sub_apply, (hrep c c.2).2, sub_self])⟩)
    have hΦ : Function.Injective Φ := by
      intro c c' h
      have h1 : (c : Γ → ZMod p) g = (c' : Γ → ZMod p) g := congrArg Prod.fst h
      have h2 := congrArg (fun y => ((Prod.snd y : homVanish p K') : Γ → ZMod p)) h
      simp only [Φ] at h2
      rw [h1] at h2
      exact Subtype.ext (sub_left_inj.mp h2)
    calc Nat.card (homVanish p K) ≤ Nat.card (ZMod p × homVanish p K') :=
          Nat.card_le_card_of_injective Φ hΦ
      _ = p * Nat.card (homVanish p K') := by
          rw [Nat.card_prod, Nat.card_zmod]
  calc Nat.card (homVanish p K) ≤ p * Nat.card (homVanish p K') := hfib
    _ ≤ K.relIndex K' * K'.index := Nat.mul_le_mul hrel ih'
    _ = m := by rw [hidx, hm]

theorem card_mul_index_sup_le [Finite Γ] (S₁ S₂ : Subgroup Γ) :
    Nat.card Γ * (S₁ ⊔ S₂).index ≤ S₁.index * S₂.index * Nat.card (S₁ ⊓ S₂ : Subgroup Γ) := by
  have : S₁.IsFiniteRelIndex (S₁ ⊔ S₂) := Subgroup.isFiniteRelIndex_of_finiteIndex
  have h1 := Subgroup.relIndex_mul_index (le_sup_left : S₁ ≤ S₁ ⊔ S₂)
  have h2 : S₁.relIndex S₂ ≤ S₁.relIndex (S₁ ⊔ S₂) :=
    Subgroup.relIndex_le_of_le_right le_sup_right Subgroup.relIndex_ne_zero
  have h3 := Subgroup.relIndex_mul_card S₁ S₂
  have h4 := Subgroup.card_mul_index S₂
  have hr : 0 < S₁.relIndex (S₁ ⊔ S₂) := Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  refine Nat.le_of_mul_le_mul_right ?_ hr
  calc Nat.card Γ * (S₁ ⊔ S₂).index * S₁.relIndex (S₁ ⊔ S₂)
      = Nat.card Γ * S₁.index := by rw [mul_assoc, mul_comm (S₁ ⊔ S₂).index, h1]
    _ = S₁.index * S₂.index * Nat.card (S₁ ⊓ S₂ : Subgroup Γ) * S₁.relIndex S₂ := by
        rw [← h4, ← h3]
        ring
    _ ≤ S₁.index * S₂.index * Nat.card (S₁ ⊓ S₂ : Subgroup Γ) * S₁.relIndex (S₁ ⊔ S₂) :=
        Nat.mul_le_mul_left _ h2

end HomCount

section Proj

variable {X : Type} [Fintype X] [DecidableEq X] {p : ℕ}

@[expose] def projFix (p : ℕ) (A : Subgroup (Equiv.Perm X)) : Set (X → ZMod p) :=
  {v | ∀ a ∈ A, ∃ c : ZMod p, ∀ x, v (a x) = v x + c}

@[expose] def permFix (p : ℕ) (A : Subgroup (Equiv.Perm X)) : Set (X → ZMod p) :=
  {v | ∀ a ∈ A, ∀ x, v (a x) = v x}

omit [Fintype X] [DecidableEq X] in
theorem permFix_prop {A : Subgroup (Equiv.Perm X)} :
    ∀ s ∈ permFix p A, ∀ s' ∈ permFix p A, ∀ a ∈ A, ∀ x, s x = s' x → s (a x) = s' (a x) :=
  fun _ hs _ hs' a ha x hx => by rw [hs a ha, hs' a ha, hx]

omit [Fintype X] [DecidableEq X] in
theorem projFix_subset_permFix {A : Subgroup (Equiv.Perm X)} {z : X} (hz : ∀ a ∈ A, a z = z) :
    projFix p A ⊆ permFix p A := by
  intro v hv a ha x
  obtain ⟨c, hc⟩ := hv a ha
  have h := hc z
  rw [hz a ha, left_eq_add] at h
  rw [hc x, h, add_zero]

omit [DecidableEq X] in
theorem card_permFix_sumZero_mul_le [NeZero p] {A : Subgroup (Equiv.Perm X)} {z : X}
    (hz : ∀ a ∈ A, a z = z) :
    Nat.card (permFix p A ∩ {v | ∑ x, v x = 0} : Set (X → ZMod p)) * p ≤
      Nat.card (permFix p A) := by
  classical
  have hδ : ∀ t : ZMod p, Pi.single z t ∈ permFix p A := by
    intro t a ha x
    by_cases hx : x = z
    · rw [hx, hz a ha]
    · have hax : a x ≠ z := fun h => hx (a.injective (h.trans (hz a ha).symm))
      rw [Pi.single_eq_of_ne hax, Pi.single_eq_of_ne hx]
  let Φ : (permFix p A ∩ {v | ∑ x, v x = 0} : Set (X → ZMod p)) × ZMod p → permFix p A :=
    fun vt => ⟨(vt.1 : X → ZMod p) + Pi.single z vt.2, fun a ha x => by
      simp only [Pi.add_apply]
      rw [vt.1.2.1 a ha x, hδ vt.2 a ha x]⟩
  have hsum : ∀ vt : (permFix p A ∩ {v | ∑ x, v x = 0} : Set (X → ZMod p)) × ZMod p,
      ∑ x, ((Φ vt : permFix p A) : X → ZMod p) x = vt.2 := by
    rintro ⟨v, t⟩
    change ∑ x, ((v : X → ZMod p) + (Pi.single z t : X → ZMod p)) x = t
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      ite_true]
    rw [show ∑ x, (v : X → ZMod p) x = 0 from v.2.2, zero_add]
  have hΦ : Function.Injective Φ := by
    rintro ⟨v, t⟩ ⟨v', t'⟩ h
    have ht : t = t' := by
      have h1 := hsum ⟨v, t⟩
      rw [h, hsum ⟨v', t'⟩] at h1
      exact h1.symm
    subst ht
    have h2 : (v : X → ZMod p) + Pi.single z t = (v' : X → ZMod p) + Pi.single z t :=
      congrArg Subtype.val h
    rw [Prod.mk.injEq]
    exact ⟨Subtype.ext (add_right_cancel h2), rfl⟩
  calc Nat.card (permFix p A ∩ {v | ∑ x, v x = 0} : Set (X → ZMod p)) * p
      = Nat.card ((permFix p A ∩ {v | ∑ x, v x = 0} : Set (X → ZMod p)) × ZMod p) := by
        rw [Nat.card_prod, Nat.card_zmod]
    _ ≤ Nat.card (permFix p A) := Nat.card_le_card_of_injective Φ hΦ

omit [Fintype X] [DecidableEq X] in
theorem projFix_apply {A : Subgroup (Equiv.Perm X)} {v : X → ZMod p} (hv : v ∈ projFix p A)
    {a : Equiv.Perm X} (ha : a ∈ A) (x₀ x : X) : v (a x) = v x + (v (a x₀) - v x₀) := by
  obtain ⟨c, hc⟩ := hv a ha
  rw [hc x, hc x₀]
  ring

omit [Fintype X] [DecidableEq X] in
theorem cocyc_mem {A : Subgroup (Equiv.Perm X)} {v : X → ZMod p} (hv : v ∈ projFix p A)
    (x₀ : X) : (fun a : A => v ((a : Equiv.Perm X) x₀) - v x₀) ∈
      homVanish p (⨆ ω : orbitRel.Quotient A X, stabilizer A ω.out) := by
  have hadd : ∀ a b : A, v (((a * b : A) : Equiv.Perm X) x₀) - v x₀ =
      (v ((a : Equiv.Perm X) x₀) - v x₀) + (v ((b : Equiv.Perm X) x₀) - v x₀) := by
    intro a b
    rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, projFix_apply hv a.2 x₀]
    ring
  refine ⟨hadd, fun k hk => ?_⟩
  have hle : (⨆ ω : orbitRel.Quotient A X, stabilizer A ω.out) ≤
      zeroSub (c := fun a : A => v ((a : Equiv.Perm X) x₀) - v x₀) hadd := by
    refine iSup_le fun ω a ha => ?_
    change v ((a : Equiv.Perm X) x₀) - v x₀ = 0
    have h1 := projFix_apply hv a.2 x₀ ω.out
    have h2 : (a : Equiv.Perm X) ω.out = ω.out := ha
    rw [h2, left_eq_add] at h1
    exact h1
  exact hle hk

omit [DecidableEq X] in
theorem card_projFix_le [NeZero p] {A : Subgroup (Equiv.Perm X)}
    [Fintype (orbitRel.Quotient A X)] (x₀ : X) :
    Nat.card (projFix p A) ≤ p ^ Fintype.card (orbitRel.Quotient A X) *
      Nat.card (homVanish p (⨆ ω : orbitRel.Quotient A X, stabilizer A ω.out)) := by
  let Φ : projFix p A → (orbitRel.Quotient A X → ZMod p) ×
      homVanish p (⨆ ω : orbitRel.Quotient A X, stabilizer A ω.out) := fun v =>
    (fun ω => (v : X → ZMod p) ω.out, ⟨_, cocyc_mem v.2 x₀⟩)
  have hΦ : Function.Injective Φ := by
    intro v v' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun y => ((Prod.snd y : homVanish p _) : A → ZMod p)) h
    simp only [Φ] at h1 h2
    apply Subtype.ext
    funext x
    obtain ⟨b, hb⟩ := mem_orbit_out A x
    change b • _ = x at hb
    rw [← hb]
    change (v : X → ZMod p) ((b : Equiv.Perm X) _) = (v' : X → ZMod p) ((b : Equiv.Perm X) _)
    rw [projFix_apply v.2 b.2 x₀, projFix_apply v'.2 b.2 x₀, congrFun h1 (Quotient.mk'' x)]
    exact congrArg _ (congrFun h2 b)
  calc Nat.card (projFix p A)
      ≤ Nat.card ((orbitRel.Quotient A X → ZMod p) ×
          homVanish p (⨆ ω : orbitRel.Quotient A X, stabilizer A ω.out)) :=
        Nat.card_le_card_of_injective Φ hΦ
    _ = _ := by rw [Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]

end Proj

section Count2

variable {X : Type} [Fintype X] [DecidableEq X] {p : ℕ}

theorem sq_mul_le_pow_self {p k : ℕ} (hp : 3 ≤ p) (hk : 3 ≤ k) : p ^ 2 * k ≤ p ^ k := by
  induction k, hk using Nat.le_induction with
  | base => nlinarith
  | succ k hk ih =>
    have h1 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    calc p ^ 2 * (k + 1) = p ^ 2 * k + p ^ 2 := by ring
      _ ≤ p ^ k + p ^ k := by omega
      _ ≤ p ^ k * p := by nlinarith
      _ = p ^ (k + 1) := by ring

theorem two_mul_add_three_le_three_pow {a : ℕ} (ha : 2 ≤ a) : 2 * a + 3 ≤ 3 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ a ha ih =>
    have : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ]
    omega

omit [Fintype X] [DecidableEq X] in
theorem iInf_stabilizer_out_eq_bot {A : Subgroup (Equiv.Perm X)}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    (⨅ ω : orbitRel.Quotient A X, stabilizer A ω.out) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨b, hb⟩ := mem_orbit_out A x
  change b • _ = x at hb
  have hfix : a • (Quotient.mk'' x : orbitRel.Quotient A X).out =
      (Quotient.mk'' x : orbitRel.Quotient A X).out :=
    Subgroup.mem_iInf.mp ha _
  have h := smul_smul_eq_of_comm hA b hfix
  rw [hb] at h
  exact h

omit [DecidableEq X] in
theorem card_projFix_mul_sq_le_of_noFix [Fact p.Prime] (hp3 : 3 ≤ p)
    (hX : 4 ≤ Fintype.card X) {A : Subgroup (Equiv.Perm X)}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ p = 1)
    (hnf : ∀ z : X, ∃ a ∈ A, a z ≠ z) :
    Nat.card (projFix p A) * Nat.card A * p ^ 2 ≤ p ^ Fintype.card X := by
  classical
  have : NeZero p := ⟨by omega⟩
  let _ : Fintype (orbitRel.Quotient A X) := Fintype.ofFinite _
  obtain ⟨x₀⟩ : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hexp' : ∀ a : A, a ^ p = 1 := fun a =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hexp a a.2)
  have hpG : IsPGroup p A := fun a => ⟨1, by rw [pow_one, hexp' a]⟩
  set k : orbitRel.Quotient A X → ℕ := fun ω => Nat.card (orbit A ω.out) with hk
  have horb : ∀ ω, 3 ≤ k ω := by
    intro ω
    obtain ⟨j, hj⟩ := hpG.card_orbit ω.out
    obtain ⟨a, haA, ha⟩ := hnf ω.out
    have h2 : 1 < Nat.card (orbit A ω.out) := by
      have hne : (⟨ω.out, mem_orbit_self _⟩ : orbit A ω.out) ≠
          ⟨(⟨a, haA⟩ : A) • ω.out, mem_orbit _ _⟩ :=
        fun h => ha (congrArg Subtype.val h).symm
      have : Nontrivial (orbit A ω.out) := ⟨⟨_, _, hne⟩⟩
      exact Finite.one_lt_card
    change 3 ≤ Nat.card (orbit A ω.out)
    rw [hj] at h2 ⊢
    rcases j with _ | j
    · simp at h2
    · exact hp3.trans (Nat.le_self_pow (Nat.succ_ne_zero j) p)
  set K := ⨆ ω : orbitRel.Quotient A X, stabilizer A ω.out with hKdef
  have hK := card_homVanish_le (p := p) hexp' K
  have hZ : Nat.card (projFix p A) ≤
      p ^ Fintype.card (orbitRel.Quotient A X) * Nat.card (homVanish p K) :=
    card_projFix_le x₀
  have hprod : Nat.card A ≤ ∏ ω, k ω := card_le_prod_card_orbit hA
  have hsum : ∑ ω, k ω = Fintype.card X := sum_card_orbit A
  have hidx : ∀ ω, (stabilizer A ω.out).index = k ω := fun ω => by
    rw [index_stabilizer]
    exact (Nat.card_coe_set_eq _).symm
  by_cases hm : Fintype.card (orbitRel.Quotient A X) ≤ 1
  ·
    have hm1 : Fintype.card (orbitRel.Quotient A X) = 1 := by
      have : 0 < Fintype.card (orbitRel.Quotient A X) :=
        Fintype.card_pos_iff.mpr ⟨Quotient.mk'' x₀⟩
      omega
    obtain ⟨ω₁, hω₁⟩ := Fintype.card_eq_one_iff.mp hm1
    have hsum1 : ∑ ω, k ω = k ω₁ :=
      Finset.sum_eq_single ω₁ (fun b _ hb => absurd (hω₁ b) hb) (by simp)
    have hprod1 : ∏ ω, k ω = k ω₁ :=
      Finset.prod_eq_single ω₁ (fun b _ hb => absurd (hω₁ b) hb) (by simp)
    have hKA : K.index ≤ Nat.card A := by
      have h1 := Subgroup.card_mul_index K
      have h2 : 0 < Nat.card K := Nat.card_pos
      nlinarith
    obtain ⟨a, ha⟩ := hpG.card_orbit ω₁.out
    have hn : Fintype.card X = p ^ a := by rw [← hsum, hsum1]; exact ha
    have hexpo : 3 + 2 * a ≤ p ^ a := by
      rcases Nat.lt_or_ge a 2 with h | h
      · interval_cases a
        · simp at hn; omega
        · have hp5 : 5 ≤ p := by
            have hpp : p.Prime := Fact.out
            rw [pow_one] at hn
            rcases Nat.lt_or_ge p 5 with h5 | h5
            · interval_cases p
              · omega
              · norm_num at hpp
            · exact h5
          simp only [pow_one]
          omega
      · exact (two_mul_add_three_le_three_pow h).trans' (by omega) |>.trans
          (Nat.pow_le_pow_left hp3 a)
    calc Nat.card (projFix p A) * Nat.card A * p ^ 2
        ≤ (p ^ 1 * Nat.card A) * Nat.card A * p ^ 2 := by
          refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
          rw [← hm1]
          exact hZ.trans (Nat.mul_le_mul_left _ (hK.trans hKA))
      _ ≤ (p ^ 1 * p ^ a) * p ^ a * p ^ 2 := by
          have hAn : Nat.card A ≤ p ^ a :=
            calc Nat.card A ≤ ∏ ω, k ω := hprod
              _ = k ω₁ := hprod1
              _ = p ^ a := ha
          gcongr
      _ = p ^ (3 + 2 * a) := by ring
      _ ≤ p ^ (p ^ a) := Nat.pow_le_pow_right (by omega) hexpo
      _ = p ^ Fintype.card X := by rw [hn]
  ·
    push Not at hm
    obtain ⟨ω₁⟩ : Nonempty (orbitRel.Quotient A X) := ⟨Quotient.mk'' x₀⟩
    obtain ⟨ω₂, hω₂⟩ := Fintype.exists_ne_of_one_lt_card hm ω₁
    set S₁ := stabilizer A ω₁.out
    set S₂ := stabilizer A ω₂.out
    have hKS : S₁ ⊔ S₂ ≤ K := sup_le (le_iSup (fun ω => stabilizer A ω.out) ω₁)
      (le_iSup (fun ω => stabilizer A ω.out) ω₂)
    have hKidx : K.index ≤ (S₁ ⊔ S₂).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
        (Subgroup.index_dvd_of_le hKS)
    have hsup := card_mul_index_sup_le S₁ S₂
    set f : orbitRel.Quotient A X → ℕ := fun ω =>
      if ω ∈ ({ω₁, ω₂} : Finset (orbitRel.Quotient A X)) then 1 else k ω with hf
    have hinf : Nat.card (S₁ ⊓ S₂ : Subgroup A) ≤ ∏ ω, f ω := by
      rw [← Subgroup.relIndex_bot_left, ← iInf_stabilizer_out_eq_bot hA]
      refine (Subgroup.relIndex_iInf_le _).trans (Finset.prod_le_prod fun ω _ => ?_)
      simp only [hf]
      split_ifs with hω
      · rw [Subgroup.relIndex_eq_one.mpr]
        rcases Finset.mem_insert.mp hω with rfl | hω
        · exact inf_le_left
        · rw [Finset.mem_singleton] at hω
          subst hω
          exact inf_le_right
      · have : (stabilizer A ω.out).IsFiniteRelIndex ⊤ := Subgroup.isFiniteRelIndex_of_finiteIndex
        rw [← hidx ω, ← Subgroup.relIndex_top_right]
        exact Subgroup.relIndex_le_of_le_right le_top Subgroup.relIndex_ne_zero
    have hsplit : ∏ ω, k ω = k ω₁ * k ω₂ * ∏ ω, f ω := by
      have hpt : ∀ ω, k ω =
          (if ω ∈ ({ω₁, ω₂} : Finset (orbitRel.Quotient A X)) then k ω else 1) * f ω := by
        intro ω
        simp only [hf]
        split_ifs <;> simp
      rw [Finset.prod_congr rfl fun ω _ => hpt ω, Finset.prod_mul_distrib, Finset.prod_ite_mem,
        Finset.univ_inter, Finset.prod_pair hω₂.symm]
    have hAK : Nat.card A * K.index ≤ ∏ ω, k ω := by
      calc Nat.card A * K.index ≤ Nat.card A * (S₁ ⊔ S₂).index := Nat.mul_le_mul_left _ hKidx
        _ ≤ S₁.index * S₂.index * Nat.card (S₁ ⊓ S₂ : Subgroup A) := hsup
        _ ≤ k ω₁ * k ω₂ * ∏ ω, f ω := by
            rw [hidx ω₁, hidx ω₂]
            exact Nat.mul_le_mul_left _ hinf
        _ = ∏ ω, k ω := hsplit.symm
    set m := Fintype.card (orbitRel.Quotient A X)
    have hpm : p ^ 2 ≤ p ^ m := Nat.pow_le_pow_right (by omega) hm
    calc Nat.card (projFix p A) * Nat.card A * p ^ 2
        ≤ (p ^ m * K.index) * Nat.card A * p ^ m := by
          gcongr
          exact hZ.trans (Nat.mul_le_mul_left _ hK)
      _ = p ^ m * p ^ m * (Nat.card A * K.index) := by ring
      _ ≤ p ^ m * p ^ m * ∏ ω, k ω := Nat.mul_le_mul_left _ hAK
      _ = ∏ ω, p ^ 2 * k ω := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul,
            ← pow_add]
          ring_nf
          rfl
      _ ≤ ∏ ω, p ^ k ω := Finset.prod_le_prod fun ω _ => sq_mul_le_pow_self hp3 (horb ω)
      _ = p ^ Fintype.card X := by rw [Finset.prod_pow_eq_pow_sum, hsum]

end Count2

section Bounds

variable {X : Type} [Fintype X] {p : ℕ}

omit [Fintype X] in
theorem zero_mem_projFix {A : Subgroup (Equiv.Perm X)} : (0 : X → ZMod p) ∈ projFix p A :=
  fun _ _ => ⟨0, fun _ => by simp⟩

theorem card_projFix_mul_lt [Fact p.Prime] (hp3 : 3 ≤ p) (hX : 4 ≤ Fintype.card X)
    {A : Subgroup (Equiv.Perm X)} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hexp : ∀ a ∈ A, a ^ p = 1) (hne : A ≠ ⊥) :
    Nat.card (projFix p A) * Nat.card A < p ^ Fintype.card X := by
  classical
  have : NeZero p := ⟨by omega⟩
  by_cases hfix : ∃ z, ∀ a ∈ A, a z = z
  · obtain ⟨z, hz⟩ := hfix
    calc Nat.card (projFix p A) * Nat.card A ≤ Nat.card (permFix p A) * Nat.card A :=
          Nat.mul_le_mul_right _ (Nat.card_mono (Set.toFinite _) (projFix_subset_permFix hz))
      _ < p ^ Fintype.card X := card_mul_card_lt_pow hp3 hA hne permFix_prop
  · push Not at hfix
    have h := card_projFix_mul_sq_le_of_noFix hp3 hX hA hexp hfix
    have : Nonempty (projFix p A) := ⟨⟨0, zero_mem_projFix⟩⟩
    have hpos : 0 < Nat.card (projFix p A) * Nat.card A := Nat.mul_pos Nat.card_pos Nat.card_pos
    have hp2 : 1 < p ^ 2 := by nlinarith
    calc Nat.card (projFix p A) * Nat.card A < Nat.card (projFix p A) * Nat.card A * p ^ 2 :=
          lt_mul_of_one_lt_right hpos hp2
      _ ≤ p ^ Fintype.card X := h

theorem card_projFix_sumZero_mul_lt [Fact p.Prime] (hp3 : 3 ≤ p) (hX : 4 ≤ Fintype.card X)
    {A : Subgroup (Equiv.Perm X)} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hexp : ∀ a ∈ A, a ^ p = 1) (hne : A ≠ ⊥) :
    Nat.card (projFix p A ∩ {v | ∑ x, v x = 0} : Set (X → ZMod p)) * Nat.card A * p <
      p ^ Fintype.card X := by
  classical
  have : NeZero p := ⟨by omega⟩
  by_cases hfix : ∃ z, ∀ a ∈ A, a z = z
  · obtain ⟨z, hz⟩ := hfix
    have h1 : Nat.card (projFix p A ∩ {v | ∑ x, v x = 0} : Set (X → ZMod p)) ≤
        Nat.card (permFix p A ∩ {v | ∑ x, v x = 0} : Set (X → ZMod p)) :=
      Nat.card_mono (Set.toFinite _) (Set.inter_subset_inter_left _ (projFix_subset_permFix hz))
    have h2 := card_permFix_sumZero_mul_le (p := p) hz
    calc Nat.card (projFix p A ∩ {v | ∑ x, v x = 0} : Set (X → ZMod p)) * Nat.card A * p
        ≤ Nat.card (permFix p A ∩ {v | ∑ x, v x = 0} : Set (X → ZMod p)) * p * Nat.card A := by
          rw [mul_right_comm]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
      _ ≤ Nat.card (permFix p A) * Nat.card A := Nat.mul_le_mul_right _ h2
      _ < p ^ Fintype.card X := card_mul_card_lt_pow hp3 hA hne permFix_prop
  · push Not at hfix
    have h := card_projFix_mul_sq_le_of_noFix hp3 hX hA hexp hfix
    have h1 : Nat.card (projFix p A ∩ {v | ∑ x, v x = 0} : Set (X → ZMod p)) ≤
        Nat.card (projFix p A) := Nat.card_mono (Set.toFinite _) Set.inter_subset_left
    have : Nonempty (projFix p A) := ⟨⟨0, zero_mem_projFix⟩⟩
    have hpos : 0 < Nat.card (projFix p A) * Nat.card A := Nat.mul_pos Nat.card_pos Nat.card_pos
    calc Nat.card (projFix p A ∩ {v | ∑ x, v x = 0} : Set (X → ZMod p)) * Nat.card A * p
        ≤ Nat.card (projFix p A) * Nat.card A * p :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
      _ < Nat.card (projFix p A) * Nat.card A * p ^ 2 := by
          rw [pow_two, ← mul_assoc]
          exact lt_mul_of_one_lt_right (Nat.mul_pos hpos (by omega)) (by omega)
      _ ≤ p ^ Fintype.card X := h

end Bounds

end NoOffUO

end CFSG.StandardType
