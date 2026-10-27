module

public import CFSG.Timmesfeld.ARS.CaseOACells
public import CFSG.Timmesfeld.ARS.Sec12Transvection
public import CFSG.Timmesfeld.Transvection.Frame

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open Transvection

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseOADeg

structure DegOA (R : Set (Subgroup G)) (A A₀ : Subgroup G) (Δ₁ Δ₂ : Set (Subgroup G)) : Prop where
  set : CaseOASetting G R A A₀ Δ₁ Δ₂
  deg : ∀ X ∈ Δ₁, ∀ Y ∈ Δ₁, ¬ Special R X Y

theorem _root_.CFSG.Timmesfeld.ARS.Sec12.IsSubframe.comp_perm {A A₀ E C : Subgroup G}
    {P Q : Fin 3 → Subgroup G} (hfr : Sec12.IsSubframe R A A₀ E C P Q) (σ : Equiv.Perm (Fin 3)) :
    Sec12.IsSubframe R A A₀ E C (P ∘ σ) (Q ∘ σ) where
  memE := hfr.memE
  memC := hfr.memC
  special := hfr.special
  memQ i := hfr.memQ (σ i)
  memP i := hfr.memP (σ i)
  opposite i := hfr.opposite (σ i)
  commuting i j hij := hfr.commuting (σ i) (σ j) (σ.injective.ne hij)

namespace DegOA

variable {A A₀ : Subgroup G} {Δ₁ Δ₂ : Set (Subgroup G)} (hD : DegOA R A A₀ Δ₁ Δ₂)
include hD

theorem hyp : Hyp G R := hD.set.1

theorem mem : A ∈ R := hD.set.2.1

theorem coatom : IsCoatom (Subgroup.normalizer (A : Set G)) := hD.set.2.2.1

theorem ne : sigmaSet R A ≠ lambdaSet R A := hD.set.2.2.2.1

theorem max : IsSigmaMaximal R (centralGroup R A) := hD.set.2.2.2.2.1

theorem opp : A₀ ∈ omegaSet R A := hD.set.2.2.2.2.2.1

theorem card_comps : Nat.card (leviComps R A A₀) = 2 := hD.set.2.2.2.2.2.2.1

theorem comp₁ : Δ₁ ∈ leviComps R A A₀ := hD.set.2.2.2.2.2.2.2.1

theorem comp₂ : Δ₂ ∈ leviComps R A A₀ := hD.set.2.2.2.2.2.2.2.2.1

theorem comp_ne : Δ₁ ≠ Δ₂ := hD.set.2.2.2.2.2.2.2.2.2.1

theorem sl2 : IsSL2Comp Δ₂ := hD.set.2.2.2.2.2.2.2.2.2.2.2

theorem mem_leviSet₁ {X : Subgroup G} (hX : X ∈ Δ₁) : X ∈ leviSet R A A₀ :=
  Sec9.mem_leviSet_of_mem_leviComps hD.hyp hD.mem hD.ne hD.opp hD.comp₁ hX

theorem mem_leviSet₂ {X : Subgroup G} (hX : X ∈ Δ₂) : X ∈ leviSet R A A₀ :=
  Sec9.mem_leviSet_of_mem_leviComps hD.hyp hD.mem hD.ne hD.opp hD.comp₂ hX

theorem commuting_gen : Commuting (gen Δ₁) (gen Δ₂) :=
  Sec9.commuting_gen_of_ne hD.hyp hD.mem hD.ne hD.opp hD.comp₁ hD.comp₂ hD.comp_ne

theorem commuting_of_mem {X Y : Subgroup G} (hX : X ∈ Δ₁) (hY : Y ∈ Δ₂) : Commuting X Y :=
  hD.commuting_gen.mono (le_gen hX) (le_gen hY)

theorem mem_or_mem {X : Subgroup G} (hX : X ∈ leviSet R A A₀) : X ∈ Δ₁ ∨ X ∈ Δ₂ := by
  have := hD.hyp.finite
  rcases CaseOA.eq_or_eq_of_card_two hD.card_comps hD.comp₁ hD.comp₂ hD.comp_ne
    (Sec9.comp_mem_leviComps hX) with e | e
  · exact Or.inl (e ▸ Sec9.self_mem_comp A A₀ X)
  · exact Or.inr (e ▸ Sec9.self_mem_comp A A₀ X)

theorem subset_R₂ : Δ₂ ⊆ R := fun _ hX => (hD.mem_leviSet₂ hX).1.1

theorem opposite_of_mem₂ {X Y : Subgroup G} (hX : X ∈ Δ₂) (hY : Y ∈ Δ₂) (hXY : X ≠ Y) :
    Opposite X Y :=
  have := hD.hyp.finite
  (hD.sl2.opposite_of_ne hD.hyp.root hD.subset_R₂ hX hY hXY).1

theorem deg_leviSet : ∀ X ∈ leviSet R A A₀, ∀ Y ∈ leviSet R A A₀, ¬ Special R X Y := by
  have := hD.hyp.finite
  have hR := hD.hyp.root
  intro X hX Y hY hs
  rcases hD.mem_or_mem hX with hX₁ | hX₂ <;> rcases hD.mem_or_mem hY with hY₁ | hY₂
  · exact hD.deg X hX₁ Y hY₁ hs
  · exact hs.not_commuting hR (hD.commuting_of_mem hX₁ hY₂)
  · exact hs.not_commuting hR (hD.commuting_of_mem hY₁ hX₂).symm
  · by_cases hXY : X = Y
    · subst hXY
      exact hs.not_commuting hR (hR.commuting_self hX.1.1)
    · exact hs.not_opposite hR hX.1.1 (hD.opposite_of_mem₂ hX₂ hY₂ hXY)

theorem sec12 : Sec12 R A A₀ :=
  Sec12.of_caseM hD.hyp hD.mem hD.coatom hD.ne hD.max hD.opp hD.deg_leviSet

theorem mem₁_of_opposite {X Y : Subgroup G} (hX : X ∈ Δ₁) (hY : Y ∈ leviSet R A A₀)
    (hXY : Opposite X Y) : Y ∈ Δ₁ :=
  Sec9.mem_of_opposite hD.hyp hD.mem hD.ne hD.opp hD.comp₁ hX hY hXY

theorem mem₂_of_opposite {X Y : Subgroup G} (hX : X ∈ Δ₂) (hY : Y ∈ leviSet R A A₀)
    (hXY : Opposite X Y) : Y ∈ Δ₂ :=
  Sec9.mem_of_opposite hD.hyp hD.mem hD.ne hD.opp hD.comp₂ hX hY hXY

theorem exists_opposite₂ {X : Subgroup G} (hX : X ∈ Δ₂) : ∃ Y ∈ Δ₂, Opposite X Y := by
  obtain ⟨E, hE, F, hF, hEF, -⟩ := hD.sl2
  by_cases hXE : X = E
  · subst hXE
    exact ⟨F, hF, hEF⟩
  · exact ⟨E, hE, hD.opposite_of_mem₂ hX hE hXE⟩

theorem not_le_gen₁ {X : Subgroup G} (hX : X ∈ Δ₂) : ¬ X ≤ gen Δ₁ := by
  intro hle
  obtain ⟨Y, hY, hXY⟩ := hD.exists_opposite₂ hX
  exact hXY.not_commuting (hD.hyp.root.ne_bot _ (hD.subset_R₂ hX))
    (hD.commuting_gen.mono hle (le_gen hY))

theorem exists_subframe : ∃ E C : Subgroup G, ∃ P Q : Fin 3 → Subgroup G,
    Sec12.IsSubframe R A A₀ E C P Q ∧ (P 0 ∈ Δ₂ ∧ Q 0 ∈ Δ₂) ∧ (P 1 ∈ Δ₁ ∧ Q 1 ∈ Δ₁) ∧
      (P 2 ∈ Δ₁ ∧ Q 2 ∈ Δ₁) := by
  have := hD.hyp.finite
  have hR := hD.hyp.root
  obtain ⟨E, C, P, Q, hfr⟩ := hD.sec12.exists_isSubframe
  have hpair : ∀ i, (P i ∈ Δ₁ ∧ Q i ∈ Δ₁) ∨ (P i ∈ Δ₂ ∧ Q i ∈ Δ₂) := fun i => by
    rcases hD.mem_or_mem (hfr.memP i).1 with h | h
    · exact Or.inl ⟨h, hD.mem₁_of_opposite h (hfr.memQ i).1 (hfr.opposite i)⟩
    · exact Or.inr ⟨h, hD.mem₂_of_opposite h (hfr.memQ i).1 (hfr.opposite i)⟩
  have hone : ∀ i j, P i ∈ Δ₂ → P j ∈ Δ₂ → i = j := by
    intro i j hi hj
    by_contra hij
    have hc : Commuting (P i) (P j) := (hfr.commuting i j hij).mono le_sup_left le_sup_left
    by_cases he : P i = P j
    · have hc' : Commuting (P j) (Q j) := by
        rw [← he]
        exact (hfr.commuting i j hij).mono le_sup_left le_sup_right
      exact (hfr.opposite j).not_commuting (hR.ne_bot _ (hfr.memP j).1.1.1) hc'
    · exact (hD.opposite_of_mem₂ hi hj he).not_commuting (hR.ne_bot _ (hfr.memP i).1.1.1) hc
  obtain ⟨k, hk⟩ : ∃ k, P k ∈ Δ₂ ∧ Q k ∈ Δ₂ := by
    by_contra hno
    push Not at hno
    have h₁ : ∀ i, P i ∈ Δ₁ ∧ Q i ∈ Δ₁ := fun i =>
      (hpair i).resolve_right fun h => hno i h.1 h.2
    obtain ⟨X, hX, -, -, -, -⟩ := hD.sl2
    have hle := hD.sec12.le_sup_of_isSubframe hfr (hD.mem_leviSet₂ hX)
      (hD.commuting_of_mem (h₁ 0).1 hX).symm (hD.commuting_of_mem (h₁ 0).2 hX).symm
      (hD.commuting_of_mem (h₁ 1).1 hX).symm (hD.commuting_of_mem (h₁ 1).2 hX).symm
    exact hD.not_le_gen₁ hX (hle.trans (sup_le (le_gen (h₁ 2).1) (le_gen (h₁ 2).2)))
  have hother : ∀ i, i ≠ k → P i ∈ Δ₁ ∧ Q i ∈ Δ₁ := fun i hik =>
    (hpair i).resolve_right fun h => hik (hone i k h.1 hk.1)
  refine ⟨E, C, P ∘ Equiv.swap 0 k, Q ∘ Equiv.swap 0 k, hfr.comp_perm _, ?_, ?_, ?_⟩
  · simpa using hk
  · refine hother _ fun h => ?_
    have := (Equiv.swap 0 k).injective (h.trans (Equiv.swap_apply_left 0 k).symm)
    exact absurd this (by decide)
  · refine hother _ fun h => ?_
    have := (Equiv.swap 0 k).injective (h.trans (Equiv.swap_apply_left 0 k).symm)
    exact absurd this (by decide)

theorem isSmallFrame {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : Sec12.IsSubframe R A A₀ E C P Q) (h0 : P 0 ∈ Δ₂ ∧ Q 0 ∈ Δ₂)
    (h1 : P 1 ∈ Δ₁ ∧ Q 1 ∈ Δ₁) (h2 : P 2 ∈ Δ₁ ∧ Q 2 ∈ Δ₁) :
    IsSmallFrame Δ₁ ![P 1, P 2] ![Q 1, Q 2] 1 where
  memP i := by fin_cases i; exacts [h1.1, h2.1]
  memQ i := by fin_cases i; exacts [h1.2, h2.2]
  opposite i := by fin_cases i; exacts [hfr.opposite 1, hfr.opposite 2]
  commuting i j hij := by
    fin_cases i <;> fin_cases j <;> simp at hij
    · exact hfr.commuting 1 2 (by decide)
    · exact hfr.commuting 2 1 (by decide)
  residue X hX h := by
    have h0' := h 0 (by decide)
    exact hD.sec12.le_sup_of_isSubframe hfr (hD.mem_leviSet₁ hX)
      (hD.commuting_of_mem hX h0.1) (hD.commuting_of_mem hX h0.2) h0'.1 h0'.2

theorem center_gen_eq_bot : Subgroup.center ↥(gen Δ₁) = ⊥ := by
  have := hD.hyp.finite
  rw [eq_bot_iff]
  intro z hz
  have hzV : levi R A A₀ ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
    rw [CaseOA.levi_eq_sup hD.hyp hD.mem hD.ne hD.opp hD.card_comps hD.comp₁ hD.comp₂ hD.comp_ne]
    refine sup_le (fun v hv => Subgroup.mem_centralizer_singleton_iff.2 ?_)
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.2 ?_)
    · have := Subgroup.mem_center_iff.1 hz ⟨v, hv⟩
      exact congrArg Subtype.val this
    · exact (hD.commuting_gen _ z.2 v hv).symm.eq
  have hzl : (z : G) ∈ levi R A A₀ :=
    Sec9.gen_le_levi (fun _ hX => hD.mem_leviSet₁ hX) z.2
  have hc : (⟨z, hzl⟩ : levi R A A₀) ∈ Subgroup.center (levi R A A₀) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨v, hv⟩
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hzV hv))
  rw [hD.sec12.center_levi_eq_bot, Subgroup.mem_bot] at hc
  have hz1 : (z : G) = 1 := congrArg Subtype.val hc
  rw [Subgroup.mem_bot]
  exact Subtype.ext hz1

theorem meetsLines : MeetsLines Δ₁ := by
  have hR := hD.hyp.root
  intro X hX Y hY hXY hc W hW
  obtain ⟨Z, ⟨hZ, hZl⟩, hWZ⟩ := hD.sec12.meetsLines X (hD.mem_leviSet₁ hX) Y
    (hD.mem_leviSet₁ hY) hXY hc W (hD.mem_leviSet₁ hW)
  have hZ₁ : Z ∈ Δ₁ := by
    refine (hD.mem_or_mem hZ).resolve_right fun hZ₂ => ?_
    obtain ⟨T, hT, hZT⟩ := hD.exists_opposite₂ hZ₂
    exact hZT.not_commuting (hR.ne_bot _ (hD.subset_R₂ hZ₂)) (hZl T (hD.mem_leviSet₂ hT)
      (hD.commuting_of_mem hX hT).symm (hD.commuting_of_mem hY hT).symm).symm
  exact ⟨Z, ⟨hZ₁, fun T hT hTX hTY => hZl T (hD.mem_leviSet₁ hT) hTX hTY⟩, hWZ⟩

end DegOA

end CaseOADeg

end CFSG.Timmesfeld.ARS
