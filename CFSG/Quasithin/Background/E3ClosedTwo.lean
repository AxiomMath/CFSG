module

public import CFSG.Quasithin.Background.E3Bar
public import CFSG.GroupTheory.LocalCores.FittingNormal

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped commutatorElement

section ETwoCore

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem component_not_isSolvable {K : Subgroup Q} (hK : CFSG.IsComponent K) :
    ¬ Group.IsSolvable K := by
  intro hs
  have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect K := hK.1.1
  exact Group.IsPerfect.not_isSolvable K inferInstance

theorem exists_component_le_of_normal (hrad : CFSG.solvableRadical Q = ⊥) {N : Subgroup Q}
    [N.Normal] (hN : N ≠ ⊥) : ∃ K : Subgroup Q, CFSG.IsComponent K ∧ K ≤ N := by
  obtain ⟨M₀, ⟨hM₀n, hM₀1, hM₀N⟩, hM₀min⟩ := (Set.toFinite {M : Subgroup Q |
    M.Normal ∧ M ≠ ⊥ ∧ M ≤ N}).exists_minimal ⟨N, inferInstance, hN, le_rfl⟩
  have hmin : ∀ M : Subgroup Q, M.Normal → M ≤ M₀ → M = ⊥ ∨ M = M₀ := fun M hM hle =>
    (em (M = ⊥)).imp id fun hM1 =>
      le_antisymm hle (hM₀min ⟨hM, hM1, hle.trans hM₀N⟩ hle)
  have hF := CFSG.LocalCores.le_generalizedFitting_of_minimal hM₀n hM₀1 hmin
  have hFit : CFSG.fittingSubgroup Q = ⊥ := by
    refine le_bot_iff.1 (hrad ▸ A3.le_solvableRadical
      (CFSG.LocalCores.fitting_nilpotent (G := Q)).2.1 ?_)
    have := (CFSG.LocalCores.fitting_nilpotent (G := Q)).1
    infer_instance
  have hlayer : M₀ ≤ CFSG.layer Q := by
    have : M₀ ≤ CFSG.fittingSubgroup Q ⊔ CFSG.layer Q := hF
    rwa [hFit, bot_sup_eq] at this
  by_contra hno
  push Not at hno
  have hcomm : ∀ K : Subgroup Q, CFSG.IsComponent K → ⁅K, M₀⁆ = ⊥ := fun K hK =>
    (CFSG.LocalCores.component_normal_subgroup hK hM₀n).resolve_left fun h =>
      hno K hK (h.trans hM₀N)
  have hlc : CFSG.layer Q ≤ Subgroup.centralizer (M₀ : Set Q) :=
    sSup_le fun K hK => Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm K hK)
  have hab : ∀ a ∈ M₀, ∀ b ∈ M₀, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 (hlc (hlayer ha)) b hb).symm
  have hsolv : Group.IsSolvable M₀ :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (hab a a.2 b b.2)
  exact hM₀1 (le_bot_iff.1 (hrad ▸ A3.le_solvableRadical hM₀n hsolv))

theorem pCore_two_le_solvableRadical : CFSG.Open.pCore 2 Q ≤ CFSG.solvableRadical Q :=
  A3.le_solvableRadical inferInstance
    (E1.isSolvable_of_isPGroup_two (CFSG.LieType.BorelTits.pCore_isPGroup 2))

theorem eTwo_core {S B : Subgroup Q} (hE : E1.ETwo Q S B) {N : Subgroup Q} [N.Normal]
    (hNB : IsPGroup 2 ↥⁅B, N⁆) : N ≤ CFSG.solvableRadical Q := by
  obtain ⟨-, -, -, L, hL, hlayer, hcase⟩ := hE
  by_contra hN
  set R := CFSG.solvableRadical Q with hR
  set π := QuotientGroup.mk' R with hπ
  have hrad : CFSG.solvableRadical (Q ⧸ R) = ⊥ := A3.solvableRadical_quotient_eq_bot Q
  set Nb := N.map π with hNb
  have hNbn : Nb.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective R)
  have hNb1 : Nb ≠ ⊥ := by
    intro h
    apply hN
    rw [hNb, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  obtain ⟨K, hK, hKN⟩ := exists_component_le_of_normal hrad hNb1
  set Bb := E1.barRad Q B with hBb
  have hBbN : IsPGroup 2 ↥⁅Bb, Nb⁆ := by
    have : ⁅Bb, Nb⁆ = (⁅B, N⁆).map π := by
      rw [hBb, hNb, E1.barRad, Subgroup.map_commutator]
    rw [this]
    exact hNB.map π
  have hKB : ⁅K, Bb⁆ = ⊥ := by
    have hKc : K ∈ cComp (⊤ : Subgroup (Q ⧸ R)) := mem_cComp_top_of_isComponent hK
    rcases cComp_commutator_dichotomy hKc Bb with ⟨h1, -⟩ | h2
    · exact le_bot_iff.1 (hrad ▸ h1)
    · exfalso
      have h3 : K ≤ ⁅K, Bb⁆ := by
        rw [h2]
        exact le_conjClosure K Bb
      have h4 : ⁅K, Bb⁆ ≤ ⁅Bb, Nb⁆ := by
        rw [Subgroup.commutator_comm K Bb]
        exact Subgroup.commutator_mono le_rfl hKN
      have h5 : IsPGroup 2 ↥K := hBbN.to_le (h3.trans h4)
      exact component_not_isSolvable hK (by have := h5.isNilpotent; infer_instance)
  have hKL : ∃ t ∈ (E1.tauOf ⊤ S B).map π, K = A1b.conjSub t L := by
    by_contra hno
    push Not at hno
    have hle : CFSG.layer (Q ⧸ R) ≤ Subgroup.centralizer (K : Set (Q ⧸ R)) := by
      rw [hlayer]
      refine iSup₂_le fun t ht => ?_
      have hcL : CFSG.IsComponent (A1b.conjSub t L) :=
        CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hL
      have := (CFSG.LocalCores.distinct_components_commute hK hcL).resolve_left (hno t ht)
      rw [Subgroup.commutator_comm] at this
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 this
    have hKc : K ≤ Subgroup.centralizer (K : Set (Q ⧸ R)) :=
      (CFSG.LocalCores.component_le_layer hK).trans hle
    have hab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.1 (hKc ha) b hb).symm
    exact component_not_isSolvable hK
      (Group.isSolvable_of_comm fun a b => Subtype.ext (hab a a.2 b b.2))
  obtain ⟨t, ht, hKt⟩ := hKL
  have htB : ∀ b ∈ Bb, t * b = b * t := by
    obtain ⟨s, hs, rfl⟩ := ht
    rintro _ ⟨a, ha, rfl⟩
    have h1 : ⁅s, a⁆ ∈ CFSG.Open.pCore 2 Q := by
      have := (E1.mem_tauOf.1 hs).2.2 a ha
      rwa [E1.pCoreOf_top_eq] at this
    have h3 : π ⁅s, a⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (pCore_two_le_solvableRadical h1)
    rw [map_commutatorElement] at h3
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  have hLB : ∀ x ∈ L, ∀ b ∈ Bb, x * b = b * x := by
    intro x hx b hb
    have hxK : t * x * t⁻¹ ∈ K := by
      rw [hKt, A1b.mem_conjSub_iff]
      have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
      rw [e]
      exact hx
    have h1 : ⁅t * x * t⁻¹, b⁆ = 1 :=
      Subgroup.mem_bot.1 (hKB ▸ Subgroup.commutator_mem_commutator hxK hb)
    have h2 := commutatorElement_eq_one_iff_mul_comm.1 h1
    have h3 := htB b hb
    have e1 : t⁻¹ * b * t = b := by rw [mul_assoc, ← h3, inv_mul_cancel_left]
    calc x * b = t⁻¹ * ((t * x * t⁻¹) * b) * t := by
          have : t⁻¹ * ((t * x * t⁻¹) * b) * t = x * (t⁻¹ * b * t) := by group
          rw [this, e1]
      _ = t⁻¹ * (b * (t * x * t⁻¹)) * t := by rw [h2]
      _ = b * x := by
          have : t⁻¹ * (b * (t * x * t⁻¹)) * t = (t⁻¹ * b * t) * x := by group
          rw [this, e1]
  have hL1 : L ≠ ⊥ := by
    have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    exact (Subgroup.nontrivial_iff_ne_bot L).1 this
  rcases hcase with h1 | ⟨h2, -⟩
  · apply hL1
    have : ⁅L, Bb⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx b hb
      exact Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_mul_comm.2 (hLB x hx b hb))
    exact h1.trans this
  · apply h2
    intro b hb
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun x hx => hLB x hx b hb)

omit [Finite Q] in
theorem eTwo_not_le_radical {S B : Subgroup Q} (hE : E1.ETwo Q S B) :
    ¬ B ≤ CFSG.solvableRadical Q := by
  obtain ⟨-, -, -, L, hL, -, hcase⟩ := hE
  intro hB
  have hBb : E1.barRad Q B = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨a, ha, rfl⟩
    exact (QuotientGroup.eq_one_iff a).2 (hB ha)
  have hL1 : L ≠ ⊥ := by
    have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    exact (Subgroup.nontrivial_iff_ne_bot L).1 this
  rcases hcase with h1 | ⟨h2, -⟩
  · apply hL1
    rw [h1, hBb, Subgroup.commutator_bot_right]
  · exact h2 (by rw [hBb]; exact bot_le)

theorem eTwo_closed {S B : Subgroup Q} (hE : E1.ETwo Q S B) {N : Subgroup Q} [N.Normal]
    (hNB : IsPGroup 2 ↥⁅B, N⁆) :
    IsSylowIn 2 (CFSG.Open.pCore 2 Q ⊓ N) N ∧ ¬ B ≤ N := by
  have hNR : N ≤ CFSG.solvableRadical Q := eTwo_core hE hNB
  refine ⟨?_, fun hBN => eTwo_not_le_radical hE (hBN.trans hNR)⟩
  have h2c : E1.IsTwoClosed (CFSG.solvableRadical Q) := hE.1
  obtain ⟨P₀, hP₀, hP₀n⟩ := h2c
  have hS : IsSylowIn 2 (P₀ ⊓ N) N :=
    hP₀.inf_normal hNR (Subgroup.Normal.subgroupOf inferInstance _)
  have hO2 : CFSG.Open.pCore 2 Q ≤ P₀ :=
    E1.le_of_isSylowIn_of_normal hP₀ hP₀n pCore_two_le_solvableRadical
      (CFSG.LieType.BorelTits.pCore_isPGroup 2)
  have h12 : P₀ ⊓ N ≤ CFSG.Open.pCore 2 Q := by
    have hX2 : IsPGroup 2 ↥(P₀ ⊓ N) := hP₀.isPGroup.to_le inf_le_left
    have h := inf_solvableRadical_eq_inf_pCore ⟨P₀, hP₀, hP₀n⟩ hX2
    intro x hx
    have hxR : x ∈ CFSG.solvableRadical Q ⊓ (P₀ ⊓ N) := ⟨hNR (Subgroup.mem_inf.1 hx).2, hx⟩
    rw [h] at hxR
    exact hxR.1
  have e : CFSG.Open.pCore 2 Q ⊓ N = P₀ ⊓ N :=
    le_antisymm (inf_le_inf_right _ hO2) (le_inf h12 inf_le_right)
  rw [e]
  exact hS

end ETwoCore

end E3

end CFSG.Quasithin
