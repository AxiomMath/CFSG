module

public import CFSG.Timmesfeld.Transvection.TriangleCrux

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

section

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

namespace TriangleSetting

section

variable {A E B : Subgroup G} {t : G}

theorem exists_mem_lineOf_commuting [Finite G] (S : TriangleSetting Δ A E B t)
    (htY : t ∈ A ⊔ E ⊔ B) (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ) :
    ∃ D ∈ lineOf Δ A B, Commuting D E := by
  classical
  have hΔ := S.cls
  have hEne : E ≠ ⊥ := hΔ.root.ne_bot E S.tri.memE
  obtain ⟨e₀, he₀, he₀1⟩ := hΔ.root.exists_ne_one S.tri.memE
  have hsN : partnerElt A E B e₀ ∈ corrN A E t :=
    corrM_le_corrN (S.partnerElt_mem_corrM he₀ he₀1)
  have hss : partnerElt A E B e₀ * partnerElt A E B e₀ = 1 := S.partnerElt_mul_self he₀ he₀1
  have hsL : conjSub (corrL A E t) (partnerElt A E B e₀) = corrL A E t :=
    S.conjSub_corrL_of_mem_corrN (S.fourTerm htY hq) hq hsN
  let σ : {C : Subgroup G // C ∈ Δ ∧ C ≤ corrL A E t} →
      {C : Subgroup G // C ∈ Δ ∧ C ≤ corrL A E t} := fun C =>
    ⟨conjSub C.1 (partnerElt A E B e₀), hΔ.root.conjSub_mem C.2.1 _,
      (Subgroup.map_mono C.2.2).trans hsL.le⟩
  have hσ : ∀ C, σ (σ C) = C := fun C => Subtype.ext (by
    show conjSub (conjSub C.1 (partnerElt A E B e₀)) (partnerElt A E B e₀) = C.1
    rw [← conjSub_mul, hss, conjSub_one])
  have hfixCE : ∀ C, σ C = C → Commuting C.1 E := by
    intro C hC
    have hCs : conjSub C.1 (partnerElt A E B e₀) = C.1 := congrArg Subtype.val hC
    have hCA : Commuting C.1 A := S.commuting_of_le_corrL htY hq C.2.2 le_corrL
    have hCB : Commuting C.1 B := S.commuting_of_le_corrL htY hq C.2.2 S.le_corrL_right
    have hne : C.1 ≠ E := fun h => S.tri.oppA.not_commuting hEne (h ▸ hCA)
    rcases hΔ.commuting_or_opposite C.2.1 S.tri.memE hne with h | h
    · exact h
    · exact absurd hCs (S.conjSub_partnerElt_ne he₀ he₀1 C.2.1 hCA hCB h.symm)
  have hpar := card_fixedPoints_modEq_two σ hσ
  obtain ⟨C, hC⟩ : (Function.fixedPoints σ).Nonempty := by
    by_contra hne
    have hfix0 : Nat.card (Function.fixedPoints σ) = 0 := by
      rw [Nat.card_eq_zero]
      left
      constructor
      rintro ⟨C, hC⟩
      exact hne ⟨C, hC⟩
    rw [hfix0] at hpar
    exact absurd ((S.card_members_corrL_modEq htY hq hpts).symm.trans hpar) (by decide)
  exact ⟨C.1, S.mem_lineOf_of_le_corrL htY hq hpts C.2.1 C.2.2, hfixCE C hC⟩

end

end TriangleSetting

theorem meetsLines_of_four_le [Finite G] (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ)
    (hrank : ∃ A ∈ Δ, ∃ B ∈ Δ, A ≠ B ∧ Commuting A B) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) :
    MeetsLines Δ := by
  intro A hA B hB hAB hcomm C hC
  by_cases hCA : Commuting C A
  · exact ⟨A, left_mem_lineOf hA, hCA⟩
  by_cases hCB : Commuting C B
  · exact ⟨B, right_mem_lineOf hB, hCB⟩
  have hCAne : C ≠ A := fun h => hCA (by rw [h]; exact hΔ.root.commuting_self hA)
  have hCBne : C ≠ B := fun h => hCB (by rw [h]; exact hΔ.root.commuting_self hB)
  have hoppA : Opposite C A := by
    rcases hΔ.commuting_or_opposite hC hA hCAne with h | h
    · exact absurd h hCA
    · exact h
  have hoppB : Opposite C B := by
    rcases hΔ.commuting_or_opposite hC hB hCBne with h | h
    · exact absurd h hCB
    · exact h
  have hT : IsTriangle Δ A C B := ⟨hA, hC, hB, hAB, hcomm, hoppA, hoppB⟩
  obtain ⟨t, htY, S⟩ := exists_triangleSetting hΔ (hΔ.noIsolated hpts hrank) hT
  obtain ⟨D, hD, hDC⟩ :=
    TriangleSetting.exists_mem_lineOf_commuting S htY (hq A hA) hpts
  exact ⟨D, hD, hDC.symm⟩

end

namespace TransvectionHyp

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)}

theorem meetsLines (h : TransvectionHyp H Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) :
    MeetsLines Δ := by
  haveI := h.finite
  exact meetsLines_of_four_le h.cls h.points h.rank hq

end TransvectionHyp

end CFSG.Timmesfeld.Transvection
