module

public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item148Solvable

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem type148_of_mulEquiv {X X' : Type} [Group X] [Group X'] (φ : X ≃* X')
    (h : Type148 X') : Type148 X := by
  rcases h with ⟨p, f, hp, hf, hcase⟩ | ⟨p, f, hp, hp3, hf, hL⟩ | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩ |
      ⟨⟨ψ⟩⟩
  · refine Or.inl ⟨p, f, hp, hf, ?_⟩
    rcases hcase with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
    · exact Or.inl ⟨hq, ⟨φ.trans ψ⟩⟩
    · exact Or.inr ⟨hq, ⟨φ.trans ψ⟩⟩
  · refine Or.inr (Or.inl ⟨p, f, hp, hp3, hf, ?_⟩)
    rcases hL with ⟨⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
    · exact Or.inl ⟨φ.trans ψ⟩
    · exact Or.inr ⟨hq, ⟨φ.trans ψ⟩⟩
  · exact Or.inr (Or.inr (Or.inl ⟨φ.trans ψ⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨φ.trans ψ⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨φ.trans ψ⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨φ.trans ψ⟩))))

theorem ne_three_of_isoLThreePi {X : Type} [Group X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h : Sec4.IsoLThreePi X p e) : p ≠ 3 := by
  rintro rfl
  have h0 : 3 ^ e % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
  rcases h with ⟨hq, -⟩ | ⟨hq, -⟩ <;> omega

theorem type148_of_kType148 {A Y : Subgroup G} [(ker148 A Y).Normal] (hch : Chosen136 A)
    {e : G} {K Le : Subgroup G} (hkt : KType148 A Y e K Le) : Type148 ↥(img148 A Y K) := by
  rcases hkt.2 with ⟨he, hLe, hφ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, he', hiso, hL3⟩⟩ |
      ⟨-, ⟨⟨φ⟩⟩ | ⟨hp7, ⟨φ⟩⟩⟩
  · obtain ⟨φ⟩ := hφ
    refine type148_of_mulEquiv φ ?_
    rcases (hch.2 e he Le hLe).1 with hJ | hL | hA7 | hM22 | hM12
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ))))
    · exact Or.inl hL
    · exact Or.inr (Or.inr (Or.inl hA7))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM22))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hM12)))
  · exact Or.inr (Or.inr (Or.inl ⟨φ⟩))
  · exact Or.inr (Or.inl ⟨p, f, hp, ne_three_of_isoLThreePi (Nat.mul_pos hf he') hiso, hf, hL3⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨φ⟩))
  · exact Or.inr (Or.inl ⟨7, 1, hp7, by norm_num, le_rfl, Or.inl ⟨φ⟩⟩)

omit [Finite G] in
theorem le_normalizer_of_eq_deltaZero {A K : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hK : K = deltaZero A LB K) : A ≤ Subgroup.normalizer (K : Set G) := by
  have h1 : A ≤ Subgroup.normalizer ((deltaZero A LB K : Subgroup G) : Set G) :=
    le_normalizer_sSup fun Q hQ => hQ.1.1.1.2.2
  rwa [← hK] at h1

theorem case148One_of_core (hCore : Step148Core) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A) (hs : ¬ Group.IsSolvable ↥Y)
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B')
    (hcore : ∀ B : Subgroup G, IsHyperplane A B → ∀ Q ∈ scriptQZero A (lB A),
      Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))) :
    Case148One A (lB A) Y := by
  show deltaZero A (lB A) Y ≤ pPrimeCoreOf 3 Y
  rw [deltaZero_eq_iSup h.isE27 Y]
  refine iSup₂_le fun B hB => sSup_le fun Q hQ => ?_
  exact hCore G A c L h Y hY hs hYB B hB Q hQ.1 hQ.2 (hcore B hB Q hQ.1 hQ.2)

omit [Finite G] in
theorem normal_of_case148One {A Y : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h1 : Case148One A LB Y) :
    (((deltaZero A LB Y).subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal := by
  have hle : (deltaZero A LB Y).subgroupOf Y ≤ CFSG.pPrimeCore 3 ↥Y := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := h1 (Subgroup.mem_subgroupOf.mp hx)
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  have hbot : ((deltaZero A LB Y).subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hle
  rw [hbot]
  infer_instance

theorem item148Normal_of_item148
    {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} (h148 : Item148 A LB) : Item148Normal A LB :=
  fun Y hY => (h148 Y hY).1

section Assembly


theorem item148Cases_of_steps_of_yBOne (hCore : Step148Core) (hPoint : Step148Point)
    (hKT : Step148KType) (hLift : Step148Lift) (hD4 : Step148D4) (hOne : Step148One)
    (hRank : Step148Rank) (hPGL : Step148PGL) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A) (hs : ¬ Group.IsSolvable ↥Y)
    (ih : Ind148 A (lB A) Y) (hYB1 : ∀ B : Subgroup G, IsHyperplane A B → YBOne A (lB A) Y B) :
    letI := ker148_normal hY.2
    Item148Cases A (lB A) Y := by
  let := ker148_normal hY.2
  by_cases hcore : ∀ B : Subgroup G, IsHyperplane A B → ∀ Q ∈ scriptQZero A (lB A),
      Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))
  · exact Or.inl (case148One_of_core hCore h hY hs hYB1 hcore)
  push Not at hcore
  obtain ⟨B, hB, Q, hQ, hQY, b, hb, hb1, hQb⟩ := hcore
  obtain ⟨e, K, Le, hP⟩ := hPoint G A c L h Y hY hs hYB1 B hB Q hQ hQY b hb hb1 hQb
  have hkt : KType148 A Y e K Le := hKT G A c L h Y hY hs hYB1 B Q e K Le hP
  have heA : e ∈ A := hB.1 hP.2.2.2.1
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) :=
    hP.2.2.2.2.2.1
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  obtain ⟨J, hJ, hKJ, hAJ, halt⟩ := hLift G A c L h Y hY hs e heA he1 K hK
    (le_normalizer_of_eq_deltaZero hKΔ) hkt.1 (type148_of_kType148 h.chosen136 hkt)
  have halt' : Lift148Eq A Y K J ∨ Lift148Ten A Y K J ∨ Lift148Field A Y e heA K J := by
    rcases halt with h1 | h2 | h3 | h4
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)
    · exact (hD4 G A c L h Y hY hs hYB1 B Q e K Le hP hkt heA J hJ hKJ hAJ h4).elim
  rcases hOne G A c L h Y hY hs hYB1 B Q e K Le hP hkt heA J hJ hKJ hAJ halt' with hA | hPGLc
  · rcases hRank G A c L h Y hY hs ih hYB1 B Q e K Le hP hkt heA J hJ hKJ hAJ halt' hA with
      h2 | h3 | h4 | h5
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  · rcases hPGL G A c L h Y hY hs ih hYB1 B Q e K Le hP hkt heA J hJ hKJ hAJ halt' hPGLc with
      h2 | h7
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h7)))))

theorem item148Cases_of_steps (hYB : Step148YB) (hHJ : Step148HJ) (hCore : Step148Core)
    (hPoint : Step148Point) (hKT : Step148KType) (hLift : Step148Lift) (hD4 : Step148D4)
    (hOne : Step148One) (hRank : Step148Rank) (hPGL : Step148PGL)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A) (ih : Ind148 A (lB A) Y) :
    letI := ker148_normal hY.2
    Item148Cases A (lB A) Y := by
  let := ker148_normal hY.2
  by_cases hs : Group.IsSolvable ↥Y
  · exact Or.inl (item148Solvable_of_mem_partTwoF h.mem_partTwoF Y hY hs)
  by_cases hHJb : ∃ B, IsHyperplane A B ∧ ¬ YBOne A (lB A) Y B
  · obtain ⟨B, hB, hnot⟩ := hHJb
    obtain ⟨YB, hYB', htype, hle, b, d, Lb, hconf, hYBle⟩ := hYB G A c L h Y hY hs B hB hnot
    rcases hHJ G A c L h Y hY hs ih B hB hnot YB hYB' htype hle b d Lb hconf hYBle with
      h2 | h3 | h6
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
  push Not at hHJb
  exact item148Cases_of_steps_of_yBOne hCore hPoint hKT hLift hD4 hOne hRank hPGL h hY hs ih
    hHJb

theorem rank3II_14_8_of_cases (hN : Step148Normal) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L)
    (hcases : ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y →
      letI := ker148_normal hY.2
      Item148Cases A (lB A) Y) :
    Item148 A (lB A) := by
  rw [item148_iff]
  suffices key : ∀ n : ℕ, ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), Nat.card Y = n →
      Item148At A (lB A) Y hY from fun Y hY => key _ Y hY rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro Y hY hn
    have ih : Ind148 A (lB A) Y := fun Y' hY' hlt => ihn _ (hn ▸ hlt) Y' hY' rfl
    by_cases hs : Group.IsSolvable ↥Y
    · have h1 : Case148One A (lB A) Y := item148Solvable_of_mem_partTwoF h.mem_partTwoF Y hY hs
      exact And.intro (normal_of_case148One h1) (Or.inl h1)
    have hc := hcases Y hY hs ih
    refine And.intro ?_ hc
    by_cases h1 : Case148One A (lB A) Y
    · exact normal_of_case148One h1
    · exact hN G A c L h Y hY hs ih hc h1

theorem rank3II_14_8_of_steps (hN : Step148Normal) (hYB : Step148YB) (hHJ : Step148HJ)
    (hCore : Step148Core) (hPoint : Step148Point) (hKT : Step148KType) (hLift : Step148Lift)
    (hD4 : Step148D4) (hOne : Step148One) (hRank : Step148Rank) (hPGL : Step148PGL)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) : Item148 A (lB A) :=
  rank3II_14_8_of_cases hN h fun _ hY _ ih =>
    item148Cases_of_steps hYB hHJ hCore hPoint hKT hLift hD4 hOne hRank hPGL h hY ih

theorem item148S14_of_steps (hN : Step148Normal) (hYB : Step148YB) (hHJ : Step148HJ)
    (hCore : Step148Core) (hPoint : Step148Point) (hKT : Step148KType) (hLift : Step148Lift)
    (hD4 : Step148D4) (hOne : Step148One) (hRank : Step148Rank) (hPGL : Step148PGL) :
    Item148S14 := fun _ _ _ _ _ _ h =>
  rank3II_14_8_of_steps hN hYB hHJ hCore hPoint hKT hLift hD4 hOne hRank hPGL h

theorem item148NormalS14_of_item148S14 (h148 : Item148S14) : Item148NormalS14 :=
  fun G _ _ A c L h => item148Normal_of_item148 (h148 G A c L h)

end Assembly

end CFSG.RankThree.PartTwo.Sec14
