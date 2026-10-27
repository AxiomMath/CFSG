module

public import CFSG.Sporadic.Recognition.HeMultiplierTables
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs

public section

namespace CFSG.Sporadic.Recognition.HeMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Open CFSG.Sporadic.He Subgroup

theorem card_le_of_shortCheck_nil {m : ℕ} (ws : List (List (Fin m × Bool))) {k cap n : ℕ}
    (h : subsetCheckShortCC ws [] k cap n = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n := by
  have hS : subsetOf m [] = [] := by simp [subsetOf]
  have : Finite (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) := by
    rw [hS]; exact (inferInstance : Finite (PG 0 _))
  have hc : Nat.card (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) = 1 := by
    rw [hS]; exact card_PG_zero _
  have := card_le_of_subsetCheckShortCC ws [] h
  rwa [hc, mul_one] at this

theorem card_presentedGroup_le {c₃ c₂ c₁ : ℕ}
    (h₃ : subsetCheckCC heRels [0, 1, 2] c₃ 4116 = true)
    (h₂ : subsetCheckCC heRels3 [0, 1] c₂ 240 = true)
    (h₁ : subsetCheckCC heRels2 [] c₁ 4080 = true) :
    Finite (PG 4 heRels) ∧ Nat.card (PG 4 heRels) ≤ 4030387200 := by
  obtain ⟨f1, c1⟩ := card_le_of_subsetCheckCC_nil _ h₁
  obtain ⟨f2, c2⟩ := card_le_of_subsetCheckCC heRels3 [0, 1] h₂
  obtain ⟨f3, c3⟩ := card_le_of_subsetCheckCC heRels [0, 1, 2] h₃
  refine ⟨f3, ?_⟩
  have := c3.trans <| Nat.mul_le_mul_left _ <| c2.trans <| Nat.mul_le_mul_left _ c1
  exact this.trans (by norm_num)

theorem card_presentedCover_le {k c₃ c₂ c₁ : ℕ}
    (h₃ : subsetCheckShortCC heCover [0, 1, 2] k c₃ 4116 = true)
    (h₂ : subsetCheckShortCC heCover3 [0, 1] k c₂ 240 = true)
    (h₁ : subsetCheckShortCC heCover2 [] k c₁ 4080 = true) :
    Finite (PresentedCover (wordSet heRels) fun i => FreeGroup.mk (heCommWord i)) ∧
      Nat.card (PresentedCover (wordSet heRels) fun i => FreeGroup.mk (heCommWord i)) ≤
        4030387200 := by
  change Finite (PresentedGroup (coverRelators (wordSet heRels)
      fun i => FreeGroup.mk (heCommWord i))) ∧
    Nat.card (PresentedGroup (coverRelators (wordSet heRels)
      fun i => FreeGroup.mk (heCommWord i))) ≤ 4030387200
  rw [coverRelators_wordSet]
  obtain ⟨f1, c1⟩ := card_le_of_shortCheck_nil _ h₁
  obtain ⟨f2, c2⟩ := card_le_of_subsetCheckShortCC heCover3 [0, 1] h₂
  obtain ⟨f3, c3⟩ := card_le_of_subsetCheckShortCC heCover [0, 1, 2] h₃
  refine ⟨f3, ?_⟩
  have := c3.trans <| Nat.mul_le_mul_left _ <| c2.trans <| Nat.mul_le_mul_left _ c1
  exact this.trans (by norm_num)

theorem isPresentation_heGen (hTab : heTabCheck = true)
    {c₃ c₂ c₁ : ℕ} (h₃ : subsetCheckCC heRels [0, 1, 2] c₃ 4116 = true)
    (h₂ : subsetCheckCC heRels3 [0, 1] c₂ 240 = true)
    (h₁ : subsetCheckCC heRels2 [] c₁ 4080 = true) :
    IsPresentation heGen (wordSet heRels) := by
  obtain ⟨hfin, hle⟩ := card_presentedGroup_le h₃ h₂ h₁
  have : Finite (PresentedGroup (wordSet heRels)) := hfin
  exact IsPresentation.of_card_le (lift_heGen_rels hTab) (closure_heGen hTab) (by
    rw [card_J]; exact hle)

theorem card_griessHopfMultiplier_of_mulEquiv {Y : Type} [Group Y]
    (e : Y ≃* J) (hTab : heTabCheck = true)
    {c₃ c₂ c₁ c₃' c₂' c₁' k : ℕ} (h₃ : subsetCheckCC heRels [0, 1, 2] c₃ 4116 = true)
    (h₂ : subsetCheckCC heRels3 [0, 1] c₂ 240 = true)
    (h₁ : subsetCheckCC heRels2 [] c₁ 4080 = true)
    (g₃ : subsetCheckShortCC heCover [0, 1, 2] k c₃' 4116 = true)
    (g₂ : subsetCheckShortCC heCover3 [0, 1] k c₂' 240 = true)
    (g₁ : subsetCheckShortCC heCover2 [] k c₁' 4080 = true) :
    Nat.card (griessHopfMultiplier Y) = 1 := by
  have hP : IsPresentation (fun i => e.symm (heGen i)) (wordSet heRels) :=
    (isPresentation_heGen hTab h₃ h₂ h₁).mulEquiv e.symm
  have hw : ∀ i, FreeGroup.mk (heCommWord i) ∈ commutator (FreeGroup (Fin 4)) :=
    fun i => mk_commWords_mem_commutator _
  have hwg : ∀ i, FreeGroup.lift (fun i => e.symm (heGen i))
      (FreeGroup.mk (heCommWord i)) = e.symm (heGen i) := fun i => by
    rw [lift_mulEquiv, lift_heCommWord hTab]
  obtain ⟨hfin, hle⟩ := card_presentedCover_le g₃ g₂ g₁
  have hc := card_presentedCover hP hw hwg
  rw [Nat.card_congr e.toEquiv, card_J] at hc
  have hpos : 0 < Nat.card (PresentedCover (wordSet heRels) fun i => FreeGroup.mk (heCommWord i)) :=
    Nat.card_pos
  rw [hc] at hpos hle
  have h1 : 0 < Nat.card (griessHopfMultiplier Y) := Nat.pos_of_mul_pos_left hpos
  have h2 : Nat.card (griessHopfMultiplier Y) ≤ 1 := by
    by_contra hcon
    have : 4030387200 * 2 ≤ 4030387200 * Nat.card (griessHopfMultiplier Y) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  omega

theorem card_griessHopfMultiplier_J (hTab : heTabCheck = true)
    {c₃ c₂ c₁ c₃' c₂' c₁' k : ℕ} (h₃ : subsetCheckCC heRels [0, 1, 2] c₃ 4116 = true)
    (h₂ : subsetCheckCC heRels3 [0, 1] c₂ 240 = true)
    (h₁ : subsetCheckCC heRels2 [] c₁ 4080 = true)
    (g₃ : subsetCheckShortCC heCover [0, 1, 2] k c₃' 4116 = true)
    (g₂ : subsetCheckShortCC heCover3 [0, 1] k c₂' 240 = true)
    (g₁ : subsetCheckShortCC heCover2 [] k c₁' 4080 = true) :
    Nat.card (griessHopfMultiplier J) = 1 :=
  card_griessHopfMultiplier_of_mulEquiv (MulEquiv.refl J) hTab h₃ h₂ h₁ g₃ g₂ g₁

theorem card_griessHopfMultiplier_He (hTab : heTabCheck = true)
    {c₃ c₂ c₁ c₃' c₂' c₁' k : ℕ} (h₃ : subsetCheckCC heRels [0, 1, 2] c₃ 4116 = true)
    (h₂ : subsetCheckCC heRels3 [0, 1] c₂ 240 = true)
    (h₁ : subsetCheckCC heRels2 [] c₁ 4080 = true)
    (g₃ : subsetCheckShortCC heCover [0, 1, 2] k c₃' 4116 = true)
    (g₂ : subsetCheckShortCC heCover3 [0, 1] k c₂' 240 = true)
    (g₁ : subsetCheckShortCC heCover2 [] k c₁' 4080 = true) :
    Nat.card (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.He) = 1 :=
  card_griessHopfMultiplier_of_mulEquiv heEquivJ hTab h₃ h₂ h₁ g₃ g₂ g₁

theorem card_center_dvd_griess {S Q : Type} [Group S] [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* S) :
    Nat.card (Subgroup.center Q) ∣ Nat.card (griessHopfMultiplier S) := by
  have := hQ
  let q : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker.le
  rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv, ← hker,
    ← hmap]
  exact Subgroup.card_map_dvd (H := CFSG.RankThree.PerfectCover.hopfMultiplier S)
    (CFSG.RankThree.PerfectCover.hopfLift q hq hker.le)

theorem heldTrivialMultiplier_holds (hTab : heTabCheck = true)
    (h₃ : subsetCheckCC heRels [0, 1, 2] 3000000 4116 = true)
    (h₂ : subsetCheckCC heRels3 [0, 1] 100000 240 = true)
    (h₁ : subsetCheckCC heRels2 [] 100000 4080 = true)
    (g₃ : subsetCheckShortCC heCover [0, 1, 2] 20 12500000 4116 = true)
    (g₂ : subsetCheckShortCC heCover3 [0, 1] 20 400000 240 = true)
    (g₁ : subsetCheckShortCC heCover2 [] 20 100000 4080 = true) :
    CFSG.ComponentClassification.TBLit.HeldTrivialMultiplier := by
  intro Q _ _ hq he
  obtain ⟨e⟩ := he
  have e' : Q ⧸ Subgroup.center Q ≃* J := e.trans heEquivJ
  have hdvd : Nat.card (Subgroup.center Q) ∣ Nat.card (griessHopfMultiplier J) :=
    card_center_dvd_griess (S := J) hq.1 e'
  rw [card_griessHopfMultiplier_J hTab h₃ h₂ h₁ g₃ g₂ g₁, Nat.dvd_one] at hdvd
  exact Subgroup.eq_bot_of_card_eq _ hdvd

end CFSG.Sporadic.Recognition.HeMultiplier
