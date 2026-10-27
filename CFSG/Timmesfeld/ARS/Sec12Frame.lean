module

public import CFSG.Timmesfeld.ARS.Sec12Lines

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec12

structure IsSubframe (R : Set (Subgroup G)) (A A₀ E C : Subgroup G)
    (P Q : Fin 3 → Subgroup G) : Prop where
  memE : E ∈ lambdaStar R A A₀
  memC : C ∈ lambdaStar R A A₀
  special : Special R E C
  memQ : ∀ i, Q i ∈ deltaSet R A A₀ E
  memP : ∀ i, P i ∈ deltaSet R A A₀ C
  opposite : ∀ i, Opposite (P i) (Q i)
  commuting : ∀ i j, i ≠ j → Commuting (P i ⊔ Q i) (P j ⊔ Q j)

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem opposite_of_not_commuting {X Y : Subgroup G} (hX : X ∈ leviSet R A A₀)
    (hY : Y ∈ leviSet R A A₀) (hXY : ¬ Commuting X Y) : Opposite X Y := by
  have hR := hS.hyp.root
  have hne : X ≠ Y := fun e => hXY (e ▸ hR.commuting_self hX.1.1)
  rcases hR.rel X hX.1.1 Y hY.1.1 hne with hc | ho | hs
  · exact absurd hc hXY
  · exact ho
  · exact absurd hs (hS.deg X hX Y hY)

theorem exists_special_lambdaStar : ∃ E ∈ lambdaStar R A A₀, ∃ C ∈ lambdaStar R A A₀,
    Special R E C ∧ ⁅E, C⁆ = A := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  by_contra hc
  push Not at hc
  have hcomm : ∀ E ∈ lambdaStar R A A₀, ∀ C ∈ lambdaStar R A A₀, Commuting E C := by
    intro E hE C hC
    by_contra hEC
    have hne : E ≠ C := fun e => hEC (e ▸ hR.commuting_self hE.1.1.1)
    obtain ⟨hs, he⟩ := (commuting_or_commutator_eq_of_mem_lambdaSet hS.hyp hS.mem hE.1 hC.1
      hne).resolve_left hEC
    exact hc E hE C hC hs he
  apply hR.ne_bot A hS.mem
  rw [← (Q_eq_M hS.hyp hS.mem).2.2.1, M_eq_gen_lambdaStar hS.hyp hS.mem hS.opp]
  exact commuting_iff_commutator_eq_bot.1 (commuting_gen_of_pairwise hcomm)

theorem not_mem_lambdaSet_and_mem_lambdaSet {E C K : Subgroup G} (hE : E ∈ lambdaStar R A A₀)
    (hC : C ∈ lambdaStar R A A₀) (hK : K ∈ lambdaStar R A A₀) (hEC : Special R E C)
    (hKE : K ∈ lambdaSet R E) (hKC : K ∈ lambdaSet R C) : False := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hKR : K ∈ R := hK.1.1.1
  have hne : E ≠ C := fun e => hR.ne_bot _ hEC.1
    (commuting_iff_commutator_eq_bot.1 (e ▸ hR.commuting_self hE.1.1.1))
  obtain ⟨-, hEC'⟩ := (commuting_or_commutator_eq_of_mem_lambdaSet hS.hyp hS.mem hE.1 hC.1
    hne).resolve_left fun hc => hR.ne_bot _ hEC.1 (commuting_iff_commutator_eq_bot.1 hc)
  have hle : A ≤ K := by
    rw [← hEC', ← (Q_eq_M hS.hyp hKR).2.2.1]
    exact Subgroup.commutator_mono (QD.le_M (mem_lambdaSet_comm hE.1.1.1 hKE))
      (QD.le_M (mem_lambdaSet_comm hC.1.1.1 hKC))
  exact hK.1.1.2.1 (QD.eq_of_le_of_mem hR hiso hS.mem hKR hle).symm

theorem not_mem_lambdaSet_commutator {E C X Y : Subgroup G} (hE : E ∈ lambdaStar R A A₀)
    (hC : C ∈ lambdaStar R A A₀) (hEC : Special R E C) (hX : X ∈ deltaSet R A A₀ C)
    (hY : Y ∈ deltaSet R A A₀ C) (hXY : X ≠ Y) :
    ⁅E, X⁆ ≠ ⁅E, Y⁆ ∧ ⁅E, Y⁆ ∉ lambdaSet R ⁅E, X⁆ := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hER : E ∈ R := hE.1.1.1
  have hemp := hS.deltaSet_inter_eq_empty_of_special hE hC hEC
  have hnotE : ∀ {Z : Subgroup G}, Z ∈ deltaSet R A A₀ C → Z ∉ deltaSet R A A₀ E :=
    fun hZ hZE => (Set.eq_empty_iff_forall_notMem.1 hemp) _ ⟨hZE, hZ⟩
  have hsX : Special R E X := (hS.mem_deltaSet_or_special hE hX.1).resolve_left (hnotE hX)
  have hsY : Special R E Y := (hS.mem_deltaSet_or_special hE hY.1).resolve_left (hnotE hY)
  obtain ⟨hKX, hKXE, hKXX⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hE hX.1 hsX
  obtain ⟨hKY, hKYE, hKYY⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hE hY.1 hsY
  have hXK : X ∈ deltaSet R A A₀ ⁅E, X⁆ := ⟨hX.1, mem_lambdaSet_comm hX.1.1.1 hKXX⟩
  have hYK : Y ∈ deltaSet R A A₀ ⁅E, Y⁆ := ⟨hY.1, mem_lambdaSet_comm hY.1.1.1 hKYY⟩
  have hXYc : Commuting X Y := hS.commuting_of_mem_deltaSet' hC hX hY
  have hCR : C ∈ R := hC.1.1.1
  have hKC : ⁅E, X⁆ ≠ C := fun e => hR.ne_bot _ hEC.1
    (commuting_iff_commutator_eq_bot.1 (e ▸ hKXE.1.2.2))
  have hne : ⁅E, X⁆ ≠ ⁅E, Y⁆ := by
    intro e
    have hCK := hS.mem_lambdaSet_of_mem_deltaSet_inter hKX hC hKC ⟨hXK, hX⟩ ⟨e ▸ hYK, hY⟩ hXY
    exact hS.not_mem_lambdaSet_and_mem_lambdaSet hE hC hKX hEC hKXE
      (mem_lambdaSet_comm hKX.1.1.1 hCK)
  refine ⟨hne, fun hcol => ?_⟩
  have hKYle : ⁅E, Y⁆ ≤ E ⊔ ⁅E, X⁆ := hS.le_sup_of_mem_lambdaSet hE hKX hKY hKXE hKYE hcol
  have hLY : E ⊔ ⁅E, Y⁆ = E ⊔ ⁅E, X⁆ := (mem_lambdaSet_of_le_sup hR hiso hER hKXE hER le_sup_left
    hKY.1.1.1 hKYle hKYE.1.2.1.symm).2
  have hLXY : ⁅E, X⁆ ⊔ ⁅E, Y⁆ = E ⊔ ⁅E, X⁆ := (mem_lambdaSet_of_le_sup hR hiso hER hKXE
    hKX.1.1.1 le_sup_right hKY.1.1.1 hKYle hne).2
  have hcentE : ∀ {Z : Subgroup G}, Commuting Z ⁅E, X⁆ → Commuting Z ⁅E, Y⁆ → Commuting Z E :=
    fun h1 h2 => (Commuting.sup_right h1 h2).mono le_rfl (hLXY ▸ le_sup_left)
  have hYL : ∀ y ∈ Y, conjSub (E ⊔ ⁅E, X⁆) y ≤ E ⊔ ⁅E, X⁆ := by
    intro y hy
    rw [← hLY, conjSub, Subgroup.map_sup, ← conjSub, ← conjSub,
      conjSub_of_forall_commute fun k hk => (hKYY.1.2.2 y hy k hk)]
    exact sup_le ((conjSub_le_commutator_sup (A := E) hy).trans (sup_comm _ _).le) le_sup_right
  have hKXYle : ⁅⁅E, X⁆, Y⁆ ≤ E ⊔ ⁅E, X⁆ := by
    rw [Subgroup.commutator_le]
    intro k hk y hy
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right hk) ?_
    have : y * (k⁻¹ * y⁻¹) = y * k⁻¹ * y⁻¹ := by group
    rw [this]
    exact hYL y hy (conj_mem_conjSub y (Subgroup.mem_sup_right (Subgroup.inv_mem _ hk)))
  have hnc : ¬ Commuting ⁅E, X⁆ Y := fun hc =>
    hnotE hY (hS.mem_deltaSet_of_commuting hE hY.1 (hcentE hc.symm hKYY.1.2.2).symm)
  have hsKY : Special R ⁅E, X⁆ Y := special_of_not_commuting_of_mem_leviSet hS.hyp hA hKX hY.1 hnc
  have heq : ⁅⁅E, X⁆, Y⁆ = ⁅E, Y⁆ := by
    by_contra hne'
    have hsup := (mem_lambdaSet_of_le_sup hR hiso hER hKXE hsKY.1 hKXYle hKY.1.1.1 hKYle hne').2
    have h1 : Commuting Y (E ⊔ ⁅E, X⁆) := hsup ▸ Commuting.sup_right hsKY.2.2.symm hKYY.1.2.2
    exact hnotE hY (hS.mem_deltaSet_of_commuting hE hY.1 (h1.mono le_rfl le_sup_left).symm)
  have hXKY := (hS.commuting_iff_mem_deltaSet_commutator hKX hY.1 hsKY hXK).1 hXYc
  rw [heq] at hXKY
  exact hnotE hX (hS.mem_deltaSet_of_commuting hE hX.1
    (hcentE hKXX.1.2.2 hXKY.2.1.2.2.symm).symm)

theorem exists_mem_deltaSet_inter_notMem {B P P' : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀) (hPB : P ∈ lambdaSet R B)
    (hPP' : P ≠ P') (hP'P : P' ∉ lambdaSet R P) :
    ∃ X ∈ deltaSet R A A₀ B ∩ deltaSet R A A₀ P, X ∉ deltaSet R A A₀ P' := by
  obtain ⟨Y, hY⟩ := hS.deltaSet_inter_nonempty_of_mem_lambdaSet hB hP hPB
  obtain ⟨Y', hY', hY'Y⟩ := hS.exists_ne_mem_deltaSet_inter hB hP hPB hY
  by_cases h1 : Y ∈ deltaSet R A A₀ P'
  · by_cases h2 : Y' ∈ deltaSet R A A₀ P'
    · exact absurd (hS.mem_lambdaSet_of_mem_deltaSet_inter hP hP' hPP' ⟨hY.2, h1⟩ ⟨hY'.2, h2⟩
        hY'Y.symm) hP'P
    · exact ⟨Y', hY', h2⟩
  · exact ⟨Y, hY, h1⟩

theorem exists_isSubframe :
    ∃ E C : Subgroup G, ∃ P Q : Fin 3 → Subgroup G, IsSubframe R A A₀ E C P Q := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  obtain ⟨E, hE, C, hC, hEC, -⟩ := hS.exists_special_lambdaStar
  have hER : E ∈ R := hE.1.1.1
  have hemp := hS.deltaSet_inter_eq_empty_of_special hE hC hEC
  have hnotE : ∀ {Z : Subgroup G}, Z ∈ deltaSet R A A₀ C → Z ∉ deltaSet R A A₀ E :=
    fun hZ hZE => (Set.eq_empty_iff_forall_notMem.1 hemp) _ ⟨hZE, hZ⟩
  have hnotC : ∀ {Z : Subgroup G}, Z ∈ deltaSet R A A₀ E → Z ∉ deltaSet R A A₀ C :=
    fun hZ hZC => (Set.eq_empty_iff_forall_notMem.1 hemp) _ ⟨hZ, hZC⟩
  have hsE : ∀ {Z : Subgroup G}, Z ∈ deltaSet R A A₀ C → Special R E Z := fun hZ =>
    (hS.mem_deltaSet_or_special hE hZ.1).resolve_left (hnotE hZ)
  have hsC : ∀ {Z : Subgroup G}, Z ∈ deltaSet R A A₀ E → Special R C Z := fun hZ =>
    (hS.mem_deltaSet_or_special hC hZ.1).resolve_left (hnotC hZ)
  have hcE : ∀ {X Z : Subgroup G}, X ∈ deltaSet R A A₀ C → Z ∈ deltaSet R A A₀ E →
      (Commuting Z X ↔ Z ∈ deltaSet R A A₀ ⁅E, X⁆) := fun hX hZ =>
    hS.commuting_iff_mem_deltaSet_commutator hE hX.1 (hsE hX) hZ
  have hcC : ∀ {Y Z : Subgroup G}, Y ∈ deltaSet R A A₀ E → Z ∈ deltaSet R A A₀ C →
      (Commuting Z Y ↔ Z ∈ deltaSet R A A₀ ⁅C, Y⁆) := fun hY hZ =>
    hS.commuting_iff_mem_deltaSet_commutator hC hY.1 (hsC hY) hZ
  have hEX : ∀ {X : Subgroup G}, X ∈ deltaSet R A A₀ C →
      ⁅E, X⁆ ∈ lambdaStar R A A₀ ∧ ⁅E, X⁆ ∈ lambdaSet R E := fun hX =>
    (commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hE hX.1 (hsE hX)).imp_right And.left
  have hCY : ∀ {Y : Subgroup G}, Y ∈ deltaSet R A A₀ E →
      ⁅C, Y⁆ ∈ lambdaStar R A A₀ ∧ ⁅C, Y⁆ ∈ lambdaSet R C := fun hY =>
    (commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hC hY.1 (hsC hY)).imp_right And.left
  obtain ⟨Q₀, hQ₀⟩ := deltaSet_nonempty hS.hyp hA hS.sec8.2 hS.opp hE
  obtain ⟨-, P₀, hP₀l, hQ₀P₀, hCP₀⟩ :=
    exists_opposite_of_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hQ₀.1 hC (hsC hQ₀)
  have hP₀ : P₀ ∈ deltaSet R A A₀ C := ⟨hP₀l, mem_lambdaSet_comm hP₀l.1.1 hCP₀⟩
  have hP₀Q₀ : ¬ Commuting P₀ Q₀ := fun hc =>
    hQ₀P₀.not_commuting (hR.ne_bot _ hQ₀.1.1.1) hc.symm
  obtain ⟨hC₀, hC₀C⟩ := hCY hQ₀
  obtain ⟨P₁, hP₁, hP₁C₀⟩ := hS.deltaSet_inter_nonempty_of_mem_lambdaSet hC hC₀ hC₀C
  have hP₁Q₀ : Commuting P₁ Q₀ := (hcC hQ₀ hP₁).2 hP₁C₀
  have hP₀P₁ : P₀ ≠ P₁ := fun e => hP₀Q₀ (e ▸ hP₁Q₀)
  obtain ⟨hE₀, hE₀E⟩ := hEX hP₀
  obtain ⟨hE₁, hE₁E⟩ := hEX hP₁
  obtain ⟨hne₀₁, hcol₀₁⟩ := hS.not_mem_lambdaSet_commutator hE hC hEC hP₀ hP₁ hP₀P₁
  obtain ⟨Q₁, ⟨hQ₁, hQ₁E₀⟩, hQ₁E₁⟩ :=
    hS.exists_mem_deltaSet_inter_notMem hE hE₀ hE₁ hE₀E hne₀₁ hcol₀₁
  have hQ₁P₀ : Commuting Q₁ P₀ := (hcE hP₀ hQ₁).2 hQ₁E₀
  have hQ₁P₁ : ¬ Commuting Q₁ P₁ := fun hc => hQ₁E₁ ((hcE hP₁ hQ₁).1 hc)
  obtain ⟨Q₂, ⟨hQ₂, hQ₂E₀⟩, hQ₂E₁⟩ := hS.deltaSet_inter_inter_nonempty hE hE₀ hE₁ hE₀E hE₁E
  have hQ₂P₀ : Commuting Q₂ P₀ := (hcE hP₀ hQ₂).2 hQ₂E₀
  have hQ₂P₁ : Commuting Q₂ P₁ := (hcE hP₁ hQ₂).2 hQ₂E₁
  obtain ⟨hC₁, hC₁C⟩ := hCY hQ₁
  obtain ⟨P₂, ⟨hP₂, hP₂C₀⟩, hP₂C₁⟩ := hS.deltaSet_inter_inter_nonempty hC hC₀ hC₁ hC₀C hC₁C
  have hP₂Q₀ : Commuting P₂ Q₀ := (hcC hQ₀ hP₂).2 hP₂C₀
  have hP₂Q₁ : Commuting P₂ Q₁ := (hcC hQ₁ hP₂).2 hP₂C₁
  have hP₂Q₂ : ¬ Commuting P₂ Q₂ := by
    intro hc
    obtain ⟨hE₂, hE₂E⟩ := hEX hP₂
    have hQ₀E₁ : Q₀ ∈ deltaSet R A A₀ ⁅E, P₁⁆ := (hcE hP₁ hQ₀).1 hP₁Q₀.symm
    have hQ₀E₂ : Q₀ ∈ deltaSet R A A₀ ⁅E, P₂⁆ := (hcE hP₂ hQ₀).1 hP₂Q₀.symm
    have hQ₂E₂ : Q₂ ∈ deltaSet R A A₀ ⁅E, P₂⁆ := (hcE hP₂ hQ₂).1 hc.symm
    have hQ₁E₂ : Q₁ ∈ deltaSet R A A₀ ⁅E, P₂⁆ := (hcE hP₂ hQ₁).1 hP₂Q₁.symm
    have hQ₀Q₂ : Q₀ ≠ Q₂ := fun e => hP₀Q₀ (e ▸ hQ₂P₀.symm)
    by_cases h12 : ⁅E, P₁⁆ = ⁅E, P₂⁆
    · exact hQ₁E₁ (h12 ▸ hQ₁E₂)
    have hcol := hS.mem_lambdaSet_of_mem_deltaSet_inter hE₁ hE₂ h12 ⟨hQ₀E₁, hQ₀E₂⟩
      ⟨hQ₂E₁, hQ₂E₂⟩ hQ₀Q₂
    have hle := hS.le_sup_of_mem_lambdaSet hE hE₁ hE₂ hE₁E hE₂E hcol
    have hsup : E ⊔ ⁅E, P₂⁆ = E ⊔ ⁅E, P₁⁆ := (mem_lambdaSet_of_le_sup hR hiso hER hE₁E hER
      le_sup_left hE₂.1.1.1 hle hE₂E.1.2.1.symm).2
    have h1 : Commuting Q₁ (E ⊔ ⁅E, P₂⁆) :=
      Commuting.sup_right hQ₁.2.1.2.2.symm hQ₁E₂.2.1.2.2.symm
    rw [hsup] at h1
    exact hQ₁E₁ (hS.mem_deltaSet_of_commuting hE₁ hQ₁.1 (h1.mono le_rfl le_sup_right).symm)
  set P : Fin 3 → Subgroup G := ![P₀, P₁, P₂] with hPdef
  set Q : Fin 3 → Subgroup G := ![Q₀, Q₁, Q₂] with hQdef
  have hPmem : ∀ i, P i ∈ deltaSet R A A₀ C := by
    intro i
    fin_cases i
    exacts [hP₀, hP₁, hP₂]
  have hQmem : ∀ i, Q i ∈ deltaSet R A A₀ E := by
    intro i
    fin_cases i
    exacts [hQ₀, hQ₁, hQ₂]
  have hPQ : ∀ i j, i ≠ j → Commuting (P i) (Q j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    exacts [hQ₁P₀.symm, hQ₂P₀.symm, hP₁Q₀, hQ₂P₁.symm, hP₂Q₀, hP₂Q₁]
  refine ⟨E, C, P, Q, ⟨hE, hC, hEC, hQmem, hPmem, fun i => ?_, fun i j hij => ?_⟩⟩
  · fin_cases i
    · exact hQ₀P₀.symm
    · exact hS.opposite_of_not_commuting hP₁.1 hQ₁.1 fun h => hQ₁P₁ h.symm
    · exact hS.opposite_of_not_commuting hP₂.1 hQ₂.1 hP₂Q₂
  · have h1 : Commuting (P i) (P j ⊔ Q j) :=
      Commuting.sup_right (hS.commuting_of_mem_deltaSet' hC (hPmem i) (hPmem j)) (hPQ i j hij)
    have h2 : Commuting (Q i) (P j ⊔ Q j) :=
      Commuting.sup_right (hPQ j i (Ne.symm hij)).symm
        (hS.commuting_of_mem_deltaSet' hE (hQmem i) (hQmem j))
    exact (Commuting.sup_right h1.symm h2.symm).symm

end Sec12

end CFSG.Timmesfeld.ARS
