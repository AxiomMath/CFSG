module

public import CFSG.Timmesfeld.ARS.Sec5Sigma
public import CFSG.Timmesfeld.ARS.Sec8Natural

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem conjSub_mem_lambdaSet_of_mem_centralGroup (hR : IsRootClass R) {A X : Subgroup G}
    {g : G} (hg : g ∈ centralGroup R A) (hX : X ∈ lambdaSet R A) :
    conjSub X g ∈ lambdaSet R A := by
  have hgA : conjSub A g = A := conjSub_of_forall_commute fun a ha =>
    ((commuting_centralGroup (R := R) A) a ha g hg).symm
  have := conjSub_mem_lambdaSet hR hX g
  rwa [hgA] at this

theorem exists_mem_centralGroup_conjSub_eq (h : Hyp G R) {A X Y : Subgroup G} (hA : A ∈ R)
    (hX : X ∈ lambdaSet R A) (hY : Y ∈ lambdaSet R A) (hXY : Y ∈ lambdaSet R X) :
    ∃ g ∈ centralGroup R A, conjSub X g = Y := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hXR : X ∈ R := hX.1.1
  have hYR : Y ∈ R := hY.1.1
  have hXA : X ≠ A := hX.1.2.1
  have hYA : Y ≠ A := hY.1.2.1
  have hcent : ∀ {U : Subgroup G}, U ∈ R → Commuting A U → U ≤ centralGroup R A :=
    fun hU hAU => le_centralGroup ⟨hU, hAU⟩
  by_cases hAle : A ≤ X ⊔ Y
  ·
    have hsup : X ⊔ A = X ⊔ Y :=
      (mem_lambdaSet_of_le_sup hR hiso hXR hXY hXR le_sup_left hA hAle hXA).2
    have hYle : Y ≤ A ⊔ X := by
      rw [sup_comm, hsup]
      exact le_sup_right
    obtain ⟨U, hU, u, hu, hXu⟩ := exists_mem_lambdaSet_conjSub_eq hR hiso hA hX hXR le_sup_right
      hXA hYR hYle hYA
    exact ⟨u, hcent hU.1.1 hU.1.2.2 hu, hXu⟩
  ·
    have hline : ∀ D ∈ R, D ≤ X ⊔ Y → D ∈ lambdaSet R A := by
      intro D hD hDle
      have hmem : D ∈ {B | B ∈ R ∧ B ≤ M R A} :=
        ⟨hD, hDle.trans (sup_le (QD.le_M hX) (QD.le_M hY))⟩
      rw [(Q_eq_M h hA).2.1] at hmem
      exact hmem.resolve_left fun e => hAle (by rw [← e]; exact hDle)
    obtain ⟨-, -, htrans⟩ := plane_transitive hR hiso hA hXR hXY hline
    obtain ⟨P, hPR, hPle, hPX, hPY⟩ := exists_mem_le_sup_ne_ne hR hiso hXR hXY X Y
    have hPA : P ≠ A := fun e => hAle (by rw [← e]; exact hPle)
    have hPN : P ≤ A ⊔ X ⊔ Y :=
      hPle.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    have hAN : A ≤ A ⊔ X ⊔ Y := le_sup_left.trans le_sup_left
    have hXN : X ≤ A ⊔ X ⊔ Y := le_sup_right.trans le_sup_left
    obtain ⟨T, hTR, hT⟩ := htrans P hPR A hA hPN hAN hPA
    have hsupP : X ⊔ P = X ⊔ Y :=
      (mem_lambdaSet_of_le_sup hR hiso hXR hXY hXR le_sup_left hPR hPle hPX.symm).2
    have hXL : ¬ X ≤ P ⊔ A := by
      intro hXle
      have hPl : A ∈ lambdaSet R P := mem_lambdaSet_comm hA (hline P hPR hPle)
      have h1 := (mem_lambdaSet_of_le_sup hR hiso hPR hPl hPR le_sup_left hXR hXle hPX).2
      exact hAle ((le_sup_right.trans h1.symm.le).trans ((sup_comm P X).trans hsupP).le)
    obtain ⟨t, ht, hXt⟩ := hT.2.2.2 X hXR hXN hXL Y hYR
      ((le_sup_right : Y ≤ X ⊔ Y).trans hsupP.symm.le) hPY.symm
    exact ⟨t, hcent hTR (hT.2.2.1.mono le_sup_right le_rfl) ht, hXt⟩

namespace CentralOrbit

abbrev orbit (R : Set (Subgroup G)) (A B : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ g ∈ centralGroup R A, conjSub B g = X}

variable {A B X Y : Subgroup G}

theorem mem_self (R : Set (Subgroup G)) (A B : Subgroup G) : B ∈ orbit R A B :=
  ⟨1, Subgroup.one_mem _, conjSub_one B⟩

theorem conjSub_mem {g : G} (hX : X ∈ orbit R A B) (hg : g ∈ centralGroup R A) :
    conjSub X g ∈ orbit R A B := by
  obtain ⟨g', hg', rfl⟩ := hX
  exact ⟨g * g', Subgroup.mul_mem _ hg hg', conjSub_mul B g g'⟩

theorem exists_conjSub_eq (hX : X ∈ orbit R A B) (hY : Y ∈ orbit R A B) :
    ∃ g ∈ centralGroup R A, conjSub X g = Y := by
  obtain ⟨g, hg, rfl⟩ := hX
  obtain ⟨g', hg', rfl⟩ := hY
  refine ⟨g' * g⁻¹, Subgroup.mul_mem _ hg' (Subgroup.inv_mem _ hg), ?_⟩
  rw [conjSub_mul, ← conjSub_mul B g⁻¹ g, inv_mul_cancel, conjSub_one]

theorem subset_lambdaSet (hR : IsRootClass R) (hB : B ∈ lambdaSet R A) :
    orbit R A B ⊆ lambdaSet R A := by
  rintro _ ⟨g, hg, rfl⟩
  exact conjSub_mem_lambdaSet_of_mem_centralGroup hR hg hB

theorem conjSub_notMem {g : G} (hX : X ∉ orbit R A B) (hg : g ∈ centralGroup R A) :
    conjSub X g ∉ orbit R A B := fun hXg => hX (by
  have := conjSub_mem hXg (Subgroup.inv_mem _ hg)
  rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this)

theorem mem_of_mem_lambdaSet (h : Hyp G R) (hA : A ∈ R) (hB : B ∈ lambdaSet R A)
    (hX : X ∈ orbit R A B) (hY : Y ∈ lambdaSet R A) (hXY : Y ∈ lambdaSet R X) :
    Y ∈ orbit R A B := by
  obtain ⟨g, hg, hXg⟩ :=
    exists_mem_centralGroup_conjSub_eq h hA (subset_lambdaSet h.root hB hX) hY hXY
  rw [← hXg]
  exact conjSub_mem hX hg

theorem commutator_mem_lambdaSet (h : Hyp G R) {C : Subgroup G} (hA : A ∈ R)
    (hC : C ∈ sigmaSet R A) (hCl : C ∉ lambdaSet R A) (hX : X ∈ lambdaSet R A)
    (hCX : ¬ Commuting C X) :
    Special R C X ∧ ⁅C, X⁆ ∈ lambdaSet R A ∧ C ∈ lambdaSet R ⁅C, X⁆ ∧
      X ∈ lambdaSet R ⁅C, X⁆ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hCR : C ∈ R := hC.1
  have hXR : X ∈ R := hX.1.1
  have hs : Special R C X := by
    have hne : C ≠ X := fun e => hCl (e ▸ hX)
    rcases hR.rel C hCR X hXR hne with hc | ho | hs
    · exact absurd hc hCX
    · exact absurd hC.2.2.symm
        (not_commuting_of_opposite_of_mem_lambdaSet hR hCR ho (mem_lambdaSet_comm hA hX))
    · exact hs
  obtain ⟨hCJ, hXJ⟩ := mem_lambdaSet_commutator hR hiso hCR hXR hs
  have hJM : ⁅C, X⁆ ≤ M R A := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_of_le_normalizer (QD.le_M hX) (QD.le_normalizer_M hR hA ⟨hCR, hC.2.2⟩)
  have hmem : ⁅C, X⁆ ∈ {B | B ∈ R ∧ B ≤ M R A} := ⟨hs.1, hJM⟩
  rw [(Q_eq_M h hA).2.1] at hmem
  exact ⟨hs, hmem.resolve_left fun e => hCl (e ▸ hCJ), hCJ, hXJ⟩

theorem mem_of_not_commuting (h : Hyp G R) {C I : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ lambdaSet R A) (hC : C ∈ sigmaSet R A) (hCl : C ∉ lambdaSet R A)
    (hY : Y ∈ orbit R A B) (hYC : C ∈ lambdaSet R Y) (hI : I ∈ lambdaSet R A)
    (hYI : Commuting Y I) (hCI : ¬ Commuting C I) : I ∈ orbit R A B := by
  have := h.finite
  have hR := h.root
  have hYR : Y ∈ R := (subset_lambdaSet hR hB hY).1.1
  obtain ⟨hs, hJA, -, hIJ⟩ := commutator_mem_lambdaSet h hA hC hCl hI hCI
  have hJM : ⁅C, I⁆ ≤ M R Y :=
    commutator_le_of_le_normalizer (QD.le_M hYC) (QD.le_normalizer_M hR hYR ⟨hI.1.1, hYI⟩)
  have hmem : ⁅C, I⁆ ∈ {X | X ∈ R ∧ X ≤ M R Y} := ⟨hs.1, hJM⟩
  rw [(Q_eq_M h hYR).2.1] at hmem
  have hJO : ⁅C, I⁆ ∈ orbit R A B := by
    rcases hmem with e | hJY
    · rw [e]
      exact hY
    · exact mem_of_mem_lambdaSet h hA hB hY hJA hJY
  exact mem_of_mem_lambdaSet h hA hB hJO hI hIJ

theorem commuting_of_mem_lambdaSet (h : Hyp G R) {C D L I : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ lambdaSet R A) (hC : C ∈ sigmaSet R A) (hCl : C ∉ lambdaSet R A)
    (hD : D ∈ orbit R A B) (hL : L ∈ orbit R A B) (hLD : L ∈ lambdaSet R D)
    (hCD : C ∈ lambdaSet R D) (hCL : C ∈ lambdaSet R L) (hI : I ∈ lambdaSet R A)
    (hIO : I ∉ orbit R A B) : Commuting C I := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hDl := subset_lambdaSet hR hB hD
  have hLl := subset_lambdaSet hR hB hL
  have hDR : D ∈ R := hDl.1.1
  have hLR : L ∈ R := hLl.1.1
  have hIR : I ∈ R := hI.1.1
  have hCR : C ∈ R := hC.1
  obtain ⟨-, -, hcommA, -, -⟩ := Q_eq_M h hA
  have hDLA : D ⊔ L ≤ M R A := sup_le (QD.le_M hDl) (QD.le_M hLl)
  have hDLC : D ⊔ L ≤ M R C :=
    sup_le (QD.le_M (mem_lambdaSet_comm hDR hCD)) (QD.le_M (mem_lambdaSet_comm hLR hCL))
  have hpt : ∀ P ∈ R, P ≤ D ⊔ L → P ∈ orbit R A B ∧ C ∈ lambdaSet R P := by
    intro P hP hPle
    have hmemA : P ∈ {X | X ∈ R ∧ X ≤ M R A} := ⟨hP, hPle.trans hDLA⟩
    have hmemC : P ∈ {X | X ∈ R ∧ X ≤ M R C} := ⟨hP, hPle.trans hDLC⟩
    rw [(Q_eq_M h hA).2.1] at hmemA
    rw [(Q_eq_M h hCR).2.1] at hmemC
    have hPA : P ≠ A := by
      rintro rfl
      rcases hmemC with e | hPC
      · exact hC.2.1 e.symm
      · exact hCl (mem_lambdaSet_comm hCR hPC)
    have hPl : P ∈ lambdaSet R A := hmemA.resolve_left hPA
    have hPC : P ∈ lambdaSet R C := hmemC.resolve_left fun e => hCl (e ▸ hPl)
    refine ⟨?_, mem_lambdaSet_comm hCR hPC⟩
    by_cases hPD : P = D
    · rw [hPD]
      exact hD
    · exact mem_of_mem_lambdaSet h hA hB hD hPl
        (mem_lambdaSet_of_le_sup hR hiso hDR hLD hDR le_sup_left hP hPle (Ne.symm hPD)).1
  have hspec : ∀ {X : Subgroup G}, X ∈ lambdaSet R A → ¬ Commuting X I →
      Special R X I ∧ ⁅X, I⁆ = A := by
    intro X hX hXI
    have hs : Special R X I := by
      have hne : X ≠ I := fun e => hXI (by rw [e]; exact hR.commuting_self hIR)
      rcases hR.rel X hX.1.1 I hIR hne with hc | ho | hs
      · exact absurd hc hXI
      · exact absurd hX.1.2.2.symm
          (not_commuting_of_opposite_of_mem_lambdaSet hR hX.1.1 ho (mem_lambdaSet_comm hA hI))
      · exact hs
    refine ⟨hs, ?_⟩
    have hle : ⁅X, I⁆ ≤ A := (Subgroup.commutator_mono (QD.le_M hX) (QD.le_M hI)).trans hcommA.le
    by_contra hne
    have hbot := inf_eq_bot hR hiso hs.1 hA hne
    rw [inf_eq_left.2 hle] at hbot
    exact hR.ne_bot _ hs.1 hbot
  have hex : ∃ P ∈ R, P ≤ D ⊔ L ∧ Commuting P I := by
    by_cases hDI : Commuting D I
    · exact ⟨D, hDR, le_sup_left, hDI⟩
    by_cases hLI : Commuting L I
    · exact ⟨L, hLR, le_sup_right, hLI⟩
    obtain ⟨-, hDIA⟩ := hspec hDl hDI
    obtain ⟨hsL, hLIA⟩ := hspec hLl hLI
    obtain ⟨i, hi, hi1⟩ := hR.exists_ne_one hIR
    obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hDR
    have hdi : ⁅d, i⁆ ∈ A := hDIA ▸ Subgroup.commutator_mem_commutator hd hi
    obtain ⟨l, hl, hli⟩ := (bijOn_commutator_left hR hiso hLR hIR hsL hi hi1).surjOn
      (show ⁅d, i⁆⁻¹ ∈ ((⁅L, I⁆ : Subgroup G) : Set G) from hLIA ▸ A.inv_mem hdi)
    have hli' : ⁅l, i⁆ = ⁅d, i⁆⁻¹ := hli
    have hx : ⁅d * l, i⁆ = 1 := by
      rw [Plane.commutatorElement_mul_left_of_commute, hli', inv_mul_cancel]
      rw [hli']
      exact ((QD.commuting_M hR hA) _ (A.inv_mem hdi) d (QD.le_M hDl hd)).symm
    have hx1 : d * l ≠ 1 := by
      intro e
      have hl' : l = d⁻¹ := eq_inv_of_mul_eq_one_right e
      have hmem : d⁻¹ ∈ D ⊓ L := ⟨D.inv_mem hd, hl' ▸ hl⟩
      rw [inf_eq_bot hR hiso hDR hLR hLD.1.2.1.symm, Subgroup.mem_bot, inv_eq_one] at hmem
      exact hd1 hmem
    obtain ⟨P, hP, hPle, hxP⟩ := hLD.2 (d * l)
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right hl)) hx1
    refine ⟨P, hP, hPle, ?_⟩
    have hPl : P ∈ lambdaSet R A := subset_lambdaSet hR hB (hpt P hP hPle).1
    by_contra hPI
    exact hi1 (eq_one_of_commute_of_special hR hiso hP hIR (hspec hPl hPI).1 hxP hx1 hi
      (commutatorElement_eq_one_iff_mul_comm.1 hx))
  obtain ⟨P, hP, hPle, hPI⟩ := hex
  obtain ⟨hPO, hCP⟩ := hpt P hP hPle
  by_contra hCI
  exact hIO (mem_of_not_commuting h hA hB hC hCl hPO hCP hI hPI hCI)

theorem commuting_of_forall_commuting (h : Hyp G R) {C I : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ lambdaSet R A) (hC : C ∈ sigmaSet R A) (hCl : C ∉ lambdaSet R A)
    (hCO : ∀ J ∈ lambdaSet R A, J ∉ orbit R A B → Commuting C J) (hX : X ∈ orbit R A B)
    (hI : I ∈ lambdaSet R A) (hIO : I ∉ orbit R A B) : Commuting X I := by
  have := h.finite
  have hR := h.root
  obtain ⟨-, -, hcommA, hcent, -⟩ := Q_eq_M h hA
  have hCR : C ∈ R := hC.1
  obtain ⟨D, hD, hCD⟩ : ∃ D ∈ orbit R A B, ¬ Commuting C D := by
    by_contra! hall
    have hCM : Commuting C (M R A) := commuting_iff_le_centralizer.2 (sup_le
      (commuting_iff_le_centralizer.1 hC.2.2.symm) (iSup₂_le fun E hE => by
        refine commuting_iff_le_centralizer.1 ?_
        by_cases hEO : E ∈ orbit R A B
        · exact hall E hEO
        · exact hCO E hE hEO))
    have hmem : C ∈ {X | X ∈ R ∧ Commuting X (M R A)} := ⟨hCR, hCM⟩
    rw [hcent] at hmem
    exact hC.2.1 hmem
  have hDl := subset_lambdaSet hR hB hD
  obtain ⟨-, hWA, -, hDW⟩ := commutator_mem_lambdaSet h hA hC hCl hDl hCD
  have hWO : ⁅C, D⁆ ∈ orbit R A B :=
    mem_of_mem_lambdaSet h hA hB hD hWA (mem_lambdaSet_comm hWA.1.1 hDW)
  have hW : ∀ J ∈ lambdaSet R A, J ∉ orbit R A B → Commuting ⁅C, D⁆ J := by
    intro J hJ hJO
    refine commuting_iff_commutator_eq_bot.2
      (Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_)
    · exact le_bot_iff.1 ((Subgroup.commutator_mono ((Subgroup.commutator_mono (QD.le_M hDl)
        (QD.le_M hJ)).trans hcommA.le) le_rfl).trans (commuting_iff_commutator_eq_bot.1 hC.2.2).le)
    · rw [Subgroup.commutator_comm J C, commuting_iff_commutator_eq_bot.1 (hCO J hJ hJO),
        Subgroup.commutator_bot_left]
  obtain ⟨g, hg, hWg⟩ := exists_conjSub_eq hWO hX
  have hIg : conjSub I g⁻¹ ∈ lambdaSet R A :=
    conjSub_mem_lambdaSet_of_mem_centralGroup hR (Subgroup.inv_mem _ hg) hI
  have := (hW _ hIg (conjSub_notMem hIO (Subgroup.inv_mem _ hg))).conjSub g
  rwa [hWg, ← conjSub_mul, mul_inv_cancel, conjSub_one] at this

theorem forall_commuting_or_forall_commuting (h : Hyp G R) (hA : A ∈ R)
    (hB : B ∈ lambdaSet R A)
    (h2 : ∀ X ∈ orbit R A B, ∀ I ∈ lambdaSet R A, I ∉ orbit R A B → Commuting X I)
    (hY : Y ∈ sigmaSet R A) (hYl : Y ∉ lambdaSet R A) :
    (∀ X ∈ orbit R A B, Commuting Y X) ∨
      ∀ I ∈ lambdaSet R A, I ∉ orbit R A B → Commuting Y I := by
  by_cases hex : ∃ X ∈ orbit R A B, Y ∈ lambdaSet R X
  · obtain ⟨X, hX, hYX⟩ := hex
    refine Or.inr fun I hI hIO => ?_
    by_contra hYI
    exact hIO (mem_of_not_commuting h hA hB hY hYl hX hYX hI (h2 X hX I hI hIO) hYI)
  · refine Or.inl fun X hX => ?_
    by_contra hYX
    have hXl := subset_lambdaSet h.root hB hX
    obtain ⟨-, hJA, hYJ, hXJ⟩ := commutator_mem_lambdaSet h hA hY hYl hXl hYX
    exact hex ⟨_, mem_of_mem_lambdaSet h hA hB hX hJA (mem_lambdaSet_comm hJA.1.1 hXJ), hYJ⟩

end CentralOrbit

end CFSG.Timmesfeld.ARS
