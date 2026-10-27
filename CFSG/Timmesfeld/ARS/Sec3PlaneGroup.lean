module

public import CFSG.Timmesfeld.ARS.Sec3Plane

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Plane

@[expose] def IsElationGroup (R : Set (Subgroup G)) (N X L T : Subgroup G) : Prop :=
  (∀ t ∈ T, conjSub N t = N) ∧ (∀ t ∈ T, ∀ n ∈ N, ⁅n, t⁆ ∈ X) ∧ Commuting L T ∧
    ∀ P ∈ R, P ≤ N → ¬ P ≤ L → ∀ P' ∈ R, P' ≤ P ⊔ X → P' ≠ X → ∃ t ∈ T, conjSub P t = P'

theorem commutatorElement_mul_left_of_commute {u v t : G} (h : Commute u ⁅v, t⁆) :
    ⁅u * v, t⁆ = ⁅v, t⁆ * ⁅u, t⁆ := by
  calc ⁅u * v, t⁆ = u * ⁅v, t⁆ * u⁻¹ * ⁅u, t⁆ := by simp only [commutatorElement_def]; group
    _ = ⁅v, t⁆ * ⁅u, t⁆ := by rw [h.eq, mul_inv_cancel_right]

theorem conjSub_conjSub_inv (H : Subgroup G) (g : G) :
    conjSub (conjSub H g) g⁻¹ = H := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_inv_conjSub (H : Subgroup G) (g : G) :
    conjSub (conjSub H g⁻¹) g = H := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem IsElationGroup.conj (hR : IsRootClass R) {N X L T : Subgroup G}
    (h : IsElationGroup R N X L T) {g : G} (hg : conjSub N g = N) :
    IsElationGroup R N (conjSub X g) (conjSub L g) (conjSub T g) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hg' : conjSub N g⁻¹ = N := by
    calc conjSub N g⁻¹ = conjSub (conjSub N g) g⁻¹ := by rw [hg]
      _ = N := conjSub_conjSub_inv N g
  refine ⟨?_, ?_, h3.conjSub g, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    change conjSub N (g * t * g⁻¹) = N
    rw [conjSub_mul, conjSub_mul, hg', h1 t ht, hg]
  · rintro _ ⟨t, ht, rfl⟩ n hn
    change ⁅n, g * t * g⁻¹⁆ ∈ conjSub X g
    have hn' : g⁻¹ * n * g ∈ N := by
      rw [← hg] at hn
      exact mem_conjSub.1 hn
    have e : ⁅n, g * t * g⁻¹⁆ = g * ⁅g⁻¹ * n * g, t⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact conj_mem_conjSub g (h2 t ht _ hn')
  · intro P hP hPle hPL P' hP' hP'le hP'X
    have hP₀le : conjSub P g⁻¹ ≤ N := hg' ▸ Subgroup.map_mono hPle
    have hP₀L : ¬ conjSub P g⁻¹ ≤ L := fun h => hPL (by
      have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h
      rwa [← conjSub, conjSub_inv_conjSub] at this)
    have hP₀'le : conjSub P' g⁻¹ ≤ conjSub P g⁻¹ ⊔ X := by
      have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hP'le
      rwa [Subgroup.map_sup, ← conjSub, ← conjSub, ← conjSub, conjSub_conjSub_inv] at this
    have hP₀'X : conjSub P' g⁻¹ ≠ X := fun e => hP'X (by rw [← e, conjSub_inv_conjSub])
    obtain ⟨t, ht, hPt⟩ := h4 _ (hR.conjSub_mem hP _) hP₀le hP₀L _ (hR.conjSub_mem hP' _)
      hP₀'le hP₀'X
    refine ⟨g * t * g⁻¹, conj_mem_conjSub g ht, ?_⟩
    rw [conjSub_mul, conjSub_mul, hPt, conjSub_inv_conjSub]

section Elation

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {A B C : Subgroup G}
  (hA : A ∈ R) (hB : B ∈ R) (hC : C ∈ lambdaSet R B)
  (hline : ∀ D ∈ R, D ≤ B ⊔ C → D ∈ lambdaSet R A)

include hR hiso hA in
theorem not_commuting_commutator {F X : Subgroup G} (hF : F ∈ R) (hAF : Opposite A F)
    (hXA : X ∈ lambdaSet R A) (hXF : X ∈ psiSet R F) : ¬ Commuting A ⁅F, X⁆ := by
  intro h
  have hXR : X ∈ R := hXA.1.1
  have hTR : ⁅F, X⁆ ∈ R := hXF.2.1
  have hle : ⁅F, X⁆ ≤ X := fun t ht => Sec3.mem_of_forall_commute_of_mem_sup hR hiso hA hF hAF
    hXA hXF (Subgroup.mem_sup_right ht) fun a ha => h a ha t ht
  have hne : X ≠ ⁅F, X⁆ := by
    have := hXF.2.symm.ne_commutator hR
    rwa [Subgroup.commutator_comm] at this
  have hbot := inf_eq_bot hR hiso hXR hTR hne
  rw [inf_of_le_right hle] at hbot
  exact hR.ne_bot _ hTR hbot

include hR hiso hA hB hC hline in
theorem commuting_commutator_of_mem_psiSet {F X P : Subgroup G} (hF : F ∈ R)
    (hAF : Opposite A F) (hX : X ∈ R) (hXle : X ≤ A ⊔ B ⊔ C) (hXF : X ∈ psiSet R F)
    (hP : P ∈ R) (hPle : P ≤ A ⊔ B ⊔ C) (hPF : P ∈ psiSet R F) (hPX : P ≠ X) :
    Commuting P ⁅F, X⁆ := by
  have hXA : X ≠ A := fun e => Special.not_opposite hR hF hXF.2 (e ▸ hAF.symm)
  have hPA : P ≠ A := fun e => Special.not_opposite hR hF hPF.2 (e ▸ hAF.symm)
  have hAN : A ≤ A ⊔ B ⊔ C := le_sup_left.trans le_sup_left
  have hXAl : X ∈ lambdaSet R A :=
    mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hA hAN hX hXle hXA.symm
  have hAPl : A ∈ lambdaSet R P :=
    mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hP hPle hA hAN hPA
  obtain ⟨C', hC', hC'le, hC'A, hC'X⟩ := exists_mem_le_sup_ne_ne hR hiso hA hXAl A X
  have hC'P : C' ≠ P := by
    rintro rfl
    obtain ⟨D, -, huniq⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hF hAF hXAl
    exact hPX ((huniq C' ⟨hC', hC'le, hPF⟩).trans (huniq X ⟨hX, le_sup_right, hXF⟩).symm)
  have hC'Pl : C' ∈ lambdaSet R P := mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hP hPle
    hC' (hC'le.trans (sup_le hAN hXle)) hC'P.symm
  obtain ⟨-, -, hcomm, -, -⟩ := natural_modules_of_opposite_special hR hiso hF hA hAF.symm hXF
    hPF (mem_lambdaSet_comm hA hXAl) hAPl ⟨C', hC', hC'le, hC'A, hC'X, hC'Pl⟩
  exact hcomm.mono le_sup_left le_sup_right

include hR hiso hA hB hC hline in
theorem exists_isElationGroup_commutator {F X Y : Subgroup G} (hF : F ∈ R)
    (hAF : Opposite A F) (hX : X ∈ R) (hXle : X ≤ B ⊔ C) (hXF : X ∈ psiSet R F) (hY : Y ∈ R)
    (hYle : Y ≤ B ⊔ C) (hYF : Opposite Y F) :
    ∃ Z ∈ R, Z ≤ A ⊔ B ⊔ C ∧ Z ≠ X ∧ ¬ A ≤ X ⊔ Z ∧
      IsElationGroup R (A ⊔ B ⊔ C) X (X ⊔ Z) ⁅F, X⁆ := by
  have hAN : A ≤ A ⊔ B ⊔ C := le_sup_left.trans le_sup_left
  have hBCN : B ⊔ C ≤ A ⊔ B ⊔ C := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hN := commuting_sup_sup hR hA hB hC hline
  have hXA := hline X hX hXle
  have hYA := hline Y hY hYle
  have hXN : X ≤ A ⊔ B ⊔ C := hXle.trans hBCN
  have hXY : X ≠ Y := fun e => Special.not_opposite hR hF hXF.2 (e ▸ hYF.symm)
  obtain ⟨hXYl, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hB hC hY hYle hX hXle hXY.symm
  obtain ⟨hnorm, -⟩ :=
    conjSub_sup_sup_eq hR hiso hA hB hC hline hF hAF hX hXle hXF hY hYle hYF
  have hXT : Commuting X ⁅F, X⁆ :=
    (Sec3.commuting_sup_commutator hR hXA hXF).mono le_sup_left le_sup_right
  obtain ⟨Z, ⟨hZ, hZle, hZF⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hF hAF hYA
  have hZN : Z ≤ A ⊔ B ⊔ C := hZle.trans (sup_le hAN (hYle.trans hBCN))
  have hZX : Z ≠ X := by
    rintro rfl
    obtain ⟨-, hsup'⟩ := mem_lambdaSet_of_le_sup hR hiso hA hYA hZ hZle hY le_sup_right hXY
    exact not_le_sup hA hline (le_sup_left.trans (hsup'.symm.le.trans (sup_le hXle hYle)))
  have hZT : Commuting Z ⁅F, X⁆ := commuting_commutator_of_mem_psiSet hR hiso hA hB hC hline
    hF hAF hX hXN hXF hZ hZN hZF hZX
  have hLT : Commuting (X ⊔ Z) ⁅F, X⁆ := Commuting.sup_left hXT hZT
  have hnc := not_commuting_commutator hR hiso hA hF hAF hXA hXF
  refine ⟨Z, hZ, hZN, hZX, fun h => hnc (hLT.mono h le_rfl),
    fun t ht => hnorm t (Subgroup.mem_sup_right ht), ?_, hLT, ?_⟩
  ·
    intro t ht n hn
    obtain ⟨a, ha, m, hm, rfl⟩ := exists_mul_eq_of_mem hB hC hline hn
    have hm' : m ∈ ((Y ⊔ X : Subgroup G) : Set G) := by rw [hsup]; exact hm
    have hleYX : X ≤ Subgroup.normalizer (Y : Set G) :=
      (commuting_iff_le_centralizer.1 hXYl.1.2.2).trans (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Y X hleYX] at hm'
    obtain ⟨y, hy, x, hx, rfl⟩ := hm'
    have h1 : ⁅y, t⁆ ∈ X :=
      Sec3.commutatorElement_mem_of_mem_commutator hR hiso hY hF hYF hXYl hXF hy ht
    have h2 : ⁅a, t⁆ ∈ X :=
      Sec3.commutatorElement_mem_of_mem_commutator hR hiso hA hF hAF hXA hXF ha ht
    have h3 : ⁅x, t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hXT x hx t ht).eq
    have hyx : ⁅y * x, t⁆ = ⁅y, t⁆ := by
      rw [commutatorElement_mul_left_of_commute (u := y) (v := x) (t := t)
        (by rw [h3]; exact Commute.one_right y), h3, one_mul]
    rw [commutatorElement_mul_left_of_commute (u := a) (v := y * x) (t := t)
      (by rw [hyx]; exact hN a (hAN ha) _ (hXN h1)), hyx]
    exact X.mul_mem h1 h2
  ·
    intro P hP hPle hPL P' hP' hP'le hP'X
    have hPX : P ≠ X := fun e => hPL (e ▸ le_sup_left)
    have hPF : Opposite P F := by
      by_cases hPA : P = A
      · rw [hPA]
        exact hAF
      have hPAl := mem_lambdaSet_of_le hR hiso hA hB hC hline hP hPle hPA
      have hnc' : ¬ Commuting F P :=
        not_commuting_of_opposite_of_mem_lambdaSet hR hF hAF.symm hPAl
      have hne : P ≠ F := fun e => hnc' (by rw [← e]; exact hR.commuting_self hP)
      rcases hR.rel P hP F hF hne with h | h | h
      · exact absurd h.symm hnc'
      · exact h
      · exfalso
        have hPT := commuting_commutator_of_mem_psiSet hR hiso hA hB hC hline hF hAF hX hXN
          hXF hP hPle ⟨hP, h.symm⟩ hPX
        obtain ⟨-, -, hNeq⟩ :=
          sup_sup_eq_of_le hR hiso hA hB hC hline hP hPle hX hXN hZ hZN hZX.symm hPL
        have : Commuting (P ⊔ X ⊔ Z) ⁅F, X⁆ :=
          Commuting.sup_left (Commuting.sup_left hPT hXT) hZT
        rw [hNeq] at this
        exact hnc (this.mono hAN le_rfl)
    have hXPl : X ∈ lambdaSet R P :=
      mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hP hPle hX hXN hPX
    have hS := Sec3.setOf_mem_le_sup_eq hR hiso hP hF hPF hXPl hXF
    have hP'mem : P' ∈ {D | D ∈ R ∧ D ≤ P ⊔ X} := ⟨hP', hP'le⟩
    rw [hS] at hP'mem
    rcases hP'mem with h | ⟨⟨n, hn⟩, rfl⟩
    · exact absurd h hP'X
    obtain ⟨x, hx, t, ht, rfl⟩ := (Sec3.mem_sup_commutator_iff hXF).1 hn
    refine ⟨t, ht, ?_⟩
    have hPt : conjSub P t ≤ A ⊔ B ⊔ C := by
      rw [← hnorm t (Subgroup.mem_sup_right ht)]
      exact Subgroup.map_mono hPle
    change conjSub P t = conjSub P (x * t)
    rw [conjSub_mul, conjSub_of_forall_commute fun y hy => hN x (hXN hx) y (hPt hy)]

include hR hiso hA hB hC hline in
theorem exists_isElationGroup {X P : Subgroup G} (hX : X ∈ R) (hXle : X ≤ A ⊔ B ⊔ C)
    (hP : P ∈ R) (hPle : P ≤ A ⊔ B ⊔ C) (hXP : X ≠ P) :
    ∃ T ∈ R, ∃ Z ∈ R, Z ≤ A ⊔ B ⊔ C ∧ Z ≠ X ∧ ¬ P ≤ X ⊔ Z ∧
      IsElationGroup R (A ⊔ B ⊔ C) X (X ⊔ Z) T := by
  have hAN : A ≤ A ⊔ B ⊔ C := le_sup_left.trans le_sup_left
  have hBN : B ≤ A ⊔ B ⊔ C := le_sup_right.trans le_sup_left
  have hCN : C ≤ A ⊔ B ⊔ C := le_sup_right
  have hXPl := mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hP hPle hX hXle hXP.symm
  have hNle : ¬ A ⊔ B ⊔ C ≤ P ⊔ X := by
    intro h
    have h1 := Subgroup.card_le_of_le h
    rw [card_sup_sup hR hiso hA hB hC hline, card_sup hR hiso hP hXPl, hR.card_eq hP hA] at h1
    have hq : 2 ≤ Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).2 (hR.ne_bot A hA)
    have h2 : Nat.card A ^ 2 < Nat.card A ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
    omega
  obtain ⟨W, hW, hWle, hWPX⟩ : ∃ W ∈ R, W ≤ A ⊔ B ⊔ C ∧ ¬ W ≤ P ⊔ X := by
    by_contra! h
    exact hNle (sup_le (sup_le (h A hA hAN) (h B hB hBN)) (h C hC.1.1 hCN))
  have hXW : X ≠ W := fun e => hWPX (e ▸ le_sup_right)
  have hWXl := mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hX hXle hW hWle hXW
  have hPXW : ¬ P ≤ X ⊔ W := by
    intro h
    obtain ⟨-, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hX hWXl hX le_sup_left hP h hXP
    exact hWPX (le_sup_right.trans (hsup.symm.le.trans (sup_comm X P).le))
  obtain ⟨hWl, hline', hNeq⟩ :=
    sup_sup_eq_of_le hR hiso hA hB hC hline hP hPle hX hXle hW hWle hXW hPXW
  obtain ⟨F, hF, hPF, hXF, Y, hY, hYle, hYF⟩ :=
    exists_opposite_special_opposite hR hiso hP hX hWl hline' hX le_sup_left
  obtain ⟨Z, hZ, hZle, hZX, hPXZ, hT⟩ := exists_isElationGroup_commutator hR hiso hP hX hWl
    hline' hF hPF hX le_sup_left hXF hY hYle hYF
  rw [hNeq] at hZle hT
  exact ⟨⁅F, X⁆, hXF.2.1, Z, hZ, hZle, hZX, hPXZ, hT⟩

include hR hiso hA hB hC hline in
theorem IsElationGroup.rotate {D E W W'' T T' : Subgroup G} (hD : D ∈ R)
    (hDle : D ≤ A ⊔ B ⊔ C) (hE : E ∈ R) (hEle : E ≤ A ⊔ B ⊔ C) (hW : W ∈ R)
    (hWle : W ≤ A ⊔ B ⊔ C) (hW'' : W'' ∈ R) (hW''le : W'' ≤ A ⊔ B ⊔ C) (hDE : D ≠ E)
    (hT : IsElationGroup R (A ⊔ B ⊔ C) D (D ⊔ E) T)
    (hT' : IsElationGroup R (A ⊔ B ⊔ C) E (E ⊔ W) T') (hWDE : ¬ W ≤ D ⊔ E)
    (hW''DE : ¬ W'' ≤ D ⊔ E) :
    ∃ t ∈ T, IsElationGroup R (A ⊔ B ⊔ C) E (E ⊔ W'') (conjSub T' t) := by
  have hWD : W ≠ D := fun e => hWDE (e ▸ le_sup_left)
  have hEW'' : E ≠ W'' := fun e => hW''DE (e ▸ le_sup_right)
  have hDEl := mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hD hDle hE hEle hDE
  have hW''El := mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hE hEle hW'' hW''le hEW''
  have hDWl := mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hW hWle hD hDle hWD
  obtain ⟨W', hW', hW'le₁, hW'le₂⟩ := exists_le_sup_le_sup hR hiso hA hB hC hline hW hWle hD
    hDle hWD hE hEle hW'' hW''le hEW''
  have hW'D : W' ≠ D := by
    intro h
    rw [h] at hW'le₂
    obtain ⟨-, hsup⟩ :=
      mem_lambdaSet_of_le_sup hR hiso hE hW''El hE le_sup_left hD hW'le₂ hDE.symm
    exact hW''DE (le_sup_right.trans (hsup.symm.le.trans (sup_comm E D).le))
  have hW'E : W' ≠ E := by
    intro h
    rw [h] at hW'le₁
    obtain ⟨-, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hW hDWl hD le_sup_right hE hW'le₁ hDE
    exact hWDE (le_sup_left.trans hsup.symm.le)
  obtain ⟨t, ht, hWt⟩ := hT.2.2.2 W hW hWle hWDE W' hW' hW'le₁ hW'D
  have hEt : conjSub E t = E :=
    conjSub_of_forall_commute fun e he => (hT.2.2.1 e (Subgroup.mem_sup_right he) t ht).symm
  have hsupt : conjSub (E ⊔ W) t = E ⊔ W' := by
    rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, hEt, hWt]
  have hconj := hT'.conj hR (hT.1 t ht)
  obtain ⟨-, hsup⟩ :=
    mem_lambdaSet_of_le_sup hR hiso hE hW''El hE le_sup_left hW' hW'le₂ hW'E.symm
  rw [hEt, hsupt, hsup] at hconj
  exact ⟨t, ht, hconj⟩

include hR hiso hA hB hC hline in
theorem exists_isElationGroup_of_le {X Z : Subgroup G} (hX : X ∈ R) (hXle : X ≤ A ⊔ B ⊔ C)
    (hZ : Z ∈ R) (hZle : Z ≤ A ⊔ B ⊔ C) (hXZ : X ≠ Z) :
    ∃ T ∈ R, IsElationGroup R (A ⊔ B ⊔ C) X (X ⊔ Z) T := by
  have hZXl := mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hX hXle hZ hZle hXZ
  obtain ⟨T₁, -, Z₁, hZ₁, hZ₁le, hZ₁Z, hXZZ₁, hE₁⟩ :=
    exists_isElationGroup hR hiso hA hB hC hline hZ hZle hX hXle hXZ.symm
  have hZ₁XZ : ¬ Z₁ ≤ X ⊔ Z := by
    intro h
    obtain ⟨-, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hX hZXl hZ le_sup_right hZ₁ h hZ₁Z.symm
    exact hXZZ₁ (le_sup_left.trans hsup.symm.le)
  have hZ₁X : Z₁ ≠ X := fun e => hZ₁XZ (e ▸ le_sup_left)
  obtain ⟨T₂, -, Z₂, hZ₂, hZ₂le, hZ₂Z₁, hZZ₁Z₂, hE₂⟩ :=
    exists_isElationGroup hR hiso hA hB hC hline hZ₁ hZ₁le hZ hZle hZ₁Z
  have hZ₂ZZ₁ : ¬ Z₂ ≤ Z ⊔ Z₁ := by
    intro h
    have hZ₁Zl := mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hZ hZle hZ₁ hZ₁le hZ₁Z.symm
    obtain ⟨-, hsup⟩ :=
      mem_lambdaSet_of_le_sup hR hiso hZ hZ₁Zl hZ₁ le_sup_right hZ₂ h hZ₂Z₁.symm
    exact hZZ₁Z₂ (le_sup_left.trans hsup.symm.le)
  obtain ⟨t₁, -, hE₃⟩ := IsElationGroup.rotate hR hiso hA hB hC hline hZ hZle hZ₁ hZ₁le hZ₂
    hZ₂le hX hXle hZ₁Z.symm hE₁ hE₂ hZ₂ZZ₁ hXZZ₁
  obtain ⟨T₄, hT₄, Z₄, hZ₄, hZ₄le, hZ₄X, hZ₁XZ₄, hE₄⟩ :=
    exists_isElationGroup hR hiso hA hB hC hline hX hXle hZ₁ hZ₁le hZ₁X.symm
  have hZ₁Xl := mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hX hXle hZ₁ hZ₁le hZ₁X.symm
  have hZ₄Z₁X : ¬ Z₄ ≤ Z₁ ⊔ X := by
    intro h
    obtain ⟨-, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hX hZ₁Xl hX le_sup_left hZ₄
      (h.trans (sup_comm Z₁ X).le) hZ₄X.symm
    exact hZ₁XZ₄ (le_sup_right.trans hsup.symm.le)
  have hZZ₁X : ¬ Z ≤ Z₁ ⊔ X := by
    intro h
    obtain ⟨-, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hX hZ₁Xl hX le_sup_left hZ
      (h.trans (sup_comm Z₁ X).le) hXZ
    exact hZ₁XZ (le_sup_right.trans hsup.symm.le)
  obtain ⟨t₂, -, hE₅⟩ := IsElationGroup.rotate hR hiso hA hB hC hline hZ₁ hZ₁le hX hXle hZ₄
    hZ₄le hZ hZle hZ₁X hE₃ hE₄ hZ₄Z₁X hZZ₁X
  exact ⟨conjSub T₄ t₂, hR.conjSub_mem hT₄ t₂, hE₅⟩

include hR hiso hA hB hC hline in
theorem exists_mem_iSup_conjSub_sup_eq {P₁ Q₁ P₂ Q₂ : Subgroup G} (hP₁ : P₁ ∈ R)
    (hP₁le : P₁ ≤ A ⊔ B ⊔ C) (hQ₁ : Q₁ ∈ R) (hQ₁le : Q₁ ≤ A ⊔ B ⊔ C) (h₁ : P₁ ≠ Q₁)
    (hP₂ : P₂ ∈ R) (hP₂le : P₂ ≤ A ⊔ B ⊔ C) (hQ₂ : Q₂ ∈ R) (hQ₂le : Q₂ ≤ A ⊔ B ⊔ C)
    (h₂ : P₂ ≠ Q₂) :
    ∃ g ∈ ⨆ E ∈ {E : Subgroup G | E ∈ R ∧ ∀ x ∈ E, conjSub (A ⊔ B ⊔ C) x = A ⊔ B ⊔ C}, E,
      conjSub (P₁ ⊔ Q₁) g = P₂ ⊔ Q₂ := by
  by_cases heq : P₁ ⊔ Q₁ = P₂ ⊔ Q₂
  · exact ⟨1, one_mem _, by rw [conjSub_one, heq]⟩
  obtain ⟨X, hX, hXle₁, hXle₂⟩ := exists_le_sup_le_sup hR hiso hA hB hC hline hP₁ hP₁le hQ₁
    hQ₁le h₁ hP₂ hP₂le hQ₂ hQ₂le h₂
  have hXN : X ≤ A ⊔ B ⊔ C := hXle₁.trans (sup_le hP₁le hQ₁le)
  have hW : ∀ {P Q : Subgroup G}, P ∈ R → P ≤ A ⊔ B ⊔ C → Q ∈ R → Q ≤ A ⊔ B ⊔ C → P ≠ Q →
      X ≤ P ⊔ Q → ∃ W ∈ R, W ≤ A ⊔ B ⊔ C ∧ W ≠ X ∧ X ⊔ W = P ⊔ Q := by
    intro P Q hP hPle hQ hQle hPQ hXPQ
    have hQl := mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hP hPle hQ hQle hPQ
    by_cases hPX : P = X
    · refine ⟨Q, hQ, hQle, fun e => hPQ (hPX.trans e.symm), ?_⟩
      rw [hPX]
    · exact ⟨P, hP, hPle, hPX, (mem_lambdaSet_of_le_sup hR hiso hP hQl hX hXPQ hP le_sup_left
        (Ne.symm hPX)).2⟩
  obtain ⟨W₁, hW₁, hW₁le, hW₁X, hL₁⟩ := hW hP₁ hP₁le hQ₁ hQ₁le h₁ hXle₁
  obtain ⟨W₂, hW₂, hW₂le, hW₂X, hL₂⟩ := hW hP₂ hP₂le hQ₂ hQ₂le h₂ hXle₂
  have hW₁W₂ : W₁ ≠ W₂ := fun e => heq (by rw [← hL₁, ← hL₂, e])
  have hW₂l := mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hW₁ hW₁le hW₂ hW₂le hW₁W₂
  have hXW : ¬ X ≤ W₁ ⊔ W₂ := by
    intro h
    obtain ⟨-, hs₁⟩ :=
      mem_lambdaSet_of_le_sup hR hiso hW₁ hW₂l hX h hW₁ le_sup_left (Ne.symm hW₁X)
    obtain ⟨-, hs₂⟩ :=
      mem_lambdaSet_of_le_sup hR hiso hW₁ hW₂l hX h hW₂ le_sup_right (Ne.symm hW₂X)
    exact heq (by rw [← hL₁, ← hL₂, hs₁, hs₂])
  obtain ⟨E, hE, hEle, hEW₁, hEW₂⟩ := exists_mem_le_sup_ne_ne hR hiso hW₁ hW₂l W₁ W₂
  have hEX : E ≠ X := fun e => hXW (e ▸ hEle)
  have hEN : E ≤ A ⊔ B ⊔ C := hEle.trans (sup_le hW₁le hW₂le)
  obtain ⟨T, hT, hTE⟩ := exists_isElationGroup_of_le hR hiso hA hB hC hline hE hEN hX hXN hEX
  have hXEl := mem_lambdaSet_of_le_of_le hR hiso hA hB hC hline hE hEN hX hXN hEX
  obtain ⟨-, hsupE⟩ := mem_lambdaSet_of_le_sup hR hiso hW₁ hW₂l hW₁ le_sup_left hE hEle hEW₁.symm
  have hW₁EX : ¬ W₁ ≤ E ⊔ X := by
    intro h
    obtain ⟨-, hs⟩ := mem_lambdaSet_of_le_sup hR hiso hE hXEl hE le_sup_left hW₁ h hEW₁
    exact hXW (le_sup_right.trans (hs.symm.le.trans
      ((sup_comm E W₁).le.trans hsupE.le)))
  obtain ⟨t, ht, hW₁t⟩ := hTE.2.2.2 W₁ hW₁ hW₁le hW₁EX W₂ hW₂ (le_sup_right.trans hsupE.symm.le)
    hEW₂.symm
  have hXt : conjSub X t = X :=
    conjSub_of_forall_commute fun x hx => (hTE.2.2.1 x (Subgroup.mem_sup_right hx) t ht).symm
  refine ⟨t, le_iSup₂ (f := fun E (_ : E ∈ {E : Subgroup G | E ∈ R ∧
    ∀ x ∈ E, conjSub (A ⊔ B ⊔ C) x = A ⊔ B ⊔ C}) => E) T ⟨hT, hTE.1⟩ ht, ?_⟩
  rw [← hL₁, ← hL₂, conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, hXt, hW₁t]

end Elation

end Plane

open Plane

theorem plane_transitive [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B C : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (hC : C ∈ lambdaSet R B)
    (hline : ∀ D ∈ R, D ≤ B ⊔ C → D ∈ lambdaSet R A) :
    (∀ D ∈ R, D ≤ A ⊔ B ⊔ C → ∃ g ∈ ⨆ E ∈ {E : Subgroup G | E ∈ R ∧
        ∀ x ∈ E, conjSub (A ⊔ B ⊔ C) x = A ⊔ B ⊔ C}, E, conjSub A g = D) ∧
      (∀ P₁ ∈ R, ∀ Q₁ ∈ R, ∀ P₂ ∈ R, ∀ Q₂ ∈ R, P₁ ≤ A ⊔ B ⊔ C → Q₁ ≤ A ⊔ B ⊔ C →
        P₂ ≤ A ⊔ B ⊔ C → Q₂ ≤ A ⊔ B ⊔ C → P₁ ≠ Q₁ → P₂ ≠ Q₂ →
        ∃ g ∈ ⨆ E ∈ {E : Subgroup G | E ∈ R ∧ ∀ x ∈ E, conjSub (A ⊔ B ⊔ C) x = A ⊔ B ⊔ C}, E,
          conjSub (P₁ ⊔ Q₁) g = P₂ ⊔ Q₂) ∧
      ∀ X ∈ R, ∀ Z ∈ R, X ≤ A ⊔ B ⊔ C → Z ≤ A ⊔ B ⊔ C → X ≠ Z →
        ∃ T ∈ R, IsElationGroup R (A ⊔ B ⊔ C) X (X ⊔ Z) T :=
  ⟨fun _ hD hDle => exists_mem_iSup_conjSub_eq hR hiso hA hB hC hline hD hDle,
    fun _ hP₁ _ hQ₁ _ hP₂ _ hQ₂ hP₁le hQ₁le hP₂le hQ₂le h₁ h₂ =>
      exists_mem_iSup_conjSub_sup_eq hR hiso hA hB hC hline hP₁ hP₁le hQ₁ hQ₁le h₁ hP₂ hP₂le hQ₂
        hQ₂le h₂,
    fun _ hX _ hZ hXle hZle hXZ =>
      exists_isElationGroup_of_le hR hiso hA hB hC hline hX hXle hZ hZle hXZ⟩

end CFSG.Timmesfeld.ARS
