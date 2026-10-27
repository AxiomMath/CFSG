module

public import CFSG.Timmesfeld.ARS.Sec8Regular

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem commuting_sup_of_mem_lambdaSet (hR : IsRootClass R) {Y P : Subgroup G} (hY : Y ∈ R)
    (hP : P ∈ lambdaSet R Y) : Commuting (Y ⊔ P) (Y ⊔ P) :=
  Commuting.sup_left (Commuting.sup_right (hR.commuting_self hY) hP.1.2.2)
    (Commuting.sup_right hP.1.2.2.symm (hR.commuting_self hP.1.1))

namespace LinePlane

section NoPlane

variable (h : Hyp G R) {Y P : Subgroup G} (hY : Y ∈ R) (hP : P ∈ lambdaSet R Y)
  (hno : ∀ E ∈ R, ¬ E ≤ Y ⊔ P → (∀ Q ∈ R, Q ≤ Y ⊔ P → Q ∈ lambdaSet R E) → False)
include h hY hP hno

theorem conjSub_sup_eq_of_commuting {X Q : Subgroup G} (hX : X ∈ R) (hQ : Q ∈ R)
    (hQle : Q ≤ Y ⊔ P) (hXQ : Commuting X Q) {x : G} (hx : x ∈ X) :
    conjSub (Y ⊔ P) x = Y ⊔ P := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hPR : P ∈ R := hP.1.1
  have hXN : X ≤ Subgroup.normalizer ((Y ⊔ P : Subgroup G) : Set G) := by
    by_cases hXL : Commuting X (Y ⊔ P)
    · exact (commuting_iff_le_centralizer.1 hXL.symm).trans (Subgroup.centralizer_le_normalizer _)
    obtain ⟨E', hE', hE'le, hXE'⟩ : ∃ E' ∈ R, E' ≤ Y ⊔ P ∧ ¬ Commuting X E' := by
      by_cases hXY : Commuting X Y
      · exact ⟨P, hPR, le_sup_right, fun hXP => hXL (hXY.sup_right hXP)⟩
      · exact ⟨Y, hY, le_sup_left, hXY⟩
    have hE'Q : E' ≠ Q := fun e => hXE' (e ▸ hXQ)
    have hE'X : X ≠ E' := fun e => hXE' (e ▸ hR.commuting_self hX)
    obtain ⟨hQE', hsupE'⟩ := mem_lambdaSet_of_le_sup hR hiso hY hP hE' hE'le hQ hQle hE'Q
    have hs : Special R X E' := by
      rcases hR.rel X hX E' hE' hE'X with hc | ho | hs
      · exact absurd hc hXE'
      · exact absurd hXQ (not_commuting_of_opposite_of_mem_lambdaSet hR hX ho hQE')
      · exact hs
    have hWR : ⁅E', X⁆ ∈ R := hs.symm.1
    by_cases hWL : ⁅E', X⁆ ≤ Y ⊔ P
    · refine le_normalizer_of_conjSub_le fun x hx => ?_
      rw [← hsupE', conjSub, Subgroup.map_sup, ← conjSub, ← conjSub,
        conjSub_of_forall_commute fun q hq => hXQ x hx q hq]
      exact sup_le ((conjSub_le_commutator_sup hx).trans (sup_le (hsupE' ▸ hWL) le_sup_left))
        le_sup_right
    exfalso
    obtain ⟨x₀, hx₀, hx₀1⟩ := hR.exists_ne_one hX
    set Y' := conjSub E' x₀ with hY'
    have hY'R : Y' ∈ R := hR.conjSub_mem hE' x₀
    have hY'l : Y' ∈ lambdaSet R E' :=
      QD.conjSub_mem_lambdaSet_of_special hR hiso hX hE' hs hx₀ hx₀1
    have hWl : ⁅E', X⁆ ∈ lambdaSet R E' :=
      mem_lambdaSet_comm hWR (mem_lambdaSet_commutator hR hiso hE' hX hs.symm).1
    have hY'le : Y' ≤ E' ⊔ ⁅E', X⁆ := (conjSub_le_commutator_sup hx₀).trans (sup_comm _ _).le
    have hY'L : ¬ Y' ≤ Y ⊔ P := by
      intro hle
      have h1 := (mem_lambdaSet_of_le_sup hR hiso hY hP hE' hE'le hY'R hle hY'l.1.2.1.symm).2
      have h2 := (mem_lambdaSet_of_le_sup hR hiso hE' hWl hE' le_sup_left hY'R hY'le
        hY'l.1.2.1.symm).2
      exact hWL (le_sup_right.trans (h2.symm.le.trans h1.le))
    refine hno Y' hY'R hY'L fun Q' hQ' hQ'le => ?_
    have hQY' : Q ∈ lambdaSet R Y' := by
      have := conjSub_mem_lambdaSet hR hQE' x₀
      rwa [conjSub_of_forall_commute fun q hq => hXQ x₀ hx₀ q hq] at this
    have hLM : Y ⊔ P ≤ M R Y' :=
      hsupE' ▸ sup_le (QD.le_M (mem_lambdaSet_comm hE' hY'l)) (QD.le_M hQY')
    have hmem : Q' ∈ {B | B ∈ R ∧ B ≤ M R Y'} := ⟨hQ', hQ'le.trans hLM⟩
    rw [(Q_eq_M h hY'R).2.1] at hmem
    exact hmem.resolve_left fun e => hY'L (e ▸ hQ'le)
  exact conjSub_eq_self_iff.2 (hXN hx)

theorem commuting_or_commutator_eq {X Q : Subgroup G} (hX : X ∈ R) (hYX : Commuting Y X)
    (hQ : Q ∈ R) (hQle : Q ≤ Y ⊔ P) (hQY : Q ≠ Y) :
    Commuting Q X ∨ (X ∈ lambdaSet R Y ∧ ⁅Q, X⁆ = Y) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnorm : ∀ x ∈ X, conjSub (Y ⊔ P) x = Y ⊔ P := fun x hx =>
    conjSub_sup_eq_of_commuting h hY hP hno hX hY le_sup_left hYX.symm hx
  have hLab := commuting_sup_of_mem_lambdaSet hR hY hP
  by_cases hXQ : X = Q
  · subst hXQ
    exact Or.inl (hR.commuting_self hX)
  rcases hR.rel Q hQ X hX (Ne.symm hXQ) with hc | ho | hs
  · exact Or.inl hc
  · exfalso
    obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hX
    have hop := opposite_conjSub_of_opposite hR hX hQ ho.symm hx hx1
    have hQx : conjSub Q x ≤ Y ⊔ P := hnorm x hx ▸ Subgroup.map_mono hQle
    exact hop.not_commuting (hR.ne_bot Q hQ) (hLab.mono hQle hQx)
  · right
    have hWle : ⁅Q, X⁆ ≤ Y ⊔ P := by
      rw [Subgroup.commutator_le]
      intro q hq x hx
      have h1 : x * q⁻¹ * x⁻¹ ∈ Y ⊔ P := by
        rw [← hnorm x hx]
        exact conj_mem_conjSub x (hQle (Q.inv_mem hq))
      have h2 := (Y ⊔ P).mul_mem (hQle hq) h1
      rwa [show q * (x * q⁻¹ * x⁻¹) = ⁅q, x⁆ by rw [commutatorElement_def]; group] at h2
    by_cases hWY : ⁅Q, X⁆ = Y
    · refine ⟨mem_lambdaSet_of_commutator_eq hR hiso hY hX hQ ?_, hWY⟩
      rw [Subgroup.commutator_comm]
      exact hWY
    · exfalso
      obtain ⟨-, hsup⟩ :=
        mem_lambdaSet_of_le_sup hR hiso hY hP hY le_sup_left hs.1 hWle (Ne.symm hWY)
      have hXL : Commuting X (Y ⊔ P) := hsup ▸ Commuting.sup_right hYX.symm hs.2.2.symm
      exact Special.not_commuting hR hs (hXL.mono le_rfl hQle).symm

theorem commuting_of_mem_sigmaSet {X Q : Subgroup G} (hXs : X ∈ sigmaSet R Y)
    (hXl : X ∉ lambdaSet R Y) (hQ : Q ∈ R) (hQle : Q ≤ Y ⊔ P) : Commuting Q X := by
  by_cases hQY : Q = Y
  · subst hQY
    exact hXs.2.2
  rcases commuting_or_commutator_eq h hY hP hno hXs.1 hXs.2.2 hQ hQle hQY with h1 | h1
  · exact h1
  · exact absurd h1.1 hXl

theorem mem_sigmaSet_notMem_of_le {X Q : Subgroup G} (hQ : Q ∈ R) (hQle : Q ≤ Y ⊔ P)
    (hQY : Q ≠ Y) (hXs : X ∈ sigmaSet R Y) (hXl : X ∉ lambdaSet R Y) :
    X ∈ sigmaSet R Q ∧ X ∉ lambdaSet R Q := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hQl : Q ∈ lambdaSet R Y :=
    (mem_lambdaSet_of_le_sup hR hiso hY hP hY le_sup_left hQ hQle (Ne.symm hQY)).1
  have hXQ : Commuting Q X := commuting_of_mem_sigmaSet h hY hP hno hXs hXl hQ hQle
  have hXne : X ≠ Q := fun e => hXl (e ▸ hQl)
  refine ⟨⟨hXs.1, hXne, hXQ⟩, fun hXQl => ?_⟩
  have hXI : X ∉ isolatedSet R Y := by
    intro hI
    have hmem : X ∈ {B | B ∈ R ∧ B ≤ M R Y} := ⟨hXs.1, (Q_eq_M h hY).1 ▸ QD.le_Q hI⟩
    rw [(Q_eq_M h hY).2.1] at hmem
    rcases hmem with h1 | h1
    · exact hXs.2.1 h1
    · exact hXl h1
  obtain ⟨Z, hZc, hXZ⟩ := QD.exists_opposite_of_notMem_isolatedSet ⟨hXs.1, hXs.2.2⟩ hXI
  have hZY : Z ≠ Y := by
    rintro rfl
    exact hXZ.not_commuting (hR.ne_bot X hXs.1) hXs.2.2.symm
  have hZl : Z ∉ lambdaSet R Y := fun hZl =>
    not_commuting_of_opposite_of_mem_lambdaSet hR hXs.1 hXZ (mem_lambdaSet_comm hY hZl)
      hXs.2.2.symm
  have hZQ : Commuting Q Z :=
    commuting_of_mem_sigmaSet h hY hP hno ⟨hZc.1, hZY, hZc.2⟩ hZl hQ hQle
  exact not_commuting_of_opposite_of_mem_lambdaSet hR hZc.1 hXZ.symm (mem_lambdaSet_comm hQ hXQl)
    hZQ.symm

end NoPlane

end LinePlane

open LinePlane

theorem exists_plane_of_sigmaSet_ne (h : Hyp G R) {Y P : Subgroup G} (hY : Y ∈ R)
    (hP : P ∈ lambdaSet R Y) (hYne : sigmaSet R Y ≠ lambdaSet R Y) :
    ∃ E ∈ R, ¬ E ≤ Y ⊔ P ∧ ∀ Q ∈ R, Q ≤ Y ⊔ P → Q ∈ lambdaSet R E := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  by_contra hno'
  have hno : ∀ E ∈ R, ¬ E ≤ Y ⊔ P → (∀ Q ∈ R, Q ≤ Y ⊔ P → Q ∈ lambdaSet R E) → False :=
    fun E hE hEL hall => hno' ⟨E, hE, hEL, hall⟩
  obtain ⟨C, hCs, hCl⟩ : ∃ C ∈ sigmaSet R Y, C ∉ lambdaSet R Y := by
    by_contra! hall
    exact hYne (Set.Subset.antisymm hall fun B hB => hB.1)
  have hCR : C ∈ R := hCs.1
  obtain ⟨F, hFl, hFC⟩ : ∃ F ∈ lambdaSet R Y, ¬ Commuting F C := by
    by_contra! hall
    have hCM : Commuting C (M R Y) := Commuting.sup_right hCs.2.2.symm
      (commuting_iff_le_centralizer.2 (iSup₂_le fun F hF =>
        commuting_iff_le_centralizer.1 (hall F hF).symm))
    have hmem : C ∈ {B | B ∈ R ∧ Commuting B (M R Y)} := ⟨hCR, hCM⟩
    rw [(Q_eq_M h hY).2.2.2.1] at hmem
    exact hCs.2.1 hmem
  have hFR : F ∈ R := hFl.1.1
  have hFCs : Special R F C := by
    have hne : F ≠ C := fun e => hFC (e ▸ hR.commuting_self hFR)
    rcases hR.rel F hFR C hCR hne with hc | ho | hs
    · exact absurd hc hFC
    · exact absurd hCs.2.2.symm
        (not_commuting_of_opposite_of_mem_lambdaSet hR hCR ho.symm (mem_lambdaSet_comm hY hFl))
    · exact hs
  set E := ⁅F, C⁆ with hE
  have hER : E ∈ R := hFCs.1
  obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hCR
  have hEle : E ≤ F ⊔ conjSub F c := commutator_le_sup_conjSub hR hiso hFR hCR hFCs hc hc1
  have hFcl : conjSub F c ∈ lambdaSet R Y := by
    have := conjSub_mem_lambdaSet hR hFl c
    rwa [conjSub_of_forall_commute fun y hy => (hCs.2.2 y hy c hc).symm] at this
  have hECl : E ∈ lambdaSet R C :=
    mem_lambdaSet_comm hER (mem_lambdaSet_commutator hR hiso hFR hCR hFCs).2
  have hEY : E ≠ Y := fun e => hCl (mem_lambdaSet_comm hCR (e ▸ hECl))
  have hEl : E ∈ lambdaSet R Y := by
    have hmem : E ∈ {B | B ∈ R ∧ B ≤ M R Y} :=
      ⟨hER, hEle.trans (sup_le (QD.le_M hFl) (QD.le_M hFcl))⟩
    rw [(Q_eq_M h hY).2.1] at hmem
    exact hmem.resolve_left hEY
  have hEQ : ∀ Q ∈ R, Q ≤ Y ⊔ P → Q ≠ Y → E ∈ lambdaSet R Q := by
    intro Q hQ hQle hQY
    have hQC : Commuting Q C := commuting_of_mem_sigmaSet h hY hP hno hCs hCl hQ hQle
    have hQF : Commuting Q F ∨ ⁅Q, F⁆ = Y :=
      (commuting_or_commutator_eq h hY hP hno hFR hFl.1.2.2 hQ hQle hQY).imp id fun h => h.2
    have hEQc : Commuting E Q := by
      rw [commuting_iff_commutator_eq_bot]
      refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
      · rw [commuting_iff_commutator_eq_bot.1 hQC.symm, Subgroup.commutator_bot_left]
      · rcases hQF with h1 | h1
        · rw [commuting_iff_commutator_eq_bot.1 h1, Subgroup.commutator_bot_left]
        · rw [h1]
          exact commuting_iff_commutator_eq_bot.1 hCs.2.2
    obtain ⟨hQl, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hY hP hY le_sup_left hQ hQle (Ne.symm hQY)
    have hCQ := mem_sigmaSet_notMem_of_le h hY hP hno hQ hQle hQY hCs hCl
    have hEQne : E ≠ Q := fun e => hCQ.2 (mem_lambdaSet_comm hCR (e ▸ hECl))
    by_contra hEQl
    have hYQl : Y ∈ lambdaSet R Q := mem_lambdaSet_comm hY hQl
    have hline : Q ⊔ Y = Y ⊔ P := (sup_comm Q Y).trans hsup
    have hno'' : ∀ E ∈ R, ¬ E ≤ Q ⊔ Y → (∀ Q' ∈ R, Q' ≤ Q ⊔ Y → Q' ∈ lambdaSet R E) → False := by
      rw [hline]
      exact hno
    exact (mem_sigmaSet_notMem_of_le h hQ hYQl hno'' hY le_sup_right (Ne.symm hQY)
      ⟨hER, hEQne, hEQc.symm⟩ hEQl).2 hEl
  refine hno E hER (fun hEL => (hEQ E hER hEL hEY).1.2.1 rfl) fun Q hQ hQle => ?_
  by_cases hQY : Q = Y
  · subst hQY
    exact mem_lambdaSet_comm hQ hEl
  · exact mem_lambdaSet_comm hQ (hEQ Q hQ hQle hQY)

end CFSG.Timmesfeld.ARS
