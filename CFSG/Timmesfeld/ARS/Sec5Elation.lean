module

public import CFSG.Timmesfeld.ARS.Sec5Centralizer

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec5

theorem exists_mem_notMem_notMem {V H K : Subgroup G} (hH : ¬ V ≤ H) (hK : ¬ V ≤ K) :
    ∃ x ∈ V, x ∉ H ∧ x ∉ K := by
  obtain ⟨h, hhV, hhH⟩ := IsConcreteLE.not_le_iff_exists.1 hH
  obtain ⟨k, hkV, hkK⟩ := IsConcreteLE.not_le_iff_exists.1 hK
  by_cases h1 : h ∈ K
  · by_cases h2 : k ∈ H
    · refine ⟨h * k, V.mul_mem hhV hkV, fun hm => hhH ?_, fun hm => hkK ?_⟩
      · simpa using H.mul_mem hm (H.inv_mem h2)
      · simpa using K.mul_mem (K.inv_mem h1) hm
    · exact ⟨k, hkV, h2, hkK⟩
  · exact ⟨h, hhV, hhH, h1⟩

theorem opposite_conjSub_self {B E : Subgroup G} (h : Opposite B E) {e : G} (he : e ∈ E)
    (he1 : e ≠ 1) : Opposite B (conjSub B e) := by
  obtain ⟨b, hb, -, hbe⟩ := h.2.2 e he he1
  have := Sec3.opposite_conjSub h b
  rwa [conjSub_of_mem hb, hbe] at this

@[expose] def axis (Δ : Set (Subgroup G)) (E : Subgroup G) : Subgroup G :=
  gen Δ ⊓ Subgroup.centralizer (E : Set G)

theorem mem_axis {Δ : Set (Subgroup G)} {E : Subgroup G} {x : G} :
    x ∈ axis Δ E ↔ x ∈ gen Δ ∧ ∀ e ∈ E, Commute x e := by
  rw [axis, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact and_congr_right fun _ => forall₂_congr fun e _ => ⟨fun h => h.symm, fun h => h.symm⟩

theorem axis_le_gen (Δ : Set (Subgroup G)) (E : Subgroup G) : axis Δ E ≤ gen Δ := inf_le_left

section Elation

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A) {Δ : Set (Subgroup G)}
include hR hiso hnd hΩ

theorem special_of_not_commuting (hΔ : IsWeakTI R Δ) {P E D : Subgroup G} (hP : P ∈ Δ)
    (hE : E ∈ lambdaSet R P) (hEΔ : E ∉ Δ) (hD : D ∈ Δ) (hDE : ¬ Commuting D E) :
    Special R D E ∧ ⁅D, E⁆ = P := by
  have hDR := hΔ.1 hD
  have hER : E ∈ R := hE.1.1
  have hne : D ≠ E := fun e => hEΔ (e ▸ hD)
  have hs : Special R D E := by
    rcases hR.rel D hDR E hER hne with h | h | h
    · exact absurd h hDE
    · exact absurd (commuting_of_mem hR hiso hnd hΔ hD hP)
        (not_commuting_of_opposite_of_mem_lambdaSet hR hDR h (mem_lambdaSet_comm (hΔ.1 hP) hE))
    · exact h
  exact ⟨hs, QD.eq_of_le_of_mem hR hiso hs.1 (hΔ.1 hP)
    ((Subgroup.commutator_mono (le_gen hD) le_rfl).trans
      (commutator_gen_le hR hiso hnd hΩ hΔ hP hE))⟩

theorem exists_special (hΔ : IsWeakTI R Δ) {P E : Subgroup G} (hP : P ∈ Δ)
    (hE : E ∈ lambdaSet R P) (hEΔ : E ∉ Δ) : ∃ D ∈ Δ, Special R D E ∧ ⁅D, E⁆ = P := by
  obtain ⟨D, hD, hDE⟩ : ∃ D ∈ Δ, ¬ Commuting D E := by
    by_contra! h
    exact hEΔ (mem_of_commuting_gen hR hiso hnd hΩ hΔ hE.1.1 (commuting_iff_le_centralizer.2
      (gen_le fun D hD => commuting_iff_le_centralizer.1 (h D hD).symm)))
  exact ⟨D, hD, special_of_not_commuting hR hiso hnd hΩ hΔ hP hE hEΔ hD hDE⟩

theorem commutator_gen_eq (hΔ : IsWeakTI R Δ) {P E : Subgroup G} (hP : P ∈ Δ)
    (hE : E ∈ lambdaSet R P) (hEΔ : E ∉ Δ) : ⁅gen Δ, E⁆ = P := by
  refine le_antisymm (commutator_gen_le hR hiso hnd hΩ hΔ hP hE) ?_
  obtain ⟨D, hD, -, hDE⟩ := exists_special hR hiso hnd hΩ hΔ hP hE hEΔ
  rw [← hDE]
  exact Subgroup.commutator_mono (le_gen hD) le_rfl

theorem mem_axis_of_commute (hΔ : IsWeakTI R Δ) {P E : Subgroup G} (hP : P ∈ Δ)
    (hE : E ∈ lambdaSet R P) (hEΔ : E ∉ Δ) {x e : G} (hx : x ∈ gen Δ) (he : e ∈ E)
    (he1 : e ≠ 1) (hxe : Commute x e) : x ∈ axis Δ E := by
  refine mem_axis.2 ⟨hx, fun e' he' => ?_⟩
  by_cases hx1 : x = 1
  · rw [hx1]
    exact Commute.one_left e'
  obtain ⟨D, hD, -, hxD⟩ := exists_mem_le_of_mem_gen hR hiso hnd hΩ hΔ subset_rfl hx hx1
  by_cases hDE : Commuting D E
  · exact hDE x hxD e' he'
  · exact absurd (eq_one_of_commute_of_special hR hiso (hΔ.1 hD) hE.1.1
      (special_of_not_commuting hR hiso hnd hΩ hΔ hP hE hEΔ hD hDE).1 hxD hx1 he hxe) he1

omit [Finite G] hR hiso hnd hΩ in
theorem le_axis_iff {E D : Subgroup G} (hD : D ∈ Δ) : D ≤ axis Δ E ↔ Commuting D E :=
  ⟨fun h _ hx e he => (mem_axis.1 (h hx)).2 e he,
    fun h x hx => mem_axis.2 ⟨le_gen hD hx, fun e he => h x hx e he⟩⟩

theorem exists_mem_le_axis (hΔ : IsWeakTI R Δ) {P E : Subgroup G} (hP : P ∈ Δ)
    (hE : E ∈ lambdaSet R P) (hEΔ : E ∉ Δ) {x : G} (hx : x ∈ axis Δ E) (hx1 : x ≠ 1) :
    ∃ D ∈ Δ, D ≤ axis Δ E ∧ x ∈ D := by
  obtain ⟨D, hD, -, hxD⟩ :=
    exists_mem_le_of_mem_gen hR hiso hnd hΩ hΔ subset_rfl (axis_le_gen Δ E hx) hx1
  refine ⟨D, hD, (le_axis_iff hD).2 ?_, hxD⟩
  by_contra hDE
  obtain ⟨e, he, he1⟩ := hR.exists_ne_one hE.1.1
  exact he1 (eq_one_of_commute_of_special hR hiso (hΔ.1 hD) hE.1.1
    (special_of_not_commuting hR hiso hnd hΩ hΔ hP hE hEΔ hD hDE).1 hxD hx1 he
    ((mem_axis.1 hx).2 e he))

omit [Finite G] hR hiso hnd hΩ in
theorem le_axis_self {P E : Subgroup G} (hP : P ∈ Δ) (hE : E ∈ lambdaSet R P) :
    P ≤ axis Δ E :=
  (le_axis_iff hP).2 hE.1.2.2

theorem not_gen_le_axis (hΔ : IsWeakTI R Δ) {P E : Subgroup G} (hP : P ∈ Δ)
    (hE : E ∈ lambdaSet R P) (hEΔ : E ∉ Δ) : ¬ gen Δ ≤ axis Δ E := fun h => by
  obtain ⟨D, hD, hs, -⟩ := exists_special hR hiso hnd hΩ hΔ hP hE hEΔ
  exact hs.not_commuting hR ((le_axis_iff hD).1 ((le_gen hD).trans h))

theorem sup_axis_eq (hΔ : IsWeakTI R Δ) {P E D : Subgroup G} (hP : P ∈ Δ)
    (hE : E ∈ lambdaSet R P) (hEΔ : E ∉ Δ) (hD : D ∈ Δ) (hDE : ¬ Commuting D E) :
    D ⊔ axis Δ E = gen Δ ∧ D ⊓ axis Δ E = ⊥ := by
  obtain ⟨hs, hDP⟩ := special_of_not_commuting hR hiso hnd hΩ hΔ hP hE hEΔ hD hDE
  have hER : E ∈ R := hE.1.1
  obtain ⟨e, he, he1⟩ := hR.exists_ne_one hER
  have hV : Commuting (gen Δ) (gen Δ) := commuting_gen_of_isWeakTI_of hR hiso hnd hΔ
  refine ⟨le_antisymm (sup_le (le_gen hD) (axis_le_gen Δ E)) fun v hv => ?_, ?_⟩
  ·
    have hve : ⁅v, e⁆ ∈ ⁅D, E⁆ := by
      rw [hDP]
      exact commutator_gen_le hR hiso hnd hΩ hΔ hP hE
        (Subgroup.commutator_mem_commutator hv he)
    obtain ⟨d, hd, hde⟩ := (bijOn_commutator_left hR hiso (hΔ.1 hD) hER hs he he1).surjOn hve
    have hde' : ⁅d, e⁆ = ⁅v, e⁆ := hde
    have hdeP : ⁅d, e⁆ ∈ P := hDP ▸ Subgroup.commutator_mem_commutator hd he
    have hcomm : Commute v ⁅d, e⁆ := hV v hv _ (le_gen hP hdeP)
    have hvd : ⁅v * d, e⁆ = 1 := by
      rw [Plane.commutatorElement_mul_left_of_commute hcomm, hde']
      exact hR.mul_self _ hs.1 _ hve
    have hmem := mem_axis_of_commute hR hiso hnd hΩ hΔ hP hE hEΔ
      ((gen Δ).mul_mem hv (le_gen hD hd)) he he1 (commutatorElement_eq_one_iff_mul_comm.1 hvd)
    have : v = (v * d) * d⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hmem) (Subgroup.mem_sup_left (D.inv_mem hd))
  · refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    by_contra hx1
    exact he1 (eq_one_of_commute_of_special hR hiso (hΔ.1 hD) hER hs hx.1 hx1 he
      ((mem_axis.1 hx.2).2 e he))

theorem card_gen_eq (hΔ : IsWeakTI R Δ) {P E : Subgroup G} (hP : P ∈ Δ)
    (hE : E ∈ lambdaSet R P) (hEΔ : E ∉ Δ) :
    Nat.card ↥(gen Δ) = Nat.card P * Nat.card ↥(axis Δ E) := by
  obtain ⟨D, hD, hs, -⟩ := exists_special hR hiso hnd hΩ hΔ hP hE hEΔ
  obtain ⟨hsup, hinf⟩ := sup_axis_eq hR hiso hnd hΩ hΔ hP hE hEΔ hD (hs.not_commuting hR)
  have hcomm : Commuting D (axis Δ E) :=
    (commuting_gen_of_isWeakTI_of hR hiso hnd hΔ).mono (le_gen hD) (axis_le_gen Δ E)
  rw [← hsup, le_antisymm (card_sup_le_of_commuting hcomm) (card_mul_card_le_card_sup hinf),
    hR.card_eq (hΔ.1 hD) (hΔ.1 hP)]

theorem exists_mem_lambdaSet_of_commuting (hΔ : IsWeakTI R Δ) {E D₀ : Subgroup G} (hE : E ∈ R)
    (hEΔ : E ∉ Δ) (hD₀ : D₀ ∈ Δ) (hED₀ : Commuting E D₀) : ∃ P ∈ Δ, E ∈ lambdaSet R P := by
  obtain ⟨D, hD, hDE⟩ : ∃ D ∈ Δ, ¬ Commuting D E := by
    by_contra! h
    exact hEΔ (mem_of_commuting_gen hR hiso hnd hΩ hΔ hE (commuting_iff_le_centralizer.2
      (gen_le fun D hD => commuting_iff_le_centralizer.1 (h D hD).symm)))
  have hDR := hΔ.1 hD
  have hne : D ≠ E := fun e => hEΔ (e ▸ hD)
  have hs : Special R D E := by
    rcases hR.rel D hDR E hE hne with h | h | h
    · exact absurd h hDE
    · obtain ⟨e, he, he1⟩ := hR.exists_ne_one hE
      exact absurd (opposite_conjSub_self h he he1) (not_opposite_of_isWeakTI hR hiso hnd hΔ hD
        (conjSub_mem_of_commuting hR hΔ hE hD₀ hED₀ he hD))
    · exact h
  exact ⟨_, commutator_mem hR hiso hΔ hD hE hD₀ hED₀ hs,
    (mem_lambdaSet_commutator hR hiso hDR hE hs).2⟩

theorem commuting_centre_of_commuting (hΔ : IsWeakTI R Δ) {P E E' : Subgroup G} (hP : P ∈ Δ)
    (hE : E ∈ lambdaSet R P) (hEΔ : E ∉ Δ) (hE' : E' ∈ R) (hE's : E' ≤ stabSet Δ)
    (hEE' : Commuting E E') : Commuting E' P := by
  refine Sec3.commuting_of_forall_conjSub_eq hR hE' (hΔ.1 hP) (fun e' he' => ?_) hiso
  have hgen : conjSub (gen Δ) e' = gen Δ := by rw [conjSub_gen, mem_stabSet.1 (hE's he')]
  have hEe : conjSub E e' = E := conjSub_of_forall_commute fun x hx => (hEE' x hx e' he').symm
  rw [← commutator_gen_eq hR hiso hnd hΩ hΔ hP hE hEΔ, conjSub, Subgroup.map_commutator, ← conjSub,
    ← conjSub, hgen, hEe]

theorem opposite_of_centre (hΔ : IsWeakTI R Δ) {P P' E E' : Subgroup G} (hP : P ∈ Δ)
    (hP' : P' ∈ Δ) (hPP' : P ≠ P') (hE : E ∈ lambdaSet R P) (hEΔ : E ∉ Δ)
    (hE' : E' ∈ lambdaSet R P') (hE'Δ : E' ∉ Δ) (h1 : ¬ Commuting P E')
    (h2 : ¬ Commuting P' E) : Opposite E E' := by
  have hER : E ∈ R := hE.1.1
  have hE'R : E' ∈ R := hE'.1.1
  have hEs : E ≤ stabSet Δ := le_stabSet_of_commuting hR hΔ hER hP hE.1.2.2.symm
  have hE's : E' ≤ stabSet Δ := le_stabSet_of_commuting hR hΔ hE'R hP' hE'.1.2.2.symm
  obtain ⟨-, hPE'⟩ := special_of_not_commuting hR hiso hnd hΩ hΔ hP' hE' hE'Δ hP h1
  obtain ⟨-, hP'E⟩ := special_of_not_commuting hR hiso hnd hΩ hΔ hP hE hEΔ hP' h2
  have hne : E ≠ E' := by
    rintro rfl
    exact hPP' ((commutator_gen_eq hR hiso hnd hΩ hΔ hP hE hEΔ).symm.trans
      (commutator_gen_eq hR hiso hnd hΩ hΔ hP' hE' hE'Δ))
  rcases hR.rel E hER E' hE'R hne with h | h | h
  · exact absurd (commuting_centre_of_commuting hR hiso hnd hΩ hΔ hP hE hEΔ hE'R hE's h).symm h1
  · exact h
  ·
    exfalso
    have hl : Commuting (P ⊔ P') (P ⊔ P') :=
      (commuting_gen_of_isWeakTI_of hR hiso hnd hΔ).mono (sup_le (le_gen hP) (le_gen hP'))
        (sup_le (le_gen hP) (le_gen hP'))
    have hlP : IsPGroup 2 ↥(P ⊔ P') := isPGroup_sup_of_commuting (hR.isPGroup (hΔ.1 hP))
      (hR.isPGroup (hΔ.1 hP')) (hl.mono le_sup_left le_sup_right)
    have hnorm : ∀ {F Q Q' : Subgroup G}, F ∈ lambdaSet R Q → ⁅Q', F⁆ ≤ Q →
        F ≤ Subgroup.normalizer ((Q ⊔ Q' : Subgroup G) : Set G) := by
      intro F Q Q' hF hle
      refine le_normalizer_of_conjSub_le fun f hf => ?_
      rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub,
        conjSub_of_forall_commute fun x hx => (hF.1.2.2 x hx f hf).symm]
      exact sup_le le_sup_left ((conjSub_le_commutator_sup hf).trans (sup_le (hle.trans
        le_sup_left) le_sup_right))
    have hEn : E ⊔ E' ≤ Subgroup.normalizer ((P ⊔ P' : Subgroup G) : Set G) :=
      sup_le (hnorm hE hP'E.le) ((sup_comm P P').symm ▸ hnorm hE' hPE'.le)
    have hK : IsPGroup 2 ↥(P ⊔ P' ⊔ (E ⊔ E')) :=
      IsPGroup.to_sup_of_normal_left' hlP (h.isPGroup_sup hR hER hE'R) hEn
    obtain ⟨B, hB, hB'⟩ := QD.exists_forall_not_le_commutator hK (P := {P, P'})
      (fun B hB => by
        rcases hB with rfl | rfl
        · exact le_sup_left.trans le_sup_left
        · exact le_sup_right.trans le_sup_left)
      (fun B hB => by
        rcases hB with rfl | rfl
        · exact hR.ne_bot _ (hΔ.1 hP)
        · exact hR.ne_bot _ (hΔ.1 hP'))
      (Set.mem_insert P _)
    rcases hB with rfl | rfl
    · exact hB' P' (Set.mem_insert_of_mem _ rfl)
        (hPE' ▸ Subgroup.commutator_mono le_rfl (le_sup_right.trans le_sup_right))
    · exact hB' P (Set.mem_insert _ _)
        (hP'E ▸ Subgroup.commutator_mono le_rfl (le_sup_left.trans le_sup_right))

theorem special_of_centre (hΔ : IsWeakTI R Δ) {P P' E E' : Subgroup G} (hP : P ∈ Δ)
    (hP' : P' ∈ Δ) (hE : E ∈ lambdaSet R P) (hE' : E' ∈ lambdaSet R P') (hE'Δ : E' ∉ Δ)
    (h1 : Commuting P E') (h2 : ¬ Commuting P' E) : Special R E E' := by
  have hER : E ∈ R := hE.1.1
  have hE'R : E' ∈ R := hE'.1.1
  have hEs : E ≤ stabSet Δ := le_stabSet_of_commuting hR hΔ hER hP hE.1.2.2.symm
  have hnc : ¬ Commuting E E' := fun h =>
    h2 (commuting_centre_of_commuting hR hiso hnd hΩ hΔ hP' hE' hE'Δ hER hEs h.symm).symm
  have hne : E ≠ E' := fun e => hnc (e ▸ hR.commuting_self hER)
  rcases hR.rel E hER E' hE'R hne with h | h | h
  · exact absurd h hnc
  · exact absurd h1.symm
      (not_commuting_of_opposite_of_mem_lambdaSet hR hE'R h.symm (mem_lambdaSet_comm (hΔ.1 hP) hE))
  · exact h

end Elation

end Sec5

end CFSG.Timmesfeld.ARS
