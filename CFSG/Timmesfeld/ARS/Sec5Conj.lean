module

public import CFSG.Timmesfeld.ARS.Sec5Elation

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec5

theorem card_conjSet (Δ : Set (Subgroup G)) (g : G) : Nat.card (conjSet Δ g) = Nat.card Δ :=
  Nat.card_image_of_injective (fun _ _ h => RankOne.map_conj_inj.1 h) Δ

theorem card_gen_conjSet (Δ : Set (Subgroup G)) (g : G) :
    Nat.card ↥(gen (conjSet Δ g)) = Nat.card ↥(gen Δ) := by
  rw [← conjSub_gen]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conjSet_inter (Δ Δ' : Set (Subgroup G)) (g : G) :
    conjSet (Δ ∩ Δ') g = conjSet Δ g ∩ conjSet Δ' g :=
  Set.image_inter fun _ _ h => RankOne.map_conj_inj.1 h

theorem isWeakTI_conjSet (hR : IsRootClass R) {Δ : Set (Subgroup G)} (hΔ : IsWeakTI R Δ)
    (g : G) : IsWeakTI R (conjSet Δ g) := by
  obtain ⟨h1, ⟨A, hA, B, hB, hAB⟩, h3, h4⟩ := hΔ
  refine ⟨?_, ⟨_, conjSub_mem_conjSet hA g, _, conjSub_mem_conjSet hB g,
    fun e => hAB (RankOne.map_conj_inj.1 e)⟩, ?_, ?_⟩
  · rintro _ ⟨X, hX, rfl⟩
    exact hR.conjSub_mem (h1 hX) g
  · intro hR'
    apply h3
    have hRg : conjSet R g⁻¹ = R := by
      refine Set.Subset.antisymm ?_ fun X hX => ?_
      · rintro _ ⟨X, hX, rfl⟩
        exact hR.conjSub_mem hX g⁻¹
      · refine ⟨conjSub X g, hR.conjSub_mem hX g, ?_⟩
        change conjSub (conjSub X g) g⁻¹ = X
        rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
    rw [← hRg, ← hR', conjSet_conjSet_inv]
  · intro d hd
    have hd' : g⁻¹ * d * g ∈ rootElts R := by
      obtain ⟨D, hD, hdD, hd1⟩ := hd
      refine ⟨conjSub D g⁻¹, hR.conjSub_mem hD g⁻¹, ?_, fun h => hd1 ?_⟩
      · have := conj_mem_conjSub g⁻¹ hdD
        rwa [inv_inv] at this
      · have : d = g * (g⁻¹ * d * g) * g⁻¹ := by group
        rw [this, h, mul_one, mul_inv_cancel]
    have e : conjSet (conjSet Δ g) d = conjSet (conjSet Δ (g⁻¹ * d * g)) g := by
      rw [← conjSet_mul, ← conjSet_mul, show g * (g⁻¹ * d * g) = d * g by group]
    rw [e, ← conjSet_inter]
    rcases h4 _ hd' with h | h
    · left
      rw [h]
      exact Set.image_empty _
    · right
      rw [h]

section Conj

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A) {Δ Δ' : Set (Subgroup G)}
include hR hiso hnd hΩ

theorem mem_lambdaSet_notMem (hΔ' : IsWeakTI R Δ') {A E : Subgroup G}
    (hint : ∀ X ∈ Δ, X ∈ Δ' → X = A) (hA' : A ∈ Δ') (hE : E ∈ Δ') (hEA : E ≠ A) :
    E ∈ lambdaSet R A ∧ E ∉ Δ :=
  ⟨mem_lambdaSet hR hiso hnd hΩ hΔ' hA' hE (Ne.symm hEA), fun h => hEA (hint E h hE)⟩

theorem axis_ne_of_not_le_sup (hΔ : IsWeakTI R Δ) (hΔ' : IsWeakTI R Δ') {A C C' : Subgroup G}
    (hA : A ∈ Δ) (hA' : A ∈ Δ') (hint : ∀ X ∈ Δ, X ∈ Δ' → X = A) (hC : C ∈ Δ') (hCA : C ≠ A)
    (hC' : C' ∈ Δ') (hC'A : C' ≠ A) (hC'le : ¬ C' ≤ A ⊔ C) : axis Δ C ≠ axis Δ C' := by
  intro hax
  obtain ⟨hCl, hCΔ⟩ := mem_lambdaSet_notMem hR hiso hnd hΩ hΔ' hint hA' hC hCA
  obtain ⟨hC'l, hC'Δ⟩ := mem_lambdaSet_notMem hR hiso hnd hΩ hΔ' hint hA' hC' hC'A
  have hCR : C ∈ R := hCl.1.1
  have hC'R : C' ∈ R := hC'l.1.1
  have hCC' : C ≠ C' := fun e => hC'le (e ▸ le_sup_right)
  have hC'C : C' ∈ lambdaSet R C := mem_lambdaSet hR hiso hnd hΩ hΔ' hC hC' hCC'
  obtain ⟨D, hD, hDC, hDCA⟩ := exists_special hR hiso hnd hΩ hΔ hA hCl hCΔ
  have hDC' : ¬ Commuting D C' := by
    rw [← le_axis_iff hD, ← hax, le_axis_iff hD]
    exact hDC.not_commuting hR
  obtain ⟨hDC's, hDC'A⟩ := special_of_not_commuting hR hiso hnd hΩ hΔ hA hC'l hC'Δ hD hDC'
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one (hΔ.1 hD)
  obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hCR
  have hdc : ⁅d, c⁆ ∈ A := hDCA ▸ Subgroup.commutator_mem_commutator hd hc
  obtain ⟨c', hc', hdc'⟩ := (bijOn_commutator hR hiso (hΔ.1 hD) hC'R hDC's hd hd1).surjOn
    (hDC'A.symm ▸ hdc : ⁅d, c⁆ ∈ ⁅D, C'⁆)
  have hdc'' : ⁅d, c'⁆ = ⁅d, c⁆ := hdc'
  have hcA : Commute c ⁅d, c'⁆ := (hCl.1.2.2 _ (hdc'' ▸ hdc) c hc).symm
  have hdx : ⁅d, c * c'⁆ = 1 := by
    have e : ⁅d, c * c'⁆ = ⁅d, c⁆ * (c * ⁅d, c'⁆ * c⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e, hcA.eq, mul_inv_cancel_right, hdc'']
    exact hR.mul_self A (hΔ.1 hA) _ hdc
  have hx1 : c * c' ≠ 1 := by
    intro h1
    have hmem : c ∈ C ⊓ C' := ⟨hc, by rw [eq_inv_of_mul_eq_one_left h1]; exact C'.inv_mem hc'⟩
    rw [inf_eq_bot hR hiso hCR hC'R hCC', Subgroup.mem_bot] at hmem
    exact hc1 hmem
  obtain ⟨C'', hC''R, hC''le, hxC''⟩ :=
    hC'C.2 _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hc')) hx1
  have hC''Δ' : C'' ∈ Δ' := mem_of_le_sup hR hiso hΔ' hC hC' hC'C hC''R hC''le
  have hC''A : C'' ≠ A := by
    intro h
    rw [h] at hC''le
    apply hC'le
    obtain ⟨-, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hCR hC'C hCR le_sup_left (hΔ.1 hA)
      hC''le hCA
    rw [sup_comm A C, hsup]
    exact le_sup_right
  obtain ⟨hC''l, hC''Δ⟩ := mem_lambdaSet_notMem hR hiso hnd hΩ hΔ' hint hA' hC''Δ' hC''A
  have hDC'' : Commuting D C'' := by
    by_contra h
    exact hd1 (eq_one_of_commute_of_special hR hiso hC''R (hΔ.1 hD)
      (special_of_not_commuting hR hiso hnd hΩ hΔ hA hC''l hC''Δ hD h).1.symm hxC'' hx1 hd
      (commutatorElement_eq_one_iff_mul_comm.1 hdx).symm)
  have hax'' : axis Δ C ≤ axis Δ C'' := by
    intro h hh
    refine mem_axis_of_commute hR hiso hnd hΩ hΔ hA hC''l hC''Δ (axis_le_gen Δ C hh) hxC'' hx1 ?_
    exact ((mem_axis.1 hh).2 c hc).mul_right ((mem_axis.1 (hax ▸ hh)).2 c' hc')
  obtain ⟨hsup, -⟩ := sup_axis_eq hR hiso hnd hΩ hΔ hA hCl hCΔ hD (hDC.not_commuting hR)
  exact not_gen_le_axis hR hiso hnd hΩ hΔ hA hC''l hC''Δ
    (hsup ▸ sup_le ((le_axis_iff hD).2 hDC'') hax'')

end Conj

end Sec5

end CFSG.Timmesfeld.ARS
