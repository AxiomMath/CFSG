module

public import CFSG.Timmesfeld.ARS.CaseHCount
public import CFSG.Timmesfeld.ARS.Singular

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

section Flag

variable (h : Hyp G R) (hH : SigmaEqLambda R)
include h hH

omit h hH in
theorem gen_pair (E D : Subgroup G) : gen {E, D} = E ⊔ D :=
  le_antisymm (gen_le fun B hB => by rcases hB with rfl | rfl; exacts [le_sup_left, le_sup_right])
    (sup_le (le_gen (Set.mem_insert _ _)) (le_gen (Set.mem_insert_of_mem _ rfl)))

theorem mem_normSet_of_mem_lambdaSet {E D X : Subgroup G} (hE : E ∈ R)
    (hD : D ∈ lambdaSet R E) (hX : X ∈ lambdaSet R E) (hXV : ¬ X ≤ E ⊔ D) :
    X ∈ normSet R (E ⊔ D) ∧ ¬ Commuting X (E ⊔ D) := by
  have hXR : X ∈ R := hX.1.1
  refine ⟨⟨hXR, fun x hx => ?_⟩, fun hc => hXV (le_of_commuting_line h hH hE hD hXR hc)⟩
  by_cases hx1 : x = 1
  · rw [hx1, conjSub_one]
  refine conjSub_line_eq h hH hE hD hXR hx hx1 hE le_sup_left ?_
  rw [conjSub_of_forall_commute fun e he => (hX.1.2.2 e he x hx).symm]
  exact le_sup_left

theorem exists_conj_of_mem_lambdaSet {E D X Y : Subgroup G} (hE : E ∈ R)
    (hD : D ∈ lambdaSet R E) (hX : X ∈ lambdaSet R E) (hXV : ¬ X ≤ E ⊔ D)
    (hY : Y ∈ lambdaSet R E) (hYV : ¬ Y ≤ E ⊔ D) :
    ∃ g : G, conjSub (E ⊔ D) g = E ⊔ D ∧ conjSub E g = E ∧ conjSub X g = Y := by
  have := h.finite
  have hR := h.root
  have hDR : D ∈ R := hD.1.1
  set S : Set (Subgroup G) := {E, D} with hSdef
  have hSR : S ⊆ R := by
    rintro B (rfl | rfl)
    exacts [hE, hDR]
  have hcol : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → Q ∈ lambdaSet R P := by
    rintro P (rfl | rfl) Q (rfl | rfl) hPQ
    · exact absurd rfl hPQ
    · exact hD
    · exact mem_lambdaSet_comm hE hD
    · exact absurd rfl hPQ
  have hgen : gen S = E ⊔ D := gen_pair E D
  obtain ⟨hXn, hXc⟩ := mem_normSet_of_mem_lambdaSet h hH hE hD hX hXV
  obtain ⟨hYn, hYc⟩ := mem_normSet_of_mem_lambdaSet h hH hE hD hY hYV
  rw [← hgen] at hXn hXc hYn hYc
  have hpath := Singular.reflTransGen_oppGraph h hSR hcol hXn hYn hXc hYc
  obtain ⟨g, hg, hgXY⟩ := Sec3.exists_conjSub_eq_of_reflTransGen hR (fun B hB => hB.1) hpath
  have hgN : g ∈ Subgroup.normalizer ((E ⊔ D : Subgroup G) : Set G) := by
    refine (iSup₂_le fun B hB => ?_ : (⨆ B ∈ {B | Relation.ReflTransGen
      (oppGraph (normSet R (gen S))) X B}, B) ≤ _) hg
    have hBn : B ∈ normSet R (gen S) := by
      rcases Relation.ReflTransGen.cases_tail hB with rfl | ⟨_, -, hlast⟩
      · exact hXn
      · exact hlast.2.1
    rw [hgen] at hBn
    exact fun b hb => conjSub_eq_self_iff.1 (hBn.2 b hb)
  have hgV : conjSub (E ⊔ D) g = E ⊔ D := conjSub_eq_self_iff.2 hgN
  refine ⟨g, hgV, ?_, hgXY⟩
  have hEg : conjSub E g ≤ E ⊔ D := by
    rw [← hgV]
    exact Subgroup.map_mono le_sup_left
  have hEgY : conjSub E g ∈ lambdaSet R Y := by
    rw [← hgXY]
    exact conjSub_mem_lambdaSet hR (mem_lambdaSet_comm hE hX) g
  by_contra hne
  exact hYV (le_line h hH hE hD (hR.conjSub_mem hE g) hEg hE le_sup_left hne hY.1.1
    hEgY.1.2.2 hY.1.2.2.symm)

theorem exists_conj_line {E V W W' : Subgroup G} (hE : E ∈ R) (hV : V ∈ linesThrough R E)
    (hW : W ∈ linesThrough R E) (hW' : W' ∈ linesThrough R E) (hWV : W ≠ V) (hW'V : W' ≠ V) :
    ∃ g : G, conjSub E g = E ∧ conjSub V g = V ∧ conjSub W g = W' := by
  obtain ⟨D, hD, rfl⟩ := (mem_linesThrough_iff h hE).1 hV
  obtain ⟨X, hX, rfl⟩ := (mem_linesThrough_iff h hE).1 hW
  obtain ⟨Y, hY, rfl⟩ := (mem_linesThrough_iff h hE).1 hW'
  have hoff : ∀ {Z : Subgroup G}, Z ∈ lambdaSet R E → E ⊔ Z ≠ E ⊔ D → ¬ Z ≤ E ⊔ D := by
    intro Z hZ hne hle
    exact hne (eq_of_le_of_le h hE hZ hE hD hE hZ.1.1 hZ.1.2.1.symm le_sup_left le_sup_right
      le_sup_left hle)
  obtain ⟨g, hgV, hgE, hgXY⟩ := exists_conj_of_mem_lambdaSet h hH hE hD hX (hoff hX hWV) hY
    (hoff hY hW'V)
  refine ⟨g, hgE, hgV, ?_⟩
  change (E ⊔ X).map _ = _
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) hgE hgXY

end Flag

end CaseH

end CFSG.Timmesfeld.ARS
