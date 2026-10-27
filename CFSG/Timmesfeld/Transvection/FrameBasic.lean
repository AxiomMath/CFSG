module

public import CFSG.Timmesfeld.Transvection.Frame
public import CFSG.Timmesfeld.Transvection.LineSpan
public import CFSG.Timmesfeld.Transvection.ModelRankBasic

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)} {r : ℕ} {P Q : Fin r → Subgroup G}

namespace IsFrame

section Pair

variable (h : IsFrame Δ P Q) {i j : Fin r} (hij : i ≠ j)
include h hij

theorem commuting_PP : Commuting (P i) (P j) :=
  (h.commuting i j hij).mono le_sup_left le_sup_left

theorem commuting_PQ : Commuting (P i) (Q j) :=
  (h.commuting i j hij).mono le_sup_left le_sup_right

theorem commuting_QP : Commuting (Q i) (P j) :=
  (h.commuting i j hij).mono le_sup_right le_sup_left

theorem commuting_QQ : Commuting (Q i) (Q j) :=
  (h.commuting i j hij).mono le_sup_right le_sup_right

theorem P_ne : P i ≠ P j := fun e =>
  ModelRank.not_commuting_of_opposite (h.opposite i) (e ▸ h.commuting_QP hij).symm

theorem Q_ne_P : Q i ≠ P j := fun e =>
  ModelRank.not_commuting_of_opposite (h.opposite j) (e ▸ h.commuting_QQ hij)

end Pair

variable (h : IsFrame Δ P Q) (hΔ : IsTransvectionClass Δ)
include h hΔ

theorem opposite_of_mem_lineOf [Finite G] (hpts : PointsDetermined Δ) {i j : Fin r}
    (hij : i ≠ j) {C : Subgroup G} (hC : C ∈ lineOf Δ (P i) (P j)) (hCj : C ≠ P j) :
    Opposite (Q i) C := by
  have hQC : Q i ≠ C := by
    rintro rfl
    exact ModelRank.not_commuting_of_opposite (h.opposite i)
      (commuting_of_mem_lineOf' hΔ (h.memP i) (h.memP j) (h.commuting_PP hij) hC).1
  rcases hΔ.commuting_or_opposite (h.memQ i) hC.1 hQC with hc | ho
  · exfalso
    have := commuting_of_commuting_of_mem_lineOf hΔ hpts (h.memP i) (h.memP j) (h.P_ne hij)
      (h.commuting_PP hij) hC (right_mem_lineOf (h.memP j)) hCj
      (left_mem_lineOf (h.memP i)) (h.memQ i) hc (h.commuting_QP hij)
    exact ModelRank.not_commuting_of_opposite (h.opposite i) this.symm
  · exact ho

end IsFrame

theorem exists_weylElt (hΔ : IsTransvectionClass Δ) {A E : Subgroup G} (hA : A ∈ Δ)
    (hE : E ∈ Δ) (hEA : Opposite E A) :
    ∃ w ∈ E ⊔ A, w * w = 1 ∧ conjSub A w = E ∧ conjSub E w = A := by
  obtain ⟨e, he, he1⟩ := hΔ.root.exists_ne_one hE
  have ha := partner_mem hEA he he1
  have haa : partner E A e * partner E A e = 1 := hΔ.root.mul_self A hA _ ha
  have hee : e * e = 1 := hΔ.root.mul_self E hE e he
  have hw := conjSub_wElt hΔ hE hEA he he1
  refine ⟨partner E A e * e * partner E A e, ?_, Aux.coxeter_w_sq haa hee, ?_, hw⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right ha)
      (Subgroup.mem_sup_left he)) (Subgroup.mem_sup_right ha)
  · have h1 : conjSub A (partner E A e * e * partner E A e) =
        conjSub (conjSub E (partner E A e * e * partner E A e))
          (partner E A e * e * partner E A e) := by rw [hw]
    rw [h1, ← conjSub_mul, Aux.coxeter_w_sq haa hee, conjSub_one]

theorem IsFrame.comp_equiv {s : ℕ} (h : IsFrame Δ P Q) (e : Fin s ≃ Fin r) :
    IsFrame Δ (P ∘ e) (Q ∘ e) :=
  ⟨fun _ => h.memP _, fun _ => h.memQ _, fun _ => h.opposite _,
    fun _ _ hij => h.commuting _ _ (e.injective.ne hij)⟩

theorem IsSmallFrame.comp_equiv {s : ℕ} {k : Fin r} (h : IsSmallFrame Δ P Q k) (e : Fin s ≃ Fin r) :
    IsSmallFrame Δ (P ∘ e) (Q ∘ e) (e.symm k) := by
  refine ⟨h.toIsFrame.comp_equiv e, fun X hX hc => ?_⟩
  have := h.residue X hX fun i hi => by
    have hi' : e.symm i ≠ e.symm k := fun h' => hi (e.symm.injective h')
    have := hc (e.symm i) hi'
    simpa using this
  simpa using this

theorem IsSmallFrame.exists_last {k : Fin r} (h : IsSmallFrame Δ P Q k) (hr : 1 ≤ r) :
    ∃ P' Q' : Fin r → Subgroup G, IsSmallFrame Δ P' Q' ⟨r - 1, by omega⟩ ∧
      (∀ i, ∃ j, P' i = P j ∧ Q' i = Q j) := by
  set e : Fin r ≃ Fin r := Equiv.swap k ⟨r - 1, by omega⟩ with he
  refine ⟨P ∘ e, Q ∘ e, ?_, fun i => ⟨e i, rfl, rfl⟩⟩
  have := h.comp_equiv e
  rwa [he, Equiv.symm_swap, Equiv.swap_apply_left] at this

end CFSG.Timmesfeld.Transvection
