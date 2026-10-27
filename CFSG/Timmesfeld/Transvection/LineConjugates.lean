module

public import CFSG.Timmesfeld.Transvection.FrameResidue
import CFSG.Timmesfeld.Transvection.OddDetermination

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)}

theorem IsFrame.lineOf_subset_frameResidue {r : ℕ} {P Q : Fin r → Subgroup H}
    (hF : IsFrame Δ P Q) (j : Fin r) : lineOf Δ (P j) (Q j) ⊆ frameResidue Δ P Q j := by
  intro D hD
  exact ⟨hD.1, fun i hi => ⟨(hD.2 (P i) (hF.memP i) (hF.commuting_PP hi)
    (hF.commuting_PQ hi)).symm, (hD.2 (Q i) (hF.memQ i) (hF.commuting_QP hi)
    (hF.commuting_QQ hi)).symm⟩⟩

theorem insert_image_conjSub_subset_lineOf (hΔ : IsTransvectionClass Δ) {A B : Subgroup H}
    (hA : A ∈ Δ) (hB : B ∈ Δ) :
    insert B ((fun b => conjSub A b) '' (B : Set H)) ⊆ lineOf Δ A B := by
  intro Y hY
  rcases Set.mem_insert_iff.1 hY with rfl | hY
  · exact right_mem_lineOf hB
  · obtain ⟨b, hb, rfl⟩ := hY
    refine ⟨hΔ.root.conjSub_mem hA b, fun X hX hXA hXB => ?_⟩
    have hXb : conjSub X b = X :=
      conjSub_of_forall_commute fun x hx => (hXB x hx b hb).symm
    have h1 := hXA.conjSub b
    rwa [hXb] at h1

theorem ncard_insert_image_conjSub [Finite H] (hΔ : IsTransvectionClass Δ) {A B : Subgroup H}
    (hA : A ∈ Δ) (hB : B ∈ Δ) (hAB : Opposite A B) :
    (insert B ((fun b => conjSub A b) '' (B : Set H))).ncard = Nat.card A + 1 := by
  have hinj : Set.InjOn (fun b => conjSub A b) (B : Set H) := by
    intro x hx y hy hxy
    change conjSub A x = conjSub A y at hxy
    have hmul : x⁻¹ * y ∈ B := B.mul_mem (B.inv_mem hx) hy
    have h1 : conjSub A (x⁻¹ * y) = A := by
      rw [conjSub_mul, ← hxy, Aux.conjSub_conjSub_inv]
    exact inv_mul_eq_one.1 (hAB.symm.eq_one_of_conjSub_eq hmul h1)
  have hnot : B ∉ (fun b => conjSub A b) '' (B : Set H) := by
    rintro ⟨x, hx, hxe⟩
    have hA' : A = conjSub B x⁻¹ := by rw [← hxe, Aux.conjSub_conjSub_inv]
    exact hAB.ne (hA'.trans (conjSub_of_mem (B.inv_mem hx)))
  rw [Set.ncard_insert_of_notMem hnot, hinj.ncard_image, ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe, hΔ.root.card_eq hB hA]

theorem le_sup_of_mem_insert_image_conjSub {A B Y : Subgroup H}
    (hY : Y ∈ insert B ((fun b => conjSub A b) '' (B : Set H))) : Y ≤ A ⊔ B := by
  rcases Set.mem_insert_iff.1 hY with rfl | hY
  · exact le_sup_right
  · obtain ⟨b, hb, rfl⟩ := hY
    exact conjSub_le le_sup_left (Subgroup.mem_sup_right hb)

theorem mem_insert_image_conjSub_of_le [Finite H] (hΔ : IsTransvectionClass Δ)
    {A B Y : Subgroup H} (hB : B ∈ Δ) (hAB : Opposite A B) (hY : Y ∈ Δ) (hle : Y ≤ A ⊔ B) :
    Y ∈ insert B ((fun b => conjSub A b) '' (B : Set H)) := by
  by_cases hYB : Y = B
  · exact Set.mem_insert_iff.2 (Or.inl hYB)
  · obtain ⟨b, hb, hbY⟩ :=
      Opposite.exists_mem_eq_conjSub hΔ.root hB hY hAB.symm (hle.trans (sup_comm A B).le) hYB
    exact Set.mem_insert_of_mem _ ⟨b, hb, hbY.symm⟩

theorem lineOf_eq_insert_of_ncard_le [Finite H] (hΔ : IsTransvectionClass Δ) {A B : Subgroup H}
    (hA : A ∈ Δ) (hB : B ∈ Δ) (hAB : Opposite A B)
    (hle : (lineOf Δ A B).ncard ≤ Nat.card A + 1) :
    lineOf Δ A B = insert B ((fun b => conjSub A b) '' (B : Set H)) := by
  refine (Set.eq_of_subset_of_ncard_le (insert_image_conjSub_subset_lineOf hΔ hA hB) ?_).symm
  rw [ncard_insert_image_conjSub hΔ hA hB hAB]
  exact hle

theorem IsSmallFrame.lineOf_eq [Finite H] (hΔ : IsTransvectionClass Δ) {r : ℕ}
    {P Q : Fin r → Subgroup H} {k : Fin r} (hF : IsSmallFrame Δ P Q k) :
    lineOf Δ (P k) (Q k) = insert (Q k) ((fun b => conjSub (P k) b) '' (Q k : Set H)) ∧
      ∀ Y ∈ lineOf Δ (P k) (Q k), Y ≤ P k ⊔ Q k := by
  have hle : ∀ Y ∈ lineOf Δ (P k) (Q k), Y ≤ P k ⊔ Q k := fun Y hY =>
    hF.residue Y hY.1 (hF.toIsFrame.lineOf_subset_frameResidue k hY).2
  exact ⟨Set.Subset.antisymm
      (fun Y hY => mem_insert_image_conjSub_of_le hΔ (hF.memQ k) (hF.opposite k) hY.1 (hle Y hY))
      (insert_image_conjSub_subset_lineOf hΔ (hF.memP k) (hF.memQ k)), hle⟩

end CFSG.Timmesfeld.Transvection
