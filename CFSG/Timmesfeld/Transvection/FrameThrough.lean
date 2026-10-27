module

public import CFSG.Timmesfeld.Transvection.FrameExists

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)}

theorem IsFrame.comp_injective {r s : ℕ} {P Q : Fin r → Subgroup H} (hF : IsFrame Δ P Q)
    {e : Fin s → Fin r} (he : Function.Injective e) : IsFrame Δ (P ∘ e) (Q ∘ e) :=
  ⟨fun _ => hF.memP _, fun _ => hF.memQ _, fun _ => hF.opposite _,
    fun _ _ hij => hF.commuting _ _ (he.ne hij)⟩

theorem IsFrame.conj {r : ℕ} {P Q : Fin r → Subgroup H} (hF : IsFrame Δ P Q)
    (hR : IsRootClass Δ) (g : H) :
    IsFrame Δ (fun i => conjSub (P i) g) (fun i => conjSub (Q i) g) where
  memP i := hR.conjSub_mem (hF.memP i) g
  memQ i := hR.conjSub_mem (hF.memQ i) g
  opposite i := (hF.opposite i).conj g
  commuting i j hij := by
    have h := (hF.commuting i j hij).conjSub g
    simpa only [conjSub, Subgroup.map_sup] using h

theorem IsFrame.le_natCard_subgroup [Finite H] {r : ℕ} {P Q : Fin r → Subgroup H}
    (hF : IsFrame Δ P Q) : r ≤ Nat.card (Subgroup H) := by
  have hinj : Function.Injective P := by
    intro i j hij
    by_contra hne
    have hcomm : Commuting (P j) (Q i) :=
      (hF.commuting j i (Ne.symm hne)).mono le_sup_left le_sup_right
    rw [← hij] at hcomm
    exact ModelRank.not_commuting_of_opposite (hF.opposite i) hcomm
  have hcard := Nat.card_le_card_of_injective P hinj
  simpa using hcard

theorem exists_isFrame_forall_le (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) :
    ∃ m, 2 ≤ m ∧ (∃ P Q : Fin m → Subgroup H, IsFrame Δ P Q) ∧
      ∀ n, (∃ P Q : Fin n → Subgroup H, IsFrame Δ P Q) → n ≤ m := by
  classical
  haveI := h.finite
  obtain ⟨r, hr, P, Q, hF⟩ := exists_isMaxFrame h hML
  have hbound : ∀ n, (∃ P Q : Fin n → Subgroup H, IsFrame Δ P Q) →
      n ≤ Nat.card (Subgroup H) := by
    intro n hn
    obtain ⟨P, Q, hF⟩ := hn
    exact hF.le_natCard_subgroup
  let good : ℕ → Prop := fun n => ∃ P Q : Fin n → Subgroup H, IsFrame Δ P Q
  let m := Nat.findGreatest good (Nat.card (Subgroup H))
  have hm : 2 ≤ m :=
    hr.trans (Nat.le_findGreatest (P := good) (hbound r ⟨P, Q, hF.toIsFrame⟩)
      ⟨P, Q, hF.toIsFrame⟩)
  refine ⟨m, hm, ?_, fun n hn => Nat.le_findGreatest (P := good) (hbound n hn) hn⟩
  exact Nat.findGreatest_spec (P := good) (hbound r ⟨P, Q, hF.toIsFrame⟩)
    ⟨P, Q, hF.toIsFrame⟩

theorem exists_isMaxFrame_last (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    {A B : Subgroup H} (hA : A ∈ Δ) (hB : B ∈ Δ) (hAB : Opposite A B) :
    ∃ n, 1 ≤ n ∧ ∃ P Q : Fin (n + 1) → Subgroup H,
      IsMaxFrame Δ P Q ∧ P (Fin.last n) = A ∧ Q (Fin.last n) = B := by
  classical
  haveI := h.finite
  have hΔ := h.cls
  have hiso : NoIsolated Δ := hΔ.noIsolated h.points h.rank
  obtain ⟨m, hm, ⟨P, Q, hF⟩, hle⟩ := exists_isFrame_forall_le h hML
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨g, hg⟩ := hΔ.root.exists_conjSub_eq (hF.memP 0) hA
  have hF₀ := (hF.comp_injective (Fin.succ_injective n)).conj hΔ.root g
  have hXc : ∀ i : Fin n,
      Commuting A (conjSub (P i.succ) g) ∧ Commuting A (conjSub (Q i.succ) g) := by
    intro i
    rw [← hg]
    exact ⟨(hF.commuting_PP (Fin.succ_ne_zero i).symm).conjSub g,
      (hF.commuting_PQ (Fin.succ_ne_zero i).symm).conjSub g⟩
  obtain ⟨P', Q', hF', hP', hQ'⟩ := hF₀.exists_succ_last hΔ h.points hML hA hXc hB hAB
  refine ⟨n, by omega, P', Q', ⟨hF', fun X hX hXc' => ?_⟩, hP', hQ'⟩
  obtain ⟨Z, hZ, hXZ⟩ := hiso X hX
  obtain ⟨P'', Q'', hF''⟩ := hF'.exists_succ hΔ h.points hML hX hXc' hZ hXZ
  have := hle (n + 1 + 1) ⟨P'', Q'', hF''⟩
  omega

end CFSG.Timmesfeld.Transvection
