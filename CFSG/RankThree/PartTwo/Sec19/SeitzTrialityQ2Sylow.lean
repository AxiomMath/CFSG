module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Pairs

public section

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.AGLEmbedding.ChevOuter HuppertD4Q2

namespace CFSG.RankThree.PartTwo.Sec19.TrialityTwo

section Sylow

@[expose] noncomputable def sGrp : Subgroup (MulAut lineGroup) :=
  Subgroup.closure {wordAut sWordA, wordAut sWordB, wordAut sWordC}

theorem sElems_forall {P : Pr → Prop} (hone : P oneP)
    (hstep : ∀ x, P x → ∀ g, (g ∈ sGenP () ∨ g = oneP) → P (mulP x g)) (par : List (ℕ × ℕ)) :
    ∀ acc : List Pr, (∀ x ∈ acc, P x) → ∀ x ∈ par.foldl (sStep (sGenP ())) acc, P x := by
  induction par with
  | nil => intro acc hacc x hx; exact hacc x (by simpa using hx)
  | cons p par ih =>
    intro acc hacc
    refine ih _ ?_
    intro x hx
    simp only [sStep, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hacc x hx
    · have h1 : P (acc.getD p.1 oneP) := by
        by_cases hi : p.1 < acc.length
        · rw [List.getD_eq_getElem _ _ hi]; exact hacc _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (by omega)]; exact hone
      refine hstep _ h1 _ ?_
      by_cases hj : p.2 < (sGenP ()).length
      · left; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
      · right; rw [List.getD_eq_default _ _ (by omega)]

theorem oneP_mem_foldl (par : List (ℕ × ℕ)) :
    ∀ acc : List Pr, oneP ∈ acc → oneP ∈ par.foldl (sStep (sGenP ())) acc := by
  induction par with
  | nil => intro acc h; simpa using h
  | cons p par ih => intro acc h; exact ih _ (by simp [sStep, h])

theorem oneP_mem_sElems : oneP ∈ sElems () := by
  unfold sElems
  exact oneP_mem_foldl _ _ (by simp)

theorem rep_of_mem_sElems {p : Pr} (hp : p ∈ sElems ()) : ∃ α ∈ sGrp, Rep p α := by
  unfold sElems at hp
  refine sElems_forall (P := fun p => ∃ α ∈ sGrp, Rep p α) ⟨1, one_mem _, rep_oneP⟩ ?_ sBfs
    [oneP] ?_ p hp
  · rintro x ⟨α, hα, hx⟩ g hg
    rcases hg with hg | rfl
    · simp only [sGenP, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨α * wordAut sWordA, mul_mem hα (Subgroup.subset_closure (by simp)),
          rep_mul hx (rep_wordP _)⟩
      · exact ⟨α * wordAut sWordB, mul_mem hα (Subgroup.subset_closure (by simp)),
          rep_mul hx (rep_wordP _)⟩
      · exact ⟨α * wordAut sWordC, mul_mem hα (Subgroup.subset_closure (by simp)),
          rep_mul hx (rep_wordP _)⟩
    · exact ⟨α * 1, mul_mem hα (one_mem _), rep_mul hx rep_oneP⟩
  · intro x hx
    simp at hx
    subst hx
    exact ⟨1, one_mem _, rep_oneP⟩

theorem exists_rep_of_mem_sGrp (h : sylowCheck () = true) {α : MulAut lineGroup}
    (hα : α ∈ sGrp) : ∃ p ∈ sElems (), Rep p α := by
  have hcl : ∀ x ∈ sElems (), ∀ g ∈ sGenP (), mulP x g ∈ sElems () := by
    simp only [sylowCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.contains_iff_mem] at h
    exact fun x hx g hg => h.2 x hx g hg
  have key : ∀ g : MulAut lineGroup,
      g ∈ Submonoid.closure {wordAut sWordA, wordAut sWordB, wordAut sWordC} →
        ∃ p ∈ sElems (), Rep p g := by
    intro g hg
    induction hg using Submonoid.closure_induction_right with
    | one => exact ⟨oneP, oneP_mem_sElems, rep_oneP⟩
    | mul_right x hx y hy ih =>
      obtain ⟨p, hp, hpx⟩ := ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨mulP p (wordP sWordA), hcl p hp _ (by simp [sGenP]), rep_mul hpx (rep_wordP _)⟩
      · exact ⟨mulP p (wordP sWordB), hcl p hp _ (by simp [sGenP]), rep_mul hpx (rep_wordP _)⟩
      · exact ⟨mulP p (wordP sWordC), hcl p hp _ (by simp [sGenP]), rep_mul hpx (rep_wordP _)⟩
  refine key α ?_
  rw [← Subgroup.closure_toSubmonoid_of_finite]
  exact hα

theorem card_sGrp (hZ : Subgroup.center lineGroup = ⊥) (h : sylowCheck () = true) :
    Nat.card sGrp = 3 ^ 5 := by
  classical
  have hlen : (sElems ()).length = 243 ∧ (sElems ()).Nodup := by
    simp only [sylowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2⟩
  let ρ : Pr → MulAut lineGroup := fun p => if hp : ∃ α, Rep p α then Classical.choose hp else 1
  have hρ : ∀ p ∈ sElems (), Rep p (ρ p) := by
    intro p hp
    obtain ⟨α, -, hα⟩ := rep_of_mem_sElems hp
    have hex : ∃ α, Rep p α := ⟨α, hα⟩
    simp only [ρ, dif_pos hex]
    exact Classical.choose_spec hex
  have hinj : Set.InjOn ρ ((sElems ()).toFinset : Set Pr) := by
    intro p hp q hq hpq
    simp only [Finset.mem_coe, List.mem_toFinset] at hp hq
    have h1 := hρ p hp
    have h2 := hρ q hq
    rw [← hpq] at h2
    exact rep_inj hZ h1 h2
  have himg : (sGrp : Set (MulAut lineGroup)) = ρ '' ((sElems ()).toFinset : Set Pr) := by
    ext α
    constructor
    · intro hα
      obtain ⟨p, hp, hpα⟩ := exists_rep_of_mem_sGrp h hα
      exact ⟨p, by simpa using hp, rep_ext (hρ p hp) hpα rfl⟩
    · rintro ⟨p, hp, rfl⟩
      simp only [Finset.mem_coe, List.mem_toFinset] at hp
      obtain ⟨β, hβ, hpβ⟩ := rep_of_mem_sElems hp
      have : ρ p = β := rep_ext (hρ p hp) hpβ rfl
      rw [this]
      exact hβ
  calc Nat.card sGrp = (sGrp : Set (MulAut lineGroup)).ncard := (Nat.card_coe_set_eq _).symm
    _ = (ρ '' ((sElems ()).toFinset : Set Pr)).ncard := by rw [himg]
    _ = ((sElems ()).toFinset : Set Pr).ncard := hinj.ncard_image
    _ = (sElems ()).toFinset.card := Set.ncard_coe_finset _
    _ = (sElems ()).length := List.toFinset_card_of_nodup hlen.2
    _ = 3 ^ 5 := by rw [hlen.1]; norm_num

end Sylow

end CFSG.RankThree.PartTwo.Sec19.TrialityTwo
