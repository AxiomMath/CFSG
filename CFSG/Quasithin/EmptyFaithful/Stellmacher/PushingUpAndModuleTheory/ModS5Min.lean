module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5C27

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

variable {n : ℕ}

theorem exists_minimal_inv (M : Model n) (hnt : ∃ w : M.W, w ≠ 1) :
    ∃ (N : Subgroup M.W) (hN : IsInvSub M ⊤ N), N ≠ ⊥ ∧ (M.restrict N hN).IsIrred := by
  let S : Set (Subgroup M.W) := {N | IsInvSub M ⊤ N ∧ N ≠ ⊥}
  have hS : (⊤ : Subgroup M.W) ∈ S := by
    refine ⟨isInvSub_top M, ?_⟩
    obtain ⟨w, hw⟩ := hnt
    intro h
    exact hw (by have : w ∈ (⊤ : Subgroup M.W) := trivial
                 rw [h] at this; exact this)
  obtain ⟨N, ⟨hN, hNbot⟩, hmin⟩ := (measure fun N : Subgroup M.W => Nat.card N).wf.has_min S ⟨_, hS⟩
  refine ⟨N, hN, hNbot, ?_, ?_⟩
  · obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNbot
    exact ⟨x, hx1⟩
  · intro Y hY
    let Y' : Subgroup M.W := Subgroup.map N.subtype (Y : Subgroup ↥N)
    by_cases hY0 : Y = ⊥
    · exact Or.inl hY0
    right
    have hY'inv : IsInvSub M ⊤ Y' := by
      rintro σ - _ ⟨y, hy, rfl⟩
      exact ⟨(M.restrict N hN).act σ y, hY σ (Subgroup.mem_top σ) y hy, rfl⟩
    have hY'bot : Y' ≠ ⊥ := by
      intro h
      apply hY0
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      have : (N.subtype y : M.W) ∈ Y' := ⟨y, hy, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subtype.ext this
    have hle : Y' ≤ N := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hcard : Nat.card N ≤ Nat.card Y' := by
      by_contra hlt
      exact hmin Y' ⟨hY'inv, hY'bot⟩ (not_le.mp hlt)
    have hY'N : Y' = N := Subgroup.eq_of_le_of_card_ge hle hcard
    rw [eq_top_iff]
    intro y _
    have : (N.subtype y : M.W) ∈ Y' := by rw [hY'N]; exact y.2
    obtain ⟨y', hy', hyy⟩ := this
    have : y' = y := Subtype.ext hyy
    rw [← this]
    exact hy'

theorem fixW_alt5_eq_bot_of_fixW_top_eq_bot (M : Model 5) (h : fixW M ⊤ = ⊥) :
    fixW M (alternatingGroup (Fin 5)) = ⊥ := by
  by_contra hne
  have hK := isInvSub_fixW_of_normal M (alternatingGroup.normal (α := Fin 5))
  have hnt : ∃ w : (M.restrict _ hK).W, w ≠ 1 := by
    obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨k, hk1⟩
  obtain ⟨v, hv1, hv⟩ := exists_fixed_vector _ hnt
  have hvA : Subtype.val v ∈ fixW M (alternatingGroup (Fin 5)) := Subtype.property v
  have hvfix : Subtype.val v ∈ fixW M ⊤ := by
    intro g _
    obtain ⟨a, ha, s, hs, rfl⟩ := perm5_eq_alt5_mul_syl g
    have hs' : M.act s (Subtype.val v) = Subtype.val v := congrArg Subtype.val (hv s hs)
    rw [act_mul_apply, hs', hvA a ha]
  rw [h, Subgroup.mem_bot] at hvfix
  exact hv1 (Subtype.ext hvfix)

theorem fixW_alt5_ne_top_of_faithful {M : Model 5} (hf : M.Faithful) :
    fixW M (alternatingGroup (Fin 5)) ≠ ⊤ := by
  intro h
  have h1 : M.act threeCyc012 = M.act 1 := by
    ext w
    have hw : w ∈ fixW M (alternatingGroup (Fin 5)) := by rw [h]; trivial
    rw [hw threeCyc012 threeCyc012_mem_alt]
    simp
  have := hf h1
  exact absurd this (by unfold threeCyc012; decide +kernel)

theorem fixW_top_of_swap (M : Model 5) {t : Perm (Fin 5)} (ht : t.IsSwap)
    (h : fixW M (Subgroup.zpowers t) = ⊤) : fixW M ⊤ = ⊤ := by
  have hker : t ∈ M.act.ker := by
    rw [MonoidHom.mem_ker]
    ext w
    have := (eq_top_iff.mp h (Subgroup.mem_top w)) t (Subgroup.mem_zpowers t)
    simpa using this
  have hall : (⊤ : Subgroup (Perm (Fin 5))) ≤ M.act.ker := by
    rw [← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    rintro _ ⟨a, b, hab, rfl⟩
    obtain ⟨x, y, hxy, rfl⟩ := ht
    obtain ⟨c, hc⟩ := isConj_iff.mp (Perm.isConj_swap hxy hab)
    rw [← hc]
    exact (inferInstance : M.act.ker.Normal).conj_mem _ hker c
  rw [eq_top_iff]
  intro w _ σ hσ
  have := hall hσ
  rw [MonoidHom.mem_ker] at this
  rw [this]
  rfl

@[expose] def Model.quotCongr (M : Model n) {U V : Subgroup M.W} (h : U = V)
    (hU : IsInvSub M ⊤ U) (hV : IsInvSub M ⊤ V) : (M.quot U hU).Iso (M.quot V hV) := by
  subst h
  exact Model.Iso.refl _

end CFSG.Quasithin.F53Mod
