module

public import CFSG.Quasithin.SteinbergBSPGroupFixedSpace

public section

namespace CFSG.Quasithin.SteinbergBS

namespace Clifford

variable {k E X : Type*} [Field k] [AddCommGroup E] [Module k E] [Group X]
variable (ρ : X →* (E ≃ₗ[k] E)) (N : Subgroup X)

@[expose] def IsInv (U : Submodule k E) : Prop := ∀ n ∈ N, ∀ u ∈ U, ρ n u ∈ U

@[expose] def IsIrr (U : Submodule k E) : Prop :=
  IsInv ρ N U ∧ U ≠ ⊥ ∧ ∀ U' : Submodule k E, U' ≤ U → IsInv ρ N U' → U' = ⊥ ∨ U' = U

@[expose] def IsIntertwining {U : Submodule k E} (f : U →ₗ[k] E) : Prop :=
  ∀ n ∈ N, ∀ x y : U, (y : E) = ρ n x → f y = ρ n (f x)

@[expose] def NIso (U V : Submodule k E) : Prop :=
  ∃ f : U →ₗ[k] E, IsIntertwining ρ N f ∧ Function.Injective f ∧ LinearMap.range f = V

variable {ρ N}

theorem isInv_inf {U V : Submodule k E} (hU : IsInv ρ N U) (hV : IsInv ρ N V) :
    IsInv ρ N (U ⊓ V) := fun n hn u hu => ⟨hU n hn u hu.1, hV n hn u hu.2⟩

theorem isInv_sSup {s : Set (Submodule k E)} (hs : ∀ U ∈ s, IsInv ρ N U) :
    IsInv ρ N (sSup s) := by
  intro n hn
  have hle : sSup s ≤ (sSup s).comap (ρ n : E →ₗ[k] E) :=
    sSup_le fun U hU u hu => le_sSup hU (hs U hU n hn u hu)
  exact fun u hu => hle hu

variable [N.Normal]

omit [N.Normal] in
theorem isInv_range {U : Submodule k E} (hU : IsInv ρ N U) {f : U →ₗ[k] E}
    (hf : IsIntertwining ρ N f) : IsInv ρ N (LinearMap.range f) := by
  rintro n hn _ ⟨x, rfl⟩
  exact ⟨⟨ρ n x, hU n hn x x.2⟩, hf n hn x _ rfl⟩

omit [N.Normal] in
theorem isIrr_range {U : Submodule k E} (hU : IsIrr ρ N U) {f : U →ₗ[k] E}
    (hf : IsIntertwining ρ N f) (hinj : Function.Injective f) :
    IsIrr ρ N (LinearMap.range f) := by
  refine ⟨isInv_range hU.1 hf, ?_, fun V hV hVi => ?_⟩
  · intro h
    apply hU.2.1
    rw [eq_bot_iff]
    intro x hx
    have h1 : f ⟨x, hx⟩ ∈ LinearMap.range f := ⟨_, rfl⟩
    rw [h, Submodule.mem_bot, ← map_zero f] at h1
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val (hinj h1)
  ·
    set W := (V.comap f).map U.subtype with hW
    have hWi : IsInv ρ N W := by
      rintro n hn _ ⟨x, hx, rfl⟩
      refine ⟨⟨ρ n x, hU.1 n hn x x.2⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap] at hx ⊢
      rw [hf n hn x _ rfl]
      exact hVi n hn _ hx
    rcases hU.2.2 W (Submodule.map_subtype_le _ _) hWi with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨x, rfl⟩ := hV hv
      have hx : (x : E) ∈ W := ⟨x, hv, rfl⟩
      rw [h, Submodule.mem_bot] at hx
      have hx0 : x = 0 := Subtype.ext hx
      rw [Submodule.mem_bot, hx0, map_zero]
    · right
      refine le_antisymm hV ?_
      rintro _ ⟨x, rfl⟩
      have hx : (x : E) ∈ W := by rw [h]; exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      rw [Subtype.ext hyx] at hy
      exact hy

omit [N.Normal] in
theorem niso_of_le_sup {B C M : Submodule k E} (hB : IsIrr ρ N B) (hC : IsIrr ρ N C)
    (hM : IsInv ρ N M) (hle : B ≤ M ⊔ C) (hBM : ¬ B ≤ M) : NIso ρ N B C := by
  have hCM : C ⊓ M = ⊥ := by
    rcases hC.2.2 (C ⊓ M) inf_le_left (isInv_inf hC.1 hM) with h | h
    · exact h
    · exfalso
      apply hBM
      have h1 : C ≤ M := h ▸ inf_le_right
      exact hle.trans (sup_le le_rfl h1)
  have hBM' : B ⊓ M = ⊥ := by
    rcases hB.2.2 (B ⊓ M) inf_le_left (isInv_inf hB.1 hM) with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hBM
  set q := M.mkQ with hq
  set qC := q.comp C.subtype with hqC
  have hqCinj : Function.Injective qC := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker, hqC, LinearMap.comp_apply, hq, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hc
    have h1 : (c : E) ∈ C ⊓ M := ⟨c.2, hc⟩
    rw [hCM, Submodule.mem_bot] at h1
    exact (Submodule.mem_bot k).2 (Subtype.ext h1)
  have hBq : ∀ b : B, q b ∈ LinearMap.range qC := by
    intro b
    obtain ⟨m, hm, c, hc, hmc⟩ := Submodule.mem_sup.1 (hle b.2)
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [hqC, LinearMap.comp_apply, hq, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq, Submodule.subtype_apply]
    rw [← hmc, show c - (m + c) = -m by abel]
    exact M.neg_mem hm
  let e := LinearEquiv.ofInjective qC hqCinj
  let π : B →ₗ[k] E :=
    C.subtype.comp (e.symm.toLinearMap.comp ((q.comp B.subtype).codRestrict _ hBq))
  have hπC : ∀ b, π b ∈ C := fun b => (e.symm _).2
  have hπq : ∀ b : B, q (π b) = q b := by
    intro b
    have h1 := congrArg Subtype.val (e.apply_symm_apply ⟨q b, hBq b⟩)
    exact h1
  have hπM : ∀ b : B, (b : E) - π b ∈ M := by
    intro b
    have h1 := hπq b
    rw [hq, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h1
    rw [← neg_sub]
    exact M.neg_mem h1
  have huniq : ∀ c c' : E, c ∈ C → c' ∈ C → c - c' ∈ M → c = c' := by
    intro c c' hc hc' hcc'
    have h1 : c - c' ∈ C ⊓ M := ⟨C.sub_mem hc hc', hcc'⟩
    rw [hCM, Submodule.mem_bot, sub_eq_zero] at h1
    exact h1
  have hπint : IsIntertwining ρ N π := by
    intro n hn b b' hbb'
    refine huniq _ _ (hπC b') (hC.1 n hn _ (hπC b)) ?_
    have h1 := hπM b'
    have h2 := hM n hn _ (hπM b)
    rw [map_sub, ← hbb'] at h2
    have h3 := M.sub_mem h2 h1
    rwa [show (b' : E) - ρ n (π b) - ((b' : E) - π b') = π b' - ρ n (π b) by abel] at h3
  have hπinj : Function.Injective π := by
    intro b b' h
    have h1 := hπM b
    have h2 := hπM b'
    rw [h] at h1
    have h3 := M.sub_mem h1 h2
    rw [sub_sub_sub_cancel_right] at h3
    have h4 : (b : E) - b' ∈ B ⊓ M := ⟨B.sub_mem b.2 b'.2, h3⟩
    rw [hBM', Submodule.mem_bot, sub_eq_zero] at h4
    exact Subtype.ext h4
  refine ⟨π, hπint, hπinj, ?_⟩
  have hrange := (isIrr_range hB hπint hπinj).2.1
  rcases hC.2.2 (LinearMap.range π) (fun x hx => by obtain ⟨b, rfl⟩ := hx; exact hπC b)
    (isInv_range hB.1 hπint) with h | h
  · exact absurd h hrange
  · exact h

omit [N.Normal] in
theorem exists_niso_of_le_sSup {B : Submodule k E} (hB : IsIrr ρ N B) (s : Set (Submodule k E))
    (hs : s.Finite) (hsi : ∀ C ∈ s, IsIrr ρ N C) (hle : B ≤ sSup s) : ∃ C ∈ s, NIso ρ N B C := by
  revert hsi hle
  refine Set.Finite.induction_on
    (motive := fun s _ => (∀ C ∈ s, IsIrr ρ N C) → B ≤ sSup s → ∃ C ∈ s, NIso ρ N B C) s hs
    ?_ ?_
  · intro _ hle
    rw [sSup_empty] at hle
    exact absurd (le_bot_iff.1 hle) hB.2.1
  · intro a s _ _ ih hsi hle
    rw [sSup_insert] at hle
    by_cases hBs : B ≤ sSup s
    · obtain ⟨C, hC, hBC⟩ := ih (fun C hC => hsi C (Set.mem_insert_of_mem _ hC)) hBs
      exact ⟨C, Set.mem_insert_of_mem _ hC, hBC⟩
    · refine ⟨a, Set.mem_insert _ _, niso_of_le_sup hB (hsi a (Set.mem_insert _ _))
        (isInv_sSup fun C hC => (hsi C (Set.mem_insert_of_mem _ hC)).1) ?_ hBs⟩
      rwa [sup_comm]

variable [Finite k] {p : ℕ} [hp : Fact p.Prime] [CharP k p] [FiniteDimensional k E]

end Clifford

open Clifford

end CFSG.Quasithin.SteinbergBS
