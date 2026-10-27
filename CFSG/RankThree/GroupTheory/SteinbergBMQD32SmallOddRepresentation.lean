module

public import CFSG.RankThree.GroupTheory.SteinbergBYQD32Extraspecial
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalPSLTwoSections

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.ComponentClassification.OutcomeLocal (odd_projective_linear_two_elementary_two_sections)
open scoped commutatorElement

theorem card_le_two_pow_finrank_of_sq_eq_one {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (n : ℕ) :
    ∀ {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V],
      Module.finrank k V = n → ∀ S : Subgroup (V →ₗ[k] V)ˣ, Finite S →
        (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) → (∀ a ∈ S, a * a = 1) → Nat.card S ≤ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn S hSfin hcomm hsq
  by_cases hsc : ∀ a ∈ S, a = 1 ∨ a = -1
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    ·
      have hV0 : ∀ v : V, v = 0 := finrank_zero_iff_forall_zero.mp (hn.trans h0)
      have hS : S = ⊥ := by
        rw [eq_bot_iff]
        intro a _
        rw [mem_bot]
        exact Units.ext (LinearMap.ext fun v => by rw [hV0 v, map_zero, map_zero])
      rw [hS, card_bot, h0, pow_zero]
    ·
      have hsub : (S : Set (V →ₗ[k] V)ˣ) ⊆ {1, -1} := fun a ha => hsc a ha
      calc Nat.card S = (S : Set (V →ₗ[k] V)ˣ).ncard := Nat.card_coe_set_eq _
        _ ≤ ({1, -1} : Set (V →ₗ[k] V)ˣ).ncard := Set.ncard_le_ncard hsub
        _ ≤ ({-1} : Set (V →ₗ[k] V)ˣ).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 ^ 1 := by rw [Set.ncard_singleton]; norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hpos
  push Not at hsc
  obtain ⟨T, hTS, hT1, hTm⟩ := hsc
  set t : V →ₗ[k] V := (T : V →ₗ[k] V) with ht
  have hsq' : ∀ s ∈ S, ∀ v, (s : V →ₗ[k] V) ((s : V →ₗ[k] V) v) = v := fun s hs v => by
    rw [← Module.End.mul_apply, ← Units.val_mul, hsq s hs, Units.val_one, Module.End.one_apply]
  have htt : ∀ v, t (t v) = v := hsq' T hTS
  have hcommT : ∀ s ∈ S, ∀ v, (s : V →ₗ[k] V) (t v) = t ((s : V →ₗ[k] V) v) := by
    intro s hs v
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ht, ← Units.val_mul, ← Units.val_mul,
      hcomm s hs T hTS]
  set Wp : Submodule k V := LinearMap.ker (t - 1) with hWp
  set Wm : Submodule k V := LinearMap.ker (t + 1) with hWm
  have hWpmem : ∀ v, v ∈ Wp ↔ t v = v := fun v => by
    rw [hWp, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hWmmem : ∀ v, v ∈ Wm ↔ t v = -v := fun v => by
    rw [hWm, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
      add_eq_zero_iff_eq_neg]
  have hplus : ∀ v, v + t v ∈ Wp := fun v => (hWpmem _).mpr (by rw [map_add, htt, add_comm])
  have hminus : ∀ v, v - t v ∈ Wm := fun v => (hWmmem _).mpr (by rw [map_sub, htt, neg_sub])
  have hdecomp : ∀ v : V, v = (2⁻¹ : k) • (v + t v) + (2⁻¹ : k) • (v - t v) := fun v => by
    rw [← smul_add, show v + t v + (v - t v) = (2 : k) • v by rw [two_smul]; abel, smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  have hsup : Wp ⊔ Wm = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [hdecomp v]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (hplus v))
      (Submodule.smul_mem _ _ (hminus v))
  have hinf : Wp ⊓ Wm = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvp, hvm⟩
    have h1 := (hWpmem v).mp hvp
    have h1' := (hWmmem v).mp hvm
    rw [Submodule.mem_bot]
    have hvv : (2 : k) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h1]
      rw [h1', neg_add_cancel]
    exact (smul_eq_zero.mp hvv).resolve_left h2
  have hWp_ne : Wp ≠ ⊥ := by
    intro hbot
    apply hTm
    apply Units.ext
    ext v
    have h := hplus v
    rw [hbot, Submodule.mem_bot] at h
    rw [Units.val_neg, Units.val_one, LinearMap.neg_apply, Module.End.one_apply]
    exact (add_eq_zero_iff_neg_eq.mp h).symm
  have hWm_ne : Wm ≠ ⊥ := by
    intro hbot
    apply hT1
    apply Units.ext
    ext v
    have h := hminus v
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at h
    rw [Units.val_one, Module.End.one_apply]
    exact h.symm
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq Wp Wm
  rw [hsup, hinf, finrank_bot, finrank_top, hn] at hdim
  have hp1 := Submodule.one_le_finrank_iff.mpr hWp_ne
  have hm1 := Submodule.one_le_finrank_iff.mpr hWm_ne
  have hmapp : ∀ s ∈ S, ∀ v ∈ Wp, (s : V →ₗ[k] V) v ∈ Wp := fun s hs v hv => by
    rw [hWpmem] at hv ⊢
    rw [← hcommT s hs, hv]
  have hmapm : ∀ s ∈ S, ∀ v ∈ Wm, (s : V →ₗ[k] V) v ∈ Wm := fun s hs v hv => by
    rw [hWmmem] at hv ⊢
    rw [← hcommT s hs, hv, map_neg]
  let resp : S →* (Wp →ₗ[k] Wp)ˣ := MonoidHom.mk'
    (fun s => ⟨(s.1 : V →ₗ[k] V).restrict (hmapp s.1 s.2),
      (s.1 : V →ₗ[k] V).restrict (hmapp s.1 s.2),
      LinearMap.ext fun w => Subtype.ext (hsq' s.1 s.2 w),
      LinearMap.ext fun w => Subtype.ext (hsq' s.1 s.2 w)⟩)
    (fun _ _ => Units.ext (LinearMap.ext fun _ => Subtype.ext rfl))
  let resm : S →* (Wm →ₗ[k] Wm)ˣ := MonoidHom.mk'
    (fun s => ⟨(s.1 : V →ₗ[k] V).restrict (hmapm s.1 s.2),
      (s.1 : V →ₗ[k] V).restrict (hmapm s.1 s.2),
      LinearMap.ext fun w => Subtype.ext (hsq' s.1 s.2 w),
      LinearMap.ext fun w => Subtype.ext (hsq' s.1 s.2 w)⟩)
    (fun _ _ => Units.ext (LinearMap.ext fun _ => Subtype.ext rfl))
  have hcommS : ∀ x y : S, x * y = y * x := fun x y => Subtype.ext (hcomm x x.2 y y.2)
  have hsqS : ∀ x : S, x * x = 1 := fun x => Subtype.ext (hsq x x.2)
  have hrange : ∀ {W : Submodule k V} (f : S →* (W →ₗ[k] W)ˣ),
      (∀ a ∈ f.range, ∀ b ∈ f.range, a * b = b * a) ∧ (∀ a ∈ f.range, a * a = 1) := by
    intro W f
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [← map_mul, ← map_mul, hcommS]
    · rintro _ ⟨x, rfl⟩
      rw [← map_mul, hsqS, map_one]
  obtain ⟨hpc, hps⟩ := hrange resp
  obtain ⟨hmc, hms⟩ := hrange resm
  have hfp : Finite resp.range := Finite.of_surjective _ resp.rangeRestrict_surjective
  have hfm : Finite resm.range := Finite.of_surjective _ resm.rangeRestrict_surjective
  have hcp := ih (Module.finrank k Wp) (by omega) (V := Wp) rfl resp.range hfp hpc hps
  have hcm := ih (Module.finrank k Wm) (by omega) (V := Wm) rfl resm.range hfm hmc hms
  have hinj : Function.Injective (fun s : S => (resp.rangeRestrict s, resm.rangeRestrict s)) := by
    intro s s' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hp, hm⟩ := h
    have hp' : ∀ v ∈ Wp, ((s : (V →ₗ[k] V)ˣ) : V →ₗ[k] V) v =
        ((s' : (V →ₗ[k] V)ˣ) : V →ₗ[k] V) v := fun v hv => by
      have h := congrArg (fun u : resp.range =>
        ((((u : (Wp →ₗ[k] Wp)ˣ) : Wp →ₗ[k] Wp) ⟨v, hv⟩ : Wp) : V)) hp
      exact h
    have hm' : ∀ v ∈ Wm, ((s : (V →ₗ[k] V)ˣ) : V →ₗ[k] V) v =
        ((s' : (V →ₗ[k] V)ˣ) : V →ₗ[k] V) v := fun v hv => by
      have h := congrArg (fun u : resm.range =>
        ((((u : (Wm →ₗ[k] Wm)ˣ) : Wm →ₗ[k] Wm) ⟨v, hv⟩ : Wm) : V)) hm
      exact h
    apply Subtype.ext
    apply Units.ext
    ext v
    rw [hdecomp v, map_add, map_add, map_smul, map_smul, map_smul, map_smul, hp' _ (hplus v),
      hm' _ (hminus v)]
  calc Nat.card S ≤ Nat.card (resp.range × resm.range) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card resp.range * Nat.card resm.range := Nat.card_prod _ _
    _ ≤ 2 ^ Module.finrank k Wp * 2 ^ Module.finrank k Wm := Nat.mul_le_mul hcp hcm
    _ = 2 ^ n := by rw [← pow_add]; congr 1; omega

end CFSG.RankThree.GroupTheory.SteinbergBM
