module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7CSignXAux_signx_not_sp {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {a : V ≃ₗ[ZMod p] V} (hp3 : p = 3) (h : C2SignX p b a) : ¬ C2SP p b a := by
  intro hsp
  unfold C2SignX at h
  unfold C2SP at hsp
  obtain ⟨σ, c, hσ0, hc0, _hc, ha⟩ := hsp
  obtain ⟨ha0, _hai⟩ := h
  have h0 : a (b 0) = b 0 := by rw [ha 0, hσ0, hc0, one_smul]
  have hb : b 0 = -b 0 := h0.symm.trans ha0
  have hsum : b 0 + b 0 = 0 := (eq_neg_iff_add_eq_zero).mp hb
  have h2b : (2 : ZMod p) • b 0 = 0 := by rw [two_smul]; exact hsum
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    change ((2 : ℕ) : ZMod p) = 0 at h
    rw [CharP.cast_eq_zero_iff (ZMod p) p 2] at h
    have h32 : 3 ∣ 2 := by rw [hp3] at h; exact h
    norm_num at h32
  exact b.ne_zero 0 (smul_eq_zero.mp h2b |>.resolve_left h2)

private lemma hdRo7CSignXAux_signx_unique {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {a a' : V ≃ₗ[ZMod p] V} (ha : C2SignX p b a) (ha' : C2SignX p b a') : a = a' := by
  unfold C2SignX at ha ha'
  obtain ⟨ha0, hai⟩ := ha
  obtain ⟨ha'0, ha'i⟩ := ha'
  apply (LinearEquiv.toLinearMap_inj).mp
  apply b.ext
  intro i
  change a (b i) = a' (b i)
  by_cases hi : i = 0
  · subst hi; rw [ha0, ha'0]
  · rw [hai i hi, ha'i i hi]

private lemma hdRo7CSignXAux_signx_sq {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {a : V ≃ₗ[ZMod p] V} (ha : C2SignX p b a) : a * a = 1 := by
  unfold C2SignX at ha
  obtain ⟨ha0, hai⟩ := ha
  apply (LinearEquiv.toLinearMap_inj).mp
  apply b.ext
  intro i
  change (a * a) (b i) = (1 : V ≃ₗ[ZMod p] V) (b i)
  by_cases hi : i = 0
  · subst hi
    rw [LinearEquiv.mul_apply, ha0, map_neg, ha0, neg_neg]
    rfl
  · rw [LinearEquiv.mul_apply, hai i hi, hai i hi]
    rfl

private lemma hdRo7CSignXAux_commute_signx_sp {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {s t : V ≃ₗ[ZMod p] V} (hs : C2SignX p b s) (ht : C2SP p b t) : Commute s t := by
  unfold C2SignX at hs
  unfold C2SP at ht
  obtain ⟨hs0, hsi⟩ := hs
  obtain ⟨σ, c, hσ0, hc0, _hc, htdef⟩ := ht
  apply (LinearEquiv.toLinearMap_inj).mp
  apply b.ext
  intro i
  change (s * t) (b i) = (t * s) (b i)
  by_cases hi : i = 0
  · subst hi
    have hL : (s * t) (b 0) = -b 0 := by
      rw [LinearEquiv.mul_apply, htdef 0, hσ0, hc0, one_smul, hs0]
    have hR : (t * s) (b 0) = -b 0 := by
      rw [LinearEquiv.mul_apply, hs0, map_neg, htdef 0, hσ0, hc0, one_smul]
    rw [hL, hR]
  · have hσi : σ i ≠ 0 := fun h => hi (σ.injective (by rw [h, hσ0]))
    have hL : (s * t) (b i) = c i • b (σ i) := by
      rw [LinearEquiv.mul_apply, htdef i, map_smul, hsi (σ i) hσi]
    have hR : (t * s) (b i) = c i • b (σ i) := by
      rw [LinearEquiv.mul_apply, hsi i hi, htdef i]
    rw [hL, hR]

private def hdRo7CSignXAux_twoSub {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {s0 : V ≃ₗ[ZMod p] V} (hsq : s0 * s0 = 1) :
    Subgroup (V ≃ₗ[ZMod p] V) where
  carrier := {x | x = 1 ∨ x = s0}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl hsq
  inv_mem' := by
    intro x hx
    rcases hx with rfl | rfl
    · exact Or.inl (inv_one)
    · exact Or.inr (inv_eq_of_mul_eq_one_right hsq)

theorem c2_signx_holds :
    ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n → ∀ (V : Type) [AddCommGroup V]
      [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
      (AL Q : Subgroup (V ≃ₗ[ZMod p] V)) (S : Set (V ≃ₗ[ZMod p] V)),
      (∀ a, a ∈ AL ↔ C2SP p b a) →
      (∀ s ∈ S, s ∈ Q ∧ GGLinRefl s ∧ (C2SP p b s ∨ C2SignX p b s ∨ C2Swap p b s)) →
      Q = Subgroup.closure S →
      (∀ s ∈ S, ∀ t ∈ S,
        Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v) s t) →
      (¬ ∃ s ∈ S, C2Swap p b s) → ¬ Q ≤ AL → (∃ a ∈ Q, a ∈ AL ∧ a ≠ 1) → False := by
  intro p hp hp3 n hn V instACG instMod b AL Q S hAL hS hQ hconn hno hnle hJ
  have hex : ∃ s ∈ S, C2SignX p b s := by
    by_contra h
    apply hnle
    rw [hQ]
    refine (Subgroup.closure_le AL).mpr ?_
    intro s hs
    rcases (hS s hs).2.2 with hsp | hsg | hsw
    · exact (hAL s).mpr hsp
    · exact absurd ⟨s, hs, hsg⟩ h
    · exact absurd ⟨s, hs, hsw⟩ hno
  obtain ⟨s0, hs0S, hs0sign⟩ := hex
  have hem : ∀ t ∈ S, t = s0 := by
    intro t ht
    rcases Relation.ReflTransGen.cases_head (hconn s0 hs0S t ht) with h | ⟨c, hR, _⟩
    · exact h.symm
    · exfalso
      obtain ⟨_, hcS, hncomm⟩ := hR
      apply hncomm
      rcases (hS c hcS).2.2 with hsp | hsg | hsw
      · exact hdRo7CSignXAux_commute_signx_sp hs0sign hsp
      · rw [hdRo7CSignXAux_signx_unique hsg hs0sign]
      · exact absurd ⟨c, hcS, hsw⟩ hno
  obtain ⟨a, haQ, haAL, ha1⟩ := hJ
  have hsub : S ⊆ ({s0} : Set (V ≃ₗ[ZMod p] V)) := fun t ht => by
    rw [Set.mem_singleton_iff]; exact hem t ht
  have haQ' : a ∈ Subgroup.closure ({s0} : Set (V ≃ₗ[ZMod p] V)) :=
    Subgroup.closure_mono hsub (hQ ▸ haQ)
  have hsq : s0 * s0 = 1 := hdRo7CSignXAux_signx_sq hs0sign
  have hle : Subgroup.closure ({s0} : Set (V ≃ₗ[ZMod p] V)) ≤ hdRo7CSignXAux_twoSub hsq := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Or.inr rfl
  have haT : a ∈ hdRo7CSignXAux_twoSub hsq := hle haQ'
  rcases haT with ha_eq_one | ha_eq_s0
  · exact ha1 ha_eq_one
  · rw [ha_eq_s0] at haAL
    exact hdRo7CSignXAux_signx_not_sp hp3 hs0sign ((hAL s0).mp haAL)

end CFSG.StandardType.HdRo7C
