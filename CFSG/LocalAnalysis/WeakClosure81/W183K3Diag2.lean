module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Diag1
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Fix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace Assumption131

variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

private lemma w183k3diag2_finite_lgl : Finite (LGL 2 V) :=
  Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
    (fun _ _ h => LinearEquiv.ext (congrFun h))

theorem false_of_three_members_quasi (h : Assumption131 G Γ VA i)
    (hVfix : ∀ A ∈ Γ, VA A ≤ fixSub A)
    {L₁ L₂ X₁ X₂ : Subgroup (LGL 2 V)} (hL₁ : CFSG.Open.IsQuasisimple ↥L₁)
    (hL₂ : CFSG.Open.IsQuasisimple ↥L₂)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hX₁ : X₁ ≤ L₁) (hX₂ : X₂ ≤ L₂)
    (hX₁nc : ¬ X₁ ≤ quasiCentre L₁) (hX₂nc : ¬ X₂ ≤ quasiCentre L₂)
    (hX₁sq : ∀ x ∈ X₁, x * x = 1)
    (D : Fin 3 → Subgroup (LGL 2 V)) (hDΓ : ∀ k, D k ∈ Γ) (hDr : ∀ k, mRank (D k) ≤ i)
    (hDne : ∀ j k, j ≠ k → D j ≠ D k)
    (hDcomm : ∀ j k, ∀ a ∈ D j, ∀ b ∈ D k, a * b = b * a)
    (hgen : X₁ ⊔ X₂ ≤ D 0 ⊔ D 1 ⊔ D 2)
    (hcover : ∀ s ∈ X₁, s ≠ 1 → ∀ u ∈ X₂, u ≠ 1 → ∃ k, s * u ∈ D k)
    (hcover' : ∀ u ∈ X₂, u ≠ 1 → ∀ k, ∃ s ∈ X₁, s ≠ 1 ∧ s * u ∈ D k) : False := by
  classical
  have hVfix_le : ∀ k, VA (D k) ≤ fixSub (X₁ ⊔ X₂) := by
    intro k v hv
    rw [mem_fixSub]
    intro x hx
    let stab : Subgroup (LGL 2 V) :=
      { carrier := {g | g v = v}
        one_mem' := rfl
        mul_mem' := fun {a b} ha hb => by
          change (a * b) v = v
          rw [LinearEquiv.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          change a⁻¹ v = v
          calc a⁻¹ v = a⁻¹ (a v) := by rw [ha]
            _ = v := a.symm_apply_apply v }
    have hDj : ∀ j, D j ≤ stab := by
      intro j d hd
      by_cases hjk : j = k
      · rw [hjk] at hd
        exact hVfix (D k) (hDΓ k) hv d hd
      · have hbot := h.commSpace_VA_eq_bot_of_commute (hDΓ k) (hDΓ j) (hDr j)
            (hDne k j (Ne.symm hjk)) (hDcomm k j)
        exact (commSpace_eq_bot_iff.mp hbot) d hd v hv
    exact (hgen.trans (sup_le (sup_le (hDj 0) (hDj 1)) (hDj 2))) hx
  have hstep2 : ∀ s ∈ X₁, s ≠ 1 → ∀ u ∈ X₂, u ≠ 1 → ∀ v : V, s (u v - v) = u v - v := by
    intro s hs hs1 u hu hu1 v
    obtain ⟨k, hk⟩ := hcover s hs hs1 u hu hu1
    have hz : (s * u) v - v ∈ VA (D k) :=
      commSub_le_VA_of_mRank_le h (hDΓ k) (hDr k) (sub_mem_commSub (D k) hk v)
    have hzfix : s ((s * u) v - v) = (s * u) v - v :=
      (hVfix_le k hz) s (Subgroup.mem_sup_left hs)
    have h1 : s ((s * u) v - v) = u v - s v := by
      rw [map_sub]
      have hsuv : s ((s * u) v) = u v := by
        rw [LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, hX₁sq s hs]
        rfl
      rw [hsuv]
    have h2 : (s * u) v - v = s (u v) - v := by rw [LinearEquiv.mul_apply]
    have heq : u v - s v = s (u v) - v := by
      rw [← h1, ← h2]
      exact hzfix
    have hsuv2 : s (u v) = u v - s v + v := by
      have hh := congrArg (fun x : V => x + v) heq
      simpa using hh.symm
    rw [map_sub, hsuv2]
    have hL : (u v - s v + v) - s v = u v + v := by
      simp only [sub_eq_add_neg, ZModModule.neg_eq_self]
      rw [show u v + s v + v + s v = u v + v + (s v + s v) by abel,
          ZModModule.add_self (s v), add_zero]
    rw [hL, sub_eq_add_neg, ZModModule.neg_eq_self]
  have hcommX₂_le : commSpace X₂ ⊤ ≤ fixSub X₁ := by
    rw [commSpace_le_iff]
    intro u hu v _
    rw [mem_fixSub]
    intro s hs
    by_cases hu1 : u = 1
    · subst hu1; simp
    by_cases hs1 : s = 1
    · subst hs1; simp
    · exact hstep2 s hs hs1 u hu hu1 v
  have hinv : Invariant L₁ (commSpace X₂ ⊤) := by
    refine invariant_commSpace (K := X₂) (K' := L₁) ?_ (fun _ _ _ _ => trivial)
    intro l hl u hu
    have h := hcomm l hl u (hX₂ hu)
    have e : l * u * l⁻¹ = u := by rw [h]; group
    rw [e]
    exact hu
  have hE₀ : commSpace X₂ ⊤ ≤ fixSub L₁ :=
    w183k3_fixSub_le_of_not_central hL₁ hX₁ hX₁nc hinv hcommX₂_le
  have hE₀_le_X₂ : fixSub L₁ ≤ fixSub X₂ := by
    intro e he
    rw [mem_fixSub]
    intro u hu
    by_cases hu1 : u = 1
    · subst hu1; simp
    · obtain ⟨s₀, hs₀, _, hs₀u⟩ := hcover' u hu hu1 0
      obtain ⟨s₁, hs₁, _, hs₁u⟩ := hcover' u hu hu1 1
      have hue : u e ∈ fixSub L₁ := by
        rw [mem_fixSub]
        intro l hl
        have h := hcomm l hl u (hX₂ hu)
        calc l (u e) = (l * u) e := (LinearEquiv.mul_apply l u e).symm
          _ = (u * l) e := by rw [h]
          _ = u (l e) := LinearEquiv.mul_apply u l e
          _ = u e := by rw [he l hl]
      have h₀ : u e - e ∈ VA (D 0) := by
        have hmem : (s₀ * u) e - e ∈ VA (D 0) :=
          commSub_le_VA_of_mRank_le h (hDΓ 0) (hDr 0) (sub_mem_commSub (D 0) hs₀u e)
        have he' : (s₀ * u) e - e = u e - e := by
          rw [LinearEquiv.mul_apply, hue s₀ (hX₁ hs₀)]
        rwa [he'] at hmem
      have h₁ : u e - e ∈ VA (D 1) := by
        have hmem : (s₁ * u) e - e ∈ VA (D 1) :=
          commSub_le_VA_of_mRank_le h (hDΓ 1) (hDr 1) (sub_mem_commSub (D 1) hs₁u e)
        have he' : (s₁ * u) e - e = u e - e := by
          rw [LinearEquiv.mul_apply, hue s₁ (hX₁ hs₁)]
        rwa [he'] at hmem
      have hbot : VA (D 0) ⊓ VA (D 1) = ⊥ :=
        h.disjoint (D 0) (hDΓ 0) (D 1) (hDΓ 1) (hDne 0 1 (by decide))
      have hmem : u e - e ∈ VA (D 0) ⊓ VA (D 1) := ⟨h₀, h₁⟩
      rw [hbot, Submodule.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
  have hL₂inv : ∀ l ∈ L₂, ∀ e ∈ fixSub L₁, l e ∈ fixSub L₁ := by
    intro l hl e he
    rw [mem_fixSub] at he ⊢
    intro l₁ hl₁
    have h := hcomm l₁ hl₁ l hl
    calc l₁ (l e) = (l₁ * l) e := (LinearEquiv.mul_apply l₁ l e).symm
      _ = (l * l₁) e := by rw [h]
      _ = l (l₁ e) := LinearEquiv.mul_apply l l₁ e
      _ = l e := by rw [he l₁ hl₁]
  have hE₀_le_L₂ : fixSub L₁ ≤ fixSub L₂ :=
    w183k3_fixSub_le_of_not_central hL₂ hX₂ hX₂nc hL₂inv hE₀_le_X₂
  have hL₂comm_le : commSpace L₂ ⊤ ≤ fixSub L₁ :=
    w183k3_commSpace_le_of_not_central hL₂ hX₂ hX₂nc hL₂inv hE₀
  have hmul : ∀ a ∈ L₂, ∀ b ∈ L₂, ∀ v : V, a (b v - v) = b v - v := by
    intro a ha b hb v
    have hmem : b v - v ∈ commSpace L₂ ⊤ := by
      rw [commSpace_top_eq_commSub]
      exact sub_mem_commSub L₂ hb v
    exact (hE₀_le_L₂ (hL₂comm_le hmem)) a ha
  obtain ⟨a, ha, b, hb, hab⟩ := W183K3.quasi_exists_noncomm hL₂
  exact hab (w183_mul_comm_of_comp_eq (N := L₂) hmul a ha b hb)

theorem false_of_diagonal_member_quasi (h : Assumption131 G Γ VA i)
    (hVfix : ∀ A ∈ Γ, VA A ≤ fixSub A)
    {L₁ L₂ X₁ X₂ D₀ : Subgroup (LGL 2 V)}
    (hL₁ : CFSG.Open.IsQuasisimple ↥L₁) (hL₂ : CFSG.Open.IsQuasisimple ↥L₂)
    (ho₁ : Odd (Nat.card ↥(Subgroup.center ↥L₁)))
    (ho₂ : Odd (Nat.card ↥(Subgroup.center ↥L₂))) (hL₁G : L₁ ≤ G)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hX₁ : X₁ ≤ L₁) (hX₂ : X₂ ≤ L₂)
    (hX₁c : Nat.card ↥X₁ = 4) (hX₁sq : ∀ x ∈ X₁, x * x = 1) (φ : ↥X₁ ≃* ↥X₂)
    (hD₀ : D₀ ∈ Γ) (hD₀r : mRank D₀ ≤ i)
    (hD₀eq : ∀ d, d ∈ D₀ ↔ ∃ x : ↥X₁, d = (x : LGL 2 V) * (φ x : LGL 2 V))
    {n : LGL 2 V} (hn : n ∈ L₁) (hnX : ∀ x ∈ X₁, n * x * n⁻¹ ∈ X₁)
    (hfpf : ∀ x ∈ X₁, x ≠ 1 → n * x * n⁻¹ ≠ x) : False := by
  haveI : Finite (LGL 2 V) := w183k3diag2_finite_lgl
  have hX₁nc : ¬ X₁ ≤ quasiCentre L₁ := by
    intro hX₁z
    have hbot : X₁ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx2 : x ^ (2 ^ 1) = 1 := by
        rw [pow_one, pow_two]
        exact hX₁sq x hx
      exact Subgroup.mem_bot.mpr
        (W183K3.quasi_centre_two_pow_eq_one ho₁ (hX₁z hx) (k := 1) hx2)
    rw [hbot] at hX₁c
    simp at hX₁c
  have hX₂nc : ¬ X₂ ≤ quasiCentre L₂ := by
    intro hX₂z
    have hbot : X₂ = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hx⟩ := φ.surjective ⟨y, hy⟩
      have hyx : y = (φ x : LGL 2 V) := congrArg Subtype.val hx.symm
      have hx2 : x * x = 1 := Subtype.ext (hX₁sq (x : LGL 2 V) x.2)
      have hy2 : y ^ (2 ^ 1) = 1 := by
        rw [pow_one, pow_two, hyx]
        calc (φ x : LGL 2 V) * (φ x : LGL 2 V) = (φ (x * x) : LGL 2 V) := by
              rw [map_mul]; rfl
          _ = 1 := by rw [hx2, map_one]; rfl
      exact Subgroup.mem_bot.mpr
        (W183K3.quasi_centre_two_pow_eq_one ho₂ (hX₂z hy) (k := 1) hy2)
    have hcard : Nat.card ↥X₂ = Nat.card ↥X₁ := (Nat.card_congr φ.toEquiv).symm
    rw [hbot, Subgroup.card_bot, hX₁c] at hcard
    norm_num at hcard
  obtain ⟨D, hDΓ, hDr, hDne, hDcomm, hgen, hcover, hcover'⟩ :=
    h.exists_three_members_quasi ho₁ hL₁G hcomm hX₁ hX₂ hX₁c hX₁sq φ hD₀ hD₀r hD₀eq hn hnX hfpf
  exact h.false_of_three_members_quasi hVfix hL₁ hL₂ hcomm hX₁ hX₂ hX₁nc hX₂nc hX₁sq D hDΓ hDr
    hDne hDcomm hgen hcover hcover'

end Assumption131

end CFSG.LocalAnalysis.WeakClosure81

end
