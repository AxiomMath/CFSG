module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Basic

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7A3ReflFixAux_neg_one_ne_zero {p : ℕ} (hp : p = 3) : (-1 : ZMod p) ≠ 0 := by
  rw [hp]; decide

private lemma hdRo7A3ReflFixAux_one_ne_neg_one {p : ℕ} (hp : p = 3) :
    (1 : ZMod p) ≠ -1 := by
  rw [hp]; decide

private lemma hdRo7A3ReflFixAux_card_pair {α : Type*} [DecidableEq α] (a b : α) :
    ({a, b} : Finset α).card ≤ 2 := by
  have h : ({a, b} : Finset α) = [a, b].toFinset := by simp
  rw [h]
  simpa using List.toFinset_card_le [a, b]

private lemma hdRo7A3ReflFixAux_card_four {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α).card ≤ 4 := by
  have h : ({a, b, c, d} : Finset α) = [a, b, c, d].toFinset := by simp
  rw [h]
  simpa using List.toFinset_card_le [a, b, c, d]

private lemma hdRo7A3ReflFixAux_card_six {α : Type*} [DecidableEq α] (a b c d e f : α) :
    ({a, b, c, d, e, f} : Finset α).card ≤ 6 := by
  have h : ({a, b, c, d, e, f} : Finset α) = [a, b, c, d, e, f].toFinset := by simp
  rw [h]
  simpa using List.toFinset_card_le [a, b, c, d, e, f]

private lemma hdRo7A3ReflFixAux_card_eight {α : Type*} [DecidableEq α]
    (a b c d e f g h : α) :
    ({a, b, c, d, e, f, g, h} : Finset α).card ≤ 8 := by
  have h1 : ({a, b, c, d, e, f, g, h} : Finset α) = [a, b, c, d, e, f, g, h].toFinset := by simp
  rw [h1]
  simpa using List.toFinset_card_le [a, b, c, d, e, f, g, h]

private lemma hdRo7A3ReflFixAux_mem_notMem {α : Type*} [Fintype α] {S : Finset α}
    (h : S.card < Fintype.card α) : ∃ x, x ∉ S := by
  by_contra hc
  push Not at hc
  have hcard : S.card = Fintype.card α := by
    rw [Finset.eq_univ_of_forall hc, Finset.card_univ]
  omega

private lemma hdRo7A3ReflFixAux_sub_apply_ne {p : ℕ} {m : ℕ} {i j k : Fin m} (hik : k ≠ i)
    (hjk : k ≠ j) : (Pi.single i (1 : ZMod p) - Pi.single j 1 : Fin m → ZMod p) k = 0 := by
  rw [Pi.sub_apply, Pi.single_eq_of_ne hik, Pi.single_eq_of_ne hjk, sub_zero]

private lemma hdRo7A3ReflFixAux_sub_apply_self {p : ℕ} {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    (Pi.single i (1 : ZMod p) - Pi.single j 1 : Fin m → ZMod p) i = 1 := by
  rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, sub_zero]

private lemma hdRo7A3ReflFixAux_sub_eq_right {p : ℕ} [Fact p.Prime] (hp : p = 3) {m : ℕ}
    {i j k : Fin m} (hij : i ≠ j)
    (h : (Pi.single i (1 : ZMod p) - Pi.single j 1 : Fin m → ZMod p) k = -1) : k = j := by
  by_contra hk
  by_cases hki : k = i
  · rw [hki, hdRo7A3ReflFixAux_sub_apply_self hij] at h
    exact absurd h (hdRo7A3ReflFixAux_one_ne_neg_one hp)
  · rw [hdRo7A3ReflFixAux_sub_apply_ne hki hk] at h
    exact absurd h.symm (hdRo7A3ReflFixAux_neg_one_ne_zero hp)

private lemma hdRo7A3ReflFixAux_const_eq_zero {p m : ℕ} {S : Finset (Fin m)}
    (hS : S.card < m) {w : Fin m → ZMod p} (hw : ∀ i, i ∉ S → w i = 0)
    (hc : ∃ c : ZMod p, w = fun _ => c) : w = 0 := by
  obtain ⟨c, rfl⟩ := hc
  have hex : ∃ k, k ∉ S := by
    refine hdRo7A3ReflFixAux_mem_notMem ?_
    rw [Fintype.card_fin]
    exact hS
  obtain ⟨k, hk⟩ := hex
  have hc0 : c = 0 := by simpa using hw k hk
  funext i
  simp [hc0]

private lemma hdRo7A3ReflFixAux_step {m : ℕ} (hm : 9 ≤ m) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ x, σ (σ x) = x) (S : Finset (Fin m)) (hS : ∀ x ∈ S, σ x ∈ S)
    (hcard : S.card ≤ 6) : ∃ x, x ∉ S ∧ σ x ∉ S := by
  have hlt : S.card < Fintype.card (Fin m) := by
    rw [Fintype.card_fin]; omega
  obtain ⟨x, hx⟩ := hdRo7A3ReflFixAux_mem_notMem hlt
  exact ⟨x, hx, fun hx' => hx (by rw [← hσ x]; exact hS (σ x) hx')⟩

private lemma hdRo7A3ReflFixAux_four_orbits {m : ℕ} (hm : 9 ≤ m) (σ : Equiv.Perm (Fin m))
    (hσ : σ * σ = 1) :
    ∃ x₁ x₂ x₃ x₄ : Fin m,
      x₁ ≠ x₂ ∧ x₃ ≠ x₄ ∧ σ x₁ ≠ x₂ ∧ σ x₃ ≠ x₄ ∧
      x₁ ∉ ({x₃, σ x₃, x₄, σ x₄} : Finset (Fin m)) ∧
      x₃ ∉ ({x₁, σ x₁, x₂, σ x₂} : Finset (Fin m)) := by
  classical
  have hσ' : ∀ x, σ (σ x) = x := by
    intro x
    have := congrArg (fun f : Equiv.Perm (Fin m) => f x) hσ
    simpa using this
  obtain ⟨x₁, -, -⟩ := hdRo7A3ReflFixAux_step hm σ hσ' ∅ (by simp) (by simp)
  have hS1inv : ∀ x ∈ ({x₁, σ x₁} : Finset (Fin m)), σ x ∈ ({x₁, σ x₁} : Finset (Fin m)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl <;> simp [hσ']
  obtain ⟨x₂, hx₂, -⟩ := hdRo7A3ReflFixAux_step hm σ hσ'
    ({x₁, σ x₁} : Finset (Fin m)) hS1inv (by
      have := hdRo7A3ReflFixAux_card_pair x₁ (σ x₁); omega)
  have hS2inv : ∀ x ∈ ({x₁, σ x₁, x₂, σ x₂} : Finset (Fin m)),
      σ x ∈ ({x₁, σ x₁, x₂, σ x₂} : Finset (Fin m)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> simp [hσ']
  obtain ⟨x₃, hx₃, hsx₃⟩ := hdRo7A3ReflFixAux_step hm σ hσ'
    ({x₁, σ x₁, x₂, σ x₂} : Finset (Fin m)) hS2inv (by
      have := hdRo7A3ReflFixAux_card_four x₁ (σ x₁) x₂ (σ x₂); omega)
  have hS3inv : ∀ x ∈ ({x₁, σ x₁, x₂, σ x₂, x₃, σ x₃} : Finset (Fin m)),
      σ x ∈ ({x₁, σ x₁, x₂, σ x₂, x₃, σ x₃} : Finset (Fin m)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hσ']
  obtain ⟨x₄, hx₄, hsx₄⟩ := hdRo7A3ReflFixAux_step hm σ hσ'
    ({x₁, σ x₁, x₂, σ x₂, x₃, σ x₃} : Finset (Fin m)) hS3inv (by
      have := hdRo7A3ReflFixAux_card_six x₁ (σ x₁) x₂ (σ x₂) x₃ (σ x₃); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx₂ hx₃ hsx₃ hx₄ hsx₄
  refine ⟨x₁, x₂, x₃, x₄, fun h => hx₂.1 h.symm, fun h => hx₄.2.2.2.2.1 h.symm,
    fun h => hx₂.2 h.symm, fun h => hx₄.2.2.2.2.2 h.symm, ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hx₃.1 h.symm, fun h => hsx₃.1 h.symm, fun h => hx₄.1 h.symm,
      fun h => hsx₄.1 h.symm⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact hx₃

private lemma hdRo7A3ReflFixAux_sq_one {p m : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}
    {r : V ≃ₗ[ZMod p] V} {σ : Equiv.Perm (Fin m)} (hfr : A3Frame p m θ z) (hm : 5 ≤ m)
    (hr2 : r * r = 1) (hrσ : ∀ u ∈ a3Aug p m, r (θ u) = -θ (fun i => u (σ.symm i))) :
    σ * σ = 1 := by
  have key : ∀ v ∈ a3Aug p m, θ (fun i => v (σ.symm (σ.symm i))) = θ v := by
    intro v hv
    have hv1 : (fun i => v (σ.symm i)) ∈ a3Aug p m := a3Aug_perm hv σ.symm
    have h1 : r (θ v) = -θ (fun i => v (σ.symm i)) := hrσ v hv
    have h2 : r (θ (fun i => v (σ.symm i))) =
        -θ (fun i => v (σ.symm (σ.symm i))) := hrσ _ hv1
    calc θ (fun i => v (σ.symm (σ.symm i)))
        = -(r (θ (fun i => v (σ.symm i)))) := by rw [h2]; simp
      _ = r (-θ (fun i => v (σ.symm i))) := by simp
      _ = r (r (θ v)) := by rw [h1]
      _ = θ v := by
          have h := congrArg (fun f : V ≃ₗ[ZMod p] V => f (θ v)) hr2
          simpa using h
  have hsymm : σ.symm = σ := by
    refine a3_perm_unique hfr hm ?_
    intro u hu
    have h := key (fun i => u (σ i)) (a3Aug_perm hu σ)
    simpa using h.symm
  have h : σ * σ = σ * σ.symm := by rw [hsymm]
  rw [h, ← Equiv.Perm.inv_def]
  exact mul_inv_cancel σ

private lemma hdRo7A3ReflFixAux_not_neg {p m : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}
    {r : V ≃ₗ[ZMod p] V} {σ : Equiv.Perm (Fin m)} (hfr : A3Frame p m θ z) (hm : 9 ≤ m)
    (hp : p = 3) (hrefl : GGLinRefl r)
    (hrσ : ∀ u ∈ a3Aug p m, r (θ u) = -θ (fun i => u (σ.symm i))) : False := by
  classical
  have hr2 : r * r = 1 := hrefl.1
  have hσ2 : σ * σ = 1 := hdRo7A3ReflFixAux_sq_one hfr (by omega) hr2 hrσ
  have hσ' : ∀ x, σ (σ x) = x := by
    intro x
    have := congrArg (fun f : Equiv.Perm (Fin m) => f x) hσ2
    simpa using this
  have hσsymm : σ.symm = σ := by
    rw [← Equiv.Perm.inv_def]
    exact (eq_inv_of_mul_eq_one_right hσ2).symm
  obtain ⟨x₁, x₂, x₃, x₄, hx₁₂, hx₃₄, hsx₁, hsx₃, hx₁out, hx₃out⟩ :=
    hdRo7A3ReflFixAux_four_orbits hm σ hσ2
  set u₁ : Fin m → ZMod p := Pi.single x₁ 1 - Pi.single x₂ 1 with hu₁def
  set u₂ : Fin m → ZMod p := Pi.single x₃ 1 - Pi.single x₄ 1 with hu₂def
  set v₁ : Fin m → ZMod p := u₁ + fun i => u₁ (σ.symm i) with hv₁def
  set v₂ : Fin m → ZMod p := u₂ + fun i => u₂ (σ.symm i) with hv₂def
  have hu₁ : u₁ ∈ a3Aug p m := by rw [hu₁def]; exact a3_single_sub_mem x₁ x₂
  have hu₂ : u₂ ∈ a3Aug p m := by rw [hu₂def]; exact a3_single_sub_mem x₃ x₄
  have hv₁ : v₁ ∈ a3Aug p m := by
    rw [hv₁def]; exact Submodule.add_mem _ hu₁ (a3Aug_perm hu₁ σ.symm)
  have hv₂ : v₂ ∈ a3Aug p m := by
    rw [hv₂def]; exact Submodule.add_mem _ hu₂ (a3Aug_perm hu₂ σ.symm)
  have hfin : Module.Finite (ZMod p) V := a3_moduleFinite hfr
  have hmove₁ : θ v₁ ∈ ggLinMove r := by
    have hmem : -θ v₁ ∈ ggLinMove r := by
      refine ⟨θ u₁, ?_⟩
      rw [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply, hrσ u₁ hu₁,
        hv₁def, map_add, neg_add]
      abel
    simpa using Submodule.neg_mem (ggLinMove r) hmem
  have hmove₂ : θ v₂ ∈ ggLinMove r := by
    have hmem : -θ v₂ ∈ ggLinMove r := by
      refine ⟨θ u₂, ?_⟩
      rw [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply, hrσ u₂ hu₂,
        hv₂def, map_add, neg_add]
      abel
    simpa using Submodule.neg_mem (ggLinMove r) hmem
  have hv₁x₁ : v₁ x₁ ≠ 0 := by
    intro h
    have h' : u₁ (σ x₁) = -1 := by
      have h2 : v₁ x₁ = u₁ x₁ + u₁ (σ x₁) := by
        rw [hv₁def, Pi.add_apply, hu₁def, hσsymm]
      have h3 : u₁ x₁ = 1 := by
        rw [hu₁def]; exact hdRo7A3ReflFixAux_sub_apply_self hx₁₂
      rw [h2, h3] at h
      linear_combination h
    exact hsx₁ (hdRo7A3ReflFixAux_sub_eq_right hp hx₁₂ h')
  have hv₂x₃ : v₂ x₃ ≠ 0 := by
    intro h
    have h' : u₂ (σ x₃) = -1 := by
      have h2 : v₂ x₃ = u₂ x₃ + u₂ (σ x₃) := by
        rw [hv₂def, Pi.add_apply, hu₂def, hσsymm]
      have h3 : u₂ x₃ = 1 := by
        rw [hu₂def]; exact hdRo7A3ReflFixAux_sub_apply_self hx₃₄
      rw [h2, h3] at h
      linear_combination h
    exact hsx₃ (hdRo7A3ReflFixAux_sub_eq_right hp hx₃₄ h')
  have hv₂x₁ : v₂ x₁ = 0 := by
    have hk : x₁ ∉ ({x₃, σ x₃, x₄, σ x₄} : Finset (Fin m)) := hx₁out
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [hv₂def, Pi.add_apply, hu₂def, hσsymm,
      hdRo7A3ReflFixAux_sub_apply_ne hk.1 hk.2.2.1,
      hdRo7A3ReflFixAux_sub_apply_ne ?_ ?_, add_zero]
    · exact fun h => hk.2.1 (by rw [← hσ' x₁, h])
    · exact fun h => hk.2.2.2 (by rw [← hσ' x₁, h])
  have hv₁x₃ : v₁ x₃ = 0 := by
    have hk : x₃ ∉ ({x₁, σ x₁, x₂, σ x₂} : Finset (Fin m)) := hx₃out
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [hv₁def, Pi.add_apply, hu₁def, hσsymm,
      hdRo7A3ReflFixAux_sub_apply_ne hk.1 hk.2.2.1,
      hdRo7A3ReflFixAux_sub_apply_ne ?_ ?_, add_zero]
    · exact fun h => hk.2.1 (by rw [← hσ' x₃, h])
    · exact fun h => hk.2.2.2 (by rw [← hσ' x₃, h])
  have hsupp : ∀ k, k ∉ ({x₁, σ x₁, x₂, σ x₂, x₃, σ x₃, x₄, σ x₄} : Finset (Fin m)) →
      v₁ k = 0 ∧ v₂ k = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    have hkσ₁ : σ k ≠ x₁ := fun h => hk.2.1 (by rw [← hσ' k, h])
    have hkσ₂ : σ k ≠ x₂ := fun h => hk.2.2.2.1 (by rw [← hσ' k, h])
    have hkσ₃ : σ k ≠ x₃ := fun h => hk.2.2.2.2.2.1 (by rw [← hσ' k, h])
    have hkσ₄ : σ k ≠ x₄ := fun h => hk.2.2.2.2.2.2.2 (by rw [← hσ' k, h])
    constructor
    · rw [hv₁def, Pi.add_apply, hu₁def, hσsymm,
        hdRo7A3ReflFixAux_sub_apply_ne hk.1 hk.2.2.1,
        hdRo7A3ReflFixAux_sub_apply_ne hkσ₁ hkσ₂, add_zero]
    · rw [hv₂def, Pi.add_apply, hu₂def, hσsymm,
        hdRo7A3ReflFixAux_sub_apply_ne hk.2.2.2.2.1 hk.2.2.2.2.2.2.1,
        hdRo7A3ReflFixAux_sub_apply_ne hkσ₃ hkσ₄, add_zero]
  have hli : LinearIndependent (ZMod p) ![θ v₁, θ v₂] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hmem : a • v₁ + b • v₂ ∈ a3Aug p m :=
      Submodule.add_mem _ (Submodule.smul_mem _ a hv₁) (Submodule.smul_mem _ b hv₂)
    have hzero : θ (a • v₁ + b • v₂) = 0 := by
      rw [map_add, map_smul, map_smul, hab]
    obtain ⟨c, hc⟩ := hfr.1 _ hmem hzero
    have hcard : ({x₁, σ x₁, x₂, σ x₂, x₃, σ x₃, x₄, σ x₄} : Finset (Fin m)).card < m := by
      have := hdRo7A3ReflFixAux_card_eight x₁ (σ x₁) x₂ (σ x₂) x₃ (σ x₃) x₄ (σ x₄)
      omega
    have hw : a • v₁ + b • v₂ = 0 := by
      refine hdRo7A3ReflFixAux_const_eq_zero hcard ?_ ⟨c, hc⟩
      intro k hk
      obtain ⟨h1, h2⟩ := hsupp k hk
      simp [h1, h2]
    have ha : a = 0 := by
      have h := congrArg (fun w : Fin m → ZMod p => w x₁) hw
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h
      rw [hv₂x₁, mul_zero, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_right hv₁x₁
    have hb : b = 0 := by
      have h := congrArg (fun w : Fin m → ZMod p => w x₃) hw
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h
      rw [hv₁x₃, mul_zero, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_right hv₂x₃
    exact ⟨ha, hb⟩
  have hspan_le : Submodule.span (ZMod p) (Set.range ![θ v₁, θ v₂]) ≤ ggLinMove r := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hmove₁
    · exact hmove₂
  have hdim : Module.finrank (ZMod p)
      (Submodule.span (ZMod p) (Set.range ![θ v₁, θ v₂])) = 2 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hle : 2 ≤ Module.finrank (ZMod p) (ggLinMove r) := by
    have hmono := Submodule.finrank_mono hspan_le
    omega
  have h1 := hrefl.2
  omega

theorem a3_reflFix_holds : A3ReflFixLeaf := by
  intro hN p hpFact m V instAC instMod θ z H A hD r hr hrefl hrz
  rcases hN p hD.hp m hD.hm hD.h3 V θ z hD.hfr r (hD.hStab r hr hrz) hrz with hP | ⟨-, σ, hσ⟩
  · exact hP
  · exact (hdRo7A3ReflFixAux_not_neg hD.hfr hD.hm hD.hp hrefl hσ).elim

theorem a3_stabCard_holds : A3StabCardLeaf := by
  intro hN p hpFact m V instAC instMod θ z H A hD
  classical
  let w : (a : {a : V ≃ₗ[ZMod p] V // a ∈ H ∧ a z = z}) →
      A3P p m θ z a.1 ∨ (θ (fun _ => 1) = 0 ∧ ∃ σ : Equiv.Perm (Fin m),
        ∀ u ∈ a3Aug p m, a.1 (θ u) = -θ (fun i => u (σ.symm i))) := fun a =>
    hN p hD.hp m hD.hm hD.h3 V θ z hD.hfr a.1
      (hD.hStab a.1 (hD.hHA a.2.1) a.2.2) a.2.2
  let f : (a : {a : V ≃ₗ[ZMod p] V // a ∈ H ∧ a z = z}) →
      Equiv.Perm (Fin m) × Bool := fun a =>
    if h : A3P p m θ z a.1 then (Classical.choose h, true)
    else (Classical.choose ((w a).resolve_left h).2, false)
  have hf : Function.Injective f := by
    intro a₁ a₂ heq
    apply Subtype.ext
    by_cases h1 : A3P p m θ z a₁.1
    · have h2 : A3P p m θ z a₂.1 := by
        by_contra h2
        have e1 : f a₁ = (Classical.choose h1, true) := by
          dsimp only [f]; exact dite_eq_left h1
        have e2 : f a₂ = (Classical.choose ((w a₂).resolve_left h2).2, false) := by
          dsimp only [f]; exact dite_eq_right h2
        rw [e1, e2] at heq
        exact Bool.noConfusion (congrArg Prod.snd heq)
      have e1 : f a₁ = (Classical.choose h1, true) := by
        dsimp only [f]; exact dite_eq_left h1
      have e2 : f a₂ = (Classical.choose h2, true) := by
        dsimp only [f]; exact dite_eq_left h2
      have hσ : Classical.choose h1 = Classical.choose h2 := by
        rw [e1, e2] at heq
        exact congrArg Prod.fst heq
      exact a3P_ext hD.hfr (Classical.choose_spec h1).1 a₁.2.2
        (by rw [hσ]; exact (Classical.choose_spec h2).1) a₂.2.2
    · have h2 : ¬ A3P p m θ z a₂.1 := by
        intro h2
        have e1 : f a₁ = (Classical.choose ((w a₁).resolve_left h1).2, false) := by
          dsimp only [f]; exact dite_eq_right h1
        have e2 : f a₂ = (Classical.choose h2, true) := by
          dsimp only [f]; exact dite_eq_left h2
        rw [e1, e2] at heq
        exact Bool.noConfusion (congrArg Prod.snd heq)
      have e1 : f a₁ = (Classical.choose ((w a₁).resolve_left h1).2, false) := by
        dsimp only [f]; exact dite_eq_right h1
      have e2 : f a₂ = (Classical.choose ((w a₂).resolve_left h2).2, false) := by
        dsimp only [f]; exact dite_eq_right h2
      have hσ : Classical.choose ((w a₁).resolve_left h1).2
          = Classical.choose ((w a₂).resolve_left h2).2 := by
        rw [e1, e2] at heq
        exact congrArg Prod.fst heq
      apply LinearEquiv.ext
      intro v
      obtain ⟨u, hu, c, hvu⟩ := hD.hfr.2.1 v
      have key : ∀ u ∈ a3Aug p m, a₁.1 (θ u) = a₂.1 (θ u) := by
        intro u hu
        have hs1 := Classical.choose_spec ((w a₁).resolve_left h1).2
        have hs2 := Classical.choose_spec ((w a₂).resolve_left h2).2
        rw [hs1 u hu, hs2 u hu, hσ]
      rw [hvu]
      simp only [map_add, map_smul, key u hu, a₁.2.2, a₂.2.2]
  calc Nat.card {a : V ≃ₗ[ZMod p] V // a ∈ H ∧ a z = z}
      ≤ Nat.card (Equiv.Perm (Fin m) × Bool) := Nat.card_le_card_of_injective f hf
    _ = 2 * m.factorial := by
        have h1 : Nat.card (Equiv.Perm (Fin m)) = m.factorial := by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
        have h2 : Nat.card Bool = 2 := by
          rw [Nat.card_eq_fintype_card, Fintype.card_bool]
        rw [Nat.card_prod, h1, h2]
        ring

end CFSG.StandardType.HdRo7A3
