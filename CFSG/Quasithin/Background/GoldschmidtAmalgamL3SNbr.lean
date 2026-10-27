module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XFix
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SPush
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2Label

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem ncard_nbrs_γ₀ : (nbrs (γ₀ (A ⊔ B) A B)).ncard = 3 := by
  let q : ↥A → CosetGeom (A ⊔ B) A B := fun k =>
    (⟨(k : D), (le_sup_left : A ≤ A ⊔ B) k.2⟩ : ↥(A ⊔ B)) • γ₁ (A ⊔ B) A B
  have hq : ∀ k k' : ↥A, q k = q k' ↔ k⁻¹ * k' ∈ (A ⊓ B).subgroupOf A := by
    intro k k'
    have e : (⟨(k' : D), (le_sup_left : A ≤ A ⊔ B) k'.2⟩ : ↥(A ⊔ B)) =
        ⟨(k : D), (le_sup_left : A ≤ A ⊔ B) k.2⟩ *
        ⟨((k⁻¹ * k' : ↥A) : D), (le_sup_left : A ≤ A ⊔ B) (k⁻¹ * k').2⟩ := by
      apply Subtype.ext
      simp
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hqq
      have h1 : (⟨((k⁻¹ * k' : ↥A) : D), (le_sup_left : A ≤ A ⊔ B) (k⁻¹ * k').2⟩ : ↥(A ⊔ B)) •
          γ₁ (A ⊔ B) A B = γ₁ (A ⊔ B) A B := by
        refine smul_left_cancel (⟨(k : D), (le_sup_left : A ≤ A ⊔ B) k.2⟩ : ↥(A ⊔ B)) ?_
        simp only [q] at hqq
        rw [← mul_smul, ← e]
        exact hqq.symm
      have h2 := mem_stab_of_smul_eq h1
      rw [stab_γ₁ (le_sup_right : B ≤ A ⊔ B)] at h2
      exact ⟨(k⁻¹ * k').2, h2⟩
    · intro hmem
      have h1 : (⟨((k⁻¹ * k' : ↥A) : D), (le_sup_left : A ≤ A ⊔ B) (k⁻¹ * k').2⟩ : ↥(A ⊔ B)) •
          γ₁ (A ⊔ B) A B = γ₁ (A ⊔ B) A B := smul_γ₁_of_mem (le_sup_right : B ≤ A ⊔ B) hmem.2
      simp only [q]
      rw [e, mul_smul, h1]
  let Q : (↥A ⧸ (A ⊓ B).subgroupOf A) → CosetGeom (A ⊔ B) A B :=
    Quotient.lift (s := QuotientGroup.leftRel _) q (fun a b hab => by
      exact (hq a b).mpr (QuotientGroup.leftRel_apply.mp hab))
  have hQinj : Function.Injective Q := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b =>
        have : q a = q b := hxy
        exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hq a b).mp this))
  have hrange : Set.range Q = nbrs (γ₀ (A ⊔ B) A B) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      induction x using Quotient.inductionOn with
      | h k =>
        have h0 : (⟨(k : D), (le_sup_left : A ≤ A ⊔ B) k.2⟩ : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B =
            γ₀ (A ⊔ B) A B := smul_γ₀_of_mem (le_sup_left : A ≤ A ⊔ B) k.2
        have := (smul_adj (⟨(k : D), (le_sup_left : A ≤ A ⊔ B) k.2⟩ : ↥(A ⊔ B))).mpr
          (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B))
        rw [h0] at this
        exact this
    · intro hy
      obtain ⟨g, hg0, hg1⟩ := exists_stab_smul_eq
        (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)) hy
      have hgA : (g : D) ∈ A := by
        have := mem_stab_of_smul_eq hg0
        rwa [stab_γ₀ (le_sup_left : A ≤ A ⊔ B)] at this
      refine ⟨((⟨(g : D), hgA⟩ : ↥A) : ↥A ⧸ (A ⊓ B).subgroupOf A), ?_⟩
      show q ⟨(g : D), hgA⟩ = y
      simp only [q]
      exact hg1
  have hcard : Nat.card ↥(Set.range Q) = Nat.card (↥A ⧸ (A ⊓ B).subgroupOf A) :=
    Nat.card_range_of_injective hQinj
  have h3 : Nat.card (↥A ⧸ (A ⊓ B).subgroupOf A) = 3 := h.gold.relIndex_left
  rw [← Nat.card_coe_set_eq, ← hrange, hcard, h3]

theorem ncard_nbrs_γ₁ : (nbrs (γ₁ (A ⊔ B) A B)).ncard = 3 := by
  let q : ↥B → CosetGeom (A ⊔ B) A B := fun k =>
    (⟨(k : D), (le_sup_right : B ≤ A ⊔ B) k.2⟩ : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B
  have hq : ∀ k k' : ↥B, q k = q k' ↔ k⁻¹ * k' ∈ (A ⊓ B).subgroupOf B := by
    intro k k'
    have e : (⟨(k' : D), (le_sup_right : B ≤ A ⊔ B) k'.2⟩ : ↥(A ⊔ B)) =
        ⟨(k : D), (le_sup_right : B ≤ A ⊔ B) k.2⟩ *
        ⟨((k⁻¹ * k' : ↥B) : D), (le_sup_right : B ≤ A ⊔ B) (k⁻¹ * k').2⟩ := by
      apply Subtype.ext
      simp
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hqq
      have h1 : (⟨((k⁻¹ * k' : ↥B) : D), (le_sup_right : B ≤ A ⊔ B) (k⁻¹ * k').2⟩ : ↥(A ⊔ B)) •
          γ₀ (A ⊔ B) A B = γ₀ (A ⊔ B) A B := by
        refine smul_left_cancel (⟨(k : D), (le_sup_right : B ≤ A ⊔ B) k.2⟩ : ↥(A ⊔ B)) ?_
        simp only [q] at hqq
        rw [← mul_smul, ← e]
        exact hqq.symm
      have h2 := mem_stab_of_smul_eq h1
      rw [stab_γ₀ (le_sup_left : A ≤ A ⊔ B)] at h2
      exact ⟨h2, (k⁻¹ * k').2⟩
    · intro hmem
      have h1 : (⟨((k⁻¹ * k' : ↥B) : D), (le_sup_right : B ≤ A ⊔ B) (k⁻¹ * k').2⟩ : ↥(A ⊔ B)) •
          γ₀ (A ⊔ B) A B = γ₀ (A ⊔ B) A B := smul_γ₀_of_mem (le_sup_left : A ≤ A ⊔ B) hmem.1
      simp only [q]
      rw [e, mul_smul, h1]
  let Q : (↥B ⧸ (A ⊓ B).subgroupOf B) → CosetGeom (A ⊔ B) A B :=
    Quotient.lift (s := QuotientGroup.leftRel _) q (fun a b hab => by
      exact (hq a b).mpr (QuotientGroup.leftRel_apply.mp hab))
  have hQinj : Function.Injective Q := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b =>
        have : q a = q b := hxy
        exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hq a b).mp this))
  have hrange : Set.range Q = nbrs (γ₁ (A ⊔ B) A B) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      induction x using Quotient.inductionOn with
      | h k =>
        have h0 : (⟨(k : D), (le_sup_right : B ≤ A ⊔ B) k.2⟩ : ↥(A ⊔ B)) • γ₁ (A ⊔ B) A B =
            γ₁ (A ⊔ B) A B := smul_γ₁_of_mem (le_sup_right : B ≤ A ⊔ B) k.2
        have := (smul_adj (⟨(k : D), (le_sup_right : B ≤ A ⊔ B) k.2⟩ : ↥(A ⊔ B))).mpr
          (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)).symm
        rw [h0] at this
        exact this
    · intro hy
      obtain ⟨g, hg1, hg0⟩ := exists_stab_smul_eq
        (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)).symm hy
      have hgB : (g : D) ∈ B := by
        have := mem_stab_of_smul_eq hg1
        rwa [stab_γ₁ (le_sup_right : B ≤ A ⊔ B)] at this
      refine ⟨((⟨(g : D), hgB⟩ : ↥B) : ↥B ⧸ (A ⊓ B).subgroupOf B), ?_⟩
      show q ⟨(g : D), hgB⟩ = y
      simp only [q]
      exact hg0
  have hcard : Nat.card ↥(Set.range Q) = Nat.card (↥B ⧸ (A ⊓ B).subgroupOf B) :=
    Nat.card_range_of_injective hQinj
  have h3 : Nat.card (↥B ⧸ (A ⊓ B).subgroupOf B) = 3 := h.gold.relIndex_right
  rw [← Nat.card_coe_set_eq, ← hrange, hcard, h3]

theorem ncard_nbrs (w : CosetGeom (A ⊔ B) A B) : (nbrs w).ncard = 3 := by
  have key : ∀ (g : ↥(A ⊔ B)) (v : CosetGeom (A ⊔ B) A B),
      (nbrs (g • v)).ncard = (nbrs v).ncard := by
    intro g v
    have : nbrs (g • v) = (fun y => g • y) '' nbrs v := by
      ext y
      constructor
      · intro hy
        refine ⟨g⁻¹ • y, ?_, by simp⟩
        have := (smul_adj g⁻¹).mpr (show (graph (A ⊔ B) A B).Adj (g • v) y from hy)
        rwa [inv_smul_smul] at this
      · rintro ⟨y', hy', rfl⟩
        exact (smul_adj g).mpr (show (graph (A ⊔ B) A B).Adj v y' from hy')
    rw [this, Set.ncard_image_of_injective _ (MulAction.injective g)]
  cases hv : vtype w with
  | false =>
    obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hv
    rw [key]
    exact h.ncard_nbrs_γ₀
  | true =>
    obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
    rw [key]
    exact h.ncard_nbrs_γ₁

theorem nbr_four {w y₁ y₂ y₃ y₄ : CosetGeom (A ⊔ B) A B}
    (h1 : (graph (A ⊔ B) A B).Adj w y₁) (h2 : (graph (A ⊔ B) A B).Adj w y₂)
    (h3 : (graph (A ⊔ B) A B).Adj w y₃) (h4 : (graph (A ⊔ B) A B).Adj w y₄)
    (n12 : y₁ ≠ y₂) (n13 : y₁ ≠ y₃) (n14 : y₁ ≠ y₄) (n23 : y₂ ≠ y₃) (n24 : y₂ ≠ y₄)
    (n34 : y₃ ≠ y₄) : False := by
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Set.ncard_eq_three.mp (h.ncard_nbrs w)
  have hm : ∀ y, (graph (A ⊔ B) A B).Adj w y → y = a ∨ y = b ∨ y = c := by
    intro y hy
    have : y ∈ nbrs w := hy
    rw [hset] at this
    simpa using this
  rcases hm y₁ h1 with rfl | rfl | rfl <;> rcases hm y₂ h2 with rfl | rfl | rfl <;>
    rcases hm y₃ h3 with rfl | rfl | rfl <;> rcases hm y₄ h4 with rfl | rfl | rfl <;>
    simp_all

theorem exists_third {w u v : CosetGeom (A ⊔ B) A B} (huv : u ≠ v) :
    ∃ x, (graph (A ⊔ B) A B).Adj w x ∧ x ≠ u ∧ x ≠ v := by
  by_contra hcon
  push Not at hcon
  have hsub : nbrs w ⊆ {u, v} := fun y hy => by
    by_cases hyu : y = u
    · simp [hyu]
    · simp [hcon y hy hyu]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h.ncard_nbrs w] at this
  have h2 : ({u, v} : Set (CosetGeom (A ⊔ B) A B)).ncard = 2 := Set.ncard_pair huv
  omega

theorem mem_ballStab_one_of_fix_two' {u v w : CosetGeom (A ⊔ B) A B}
    (hv : (graph (A ⊔ B) A B).Adj u v) (hw : (graph (A ⊔ B) A B).Adj u w) (hvw : v ≠ w) {x : D}
    (hxu : x ∈ stab u) (hxv : x ∈ stab v) (hxw : x ∈ stab w) : x ∈ ballStab 1 u := by
  cases hu : vtype u with
  | false => exact h.mem_ballStab_one_of_fix_two_A hu hv hw hvw hxu hxv hxw
  | true => exact h.mem_ballStab_one_of_fix_two hu hv hw hvw hxu hxv hxw

theorem exists_smul_of_not_le {w u x x' : CosetGeom (A ⊔ B) A B}
    (hu : (graph (A ⊔ B) A B).Adj w u) (hx : (graph (A ⊔ B) A B).Adj w x)
    (hx' : (graph (A ⊔ B) A B).Adj w x') (hux : u ≠ x) (hux' : u ≠ x') (hxx' : x ≠ x')
    {H : Subgroup D} (hHw : H ≤ stab w) (hHu : H ≤ stab u) (hH : ¬ H ≤ ballStab 1 w) :
    ∃ k : ↥(A ⊔ B), (k : D) ∈ H ∧ k • x = x' := by
  obtain ⟨t, htH, htn⟩ := IsConcreteLE.not_le_iff_exists.mp hH
  have htG : t ∈ A ⊔ B := stab_le w (hHw htH)
  refine ⟨⟨t, htG⟩, htH, ?_⟩
  have hkw : (⟨t, htG⟩ : ↥(A ⊔ B)) • w = w := smul_eq_of_mem_stab (hHw htH)
  have hku : (⟨t, htG⟩ : ↥(A ⊔ B)) • u = u := smul_eq_of_mem_stab (hHu htH)
  have hkx : (graph (A ⊔ B) A B).Adj w ((⟨t, htG⟩ : ↥(A ⊔ B)) • x) := by
    have := (smul_adj (⟨t, htG⟩ : ↥(A ⊔ B))).mpr hx
    rwa [hkw] at this
  have hkxu : (⟨t, htG⟩ : ↥(A ⊔ B)) • x ≠ u := fun e =>
    hux (smul_left_cancel (⟨t, htG⟩ : ↥(A ⊔ B)) (e.trans hku.symm)).symm
  have hkxx : (⟨t, htG⟩ : ↥(A ⊔ B)) • x ≠ x := by
    intro e
    apply htn
    exact h.mem_ballStab_one_of_fix_two' hu hx hux (hHw htH) (hHu htH) (mem_stab_of_smul_eq e)
  by_contra hne
  exact h.nbr_four hu hx hx' hkx hux hux' hkxu.symm hxx' hkxx.symm (Ne.symm hne)

theorem not_stab_inf_le_ballStab_one {u v : CosetGeom (A ⊔ B) A B}
    (huv : (graph (A ⊔ B) A B).Adj u v) (hu : vtype u = false) :
    ¬ stab u ⊓ stab v ≤ ballStab 1 u := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB huv hu
  rw [stab_smul, stab_smul, ballStab_smul, ballStab_one_γ₀_eq_pCoreOf h.gold,
    stab_γ₀ (le_sup_left : A ≤ A ⊔ B), stab_γ₁ (le_sup_right : B ≤ A ⊔ B), ← conjSub_inf]
  intro hle
  have h1 : A ⊓ B ≤ pCoreOf 2 A := by
    have := (conjSub_le_iff (g : D)).mp hle
    rwa [conjSub_conjSub_inv] at this
  have h2 : (pCoreOf 2 A).relIndex (A ⊓ B) = 1 := Subgroup.relIndex_eq_one.mpr h1
  rw [h.gold.relIndex_pCoreOf_T_left] at h2
  omega

theorem not_ballStab_le_of_left {u v : CosetGeom (A ⊔ B) A B}
    (huv : (graph (A ⊔ B) A B).Adj u v) (hu : vtype u = false) :
    ¬ ballStab 1 u ≤ ballStab 1 v := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB huv hu
  rw [ballStab_smul, ballStab_smul, ballStab_one_γ₀_eq_pCoreOf h.gold,
    ballStab_one_γ₁_eq_pCoreOf h.gold]
  intro hle
  have h1 : pCoreOf 2 A ≤ pCoreOf 2 B := by
    have := (conjSub_le_iff (g : D)).mp hle
    rwa [conjSub_conjSub_inv] at this
  exact h.gold.symm.not_pCoreOf_right_le_left (h.gold.pCoreOf_ne h.card_inf_ne_two).symm h1

theorem not_ballStab_le_of_right {u v : CosetGeom (A ⊔ B) A B}
    (huv : (graph (A ⊔ B) A B).Adj u v) (hu : vtype u = false) :
    ¬ ballStab 1 v ≤ ballStab 1 u := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB huv hu
  rw [ballStab_smul, ballStab_smul, ballStab_one_γ₀_eq_pCoreOf h.gold,
    ballStab_one_γ₁_eq_pCoreOf h.gold]
  intro hle
  have h1 : pCoreOf 2 B ≤ pCoreOf 2 A := by
    have := (conjSub_le_iff (g : D)).mp hle
    rwa [conjSub_conjSub_inv] at this
  exact h.gold.not_pCoreOf_right_le_left (h.gold.pCoreOf_ne h.card_inf_ne_two) h1

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
