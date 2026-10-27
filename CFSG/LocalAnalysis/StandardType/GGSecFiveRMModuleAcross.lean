module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleConnected

public section

namespace CFSG.StandardType

section Module

private lemma ggLinMove_mul_le
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (g h : V ≃ₗ[ZMod p] V) :
    ggLinMove (g * h) ≤ ggLinMove g ⊔ ggLinMove h := by
  intro x hx
  simp only [ggLinMove] at hx
  obtain ⟨v, rfl⟩ := hx
  have hsplit : (((g * h : V ≃ₗ[ZMod p] V).toLinearMap : V →ₗ[ZMod p] V)
        - (LinearMap.id : V →ₗ[ZMod p] V)) v
      = ((g.toLinearMap : V →ₗ[ZMod p] V) - (LinearMap.id : V →ₗ[ZMod p] V)) (h v)
        + ((h.toLinearMap : V →ₗ[ZMod p] V) - (LinearMap.id : V →ₗ[ZMod p] V)) v := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.mul_apply]
    abel
  rw [hsplit]
  exact Submodule.add_mem_sup
    (LinearMap.mem_range_self (g.toLinearMap - (LinearMap.id : V →ₗ[ZMod p] V)) (h v))
    (LinearMap.mem_range_self (h.toLinearMap - (LinearMap.id : V →ₗ[ZMod p] V)) v)

private lemma ggLinMove_inv_le
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (g : V ≃ₗ[ZMod p] V) :
    ggLinMove g⁻¹ ≤ ggLinMove g := by
  rw [show g⁻¹ = g.symm from rfl]
  intro x hx
  simp only [ggLinMove] at hx ⊢
  obtain ⟨v, rfl⟩ := hx
  rw [LinearMap.mem_range]
  refine ⟨-(g.symm v), ?_⟩
  rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.id_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap, map_neg,
    LinearEquiv.apply_symm_apply]
  abel

private lemma ggLinMove_closure_le
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {T : Set (V ≃ₗ[ZMod p] V)} {a : V ≃ₗ[ZMod p] V}
    (ha : a ∈ Subgroup.closure T) :
    ggLinMove a ≤ ⨆ t ∈ T, ggLinMove t := by
  refine Subgroup.closure_induction (p := fun a _ => ggLinMove a ≤ ⨆ t ∈ T, ggLinMove t)
    ?_ ?_ ?_ ?_ ha
  · intro x hx
    exact le_iSup₂ (f := fun t (_ : t ∈ T) => ggLinMove t) x hx
  · simp only [ggLinMove]
    have hone : (1 : V ≃ₗ[ZMod p] V).toLinearMap - LinearMap.id = 0 := by
      ext v; simp
    rw [hone, LinearMap.range_zero]
    exact bot_le
  · intro x y _ _ ihx ihy
    exact (ggLinMove_mul_le x y).trans (sup_le ihx ihy)
  · intro x _ ih
    exact (ggLinMove_inv_le x).trans ih

private lemma ggLinCom_closure_le
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {T : Set (V ≃ₗ[ZMod p] V)} :
    ggLinCom (Subgroup.closure T : Set (V ≃ₗ[ZMod p] V)) ≤ ⨆ t ∈ T, ggLinMove t := by
  refine iSup_le fun a => iSup_le fun ha => ggLinMove_closure_le ha

private lemma ggLinCom_mono
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {A B : Set (V ≃ₗ[ZMod p] V)} (h : A ⊆ B) :
    ggLinCom A ≤ ggLinCom B := by
  refine iSup_le fun a => iSup_le fun ha => ?_
  exact le_iSup₂ (f := fun t (_ : t ∈ B) => ggLinMove t) a (h ha)

private lemma ggLin_closure_fix
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {T : Set (V ≃ₗ[ZMod p] V)} {u : V}
    (hfix : ∀ t ∈ T, t u = u) {a : V ≃ₗ[ZMod p] V} (ha : a ∈ Subgroup.closure T) :
    a u = u := by
  let K : Subgroup (V ≃ₗ[ZMod p] V) :=
    { carrier := {a | a u = u}
      one_mem' := rfl
      mul_mem' := by
        intro a b ha hb
        change (a * b) u = u
        rw [LinearEquiv.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        change a⁻¹ u = u
        rw [show a⁻¹ = a.symm from rfl]
        have h : a.symm (a u) = a.symm u := congrArg a.symm ha
        rw [LinearEquiv.symm_apply_apply] at h
        exact h.symm }
  exact (Subgroup.closure_le K).mpr (fun t ht => hfix t ht) ha

private lemma exists_mem_of_closure_move
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {T : Set (V ≃ₗ[ZMod p] V)}
    {a : V ≃ₗ[ZMod p] V} {u : V} (ha : a ∈ Subgroup.closure T) (hau : a u ≠ u) :
    ∃ t ∈ T, t u ≠ u := by
  by_contra h
  push Not at h
  exact hau (ggLin_closure_fix h ha)

theorem ggLin_propagate_across
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {I : Type*} (S : I → Set (V ≃ₗ[ZMod p] V))
    (hS : ∀ X, ∀ r ∈ S X, GGLinRefl r)
    (hconn : ∀ X, ∀ r ∈ S X, ∀ s ∈ S X, Relation.EqvGen (fun a b => a ∈ S X ∧ b ∈ S X ∧ GGLinAdj a b) r s)
    (AJ : Subgroup (V ≃ₗ[ZMod p] V)) (hJ : ∀ X, AJ ≤ Subgroup.closure (S X))
    (hJnt : ∃ a ∈ AJ, ∃ u ∈ ggLinCom (AJ : Set (V ≃ₗ[ZMod p] V)), a u ≠ u)
    (W : Submodule (ZMod p) V) (hW : ∀ a ∈ ⨆ X, Subgroup.closure (S X), ∀ w ∈ W, a w ∈ W) :
    W ≤ ggLinFix ((⨆ X, Subgroup.closure (S X) : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V)) ∨
      ggLinCom ((⨆ X, Subgroup.closure (S X) : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V)) ≤ W := by
  by_cases hfixW : W ≤
      ggLinFix ((⨆ X, Subgroup.closure (S X) : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V))
  · exact Or.inl hfixW
  · right
    have hAeq : (⨆ X, Subgroup.closure (S X) : Subgroup (V ≃ₗ[ZMod p] V))
        = Subgroup.closure (⋃ X, S X) := by
      rw [Subgroup.closure_iUnion]
    have hAeqSet : ((⨆ X, Subgroup.closure (S X) : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V))
        = (Subgroup.closure (⋃ X, S X) : Set (V ≃ₗ[ZMod p] V)) := by
      rw [hAeq]
    have hWle : ∀ X, ∀ a ∈ Subgroup.closure (S X), ∀ w ∈ W, a w ∈ W :=
      fun X a ha w hw => hW a (le_iSup (fun X => Subgroup.closure (S X)) X ha) w hw
    rw [SetLike.le_def] at hfixW
    push Not at hfixW
    obtain ⟨w, hwW, hwfix⟩ := hfixW
    have hwfix' : ¬ ∀ a ∈ (⨆ X, Subgroup.closure (S X) : Subgroup (V ≃ₗ[ZMod p] V)),
        a w = w := by
      intro h; exact hwfix h
    push Not at hwfix'
    obtain ⟨a, haA, haw⟩ := hwfix'
    have haCl : a ∈ Subgroup.closure (⋃ X, S X) := by
      rw [← hAeq]; exact haA
    obtain ⟨t, htU, htw⟩ := exists_mem_of_closure_move haCl haw
    obtain ⟨X₀, htS⟩ := Set.mem_iUnion.mp htU
    have h0 : ∀ s ∈ S X₀, ggLinMove s ≤ W :=
      ggLin_propagate_connected (S X₀) (hS X₀) (hconn X₀) W
        (fun a ha w hw => hWle X₀ a ha w hw) ⟨t, htS, w, hwW, htw⟩
    have hcom0 : ggLinCom (Subgroup.closure (S X₀) : Set (V ≃ₗ[ZMod p] V)) ≤ W :=
      (ggLinCom_closure_le (T := S X₀)).trans (iSup_le fun s => iSup_le fun hs => h0 s hs)
    have hcomAJ : ggLinCom (AJ : Set (V ≃ₗ[ZMod p] V)) ≤ W :=
      (ggLinCom_mono (fun a ha => hJ X₀ ha)).trans hcom0
    obtain ⟨a₀, ha₀J, u, huAJ, ha₀u⟩ := hJnt
    have huW : u ∈ W := hcomAJ huAJ
    have hgen : ∀ Y, ∀ s ∈ S Y, ggLinMove s ≤ W := by
      intro Y s hs
      have ha₀Cl : a₀ ∈ Subgroup.closure (S Y) := hJ Y ha₀J
      obtain ⟨s₀, hs₀, hs₀u⟩ := exists_mem_of_closure_move ha₀Cl ha₀u
      exact ggLin_propagate_connected (S Y) (hS Y) (hconn Y) W
        (fun a ha w hw => hWle Y a ha w hw) ⟨s₀, hs₀, u, huW, hs₀u⟩ s hs
    show ggLinCom
      ((⨆ X, Subgroup.closure (S X) : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V)) ≤ W
    rw [hAeqSet]
    refine (ggLinCom_closure_le (T := ⋃ X, S X)).trans (iSup_le fun s => iSup_le fun hs => ?_)
    obtain ⟨Y, hsY⟩ := Set.mem_iUnion.mp hs
    exact hgen Y s hsY

end Module

end CFSG.StandardType

end
