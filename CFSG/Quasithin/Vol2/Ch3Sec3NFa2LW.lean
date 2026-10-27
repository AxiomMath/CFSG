module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LNT

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.Assembly.LowTwoRank

section Two

variable {Kb : Type} [Group Kb] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

def nfa2Fix (ρ : Kb →* (W ≃ₗ[ZMod 2] W)) : Submodule (ZMod 2) W where
  carrier := {w | ∀ k, ρ k w = w}
  add_mem' := fun {a b} ha hb k => by
    show ρ k (a + b) = a + b
    rw [map_add, ha k, hb k]
  zero_mem' := by
    show ∀ k, ρ k (0 : W) = 0
    exact fun k => map_zero (ρ k)
  smul_mem' := fun c x hx k => by
    show ρ k (c • x) = c • x
    rw [map_smul, hx k]

theorem nfa2_mem_fix {ρ : Kb →* (W ≃ₗ[ZMod 2] W)} {w : W} :
    w ∈ nfa2Fix ρ ↔ ∀ k, ρ k w = w :=
  Iff.rfl

theorem nfa2_map_fix_eq {σ τ : Kb →* (W ≃ₗ[ZMod 2] W)}
    (hc : ∀ k l, σ k * τ l = τ l * σ k) (l : Kb) :
    (nfa2Fix σ).map (τ l : W →ₗ[ZMod 2] W) = nfa2Fix σ := by
  have hle : ∀ m : Kb, (nfa2Fix σ).map (τ m : W →ₗ[ZMod 2] W) ≤ nfa2Fix σ := by
    intro m
    rintro _ ⟨w, hw, rfl⟩
    rw [nfa2_mem_fix]
    intro k
    have h1 : σ k ((τ m : W →ₗ[ZMod 2] W) w) = (τ m : W →ₗ[ZMod 2] W) (σ k w) :=
      congrArg (fun f : W ≃ₗ[ZMod 2] W => f w) (hc k m)
    rw [h1, nfa2_mem_fix.1 hw k]
  refine le_antisymm (hle l) ?_
  intro w hw
  have hinv : τ l * τ l⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  refine Submodule.mem_map.2 ⟨τ l⁻¹ w, hle l⁻¹ (Submodule.mem_map_of_mem hw), ?_⟩
  exact congrArg (fun f : W ≃ₗ[ZMod 2] W => f w) hinv

def nfa2Restrict (ρ : Kb →* (W ≃ₗ[ZMod 2] W)) (A : Submodule (ZMod 2) W)
    (hA : ∀ k, A.map (ρ k : W →ₗ[ZMod 2] W) = A) : Kb →* (A ≃ₗ[ZMod 2] A) where
  toFun k := LinearEquiv.ofSubmodules (ρ k) A A (hA k)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : W ≃ₗ[ZMod 2] W => f (x : W)) (map_one ρ)
  map_mul' k l := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : W ≃ₗ[ZMod 2] W => f (x : W)) (map_mul ρ k l)

theorem nfa2_finrank_range_restrict {A : Submodule (ZMod 2) W} (T : W →ₗ[ZMod 2] W)
    (TA : A →ₗ[ZMod 2] A) (hTA : ∀ x : A, ((TA x : A) : W) = T x) :
    Module.finrank (ZMod 2) (LinearMap.range TA) =
      Module.finrank (ZMod 2) (Submodule.map T A) := by
  have hcomp : A.subtype.comp TA = T.comp A.subtype := LinearMap.ext hTA
  have hmap : (LinearMap.range TA).map A.subtype = Submodule.map T A := by
    rw [← LinearMap.range_comp, hcomp, LinearMap.range_comp, Submodule.range_subtype]
  rw [← Submodule.finrank_map_subtype_eq A (LinearMap.range TA), hmap]

theorem nfa2_prodRep_mk (ρ₁ ρ₂ : Kb →* (W ≃ₗ[ZMod 2] W))
    (hcomm : ∀ k k', ρ₁ k * ρ₂ k' = ρ₂ k' * ρ₁ k) (k k' : Kb) :
    nfa2ProdRep ρ₁ ρ₂ hcomm (k, k') = ρ₁ k * ρ₂ k' :=
  rfl

end Two

theorem nfa2_two_factor_bounds (hG1 : Leaf_G1) (hG2 : Leaf_G2) (hG3 : Leaf_G3)
    (q : ℕ) (hq : q.Prime) (h24 : q % 24 = 11 ∨ q % 24 = 13)
    (Kb : Type) [Group Kb] (hmodel : StatedClassicalModel Kb .PSL 2 q 1)
    (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ₁ ρ₂ : Kb →* (W ≃ₗ[ZMod 2] W))
    (hcomm : ∀ k k', ρ₁ k * ρ₂ k' = ρ₂ k' * ρ₁ k)
    (h₁ : ∃ k, ρ₁ k ≠ 1) (h₂ : ∃ k, ρ₂ k ≠ 1)
    (hfix : ∀ w : W, (∀ k, ρ₁ k w = w) → (∀ k, ρ₂ k w = w) → w = 0)
    (hdich : ((∀ w : W, (∀ k, ρ₁ k w = w) → w = 0) ∧ (∀ w : W, (∀ k, ρ₂ k w = w) → w = 0)) ∨
      (∀ w : W, ∃ a b : W, (∀ k, ρ₁ k a = a) ∧ (∀ k, ρ₂ k b = b) ∧ w = a + b))
    (i : Kb) (hi : orderOf i = 2) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range ((ρ₁ i).toLinearMap - LinearMap.id)) ∧
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range ((ρ₂ i).toLinearMap - LinearMap.id)) ∧
    5 ≤ Module.finrank (ZMod 2) (LinearMap.range ((ρ₁ i * ρ₂ i).toLinearMap - LinearMap.id)) := by
  rcases hdich with ⟨hd1, hd2⟩ | hdich2
  ·
    have hdim : 20 ≤ Module.finrank (ZMod 2) W :=
      nfa2_two_factor_dim q hq h24 Kb hmodel W ρ₁ ρ₂ hcomm h₁ h₂
    have hG2₁ := hG2 q hq h24 Kb hmodel W ρ₁ hd1 i hi
    have hG2₂ := hG2 q hq h24 Kb hmodel W ρ₂ hd2 i hi
    have hfixP : ∀ x : W, (∀ p : Kb × Kb, nfa2ProdRep ρ₁ ρ₂ hcomm p x = x) → x = 0 := by
      intro x hx
      apply hd1 x
      intro k
      have h := hx (k, 1)
      rw [nfa2_prodRep_mk, map_one, mul_one] at h
      exact h
    have hG3' := hG3 q hq h24 Kb hmodel W (nfa2ProdRep ρ₁ ρ₂ hcomm) hfixP i hi
    rw [show nfa2ProdRep ρ₁ ρ₂ hcomm (i, i) = ρ₁ i * ρ₂ i from nfa2_prodRep_mk ρ₁ ρ₂ hcomm i i]
      at hG3'
    exact ⟨by omega, by omega, by omega⟩
  ·
    have hA_inv : ∀ l, (nfa2Fix ρ₁).map (ρ₂ l : W →ₗ[ZMod 2] W) = nfa2Fix ρ₁ :=
      fun l => nfa2_map_fix_eq (σ := ρ₁) (τ := ρ₂) hcomm l
    have hB_inv : ∀ l, (nfa2Fix ρ₂).map (ρ₁ l : W →ₗ[ZMod 2] W) = nfa2Fix ρ₂ :=
      fun l => nfa2_map_fix_eq (σ := ρ₂) (τ := ρ₁) (fun k l' => (hcomm l' k).symm) l
    have hne₂ : ∃ l, ∃ a ∈ nfa2Fix ρ₁, ρ₂ l a ≠ a := by
      obtain ⟨k, hk⟩ := h₂
      by_contra hcon
      apply hk
      ext w
      obtain ⟨a, b, ha, hb, rfl⟩ := hdich2 w
      have hfa : ρ₂ k a = a := by
        by_contra hne
        exact hcon ⟨k, a, nfa2_mem_fix.2 ha, hne⟩
      rw [map_add, hfa, hb k]
      rfl
    have hne₁ : ∃ k, ∃ b ∈ nfa2Fix ρ₂, ρ₁ k b ≠ b := by
      obtain ⟨k, hk⟩ := h₁
      by_contra hcon
      apply hk
      ext w
      obtain ⟨a, b, ha, hb, rfl⟩ := hdich2 w
      have hfb : ρ₁ k b = b := by
        by_contra hne
        exact hcon ⟨k, b, nfa2_mem_fix.2 hb, hne⟩
      rw [map_add, ha k, hfb]
      rfl
    obtain ⟨R₂, hR₂⟩ : ∃ R : Kb →* (nfa2Fix ρ₁ ≃ₗ[ZMod 2] nfa2Fix ρ₁),
        ∀ l (x : nfa2Fix ρ₁), ((R l x : nfa2Fix ρ₁) : W) = ρ₂ l x :=
      ⟨nfa2Restrict ρ₂ (nfa2Fix ρ₁) hA_inv, fun l x => rfl⟩
    obtain ⟨R₁, hR₁⟩ : ∃ R : Kb →* (nfa2Fix ρ₂ ≃ₗ[ZMod 2] nfa2Fix ρ₂),
        ∀ l (y : nfa2Fix ρ₂), ((R l y : nfa2Fix ρ₂) : W) = ρ₁ l y :=
      ⟨nfa2Restrict ρ₁ (nfa2Fix ρ₂) hB_inv, fun l y => rfl⟩
    have hR₂ne : ∃ k, R₂ k ≠ 1 := by
      obtain ⟨l, a, ha, hla⟩ := hne₂
      refine ⟨l, fun h => hla ?_⟩
      have h' : ((R₂ l ⟨a, ha⟩ : nfa2Fix ρ₁) : W) =
          (((1 : nfa2Fix ρ₁ ≃ₗ[ZMod 2] nfa2Fix ρ₁) ⟨a, ha⟩ : nfa2Fix ρ₁) : W) := by
        rw [h]
      rw [hR₂] at h'
      exact h'
    have hR₁ne : ∃ k, R₁ k ≠ 1 := by
      obtain ⟨k, b, hb, hkb⟩ := hne₁
      refine ⟨k, fun h => hkb ?_⟩
      have h' : ((R₁ k ⟨b, hb⟩ : nfa2Fix ρ₂) : W) =
          (((1 : nfa2Fix ρ₂ ≃ₗ[ZMod 2] nfa2Fix ρ₂) ⟨b, hb⟩ : nfa2Fix ρ₂) : W) := by
        rw [h]
      rw [hR₁] at h'
      exact h'
    have hR₂fix : ∀ x : nfa2Fix ρ₁, (∀ k, R₂ k x = x) → x = 0 := by
      intro x hx
      have hx0 : (x : W) = 0 := by
        refine hfix (x : W) (nfa2_mem_fix.1 x.2) ?_
        intro k
        have h := congrArg Subtype.val (hx k)
        rw [hR₂] at h
        exact h
      exact Subtype.ext hx0
    have hR₁fix : ∀ y : nfa2Fix ρ₂, (∀ k, R₁ k y = y) → y = 0 := by
      intro y hy
      have hy0 : (y : W) = 0 := by
        refine hfix (y : W) ?_ (nfa2_mem_fix.1 y.2)
        intro k
        have h := congrArg Subtype.val (hy k)
        rw [hR₁] at h
        exact h
      exact Subtype.ext hy0
    have hG1A : 10 ≤ Module.finrank (ZMod 2) (nfa2Fix ρ₁) :=
      hG1 q hq h24 Kb hmodel (nfa2Fix ρ₁) R₂ hR₂ne
    have hG1B : 10 ≤ Module.finrank (ZMod 2) (nfa2Fix ρ₂) :=
      hG1 q hq h24 Kb hmodel (nfa2Fix ρ₂) R₁ hR₁ne
    have hG2A := hG2 q hq h24 Kb hmodel (nfa2Fix ρ₁) R₂ hR₂fix i hi
    have hG2B := hG2 q hq h24 Kb hmodel (nfa2Fix ρ₂) R₁ hR₁fix i hi
    have hTA₂ : ∀ x : nfa2Fix ρ₁,
        ((((R₂ i).toLinearMap - LinearMap.id : nfa2Fix ρ₁ →ₗ[ZMod 2] nfa2Fix ρ₁) x :
          nfa2Fix ρ₁) : W) =
          (((ρ₂ i).toLinearMap - LinearMap.id : W →ₗ[ZMod 2] W) (x : W)) := by
      intro x
      simp [hR₂]
    have hTB₁ : ∀ y : nfa2Fix ρ₂,
        ((((R₁ i).toLinearMap - LinearMap.id : nfa2Fix ρ₂ →ₗ[ZMod 2] nfa2Fix ρ₂) y :
          nfa2Fix ρ₂) : W) =
          (((ρ₁ i).toLinearMap - LinearMap.id : W →ₗ[ZMod 2] W) (y : W)) := by
      intro y
      simp [hR₁]
    have hT₂ := nfa2_finrank_range_restrict ((ρ₂ i).toLinearMap - LinearMap.id)
      ((R₂ i).toLinearMap - LinearMap.id) hTA₂
    have hT₁ := nfa2_finrank_range_restrict ((ρ₁ i).toLinearMap - LinearMap.id)
      ((R₁ i).toLinearMap - LinearMap.id) hTB₁
    have hU₂ : 4 ≤ Module.finrank (ZMod 2)
        (Submodule.map ((ρ₂ i).toLinearMap - LinearMap.id) (nfa2Fix ρ₁)) := by
      omega
    have hU₁ : 4 ≤ Module.finrank (ZMod 2)
        (Submodule.map ((ρ₁ i).toLinearMap - LinearMap.id) (nfa2Fix ρ₂)) := by
      omega
    have hr₂ : 4 ≤ Module.finrank (ZMod 2)
        (LinearMap.range ((ρ₂ i).toLinearMap - LinearMap.id)) :=
      le_trans hU₂ (Submodule.finrank_mono (LinearMap.map_le_range))
    have hr₁ : 4 ≤ Module.finrank (ZMod 2)
        (LinearMap.range ((ρ₁ i).toLinearMap - LinearMap.id)) :=
      le_trans hU₁ (Submodule.finrank_mono (LinearMap.map_le_range))
    have hA_pres : ∀ l, ∀ x ∈ nfa2Fix ρ₁, ρ₂ l x ∈ nfa2Fix ρ₁ := by
      intro l x hx
      have h := Submodule.mem_map_of_mem (f := (ρ₂ l : W →ₗ[ZMod 2] W)) hx
      rw [hA_inv l] at h
      exact h
    have hB_pres : ∀ l, ∀ y ∈ nfa2Fix ρ₂, ρ₁ l y ∈ nfa2Fix ρ₂ := by
      intro l y hy
      have h := Submodule.mem_map_of_mem (f := (ρ₁ l : W →ₗ[ZMod 2] W)) hy
      rw [hB_inv l] at h
      exact h
    have hU_le : Submodule.map ((ρ₂ i).toLinearMap - LinearMap.id) (nfa2Fix ρ₁) ≤ nfa2Fix ρ₁ := by
      rintro _ ⟨x, hx, rfl⟩
      have h2 : ((ρ₂ i).toLinearMap - LinearMap.id : W →ₗ[ZMod 2] W) x = ρ₂ i x - x := by simp
      rw [h2]
      exact (nfa2Fix ρ₁).sub_mem (hA_pres i x hx) hx
    have hV_le : Submodule.map ((ρ₁ i).toLinearMap - LinearMap.id) (nfa2Fix ρ₂) ≤ nfa2Fix ρ₂ := by
      rintro _ ⟨y, hy, rfl⟩
      have h2 : ((ρ₁ i).toLinearMap - LinearMap.id : W →ₗ[ZMod 2] W) y = ρ₁ i y - y := by simp
      rw [h2]
      exact (nfa2Fix ρ₂).sub_mem (hB_pres i y hy) hy
    have hdisj : Submodule.map ((ρ₂ i).toLinearMap - LinearMap.id) (nfa2Fix ρ₁) ⊓
        Submodule.map ((ρ₁ i).toLinearMap - LinearMap.id) (nfa2Fix ρ₂) = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_bot]
      exact hfix w (nfa2_mem_fix.1 (hU_le (Submodule.mem_inf.1 hw).1))
        (nfa2_mem_fix.1 (hV_le (Submodule.mem_inf.1 hw).2))
    have hUV : Submodule.map ((ρ₂ i).toLinearMap - LinearMap.id) (nfa2Fix ρ₁) ⊔
        Submodule.map ((ρ₁ i).toLinearMap - LinearMap.id) (nfa2Fix ρ₂) ≤
        LinearMap.range ((ρ₁ i * ρ₂ i).toLinearMap - LinearMap.id) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        refine LinearMap.mem_range.2 ⟨x, ?_⟩
        have h1 : ρ₁ i (ρ₂ i x) = ρ₂ i x := nfa2_mem_fix.1 (hA_pres i x hx) i
        show ((ρ₁ i * ρ₂ i).toLinearMap - LinearMap.id : W →ₗ[ZMod 2] W) x =
          ((ρ₂ i).toLinearMap - LinearMap.id : W →ₗ[ZMod 2] W) x
        simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap,
          LinearEquiv.mul_apply, h1]
      · rintro _ ⟨y, hy, rfl⟩
        refine LinearMap.mem_range.2 ⟨y, ?_⟩
        have h1 : ρ₂ i y = y := nfa2_mem_fix.1 hy i
        show ((ρ₁ i * ρ₂ i).toLinearMap - LinearMap.id : W →ₗ[ZMod 2] W) y =
          ((ρ₁ i).toLinearMap - LinearMap.id : W →ₗ[ZMod 2] W) y
        simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap,
          LinearEquiv.mul_apply, h1]
    have hfin := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.map ((ρ₂ i).toLinearMap - LinearMap.id) (nfa2Fix ρ₁))
      (Submodule.map ((ρ₁ i).toLinearMap - LinearMap.id) (nfa2Fix ρ₂))
    rw [hdisj, finrank_bot] at hfin
    have hmono := Submodule.finrank_mono hUV
    have hr₃ : 5 ≤ Module.finrank (ZMod 2)
        (LinearMap.range ((ρ₁ i * ρ₂ i).toLinearMap - LinearMap.id)) := by
      omega
    exact ⟨hr₁, hr₂, hr₃⟩

end CFSG.Quasithin.H13.NFa2
