module

public import CFSG.LocalAnalysis.StandardType.GGWeylNoEichlerACoord
public import CFSG.LocalAnalysis.StandardType.GGQ2EichlerDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggWeylNoEichlerRho_A {n : ℕ} (hn : 5 ≤ n) :
    GGWeylNoEichlerRho (CartanMatrix.A n) := by
  intro U _ _ h α hb hspan hα g hg hgne
  classical
  have hn4 : 4 ≤ n := by omega
  obtain ⟨Φ, hinj, hΦswap⟩ := ggQ2xKD_A_model hn4 h hb hspan α hα
  let bU : Basis (Fin n) (ZMod 3) U := Basis.mk hb (le_of_eq hspan.symm)
  have hbU : ∀ k, h k = bU k := fun k => (Basis.mk_apply hb (le_of_eq hspan.symm) k).symm
  let x : Fin (n + 1) → Module.Dual (ZMod 3) U := fun a => ggAE_x bU a
  have hx_h : ∀ a k, x a (h k) =
      (if a = k.castSucc then (1 : ZMod 3) else 0)
        - (if a = k.succ then (1 : ZMod 3) else 0) := by
    intro a k
    dsimp only [x]
    rw [hbU k]
    exact ggAE_x_self bU a k
  have hαx : ∀ i, α i = x i.castSucc - x i.succ := by
    intro i
    apply Basis.ext
    intro j
    rw [show bU j = h j from (hbU j).symm]
    rw [hα i j, LinearMap.sub_apply, hx_h i.castSucc j, hx_h i.succ j]
    exact ggAE_A_eq n i j
  have hequiv : ∀ σ a u, x a (Φ σ u) = x (σ⁻¹ a) u :=
    ggAE_x_equiv h α Φ hΦswap x hαx hx_h
  have hgen_top : Subgroup.closure
      (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ n)
  have hWle : ggQ2WeylOf h α ≤ Φ.range := by
    intro t ht
    rw [ggQ2WeylOf] at ht
    refine Subgroup.closure_induction (p := fun t _ => t ∈ Φ.range) ?_ ?_ ?_ ?_ ht
    · rintro s ⟨j, hs⟩
      exact MonoidHom.mem_range.mpr ⟨Equiv.swap j.castSucc j.succ,
        LinearEquiv.ext fun v => (hΦswap j v).trans (hs v).symm⟩
    · exact Subgroup.one_mem _
    · intro x y _ _ hx hy; exact Subgroup.mul_mem _ hx hy
    · intro x _ hx; exact Subgroup.inv_mem _ hx
  have hle2 : Φ.range ≤ ggQ2WeylOf h α := by
    rintro _ ⟨σ, rfl⟩
    have hmem : σ ∈ Subgroup.closure
        (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
      rw [hgen_top]; trivial
    refine Subgroup.closure_induction (p := fun τ _ => Φ τ ∈ ggQ2WeylOf h α)
      ?_ ?_ ?_ ?_ hmem
    · rintro t ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨i, fun v => hΦswap i v⟩
    · rw [map_one]; exact Subgroup.one_mem _
    · intro σ τ _ _ hσ hτ
      rw [map_mul]; exact Subgroup.mul_mem _ hσ hτ
    · intro σ _ hσ
      rw [map_inv]; exact Subgroup.inv_mem _ hσ
  have hWdef : ggQ2WeylOf h α = Φ.range := le_antisymm hWle hle2
  have hgΦ : g ∈ Φ.range := by rw [← hWdef]; exact hg
  obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp hgΦ
  have hσne : σ ≠ 1 := by
    intro h1
    apply hgne
    rw [← hσ, h1, map_one]
  by_contra hcon
  have hN : ∀ u i, α i (g (g u) + g u + u) = 0 := by
    intro u i
    by_contra hh
    exact hcon ⟨u, i, hh⟩
  have hconst : ∀ (u : U) (c c' : Fin (n + 1)),
      x c (g (g u) + g u + u) = x c' (g (g u) + g u + u) := by
    intro u
    apply ggAE_const_of_adj
    intro i
    have hh := hN u i
    rw [hαx i, LinearMap.sub_apply] at hh
    exact sub_eq_zero.mp hh
  have hg' : g = Φ σ := hσ.symm
  have hequiv_g : ∀ a u, x a (g u) = x (σ⁻¹ a) u := by
    intro a u
    rw [hg']
    exact hequiv σ a u
  have hequiv_g2 : ∀ a u, x a (g (g u)) = x (σ⁻¹ (σ⁻¹ a)) u := by
    intro a u
    rw [hequiv_g a (g u), hequiv_g (σ⁻¹ a) u]
  have hfixN : ∀ u, g (g (g u) + g u + u) = g (g u) + g u + u := by
    intro u
    have hw : ∀ c : Fin (n + 1),
        x c (g (g (g u) + g u + u) - (g (g u) + g u + u)) = 0 := by
      intro c
      rw [map_sub, hequiv_g c (g (g u) + g u + u), hconst u (σ⁻¹ c) c, sub_self]
    exact sub_eq_zero.mp (ggAE_sep bU (by omega) _ (fun j => hw j.castSucc))
  have hg3 : g ^ 3 = 1 := by
    ext u
    rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have h1 := hfixN u
    simp only [map_add] at h1
    exact add_right_cancel (by
      calc g (g (g u)) + (g (g u) + g u)
          = g (g (g u)) + g (g u) + g u := by abel
        _ = g (g u) + g u + u := h1
        _ = u + (g (g u) + g u) := by abel)
  have hσ3 : σ ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hσ, hg3, map_one]
  have hσ3_apply : ∀ x : Fin (n + 1), σ (σ (σ x)) = x := by
    intro x
    have h := congrFun (congrArg (fun e : Equiv.Perm (Fin (n + 1)) =>
      (e : Fin (n + 1) → Fin (n + 1))) hσ3) x
    simpa [pow_three, Equiv.Perm.mul_apply] using h
  have hσinv_apply : ∀ x : Fin (n + 1), σ⁻¹ x = σ (σ x) := by
    intro x
    calc σ⁻¹ x = σ⁻¹ (σ (σ (σ x))) := by rw [hσ3_apply x]
      _ = σ (σ x) := by rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  have hσinv2_apply : ∀ x : Fin (n + 1), σ⁻¹ (σ⁻¹ x) = σ x := by
    intro x
    rw [hσinv_apply (σ⁻¹ x), hσinv_apply x]
    exact hσ3_apply (σ x)
  have hy : ∀ (u : U) (c : Fin (n + 1)), x c (g (g u) + g u + u) =
      x (σ c) u + x (σ (σ c)) u + x c u := by
    intro u c
    have e1 : x c (g (g u)) = x (σ c) u := by
      rw [hequiv_g2 c u, hσinv2_apply c]
    have e2 : x c (g u) = x (σ (σ c)) u := by
      rw [hequiv_g c u, hσinv_apply c]
    rw [map_add, map_add, e1, e2]
  have hex : ∃ a : Fin (n + 1), σ a ≠ a := by
    by_contra h
    apply hσne
    apply Equiv.Perm.ext
    intro a
    show σ a = a
    exact not_not.mp (not_exists.mp h a)
  obtain ⟨a, ha⟩ := hex
  have ha2 : σ (σ a) ≠ a := by
    intro h
    have h' := congrArg (fun x => σ x) h
    rw [hσ3_apply a] at h'
    exact ha h'.symm
  let O : Finset (Fin (n + 1)) := {a, σ a, σ (σ a)}
  have hOcard : O.card = 3 := by
    have h1 : a ∉ ({σ a, σ (σ a)} : Finset (Fin (n + 1))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact ha h.symm
      · exact ha2 h.symm
    have h2 : σ a ∉ ({σ (σ a)} : Finset (Fin (n + 1))) := by
      simp only [Finset.mem_singleton]
      intro h
      apply ha2
      have h' := congrArg (fun x => σ x) h
      rw [hσ3_apply a] at h'
      exact h'
    simp only [O, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_singleton]
  have hlt : O.card < (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [hOcard, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨d, -, hdO⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hdO' : d ≠ a ∧ d ≠ σ a ∧ d ≠ σ (σ a) := by
    simpa [O, Finset.mem_insert, Finset.mem_singleton] using hdO
  have ha_d : a ≠ d := fun h => hdO'.1 h.symm
  have hd_a : d ≠ a := fun h => ha_d h.symm
  have hσa_d : σ a ≠ d := fun h => hdO'.2.1 h.symm
  have hσ2a_d : σ (σ a) ≠ d := fun h => hdO'.2.2 h.symm
  have hσd_a : σ d ≠ a := by
    intro h
    have h' := congrArg (fun x => σ (σ x)) h
    rw [hσ3_apply d] at h'
    exact hdO'.2.2 h'
  have hσ2d_a : σ (σ d) ≠ a := by
    intro h
    have h' := congrArg (fun x => σ x) h
    rw [hσ3_apply d] at h'
    exact hdO'.2.1 h'
  obtain ⟨u, hu⟩ := ggAE_exists_diff h bU hbU a d ha_d
  have hya : x a (g (g u) + g u + u) = 1 := by
    rw [hy u a]
    dsimp only [x]
    rw [hu a, hu (σ a), hu (σ (σ a))]
    simp only [if_neg ha, if_neg ha2, if_neg hσa_d, if_neg hσ2a_d, if_neg ha_d]
    norm_num
  have hyd : x d (g (g u) + g u + u) = 0 ∨ x d (g (g u) + g u + u) = -1 := by
    rw [hy u d]
    dsimp only [x]
    rw [hu d, hu (σ d), hu (σ (σ d))]
    by_cases hfix : σ d = d
    · left
      have hfix2 : σ (σ d) = d := by rw [hfix, hfix]
      simp only [if_neg hd_a, if_pos hfix, if_pos hfix2, if_neg hσd_a, if_neg hσ2d_a]
      decide
    · right
      have hfix2 : σ (σ d) ≠ d := by
        intro h
        apply hfix
        have h' := congrArg (fun x => σ x) h
        rw [hσ3_apply d] at h'
        exact h'.symm
      simp only [if_neg hd_a, if_neg hfix, if_neg hfix2, if_neg hσd_a, if_neg hσ2d_a]
      decide
  have hconst_ad := hconst u a d
  rw [hya] at hconst_ad
  rcases hyd with h | h
  · rw [h] at hconst_ad
    exact (by decide : (1 : ZMod 3) ≠ 0) hconst_ad
  · rw [h] at hconst_ad
    exact (by decide : (1 : ZMod 3) ≠ -1) hconst_ad

end CFSG.StandardType

end
