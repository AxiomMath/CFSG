module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCARes
public import CFSG.LocalAnalysis.StandardType.GGHalfKGCANum
public import CFSG.LocalAnalysis.StandardType.GGHalfKGCANat
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

namespace CFSG.StandardType

private lemma ggKGCACent_add_self {M : Type} [AddCommGroup M] [Module GGKGCF M] (x : M) :
    x + x = 0 := by
  have h : (2 : GGKGCF) = 0 := CharP.cast_eq_zero GGKGCF 2
  rw [← two_smul GGKGCF x, h, zero_smul]

private lemma ggKGCACent_mem_sup {V : Type} [AddCommGroup V] [Module GGKGCF V]
    {W T : Submodule GGKGCF V} (hc : IsCompl W T) (v : V) :
    ∃ w ∈ W, ∃ t ∈ T, w + t = v :=
  Submodule.mem_sup.mp (by rw [hc.sup_eq_top]; exact Submodule.mem_top)

private lemma ggKGCACent_mapsTo_T {V : Type} [AddCommGroup V] [Module GGKGCF V]
    [FiniteDimensional GGKGCF V]
    (J : Subgroup (V ≃ₗ[GGKGCF] V)) (W T : Submodule GGKGCF V) (hc : IsCompl W T)
    (hTfix : ∀ a ∈ J, ∀ t ∈ T, a t = t)
    (hWfull : ∀ φ : W ≃ₗ[GGKGCF] W, ∃ a ∈ J, ∀ w : W, (a (w : V) : V) = (φ w : V))
    (h2 : 2 ≤ Module.finrank GGKGCF W)
    (g : V ≃ₗ[GGKGCF] V) (hg : g ∈ Subgroup.centralizer (J : Set (V ≃ₗ[GGKGCF] V))) :
    ∀ t ∈ T, g t ∈ T := by
  intro t ht
  have hfix : ∀ a ∈ J, a (g t) = g t := by
    intro a ha
    have hcomm : a * g = g * a := Subgroup.mem_centralizer_iff.mp hg a ha
    have h := congrArg (fun e : V ≃ₗ[GGKGCF] V => e t) hcomm
    simp only [LinearEquiv.mul_apply] at h
    rw [hTfix a ha t ht] at h
    exact h
  obtain ⟨w, hw, t', ht', hwt⟩ := ggKGCACent_mem_sup hc (g t)
  have hw0W : (⟨w, hw⟩ : W) = 0 := by
    apply ggKGCANat_no_fixed h2
    intro φ
    obtain ⟨a, haJ, ha⟩ := hWfull φ
    have ha' := hfix a haJ
    rw [← hwt, map_add, hTfix a haJ t' ht'] at ha'
    have haw : a w = w := add_right_cancel ha'
    apply Subtype.ext
    rw [← ha ⟨w, hw⟩, haw]
  have hw0 : w = 0 := by simpa using congrArg Subtype.val hw0W
  rw [hw0, zero_add] at hwt
  rw [← hwt]
  exact ht'

private lemma ggKGCACent_mapsTo_W {V : Type} [AddCommGroup V] [Module GGKGCF V]
    [FiniteDimensional GGKGCF V]
    (J : Subgroup (V ≃ₗ[GGKGCF] V)) (W T : Submodule GGKGCF V) (hc : IsCompl W T)
    (hWst : ∀ a ∈ J, ∀ w ∈ W, a w ∈ W)
    (hTfix : ∀ a ∈ J, ∀ t ∈ T, a t = t)
    (hWfull : ∀ φ : W ≃ₗ[GGKGCF] W, ∃ a ∈ J, ∀ w : W, (a (w : V) : V) = (φ w : V))
    (h2 : 2 ≤ Module.finrank GGKGCF W)
    (g : V ≃ₗ[GGKGCF] V) (hg : g ∈ Subgroup.centralizer (J : Set (V ≃ₗ[GGKGCF] V))) :
    ∀ w ∈ W, g w ∈ W := by
  intro w hw
  by_cases hw0 : w = 0
  · rw [hw0, map_zero]; exact W.zero_mem
  · let wW : W := ⟨w, hw⟩
    have hwW0 : wW ≠ 0 := by
      intro h
      exact hw0 (congrArg (fun x : W => (x : V)) h)
    have hspan_ne_top : Submodule.span GGKGCF ({wW} : Set W) ≠ ⊤ := by
      intro htop
      have hfr : Module.finrank GGKGCF W = 1 := by
        rw [← finrank_top GGKGCF W, ← htop, finrank_span_singleton hwW0]
      omega
    obtain ⟨w'W, hw'W⟩ : ∃ x : W, x ∉ Submodule.span GGKGCF ({wW} : Set W) := by
      by_contra h
      push Not at h
      exact hspan_ne_top ((Submodule.eq_top_iff').mpr h)
    have hw'W0 : w'W ≠ 0 := by
      intro h
      exact hw'W (by rw [h]; exact Submodule.zero_mem _)
    have hw'Ww : w'W ≠ wW := by
      intro h
      exact hw'W (by rw [h]; exact Submodule.mem_span_singleton_self wW)
    have hsum : wW + w'W ≠ 0 := by
      intro h
      apply hw'Ww
      have h1 : wW + (wW + w'W) = wW + 0 := by rw [h, add_zero]
      rw [← add_assoc, ggKGCACent_add_self wW, zero_add] at h1
      simpa using h1
    obtain ⟨φ, hφ⟩ := ggKGCANat_transitive w'W (wW + w'W) hw'W0 hsum
    obtain ⟨a, haJ, ha⟩ := hWfull φ
    have haw : a (w'W : V) = w + (w'W : V) := by
      have h := ha w'W
      rw [hφ] at h
      simpa using h
    have haw' : a (w'W : V) - (w'W : V) = w := by
      rw [haw]; abel
    obtain ⟨u, hu, t, ht, hut⟩ := ggKGCACent_mem_sup hc (g (w'W : V))
    have hga : g (a (w'W : V)) = a (g (w'W : V)) := by
      have h := congrArg (fun e : V ≃ₗ[GGKGCF] V => e (w'W : V))
        (Subgroup.mem_centralizer_iff.mp hg a haJ)
      simp only [LinearEquiv.mul_apply] at h
      exact h.symm
    have hgw : g w = a u - u := by
      calc g w = g (a (w'W : V) - (w'W : V)) := by rw [haw']
        _ = g (a (w'W : V)) - g (w'W : V) := map_sub g _ _
        _ = a (g (w'W : V)) - g (w'W : V) := by rw [hga]
        _ = a (u + t) - (u + t) := by rw [← hut]
        _ = (a u + t) - (u + t) := by rw [map_add, hTfix a haJ t ht]
        _ = a u - u := by abel
    rw [hgw]
    exact W.sub_mem (hWst a haJ u hu) hu

private lemma ggKGCACent_fixes_W {V : Type} [AddCommGroup V] [Module GGKGCF V]
    [FiniteDimensional GGKGCF V]
    (J : Subgroup (V ≃ₗ[GGKGCF] V)) (W T : Submodule GGKGCF V) (hc : IsCompl W T)
    (hWst : ∀ a ∈ J, ∀ w ∈ W, a w ∈ W)
    (hTfix : ∀ a ∈ J, ∀ t ∈ T, a t = t)
    (hWfull : ∀ φ : W ≃ₗ[GGKGCF] W, ∃ a ∈ J, ∀ w : W, (a (w : V) : V) = (φ w : V))
    (h2 : 2 ≤ Module.finrank GGKGCF W)
    (g : V ≃ₗ[GGKGCF] V) (hg : g ∈ Subgroup.centralizer (J : Set (V ≃ₗ[GGKGCF] V))) :
    ∀ w ∈ W, g w = w := by
  have hgW : ∀ w ∈ W, g w ∈ W :=
    ggKGCACent_mapsTo_W J W T hc hWst hTfix hWfull h2 g hg
  have hgW' : ∀ w ∈ W, g⁻¹ w ∈ W :=
    ggKGCACent_mapsTo_W J W T hc hWst hTfix hWfull h2 g⁻¹ (Subgroup.inv_mem _ hg)
  let gW : W ≃ₗ[GGKGCF] W := ggKGCARestrict W g hgW hgW'
  have hgW_val : ∀ x : W, ((gW x : W) : V) = g ((x : W) : V) :=
    fun x => ggKGCARestrict_apply W g hgW hgW' x
  have hcenter : ∀ h : W ≃ₗ[GGKGCF] W, gW * h = h * gW := by
    intro h
    obtain ⟨a, haJ, ha⟩ := hWfull h
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change g ((h x : W) : V) = ((h (gW x) : W) : V)
    have hcomm_apply : g (a ((x : W) : V)) = a (g ((x : W) : V)) := by
      have hh := congrArg (fun e : V ≃ₗ[GGKGCF] V => e ((x : W) : V))
        (Subgroup.mem_centralizer_iff.mp hg a haJ)
      simp only [LinearEquiv.mul_apply] at hh
      exact hh.symm
    rw [← ha x, hcomm_apply, ← hgW_val x, ha (gW x)]
  have hgW1 : gW = 1 := ggKGCANat_center gW hcenter
  intro w hw
  have h := congrArg (fun e : W ≃ₗ[GGKGCF] W => ((e ⟨w, hw⟩ : W) : V)) hgW1
  rw [hgW_val ⟨w, hw⟩] at h
  simpa using h

private lemma ggKGCACent_res_injective {V : Type} [AddCommGroup V] [Module GGKGCF V]
    [FiniteDimensional GGKGCF V]
    (J : Subgroup (V ≃ₗ[GGKGCF] V)) (W T : Submodule GGKGCF V) (hc : IsCompl W T)
    (hWst : ∀ a ∈ J, ∀ w ∈ W, a w ∈ W)
    (hTfix : ∀ a ∈ J, ∀ t ∈ T, a t = t)
    (hWfull : ∀ φ : W ≃ₗ[GGKGCF] W, ∃ a ∈ J, ∀ w : W, (a (w : V) : V) = (φ w : V))
    (h2 : 2 ≤ Module.finrank GGKGCF W)
    (hS : ∀ a ∈ Subgroup.centralizer (J : Set (V ≃ₗ[GGKGCF] V)), ∀ x ∈ T, a x ∈ T) :
    Function.Injective
      (ggKGCARes T (Subgroup.centralizer (J : Set (V ≃ₗ[GGKGCF] V))) hS) := by
  intro a b hab
  have key : ∀ c : Subgroup.centralizer (J : Set (V ≃ₗ[GGKGCF] V)),
      ggKGCARes T (Subgroup.centralizer (J : Set (V ≃ₗ[GGKGCF] V))) hS c = 1 → c = 1 := by
    intro c hc1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change (c : V ≃ₗ[GGKGCF] V) v = v
    have hcW : ∀ w ∈ W, (c : V ≃ₗ[GGKGCF] V) w = w :=
      ggKGCACent_fixes_W J W T hc hWst hTfix hWfull h2 c c.2
    have hcT : ∀ t ∈ T, (c : V ≃ₗ[GGKGCF] V) t = t := by
      intro t ht
      have h := congrArg (fun e : T ≃ₗ[GGKGCF] T => ((e ⟨t, ht⟩ : T) : V)) hc1
      rw [ggKGCARes_apply] at h
      simpa using h
    obtain ⟨w, hw, t, ht, hwt⟩ := ggKGCACent_mem_sup hc v
    calc (c : V ≃ₗ[GGKGCF] V) v = (c : V ≃ₗ[GGKGCF] V) (w + t) := by rw [hwt]
      _ = (c : V ≃ₗ[GGKGCF] V) w + (c : V ≃ₗ[GGKGCF] V) t :=
          map_add (c : V ≃ₗ[GGKGCF] V) w t
      _ = w + t := by rw [hcW w hw, hcT t ht]
      _ = v := hwt
  have hab' : a / b = 1 := by
    apply key
    rw [map_div, hab]
    exact div_eq_one.mpr rfl
  exact div_eq_one.mp hab'

theorem ggKGCACent
    {V : Type} [AddCommGroup V] [Module GGKGCF V] [FiniteDimensional GGKGCF V]
    (J : Subgroup (V ≃ₗ[GGKGCF] V)) (W T : Submodule GGKGCF V) (hc : IsCompl W T)
    (hWst : ∀ a ∈ J, ∀ w ∈ W, a w ∈ W)
    (hTfix : ∀ a ∈ J, ∀ t ∈ T, a t = t)
    (hWfull : ∀ φ : W ≃ₗ[GGKGCF] W, ∃ a ∈ J, ∀ w : W, (a (w : V) : V) = (φ w : V))
    (h2 : 2 ≤ Module.finrank GGKGCF W) (hT2 : Module.finrank GGKGCF T = 2) :
    Group.IsSolvable ↥(Subgroup.centralizer (J : Set (V ≃ₗ[GGKGCF] V))) := by
  haveI : Finite T := Module.finite_of_finite GGKGCF
  haveI : Finite (T ≃ₗ[GGKGCF] T) :=
    Finite.of_injective (fun e : T ≃ₗ[GGKGCF] T => (e : T → T))
      (fun e1 e2 h => LinearEquiv.ext (congrFun h))
  have hTcard : Nat.card (T ≃ₗ[GGKGCF] T) = 6 := ggKGCANum_card_aut_two hT2
  haveI : Group.IsSolvable (T ≃ₗ[GGKGCF] T) :=
    CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hTcard]; norm_num)
  have hS : ∀ a ∈ Subgroup.centralizer (J : Set (V ≃ₗ[GGKGCF] V)), ∀ x ∈ T, a x ∈ T :=
    fun a ha => ggKGCACent_mapsTo_T J W T hc hTfix hWfull h2 a ha
  exact Group.isSolvable_of_isSolvable_injective
    (f := ggKGCARes T (Subgroup.centralizer (J : Set (V ≃ₗ[GGKGCF] V))) hS)
    (ggKGCACent_res_injective J W T hc hWst hTfix hWfull h2 hS)

end CFSG.StandardType

end
