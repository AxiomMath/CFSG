module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoTransfer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixModuleAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixModuleAux2
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixModuleAux3

public section

namespace CFSG.StandardType.E6QTwo

open Module
open CFSG.Blueprint.Chevalley

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V}

theorem apply_mem_span_range_of_mem_e6Weyl (hα : ∀ i, α i (h i) = 2)
    {g : V ≃ₗ[ZMod 3] V} (hg : g ∈ e6Weyl hα) {v : V}
    (hv : v ∈ Submodule.span (ZMod 3) (Set.range h)) :
    g v ∈ Submodule.span (ZMod 3) (Set.range h) := by
  have hgen : ∀ i, ∀ v ∈ Submodule.span (ZMod 3) (Set.range h),
      reflection (hα i) v ∈ Submodule.span (ZMod 3) (Set.range h) := fun i v hv => by
    rw [reflection_apply]
    exact sub_mem hv (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  suffices key : ∀ v ∈ Submodule.span (ZMod 3) (Set.range h),
      g v ∈ Submodule.span (ZMod 3) (Set.range h) from key v hv
  refine Subgroup.closure_induction''
    (p := fun g _ => ∀ v ∈ Submodule.span (ZMod 3) (Set.range h),
      g v ∈ Submodule.span (ZMod 3) (Set.range h)) ?_ ?_ ?_ ?_ hg
  · rintro x ⟨i, rfl⟩
    exact hgen i
  · rintro x ⟨i, rfl⟩
    rw [reflection_inv]
    exact hgen i
  · intro v hv
    simpa using hv
  · intro x y _ _ hx hy v hv
    rw [LinearEquiv.mul_apply]
    exact hx _ (hy v hv)

theorem span_range_eq_of_card_six (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hα : ∀ i, α i (h i) = 2) (hV : Nat.card V = 3 ^ 6)
    (hW : Nat.card (e6Weyl hα) = 51840) {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hA : A ≤ e6Weyl hα)
    (hcardA : 720 ≤ Nat.card A) {x : V} (hx : x ≠ 0) (hAx : ∀ g ∈ A, g x = x)
    {H : Submodule (ZMod 3) V} (hH : Nat.card H = 3 ^ 5) (hxH : x ∈ H)
    (hAH : ∀ g ∈ A, ∀ v, g v - v ∈ H)
    (hfix : ∀ v, (∀ g ∈ A, g v - v ∈ (ZMod 3) ∙ x) → v ∈ (ZMod 3) ∙ x) :
    Submodule.span (ZMod 3) (Set.range h) = H :=
  spanH_eq_of_card_six hP hα hV hW hA hcardA hx hAx hH hxH hAH hfix

theorem mem_of_mem_e6Weyl_of_apply_eq_of_card_six
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hα : ∀ i, α i (h i) = 2) (hV : Nat.card V = 3 ^ 6)
    (hW : Nat.card (e6Weyl hα) = 51840) {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hA : A ≤ e6Weyl hα)
    (hcardA : 720 ≤ Nat.card A) {x : V} (hx : x ≠ 0) (hAx : ∀ g ∈ A, g x = x)
    {H : Submodule (ZMod 3) V} (hH : Nat.card H = 3 ^ 5) (hxH : x ∈ H)
    (hAH : ∀ g ∈ A, ∀ v, g v - v ∈ H)
    (hfix : ∀ v, (∀ g ∈ A, g v - v ∈ (ZMod 3) ∙ x) → v ∈ (ZMod 3) ∙ x)
    {g : V ≃ₗ[ZMod 3] V} (hg : g ∈ e6Weyl hα) (hgx : g x = x) : g ∈ A := by
  classical
  have hSH : spanH h = H :=
    spanH_eq_of_card_six hP hα hV hW hA hcardA hx hAx hH hxH hAH hfix
  have hxS : x ∈ spanH h := by rw [hSH]; exact hxH
  have hS_card : Nat.card (spanH h) = 3 ^ 5 := by rw [hSH]; exact hH
  obtain ⟨B', hB', hxx2, hstab⟩ :=
    norm_two_and_stabilizer_of_card_six hP hα hW hA hcardA hx hAx hxS hS_card
  have hAle : Nat.card A ≤ Nat.card (MulAction.stabilizer (e6Weyl hα) x) :=
    card_le_stabilizer_of_forall_apply_eq hA hAx
  rw [hstab] at hAle
  have hcardA' : Nat.card A = 720 := le_antisymm hAle hcardA
  have : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun a b h => LinearEquiv.ext (by simpa using congrFun h))
  haveI : Fintype ↥(e6Weyl hα) := Fintype.ofFinite _
  have hgstab : (⟨g, hg⟩ : ↥(e6Weyl hα)) ∈ MulAction.stabilizer (e6Weyl hα) x := by
    rw [MulAction.mem_stabilizer_iff]
    simpa [Subgroup.smul_def, LinearEquiv.smul_def] using hgx
  have hsub_le : A.subgroupOf (e6Weyl hα) ≤ MulAction.stabilizer (e6Weyl hα) x := by
    intro y hy
    rw [MulAction.mem_stabilizer_iff]
    rw [Subgroup.mem_subgroupOf] at hy
    simpa [Subgroup.smul_def, LinearEquiv.smul_def] using hAx y hy
  have heq : A.subgroupOf (e6Weyl hα) = MulAction.stabilizer (e6Weyl hα) x := by
    apply Subgroup.eq_of_le_of_card_ge hsub_le
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hcardA', hstab]
  rw [← heq] at hgstab
  rwa [Subgroup.mem_subgroupOf] at hgstab

theorem exists_reflection_of_card_six
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hα : ∀ i, α i (h i) = 2) (hV : Nat.card V = 3 ^ 6)
    (hW : Nat.card (e6Weyl hα) = 51840) {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hA : A ≤ e6Weyl hα)
    (hcardA : 720 ≤ Nat.card A) {x : V} (hx : x ≠ 0) (hAx : ∀ g ∈ A, g x = x)
    {H : Submodule (ZMod 3) V} (hH : Nat.card H = 3 ^ 5) (hxH : x ∈ H)
    (hAH : ∀ g ∈ A, ∀ v, g v - v ∈ H)
    (hfix : ∀ v, (∀ g ∈ A, g v - v ∈ (ZMod 3) ∙ x) → v ∈ (ZMod 3) ∙ x) :
    ∃ r ∈ e6Weyl hα, r x = -x ∧ (∀ v, r v - v ∈ (ZMod 3) ∙ x) ∧
      (∀ E : Submodule (ZMod 3) V, E ≤ H → Nat.card E = 3 ^ 4 → x ∉ E →
        (∀ g ∈ A, ∀ v ∈ E, g v ∈ E) → ∀ v ∈ E, r v = v) ∧
      ∃ v₀ ∉ H, r v₀ = v₀ := by
  classical
  have hSH : spanH h = H :=
    span_range_eq_of_card_six hP hα hV hW hA hcardA hx hAx hH hxH hAH hfix
  have hS_card : Nat.card (spanH h) = 3 ^ 5 := by rw [hSH]; exact hH
  have hxS : x ∈ spanH h := by rw [hSH]; exact hxH
  let xS : spanH h := ⟨x, hxS⟩
  obtain ⟨B', hB', hxx2, hstab⟩ :=
    norm_two_and_stabilizer_of_card_six hP hα hW hA hcardA hx hAx hxS hS_card
  have hnorm_h0 : B' (hIn h 0) (hIn h 0) = 2 := by
    rw [hB' 0 (hIn h 0), alphaIn_self hα 0]
  have hh0 : h 0 ≠ 0 := by
    intro h0
    have hsub : (hIn h 0 : spanH h) = 0 := by
      apply Subtype.ext
      simp [hIn, h0]
    have h2 : B' (hIn h 0) (hIn h 0) = 0 := by rw [hsub, map_zero]
    rw [hnorm_h0] at h2
    exact absurd h2 (by decide)
  obtain ⟨g₀, hg₀_mem, hg₀_eq⟩ :=
    exists_mem_e6Weyl_apply_eq_of_mem_spanH hP hα hS_card hB'
      (hIn h 0).2 hxS hh0 hx (hnorm_h0.trans hxx2.symm)
  let r : V ≃ₗ[ZMod 3] V := g₀ * Module.reflection (hα 0) * g₀⁻¹
  have hr_mem : r ∈ e6Weyl hα := by
    dsimp [r]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₀_mem (Subgroup.subset_closure ⟨0, rfl⟩))
      (Subgroup.inv_mem _ hg₀_mem)
  have hg₀_inv : g₀⁻¹ x = h 0 := by
    rw [← hg₀_eq]
    exact LinearEquiv.symm_apply_apply g₀ (h 0)
  have hg₀_eq' : g₀ (h 0) = x := by
    change g₀ ↑(hIn h 0) = x
    exact hg₀_eq
  have hrx : r x = -x := by
    calc r x = g₀ (Module.reflection (hα 0) (g₀⁻¹ x)) := rfl
      _ = g₀ (Module.reflection (hα 0) (h 0)) := by rw [hg₀_inv]
      _ = g₀ (-h 0) := by rw [Module.reflection_apply_self]
      _ = -g₀ (h 0) := by rw [map_neg]
      _ = -x := by rw [hg₀_eq']
  have hrmove : ∀ v, r v - v ∈ (ZMod 3) ∙ x := by
    intro v
    have hv : g₀ (g₀⁻¹ v) = v := LinearEquiv.apply_symm_apply g₀ v
    have heq : r v - v = (- α 0 (g₀⁻¹ v)) • x := by
      calc r v - v = g₀ (Module.reflection (hα 0) (g₀⁻¹ v)) - v := rfl
        _ = g₀ (g₀⁻¹ v - α 0 (g₀⁻¹ v) • h 0) - v := by
            rw [Module.reflection_apply]
        _ = g₀ (g₀⁻¹ v) - g₀ (α 0 (g₀⁻¹ v) • h 0) - v := by rw [map_sub]
        _ = v - α 0 (g₀⁻¹ v) • g₀ (h 0) - v := by rw [map_smul, hv]
        _ = v - α 0 (g₀⁻¹ v) • x - v := by rw [hg₀_eq']
        _ = (- α 0 (g₀⁻¹ v)) • x := by
          have h1 : v - α 0 (g₀⁻¹ v) • x - v = -(α 0 (g₀⁻¹ v) • x) := by abel
          rw [h1]
          exact neg_smul _ _ |>.symm
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton x))
  have hcomp : ∀ E : Submodule (ZMod 3) V, E ≤ H → Nat.card E = 3 ^ 4 → x ∉ E →
      (∀ g ∈ A, ∀ v ∈ E, g v ∈ E) → ∀ v ∈ E, r v = v := by
    intro E hEH hEcard hxE hEA v hv
    have hES : E ≤ spanH h := by rw [hSH]; exact hEH
    have horth :=
      orthogonal_of_invariant_compl hP hα hS_card hB' hxS hx hxx2 hA hES hEcard hxE hEA hAx
        hfix v hv
    obtain ⟨g₀', hg₀'_mem, hg₀'_eq⟩ := restrict_mem_e6Weyl (hα := hα) hg₀_mem
    have hxS_eq : g₀' (hIn h 0) = xS := by
      apply Subtype.ext
      rw [hg₀'_eq]
      exact hg₀_eq
    have hα0 : α 0 (g₀⁻¹ v) = 0 := by
      have hrel : B' xS ⟨v, hES hv⟩ = α 0 (g₀⁻¹ v) := by
        calc B' xS ⟨v, hES hv⟩
            = B' (g₀' (hIn h 0)) ⟨v, hES hv⟩ := by rw [hxS_eq]
          _ = B' (hIn h 0) (g₀'⁻¹ ⟨v, hES hv⟩) := by
              have hiso := bilinForm_apply_e6Weyl (alphaIn_hIn hP) hS_card hB'
                (alphaIn_self hα) hg₀'_mem (u := hIn h 0) (v := g₀'⁻¹ ⟨v, hES hv⟩)
              simpa using hiso
          _ = alphaIn α 0 (g₀'⁻¹ ⟨v, hES hv⟩) := hB' 0 _
          _ = α 0 ((g₀'⁻¹ ⟨v, hES hv⟩ : V)) := rfl
          _ = α 0 (g₀⁻¹ v) := by
              have h : g₀' (g₀'⁻¹ ⟨v, hES hv⟩) = ⟨v, hES hv⟩ :=
                LinearEquiv.apply_symm_apply g₀' _
              have h2 : (g₀' (g₀'⁻¹ ⟨v, hES hv⟩) : V) = g₀ (g₀'⁻¹ ⟨v, hES hv⟩) :=
                hg₀'_eq _
              have h2' : v = g₀ (g₀'⁻¹ ⟨v, hES hv⟩) := by
                simpa [LinearEquiv.apply_symm_apply, Subtype.coe_mk] using h2
              have h3 : g₀⁻¹ v = g₀'⁻¹ ⟨v, hES hv⟩ := by
                apply g₀.injective
                simpa using h2'
              rw [← h3]
      rw [hrel] at horth
      exact horth
    have hfixrefl : Module.reflection (hα 0) (g₀⁻¹ v) = g₀⁻¹ v := by
      rw [Module.reflection_apply, hα0, zero_smul, sub_zero]
    calc r v = g₀ (Module.reflection (hα 0) (g₀⁻¹ v)) := rfl
      _ = g₀ (g₀⁻¹ v) := by rw [hfixrefl]
      _ = v := LinearEquiv.apply_symm_apply g₀ v
  have hfixed : ∃ v₀ ∉ H, r v₀ = v₀ := by
    have hα0_ne : α 0 ≠ 0 := by
      intro h0
      have h2 : α 0 (h 0) = 0 := by rw [h0]; rfl
      rw [hα 0] at h2
      exact absurd h2 (by decide)
    have hfin_ker : finrank (ZMod 3) (LinearMap.ker (α 0)) = 5 := by
      have h := Module.Dual.finrank_ker_add_one_of_ne_zero (f := α 0) hα0_ne
      have hV6 := finrank_eq_six hV
      omega
    let K : Submodule (ZMod 3) V := (LinearMap.ker (α 0)).map g₀.toLinearMap
    have hK_fin : finrank (ZMod 3) K = 5 := by
      have h := LinearEquiv.finrank_map_eq g₀ (LinearMap.ker (α 0))
      simpa [K] using h.trans hfin_ker
    have hxK : x ∉ K := by
      intro hxK
      obtain ⟨w, hw_ker, hw_eq⟩ := Submodule.mem_map.mp hxK
      have hw : w = h 0 := g₀.injective (hw_eq.trans hg₀_eq.symm)
      rw [hw] at hw_ker
      have hα0 : α 0 (h 0) = 0 := LinearMap.mem_ker.mp hw_ker
      rw [hα 0] at hα0
      exact absurd hα0 (by decide)
    have hK_ne_H : K ≠ H := by
      intro heq
      rw [heq] at hxK
      exact hxK hxH
    have hH_fin : finrank (ZMod 3) H = 5 := by
      have hc := natCard_submodule H
      rw [hH] at hc
      exact (Nat.pow_right_injective (by norm_num) hc).symm
    have hK_not_le : ¬ K ≤ H := by
      intro hle
      have heq : K = H := Submodule.eq_of_le_of_finrank_eq hle (by rw [hK_fin, hH_fin])
      exact hK_ne_H heq
    have hv₀_exists : ∃ v₀ ∈ K, v₀ ∉ H := by
      by_contra h
      push Not at h
      exact hK_not_le h
    obtain ⟨v₀, hv₀K, hv₀H⟩ := hv₀_exists
    have hrfix : r v₀ = v₀ := by
      have hv₀_ker : g₀⁻¹ v₀ ∈ LinearMap.ker (α 0) := by
        obtain ⟨w, hw_ker, hw_eq⟩ := Submodule.mem_map.mp hv₀K
        have hw : g₀⁻¹ v₀ = w := by
          rw [← hw_eq]
          exact LinearEquiv.symm_apply_apply g₀ w
        rw [hw]
        exact hw_ker
      have hα0 : α 0 (g₀⁻¹ v₀) = 0 := LinearMap.mem_ker.mp hv₀_ker
      calc r v₀ = g₀ (Module.reflection (hα 0) (g₀⁻¹ v₀)) := rfl
        _ = g₀ (g₀⁻¹ v₀) := by rw [Module.reflection_apply, hα0, zero_smul, sub_zero]
        _ = v₀ := LinearEquiv.apply_symm_apply g₀ v₀
    exact ⟨v₀, hv₀H, hrfix⟩
  exact ⟨r, hr_mem, hrx, hrmove, hcomp, hfixed⟩

theorem exists_mem_e6Weyl_apply_eq_of_card_six
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hα : ∀ i, α i (h i) = 2) (hV : Nat.card V = 3 ^ 6)
    (hW : Nat.card (e6Weyl hα) = 51840) {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hA : A ≤ e6Weyl hα)
    (hcardA : 720 ≤ Nat.card A) {x : V} (hx : x ≠ 0) (hAx : ∀ g ∈ A, g x = x)
    {H : Submodule (ZMod 3) V} (hH : Nat.card H = 3 ^ 5) (hxH : x ∈ H)
    (hAH : ∀ g ∈ A, ∀ v, g v - v ∈ H)
    (hfix : ∀ v, (∀ g ∈ A, g v - v ∈ (ZMod 3) ∙ x) → v ∈ (ZMod 3) ∙ x)
    {a : V} (ha : a ≠ 0) (haH : a ∈ H) {ψ : V ≃ₗ[ZMod 3] V} (hψ : ψ ∈ A) (hψa : ψ a = -a)
    (hψu : ∀ u, ∃ c : ZMod 3, ψ u - u = c • a) :
    ∃ g ∈ e6Weyl hα, g x = a := by
  classical
  have hSH : spanH h = H :=
    span_range_eq_of_card_six hP hα hV hW hA hcardA hx hAx hH hxH hAH hfix
  have hS_card : Nat.card (spanH h) = 3 ^ 5 := by rw [hSH]; exact hH
  have hxS : x ∈ spanH h := by rw [hSH]; exact hxH
  have haS : a ∈ spanH h := by rw [hSH]; exact haH
  obtain ⟨B', hB', hxx2, -⟩ :=
    norm_two_and_stabilizer_of_card_six hP hα hW hA hcardA hx hAx hxS hS_card
  obtain ⟨ψ', hψ', hψ'eq⟩ := restrict_mem_e6Weyl (hα := hα) (hA hψ)
  have haS0 : (⟨a, haS⟩ : spanH h) ≠ 0 := by
    intro h0
    exact ha (by simpa using congrArg Subtype.val h0)
  have hψ'a : ψ' ⟨a, haS⟩ = -⟨a, haS⟩ := by
    apply Subtype.ext
    change (ψ' ⟨a, haS⟩ : V) = -a
    rw [hψ'eq]
    exact hψa
  have hψ'u : ∀ u : spanH h, ∃ c : ZMod 3, ψ' u - u = c • (⟨a, haS⟩ : spanH h) := by
    intro u
    obtain ⟨c, hc⟩ := hψu (u : V)
    refine ⟨c, ?_⟩
    apply Subtype.ext
    change (ψ' u : V) - (u : V) = c • a
    rw [hψ'eq u, hc]
  have haa2 : B' ⟨a, haS⟩ ⟨a, haS⟩ = 2 :=
    bilinForm_self_eq_two_of_neg (hP := alphaIn_hIn hP) (hV := hS_card) (hB := hB')
      (hα := alphaIn_self hα) hψ' haS0 hψ'a hψ'u
  obtain ⟨g, hg, hga⟩ :=
    exists_mem_e6Weyl_apply_eq_of_mem_spanH hP hα hS_card hB' haS hxS ha hx
      (haa2.trans hxx2.symm)
  refine ⟨g⁻¹, Subgroup.inv_mem _ hg, ?_⟩
  rw [← hga]
  exact LinearEquiv.symm_apply_apply g a

end CFSG.StandardType.E6QTwo

end
