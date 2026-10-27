module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUReduceVIrr
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.RankThree.PartOne.ReflF

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SUReduceVAux_equiv_ones {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (σ : Equiv.Perm (Fin m)) : (b.equiv b σ) (SUOnes 3 b) = SUOnes 3 b := by
  rw [SUOnes, map_sum]
  simp_rw [Module.Basis.equiv_apply]
  exact Equiv.sum_comp σ (fun i => b i)

theorem hdRo7SUReduceVAux_sum_coord_fun {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (σ : Equiv.Perm (Fin m)) (v : V) :
    (∑ i, b.coord i) ((b.equiv b σ) v) = (∑ i, b.coord i) v := by
  have hfun : (∑ i, b.coord i).comp ((b.equiv b σ).toLinearMap) = ∑ i, b.coord i := by
    apply b.ext
    intro k
    rw [LinearMap.comp_apply]
    simp only [LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      hdRo7SUReduceVAux_sum_coord_basis]
  exact congrArg (fun L : V →ₗ[ZMod 3] ZMod 3 => L v) hfun

theorem hdRo7SUReduceVAux_sum_coord_equiv {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (σ : Equiv.Perm (Fin m)) (v : V) :
    (∑ i, b.coord i ((b.equiv b σ) v)) = ∑ i, b.coord i v := by
  rw [← LinearMap.sum_apply, ← LinearMap.sum_apply]
  exact hdRo7SUReduceVAux_sum_coord_fun b σ v

theorem hdRo7SUReduceVAux_singleton_contra {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (H A : Subgroup (V ≃ₗ[ZMod 3] V)) (hD : SULinData 3 m V b H A)
    {S : Set (V ≃ₗ[ZMod 3] V)} {s0 : V ≃ₗ[ZMod 3] V}
    (hHcl : H = Subgroup.closure S) (hSsing : S = {s0})
    (hs0sq : s0 * s0 = 1) (hs0nsuperm : ¬ SUPerm 3 b s0) : False := by
  have hm7 : 7 ≤ m := hD.hm
  haveI : NeZero m := ⟨by omega⟩
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  let τ : V ≃ₗ[ZMod 3] V := b.equiv b (Equiv.swap i j)
  have hτsup : SUPerm 3 b τ := ⟨Equiv.swap i j, fun k => by rw [Module.Basis.equiv_apply]⟩
  have hτH : τ ∈ H := hD.hPH τ hτsup
  have hτclos : τ ∈ Subgroup.closure ({s0} : Set (V ≃ₗ[ZMod 3] V)) := by
    rw [← hSsing, ← hHcl]; exact hτH
  have hτcases : τ = 1 ∨ τ = s0 := by
    refine Subgroup.closure_induction (p := fun x _ => x = 1 ∨ x = s0) ?_ ?_ ?_ ?_ hτclos
    · intro x hx
      rw [Set.mem_singleton_iff] at hx; subst hx; exact Or.inr rfl
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · left; rw [one_mul]
      · right; rw [one_mul]
      · right; rw [mul_one]
      · left; exact hs0sq
    · intro x _ hx
      rcases hx with rfl | rfl
      · left; rw [inv_one]
      · right; rw [inv_eq_of_mul_eq_one_right hs0sq]
  have hτne1 : τ ≠ 1 := by
    intro h
    have h1 := congrArg (fun e : V ≃ₗ[ZMod 3] V => e (b i)) h
    simp only [τ, Module.Basis.equiv_apply, Equiv.swap_apply_left, LinearEquiv.one_eq_refl,
      LinearEquiv.refl_apply] at h1
    exact hij (b.injective h1).symm
  rcases hτcases with h | h
  · exact hτne1 h
  · exact hs0nsuperm (h ▸ hτsup)

theorem hdRo7SUReduceVAux_not_preserves_ones {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (H A : Subgroup (V ≃ₗ[ZMod 3] V)) (hD : SULinData 3 m V b H A)
    (hN : SUNormalizerLeaf)
    (hU : ¬ (∀ a ∈ H, ∀ w ∈ SUAug 3 b, a w ∈ SUAug 3 b)) :
    ¬ (∀ a ∈ H, a (SUOnes 3 b) ∈ Submodule.span (ZMod 3) {SUOnes 3 b}) := by
  intro hHx
  have hm7 : 7 ≤ m := hD.hm
  haveI : NeZero m := ⟨by omega⟩
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_basis b
  obtain ⟨S, hS, hHcl, hSconn⟩ := hD.hgen
  have hsA : ∀ i j, i ≠ j → b.equiv b (Equiv.swap i j) ∈ A := by
    intro i j hij
    exact hD.hHA (hD.hPH _ ⟨Equiv.swap i j, fun k => by rw [Module.Basis.equiv_apply]⟩)
  have hgen : ∀ s ∈ S, SUPerm 3 b s ∨
      (∀ v, s v = v - ((2 / (m : ZMod 3)) * (∑ i, b.coord i v)) • SUOnes 3 b) := by
    intro s hs
    have hsH : s ∈ H := (hS s hs).1
    have hsrefl : GGLinRefl (p := 3) s := (hS s hs).2
    have hsA' : s ∈ A := hD.hHA hsH
    obtain ⟨u, φ, hrd⟩ := hdRo7SUReduceVAux_reflData s hsrefl
    by_cases huconst : ∀ i j, b.coord i u = b.coord j u
    · right
      have hφconst : ∀ i j, φ (b i) = φ (b j) :=
        hdRo7SUReduceVAux_phi_const_of_root_const b hD.hNoT hsA hrd hsA' huconst
      intro v
      exact hdRo7SUReduceVAux_const_refl_action b hD.h3 hrd huconst hφconst v
    · left
      have hφx : φ (SUOnes 3 b) = 0 := by
        by_contra hφ
        apply huconst
        have hu : u = (φ (SUOnes 3 b))⁻¹ • (SUOnes 3 b - s (SUOnes 3 b)) := by
          conv_rhs => rw [hrd.apply (SUOnes 3 b)]
          rw [show SUOnes 3 b - (SUOnes 3 b - φ (SUOnes 3 b) • u) =
            φ (SUOnes 3 b) • u by abel, smul_smul, inv_mul_cancel₀ hφ, one_smul]
        have hxs : s (SUOnes 3 b) ∈ Submodule.span (ZMod 3) {SUOnes 3 b} := hHx s hsH
        have humem : u ∈ Submodule.span (ZMod 3) {SUOnes 3 b} := by
          rw [hu]
          exact Submodule.smul_mem _ _ (Submodule.sub_mem _
            (Submodule.subset_span (Set.mem_singleton _)) hxs)
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp humem
        intro i j
        rw [← hc, map_smul, map_smul, hdRo7SUReduceVAux_coord_ones,
          hdRo7SUReduceVAux_coord_ones]
      have hsx : s (SUOnes 3 b) = SUOnes 3 b := by
        rw [hrd.apply (SUOnes 3 b), hφx, zero_smul, sub_zero]
      have hnorm : ∀ t, SUPerm 3 b t → SUPerm 3 b (s * t * s⁻¹) := hD.hStab s hsA' hsx
      rcases hN 3 rfl m hD.hm hD.h3 V b s hnorm hsx with
        hsuper | ⟨σ, hσ⟩
      · exact hsuper
      · exfalso; exact hdRo7SUReduceVAux_second_form_not_refl b (by omega) hD.h3 hσ hsrefl
  by_cases hS0 : ∃ s ∈ S, ¬ SUPerm 3 b s
  · obtain ⟨s0, hs0S, hs0nsuperm⟩ := hS0
    have hs0act : ∀ v, s0 v =
        v - ((2 / (m : ZMod 3)) * (∑ i, b.coord i v)) • SUOnes 3 b :=
      (hgen s0 hs0S).resolve_left hs0nsuperm
    have hcomm : ∀ t ∈ S, Commute s0 t := by
      intro t htS
      rcases hgen t htS with ht | ht
      · obtain ⟨σ, hσ⟩ := ht
        have heqt : t = b.equiv b σ := by
          have hlin : (t : V →ₗ[ZMod 3] V) = (b.equiv b σ : V →ₗ[ZMod 3] V) := by
            apply b.ext
            intro k
            change t (b k) = (b.equiv b σ) (b k)
            rw [hσ k, Module.Basis.equiv_apply]
          exact LinearEquiv.toLinearMap_injective hlin
        rw [heqt]
        ext v
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        have h1 : s0 ((b.equiv b σ) v) = (b.equiv b σ) v -
            ((2 / (m : ZMod 3)) * (∑ i, b.coord i v)) • SUOnes 3 b := by
          rw [hs0act ((b.equiv b σ) v), hdRo7SUReduceVAux_sum_coord_equiv]
        have h2 : (b.equiv b σ) (s0 v) = (b.equiv b σ) v -
            ((2 / (m : ZMod 3)) * (∑ i, b.coord i v)) • SUOnes 3 b := by
          rw [hs0act v, map_sub, map_smul, hdRo7SUReduceVAux_equiv_ones]
        rw [h1, h2]
      · have heq : t = s0 := by
          ext v; rw [ht v, hs0act v]
        rw [heq]
    have hSsing : S = {s0} := by
      ext t; constructor
      · intro ht
        have := hdRo7SUReduceVAux_reflTransGen_eq_of_no_edge
          (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v)
          (fun b hb => hb.2.2 (hcomm b hb.2.1)) (hSconn s0 hs0S t ht)
        rw [Set.mem_singleton_iff]; exact this
      · intro ht; rw [Set.mem_singleton_iff] at ht; subst ht; exact hs0S
    exact hdRo7SUReduceVAux_singleton_contra b H A hD hHcl hSsing (hS s0 hs0S).2.1 hs0nsuperm
  · push Not at hS0
    apply hU
    have hLe : S ⊆ hdRo7SUReduceVAux_augStab b := fun s hs =>
      (hdRo7SUReduceVAux_move_le_iff b s).mp (hdRo7SUReduceVAux_superm_move_le b (hS0 s hs))
    have hHaug : H ≤ hdRo7SUReduceVAux_augStab b := by
      rw [hHcl]; exact (Subgroup.closure_le _).mpr hLe
    intro a ha w hw
    have hav : a w - w ∈ SUAug 3 b := hHaug ha w
    have : a w = w + (a w - w) := by abel
    rw [this]
    exact Submodule.add_mem _ hw hav

theorem hdRo7SUReduceVAux_absIrred {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V)
    (H A : Subgroup (V ≃ₗ[ZMod 3] V)) (hP1 : SUPInvLeaf) (hP2 : SUPCentLeaf)
    (hN : SUNormalizerLeaf) (hD : SULinData 3 m V b H A)
    (hV : ∃ r ∈ H, GGLinRefl (p := 3) r ∧ ¬ ggLinMove (p := 3) r ≤ SUAug 3 b) :
    ZS.AbsIrred 3 H := by
  have hm7 : 7 ≤ m := hD.hm
  haveI : NeZero m := ⟨by omega⟩
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_basis b
  have hU := hdRo7SUReduceVAux_not_preserves_aug b H A hD hV
  have hx := hdRo7SUReduceVAux_not_preserves_ones b H A hD hN hU
  have hIrr : ∀ W : Submodule (ZMod 3) V, (∀ a ∈ H, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hPinv : ∀ a, SUPerm 3 b a → ∀ w ∈ W, a w ∈ W :=
      fun a ha w hw => hW a (hD.hPH a ha) w hw
    rcases hP1 3 rfl m hD.hm hD.h3 V b W hPinv with hbot | hones | haug | htop
    · exact Or.inl hbot
    · exfalso
      apply hx
      intro a ha
      have hxW : SUOnes 3 b ∈ W := by
        rw [hones]; exact Submodule.subset_span (Set.mem_singleton _)
      have := hW a ha (SUOnes 3 b) hxW
      rwa [hones] at this
    · exfalso
      apply hU
      intro a ha w hw
      rw [← haug] at hw ⊢
      exact hW a ha w hw
    · exact Or.inr htop
  refine ⟨hIrr, ?_⟩
  intro T hT
  have hTP : ∀ a, SUPerm 3 b a → T ∘ₗ (a : V →ₗ[ZMod 3] V) = (a : V →ₗ[ZMod 3] V) ∘ₗ T :=
    fun a ha => hT a (hD.hPH a ha)
  obtain ⟨α, β, hαβ⟩ := hP2 3 rfl m hD.hm hD.h3 V b T hTP
  by_cases hβ : β = 0
  · refine ⟨α, ?_⟩
    ext v
    rw [hαβ v, hβ, zero_mul, zero_smul, add_zero, LinearMap.smul_apply,
      LinearMap.id_apply]
  · exfalso
    let W : Submodule (ZMod 3) V := LinearMap.ker (T - α • LinearMap.id)
    have hUle : SUAug 3 b ≤ W := by
      intro w hw
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      have hwsum : (∑ i, b.repr w i) = 0 := by
        have h1 : (∑ i, b.coord i) w = 0 := by
          have := hw; rwa [SUAug, LinearMap.mem_ker] at this
        rw [LinearMap.sum_apply] at h1
        simpa only [Module.Basis.coord_apply] using h1
      rw [hαβ w, hwsum, mul_zero, zero_smul, add_zero, sub_self]
    have hWstab : ∀ a ∈ H, ∀ w ∈ W, a w ∈ W := by
      intro a ha w hw
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hw ⊢
      have hcommv : T (a w) = a (T w) :=
        congrArg (fun L : V →ₗ[ZMod 3] V => L w) (hT a ha)
      rw [hcommv, ← map_smul, ← map_sub, hw, map_zero]
    let i0 : Fin m := ⟨0, by omega⟩
    let i1 : Fin m := ⟨1, by omega⟩
    have hi01 : i0 ≠ i1 := by
      intro h; have := congrArg Fin.val h; simp [i0, i1] at this
    have hUne : SUAug 3 b ≠ ⊥ := by
      intro h
      have hmem : b i0 - b i1 ∈ SUAug 3 b := hdRo7SUReduceVAux_diff_mem_aug b i0 i1
      rw [h, Submodule.mem_bot] at hmem
      exact hi01 (b.injective (sub_eq_zero.mp hmem))
    have hxW : SUOnes 3 b ∉ W := by
      intro hxmem
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hxmem
      have hsumx : (∑ i, b.repr (SUOnes 3 b) i) = (m : ZMod 3) := by
        have hconst : ∀ i ∈ (Finset.univ : Finset (Fin m)), b.repr (SUOnes 3 b) i = 1 := by
          intro i _; rw [← Module.Basis.coord_apply, hdRo7SUReduceVAux_coord_ones]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one]
      have hTx := hαβ (SUOnes 3 b)
      rw [hsumx] at hTx
      rw [hTx] at hxmem
      have hzero : (β * (m : ZMod 3)) • SUOnes 3 b = 0 := by
        rw [← hxmem]; module
      have hm_ne : (m : ZMod 3) ≠ 0 := by
        intro h; exact hD.h3 ((CharP.cast_eq_zero_iff (ZMod 3) 3 m).mp h)
      rcases smul_eq_zero.mp hzero with hbm | hzero'
      · rcases mul_eq_zero.mp hbm with hb | hm
        · exact hβ hb
        · exact hm_ne hm
      · have h1 := hdRo7SUReduceVAux_coord_ones b i0
        rw [hzero'] at h1
        have h0 : b.coord i0 (0 : V) = 0 := map_zero _
        rw [h0] at h1
        exact (zero_ne_one : (0 : ZMod 3) ≠ 1) h1
    rcases hIrr W hWstab with hbot | htop
    · exact hUne (le_bot_iff.mp (hUle.trans (le_of_eq hbot)))
    · exact hxW (htop ▸ Submodule.mem_top)

end CFSG.StandardType.HdRo7SU
