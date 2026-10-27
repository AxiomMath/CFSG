module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri

open Subgroup
theorem braid_of_disjoint_range {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {a b : Module.End (ZMod 2) W} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b * a = b * a * b)
    (hdisj : ∀ w : W, (∃ x, (a - 1) x = w) → (∃ y, (b - 1) y = w) → w = 0) :
    (a - 1) * (b - 1) * (a - 1) = a - 1 := by
  set A : Module.End (ZMod 2) W := a - 1 with hA
  set B : Module.End (ZMod 2) W := b - 1 with hB
  have hA' : A = a + 1 := by rw [hA, ZModModule.sub_eq_add]
  have hB' : B = b + 1 := by rw [hB, ZModModule.sub_eq_add]
  have hadd_cancel : ∀ x y : Module.End (ZMod 2) W, x + (x + y) = y := by
    intro x y; rw [← add_assoc, ZModModule.add_self, zero_add]
  have h_expand : (a + 1) * (b + 1) * (a + 1) = a * b * a + a * b + b * a + b := by
    have h1 : (a + 1) * (b + 1) = a * b + a + b + 1 := by
      simp only [mul_add, add_mul, one_mul, mul_one]
      ac_rfl
    rw [h1]
    simp only [add_mul, mul_add, one_mul, mul_one, ha]
    simp only [add_assoc, add_comm, add_left_comm, ZModModule.add_self, add_zero, zero_add]
    rw [hadd_cancel]
  have hAB : A * B * A + A = B * (a * b + a + 1) := by
    rw [hA', hB']
    rw [h_expand, hab]
    simp only [mul_add, add_mul, one_mul, mul_one]
    simp only [add_assoc, add_comm, add_left_comm, ZModModule.add_self, add_zero, zero_add]
    rw [← mul_assoc]
  have hkey : ∀ u : W, A (B (A u)) = A u := by
    intro u
    have hwA : ∃ x, (a - 1) x = A (B (A u)) + A u := by
      refine ⟨B (A u) + u, ?_⟩
      rw [← hA, map_add]
    have hwB : ∃ y, (b - 1) y = A (B (A u)) + A u := by
      refine ⟨(a * b + a + 1) u, ?_⟩
      rw [← hB]
      have h := congrArg (fun f : Module.End (ZMod 2) W => f u) hAB
      simp only [LinearMap.add_apply, Module.End.mul_apply] at h
      exact h.symm
    have hw0 : A (B (A u)) + A u = 0 := hdisj _ hwA hwB
    have hneg : A (B (A u)) = -(A u) := eq_neg_of_add_eq_zero_left hw0
    simpa only [ZModModule.neg_eq_self] using hneg
  ext u
  simp only [Module.End.mul_apply]
  exact hkey u

private theorem exists_equivariant_family {X : Type} [Group X] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : X →* Module.End (ZMod 2) W) (s : X)
    (hcent : ∀ r : X, IsConj s r → Subgroup.centralizer ({r} : Set X) =
      Subgroup.closure ({x : X | IsConj s x} ∩ (Subgroup.centralizer ({r} : Set X) : Set X)))
    (hcomm : ∀ a b : X, IsConj s a → IsConj s b → a * b = b * a →
      (ρ a - 1) * (ρ b - 1) = 0)
    (hne : ρ s ≠ 1) :
    ∃ w : X → W, (∀ d : X, IsConj s d → w d ≠ 0 ∧ ∃ u, (ρ d - 1) u = w d) ∧
      ∀ (x d : X), IsConj s d → w (x * d * x⁻¹) = ρ x (w d) := by
  classical
  have hne' : ρ s - 1 ≠ 0 := by
    intro h
    apply hne
    ext x
    have := congrArg (fun f : Module.End (ZMod 2) W => f x) h
    have h' : (ρ s) x - x = 0 := by
      simpa only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply] using this
    exact sub_eq_zero.mp h'
  obtain ⟨u, hu⟩ : ∃ u, (ρ s - 1) u ≠ 0 := by
    by_contra h
    apply hne'
    ext x
    exact not_not.mp (not_exists.mp h x)
  let w₀ : W := (ρ s - 1) u
  have hw₀ : w₀ ≠ 0 := hu
  have hw₀_eq : w₀ = ρ s u - u := by
    change (ρ s - 1) u = ρ s u - u
    rw [LinearMap.sub_apply, Module.End.one_apply]
  let St : Subgroup X :=
    { carrier := {g : X | ρ g w₀ = w₀}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change ρ a w₀ = w₀ at ha
        change ρ b w₀ = w₀ at hb
        change ρ (a * b) w₀ = w₀
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        change ρ a w₀ = w₀ at ha
        change ρ a⁻¹ w₀ = w₀
        have h1 : ρ a⁻¹ (ρ a w₀) = w₀ := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha] at h1 }
  have hsubset : ({x : X | IsConj s x} ∩ (Subgroup.centralizer ({s} : Set X) : Set X)) ⊆ St := by
    rintro e ⟨heD, heC⟩
    change IsConj s e at heD
    have hse : s * e = e * s := (Subgroup.mem_centralizer_iff.mp heC) s (Set.mem_singleton s)
    have hzero : (ρ e - 1) * (ρ s - 1) = 0 := hcomm e s heD (IsConj.refl s) hse.symm
    have h1 : (ρ e - 1) w₀ = 0 := by
      have := congrArg (fun f : Module.End (ZMod 2) W => f u) hzero
      simp only [Module.End.mul_apply, LinearMap.zero_apply] at this
      exact this
    change ρ e w₀ = w₀
    have h2 : ρ e w₀ - w₀ = 0 := by
      simpa only [LinearMap.sub_apply, Module.End.one_apply] using h1
    exact sub_eq_zero.mp h2
  have hCs_le : Subgroup.centralizer ({s} : Set X) ≤ St := by
    rw [hcent s (IsConj.refl s), Subgroup.closure_le]
    exact hsubset
  have w_eq_of_conj : ∀ {g h : X}, g * s * g⁻¹ = h * s * h⁻¹ → ρ g w₀ = ρ h w₀ := by
    intro g h hgh
    have hk_conj : (h⁻¹ * g) * s * (h⁻¹ * g)⁻¹ = s := by
      rw [mul_inv_rev, inv_inv]
      calc (h⁻¹ * g) * s * (g⁻¹ * h)
          = h⁻¹ * (g * s * g⁻¹) * h := by simp only [mul_assoc]
        _ = h⁻¹ * (h * s * h⁻¹) * h := by rw [hgh]
        _ = s := by simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    have hsk : s * (h⁻¹ * g) = (h⁻¹ * g) * s := by
      calc s * (h⁻¹ * g) = ((h⁻¹ * g) * s * (h⁻¹ * g)⁻¹) * (h⁻¹ * g) := by rw [hk_conj]
        _ = (h⁻¹ * g) * s := by simp only [mul_assoc, inv_mul_cancel, mul_one]
    have hk : h⁻¹ * g ∈ Subgroup.centralizer ({s} : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact hsk
    have hfix : ρ (h⁻¹ * g) w₀ = w₀ := hCs_le hk
    have h1 : ρ h⁻¹ (ρ g w₀) = w₀ := by
      rw [← Module.End.mul_apply, ← map_mul]
      exact hfix
    have h2 := congrArg (ρ h) h1
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, map_one,
      Module.End.one_apply] using h2
  let w : X → W :=
    fun d => if h : IsConj s d then ρ (Classical.choose (isConj_iff.mp h)) w₀ else 0
  have w_of_conj : ∀ {g d : X}, g * s * g⁻¹ = d → w d = ρ g w₀ := by
    intro g d hgd
    have hd : IsConj s d := isConj_iff.mpr ⟨g, hgd⟩
    have hc := Classical.choose_spec (isConj_iff.mp hd)
    dsimp only [w]
    rw [dif_pos hd]
    exact w_eq_of_conj (hc.trans hgd.symm)
  refine ⟨w, ?_, ?_⟩
  · intro d hd
    obtain ⟨g, hg⟩ := isConj_iff.mp hd
    constructor
    · rw [w_of_conj hg]
      intro h0
      apply hw₀
      have hinj : Function.Injective (ρ g) := by
        intro x y hxy
        have h3 := congrArg (ρ g⁻¹) hxy
        simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply] using h3
      exact hinj (by simpa using h0)
    · refine ⟨ρ g u, ?_⟩
      rw [w_of_conj hg]
      rw [LinearMap.sub_apply, Module.End.one_apply]
      rw [← Module.End.mul_apply, ← map_mul]
      have hdg : d * g = g * s := by
        rw [← hg]
        simp only [mul_assoc, inv_mul_cancel, mul_one]
      rw [hdg, map_mul, Module.End.mul_apply, ← map_sub, hw₀_eq]
  · intro x d hd
    obtain ⟨g, hg⟩ := isConj_iff.mp hd
    have hw_d : w d = ρ g w₀ := w_of_conj hg
    have hxdx : (x * g) * s * (x * g)⁻¹ = x * d * x⁻¹ := by
      rw [mul_inv_rev]
      calc (x * g) * s * (g⁻¹ * x⁻¹)
          = x * (g * s * g⁻¹) * x⁻¹ := by simp only [mul_assoc]
        _ = x * d * x⁻¹ := by rw [hg]
    rw [w_of_conj hxdx, hw_d, map_mul, Module.End.mul_apply]

private theorem apply_family_of_orderOf_eq_three {X : Type} [Group X] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : X →* Module.End (ZMod 2) W) (s : X) (hs2 : s ^ 2 = 1)
    (w : X → W) (hw : ∀ d : X, IsConj s d → ∃ u, (ρ d - 1) u = w d)
    (hequiv : ∀ (x d : X), IsConj s d → w (x * d * x⁻¹) = ρ x (w d))
    (hcomm : ∀ a b : X, IsConj s a → IsConj s b → a * b = b * a →
      (ρ a - 1) * (ρ b - 1) = 0)
    (hbraid : ∀ a b : X, IsConj s a → IsConj s b → orderOf (a * b) = 3 →
      (ρ a - 1) * (ρ b - 1) * (ρ a - 1) = ρ a - 1)
    {a b : X} (ha : IsConj s a) (hb : IsConj s b) (hab : orderOf (a * b) = 3) :
    (ρ b - 1) (w a) = w b ∧ w a + w b + w (b * a * b⁻¹) = 0 := by
  have hadd_cancel : ∀ x y : W, x + (x + y) = y := by
    intro x y; rw [← add_assoc, ZModModule.add_self, zero_add]
  have ha2 : a * a = 1 := by
    have h := ha.pow 2
    rw [hs2] at h
    rw [pow_two] at h
    exact isConj_one_right.mp h
  have hb2 : b * b = 1 := by
    have h := hb.pow 2
    rw [hs2] at h
    rw [pow_two] at h
    exact isConj_one_right.mp h
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hab3 : (a * b) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (a * b)
    rwa [hab] at this
  have h3 : a * b * a * b * a * b = 1 := by
    have h : (a * b) * (a * b) * (a * b) = 1 := by
      rw [← pow_two, ← pow_succ]
      exact hab3
    simpa only [mul_assoc] using h
  have h4 : a * b * a * b * a = b := by
    have h := h3
    rw [← hb2] at h
    exact mul_right_cancel h
  have hconj : (a * b) * a * (a * b)⁻¹ = b := by
    rw [mul_inv_rev, hbinv, hainv]
    simpa only [mul_assoc] using h4
  have hwb : w b = ρ a (ρ b (w a)) := by
    have h := hequiv (a * b) a ha
    rw [hconj] at h
    rw [map_mul, Module.End.mul_apply] at h
    exact h
  obtain ⟨u, hu⟩ := hw a ha
  have hAwa : (ρ a - 1) (w a) = 0 := by
    rw [← hu]
    rw [← Module.End.mul_apply]
    rw [hcomm a a ha ha rfl, LinearMap.zero_apply]
  have hABA : (ρ a - 1) ((ρ b - 1) (w a)) = w a := by
    rw [← hu]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hbraid a b ha hb hab]
  have hX : ρ b (w a) = w a + (ρ b - 1) (w a) := by
    calc ρ b (w a) = (1 + (ρ b - 1)) (w a) := by rw [add_sub_cancel]
      _ = w a + (ρ b - 1) (w a) := by rw [LinearMap.add_apply, Module.End.one_apply]
  have hAX : (ρ a - 1) (w a + (ρ b - 1) (w a)) = w a := by
    rw [map_add, hAwa, hABA, zero_add]
  have hwb' : (ρ b - 1) (w a) = w b := by
    rw [hwb]
    rw [show ρ a = 1 + (ρ a - 1) from (add_sub_cancel 1 (ρ a)).symm]
    rw [LinearMap.add_apply, Module.End.one_apply, hX, hAX, add_assoc,
      add_comm ((ρ b - 1) (w a)) (w a)]
    exact (hadd_cancel (w a) ((ρ b - 1) (w a))).symm
  have hwbab : w (b * a * b⁻¹) = w a + w b := by
    rw [hequiv b a ha, hX, hwb']
  exact ⟨hwb', by rw [hwbab, ZModModule.add_self]⟩


private lemma triaRep_orderOf_mul_comm {G : Type} [Group G] (x y : G) :
    orderOf (x * y) = orderOf (y * x) := by
  have h : y * x = y * (x * y) * y⁻¹ := by
    rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  rw [h, ← MulAut.conj_apply]
  exact (MulEquiv.orderOf_eq (MulAut.conj y) (x * y)).symm

theorem triality_rep_trivial {X : Type} [Group X] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : X →* Module.End (ZMod 2) W) (s : X) (hs2 : s ^ 2 = 1)
    (hgen : Subgroup.normalClosure ({s} : Set X) = ⊤)
    (hcent : ∀ r : X, IsConj s r → Subgroup.centralizer ({r} : Set X) =
      Subgroup.closure ({x : X | IsConj s x} ∩ (Subgroup.centralizer ({r} : Set X) : Set X)))
    (hline : ∃ a b t : X, IsConj s a ∧ IsConj s b ∧ IsConj s t ∧ orderOf (a * b) = 3 ∧
      orderOf (t * a) = 3 ∧ orderOf (t * b) = 3 ∧ orderOf (t * (b * a * b⁻¹)) = 3)
    (hcomm : ∀ a b : X, IsConj s a → IsConj s b → a * b = b * a →
      (ρ a - 1) * (ρ b - 1) = 0)
    (hbraid : ∀ a b : X, IsConj s a → IsConj s b → orderOf (a * b) = 3 →
      (ρ a - 1) * (ρ b - 1) * (ρ a - 1) = ρ a - 1) :
    ∀ x : X, ρ x = 1 := by
  suffices hρs : ρ s = 1 by
    intro x
    have hle : Subgroup.normalClosure ({s} : Set X) ≤ MonoidHom.ker ρ :=
      Subgroup.normalClosure_le_normal (by rintro y rfl; exact hρs)
    exact hle (by rw [hgen]; trivial)
  by_contra hne
  obtain ⟨w, hw, hequiv⟩ := exists_equivariant_family ρ s hcent hcomm hne
  obtain ⟨a, b, t, ha, hb, ht, hab3, hta3, htb3, htf3⟩ := hline
  set f : X := b * a * b⁻¹ with hf
  have htf3' : orderOf (t * f) = 3 := by rw [hf]; exact htf3
  have hf_conj : IsConj s f := by
    obtain ⟨c, hc⟩ := isConj_iff.mp ha
    rw [hf]
    refine isConj_iff.mpr ⟨b * c, ?_⟩
    calc (b * c) * s * (b * c)⁻¹ = b * (c * s * c⁻¹) * b⁻¹ := by
          rw [mul_inv_rev]; simp only [mul_assoc]
      _ = b * a * b⁻¹ := by rw [hc]
  have hwrange : ∀ d : X, IsConj s d → ∃ u, (ρ d - 1) u = w d :=
    fun d hd => (hw d hd).2
  obtain ⟨_, hab_sum⟩ :=
    apply_family_of_orderOf_eq_three ρ s hs2 w hwrange hequiv hcomm hbraid ha hb hab3
  have hat3 : orderOf (a * t) = 3 := by rw [triaRep_orderOf_mul_comm, hta3]
  obtain ⟨hat_eq, _⟩ :=
    apply_family_of_orderOf_eq_three ρ s hs2 w hwrange hequiv hcomm hbraid ha ht hat3
  have hbt3 : orderOf (b * t) = 3 := by rw [triaRep_orderOf_mul_comm, htb3]
  obtain ⟨hbt_eq, _⟩ :=
    apply_family_of_orderOf_eq_three ρ s hs2 w hwrange hequiv hcomm hbraid hb ht hbt3
  have hft3 : orderOf (f * t) = 3 := by rw [triaRep_orderOf_mul_comm]; exact htf3'
  obtain ⟨hft_eq, _⟩ :=
    apply_family_of_orderOf_eq_three ρ s hs2 w hwrange hequiv hcomm hbraid hf_conj ht hft3
  have hsum : w a + w b + w f = 0 := by
    rw [← hf] at hab_sum
    exact hab_sum
  have hwt0 : w t = 0 := by
    have hzero : (ρ t - 1) (w a + w b + w f) = 0 := by
      rw [hsum, map_zero]
    rw [map_add, map_add] at hzero
    rw [hat_eq, hbt_eq, hft_eq] at hzero
    simpa only [ZModModule.add_self, zero_add] using hzero
  exact (hw t ht).1 hwt0

end CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri
