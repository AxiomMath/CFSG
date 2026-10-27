module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Fix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic

public section

namespace CFSG.Quasithin.He6

open CFSG.QuasithinUnique.Setup.X1

variable {W : Type} [CommGroup W]

@[expose] def dsp (x : MulAut W) : W →* W :=
  MonoidHom.mk' (fun w => x w * w⁻¹) (fun a b => by
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)

theorem dsp_apply (x : MulAut W) (w : W) : dsp x w = x w * w⁻¹ := rfl

@[expose] def cmt (x : MulAut W) (U : Subgroup W) : Subgroup W := U.map (dsp x)

theorem mem_cmt {x : MulAut W} {U : Subgroup W} {v : W} :
    v ∈ cmt x U ↔ ∃ u ∈ U, x u * u⁻¹ = v := by
  simp [cmt, Subgroup.mem_map, dsp_apply]

theorem dsp_mem_cmt {x : MulAut W} {U : Subgroup W} {u : W} (hu : u ∈ U) :
    x u * u⁻¹ ∈ cmt x U :=
  mem_cmt.2 ⟨u, hu, rfl⟩

theorem cmt_eq_bot_iff {x : MulAut W} {U : Subgroup W} :
    cmt x U = ⊥ ↔ ∀ u ∈ U, x u = u := by
  constructor
  · intro h u hu
    have := dsp_mem_cmt (x := x) hu
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  · intro h
    refine (Subgroup.eq_bot_iff_forall _).2 fun v hv => ?_
    obtain ⟨u, hu, rfl⟩ := mem_cmt.1 hv
    rw [h u hu, mul_inv_cancel]

theorem cmt_mono {x : MulAut W} {U V : Subgroup W} (h : U ≤ V) : cmt x U ≤ cmt x V :=
  Subgroup.map_mono h

theorem cmt_le_of_invariant {x : MulAut W} {U : Subgroup W} (hU : ∀ u ∈ U, x u ∈ U) :
    cmt x U ≤ U := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := mem_cmt.1 hv
  exact U.mul_mem (hU u hu) (U.inv_mem hu)

theorem cmt_invariant {g x : MulAut W} (hgx : g * x = x * g) {U : Subgroup W}
    (hU : ∀ u ∈ U, g u ∈ U) : ∀ v ∈ cmt x U, g v ∈ cmt x U := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := mem_cmt.1 hv
  refine mem_cmt.2 ⟨g u, hU u hu, ?_⟩
  have h1 : g (x u) = x (g u) := by
    have := congrArg (fun m : MulAut W => m u) hgx
    exact this
  rw [map_mul, map_inv, h1]

@[expose] def fixer (U : Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | ∀ u ∈ U, g u = u}
  one_mem' := fun u _ => rfl
  mul_mem' := by
    intro g h hg hh u hu
    show g (h u) = u
    rw [hh u hu, hg u hu]
  inv_mem' := by
    intro g hg u hu
    have h1 : g⁻¹ (g u) = u := MulAut.inv_apply_self W g u
    rw [hg u hu] at h1
    exact h1

theorem inv_apply_mem {A : Subgroup (MulAut W)} {U : Subgroup W} (hU : ∀ g ∈ A, ∀ u ∈ U, g u ∈ U)
    {g : MulAut W} (hg : g ∈ A) {u : W} (hu : u ∈ U) : g⁻¹ u ∈ U :=
  hU g⁻¹ (A.inv_mem hg) u hu

section Simple

variable {A N : Subgroup (MulAut W)}

theorem eq_bot_or_eq_of_normal (hA : IsSimpleGroup ↥A) (hNA : N ≤ A)
    (hN : ∀ g ∈ A, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : N = ⊥ ∨ N = A := by
  have hnorm : (N.subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNA]
    exact fun h g hh hg => hN g hg h hh
  have := hnorm
  rcases hA.eq_bot_or_eq_top_of_normal (N.subgroupOf A) with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le hNA
  · right
    rw [Subgroup.subgroupOf_eq_top] at h
    exact le_antisymm hNA h

theorem acts_trivially_of_simple (hA : IsSimpleGroup ↥A) {U : Subgroup W}
    (hU : ∀ g ∈ A, ∀ u ∈ U, g u ∈ U) {a : MulAut W} (haA : a ∈ A) (ha1 : a ≠ 1)
    (ha : ∀ u ∈ U, a u = u) : ∀ g ∈ A, ∀ u ∈ U, g u = u := by
  have hNA : A ⊓ fixer U ≤ A := inf_le_left
  have hN : ∀ g ∈ A, ∀ n ∈ A ⊓ fixer U, g * n * g⁻¹ ∈ A ⊓ fixer U := by
    intro g hg n hn
    refine ⟨A.mul_mem (A.mul_mem hg hn.1) (A.inv_mem hg), ?_⟩
    intro u hu
    show g (n (g⁻¹ u)) = u
    rw [hn.2 _ (inv_apply_mem hU hg hu)]
    exact MulAut.apply_inv_self W g u
  rcases eq_bot_or_eq_of_normal hA hNA hN with h | h
  · exfalso
    have : a ∈ A ⊓ fixer U := ⟨haA, ha⟩
    rw [h, Subgroup.mem_bot] at this
    exact ha1 this
  · intro g hg u hu
    have : g ∈ A ⊓ fixer U := by rw [h]; exact hg
    exact this.2 u hu

end Simple

section Card

variable [Finite W]

omit [Finite W] in
theorem index_fixV_zpowers_eq_card_cmt (x : MulAut W) :
    (fixV (Subgroup.zpowers x)).index = Nat.card (cmt x ⊤) := by
  have hker : (dsp x).ker = fixV (Subgroup.zpowers x) := by
    ext w
    rw [MonoidHom.mem_ker, mem_fixV_zpowers]
    show x w * w⁻¹ = 1 ↔ x w = w
    exact mul_inv_eq_one
  rw [← hker, Subgroup.index_ker, cmt, ← MonoidHom.range_eq_map]

omit [Finite W] in
theorem cmt_lt_of_sq_eq_one (hW : ∀ w : W, w * w = 1) {x : MulAut W} (hx : x * x = 1)
    {U : Subgroup W} (hU : ∀ u ∈ U, x u ∈ U) (hne : U ≠ ⊥) : cmt x U < U := by
  have hle : cmt x U ≤ U := cmt_le_of_invariant hU
  refine lt_of_le_of_ne hle fun heq => hne ?_
  have hinv : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hW w)
  have hfix : ∀ v ∈ cmt x U, x v = v := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := mem_cmt.1 hv
    have hxx : x (x u) = u := by
      have := congrArg (fun m : MulAut W => m u) hx
      exact this
    rw [map_mul, map_inv, hxx, hinv (x u), hinv u, mul_comm]
  have h0 : cmt x (cmt x U) = ⊥ := cmt_eq_bot_iff.2 hfix
  rw [heq] at h0
  rw [← heq]
  exact (Subgroup.eq_bot_iff_forall _).2 fun v hv => by
    rw [h0] at hv
    exact hv

theorem card_cmt_le_two_of_card_le_four (hW : ∀ w : W, w * w = 1) {x : MulAut W} (hx : x * x = 1)
    {U : Subgroup W} (hU : ∀ u ∈ U, x u ∈ U) (hcard : Nat.card U ≤ 4) :
    Nat.card (cmt x U) ≤ 2 := by
  by_cases hne : U = ⊥
  · have : cmt x U = ⊥ := by rw [hne]; exact Subgroup.map_bot _
    rw [this]
    simp
  have hlt := cmt_lt_of_sq_eq_one hW hx hU hne
  have hdvd : Nat.card (cmt x U) ∣ Nat.card U := by
    have : (cmt x U).subgroupOf U ≤ ⊤ := le_top
    exact Subgroup.card_dvd_of_le hlt.le
  have hsub : Nat.card (cmt x U) < Nat.card U := Subgroup.card_lt_of_lt hlt
  have hpos : 0 < Nat.card U := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> omega
  nlinarith [Nat.card_pos (α := cmt x U)]

end Card

end CFSG.Quasithin.He6
