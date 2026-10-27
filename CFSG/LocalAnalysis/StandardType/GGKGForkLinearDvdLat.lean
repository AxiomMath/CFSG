module

public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticePerm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord Multiplicative UCoord

private def ggKGTl_red (p : ℕ) {d : ℕ} (y : Fin d → ℤ) : Fin d → Multiplicative (ZMod p) :=
  fun i => ofAdd ((y i : ZMod p))

private theorem ggKGTl_red_add {p d : ℕ} (y z : Fin d → ℤ) :
    ggKGTl_red p (y + z) = ggKGTl_red p y * ggKGTl_red p z := by
  funext i
  simp only [ggKGTl_red, Pi.add_apply, Pi.mul_apply, Int.cast_add, ofAdd_add]

private theorem ggKGTl_red_zero {p d : ℕ} :
    ggKGTl_red p (0 : Fin d → ℤ) = 1 := by
  funext i
  simp only [ggKGTl_red, Pi.zero_apply, Int.cast_zero, ofAdd_zero, Pi.one_apply]

private theorem ggKGTl_red_swap {p d : ℕ} (i j : Fin d) (y : Fin d → ℤ) :
    ggKGTl_red p (fun k => y (Equiv.swap i j k)) = permAut (Equiv.swap i j) (ggKGTl_red p y) := by
  funext k
  simp only [ggKGTl_red, permAut_apply, Function.comp_apply, Equiv.swap_inv]

private theorem ggKGTl_rootV_apply {p d : ℕ} (a b k : Fin d) :
    ((rootV a b : ↥(sumZero d p)) : Fin d → Multiplicative (ZMod p)) k =
      ofAdd ((if k = a then 1 else 0) - (if k = b then 1 else 0)) := rfl

private theorem ggKGTl_permAut_rootV {p d : ℕ} (σ : Equiv.Perm (Fin d)) (i j : Fin d) :
    permAut σ ((rootV i j : ↥(sumZero d p)) : Fin d → Multiplicative (ZMod p)) =
      ((rootV (σ i) (σ j) : ↥(sumZero d p)) : Fin d → Multiplicative (ZMod p)) :=
  congrArg (fun x : ↥(sumZero d p) => (x : Fin d → Multiplicative (ZMod p)))
    (permAutV_rootV σ i j)

private theorem ggKGTl_permAut_swap_mul_inv_const {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {i j : Fin d} (v : Fin d → Multiplicative (ZMod p)) {c : Multiplicative (ZMod p)}
    (hc : permAut (Equiv.swap i j) v * v⁻¹ = fun _ => c) : v i = v j := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hi' : (permAut (Equiv.swap i j) v * v⁻¹) i = c := congrFun hc i
  have hj' : (permAut (Equiv.swap i j) v * v⁻¹) j = c := congrFun hc j
  have h1 : toAdd ((permAut (Equiv.swap i j) v * v⁻¹) i) =
      toAdd ((permAut (Equiv.swap i j) v * v⁻¹) j) := by rw [hi', hj']
  simp only [Pi.mul_apply, Pi.inv_apply, toAdd_mul, toAdd_inv, permAut_apply,
    Function.comp_apply, Equiv.swap_inv, Equiv.swap_apply_left, Equiv.swap_apply_right] at h1
  have h3 : toAdd (v j) - toAdd (v i) = 0 := by
    have h1' : toAdd (v j) - toAdd (v i) = toAdd (v i) - toAdd (v j) := by
      rw [sub_eq_add_neg, sub_eq_add_neg]
      exact h1
    have h2 : (toAdd (v j) - toAdd (v i)) + (toAdd (v j) - toAdd (v i)) = 0 := by
      nth_rewrite 2 [h1']
      rw [sub_add_sub_cancel, sub_self]
    have h2' : (2 : ZMod p) * (toAdd (v j) - toAdd (v i)) = 0 := by
      rw [two_mul]
      exact h2
    exact (mul_eq_zero.mp h2').resolve_left (coord_two_ne_zero hp hp2)
  have h4 : toAdd (v j) = toAdd (v i) := sub_eq_zero.mp h3
  exact toAdd.injective h4.symm

private theorem ggKGTl_ratio_ne_const {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : 4 ≤ d)
    {σ : Equiv.Perm (Fin d)} {i : Fin d} (hi : σ i ≠ i) :
    ¬ ∃ c : Multiplicative (ZMod p),
      permAut σ ((rootV i (σ i) : ↥(sumZero d p)) : Fin d → Multiplicative (ZMod p)) *
        (((rootV i (σ i) : ↥(sumZero d p)) : Fin d → Multiplicative (ZMod p)))⁻¹ =
          fun _ => c := by
  haveI : Fact p.Prime := ⟨hp⟩
  rintro ⟨c, hc⟩
  obtain ⟨l, hli, hlj, hlk⟩ := TypeA.exists_fin_avoid_three hd i (σ i) (σ (σ i))
  have hl : (permAut σ ((rootV i (σ i) : ↥(sumZero d p)) :
        Fin d → Multiplicative (ZMod p)) *
      (((rootV i (σ i) : ↥(sumZero d p)) : Fin d → Multiplicative (ZMod p)))⁻¹) l = 1 := by
    simp only [Pi.mul_apply, Pi.inv_apply, ggKGTl_permAut_rootV, ggKGTl_rootV_apply,
      if_neg hlj, if_neg hlk, if_neg hli]
    exact mul_inv_cancel _
  have hsi : (permAut σ ((rootV i (σ i) : ↥(sumZero d p)) :
        Fin d → Multiplicative (ZMod p)) *
      (((rootV i (σ i) : ↥(sumZero d p)) : Fin d → Multiplicative (ZMod p)))⁻¹) (σ i) =
        ofAdd (2 : ZMod p) := by
    have hne : σ i ≠ σ (σ i) := fun h => hi (σ.injective h).symm
    simp only [Pi.mul_apply, Pi.inv_apply, ggKGTl_permAut_rootV, ggKGTl_rootV_apply,
      if_pos rfl, if_neg hne, if_neg hi, if_true]
    rw [show (0 : ZMod p) - 1 = -1 by exact zero_sub 1]
    rw [show (1 : ZMod p) - 0 = 1 by exact sub_zero 1]
    rw [ofAdd_neg]
    rw [show ((Multiplicative.ofAdd (1 : ZMod p))⁻¹)⁻¹ = Multiplicative.ofAdd 1 by
      exact inv_inv _]
    rw [← ofAdd_add, one_add_one_eq_two]
  have hc1 : c = 1 := ((congrFun hc l).symm).trans hl
  have hc2 : c = ofAdd (2 : ZMod p) := ((congrFun hc (σ i)).symm).trans hsi
  rw [hc1] at hc2
  apply coord_two_ne_zero hp hp2
  simpa using (congrArg toAdd hc2).symm

private theorem ggKGTl_mem_permAut {p d : ℕ} {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (σ : Equiv.Perm (Fin d))
    (f : Fin d → Multiplicative (ZMod p)) (hf : f ∈ S) : permAut σ f ∈ S := by
  rcases hS with h | h
  · rw [h]; exact Subgroup.mem_top _
  · rw [h] at hf ⊢; exact permAut_mem_sumZero σ hf

private noncomputable def ggKGTl_permS {p d : ℕ} {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (σ : Equiv.Perm (Fin d)) : MulAut ↥S where
  toFun f := ⟨permAut σ f, ggKGTl_mem_permAut hS σ f f.2⟩
  invFun f := ⟨permAut σ⁻¹ f, ggKGTl_mem_permAut hS σ⁻¹ f f.2⟩
  left_inv f := Subtype.ext (by
    show permAut σ⁻¹ (permAut σ (↑f)) = (↑f : Fin d → Multiplicative (ZMod p))
    funext k
    simp only [permAut_apply, Function.comp_apply, inv_inv]
    exact congrArg (f : Fin d → Multiplicative (ZMod p)) (Equiv.symm_apply_apply σ k))
  right_inv f := Subtype.ext (by
    show permAut σ (permAut σ⁻¹ (↑f)) = (↑f : Fin d → Multiplicative (ZMod p))
    funext k
    simp only [permAut_apply, Function.comp_apply, inv_inv]
    exact congrArg (f : Fin d → Multiplicative (ZMod p)) (Equiv.apply_symm_apply σ k))
  map_mul' f g := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    exact map_mul (permAut σ) (f : Fin d → Multiplicative (ZMod p))
      (g : Fin d → Multiplicative (ZMod p)))

private theorem ggKGTl_permS_apply {p d : ℕ} {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (σ : Equiv.Perm (Fin d)) (f : ↥S) :
    (ggKGTl_permS hS σ f : Fin d → Multiplicative (ZMod p)) = permAut σ f := rfl

private theorem ggKGTl_permAut_mul {p d : ℕ} (σ τ : Equiv.Perm (Fin d))
    (f : Fin d → Multiplicative (ZMod p)) :
    permAut (σ * τ) f = permAut σ (permAut τ f) := by
  funext k
  simp only [permAut_apply, Function.comp_apply, mul_inv_rev, Equiv.Perm.mul_apply]

private theorem ggKGTl_permS_mul {p d : ℕ} {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (σ τ : Equiv.Perm (Fin d)) :
    ggKGTl_permS hS (σ * τ) = ggKGTl_permS hS σ * ggKGTl_permS hS τ := by
  refine MulEquiv.ext fun f => Subtype.ext ?_
  show (ggKGTl_permS hS (σ * τ) f : Fin d → Multiplicative (ZMod p)) =
    (ggKGTl_permS hS σ (ggKGTl_permS hS τ f) : Fin d → Multiplicative (ZMod p))
  rw [ggKGTl_permS_apply, ggKGTl_permS_apply, ggKGTl_permS_apply]
  exact ggKGTl_permAut_mul σ τ (f : Fin d → Multiplicative (ZMod p))

private noncomputable def ggKGTl_PS {p d : ℕ} {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) : Equiv.Perm (Fin d) →* MulAut ↥S :=
  MonoidHom.mk' (ggKGTl_permS hS) (ggKGTl_permS_mul hS)

private theorem ggKGTl_PS_apply {p d : ℕ} {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (σ : Equiv.Perm (Fin d)) :
    ggKGTl_PS hS σ = ggKGTl_permS hS σ := rfl

private theorem ggKGTl_PS_const {p d : ℕ} {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (σ : Equiv.Perm (Fin d)) (c : Multiplicative (ZMod p))
    {k : ↥S} (hk : (k : Fin d → Multiplicative (ZMod p)) = fun _ => c) :
    ggKGTl_PS hS σ k = k := by
  apply Subtype.ext
  rw [ggKGTl_PS_apply]
  change (ggKGTl_permS hS σ k : Fin d → Multiplicative (ZMod p)) =
    (k : Fin d → Multiplicative (ZMod p))
  rw [ggKGTl_permS_apply, hk]
  funext i
  simp only [permAut_apply, Function.comp_apply]

private noncomputable def ggKGTl_lift {α β : Type*} {f : α → β} (h : Function.Surjective f)
    (b : β) : α :=
  Classical.choose (h b)

private theorem ggKGTl_lift_spec {α β : Type*} {f : α → β} (h : Function.Surjective f) (b : β) :
    f (ggKGTl_lift h b) = b :=
  Classical.choose_spec (h b)

private theorem ggKGTl_PS_wd {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (Θ : ↥S →* ↥A)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod p),
      (f : Fin d → Multiplicative (ZMod p)) = fun _ => c)
    (σ : Equiv.Perm (Fin d)) {f f' : ↥S} (h : Θ f = Θ f') :
    Θ (ggKGTl_PS hS σ f) = Θ (ggKGTl_PS hS σ f') := by
  have hk : Θ (f' * f⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨c, hc⟩ := (hker (f' * f⁻¹)).mp hk
  have hf' : f * (f' * f⁻¹) = f' := by
    calc f * (f' * f⁻¹) = (f * f') * f⁻¹ := (mul_assoc f f' f⁻¹).symm
      _ = (f' * f) * f⁻¹ := by rw [mul_comm f f']
      _ = f' * (f * f⁻¹) := mul_assoc f' f f⁻¹
      _ = f' * 1 := by rw [mul_inv_cancel]
      _ = f' := mul_one f'
  have hPSk : ggKGTl_PS hS σ (f' * f⁻¹) = f' * f⁻¹ := ggKGTl_PS_const hS σ c hc
  have hmain : Θ (ggKGTl_PS hS σ f') = Θ (ggKGTl_PS hS σ f) := by
    calc Θ (ggKGTl_PS hS σ f')
        = Θ (ggKGTl_PS hS σ (f * (f' * f⁻¹))) := by rw [hf']
      _ = Θ (ggKGTl_PS hS σ f * ggKGTl_PS hS σ (f' * f⁻¹)) := by rw [map_mul]
      _ = Θ (ggKGTl_PS hS σ f * (f' * f⁻¹)) := by rw [hPSk]
      _ = Θ (ggKGTl_PS hS σ f) * Θ (f' * f⁻¹) := by rw [map_mul]
      _ = Θ (ggKGTl_PS hS σ f) * 1 := by rw [hk]
      _ = Θ (ggKGTl_PS hS σ f) := mul_one _
  exact hmain.symm

private noncomputable def ggKGTl_E {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (Θ : ↥S →* ↥A) (hΘ : Function.Surjective Θ)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod p),
      (f : Fin d → Multiplicative (ZMod p)) = fun _ => c)
    (σ : Equiv.Perm (Fin d)) : MulAut ↥A where
  toFun a := Θ (ggKGTl_PS hS σ (ggKGTl_lift hΘ a))
  invFun a := Θ (ggKGTl_PS hS σ⁻¹ (ggKGTl_lift hΘ a))
  left_inv a := by
    dsimp only
    set g := ggKGTl_lift hΘ a with hg
    have hgΘ : Θ g = a := ggKGTl_lift_spec hΘ a
    have hwd := ggKGTl_PS_wd hS Θ hker σ⁻¹
      (ggKGTl_lift_spec hΘ (Θ (ggKGTl_PS hS σ g)))
    have hmul : ggKGTl_PS hS σ⁻¹ * ggKGTl_PS hS σ = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have hguard : ggKGTl_PS hS σ⁻¹ (ggKGTl_PS hS σ g) = g := by
      rw [← MulAut.mul_apply, hmul, MulAut.one_apply]
    calc Θ (ggKGTl_PS hS σ⁻¹ (ggKGTl_lift hΘ (Θ (ggKGTl_PS hS σ g))))
        = Θ (ggKGTl_PS hS σ⁻¹ (ggKGTl_PS hS σ g)) := hwd
      _ = Θ g := by rw [hguard]
      _ = a := hgΘ
  right_inv a := by
    dsimp only
    set g := ggKGTl_lift hΘ a with hg
    have hgΘ : Θ g = a := ggKGTl_lift_spec hΘ a
    have hwd := ggKGTl_PS_wd hS Θ hker σ
      (ggKGTl_lift_spec hΘ (Θ (ggKGTl_PS hS σ⁻¹ g)))
    have hmul : ggKGTl_PS hS σ * ggKGTl_PS hS σ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hguard : ggKGTl_PS hS σ (ggKGTl_PS hS σ⁻¹ g) = g := by
      rw [← MulAut.mul_apply, hmul, MulAut.one_apply]
    calc Θ (ggKGTl_PS hS σ (ggKGTl_lift hΘ (Θ (ggKGTl_PS hS σ⁻¹ g))))
        = Θ (ggKGTl_PS hS σ (ggKGTl_PS hS σ⁻¹ g)) := hwd
      _ = Θ g := by rw [hguard]
      _ = a := hgΘ
  map_mul' a b := by
    have h1 : Θ (ggKGTl_lift hΘ (a * b)) = Θ (ggKGTl_lift hΘ a * ggKGTl_lift hΘ b) := by
      rw [ggKGTl_lift_spec hΘ (a * b), map_mul, ggKGTl_lift_spec hΘ a, ggKGTl_lift_spec hΘ b]
    calc Θ (ggKGTl_PS hS σ (ggKGTl_lift hΘ (a * b)))
        = Θ (ggKGTl_PS hS σ (ggKGTl_lift hΘ a * ggKGTl_lift hΘ b)) :=
          ggKGTl_PS_wd hS Θ hker σ h1
      _ = Θ (ggKGTl_PS hS σ (ggKGTl_lift hΘ a) * ggKGTl_PS hS σ (ggKGTl_lift hΘ b)) := by
          rw [map_mul]
      _ = Θ (ggKGTl_PS hS σ (ggKGTl_lift hΘ a)) * Θ (ggKGTl_PS hS σ (ggKGTl_lift hΘ b)) := by
          rw [map_mul]

private theorem ggKGTl_E_apply {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (Θ : ↥S →* ↥A) (hΘ : Function.Surjective Θ)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod p),
      (f : Fin d → Multiplicative (ZMod p)) = fun _ => c)
    (σ : Equiv.Perm (Fin d)) (f : ↥S) :
    ggKGTl_E hS Θ hΘ hker σ (Θ f) = Θ (ggKGTl_PS hS σ f) :=
  ggKGTl_PS_wd hS Θ hker σ (ggKGTl_lift_spec hΘ (Θ f))

private theorem ggKGTl_E_mul {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (Θ : ↥S →* ↥A) (hΘ : Function.Surjective Θ)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod p),
      (f : Fin d → Multiplicative (ZMod p)) = fun _ => c)
    (σ τ : Equiv.Perm (Fin d)) :
    ggKGTl_E hS Θ hΘ hker (σ * τ) = ggKGTl_E hS Θ hΘ hker σ * ggKGTl_E hS Θ hΘ hker τ := by
  refine MulEquiv.ext fun a => ?_
  show Θ (ggKGTl_PS hS (σ * τ) (ggKGTl_lift hΘ a)) =
    Θ (ggKGTl_PS hS σ (ggKGTl_lift hΘ (Θ (ggKGTl_PS hS τ (ggKGTl_lift hΘ a)))))
  calc Θ (ggKGTl_PS hS (σ * τ) (ggKGTl_lift hΘ a))
      = Θ (ggKGTl_PS hS σ (ggKGTl_PS hS τ (ggKGTl_lift hΘ a))) := by
        simp only [ggKGTl_PS_apply, ggKGTl_permS_mul, MulAut.mul_apply]
    _ = Θ (ggKGTl_PS hS σ (ggKGTl_lift hΘ (Θ (ggKGTl_PS hS τ (ggKGTl_lift hΘ a))))) :=
        (ggKGTl_PS_wd hS Θ hker σ
          (ggKGTl_lift_spec hΘ (Θ (ggKGTl_PS hS τ (ggKGTl_lift hΘ a))))).symm

private noncomputable def ggKGTl_EHom {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (Θ : ↥S →* ↥A) (hΘ : Function.Surjective Θ)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod p),
      (f : Fin d → Multiplicative (ZMod p)) = fun _ => c) :
    Equiv.Perm (Fin d) →* MulAut ↥A :=
  MonoidHom.mk' (ggKGTl_E hS Θ hΘ hker) (ggKGTl_E_mul hS Θ hΘ hker)

private theorem ggKGTl_EHom_apply {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (Θ : ↥S →* ↥A) (hΘ : Function.Surjective Θ)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod p),
      (f : Fin d → Multiplicative (ZMod p)) = fun _ => c)
    (σ : Equiv.Perm (Fin d)) :
    ggKGTl_EHom hS Θ hΘ hker σ = ggKGTl_E hS Θ hΘ hker σ := rfl

private theorem ggKGTl_rootV_mem {p d : ℕ} {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (i j : Fin d) :
    ((rootV i j : ↥(sumZero d p)) : Fin d → Multiplicative (ZMod p)) ∈ S := by
  rcases hS with h | h
  · rw [h]; exact Subgroup.mem_top _
  · rw [h]; exact (rootV i j).2

private theorem ggKGTl_E_kernel {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : 4 ≤ d)
    (hS : S = ⊤ ∨ S = sumZero d p) (Θ : ↥S →* ↥A) (hΘ : Function.Surjective Θ)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod p),
      (f : Fin d → Multiplicative (ZMod p)) = fun _ => c)
    {σ : Equiv.Perm (Fin d)} (hσ : ggKGTl_EHom hS Θ hΘ hker σ = 1) : σ = 1 := by
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra h
    push Not at h
    exact hne (Equiv.ext h)
  let f : ↥S := ⟨((rootV i (σ i) : ↥(sumZero d p)) : Fin d → Multiplicative (ZMod p)),
    ggKGTl_rootV_mem hS i (σ i)⟩
  have h1 : Θ (ggKGTl_PS hS σ f) = Θ f := by
    have h2 : ggKGTl_EHom hS Θ hΘ hker σ (Θ f) = Θ f := by rw [hσ, MulAut.one_apply]
    rw [ggKGTl_EHom_apply, ggKGTl_E_apply] at h2
    exact h2
  have hk : Θ (ggKGTl_PS hS σ f * f⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
  obtain ⟨c, hc⟩ := (hker (ggKGTl_PS hS σ f * f⁻¹)).mp hk
  apply ggKGTl_ratio_ne_const hp hp2 hd hi
  refine ⟨c, ?_⟩
  simpa only [f, Subgroup.coe_mul, Subgroup.coe_inv, ggKGTl_PS_apply, ggKGTl_permS_apply]
    using hc

private theorem ggKGTl_E_injective {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : 4 ≤ d)
    (hS : S = ⊤ ∨ S = sumZero d p) (Θ : ↥S →* ↥A) (hΘ : Function.Surjective Θ)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod p),
      (f : Fin d → Multiplicative (ZMod p)) = fun _ => c) :
    Function.Injective (ggKGTl_EHom hS Θ hΘ hker) := by
  intro σ τ h
  have h1 : ggKGTl_EHom hS Θ hΘ hker (σ * τ⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : σ * τ⁻¹ = 1 := ggKGTl_E_kernel hp hp2 hd hS Θ hΘ hker h1
  exact mul_inv_eq_one.mp h2

private def ggKGTl_fixSub {G : Type*} [Group G] (φ : MulAut G) : Subgroup G :=
  φ.toMonoidHom.eqLocus (MonoidHom.id G)

private theorem ggKGTl_mem_fixSub {G : Type*} [Group G] (φ : MulAut G) {x : G} :
    x ∈ ggKGTl_fixSub φ ↔ φ x = x := Iff.rfl

private def ggKGTl_fixMS {p d : ℕ} (S : Subgroup (Fin d → Multiplicative (ZMod p)))
    (σ : Equiv.Perm (Fin d)) : Subgroup (Fin d → Multiplicative (ZMod p)) :=
  S ⊓ ggKGTl_fixSub (permAut σ)

private noncomputable def ggKGTl_fixS_equiv_fixMS {p d : ℕ}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (σ : Equiv.Perm (Fin d)) :
    ↥(ggKGTl_fixSub (ggKGTl_permS hS σ)) ≃ ↥(ggKGTl_fixMS S σ) where
  toFun f := ⟨f.1.1, f.1.2, by
    change permAut σ f.1.1 = f.1.1
    exact congrArg Subtype.val (f.2 : ggKGTl_permS hS σ f.1 = f.1)⟩
  invFun v := ⟨⟨v.1, v.2.1⟩, by
    change ggKGTl_permS hS σ ⟨v.1, v.2.1⟩ = ⟨v.1, v.2.1⟩
    apply Subtype.ext
    exact v.2.2⟩
  left_inv f := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; rfl

private theorem ggKGTl_fixMS_card {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) {a b : Fin d} (hab : a ≠ b) :
    Nat.card ↥(ggKGTl_fixMS S (Equiv.swap a b)) * p = Nat.card ↥S := by
  rcases hS with h | h
  · rw [h]
    have e : ↥(ggKGTl_fixMS (⊤ : Subgroup (Fin d → Multiplicative (ZMod p)))
        (Equiv.swap a b)) ≃ {v : Fin d → Multiplicative (ZMod p) //
          permAut (Equiv.swap a b) v = v} :=
      { toFun := fun v => ⟨v.1, v.2.2⟩
        invFun := fun v => ⟨v.1, Subgroup.mem_top _, v.2⟩
        left_inv := fun v => by apply Subtype.ext; rfl
        right_inv := fun v => by apply Subtype.ext; rfl }
    rw [Nat.card_congr e]
    have htop : Nat.card ↥(⊤ : Subgroup (Fin d → Multiplicative (ZMod p))) =
        Nat.card (Fin d → Multiplicative (ZMod p)) :=
      Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [htop]
    exact card_fix_permAut_swap hp hp2 hab
  · rw [h]
    have e : ↥(ggKGTl_fixMS (sumZero d p) (Equiv.swap a b)) ≃
        {v : ↥(sumZero d p) // permAutV (Equiv.swap a b) v = v} :=
      { toFun := fun v => ⟨⟨v.1, v.2.1⟩, by apply Subtype.ext; exact v.2.2⟩
        invFun := fun v => ⟨v.1.1, v.1.2, by exact congrArg Subtype.val v.2⟩
        left_inv := fun v => by apply Subtype.ext; rfl
        right_inv := fun v => by apply Subtype.ext; rfl }
    rw [Nat.card_congr e]
    exact (isPseudoReflection_permAutV_swap hp hp2 hab).2

private theorem ggKGTl_const_mem {p d : ℕ} (hpd : p ∣ d)
    {S : Subgroup (Fin d → Multiplicative (ZMod p))} (hS : S = ⊤ ∨ S = sumZero d p)
    (c : Multiplicative (ZMod p)) :
    (fun _ => c : Fin d → Multiplicative (ZMod p)) ∈ S := by
  rcases hS with h | h
  · rw [h]; exact Subgroup.mem_top _
  · rw [h, mem_sumZero]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show ((d : ℕ) : ZMod p) = 0 from (ZMod.natCast_eq_zero_iff d p).mpr hpd, zero_mul]

private theorem ggKGTl_ker_card {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))} (hpd : p ∣ d) (hd : 0 < d)
    (hS : S = ⊤ ∨ S = sumZero d p) (Θ : ↥S →* ↥A)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod p),
      (f : Fin d → Multiplicative (ZMod p)) = fun _ => c) :
    Nat.card ↥(Θ.ker) = p := by
  let i0 : Fin d := ⟨0, hd⟩
  have e : Multiplicative (ZMod p) ≃ ↥(Θ.ker) :=
    { toFun := fun c => ⟨⟨fun _ => c, ggKGTl_const_mem hpd hS c⟩,
        show Θ ⟨(fun _ => c), ggKGTl_const_mem hpd hS c⟩ = 1 from (hker _).mpr ⟨c, rfl⟩⟩
      invFun := fun f => (f.1 : Fin d → Multiplicative (ZMod p)) i0
      left_inv := fun c => rfl
      right_inv := fun f => by
        obtain ⟨c, hc⟩ := (hker (f.1 : ↥S)).mp (show Θ (f.1) = 1 from f.2)
        apply Subtype.ext
        apply Subtype.ext
        show (fun _ => (f.1 : Fin d → Multiplicative (ZMod p)) i0) =
          (f.1 : Fin d → Multiplicative (ZMod p))
        rw [hc] }
  calc Nat.card ↥(Θ.ker) = Nat.card (Multiplicative (ZMod p)) := (Nat.card_congr e).symm
    _ = Nat.card (ZMod p) := rfl
    _ = p := Nat.card_zmod p

private theorem ggKGTl_Spow {p d : ℕ} {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (f : ↥S) : f ^ p = 1 := by
  rcases hS with h | h
  · subst h
    apply Subtype.ext
    funext i
    apply toAdd.injective
    simp only [Subgroup.coe_pow, Subgroup.coe_one, Pi.pow_apply, toAdd_pow, Pi.one_apply,
      toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  · subst h
    exact pow_p_eq_one f

private theorem ggKGTl_Aelem {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (Θ : ↥S →* ↥A) (hΘ : Function.Surjective Θ) :
    IsElemAbelian p A := by
  refine ⟨IsMulCommutative.mk ⟨fun a b => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨f, rfl⟩ := hΘ a
    obtain ⟨g, rfl⟩ := hΘ b
    rw [← map_mul, ← map_mul,
      show f * g = g * f from Subtype.ext (mul_comm (f : Fin d → Multiplicative (ZMod p))
        (g : Fin d → Multiplicative (ZMod p)))]
  · obtain ⟨f, hf⟩ := hΘ ⟨x, hx⟩
    have hxeq : x = (Θ f : MulAut L') := congrArg Subtype.val hf.symm
    rw [hxeq, ← Subgroup.coe_pow, ← map_pow, ggKGTl_Spow hS f, map_one]
    rfl

private theorem ggKGTl_fixS_of_theta {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (Θ : ↥S →* ↥A)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod p),
      (f : Fin d → Multiplicative (ZMod p)) = fun _ => c)
    {a b : Fin d} (hab : a ≠ b) {f : ↥S}
    (hf : Θ (ggKGTl_PS hS (Equiv.swap a b) f) = Θ f) :
    ggKGTl_PS hS (Equiv.swap a b) f = f := by
  have hk : Θ (ggKGTl_PS hS (Equiv.swap a b) f * f⁻¹) = 1 := by
    rw [map_mul, map_inv, hf, mul_inv_cancel]
  obtain ⟨c, hc⟩ := (hker (ggKGTl_PS hS (Equiv.swap a b) f * f⁻¹)).mp hk
  have hv : permAut (Equiv.swap a b) (f : Fin d → Multiplicative (ZMod p)) *
      (f : Fin d → Multiplicative (ZMod p))⁻¹ = fun _ => c := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, ggKGTl_PS_apply, ggKGTl_permS_apply] using hc
  have hsym : (f : Fin d → Multiplicative (ZMod p)) a =
      (f : Fin d → Multiplicative (ZMod p)) b :=
    ggKGTl_permAut_swap_mul_inv_const hp hp2 _ hv
  apply Subtype.ext
  funext k
  by_cases hka : k = a
  · subst hka
    rw [ggKGTl_PS_apply, ggKGTl_permS_apply, permAut_apply, Function.comp_apply,
      Equiv.swap_inv, Equiv.swap_apply_left]
    exact hsym.symm
  · by_cases hkb : k = b
    · subst hkb
      rw [ggKGTl_PS_apply, ggKGTl_permS_apply, permAut_apply, Function.comp_apply,
        Equiv.swap_inv, Equiv.swap_apply_right]
      exact hsym
    · rw [ggKGTl_PS_apply, ggKGTl_permS_apply, permAut_apply, Function.comp_apply,
        Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hka hkb]

private theorem ggKGTl_fixA_eq {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hS : S = ⊤ ∨ S = sumZero d p) (Θ : ↥S →* ↥A) (hΘ : Function.Surjective Θ)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod p),
      (f : Fin d → Multiplicative (ZMod p)) = fun _ => c)
    {a b : Fin d} (hab : a ≠ b) :
    ggKGTl_fixSub (ggKGTl_EHom hS Θ hΘ hker (Equiv.swap a b)) =
      (ggKGTl_fixSub (ggKGTl_PS hS (Equiv.swap a b))).map Θ := by
  ext x
  constructor
  · intro hx
    rw [ggKGTl_mem_fixSub] at hx
    obtain ⟨f, rfl⟩ := hΘ x
    rw [Subgroup.mem_map]
    refine ⟨f, ?_, rfl⟩
    rw [ggKGTl_mem_fixSub]
    apply ggKGTl_fixS_of_theta hp hp2 hS Θ hker hab
    rw [ggKGTl_EHom_apply, ggKGTl_E_apply] at hx
    exact hx
  · rintro ⟨f, hf, rfl⟩
    change ggKGTl_EHom hS Θ hΘ hker (Equiv.swap a b) (Θ f) = Θ f
    have hf' : ggKGTl_PS hS (Equiv.swap a b) f = f :=
      (ggKGTl_mem_fixSub (ggKGTl_PS hS (Equiv.swap a b))).mp hf
    rw [ggKGTl_EHom_apply, ggKGTl_E_apply, hf']

private theorem ggKGTl_E_swap_fix_card {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ d) (hd : 4 ≤ d)
    (hS : S = ⊤ ∨ S = sumZero d p) (Θ : ↥S →* ↥A) (hΘ : Function.Surjective Θ)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod p),
      (f : Fin d → Multiplicative (ZMod p)) = fun _ => c)
    {a b : Fin d} (hab : a ≠ b) :
    Nat.card ↥(ggKGTl_fixSub (ggKGTl_EHom hS Θ hΘ hker (Equiv.swap a b))) * p =
      Nat.card ↥A := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hK : Nat.card ↥(Θ.ker) = p := ggKGTl_ker_card hpd (by omega) hS Θ hker
  have hFixS_card : Nat.card ↥(ggKGTl_fixSub (ggKGTl_permS hS (Equiv.swap a b))) * p =
      Nat.card ↥S := by
    rw [Nat.card_congr (ggKGTl_fixS_equiv_fixMS hS (Equiv.swap a b))]
    exact ggKGTl_fixMS_card hp hp2 hS hab
  have hle : Θ.ker ≤ ggKGTl_fixSub (ggKGTl_permS hS (Equiv.swap a b)) := by
    intro k hk
    rw [ggKGTl_mem_fixSub]
    obtain ⟨c, hc⟩ := (hker k).mp (show Θ k = 1 from hk)
    exact ggKGTl_PS_const hS (Equiv.swap a b) c hc
  have hS_card : Nat.card ↥S = Nat.card ↥(Θ.ker) * Nat.card ↥A :=
    (Subgroup.card_ker_mul_card_of_surjective hΘ).symm
  have hidx : (ggKGTl_fixSub (ggKGTl_EHom hS Θ hΘ hker (Equiv.swap a b))).index =
      (ggKGTl_fixSub (ggKGTl_permS hS (Equiv.swap a b))).index := by
    rw [ggKGTl_fixA_eq hp hp2 hS Θ hΘ hker hab]
    exact Subgroup.index_map_eq (ggKGTl_fixSub (ggKGTl_permS hS (Equiv.swap a b))) hΘ hle
  have hFixSpos : 0 < Nat.card ↥(ggKGTl_fixSub (ggKGTl_permS hS (Equiv.swap a b))) := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, zero_mul] at hFixS_card
    exact (Nat.card_pos (α := ↥S)).ne' hFixS_card.symm
  have hp_index : (ggKGTl_fixSub (ggKGTl_permS hS (Equiv.swap a b))).index = p := by
    have h1 := Subgroup.card_mul_index (ggKGTl_fixSub (ggKGTl_permS hS (Equiv.swap a b)))
    rw [← hFixS_card] at h1
    exact Nat.mul_left_cancel hFixSpos h1
  have hFixA_index : (ggKGTl_fixSub (ggKGTl_EHom hS Θ hΘ hker (Equiv.swap a b))).index = p := by
    rw [hidx, hp_index]
  have h2 := Subgroup.card_mul_index
    (ggKGTl_fixSub (ggKGTl_EHom hS Θ hΘ hker (Equiv.swap a b)))
  rw [hFixA_index] at h2
  exact h2

private theorem ggKGTl_E_swap_refl {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ d) (hd : 4 ≤ d)
    (hS : S = ⊤ ∨ S = sumZero d p) (Θ : ↥S →* ↥A) (hΘ : Function.Surjective Θ)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod p),
      (f : Fin d → Multiplicative (ZMod p)) = fun _ => c)
    {a b : Fin d} (hab : a ≠ b) :
    GGIsReflection p (ggKGTl_EHom hS Θ hΘ hker (Equiv.swap a b)) := by
  refine ⟨?_, ggKGTl_E_swap_fix_card hp hp2 hpd hd hS Θ hΘ hker hab⟩
  rw [sq, ← map_mul, Equiv.swap_mul_self, map_one]

private theorem ggKGTl_classify {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ d) (hd : 4 ≤ d)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))} (hS : S = ⊤ ∨ S = sumZero d p)
    (Θ : ↥S →* ↥A) (hΘ : Function.Surjective Θ)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod p),
      (f : Fin d → Multiplicative (ZMod p)) = fun _ => c)
    (hperm : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ∃ π : Equiv.Perm (Fin d), ∀ f g : ↥S,
        (g : Fin d → Multiplicative (ZMod p)) = permAut π (f : Fin d → Multiplicative (ZMod p)) →
          ggConjAut A hn (Θ f) = Θ g)
    {φ : MulAut ↥A} (hφmem : φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (hφrefl : GGIsReflection p φ) :
    ∃ i j : Fin d, i ≠ j ∧ φ = ggKGTl_EHom hS Θ hΘ hker (Equiv.swap i j) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite ↥A := Finite.of_surjective Θ hΘ
  obtain ⟨g, hgH, hgnorm, hgapply⟩ := mem_ggAutomizer_iff.mp hφmem
  obtain ⟨n, rfl⟩ := hgH
  have hφeq : φ = ggConjAut A hgnorm := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_apply]
    exact hgapply b
  obtain ⟨π, hπ⟩ := hperm n hgnorm
  have hE : φ = ggKGTl_EHom hS Θ hΘ hker π := by
    refine MulEquiv.ext fun b => ?_
    obtain ⟨f, rfl⟩ := hΘ b
    have hg_eq : (ggKGTl_PS hS π f : Fin d → Multiplicative (ZMod p)) = permAut π
        (f : Fin d → Multiplicative (ZMod p)) := by
      rw [ggKGTl_PS_apply, ggKGTl_permS_apply]
    rw [hφeq, hπ f (ggKGTl_PS hS π f) hg_eq, ggKGTl_EHom_apply, ggKGTl_E_apply]
  have hswap : π.IsSwap :=
    isSwap_of_ggIsReflection hp2 (ggKGTl_Aelem hS Θ hΘ) (ggKGTl_EHom hS Θ hΘ hker)
      (ggKGTl_E_injective hp hp2 hd hS Θ hΘ hker)
      (fun a b hab => ggKGTl_E_swap_refl hp hp2 hpd hd hS Θ hΘ hker hab)
      (by rw [← hE]; exact hφrefl)
  obtain ⟨i, j, hij, rfl⟩ := hswap
  exact ⟨i, j, hij, hE⟩

theorem ggKGTl_classify_apply {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ d) (hd : 4 ≤ d)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))} (hS : S = ⊤ ∨ S = sumZero d p)
    (Θ : ↥S →* ↥A) (hΘ : Function.Surjective Θ)
    (hker : ∀ f : ↥S, Θ f = 1 ↔ ∃ c : Multiplicative (ZMod p),
      (f : Fin d → Multiplicative (ZMod p)) = fun _ => c)
    (hperm : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ∃ π : Equiv.Perm (Fin d), ∀ f g : ↥S,
        (g : Fin d → Multiplicative (ZMod p)) = permAut π (f : Fin d → Multiplicative (ZMod p)) →
          ggConjAut A hn (Θ f) = Θ g)
    {φ : MulAut ↥A} (hφmem : φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (hφrefl : GGIsReflection p φ) :
    ∃ i j : Fin d, i ≠ j ∧ ∀ f g : ↥S,
      (g : Fin d → Multiplicative (ZMod p)) =
        permAut (Equiv.swap i j) (f : Fin d → Multiplicative (ZMod p)) → φ (Θ f) = Θ g := by
  obtain ⟨i, j, hij, hφ⟩ := ggKGTl_classify hp hp2 hpd hd hS Θ hΘ hker hperm hφmem hφrefl
  refine ⟨i, j, hij, fun f g hg => ?_⟩
  have hgPS : g = ggKGTl_PS hS (Equiv.swap i j) f := by
    apply Subtype.ext
    rw [ggKGTl_PS_apply, ggKGTl_permS_apply]
    exact hg
  rw [hφ, ggKGTl_EHom_apply, ggKGTl_E_apply, hgPS]

private noncomputable def ggKGTl_piTop {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (Θ : ↥(⊤ : Subgroup (Fin d → Multiplicative (ZMod p))) →* ↥A) :
    (Fin d → ℤ) →+ Additive ↥A where
  toFun y := Additive.ofMul (Θ ⟨ggKGTl_red p y, Subgroup.mem_top _⟩)
  map_zero' := by
    show Additive.ofMul (Θ ⟨ggKGTl_red p (0 : Fin d → ℤ), Subgroup.mem_top _⟩) = 0
    rw [show (⟨ggKGTl_red p (0 : Fin d → ℤ), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup (Fin d → Multiplicative (ZMod p)))) = 1 from
      Subtype.ext ggKGTl_red_zero, map_one, ofMul_one]
  map_add' y z := by
    show Additive.ofMul (Θ ⟨ggKGTl_red p (y + z), Subgroup.mem_top _⟩) =
      Additive.ofMul (Θ ⟨ggKGTl_red p y, Subgroup.mem_top _⟩) +
        Additive.ofMul (Θ ⟨ggKGTl_red p z, Subgroup.mem_top _⟩)
    rw [show (⟨ggKGTl_red p (y + z), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup (Fin d → Multiplicative (ZMod p)))) =
        ⟨ggKGTl_red p y, Subgroup.mem_top _⟩ * ⟨ggKGTl_red p z, Subgroup.mem_top _⟩ from
      Subtype.ext (ggKGTl_red_add y z), map_mul, ofMul_mul]

private theorem ggKGTl_piTop_surjective {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (hp : p.Prime) (Θ : ↥(⊤ : Subgroup (Fin d → Multiplicative (ZMod p))) →* ↥A)
    (hΘ : Function.Surjective Θ) : Function.Surjective (ggKGTl_piTop (p := p) Θ) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro a
  obtain ⟨f, hf⟩ := hΘ (Additive.toMul a)
  refine ⟨fun i => ((toAdd ((f : Fin d → Multiplicative (ZMod p)) i)).val : ℤ), ?_⟩
  have hy : ggKGTl_red p (fun i => ((toAdd ((f : Fin d → Multiplicative (ZMod p)) i)).val : ℤ)) =
      (f : Fin d → Multiplicative (ZMod p)) := by
    funext i
    apply toAdd.injective
    rw [ggKGTl_red, toAdd_ofAdd, Int.cast_natCast]
    exact ZMod.natCast_zmod_val _
  change Additive.ofMul (Θ ⟨ggKGTl_red p _, Subgroup.mem_top _⟩) = a
  rw [hy, show (⟨(f : Fin d → Multiplicative (ZMod p)), Subgroup.mem_top _⟩ :
      ↥(⊤ : Subgroup (Fin d → Multiplicative (ZMod p)))) = f from Subtype.ext rfl, hf]
  rfl

private theorem ggKGTl_latForm_one (d : ℕ) :
    GGLatForm (1 : Matrix (Fin d) (Fin d) ℤ) := by
  refine ⟨Matrix.transpose_one, fun y hy => ?_⟩
  rw [Matrix.one_mulVec]
  have hnn : 0 ≤ dotProduct y y := by
    rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (y i)
  have hne : dotProduct y y ≠ 0 := fun h => hy (dotProduct_self_eq_zero.mp h)
  exact lt_of_le_of_ne hnn hne.symm

private def ggKGTl_w {d : ℕ} (i j : Fin d) : Fin d → ℤ :=
  Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ)

private theorem ggKGTl_dot_y_w {d : ℕ} (i j : Fin d) (y : Fin d → ℤ) :
    dotProduct y (ggKGTl_w i j) = y i - y j := by
  simp only [ggKGTl_w, dotProduct_sub, dotProduct_single, mul_one]

private theorem ggKGTl_dot_w_w {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    dotProduct (ggKGTl_w i j) (ggKGTl_w i j) = 2 := by
  simp only [ggKGTl_w, sub_dotProduct, dotProduct_sub, single_dotProduct, Pi.single_apply,
    if_true, if_neg hij, if_neg (Ne.symm hij)]
  norm_num

private theorem ggKGTl_cartan {d : ℕ} {i j : Fin d} (hij : i ≠ j) (y : Fin d → ℤ) :
    ggLatCartan (1 : Matrix (Fin d) (Fin d) ℤ) y (ggKGTl_w i j) = y i - y j := by
  rw [ggLatCartan, Matrix.one_mulVec, ggKGTl_dot_y_w, ggKGTl_dot_w_w hij,
    Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]

private theorem ggKGTl_refl {d : ℕ} {i j : Fin d} (hij : i ≠ j) (y : Fin d → ℤ) :
    ggLatRefl (1 : Matrix (Fin d) (Fin d) ℤ) (ggKGTl_w i j) y =
      fun k => y (Equiv.swap i j k) := by
  funext k
  rw [ggLatRefl, ggKGTl_cartan hij]
  simp only [ggKGTl_w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hki : k = i
  · subst hki
    simp [Pi.single_eq_same, Pi.single_eq_of_ne, hij, Ne.symm hij, Equiv.swap_apply_left]
  · by_cases hkj : k = j
    · subst hkj
      simp [Pi.single_eq_same, Pi.single_eq_of_ne, hij, Ne.symm hij, Equiv.swap_apply_right]
    · simp [Pi.single_eq_of_ne, hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

private theorem ggKGTl_root {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    GGLatRoot (1 : Matrix (Fin d) (Fin d) ℤ) (ggKGTl_w i j) := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : ggKGTl_w i j i = 1 := by simp [ggKGTl_w, hij]
    have h2 : ggKGTl_w i j i = 0 := by rw [h]; rfl
    rw [h1] at h2
    exact one_ne_zero h2
  · intro y
    rw [Matrix.one_mulVec, ggKGTl_dot_w_w hij]
    exact dvd_mul_right 2 _

private def ggKGTl_gamma {m : ℕ} (c : Fin (m + 1)) : Fin m → ℤ :=
  if h : c.val < m then Pi.single ⟨c.val, h⟩ 1 else 0

private def ggKGTl_emb {m : ℕ} (y : Fin m → ℤ) : Fin (m + 1) → ℤ :=
  Fin.lastCases (-∑ k, y k) y

private theorem ggKGTl_emb_castSucc {m : ℕ} (y : Fin m → ℤ) (k : Fin m) :
    ggKGTl_emb y (Fin.castSucc k) = y k :=
  Fin.lastCases_castSucc k

private theorem ggKGTl_emb_last {m : ℕ} (y : Fin m → ℤ) :
    ggKGTl_emb y (Fin.last m) = -∑ k, y k :=
  Fin.lastCases_last

private theorem ggKGTl_emb_add {m : ℕ} (y z : Fin m → ℤ) :
    ggKGTl_emb (y + z) = ggKGTl_emb y + ggKGTl_emb z := by
  funext i
  induction i using Fin.lastCases with
  | last => simp only [ggKGTl_emb_last, Pi.add_apply, Finset.sum_add_distrib, neg_add]
  | cast k => simp only [ggKGTl_emb_castSucc, Pi.add_apply]

private theorem ggKGTl_emb_zero {m : ℕ} :
    ggKGTl_emb (0 : Fin m → ℤ) = 0 := by
  funext i
  induction i using Fin.lastCases with
  | last => simp only [ggKGTl_emb_last, Finset.sum_const_zero, neg_zero, Pi.zero_apply]
  | cast k => simp only [ggKGTl_emb_castSucc, Pi.zero_apply]

private def ggKGTl_embHom {m : ℕ} : (Fin m → ℤ) →+ (Fin (m + 1) → ℤ) where
  toFun := ggKGTl_emb
  map_zero' := ggKGTl_emb_zero
  map_add' := ggKGTl_emb_add

private theorem ggKGTl_emb_sum_zero {m : ℕ} (y : Fin m → ℤ) :
    ∑ i, ggKGTl_emb y i = 0 := by
  rw [Fin.sum_univ_castSucc]
  rw [show (∑ k : Fin m, ggKGTl_emb y (Fin.castSucc k)) = ∑ k, y k from
    Finset.sum_congr rfl fun k _ => ggKGTl_emb_castSucc y k]
  rw [ggKGTl_emb_last, add_neg_cancel]

private def ggKGTl_Q {m : ℕ} : Matrix (Fin m) (Fin m) ℤ :=
  fun i j => if i = j then 2 else 1

private theorem ggKGTl_gamma_castSucc {m : ℕ} (k : Fin m) :
    ggKGTl_gamma (Fin.castSucc k) = Pi.single k 1 := by
  rw [ggKGTl_gamma]
  rw [dif_pos (show (Fin.castSucc k).val < m from k.isLt)]
  rfl

private theorem ggKGTl_emb_single {m : ℕ} (k : Fin m) :
    ggKGTl_emb (Pi.single k 1) =
      Pi.single (Fin.castSucc k) 1 - Pi.single (Fin.last m) 1 := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    rw [ggKGTl_emb_last]
    simp only [Pi.sub_apply, Pi.single_apply]
    rw [if_neg (Ne.symm (Fin.castSucc_ne_last k))]
    simp [Finset.sum_ite_eq']
  | cast j =>
    rw [ggKGTl_emb_castSucc]
    simp only [Pi.sub_apply, Pi.single_apply, Pi.single_eq_of_ne (Fin.castSucc_ne_last j),
      sub_zero]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [hjk, fun h => hjk (Fin.castSucc_injective _ h)]

private theorem ggKGTl_emb_gamma {m : ℕ} (c : Fin (m + 1)) :
    ggKGTl_emb (ggKGTl_gamma c) = Pi.single c 1 - Pi.single (Fin.last m) 1 := by
  rcases Fin.eq_castSucc_or_eq_last c with ⟨k, rfl⟩ | rfl
  · rw [ggKGTl_gamma_castSucc, ggKGTl_emb_single]
  · rw [ggKGTl_gamma, dif_neg (by simp)]
    funext i
    induction i using Fin.lastCases with
    | last => simp [ggKGTl_emb]
    | cast j => simp [ggKGTl_emb, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]

private theorem ggKGTl_emb_gamma_sub {m : ℕ} (a b : Fin (m + 1)) :
    ggKGTl_emb (ggKGTl_gamma a - ggKGTl_gamma b) =
      Pi.single a 1 - Pi.single b 1 := by
  change ggKGTl_embHom (ggKGTl_gamma a - ggKGTl_gamma b) =
    Pi.single a 1 - Pi.single b 1
  rw [map_sub]
  change ggKGTl_emb (ggKGTl_gamma a) - ggKGTl_emb (ggKGTl_gamma b) =
    Pi.single a 1 - Pi.single b 1
  rw [ggKGTl_emb_gamma, ggKGTl_emb_gamma]
  abel

private theorem ggKGTl_Q_mulVec {m : ℕ} (z : Fin m → ℤ) (k : Fin m) :
    (ggKGTl_Q.mulVec z) k = z k + ∑ j, z j := by
  show dotProduct (fun j => ggKGTl_Q k j) z = z k + ∑ j, z j
  rw [dotProduct]
  have hsplit : (∑ j, ggKGTl_Q k j * z j) = (∑ j, z j) + z k := by
    rw [show (∑ j, ggKGTl_Q k j * z j) = ∑ j, (z j + (if j = k then 1 else 0) * z j) from by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ggKGTl_Q]
      by_cases hjk : k = j
      · subst hjk; simp; ring
      · rw [if_neg hjk, if_neg (Ne.symm hjk)]; ring]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [show (∑ j, (if j = k then (1 : ℤ) else 0) * z j) = ∑ j, (if j = k then z j else 0) from by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : j = k <;> simp [h]]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ k)]
  rw [hsplit]; ring

private theorem ggKGTl_gram {m : ℕ} (y z : Fin m → ℤ) :
    dotProduct (ggKGTl_emb y) (ggKGTl_emb z) = dotProduct y (ggKGTl_Q.mulVec z) := by
  have hL : dotProduct (ggKGTl_emb y) (ggKGTl_emb z) =
      (∑ k, y k * z k) + (∑ k, y k) * (∑ k, z k) := by
    rw [dotProduct, Fin.sum_univ_castSucc]
    rw [show (∑ k : Fin m, ggKGTl_emb y (Fin.castSucc k) * ggKGTl_emb z (Fin.castSucc k)) =
        ∑ k, y k * z k from
      Finset.sum_congr rfl fun k _ => by rw [ggKGTl_emb_castSucc, ggKGTl_emb_castSucc]]
    rw [ggKGTl_emb_last, ggKGTl_emb_last, neg_mul_neg]
  have hR : dotProduct y (ggKGTl_Q.mulVec z) =
      (∑ k, y k * z k) + (∑ k, z k) * (∑ k, y k) := by
    rw [dotProduct]
    rw [show (∑ k, y k * (ggKGTl_Q.mulVec z) k) = ∑ k, y k * (z k + ∑ j, z j) from
      Finset.sum_congr rfl fun k _ => by rw [ggKGTl_Q_mulVec]]
    rw [show (∑ k, y k * (z k + ∑ j, z j)) =
        ∑ k, (y k * z k + y k * (∑ j, z j)) from
      Finset.sum_congr rfl fun k _ => by rw [mul_add]]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, mul_comm]
  rw [hL, hR, mul_comm (∑ k, z k) (∑ k, y k)]

private theorem ggKGTl_Q_form (m : ℕ) : GGLatForm (ggKGTl_Q (m := m)) := by
  refine ⟨?_, fun y hy => ?_⟩
  · ext i j
    rw [Matrix.transpose_apply, ggKGTl_Q, ggKGTl_Q]
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  · rw [← ggKGTl_gram y y]
    have hemb : ggKGTl_emb y ≠ 0 := by
      intro h
      apply hy
      funext k
      have := congrFun h (Fin.castSucc k)
      rwa [ggKGTl_emb_castSucc, Pi.zero_apply] at this
    have hnn : 0 ≤ dotProduct (ggKGTl_emb y) (ggKGTl_emb y) := by
      rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hne : dotProduct (ggKGTl_emb y) (ggKGTl_emb y) ≠ 0 :=
      fun h => hemb (dotProduct_self_eq_zero.mp h)
    exact lt_of_le_of_ne hnn hne.symm

private noncomputable def ggKGTl_toV {p m : ℕ} (y : Fin m → ℤ) :
    ↥(sumZero (m + 1) p) :=
  ⟨ggKGTl_red p (ggKGTl_emb y), by
    rw [mem_sumZero]
    rw [show (∑ i, toAdd (ggKGTl_red p (ggKGTl_emb y) i)) =
        ∑ i, ((ggKGTl_emb y i : ℤ) : ZMod p) from
      Finset.sum_congr rfl fun i _ => by rw [ggKGTl_red, toAdd_ofAdd]]
    rw [← Int.cast_sum, ggKGTl_emb_sum_zero, Int.cast_zero]⟩

private noncomputable def ggKGTl_piInn {p m : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (Θ : ↥(sumZero (m + 1) p) →* ↥A) : (Fin m → ℤ) →+ Additive ↥A where
  toFun y := Additive.ofMul (Θ (ggKGTl_toV y))
  map_zero' := by
    have h1 : ggKGTl_toV (p := p) (0 : Fin m → ℤ) = 1 := by
      apply Subtype.ext
      show ggKGTl_red p (ggKGTl_emb 0) = 1
      rw [ggKGTl_emb_zero, ggKGTl_red_zero]
    change Additive.ofMul (Θ (ggKGTl_toV (p := p) 0)) = 0
    exact (congrArg (fun t : ↥(sumZero (m + 1) p) => Additive.ofMul (Θ t)) h1).trans
      (by rw [map_one, ofMul_one])
  map_add' y z := by
    have h1 : ggKGTl_toV (p := p) (y + z) = ggKGTl_toV (p := p) y * ggKGTl_toV (p := p) z := by
      apply Subtype.ext
      show ggKGTl_red p (ggKGTl_emb (y + z)) =
        ggKGTl_red p (ggKGTl_emb y) * ggKGTl_red p (ggKGTl_emb z)
      rw [ggKGTl_emb_add, ggKGTl_red_add]
    change Additive.ofMul (Θ (ggKGTl_toV (p := p) (y + z))) =
      Additive.ofMul (Θ (ggKGTl_toV (p := p) y)) +
        Additive.ofMul (Θ (ggKGTl_toV (p := p) z))
    exact (congrArg (fun t : ↥(sumZero (m + 1) p) => Additive.ofMul (Θ t)) h1).trans
      (by rw [map_mul, ofMul_mul])

private theorem ggKGTl_piInn_surjective {p m : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (hp : p.Prime) (Θ : ↥(sumZero (m + 1) p) →* ↥A) (hΘ : Function.Surjective Θ) :
    Function.Surjective (ggKGTl_piInn (p := p) Θ) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro a
  obtain ⟨f, hf⟩ := hΘ (Additive.toMul a)
  let y0 : Fin m → ℤ :=
    fun k => ((toAdd ((f : Fin (m + 1) → Multiplicative (ZMod p)) (Fin.castSucc k))).val : ℤ)
  refine ⟨y0, ?_⟩
  have hy : ggKGTl_red p (ggKGTl_emb y0) = (f : Fin (m + 1) → Multiplicative (ZMod p)) := by
    funext i
    induction i using Fin.lastCases with
    | cast k =>
      simp only [y0, ggKGTl_red]
      rw [ggKGTl_emb_castSucc, Int.cast_natCast, ZMod.natCast_zmod_val, ofAdd_toAdd]
    | last =>
      simp only [y0, ggKGTl_red]
      rw [ggKGTl_emb_last]
      have hsum : (((∑ k, ((toAdd ((f : Fin (m + 1) → Multiplicative (ZMod p))
          (Fin.castSucc k))).val : ℤ)) : ℤ) : ZMod p) =
          ∑ k, crd f (Fin.castSucc k) := by
        rw [Int.cast_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Int.cast_natCast, ZMod.natCast_zmod_val, crd]
      rw [Int.cast_neg, hsum]
      have hlast : crd f (Fin.last m) = -∑ k, crd f (Fin.castSucc k) := by
        have h := sum_crd f
        rw [Fin.sum_univ_castSucc] at h
        have h2 : crd f (Fin.last m) + ∑ k, crd f (Fin.castSucc k) = 0 := by
          rw [add_comm]; exact h
        exact eq_neg_of_add_eq_zero_left h2
      rw [← hlast, crd]
      rfl
  have hx : ggKGTl_toV (p := p) y0 = f := by
    apply Subtype.ext
    exact hy
  change Additive.ofMul (Θ (ggKGTl_toV (p := p) y0)) = a
  exact (congrArg (fun t : ↥(sumZero (m + 1) p) => Additive.ofMul (Θ t)) hx).trans
    (by rw [hf]; rfl)

private theorem ggKGTl_Q_root {m : ℕ} {a b : Fin (m + 1)} (hab : a ≠ b) :
    GGLatRoot ggKGTl_Q (ggKGTl_gamma a - ggKGTl_gamma b) := by
  have hw : ggKGTl_emb (ggKGTl_gamma a - ggKGTl_gamma b) = ggKGTl_w a b := by
    rw [ggKGTl_emb_gamma_sub]; rfl
  have hdot : dotProduct (ggKGTl_gamma a - ggKGTl_gamma b)
      (ggKGTl_Q.mulVec (ggKGTl_gamma a - ggKGTl_gamma b)) = 2 := by
    rw [← ggKGTl_gram, hw]
    exact ggKGTl_dot_w_w hab
  refine ⟨?_, ?_⟩
  · intro h
    have h0 : ggKGTl_emb (ggKGTl_gamma a - ggKGTl_gamma b) = 0 := by rw [h, ggKGTl_emb_zero]
    rw [hw] at h0
    have h1 : ggKGTl_w a b a = 1 := by simp [ggKGTl_w, hab]
    rw [h0] at h1
    simp at h1
  · intro y
    rw [hdot]
    exact dvd_mul_right 2 _

private theorem ggKGTl_Q_refl {m : ℕ} {a b : Fin (m + 1)} (hab : a ≠ b) (y : Fin m → ℤ) :
    ggKGTl_emb (ggLatRefl ggKGTl_Q (ggKGTl_gamma a - ggKGTl_gamma b) y) =
      fun k => ggKGTl_emb y (Equiv.swap a b k) := by
  have hw : ggKGTl_emb (ggKGTl_gamma a - ggKGTl_gamma b) = ggKGTl_w a b := by
    rw [ggKGTl_emb_gamma_sub]; rfl
  have hdot : dotProduct (ggKGTl_gamma a - ggKGTl_gamma b)
      (ggKGTl_Q.mulVec (ggKGTl_gamma a - ggKGTl_gamma b)) = 2 := by
    rw [← ggKGTl_gram, hw]
    exact ggKGTl_dot_w_w hab
  have hcartan : ggLatCartan ggKGTl_Q y (ggKGTl_gamma a - ggKGTl_gamma b) =
      dotProduct (ggKGTl_emb y) (ggKGTl_w a b) := by
    rw [ggLatCartan, ← ggKGTl_gram y (ggKGTl_gamma a - ggKGTl_gamma b), hdot, hw,
      Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  calc ggKGTl_emb (ggLatRefl ggKGTl_Q (ggKGTl_gamma a - ggKGTl_gamma b) y)
      = ggKGTl_emb y - ggLatCartan ggKGTl_Q y (ggKGTl_gamma a - ggKGTl_gamma b) •
          ggKGTl_emb (ggKGTl_gamma a - ggKGTl_gamma b) := by
        rw [ggLatRefl]
        change ggKGTl_embHom (y - ggLatCartan ggKGTl_Q y
            (ggKGTl_gamma a - ggKGTl_gamma b) • (ggKGTl_gamma a - ggKGTl_gamma b)) =
          ggKGTl_emb y - ggLatCartan ggKGTl_Q y (ggKGTl_gamma a - ggKGTl_gamma b) •
            ggKGTl_emb (ggKGTl_gamma a - ggKGTl_gamma b)
        rw [map_sub, map_zsmul]
        rfl
    _ = ggKGTl_emb y - dotProduct (ggKGTl_emb y) (ggKGTl_w a b) • ggKGTl_w a b := by
        rw [hcartan, hw]
    _ = ggLatRefl (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (ggKGTl_w a b) (ggKGTl_emb y) := by
        rw [ggLatRefl, ggKGTl_cartan hab, ggKGTl_dot_y_w]
    _ = fun k => ggKGTl_emb y (Equiv.swap a b k) := ggKGTl_refl hab (ggKGTl_emb y)

theorem ggKGTAD_lattice {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ d) (hd : 5 ≤ d)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {S : Subgroup (Fin d → Multiplicative (ZMod p))} (hS : S = ⊤ ∨ S = sumZero d p)
    (Θ : ↥S →* ↥A) (hΘ : Function.Surjective Θ)
    (hker : ∀ f : ↥S, Θ f = 1 ↔
      ∃ c : Multiplicative (ZMod p), (f : Fin d → Multiplicative (ZMod p)) = fun _ => c)
    (hperm : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ∃ π : Equiv.Perm (Fin d), ∀ f g : ↥S,
        (g : Fin d → Multiplicative (ZMod p)) = permAut π (f : Fin d → Multiplicative (ZMod p)) →
          ggConjAut A hn (Θ f) = Θ g) :
    ∃ (m : ℕ) (Q : Matrix (Fin m) (Fin m) ℤ) (π : (Fin m → ℤ) →+ Additive ↥A),
      GGLatForm Q ∧ Function.Surjective π ∧
      ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, GGIsReflection p φ →
        ∃ w : Fin m → ℤ, GGLatRoot Q w ∧
          ∀ y : Fin m → ℤ, φ (Additive.toMul (π y)) = Additive.toMul (π (ggLatRefl Q w y)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite ↥A := Finite.of_surjective Θ hΘ
  rcases hS with h | h
  · subst h
    refine ⟨d, 1, ggKGTl_piTop Θ, ggKGTl_latForm_one d,
      ggKGTl_piTop_surjective hp Θ hΘ, ?_⟩
    intro φ hφmem hφrefl
    obtain ⟨i, j, hij, hφij⟩ :=
      ggKGTl_classify hp hp2 hpd (by omega) (Or.inl rfl) Θ hΘ hker hperm hφmem hφrefl
    refine ⟨ggKGTl_w i j, ggKGTl_root hij, fun y => ?_⟩
    have harg : ggKGTl_PS (Or.inl rfl) (Equiv.swap i j)
        ⟨ggKGTl_red p y, Subgroup.mem_top _⟩ =
        ⟨ggKGTl_red p (ggLatRefl (1 : Matrix (Fin d) (Fin d) ℤ) (ggKGTl_w i j) y),
          Subgroup.mem_top _⟩ := by
      apply Subtype.ext
      rw [ggKGTl_PS_apply, ggKGTl_permS_apply, ggKGTl_refl hij y, ggKGTl_red_swap]
    change φ (Θ ((⟨ggKGTl_red p y, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup
        (Fin d → Multiplicative (ZMod p)))))) =
      Θ ((⟨ggKGTl_red p (ggLatRefl (1 : Matrix (Fin d) (Fin d) ℤ) (ggKGTl_w i j) y),
        Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (Fin d → Multiplicative (ZMod p)))))
    rw [hφij, ggKGTl_EHom_apply, ggKGTl_E_apply, harg]
  · subst h
    obtain ⟨m, hm⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    subst hm
    refine ⟨m, ggKGTl_Q (m := m), ggKGTl_piInn (p := p) Θ, ggKGTl_Q_form m,
      ggKGTl_piInn_surjective hp Θ hΘ, ?_⟩
    intro φ hφmem hφrefl
    obtain ⟨i, j, hij, hφij⟩ :=
      ggKGTl_classify hp hp2 hpd (by omega) (Or.inr rfl) Θ hΘ hker hperm hφmem hφrefl
    refine ⟨ggKGTl_gamma i - ggKGTl_gamma j, ggKGTl_Q_root hij, fun y => ?_⟩
    have harg : ggKGTl_PS (Or.inr rfl) (Equiv.swap i j) (ggKGTl_toV (p := p) y) =
        ggKGTl_toV (p := p) (ggLatRefl (ggKGTl_Q (m := m))
          (ggKGTl_gamma i - ggKGTl_gamma j) y) := by
      apply Subtype.ext
      rw [ggKGTl_PS_apply, ggKGTl_permS_apply]
      change permAut (Equiv.swap i j) (ggKGTl_red p (ggKGTl_emb y)) =
        ggKGTl_red p (ggKGTl_emb (ggLatRefl (ggKGTl_Q (m := m))
          (ggKGTl_gamma i - ggKGTl_gamma j) y))
      rw [← ggKGTl_red_swap i j (ggKGTl_emb y), ggKGTl_Q_refl hij y]
    change φ (Θ (ggKGTl_toV (p := p) y)) =
      Θ (ggKGTl_toV (p := p) (ggLatRefl (ggKGTl_Q (m := m))
        (ggKGTl_gamma i - ggKGTl_gamma j) y))
    rw [hφij, ggKGTl_EHom_apply, ggKGTl_E_apply, harg]

end CFSG.StandardType
