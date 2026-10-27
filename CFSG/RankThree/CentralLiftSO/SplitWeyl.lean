module

public import CFSG.RankThree.CentralLiftSO.SplitLift
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryWeylLift
public import CFSG.LieType.Universal.Spin.Roots.TypeD
public import CFSG.LieType.Chevalley.RankOneGaussian
import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylQuotient

public section

namespace CFSG.RankThree.CentralLiftSO.SplitO

open Matrix CFSG.LieType.CentralExt CFSG.LieType.Universal.Spin CFSG.RankThree.CentralLift
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LocalAnalysis.ComponentInitial (orthElementaryGroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2Diag sl2W sl2ConjDiag
  coe_sl2Diag coe_sl2W coe_sl2W_inv coe_sl2ConjDiag sl2W_mul_sl2W conj_comp_eq signedPermGroup)
open CFSG.LieType.Universal.SpecialLinear (signedPerm)
open CFSG.LieType.Chevalley (uSL vSL coe_uSL coe_vSL)

section Matrices

variable {r : ℕ} {k : Type} [Field k]

theorem autMat_etaLin {a b : Fin r ⊕ Fin r} (h : coordIdx a ≠ coordIdx b)
    (g : SpecialLinearGroup (Fin 2) k) : autMat (etaLin h g) = etaMat a b g := by
  ext x y
  rw [autMat_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, etaLin_apply]
  simp [Matrix.mulVec_single]

theorem mul_etaLin_of_autMat {y : (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)}
    {σ : Equiv.Perm (Fin r ⊕ Fin r)} (hσ : σ ∈ signedPermGroup r) {μ : Fin r ⊕ Fin r → k}
    (hy : autMat y = signedPerm σ μ) {a b a' b' : Fin r ⊕ Fin r} (h : coordIdx a ≠ coordIdx b)
    (h' : coordIdx a' ≠ coordIdx b') (ha : σ a = a') (hb : σ b = b') (hμa : μ a ≠ 0)
    (hμa' : μ a.swap * μ a = 1) (hμb' : μ b.swap * μ b = 1) {u : kˣ} (hu : μ a * u = μ b)
    (g : SpecialLinearGroup (Fin 2) k) :
    y * etaLin h g = etaLin h' (sl2ConjDiag u g) * y := by
  apply autMat_injective
  rw [map_mul, map_mul, hy, autMat_etaLin, autMat_etaLin]
  have hu0 : (u : k) ≠ 0 := u.ne_zero
  have hμb : μ b = μ a * u := hu.symm
  have ha'' : μ a.swap = (μ a)⁻¹ := eq_inv_of_mul_eq_one_left hμa'
  have hb'' : μ b.swap = (μ b)⁻¹ := eq_inv_of_mul_eq_one_left hμb'
  refine signedPerm_mul_etaMat σ μ h ha hb (by rw [hσ a, ha]) (by rw [hσ b, hb]) ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ <;>
    simp only [coe_sl2ConjDiag, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, ha'', hb'', hμb, Units.val_inv_eq_inv_val] <;>
    field_simp

theorem sl2Swap_sl2W : sl2Swap (sl2W : SpecialLinearGroup (Fin 2) k) = sl2W⁻¹ := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_sl2Swap, coe_sl2W_inv, coe_sl2W]
  fin_cases i <;> fin_cases j <;> simp

theorem uSL_mul_vSL_mul_uSL :
    uSL (1 : k) * vSL (-1) * uSL 1 = (sl2W : SpecialLinearGroup (Fin 2) k)⁻¹ := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2W_inv,
    coe_uSL, coe_vSL]
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

theorem sl2ConjDiag_one (g : SpecialLinearGroup (Fin 2) k) : sl2ConjDiag 1 g = g := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_sl2ConjDiag]
  fin_cases i <;> fin_cases j <;> simp

@[expose] def wSign (d s : Fin r ⊕ Fin r) : k := if s = d ∨ s = d.swap then -1 else 1

theorem wSign_of_eq {d s : Fin r ⊕ Fin r} (h : s = d) : wSign (k := k) d s = -1 :=
  ite_eq_left (Or.inl h)

theorem wSign_of_ne {d s : Fin r ⊕ Fin r} (h1 : s ≠ d) (h2 : s ≠ d.swap) :
    wSign (k := k) d s = 1 :=
  ite_eq_right (by rintro (h | h) <;> contradiction)

theorem wSign_ne_zero (d s : Fin r ⊕ Fin r) : wSign (k := k) d s ≠ 0 := by
  unfold wSign
  split_ifs <;> simp

theorem wSign_swap_mul_self (d s : Fin r ⊕ Fin r) : wSign (k := k) d s.swap * wSign d s = 1 := by
  have hiff : (s.swap = d ∨ s.swap = d.swap) ↔ (s = d ∨ s = d.swap) := by
    constructor
    · rintro (h | h)
      · exact Or.inr (by rw [← h, Sum.swap_swap])
      · exact Or.inl (Sum.swap_leftInverse.injective h)
    · rintro (h | h)
      · exact Or.inr (by rw [h])
      · exact Or.inl (by rw [h, Sum.swap_swap])
  unfold wSign
  by_cases hs : s = d ∨ s = d.swap
  · rw [ite_eq_left (hiff.2 hs), ite_eq_left hs]
    norm_num
  · rw [ite_eq_right (fun h => hs (hiff.1 h)), ite_eq_right hs, one_mul]

theorem swap_mul_swap_apply_of_ne {a c d : Fin r ⊕ Fin r} (h1 : a ≠ c) (h2 : a ≠ d)
    (h3 : a ≠ c.swap) (h4 : a ≠ d.swap) :
    (Equiv.swap c d * Equiv.swap c.swap d.swap) a = a := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h3 h4,
    Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem etaMat_sl2W_eq {c d : Fin r ⊕ Fin r} (h : coordIdx c ≠ coordIdx d) :
    etaMat c d (sl2W : SpecialLinearGroup (Fin 2) k) =
      signedPerm (Equiv.swap c d * Equiv.swap c.swap d.swap) (wSign d) := by
  rw [etaMat_sl2W h]
  congr 1
  funext s
  have h1 : c ≠ d := ne_of_coordIdx_ne h
  have h3 : d ≠ c.swap := ne_swap_of_coordIdx_ne (Ne.symm h)
  have hsw : c.swap ≠ d.swap := swap_ne_swap_of_coordIdx_ne h
  by_cases hsd : s = d
  · subst hsd
    rw [Equiv.swap_apply_of_ne_of_ne h3 (swap_ne_self s).symm, wSign_of_eq rfl,
      ite_eq_left rfl, ite_eq_right (swap_ne_self s).symm, mul_one]
  by_cases hsd' : s = d.swap
  · subst hsd'
    rw [Equiv.swap_apply_right, ite_eq_right (Ne.symm h3), ite_eq_left rfl, one_mul,
      wSign, ite_eq_left (Or.inr rfl)]
  rw [wSign_of_ne hsd hsd', ite_eq_right hsd', mul_one]
  by_cases hsc : s = c.swap
  · subst hsc
    rw [Equiv.swap_apply_left, ite_eq_right (swap_ne_self d)]
  · rw [Equiv.swap_apply_of_ne_of_ne hsc hsd', ite_eq_right hsd]

end Matrices

variable {r : ℕ} {k : Type} [Field k] {E : Type*} [Group E]

section Defs

variable (π : E →* orthElementaryGroup (quadPlus r k))

@[expose] noncomputable def sLift (i : Fin r) : E := simpleLift π i sl2W

@[expose] noncomputable def liftWeyl : Subgroup E :=
  Subgroup.closure ((liftTorus π : Set E) ∪ Set.range (sLift π))

end Defs

variable {π : E →* orthElementaryGroup (quadPlus r k)}

theorem liftTorus_le_liftWeyl : liftTorus π ≤ liftWeyl π :=
  fun _ hx => Subgroup.subset_closure (Or.inl hx)

theorem sLift_mem (i : Fin r) : sLift π i ∈ liftWeyl π :=
  Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)

theorem sLift_of_lt {i : Fin r} (h : i.val + 1 < r) :
    sLift π i = sl2Lift π (eta (k := k) (coordIdx_inl_ne (ne_succ_of_lt h))) sl2W := by
  rw [sLift, simpleLift, dite_eq_left h]
  rfl

theorem sLift_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) (h' : 1 ≤ i.val) :
    sLift π i = sl2Lift π (eta (k := k) (coordIdx_inl_inr_ne (pred_ne_of_one_le h'))) sl2W := by
  rw [sLift, simpleLift, dite_eq_right h, dite_eq_left h', etaPlusLift, etaPlus_eq]

theorem sLift_mul_self (i : Fin r) : sLift π i * sLift π i = hSimple π i (-1) := by
  rw [sLift, ← map_mul, sl2W_mul_sl2W]
  rfl

theorem sLift_sq_mem (i : Fin r) : sLift π i ^ 2 ∈ liftTorus π := by
  rw [sq, sLift_mul_self]
  exact hSimple_mem i (-1)

theorem sl2Lift_eta_congr {a b a' b' : Fin r ⊕ Fin r} (ha : a = a') (hb : b = b')
    (h : coordIdx a ≠ coordIdx b) (h' : coordIdx a' ≠ coordIdx b')
    (g : SpecialLinearGroup (Fin 2) k) :
    sl2Lift π (eta h) g = sl2Lift π (eta h') g := by
  subst ha hb
  rfl

variable [Finite k] [Finite E]

section Conj

variable (hS : LargeHyp π)
include hS

theorem conj_sl2Lift_eta_of_autMat {x : E} {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    (hσ : σ ∈ signedPermGroup r) {μ : Fin r ⊕ Fin r → k}
    (hx : autMat ((π x : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) = signedPerm σ μ)
    {a b a' b' : Fin r ⊕ Fin r} (h : coordIdx a ≠ coordIdx b) (h' : coordIdx a' ≠ coordIdx b')
    (ha : σ a = a') (hb : σ b = b') (hμa : μ a ≠ 0) (hμa' : μ a.swap * μ a = 1)
    (hμb' : μ b.swap * μ b = 1) {u : kˣ} (hu : μ a * u = μ b) (g : SpecialLinearGroup (Fin 2) k) :
    x * sl2Lift π (eta h) g * x⁻¹ = sl2Lift π (eta h') (sl2ConjDiag u g) :=
  hS.conj_lift_apply (conj_comp_eq fun g => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, MonoidHom.comp_apply, coe_eta, coe_eta]
    exact mul_etaLin_of_autMat hσ hx h h' ha hb hμa hμa' hμb' hu g)) g

theorem conj_sl2Lift_eta_sl2W {c d : Fin r ⊕ Fin r} (h₀ : coordIdx c ≠ coordIdx d)
    {a b a' b' : Fin r ⊕ Fin r} (h : coordIdx a ≠ coordIdx b) (h' : coordIdx a' ≠ coordIdx b')
    (ha : (Equiv.swap c d * Equiv.swap c.swap d.swap) a = a')
    (hb : (Equiv.swap c d * Equiv.swap c.swap d.swap) b = b') {u : kˣ}
    (hu : wSign (k := k) d a * (u : k) = wSign d b) (g : SpecialLinearGroup (Fin 2) k) :
    sl2Lift π (eta h₀) sl2W * sl2Lift π (eta h) g * (sl2Lift π (eta h₀) sl2W)⁻¹ =
      sl2Lift π (eta h') (sl2ConjDiag u g) :=
  conj_sl2Lift_eta_of_autMat hS (swap_mul_swap_mem_signedPermGroup h₀)
    (by rw [hS.map_lift, coe_eta, autMat_etaLin, etaMat_sl2W_eq h₀]) h h' ha hb
    (wSign_ne_zero d a) (wSign_swap_mul_self d a) (wSign_swap_mul_self d b) hu g

theorem sl2Lift_eta_symm_sl2W {c d : Fin r ⊕ Fin r} (h₀ : coordIdx c ≠ coordIdx d) :
    sl2Lift π (eta (Ne.symm h₀)) sl2W = (sl2Lift π (eta h₀) sl2W)⁻¹ := by
  rw [eta_swap_args h₀, ← hS.lift_comp, MonoidHom.comp_apply, sl2Swap_sl2W, map_inv]

theorem commute_sl2Lift_eta_sl2W {c d : Fin r ⊕ Fin r} (h₀ : coordIdx c ≠ coordIdx d)
    {a b : Fin r ⊕ Fin r} (h : coordIdx a ≠ coordIdx b)
    (ha : (Equiv.swap c d * Equiv.swap c.swap d.swap) a = a)
    (hb : (Equiv.swap c d * Equiv.swap c.swap d.swap) b = b) (hwa : wSign (k := k) d a = 1)
    (hwb : wSign (k := k) d b = 1) (g : SpecialLinearGroup (Fin 2) k) :
    Commute (sl2Lift π (eta h₀) sl2W) (sl2Lift π (eta h) g) := by
  have h1 := conj_sl2Lift_eta_sl2W hS h₀ h h ha hb (u := 1) (by rw [hwa, hwb, Units.val_one,
    mul_one]) g
  rw [sl2ConjDiag_one] at h1
  exact mul_inv_eq_iff_eq_mul.1 h1

theorem braid_inl_inl {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    sl2Lift π (eta (k := k) (coordIdx_inl_ne hjl)) sl2W *
        sl2Lift π (eta (k := k) (coordIdx_inl_ne hij)) sl2W *
        sl2Lift π (eta (k := k) (coordIdx_inl_ne hjl)) sl2W =
      sl2Lift π (eta (k := k) (coordIdx_inl_ne hij)) sl2W *
        sl2Lift π (eta (k := k) (coordIdx_inl_ne hjl)) sl2W *
        sl2Lift π (eta (k := k) (coordIdx_inl_ne hij)) sl2W := by
  have hji : Sum.inl j ≠ (Sum.inl i : Fin r ⊕ Fin r) := fun h => hij (Sum.inl_injective h).symm
  have hlj : Sum.inl l ≠ (Sum.inl j : Fin r ⊕ Fin r) := fun h => hjl (Sum.inl_injective h).symm
  have hli : Sum.inl l ≠ (Sum.inl i : Fin r ⊕ Fin r) := fun h => hil (Sum.inl_injective h).symm
  have h1 := conj_sl2Lift_eta_sl2W hS (coordIdx_inl_ne hij) (a := Sum.inl j) (b := Sum.inl l)
    (coordIdx_inl_ne hjl) (coordIdx_inl_ne hil)
    (by simp [Equiv.swap_apply_of_ne_of_ne])
    (by simp [Equiv.swap_apply_of_ne_of_ne, hjl.symm, hil.symm])
    (u := -1) (by rw [wSign_of_eq rfl, wSign_of_ne hlj (by simp)]; simp) sl2W
  have h2 := conj_sl2Lift_eta_sl2W hS (coordIdx_inl_ne hjl.symm) (a := Sum.inl i)
    (b := Sum.inl j) (coordIdx_inl_ne hij) (coordIdx_inl_ne hil)
    (by simp [Equiv.swap_apply_def, hij, hil])
    (by simp [Equiv.swap_apply_def])
    (u := -1) (by rw [wSign_of_ne (Ne.symm hji) (by simp), wSign_of_eq rfl]; simp) sl2W
  rw [sl2Lift_eta_symm_sl2W hS (coordIdx_inl_ne hjl), inv_inv] at h2
  have h := h1.trans h2.symm
  have h' := congrArg (fun x => sl2Lift π (eta (k := k) (coordIdx_inl_ne hjl)) sl2W * x *
    sl2Lift π (eta (k := k) (coordIdx_inl_ne hij)) sl2W) h
  simp only [mul_assoc, inv_mul_cancel, mul_inv_cancel_left, mul_one] at h'
  simpa only [mul_assoc] using h'

theorem braid_inl_inr {a b c : Fin r} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sl2Lift π (eta (k := k) (coordIdx_inl_inr_ne hbc)) sl2W *
        sl2Lift π (eta (k := k) (coordIdx_inl_ne hab)) sl2W *
        sl2Lift π (eta (k := k) (coordIdx_inl_inr_ne hbc)) sl2W =
      sl2Lift π (eta (k := k) (coordIdx_inl_ne hab)) sl2W *
        sl2Lift π (eta (k := k) (coordIdx_inl_inr_ne hbc)) sl2W *
        sl2Lift π (eta (k := k) (coordIdx_inl_ne hab)) sl2W := by
  have hba : Sum.inl b ≠ (Sum.inl a : Fin r ⊕ Fin r) := fun h => hab (Sum.inl_injective h).symm
  have h1 := conj_sl2Lift_eta_sl2W hS (coordIdx_inl_ne hab) (a := Sum.inl b) (b := Sum.inr c)
    (coordIdx_inl_inr_ne hbc) (coordIdx_inl_inr_ne hac)
    (by simp [Equiv.swap_apply_def])
    (by simp [Equiv.swap_apply_def, hac.symm, hbc.symm])
    (u := -1) (by rw [wSign_of_eq rfl, wSign_of_ne (by simp) (by simp [hbc.symm])]; simp) sl2W
  have h2 := conj_sl2Lift_eta_sl2W hS (Ne.symm (coordIdx_inl_inr_ne hbc))
    (a := Sum.inl a) (b := Sum.inl b) (coordIdx_inl_ne hab) (coordIdx_inl_inr_ne hac)
    (by simp [Equiv.swap_apply_def, hab, hac])
    (by simp [Equiv.swap_apply_def, hbc])
    (u := -1) (by rw [wSign_of_ne hba.symm (by simp), wSign_of_eq rfl]; simp) sl2W
  rw [sl2Lift_eta_symm_sl2W hS (coordIdx_inl_inr_ne hbc), inv_inv] at h2
  have h := h1.trans h2.symm
  have h' := congrArg (fun x => sl2Lift π (eta (k := k) (coordIdx_inl_inr_ne hbc)) sl2W * x *
    sl2Lift π (eta (k := k) (coordIdx_inl_ne hab)) sl2W) h
  simp only [mul_assoc, inv_mul_cancel, mul_inv_cancel_left, mul_one] at h'
  simpa only [mul_assoc] using h'

end Conj

section Images

omit [Finite k] [Finite E] in
theorem weylElt_eq_etaLin_of_lt {i : Fin r} (h : i.val + 1 < r) :
    weylElt r k i =
      etaLin (coordIdx_inl_ne (ne_succ_of_lt h)) (sl2W⁻¹ : SpecialLinearGroup (Fin 2) k) := by
  have hlt : i < ⟨i.val + 1, h⟩ := Fin.lt_def.2 (by simp)
  have hneg : -(eps r i - eps r ⟨i.val + 1, h⟩) = -eps r i + eps r ⟨i.val + 1, h⟩ := by abel
  rw [← uSL_mul_vSL_mul_uSL, map_mul, map_mul, weylElt, simpleRoot, dite_eq_left h, hneg,
    rootElt_eps_sub_eps' hlt, rootElt_neg_eps_add_eps' hlt,
    etaLin_of_upper _ (coe_uSL 1), etaLin_of_lower _ (coe_vSL (-1))]
  rfl

omit [Finite k] [Finite E] in
theorem weylElt_eq_etaLin_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) (h' : 1 ≤ i.val) :
    weylElt r k i = etaLin (coordIdx_inl_inr_ne (pred_ne_of_one_le h'))
      (sl2W⁻¹ : SpecialLinearGroup (Fin 2) k) := by
  have hlt : (⟨r - 2, by omega⟩ : Fin r) < i := Fin.lt_def.2 (by simp; omega)
  have hp : (⟨i.val - 1, by omega⟩ : Fin r) = ⟨r - 2, by omega⟩ := Fin.ext (by simp; omega)
  have hneg : -(eps r ⟨r - 2, by omega⟩ + eps r i) = -eps r ⟨r - 2, by omega⟩ - eps r i := by
    abel
  rw [← uSL_mul_vSL_mul_uSL, map_mul, map_mul, weylElt, simpleRoot, dite_eq_right h, hneg,
    rootElt_eps_add_eps' hlt, rootElt_neg_eps_sub_eps' hlt,
    etaLin_of_upper _ (coe_uSL 1), etaLin_of_lower _ (coe_vSL (-1)), hp]
  rfl

variable (hS : LargeHyp π)
include hS

theorem coe_pi_sLift (hr : 2 ≤ r) (i : Fin r) :
    ((π (sLift π i) : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) = (weylElt r k i)⁻¹ := by
  by_cases h : i.val + 1 < r
  · rw [sLift_of_lt h, hS.map_lift, coe_eta, weylElt_eq_etaLin_of_lt h, map_inv, inv_inv]
  · rw [sLift_of_not_lt h (by omega), hS.map_lift, coe_eta,
      weylElt_eq_etaLin_of_not_lt h (by omega), map_inv, inv_inv]

theorem coe_pi_mem_torus {x : E} (hx : x ∈ liftTorus π) :
    ((π x : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ torus r k := by
  have hle : liftTorus π ≤
      (torus r k).comap ((orthElementaryGroup (quadPlus r k)).subtype.comp π) := by
    rw [liftTorus, Subgroup.closure_le]
    intro y hy
    obtain ⟨d, hd⟩ := exists_torusElt_of_mem_hGens hS hy
    exact ⟨(π y).2, d, hd.symm⟩
  exact hle hx

theorem coe_pi_mem_torusWeyl (hr : 2 ≤ r) {v : E} (hv : v ∈ liftWeyl π) :
    ((π v : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ torusWeyl r k := by
  have hle : liftWeyl π ≤
      (torusWeyl r k).comap ((orthElementaryGroup (quadPlus r k)).subtype.comp π) := by
    rw [liftWeyl, Subgroup.closure_le]
    rintro x (hx | ⟨i, rfl⟩)
    · exact torus_le_torusWeyl (coe_pi_mem_torus hS hx)
    · change ((π (sLift π i) : orthElementaryGroup (quadPlus r k)) :
        (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ torusWeyl r k
      rw [coe_pi_sLift hS hr]
      exact inv_mem (weylElt_mem_torusWeyl i)
  exact hle hv

end Images

section Normalizer

variable (hS : LargeHyp π)
include hS

theorem sl2Lift_eta_sl2Diag_mem {c d : Fin r ⊕ Fin r} (h : coordIdx c ≠ coordIdx d) (a : kˣ) :
    sl2Lift π (eta h) (sl2Diag a) ∈ liftTorus π := by
  rcases c with i | i <;> rcases d with j | j
  · exact hMinus_mem (π := π) (show i ≠ j from h) a
  · rw [← hPlus_eq_liftEta (show i ≠ j from h)]
    exact hPlus_mem _ a
  · have h'' : coordIdx (Sum.inl i : Fin r ⊕ Fin r) ≠ coordIdx (Sum.inr j) := h
    have e : eta (k := k) h = (eta h'').comp sl2InvT := eta_swap_swap h''
    rw [e, ← hS.lift_comp, MonoidHom.comp_apply, sl2InvT_sl2Diag,
      ← hPlus_eq_liftEta (show i ≠ j from h'')]
    exact hPlus_mem _ _
  · have h'' : coordIdx (Sum.inl i : Fin r ⊕ Fin r) ≠ coordIdx (Sum.inl j) := h
    have e : eta (k := k) h = (eta h'').comp sl2InvT := eta_swap_swap h''
    rw [e, ← hS.lift_comp, MonoidHom.comp_apply, sl2InvT_sl2Diag]
    exact hMinus_mem (π := π) (show i ≠ j from h'') a⁻¹

theorem conj_mem_liftTorus_of_mem_monoAut {x : E}
    (hx : ((π x : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ monoAut r k) {y : E}
    (hy : y ∈ liftTorus π) : x * y * x⁻¹ ∈ liftTorus π := by
  obtain ⟨μ, hμ, hmat⟩ := exists_autMat_eq_monoPermFun (⟨_, hx⟩ : monoAut r k)
  have hσ := monoPermFun_mem (⟨_, hx⟩ : monoAut r k)
  have key : ∀ {c d : Fin r ⊕ Fin r} (h : coordIdx c ≠ coordIdx d) (a : kˣ),
      x * sl2Lift π (eta h) (sl2Diag a) * x⁻¹ ∈ liftTorus π := by
    intro c d h a
    rw [conj_sl2Lift_eta_of_autMat hS hσ hmat h (coordIdx_ne_of_mem_signedPermGroup hσ h) rfl rfl
      (μ c).ne_zero (units_swap_mul_self hμ c) (units_swap_mul_self hμ d)
      (u := (μ c)⁻¹ * μ d) (by simp) (sl2Diag a), sl2ConjDiag_sl2Diag]
    exact sl2Lift_eta_sl2Diag_mem hS _ a
  have hle : liftTorus π ≤ (liftTorus π).comap (MulAut.conj x).toMonoidHom := by
    rw [liftTorus, Subgroup.closure_le]
    rintro z (⟨i, j, hij, a, rfl⟩ | ⟨i, j, hij, a, rfl⟩)
    · exact key _ a
    · rw [SetLike.mem_coe, Subgroup.mem_comap, hPlus_eq_liftEta]
      exact key _ a
  exact hle hy

theorem mem_normalizer_of_mem_monoAut {x : E}
    (hx : ((π x : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ monoAut r k) :
    x ∈ Subgroup.normalizer (liftTorus π : Set E) := by
  have hx' : ((π x⁻¹ : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) ∈ monoAut r k := by
    rw [map_inv, Subgroup.coe_inv]
    exact inv_mem hx
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · exact conj_mem_liftTorus_of_mem_monoAut hS hx
  · intro hy
    have := conj_mem_liftTorus_of_mem_monoAut hS hx' hy
    simpa [mul_assoc] using this

theorem liftWeyl_le_normalizer (hr : 2 ≤ r) :
    liftWeyl π ≤ Subgroup.normalizer (liftTorus π : Set E) :=
  fun _ hv => mem_normalizer_of_mem_monoAut hS
    (torusWeyl_le_monoAut hr (coe_pi_mem_torusWeyl hS hr hv))

theorem normal_liftTorus_subgroupOf (hr : 2 ≤ r) :
    ((liftTorus π).subgroupOf (liftWeyl π)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer liftTorus_le_liftWeyl).2
    (liftWeyl_le_normalizer hS hr)

end Normalizer

section WeylHom

variable (hS : LargeHyp π)
include hS

@[expose] noncomputable def piWeyl (hr : 2 ≤ r) : liftWeyl π →* torusWeyl r k :=
  ((orthElementaryGroup (quadPlus r k)).subtype.comp (π.comp (liftWeyl π).subtype)).codRestrict
    (torusWeyl r k) fun v => coe_pi_mem_torusWeyl hS hr v.2

theorem coe_piWeyl (hr : 2 ≤ r) (v : liftWeyl π) :
    ((piWeyl hS hr v : torusWeyl r k) : (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) =
      ((π v : orthElementaryGroup (quadPlus r k)) : (Fin r ⊕ Fin r → k) ≃ₗ[k] _) :=
  rfl

@[expose] noncomputable def weylHom (hr : 2 ≤ r) : liftWeyl π →* weylGroup r :=
  (torusWeylNu r k hr).comp (piWeyl hS hr)

theorem weylHom_apply (hr : 2 ≤ r) (v : liftWeyl π) :
    weylHom hS hr v = torusWeylNu r k hr (piWeyl hS hr v) :=
  rfl

theorem piWeyl_sLift (hr : 2 ≤ r) (i : Fin r) :
    piWeyl hS hr ⟨sLift π i, sLift_mem i⟩ =
      (⟨weylElt r k i, weylElt_mem_torusWeyl i⟩ : torusWeyl r k)⁻¹ :=
  Subtype.ext (coe_pi_sLift hS hr i)

theorem weylHom_sLift (hr : 2 ≤ r) (i : Fin r) :
    weylHom hS hr ⟨sLift π i, sLift_mem i⟩ = ⟨simpleRefl r i, simpleRefl_mem hr i⟩ := by
  rw [weylHom_apply, piWeyl_sLift, map_inv, torusWeylNu_weylElt hr i]
  exact inv_eq_of_mul_eq_one_right (Subtype.ext (simpleRefl_mul_self hr i))

theorem weylHom_eq_one_of_mem (hr : 2 ≤ r) {v : liftWeyl π} (hv : (v : E) ∈ liftTorus π) :
    weylHom hS hr v = 1 := by
  rw [weylHom_apply, ← MonoidHom.mem_ker, torusWeylNu_ker hr, Subgroup.mem_subgroupOf]
  exact coe_pi_mem_torus hS hv

theorem liftTorus_le_ker_weylHom (hr : 2 ≤ r) :
    (liftTorus π).subgroupOf (liftWeyl π) ≤ (weylHom hS hr).ker :=
  fun _ hv => weylHom_eq_one_of_mem hS hr (Subgroup.mem_subgroupOf.1 hv)

theorem weylHom_surjective (hr : 2 ≤ r) (hr3 : 3 ≤ r) : Function.Surjective (weylHom hS hr) := by
  rintro ⟨w, hw⟩
  have hle : Subgroup.closure (Set.range (simpleRefl r)) ≤
      (weylHom hS hr).range.map (weylGroup r).subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, ⟨⟨sLift π i, sLift_mem i⟩, rfl⟩, by rw [weylHom_sLift]; rfl⟩
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hle ((closure_simpleRefl hr3).ge hw)
  exact ⟨n, Subtype.ext hn⟩

theorem apply_single_weylHom (hr : 2 ≤ r) (v : liftWeyl π) (c : Fin r ⊕ Fin r) :
    ∃ (μ : kˣ) (c' : Fin r ⊕ Fin r),
      ((π v : orthElementaryGroup (quadPlus r k)) :
          (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) (Pi.single c 1) =
          (μ : k) • Pi.single c' 1 ∧
        coordWt c' = ((weylHom hS hr v : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] _) (coordWt c) :=
  apply_single_torusWeylNu hr (piWeyl hS hr v) c

theorem map_conj_rootSubgroup_weylHom (hr : 2 ≤ r) (v : liftWeyl π) {α : Fin r → ℤ}
    (hα : α ∈ roots r) :
    (rootSubgroup r k α).map (MulAut.conj ((π v : orthElementaryGroup (quadPlus r k)) :
        (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k))).toMonoidHom =
      rootSubgroup r k (((weylHom hS hr v : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) α) :=
  map_conj_rootSubgroup_torusWeyl hr (piWeyl hS hr v) hα

end WeylHom

section Coxeter

variable (π) in
@[expose] noncomputable def sClass (i : Fin r) :
    liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π) :=
  QuotientGroup.mk ⟨sLift π i, sLift_mem i⟩

omit [Finite k] [Finite E] in
theorem qmk_congr {x y : E} (hx : x ∈ liftWeyl π) (hy : y ∈ liftWeyl π) (h : x = y) :
    (QuotientGroup.mk ⟨x, hx⟩ : liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π)) =
      QuotientGroup.mk ⟨y, hy⟩ := by
  subst h
  rfl

variable [((liftTorus π).subgroupOf (liftWeyl π)).Normal]

omit [Finite k] [Finite E] in
theorem qmk_mul {x y : E} (hx : x ∈ liftWeyl π) (hy : y ∈ liftWeyl π) :
    (QuotientGroup.mk ⟨x, hx⟩ : liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π)) *
      QuotientGroup.mk ⟨y, hy⟩ = QuotientGroup.mk ⟨x * y, mul_mem hx hy⟩ := rfl

omit [Finite k] [Finite E] in
theorem qmk_eq_one_iff {x : E} (hx : x ∈ liftWeyl π) :
    (QuotientGroup.mk ⟨x, hx⟩ : liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π)) = 1 ↔
      x ∈ liftTorus π := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

omit [Finite k] [Finite E] in
theorem sClass_mul_self (i : Fin r) : sClass π i * sClass π i = 1 := by
  rw [sClass, qmk_mul, qmk_eq_one_iff, sLift_mul_self]
  exact hSimple_mem i (-1)

variable (hS : LargeHyp π)
include hS

theorem sClass_braid_chain {i j : Fin r} (hij : i.val + 1 = j.val) (hj : j.val + 1 < r) :
    sClass π j * sClass π i * sClass π j = sClass π i * sClass π j * sClass π i := by
  have hi : i.val + 1 < r := by omega
  simp only [sClass, qmk_mul]
  apply qmk_congr
  obtain rfl : j = ⟨i.val + 1, hi⟩ := Fin.ext hij.symm
  rw [sLift_of_lt hi, sLift_of_lt hj]
  exact braid_inl_inl hS (ne_succ_of_lt hi) (ne_succ_of_lt hj)
    (Fin.ne_of_val_ne (by simp only; omega))

theorem sClass_braid_fork {i j : Fin r} (hi3 : i.val + 3 = r) (hj : j.val + 1 = r) :
    sClass π j * sClass π i * sClass π j = sClass π i * sClass π j * sClass π i := by
  have hi : i.val + 1 < r := by omega
  have hj' : ¬j.val + 1 < r := by omega
  have hj1 : 1 ≤ j.val := by omega
  have hb : (⟨j.val - 1, by omega⟩ : Fin r) = ⟨i.val + 1, hi⟩ := Fin.ext (by simp only; omega)
  have hbj : (⟨i.val + 1, hi⟩ : Fin r) ≠ j := Fin.ne_of_val_ne (by simp only; omega)
  have hij : i ≠ j := Fin.ne_of_val_ne (by omega)
  simp only [sClass, qmk_mul]
  apply qmk_congr
  rw [sLift_of_lt hi, sLift_of_not_lt hj' hj1,
    sl2Lift_eta_congr (congrArg Sum.inl hb) rfl _ (coordIdx_inl_inr_ne hbj)]
  exact braid_inl_inr hS (ne_succ_of_lt hi) hbj hij

theorem sClass_comm {i j : Fin r} (hij : i < j)
    (hadj : ¬((i.val + 1 = j.val ∧ j.val + 1 < r) ∨ (j.val + 1 = i.val ∧ i.val + 1 < r) ∨
      (i.val + 3 = r ∧ j.val + 1 = r) ∨ (j.val + 3 = r ∧ i.val + 1 = r))) :
    sClass π i * sClass π j = sClass π j * sClass π i := by
  have hij' : i.val < j.val := hij
  have hi : i.val + 1 < r := by omega
  simp only [sClass, qmk_mul]
  apply qmk_congr
  rw [sLift_of_lt hi]
  by_cases hj : j.val + 1 < r
  · have hij2 : i.val + 1 < j.val := by
      rcases Nat.lt_or_ge (i.val + 1) j.val with h | h
      · exact h
      · exact absurd (Or.inl ⟨by omega, hj⟩) hadj
    rw [sLift_of_lt hj]
    refine (commute_sl2Lift_eta_sl2W hS _ _ ?_ ?_ ?_ ?_ sl2W).eq.symm
    · exact swap_mul_swap_apply_of_ne (by simp [Fin.ext_iff]; omega)
        (by simp [Fin.ext_iff]; omega) (by simp) (by simp)
    · exact swap_mul_swap_apply_of_ne (by simp [Fin.ext_iff]; omega)
        (by simp [Fin.ext_iff]; omega) (by simp) (by simp)
    · exact wSign_of_ne (by simp [Fin.ext_iff]; omega) (by simp)
    · exact wSign_of_ne (by simp [Fin.ext_iff]; omega) (by simp)
  · have hj1 : 1 ≤ j.val := by omega
    rw [sLift_of_not_lt hj hj1]
    by_cases hi2 : i.val + 2 = r
    · have e1 : (⟨i.val + 1, hi⟩ : Fin r) = j := Fin.ext (by simp only; omega)
      have e2 : (⟨j.val - 1, by omega⟩ : Fin r) = i := Fin.ext (by simp only; omega)
      rw [sl2Lift_eta_congr rfl (congrArg Sum.inl e1) _ (coordIdx_inl_ne hij.ne),
        sl2Lift_eta_congr (congrArg Sum.inl e2) rfl _ (coordIdx_inl_inr_ne hij.ne)]
      have h := commute_etaMinusLift_etaPlusLift hS hij.ne sl2W sl2W
      rw [etaMinusLift, etaPlusLift, etaPlus_eq] at h
      exact h.eq
    · have hi4 : i.val + 4 ≤ r := by
        have h3 : ¬i.val + 3 = r := fun h => hadj (Or.inr (Or.inr (Or.inl ⟨h, by omega⟩)))
        omega
      refine (commute_sl2Lift_eta_sl2W hS _ _ ?_ ?_ ?_ ?_ sl2W).eq.symm
      · exact swap_mul_swap_apply_of_ne (by simp [Fin.ext_iff]; omega) (by simp)
          (by simp) (by simp [Fin.ext_iff]; omega)
      · exact swap_mul_swap_apply_of_ne (by simp [Fin.ext_iff]; omega) (by simp)
          (by simp) (by simp [Fin.ext_iff]; omega)
      · exact wSign_of_ne (by simp) (by simp [Fin.ext_iff]; omega)
      · exact wSign_of_ne (by simp) (by simp [Fin.ext_iff]; omega)

omit hS in
private theorem coxeterMatrix_cartanD_apply (i j : Fin r) :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanD r) i j =
      TauCeti.coxeterOrder (cartanD r i j * cartanD r j i) :=
  TauCeti.coxeterMatrixOfCartanMatrix_apply _ _ _ i j

omit hS in
private theorem coxeterMatrix_cartanD_of_adj {i j : Fin r} (hij : i ≠ j)
    (h : (i.val + 1 = j.val ∧ j.val + 1 < r) ∨ (j.val + 1 = i.val ∧ i.val + 1 < r) ∨
      (i.val + 3 = r ∧ j.val + 1 = r) ∨ (j.val + 3 = r ∧ i.val + 1 = r)) :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanD r) i j = 3 := by
  have h' : (j.val + 1 = i.val ∧ i.val + 1 < r) ∨ (i.val + 1 = j.val ∧ j.val + 1 < r) ∨
      (j.val + 3 = r ∧ i.val + 1 = r) ∨ (i.val + 3 = r ∧ j.val + 1 = r) := by
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  have h1 : cartanD r i j = -1 := by
    simp only [cartanD, Matrix.of_apply, ite_eq_right hij, ite_eq_left h]
  have h2 : cartanD r j i = -1 := by
    simp only [cartanD, Matrix.of_apply, ite_eq_right (Ne.symm hij), ite_eq_left h']
  rw [coxeterMatrix_cartanD_apply, h1, h2, show (-1 : ℤ) * -1 = 1 by norm_num,
    TauCeti.coxeterOrder_one]

omit hS in
private theorem coxeterMatrix_cartanD_of_not_adj {i j : Fin r} (hij : i ≠ j)
    (h : ¬((i.val + 1 = j.val ∧ j.val + 1 < r) ∨ (j.val + 1 = i.val ∧ i.val + 1 < r) ∨
      (i.val + 3 = r ∧ j.val + 1 = r) ∨ (j.val + 3 = r ∧ i.val + 1 = r))) :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanD r) i j = 2 := by
  have h1 : cartanD r i j = 0 := by
    simp only [cartanD, Matrix.of_apply, ite_eq_right hij, ite_eq_right h]
  rw [coxeterMatrix_cartanD_apply, h1, zero_mul, TauCeti.coxeterOrder_zero]

private theorem isLiftable_sClass :
    (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanD r)).IsLiftable (sClass π) := by
  have key : ∀ i j : Fin r, i < j → (sClass π i * sClass π j) ^
      (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanD r)) i j = 1 := by
    intro i j hij
    have hij' : i.val < j.val := hij
    by_cases hadj : (i.val + 1 = j.val ∧ j.val + 1 < r) ∨ (j.val + 1 = i.val ∧ i.val + 1 < r) ∨
        (i.val + 3 = r ∧ j.val + 1 = r) ∨ (j.val + 3 = r ∧ i.val + 1 = r)
    · rw [coxeterMatrix_cartanD_of_adj hij.ne hadj]
      rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.pow_three_eq_one
          (sClass_mul_self i) (sClass_mul_self j) (sClass_braid_chain hS h1 h2)
      · omega
      · exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.pow_three_eq_one
          (sClass_mul_self i) (sClass_mul_self j) (sClass_braid_fork hS h1 h2)
      · omega
    · rw [coxeterMatrix_cartanD_of_not_adj hij.ne hadj]
      exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.pow_two_eq_one_of_commute
        (sClass_mul_self i) (sClass_mul_self j) (sClass_comm hS hij hadj)
  intro i j
  rcases lt_trichotomy i j with h | rfl | h
  · exact key i j h
  · rw [CoxeterMatrix.diagonal, pow_one]
    exact sClass_mul_self i
  · rw [CoxeterMatrix.symmetric]
    exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.pow_eq_one_comm (key j i h)

end Coxeter

section Kernel

omit [Field k] [Finite k] [Finite E] in
theorem simpleRefl_apply_eq_stdReflD (hr : 2 ≤ r) (i : Fin r) (e : Fin r → ℤ) :
    simpleRefl r i e = stdReflD r i e := by
  by_cases h : i.val + 1 < r
  · rw [simpleRefl_of_lt h, stdReflD_of_lt r h]
    funext j
    rw [signedPermAut_apply, Equiv.swap_inv, Pi.one_apply, Units.val_one, one_mul,
      Function.comp_apply]
  · rw [simpleRefl_of_not_lt h, stdReflD_of_not_lt r h]
    have hp : (⟨i.val - 1, by omega⟩ : Fin r) = ⟨r - 2, by omega⟩ := Fin.ext (by simp only; omega)
    funext j
    rw [signedPermAut_apply, Equiv.swap_inv, hp]
    congr 1
    have hpi : (⟨r - 2, by omega⟩ : Fin r) ≠ i := Fin.ne_of_val_ne (by simp only; omega)
    by_cases hj1 : j = ⟨r - 2, by omega⟩
    · subst hj1
      rw [Equiv.swap_apply_left, lastSigns, ite_eq_left (Or.inl rfl),
        ite_eq_left (Or.inl (by simp only; omega))]
      rfl
    by_cases hj2 : j = i
    · subst hj2
      rw [Equiv.swap_apply_right, lastSigns, ite_eq_left (Or.inr (by simp only; omega)),
        ite_eq_left (Or.inr (by omega))]
      rfl
    · rw [Equiv.swap_apply_of_ne_of_ne hj1 hj2, lastSigns, ite_eq_right, ite_eq_right]
      · rfl
      · rintro (h' | h')
        · exact hj1 (Fin.ext (by simp only; omega))
        · exact hj2 (Fin.ext (by omega))
      · rintro (h' | h')
        · exact hj2 h'
        · exact hj1 (Fin.ext (by simp only; omega))

variable (hS : LargeHyp π)
include hS

theorem ker_weylHom_le (hr : 2 ≤ r) :
    (weylHom hS hr).ker ≤ (liftTorus π).subgroupOf (liftWeyl π) := by
  have := normal_liftTorus_subgroupOf hS hr
  set hA := isFiniteType_cartanD r
  set cs := (CFSG.LieType.RootSystem.coxeterMatrix hA).toCoxeterSystem
  set L := cs.lift ⟨sClass π, isLiftable_sClass hS⟩ with hL
  set φbar := QuotientGroup.lift _ (weylHom hS hr) (liftTorus_le_ker_weylHom hS hr) with hφbar
  have hsimple : ∀ i, ((φbar (L (cs.simple i)) : weylGroup r) :
      (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = simpleRefl r i := by
    intro i
    rw [hL, CoxeterSystem.lift_apply_simple, sClass, hφbar, QuotientGroup.lift_mk, weylHom_sLift]
  have hact : ∀ w v, toStdD r (CFSG.LieType.RootSystem.weylAction hA w v) =
      ((φbar (L w) : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (toStdD r v) := by
    intro w
    refine cs.simple_induction_left (p := fun w => ∀ v,
      toStdD r (CFSG.LieType.RootSystem.weylAction hA w v) =
        ((φbar (L w) : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (toStdD r v)) w ?_ ?_
    · intro v
      rw [map_one, map_one, map_one]
      rfl
    · intro w i ih v
      rw [CFSG.LieType.RootSystem.weylAction_mul_apply, CFSG.LieType.RootSystem.weylAction_simple,
        toStdD_reflection, ih, map_mul, map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply,
        hsimple, simpleRefl_apply_eq_stdReflD hr]
  have hinj : ∀ w, φbar (L w) = 1 → w = 1 := by
    intro w hw
    apply CFSG.LieType.RootSystem.weylAction_injective hA
    rw [map_one]
    refine LinearMap.ext fun v => toStdD_injective r ?_
    rw [hact, hw, Module.End.one_apply]
    rfl
  have hsurj : Function.Surjective L := by
    have key : ∀ x (hx : x ∈ liftWeyl π),
        (QuotientGroup.mk ⟨x, hx⟩ : liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π)) ∈
          L.range := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | ⟨i, rfl⟩
        · exact ⟨1, by rw [map_one]; exact ((qmk_eq_one_iff _).2 hx).symm⟩
        · exact ⟨cs.simple i, CoxeterSystem.lift_apply_simple _ _ i⟩
      | one => exact L.range.one_mem
      | mul x y hx hy ihx ihy => exact mul_mem ihx ihy
      | inv x hx ihx => exact inv_mem ihx
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    exact key x hx
  intro n hn
  obtain ⟨w, hw⟩ := hsurj (QuotientGroup.mk n)
  have h1 : φbar (L w) = 1 := by
    rw [hw, hφbar, QuotientGroup.lift_mk]
    exact hn
  rw [hinj w h1, map_one] at hw
  exact (QuotientGroup.eq_one_iff n).1 hw.symm

theorem ker_weylHom (hr : 2 ≤ r) : (weylHom hS hr).ker = (liftTorus π).subgroupOf (liftWeyl π) :=
  le_antisymm (ker_weylHom_le hS hr) (liftTorus_le_ker_weylHom hS hr)

theorem injective_pi_liftWeyl (hr : 3 ≤ r) : Function.Injective (π.comp (liftWeyl π).subtype) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  have hn' : π n = 1 := hn
  have hw : weylHom hS (by omega) n = 1 := by
    have hpi : piWeyl hS (by omega) n = 1 := Subtype.ext (by rw [coe_piWeyl, hn']; rfl)
    rw [weylHom_apply, hpi, map_one]
  have hH : (n : E) ∈ liftTorus π := Subgroup.mem_subgroupOf.1 (ker_weylHom_le hS _ hw)
  have h1 : (⟨n, hH⟩ : liftTorus π) = 1 :=
    injective_pi_liftTorus hS hr (by rw [map_one]; exact hn')
  have h2 : (n : E) = 1 := congrArg Subtype.val h1
  exact Subtype.ext h2

@[expose] noncomputable def weylQuotientEquiv (hr : 2 ≤ r) (hr3 : 3 ≤ r)
    [((liftTorus π).subgroupOf (liftWeyl π)).Normal] :
    liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π) ≃* weylGroup r :=
  (QuotientGroup.quotientMulEquivOfEq (ker_weylHom hS hr).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (weylHom hS hr) (weylHom_surjective hS hr hr3))

theorem weylQuotientEquiv_mk (hr : 2 ≤ r) (hr3 : 3 ≤ r)
    [((liftTorus π).subgroupOf (liftWeyl π)).Normal] (n : liftWeyl π) :
    weylQuotientEquiv hS hr hr3 n = weylHom hS hr n :=
  rfl

end Kernel

end CFSG.RankThree.CentralLiftSO.SplitO
