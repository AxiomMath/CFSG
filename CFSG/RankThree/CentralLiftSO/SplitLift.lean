module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitTorus
public import CFSG.RankThree.CentralLift.LargeLift
import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylLift

public section

namespace CFSG.RankThree.CentralLiftSO.SplitO

open Matrix CFSG.LieType.CentralExt CFSG.LieType.Universal.Spin CFSG.RankThree.CentralLift
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LocalAnalysis.ComponentInitial (orthElementaryGroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2Diag sl2W sl2ConjDiag
  coe_sl2Diag sl2ConjDiag_inv_sl2W conj_comp_eq)

variable {r : ℕ} {k : Type} [Field k] {E : Type*} [Group E]

structure LargeHyp (π : E →* orthElementaryGroup (quadPlus r k)) : Prop where
  char : ringChar k ≠ 2
  ext : IsLargeCentralExt π

variable [Finite k] [Finite E] {π : E →* orthElementaryGroup (quadPlus r k)}

namespace LargeHyp

variable (hS : LargeHyp π)
include hS

theorem map_lift (α : SpecialLinearGroup (Fin 2) k →* orthElementaryGroup (quadPlus r k))
    (g : SpecialLinearGroup (Fin 2) k) : π (sl2Lift π α g) = α g :=
  map_sl2Lift_large hS.char hS.ext α g

theorem lift_comp (α : SpecialLinearGroup (Fin 2) k →* orthElementaryGroup (quadPlus r k))
    (β : SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin 2) k) :
    (sl2Lift π α).comp β = sl2Lift π (α.comp β) :=
  sl2Lift_comp_large hS.char hS.char hS.ext α β

theorem commute_lift (α α' : SpecialLinearGroup (Fin 2) k →* orthElementaryGroup (quadPlus r k))
    (h : ∀ g g', Commute (α g) (α' g')) (g g' : SpecialLinearGroup (Fin 2) k) :
    Commute (sl2Lift π α g) (sl2Lift π α' g') :=
  commute_sl2Lift_large hS.char hS.char hS.ext α α' h g g'

theorem conj_lift_apply {e : E}
    {α β : SpecialLinearGroup (Fin 2) k →* orthElementaryGroup (quadPlus r k)}
    {γ : SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin 2) k}
    (h : (MulAut.conj (π e)).toMonoidHom.comp α = β.comp γ) (g : SpecialLinearGroup (Fin 2) k) :
    e * sl2Lift π α g * e⁻¹ = sl2Lift π β (γ g) := by
  rw [conj_sl2Lift_apply_large hS.char hS.ext α e g, h, ← hS.lift_comp]
  rfl

theorem conj_lift_apply' {e : E}
    {α β : SpecialLinearGroup (Fin 2) k →* orthElementaryGroup (quadPlus r k)}
    (h : (MulAut.conj (π e)).toMonoidHom.comp α = β) (g : SpecialLinearGroup (Fin 2) k) :
    e * sl2Lift π α g * e⁻¹ = sl2Lift π β g := by
  rw [conj_sl2Lift_apply_large hS.char hS.ext α e g, h]

end LargeHyp

section Images

variable (hS : LargeHyp π)
include hS

theorem pi_etaMinusLift {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) k) :
    π (etaMinusLift π i j hij g) = etaMinus i j hij g :=
  hS.map_lift _ g

theorem pi_etaPlusLift {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) k) :
    π (etaPlusLift π i j hij g) = etaPlus i j hij g :=
  hS.map_lift _ g

theorem coe_pi_hMinus {i j : Fin r} (hij : i ≠ j) (a : kˣ) :
    ((π (hMinus π i j hij a) : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) =
      torusElt r k (Pi.mulSingle i a * Pi.mulSingle j a⁻¹) := by
  rw [hMinus, pi_etaMinusLift hS, coe_etaMinus_sl2Diag]

theorem coe_pi_hPlus {i j : Fin r} (hij : i ≠ j) (a : kˣ) :
    ((π (hPlus π i j hij a) : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] (Fin r ⊕ Fin r → k)) =
      torusElt r k (Pi.mulSingle i a * Pi.mulSingle j a) := by
  rw [hPlus, pi_etaPlusLift hS, coe_etaPlus_sl2Diag]

end Images

section Commutation

variable (hS : LargeHyp π)
include hS

theorem commute_etaMinusLift_etaPlusLift {i j : Fin r} (hij : i ≠ j)
    (g g' : SpecialLinearGroup (Fin 2) k) :
    Commute (etaMinusLift π i j hij g) (etaPlusLift π i j hij g') :=
  hS.commute_lift _ _ (commute_etaMinus_etaPlus hij) g g'

theorem conj_liftEta_of_torusElt {a b : Fin r ⊕ Fin r} (h : coordIdx a ≠ coordIdx b) {x : E}
    {d : Fin r → kˣ} (hx : ((π x : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] _) = torusElt r k d) {u : kˣ}
    (hu : (Sum.elim d d⁻¹ a)⁻¹ * Sum.elim d d⁻¹ b = u) (g : SpecialLinearGroup (Fin 2) k) :
    x * sl2Lift π (eta h) g * x⁻¹ = sl2Lift π (eta h) (sl2ConjDiag u g) := by
  rw [← hu]
  exact hS.conj_lift_apply (conj_eta_of_torusElt h hx) g

theorem commute_liftEta_sl2Diag_of_torusElt {a b : Fin r ⊕ Fin r} (h : coordIdx a ≠ coordIdx b)
    {x : E} {d : Fin r → kˣ} (hx : ((π x : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] _) = torusElt r k d) (c : kˣ) :
    Commute x (sl2Lift π (eta h) (sl2Diag c)) := by
  have h1 := conj_liftEta_of_torusElt hS h hx rfl (sl2Diag c)
  rw [sl2ConjDiag_sl2Diag] at h1
  exact mul_inv_eq_iff_eq_mul.1 h1

theorem exists_torusElt_of_mem_hGens {x : E} (hx : x ∈ hGens π) :
    ∃ d : Fin r → kˣ, ((π x : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] _) = torusElt r k d := by
  rcases hx with ⟨i, j, hij, a, rfl⟩ | ⟨i, j, hij, a, rfl⟩
  · exact ⟨_, coe_pi_hMinus hS hij a⟩
  · exact ⟨_, coe_pi_hPlus hS hij a⟩

theorem commute_hGens_of_torusElt {x : E} {d : Fin r → kˣ}
    (hx : ((π x : orthElementaryGroup (quadPlus r k)) : (Fin r ⊕ Fin r → k) ≃ₗ[k] _) =
      torusElt r k d) {y : E} (hy : y ∈ hGens π) : Commute x y := by
  rcases hy with ⟨i, j, hij, a, rfl⟩ | ⟨i, j, hij, a, rfl⟩
  · rw [hMinus_eq_liftEta]
    exact commute_liftEta_sl2Diag_of_torusElt hS _ hx a
  · rw [hPlus_eq_liftEta]
    exact commute_liftEta_sl2Diag_of_torusElt hS _ hx a

theorem commute_of_mem_hGens {x y : E} (hx : x ∈ hGens π) (hy : y ∈ hGens π) : Commute x y := by
  obtain ⟨d, hd⟩ := exists_torusElt_of_mem_hGens hS hx
  exact commute_hGens_of_torusElt hS hd hy

theorem liftTorus_commute {x y : E} (hx : x ∈ liftTorus π) (hy : y ∈ liftTorus π) :
    Commute x y := by
  have hcomm := Subgroup.isMulCommutative_closure (k := hGens π)
    (fun x hx y hy _ => commute_of_mem_hGens hS hx hy)
  exact congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : liftTorus π) ⟨y, hy⟩)

end Commutation

section Relations

variable (hS : LargeHyp π)
include hS

theorem vMinus_conj_hMinus {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a : kˣ) :
    etaMinusLift π i j hij sl2W * hMinus π j l hjl a * (etaMinusLift π i j hij sl2W)⁻¹ =
      hMinus π i l hil a := by
  have h := hS.conj_lift_apply (e := etaMinusLift π i j hij sl2W) (α := etaMinus j l hjl)
    (β := etaMinus i l hil) (γ := sl2ConjDiag (-1))
    (by rw [pi_etaMinusLift hS]; exact conj_eta_sl2W_inl_inl hij hjl hil) (sl2Diag a)
  rw [sl2ConjDiag_sl2Diag] at h
  exact h

theorem hMinus_inv_conj_vMinus {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (a : kˣ) :
    (hMinus π j l hjl a)⁻¹ * etaMinusLift π i j hij sl2W * hMinus π j l hjl a =
      hMinus π i j hij a * etaMinusLift π i j hij sl2W := by
  have hx : ((π (hMinus π j l hjl a)⁻¹ : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] _) = torusElt r k (Pi.mulSingle j a * Pi.mulSingle l a⁻¹)⁻¹ := by
    rw [map_inv, Subgroup.coe_inv, coe_pi_hMinus hS, map_inv]
  have h := conj_liftEta_of_torusElt hS (coordIdx_inl_ne hij) hx (u := a⁻¹)
    (by simp [hij, hil, hjl]) sl2W
  rw [sl2ConjDiag_inv_sl2W, map_mul, inv_inv] at h
  exact h

theorem hMinus_trans {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a : kˣ) :
    hMinus π i l hil a = hMinus π i j hij a * hMinus π j l hjl a := by
  have h1 := vMinus_conj_hMinus hS hij hjl hil a
  have h2 := hMinus_inv_conj_vMinus hS hij hjl hil a
  have h3 : etaMinusLift π i j hij sl2W * hMinus π j l hjl a =
      hMinus π j l hjl a * (hMinus π i j hij a * etaMinusLift π i j hij sl2W) := by
    rw [← h2]
    group
  rw [← h1, h3, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  exact (commute_of_mem_hGens hS (hMinus_mem_hGens hjl a) (hMinus_mem_hGens hij a)).eq

theorem vMinus_conj_hPlus {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a : kˣ) :
    etaMinusLift π j l hjl sl2W * hPlus π i j hij a * (etaMinusLift π j l hjl sl2W)⁻¹ =
      hPlus π i l hil a := by
  have h := hS.conj_lift_apply' (e := etaMinusLift π j l hjl sl2W) (α := etaPlus i j hij)
    (β := etaPlus i l hil)
    (by rw [pi_etaMinusLift hS, etaPlus_eq, etaPlus_eq]; exact conj_eta_sl2W_inl_inr hij hjl hil)
    (sl2Diag a)
  exact h

theorem hPlus_inv_conj_vMinus {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (a : kˣ) :
    (hPlus π i j hij a)⁻¹ * etaMinusLift π j l hjl sl2W * hPlus π i j hij a =
      hMinus π j l hjl a⁻¹ * etaMinusLift π j l hjl sl2W := by
  have hx : ((π (hPlus π i j hij a)⁻¹ : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] _) = torusElt r k (Pi.mulSingle i a * Pi.mulSingle j a)⁻¹ := by
    rw [map_inv, Subgroup.coe_inv, coe_pi_hPlus hS, map_inv]
  have h := conj_liftEta_of_torusElt hS (coordIdx_inl_ne hjl) hx (u := a⁻¹⁻¹)
    (by simp [hij.symm, hil.symm, hjl.symm]) sl2W
  rw [sl2ConjDiag_inv_sl2W, map_mul, inv_inv] at h
  exact h

theorem hPlus_trans {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a : kˣ) :
    hPlus π i j hij a = hPlus π i l hil a * hMinus π j l hjl a := by
  have h1 := vMinus_conj_hPlus hS hij hjl hil a
  have h2 := hPlus_inv_conj_vMinus hS hij hjl hil a
  have h3 : etaMinusLift π j l hjl sl2W * hPlus π i j hij a =
      hPlus π i j hij a * (hMinus π j l hjl a⁻¹ * etaMinusLift π j l hjl sl2W) := by
    rw [← h2]
    group
  calc hPlus π i j hij a = hPlus π i j hij a * (hMinus π j l hjl a⁻¹ * hMinus π j l hjl a) := by
        rw [hMinus_mul, inv_mul_cancel, hMinus, map_one, map_one, mul_one]
    _ = hPlus π i l hil a * hMinus π j l hjl a := by
        rw [← h1, h3]
        group

theorem hMinus_symm {i j : Fin r} (hij : i ≠ j) (a : kˣ) :
    hMinus π j i hij.symm a = hMinus π i j hij a⁻¹ := by
  have hη : etaMinus (k := k) j i hij.symm = (etaMinus i j hij).comp sl2Swap :=
    eta_swap_args (coordIdx_inl_ne hij)
  rw [hMinus, etaMinusLift, hη, ← hS.lift_comp, MonoidHom.comp_apply, sl2Swap_sl2Diag]
  rfl

theorem hPlus_symm {i j : Fin r} (hij : i ≠ j) (a : kˣ) :
    hPlus π j i hij.symm a = hPlus π i j hij a := by
  have h₀ : coordIdx (Sum.inr j : Fin r ⊕ Fin r) ≠ coordIdx (Sum.inl i) :=
    Ne.symm (coordIdx_inl_inr_ne hij)
  have h1 : eta (k := k) (coordIdx_inl_inr_ne hij.symm) = (eta h₀).comp sl2InvT :=
    eta_swap_swap h₀
  have h2 : eta (k := k) h₀ = (eta (coordIdx_inl_inr_ne hij)).comp sl2Swap :=
    eta_swap_args (coordIdx_inl_inr_ne hij)
  have hη : etaPlus (k := k) j i hij.symm = (etaPlus i j hij).comp (sl2Swap.comp sl2InvT) := by
    rw [etaPlus_eq, etaPlus_eq, h1, h2, MonoidHom.comp_assoc]
  rw [hPlus, etaPlusLift, hη, ← hS.lift_comp, MonoidHom.comp_apply, MonoidHom.comp_apply,
    sl2InvT_sl2Diag, sl2Swap_sl2Diag, inv_inv]
  rfl

end Relations

section Theta

variable (hS : LargeHyp π)
include hS

theorem pairwise_commute_simpleLift :
    Pairwise fun i j => ∀ x y : kˣ,
      Commute (((simpleLift π i).comp sl2Diag) x) (((simpleLift π j).comp sl2Diag) y) :=
  fun i j _ x y => liftTorus_commute hS (hSimple_mem i x) (hSimple_mem j y)

noncomputable def thetaHom : (Fin r → kˣ) →* E :=
  MonoidHom.noncommPiCoprod (fun i => (simpleLift π i).comp sl2Diag)
    (pairwise_commute_simpleLift hS)

theorem thetaHom_mulSingle (i : Fin r) (a : kˣ) :
    thetaHom hS (Pi.mulSingle i a) = hSimple π i a :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

theorem thetaHom_apply (u : Fin r → kˣ) :
    thetaHom hS u = (List.ofFn fun i => hSimple π i (u i)).prod := by
  rw [thetaHom, MonoidHom.noncommPiCoprod_apply]
  exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.noncommProd_univ_fin _ _

theorem thetaHom_mem (u : Fin r → kˣ) : thetaHom hS u ∈ liftTorus π := by
  have hle : (thetaHom hS).range ≤ liftTorus π := by
    rw [thetaHom, MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨a, rfl⟩
    exact hSimple_mem i a
  exact hle ⟨u, rfl⟩

theorem hSimple_mem_range (i : Fin r) (a : kˣ) : hSimple π i a ∈ (thetaHom hS).range :=
  ⟨Pi.mulSingle i a, thetaHom_mulSingle hS i a⟩

theorem hMinus_mem_range_of_lt {i j : Fin r} (hij : i < j) (a : kˣ) :
    hMinus π i j hij.ne a ∈ (thetaHom hS).range := by
  suffices h : ∀ m : ℕ, ∀ (i j : Fin r) (hij : i ≠ j), j.val = i.val + m + 1 →
      hMinus π i j hij a ∈ (thetaHom hS).range from
    h (j.val - i.val - 1) i j hij.ne (by have := Fin.lt_def.1 hij; omega)
  intro m
  induction m with
  | zero =>
    intro i j hij hj
    have hlt : i.val + 1 < r := by have := j.isLt; omega
    obtain rfl : j = ⟨i.val + 1, hlt⟩ := Fin.ext (by simpa using hj)
    rw [← hSimple_of_lt hlt]
    exact hSimple_mem_range hS i a
  | succ m ih =>
    intro i j hij hj
    have hlt : i.val + m + 1 < r := by have := j.isLt; omega
    set j' : Fin r := ⟨i.val + m + 1, hlt⟩
    have hij' : i ≠ j' := Fin.ne_of_val_ne (by simp [j']; omega)
    have hj'j : j' ≠ j := Fin.ne_of_val_ne (by simp [j']; omega)
    have hlt' : j'.val + 1 < r := by have := j.isLt; simp [j']; omega
    obtain rfl : j = ⟨j'.val + 1, hlt'⟩ := Fin.ext (by simp [j']; omega)
    rw [hMinus_trans hS hij' hj'j hij]
    refine mul_mem (ih i j' hij' rfl) ?_
    rw [← hSimple_of_lt hlt']
    exact hSimple_mem_range hS j' a

theorem hMinus_mem_range {i j : Fin r} (hij : i ≠ j) (a : kˣ) :
    hMinus π i j hij a ∈ (thetaHom hS).range := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact hMinus_mem_range_of_lt hS h a
  · rw [hMinus_symm hS h.ne a]
    exact hMinus_mem_range_of_lt hS h _

theorem hPlus_mem_range (hr : 2 ≤ r) {i j : Fin r} (hij : i ≠ j) (a : kˣ) :
    hPlus π i j hij a ∈ (thetaHom hS).range := by
  set L : Fin r := ⟨r - 1, by omega⟩
  set L' : Fin r := ⟨r - 2, by omega⟩
  have hL'L : L' ≠ L := Fin.ne_of_val_ne (by simp [L, L']; omega)
  have hlast : hPlus π L' L hL'L a ∈ (thetaHom hS).range := by
    have hnlt : ¬L.val + 1 < r := by simp [L]; omega
    have h1 : 1 ≤ L.val := by simp [L]; omega
    rw [hPlus_congr_left (Fin.ext (by simp [L, L']; omega) : L' = ⟨L.val - 1, by omega⟩) hL'L
      (pred_ne_of_one_le h1), ← hSimple_of_not_lt hnlt h1]
    exact hSimple_mem_range hS L a
  have hfromL : ∀ (j : Fin r) (hj : L ≠ j), hPlus π L j hj a ∈ (thetaHom hS).range := by
    intro j hj
    by_cases hjL' : j = L'
    · subst hjL'
      rw [hPlus_symm hS hL'L]
      exact hlast
    · have hrel := hPlus_trans hS (i := L) (j := L') (l := j) hL'L.symm (Ne.symm hjL') hj a
      have : hPlus π L j hj a = hPlus π L L' hL'L.symm a * (hMinus π L' j (Ne.symm hjL') a)⁻¹ := by
        rw [hrel, mul_inv_cancel_right]
      rw [this]
      refine mul_mem ?_ (inv_mem (hMinus_mem_range hS _ a))
      rw [hPlus_symm hS hL'L]
      exact hlast
  by_cases hiL : i = L
  · subst hiL
    exact hfromL j hij
  by_cases hjL : j = L
  · subst hjL
    rw [hPlus_symm hS (Ne.symm hij)]
    exact hfromL i (Ne.symm hiL)
  · rw [hPlus_trans hS hij (j := j) (l := L) hjL hiL]
    refine mul_mem ?_ (hMinus_mem_range hS _ a)
    rw [hPlus_symm hS (Ne.symm hiL)]
    exact hfromL i (Ne.symm hiL)

theorem range_thetaHom (hr : 2 ≤ r) : (thetaHom hS).range = liftTorus π := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    exact thetaHom_mem hS u
  · rw [liftTorus, Subgroup.closure_le]
    rintro _ (⟨i, j, hij, a, rfl⟩ | ⟨i, j, hij, a, rfl⟩)
    · exact hMinus_mem_range hS hij a
    · exact hPlus_mem_range hS hr hij a

end Theta

section Image

variable (hS : LargeHyp π)
include hS

theorem coe_pi_hSimple (i : Fin r) (c : kˣ) :
    ((π (hSimple π i c) : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] _) = torusElt r k (simpleDiag i c) := by
  by_cases h : i.val + 1 < r
  · rw [hSimple_of_lt h, coe_pi_hMinus hS, simpleDiag, dite_eq_left h]
  · by_cases h' : 1 ≤ i.val
    · rw [hSimple_of_not_lt h h', coe_pi_hPlus hS, simpleDiag, dite_eq_right h, dite_eq_left h']
    · rw [hSimple, simpleLift, dite_eq_right h, dite_eq_right h', MonoidHom.one_apply, map_one,
        simpleDiag, dite_eq_right h, dite_eq_right h', map_one, Subgroup.coe_one]

theorem coe_pi_thetaHom (u : Fin r → kˣ) :
    ((π (thetaHom hS u) : orthElementaryGroup (quadPlus r k)) :
      (Fin r ⊕ Fin r → k) ≃ₗ[k] _) = torusElt r k (∏ i, simpleDiag i (u i)) := by
  change ((orthElementaryGroup (quadPlus r k)).subtype.comp π) (thetaHom hS u) = _
  rw [thetaHom_apply, map_list_prod, List.map_ofFn, ← List.prod_ofFn, map_list_prod,
    List.map_ofFn]
  congr 2
  funext i
  exact coe_pi_hSimple hS i (u i)

theorem range_pi_thetaHom (hr : 2 ≤ r) :
    ((orthElementaryGroup (quadPlus r k)).subtype.comp (π.comp (thetaHom hS))).range =
      sqTorus r k := by
  set f := (orthElementaryGroup (quadPlus r k)).subtype.comp π
  have hf : (orthElementaryGroup (quadPlus r k)).subtype.comp (π.comp (thetaHom hS)) =
      f.comp (thetaHom hS) := rfl
  have hfm : ∀ {i j : Fin r} (hij : i ≠ j) (a : kˣ),
      f (hMinus π i j hij a) = torusElt r k (Pi.mulSingle i a * Pi.mulSingle j a⁻¹) :=
    fun hij a => coe_pi_hMinus hS hij a
  have hfp : ∀ {i j : Fin r} (hij : i ≠ j) (a : kˣ),
      f (hPlus π i j hij a) = torusElt r k (Pi.mulSingle i a * Pi.mulSingle j a) :=
    fun hij a => coe_pi_hPlus hS hij a
  rw [hf, MonoidHom.range_comp, range_thetaHom hS hr]
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, liftTorus, Subgroup.closure_le]
    rintro _ (⟨i, j, hij, a, rfl⟩ | ⟨i, j, hij, a, rfl⟩)
    · refine ⟨_, (hfm hij a).symm, ?_⟩
      rw [prod_mulSingle_mul_mulSingle, mul_inv_cancel]
      exact ⟨1, (one_mul 1).symm⟩
    · exact ⟨_, (hfp hij a).symm, by rw [prod_mulSingle_mul_mulSingle]; exact ⟨a, rfl⟩⟩
  · rintro _ ⟨a, rfl, b, hb⟩
    set L : Fin r := ⟨r - 1, by omega⟩
    set L' : Fin r := ⟨r - 2, by omega⟩
    have hL'L : L' ≠ L := Fin.ne_of_val_ne (by simp [L, L']; omega)
    have hdecomp : a = (∏ j, ((Pi.mulSingle j (a j) : Fin r → kˣ) *
        (Pi.mulSingle L (a j)⁻¹ : Fin r → kˣ))) *
        ((Pi.mulSingle L' b * Pi.mulSingle L b) *
          (Pi.mulSingle L' b⁻¹ * Pi.mulSingle L b⁻¹⁻¹)) := by
      have h1 : ((Pi.mulSingle L' b * Pi.mulSingle L b) *
          (Pi.mulSingle L' b⁻¹ * Pi.mulSingle L b⁻¹⁻¹) : Fin r → kˣ) =
          Pi.mulSingle L (∏ j, a j) := by
        rw [hb, inv_inv, mul_mul_mul_comm, ← Pi.mulSingle_mul, ← Pi.mulSingle_mul,
          mul_inv_cancel, Pi.mulSingle_one, one_mul]
      rw [h1, Finset.prod_mul_distrib, Finset.univ_prod_mulSingle, mul_assoc]
      conv_lhs => rw [← mul_one a]
      congr 1
      funext y
      rw [Pi.one_apply, Pi.mul_apply, Finset.prod_apply]
      by_cases hy : y = L
      · subst hy
        simp [Finset.prod_inv_distrib]
      · simp [Pi.mulSingle_eq_of_ne hy]
    change a ∈ ((liftTorus π).map f).comap (torusElt r k)
    rw [hdecomp]
    refine mul_mem (Subgroup.prod_mem _ fun j _ => ?_) (mul_mem ?_ ?_)
    · by_cases hj : j = L
      · subst hj
        rw [← Pi.mulSingle_mul, mul_inv_cancel, Pi.mulSingle_one]
        exact one_mem _
      · exact ⟨_, hMinus_mem hj (a j), hfm hj (a j)⟩
    · exact ⟨_, hPlus_mem hL'L b, hfp hL'L b⟩
    · exact ⟨_, hMinus_mem hL'L b⁻¹, hfm hL'L b⁻¹⟩

end Image

section Kernel

variable (hS : LargeHyp π)
include hS

theorem thetaHom_epsilon (hr : 3 ≤ r) :
    thetaHom hS (Pi.mulSingle ⟨r - 2, by omega⟩ (-1) * Pi.mulSingle ⟨r - 1, by omega⟩ (-1)) =
      hSimple π ⟨r - 2, by omega⟩ (-1) * hSimple π ⟨r - 1, by omega⟩ (-1) := by
  rw [map_mul, thetaHom_mulSingle, thetaHom_mulSingle]

theorem epsilon_sq (hr : 3 ≤ r) :
    (hSimple π ⟨r - 2, by omega⟩ (-1) * hSimple π ⟨r - 1, by omega⟩ (-1)) ^ 2 = 1 := by
  rw [← thetaHom_epsilon hS hr, ← map_pow]
  convert map_one (thetaHom hS)
  funext j
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.one_apply]
  by_cases h1 : j = ⟨r - 2, by omega⟩ <;> by_cases h2 : j = ⟨r - 1, by omega⟩ <;>
    simp [h1, h2, Pi.mulSingle_apply]

theorem epsilon_mem_ker (hr : 3 ≤ r) :
    hSimple π ⟨r - 2, by omega⟩ (-1) * hSimple π ⟨r - 1, by omega⟩ (-1) ∈ π.ker := by
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  rw [map_mul, Subgroup.coe_mul, coe_pi_hSimple hS, coe_pi_hSimple hS, ← map_mul,
    Subgroup.coe_one]
  convert map_one (torusElt r k)
  funext j
  rw [Pi.mul_apply, simpleDiag_apply, simpleDiag_apply, Pi.one_apply]
  dsimp only
  split_ifs <;> first | omega | simp

theorem liftTorus_inf_ker (hr : 3 ≤ r) :
    liftTorus π ⊓ π.ker =
      Subgroup.zpowers (hSimple π ⟨r - 2, by omega⟩ (-1) * hSimple π ⟨r - 1, by omega⟩ (-1)) := by
  apply le_antisymm
  · rintro x ⟨hxH, hxK⟩
    rw [← range_thetaHom hS (by omega)] at hxH
    obtain ⟨u, rfl⟩ := hxH
    have h1 : torusElt r k (∏ i, simpleDiag i (u i)) = torusElt r k 1 := by
      rw [← coe_pi_thetaHom hS, (MonoidHom.mem_ker).1 hxK, map_one, Subgroup.coe_one]
    rcases eq_of_prod_simpleDiag_eq_one hr (torusElt_injective h1) with rfl | rfl
    · rw [map_one]
      exact one_mem _
    · rw [thetaHom_epsilon hS hr]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact ⟨mul_mem (hSimple_mem _ _) (hSimple_mem _ _), epsilon_mem_ker hS hr⟩

theorem card_liftTorus_inf_ker_le_two (hr : 3 ≤ r) :
    Nat.card (liftTorus π ⊓ π.ker : Subgroup E) ≤ 2 := by
  rw [liftTorus_inf_ker hS hr, Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by norm_num) (epsilon_sq hS hr)

omit [Finite k] [Finite E] in
theorem eq_one_of_mem_ker_of_sq_eq_one {x : E} (hx : x ∈ π.ker) (hx2 : x ^ 2 = 1) : x = 1 := by
  obtain ⟨p, hp, hp3, hpk⟩ := hS.ext.large
  obtain ⟨n, hn⟩ := hpk ⟨x, hx⟩
  have hn' : x ^ p ^ n = 1 := congrArg Subtype.val hn
  have hcop : Nat.Coprime 2 (p ^ n) :=
    Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))
  have h1 : x ^ Nat.gcd 2 (p ^ n) = 1 := pow_gcd_eq_one.2 ⟨hx2, hn'⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1

theorem epsilon_eq_one (hr : 3 ≤ r) :
    hSimple π ⟨r - 2, by omega⟩ (-1) * hSimple π ⟨r - 1, by omega⟩ (-1) = 1 :=
  eq_one_of_mem_ker_of_sq_eq_one hS (epsilon_mem_ker hS hr) (epsilon_sq hS hr)

theorem liftTorus_inf_ker_eq_bot (hr : 3 ≤ r) : liftTorus π ⊓ π.ker = ⊥ := by
  rw [liftTorus_inf_ker hS hr, epsilon_eq_one hS hr, Subgroup.zpowers_one_eq_bot]

theorem injective_pi_liftTorus (hr : 3 ≤ r) :
    Function.Injective (π.comp (liftTorus π).subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : (x : E) ∈ liftTorus π ⊓ π.ker := ⟨x.2, hx⟩
  rw [liftTorus_inf_ker_eq_bot hS hr, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

end Kernel

end CFSG.RankThree.CentralLiftSO.SplitO
