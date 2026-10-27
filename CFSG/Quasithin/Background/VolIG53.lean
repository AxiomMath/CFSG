module

public import CFSG.Quasithin.H13.A6Model4
public import CFSG.Quasithin.H13.Sp62S6Over

public section

namespace CFSG.Quasithin.VolI

namespace G53

open Equiv CFSG.Quasithin.H13.A6

theorem zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

section Scalars

variable {M : Type} [AddCommGroup M]

@[expose] def zs (c : ZMod 2) (m : M) : M := if c = 0 then 0 else m

theorem zs_add (h2 : ∀ m : M, m + m = 0) (c d : ZMod 2) (m : M) :
    zs (c + d) m = zs c m + zs d m := by
  rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases d with rfl | rfl
  · simp [zs]
  · simp [zs]
  · simp [zs]
  · rw [show (1 + 1 : ZMod 2) = 0 from rfl]
    simp [zs, h2]

end Scalars

@[expose] def zsM (c : ZMod 2) (w : ↥W4) : ↥W4 := if c = 0 then 1 else w

theorem mul_self_P6 : ∀ y : P6, y * y = 1 := by decide +kernel

theorem w4_mul_self (w : ↥W4) : w * w = 1 := Subtype.ext (mul_self_P6 w)

theorem zsM_add (c d : ZMod 2) (w : ↥W4) : zsM (c + d) w = zsM c w * zsM d w := by
  rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases d with rfl | rfl
  · simp [zsM]
  · simp [zsM]
  · simp [zsM]
  · rw [show (1 + 1 : ZMod 2) = 0 from rfl]
    simp [zsM, w4_mul_self]

theorem add_self_fun (u : ↥W4 → ZMod 2) : u + u = 0 := by
  funext w
  simp only [Pi.add_apply, Pi.zero_apply]
  rcases zmod_two_cases (u w) with h | h <;> rw [h] <;> decide

theorem act4_mul_apply (σ τ : Perm (Fin 6)) (w : ↥W4) :
    act4 (σ * τ) w = act4 σ (act4 τ w) := by
  rw [map_mul, MulAut.mul_apply]

theorem act4_inv_apply (σ : Perm (Fin 6)) (w : ↥W4) : act4 σ⁻¹ (act4 σ w) = w := by
  rw [← act4_mul_apply, inv_mul_cancel, map_one, MulAut.one_apply]

theorem act4_apply_inv (σ : Perm (Fin 6)) (w : ↥W4) : act4 σ (act4 σ⁻¹ w) = w := by
  rw [← act4_mul_apply, mul_inv_cancel, map_one, MulAut.one_apply]

theorem coe_act4 (σ : Perm (Fin 6)) (w : ↥W4) : ((act4 σ w : ↥W4) : P6) = act4f σ w := rfl

@[expose] noncomputable def uact (σ : Perm (Fin 6)) (u : ↥W4 → ZMod 2) : ↥W4 → ZMod 2 :=
  fun w => u (act4 σ⁻¹ w)

theorem uact_add (σ : Perm (Fin 6)) (u u' : ↥W4 → ZMod 2) :
    uact σ (u + u') = uact σ u + uact σ u' := rfl

theorem uact_single (σ : Perm (Fin 6)) (w : ↥W4) (c : ZMod 2) :
    uact σ (Pi.single w c) = Pi.single (act4 σ w) c := by
  funext w'
  simp only [uact, Pi.single_apply]
  by_cases h : w' = act4 σ w
  · rw [ite_eq_left h, ite_eq_left (by rw [h, act4_inv_apply])]
  · rw [ite_eq_right h, ite_eq_right]
    intro h'
    exact h (by rw [← h', act4_apply_inv])

theorem single_apply_coe (a w : ↥W4) :
    (Pi.single a (1 : ZMod 2) : ↥W4 → ZMod 2) w = if (w : P6) = a then 1 else 0 := by
  rw [Pi.single_apply]
  exact if_congr Subtype.coe_inj.symm rfl rfl

@[expose] def d45 : ↥W4 := ⟨dv 4 5, dv_mem 4 5⟩

@[expose] def d34 : ↥W4 := ⟨dv 3 4, dv_mem 3 4⟩

@[expose] def d01 : ↥W4 := ⟨dv 0 1, dv_mem 0 1⟩

@[expose] def d02 : ↥W4 := ⟨dv 0 2, dv_mem 0 2⟩

theorem dv_eq_dv45 : ∀ a b : Fin 6, dv a b = dv 4 5 → (a : ℕ) / 2 = 2 ∧ (b : ℕ) / 2 = 2 := by
  decide +kernel

theorem mem_P1sub_of_act4 {σ : Perm (Fin 6)} (h : act4 σ d45 = d45) : σ ∈ P1sub := by
  have h1 : act4f σ (dv 4 5) = dv 4 5 := congrArg Subtype.val h
  rw [act4f_dv] at h1
  exact dv_eq_dv45 _ _ h1

theorem dv45_ne_one : dv 4 5 ≠ 1 := by decide +kernel

theorem d45_ne_one : d45 ≠ 1 := fun h => dv45_ne_one (congrArg Subtype.val h)

theorem dot_34_45 : dot (dv 3 4) (dv 4 5) = 1 := by decide +kernel

section Points

variable {M : Type} [AddCommGroup M] (ρ : ↥(alternatingGroup (Fin 6)) →* AddMonoid.End M)

theorem rho_mul (g h : ↥(alternatingGroup (Fin 6))) (m : M) : ρ (g * h) m = ρ g (ρ h m) := by
  rw [map_mul]; rfl

theorem rho_one (m : M) : ρ 1 m = m := by
  rw [map_one]; rfl

theorem map_zs (g : ↥(alternatingGroup (Fin 6))) (c : ZMod 2) (m : M) :
    ρ g (zs c m) = zs c (ρ g m) := by
  unfold zs
  split_ifs <;> simp

variable (x : M)

@[expose] noncomputable def xw (w : ↥W4) : M :=
  if h : ∃ g : ↥(alternatingGroup (Fin 6)), act4 (g : Perm (Fin 6)) d45 = w then ρ h.choose x
  else 0

@[expose] noncomputable def phiF (u : ↥W4 → ZMod 2) : M := ∑ w, zs (u w) (xw ρ x w)

theorem phiF_add (h2 : ∀ m : M, m + m = 0) (u u' : ↥W4 → ZMod 2) :
    phiF ρ x (u + u') = phiF ρ x u + phiF ρ x u' := by
  simp only [phiF, Pi.add_apply, zs_add h2, Finset.sum_add_distrib]

theorem phiF_single (w : ↥W4) : phiF ρ x (Pi.single w 1) = xw ρ x w := by
  simp only [phiF, Pi.single_apply]
  rw [Finset.sum_eq_single w]
  · simp [zs]
  · intro j _ hj
    simp [zs, hj]
  · simp

@[expose] noncomputable def phiHom (h2 : ∀ m : M, m + m = 0) : (↥W4 → ZMod 2) →+ M where
  toFun := phiF ρ x
  map_zero' := by simp [phiF, zs]
  map_add' := phiF_add ρ x h2

theorem phiHom_apply (h2 : ∀ m : M, m + m = 0) (u : ↥W4 → ZMod 2) :
    phiHom ρ x h2 u = phiF ρ x u := rfl

variable {ρ x}
variable (hx : ∀ g : ↥(alternatingGroup (Fin 6)), (g : Perm (Fin 6)) ∈ P1sub → ρ g x = x)
include hx

theorem rho_eq_of_act4 {g g' : ↥(alternatingGroup (Fin 6))}
    (h : act4 (g : Perm (Fin 6)) d45 = act4 (g' : Perm (Fin 6)) d45) : ρ g x = ρ g' x := by
  have hm : ((g⁻¹ * g' : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) ∈ P1sub := by
    apply mem_P1sub_of_act4
    rw [Subgroup.coe_mul, Subgroup.coe_inv, act4_mul_apply, ← h, act4_inv_apply]
  calc ρ g x = ρ g (ρ (g⁻¹ * g') x) := by rw [hx _ hm]
    _ = ρ g' x := by rw [← rho_mul, mul_inv_cancel_left]

theorem rho_eq_xw (g : ↥(alternatingGroup (Fin 6))) :
    ρ g x = xw ρ x (act4 (g : Perm (Fin 6)) d45) := by
  have h : ∃ g' : ↥(alternatingGroup (Fin 6)),
      act4 (g' : Perm (Fin 6)) d45 = act4 (g : Perm (Fin 6)) d45 := ⟨g, rfl⟩
  rw [xw, dite_eq_left h]
  exact rho_eq_of_act4 hx h.choose_spec.symm

theorem xw_act4 (g : ↥(alternatingGroup (Fin 6))) (w : ↥W4) :
    xw ρ x (act4 (g : Perm (Fin 6)) w) = ρ g (xw ρ x w) := by
  by_cases hw : ∃ g' : ↥(alternatingGroup (Fin 6)), act4 (g' : Perm (Fin 6)) d45 = w
  · obtain ⟨g', rfl⟩ := hw
    rw [← rho_eq_xw hx g', ← act4_mul_apply, ← Subgroup.coe_mul, ← rho_eq_xw hx, rho_mul]
  · have hw' : ¬ ∃ g' : ↥(alternatingGroup (Fin 6)),
        act4 (g' : Perm (Fin 6)) d45 = act4 (g : Perm (Fin 6)) w := by
      rintro ⟨g', hg'⟩
      refine hw ⟨g⁻¹ * g', ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv, act4_mul_apply, hg', act4_inv_apply]
    unfold xw
    rw [dite_eq_right hw', dite_eq_right hw, map_zero]

theorem phiF_uact (g : ↥(alternatingGroup (Fin 6))) (u : ↥W4 → ZMod 2) :
    phiF ρ x (uact (g : Perm (Fin 6)) u) = ρ g (phiF ρ x u) := by
  simp only [phiF, uact, map_sum, map_zs]
  refine Fintype.sum_bijective (act4 (g : Perm (Fin 6))⁻¹) (act4 (g : Perm (Fin 6))⁻¹).bijective
    _ _ fun w => ?_
  rw [← xw_act4 hx, act4_apply_inv]

end Points

@[expose] def epsM (u : ↥W4 → ZMod 2) : ↥W4 := ∏ w, zsM (u w) w

theorem epsM_add (u u' : ↥W4 → ZMod 2) : epsM (u + u') = epsM u * epsM u' := by
  simp only [epsM, Pi.add_apply, zsM_add, Finset.prod_mul_distrib]

theorem epsM_zero : epsM 0 = 1 := by
  simp [epsM, zsM]

theorem epsM_single (w : ↥W4) : epsM (Pi.single w 1) = w := by
  simp only [epsM, Pi.single_apply]
  rw [Finset.prod_eq_single w]
  · simp [zsM]
  · intro j _ hj
    simp [zsM, hj]
  · simp

theorem map_zsM (σ : Perm (Fin 6)) (c : ZMod 2) (w : ↥W4) :
    act4 σ (zsM c w) = zsM c (act4 σ w) := by
  unfold zsM
  split_ifs <;> simp

theorem epsM_uact (σ : Perm (Fin 6)) (u : ↥W4 → ZMod 2) :
    epsM (uact σ u) = act4 σ (epsM u) := by
  simp only [epsM, uact, map_prod, map_zsM]
  exact Fintype.prod_bijective (act4 σ⁻¹) (act4 σ⁻¹).bijective _ _ fun w => by
    rw [act4_apply_inv]

@[expose] def epsHom : (↥W4 → ZMod 2) →+ Additive ↥W4 where
  toFun u := Additive.ofMul (epsM u)
  map_zero' := by rw [epsM_zero]; rfl
  map_add' u u' := by rw [epsM_add]; rfl

theorem dot_mul_left (a b z : P6) : dot (a * b) z = dot a z + dot b z := by
  simp only [dot, toAdd_mul, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dot_one_left (z : P6) : dot 1 z = 0 := by
  simp [dot]

theorem dot_zsM (c : ZMod 2) (w : ↥W4) (z : P6) :
    dot ((zsM c w : ↥W4) : P6) z = c * dot (w : P6) z := by
  rcases zmod_two_cases c with rfl | rfl
  · simp [zsM, dot_one_left]
  · simp [zsM]

theorem dot_prod_zsM (v : ↥W4 → ZMod 2) (z : P6) (s : Finset ↥W4) :
    dot ((∏ w ∈ s, zsM (v w) w : ↥W4) : P6) z = ∑ w ∈ s, v w * dot (w : P6) z := by
  refine Finset.induction_on s ?_ ?_
  · simp [dot_one_left]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Subgroup.coe_mul, dot_mul_left, ih,
      dot_zsM]

theorem dot_epsM (v : ↥W4 → ZMod 2) (z : P6) :
    dot ((epsM v : ↥W4) : P6) z = ∑ w, v w * dot (w : P6) z :=
  dot_prod_zsM v z Finset.univ

@[expose] def chiA (y : P6) : ZMod 2 :=
  if y = dv 0 4 ∨ y = dv 1 4 ∨ y = dv 2 4 ∨ y = dv 3 4 then 1 else 0

@[expose] def chiB (y : P6) : ZMod 2 :=
  if y = dv 0 5 ∨ y = dv 1 5 ∨ y = dv 2 5 ∨ y = dv 3 5 then 1 else 0

theorem dot_dv45 : ∀ w : P6, InW4 w → dot w (dv 4 5) = chiA w + chiB w := by
  decide +kernel

@[expose] def kA : Perm (Fin 6) := swap 0 1 * swap 2 3

@[expose] def kB : Perm (Fin 6) := swap 0 2 * swap 1 3

@[expose] def kC : Perm (Fin 6) := swap 0 3 * swap 1 2

@[expose] def tAB : Perm (Fin 6) := swap 0 1 * swap 4 5

@[expose] def hStep : Perm (Fin 6) := swap 0 1 * swap 3 5

theorem gens_mem : kA ∈ alternatingGroup (Fin 6) ∧ kB ∈ alternatingGroup (Fin 6) ∧
    kC ∈ alternatingGroup (Fin 6) ∧ tAB ∈ alternatingGroup (Fin 6) ∧
    hStep ∈ alternatingGroup (Fin 6) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem coef_K : ∀ w0 : P6, InW4 w0 → ∀ w : P6, InW4 w →
    ((if w = w0 then 1 else 0) + (if w = act4f kA⁻¹ w0 then 1 else 0) +
      (if w = act4f kB⁻¹ w0 then 1 else 0) + (if w = act4f kC⁻¹ w0 then 1 else 0) : ZMod 2) =
      chiA w * chiA w0 + chiB w * chiB w0 := by
  decide +kernel

theorem chiA_hStep : ∀ w : P6, InW4 w →
    chiA w + chiA (act4f hStep⁻¹ w) =
      (if w = dv 3 4 then 1 else 0) + (if w = dv 4 5 then 1 else 0) := by
  decide +kernel

theorem chiB_tAB : ∀ w : P6, InW4 w → chiB (act4f tAB⁻¹ w) = chiA w := by
  decide +kernel

@[expose] def Lb : List (Perm (Fin 6)) :=
  [1, swap 0 4 * swap 2 3, swap 1 4 * swap 2 3, swap 2 4 * swap 0 1]

theorem Lb_mem : ∀ σ ∈ Lb, σ ∈ alternatingGroup (Fin 6) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem exists_Lb : ∀ y : P6, InW4 y → y ≠ 1 → ∃ σ ∈ Lb, dot (act4f σ y) (dv 4 5) = 1 := by
  decide +kernel

theorem exists_common : ∀ w : P6, InW4 w → w ≠ 1 → w ≠ dv 4 5 → dot w (dv 4 5) = 0 →
    ∃ c : P6, InW4 c ∧ dot w c = 1 ∧ dot c (dv 4 5) = 1 := by
  decide +kernel

theorem norm_apply (v : ↥W4 → ZMod 2) (w0 : ↥W4) :
    (v + uact kA v + uact kB v + uact kC v) w0 =
      (∑ w, v w * chiA w) * chiA w0 + (∑ w, v w * chiB w) * chiB w0 := by
  have e : ∀ z : ↥W4, v z = ∑ w, v w * (if (w : P6) = z then 1 else 0) := by
    intro z
    simp only [Subtype.coe_inj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  simp only [Pi.add_apply, uact]
  rw [e w0, e (act4 kA⁻¹ w0), e (act4 kB⁻¹ w0), e (act4 kC⁻¹ w0), ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hc : ((if (w : P6) = w0 then 1 else 0) +
      (if (w : P6) = ((act4 kA⁻¹ w0 : ↥W4) : P6) then 1 else 0) +
      (if (w : P6) = ((act4 kB⁻¹ w0 : ↥W4) : P6) then 1 else 0) +
      (if (w : P6) = ((act4 kC⁻¹ w0 : ↥W4) : P6) then 1 else 0) : ZMod 2) =
      chiA w * chiA w0 + chiB w * chiB w0 :=
    coef_K w0 w0.2 w w.2
  linear_combination v w * hc

section Core

variable (N : AddSubgroup (↥W4 → ZMod 2))

theorem cA_mem (hN : ∀ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) → ∀ u ∈ N, uact σ u ∈ N)
    {u : ↥W4 → ZMod 2} (hu : u ∈ N) (hne : epsM u ≠ 1) :
    (fun w : ↥W4 => chiA (w : P6)) ∈ N := by
  have hy : ((epsM u : ↥W4) : P6) ≠ 1 := fun h => hne (Subtype.ext h)
  obtain ⟨σ, hσL, hσ⟩ := exists_Lb _ (epsM u).2 hy
  obtain ⟨v, hvN, hdot⟩ : ∃ v ∈ N, dot ((epsM v : ↥W4) : P6) (dv 4 5) = 1 :=
    ⟨uact σ u, hN σ (Lb_mem σ hσL) u hu, by rw [epsM_uact, coe_act4]; exact hσ⟩
  rw [dot_epsM] at hdot
  have hsum : (∑ w, v w * chiA w) + (∑ w, v w * chiB w) = 1 := by
    rw [← hdot, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [dot_dv45 w w.2, mul_add]
  obtain ⟨hA, hB, hC, hT, -⟩ := gens_mem
  have hnorm : v + uact kA v + uact kB v + uact kC v ∈ N :=
    N.add_mem (N.add_mem (N.add_mem hvN (hN _ hA v hvN)) (hN _ hB v hvN)) (hN _ hC v hvN)
  rcases zmod_two_cases (∑ w, v w * chiA w) with h0 | h1
  · have hb : ∑ w, v w * chiB w = 1 := by
      rw [h0] at hsum
      linear_combination hsum
    have heq : v + uact kA v + uact kB v + uact kC v = fun w : ↥W4 => chiB (w : P6) := by
      funext w0
      rw [norm_apply, h0, hb, zero_mul, zero_add, one_mul]
    rw [heq] at hnorm
    have := hN _ hT _ hnorm
    convert this using 1
    funext w
    exact (chiB_tAB w w.2).symm
  · have hb : ∑ w, v w * chiB w = 0 := by
      rw [h1] at hsum
      linear_combination hsum
    have heq : v + uact kA v + uact kB v + uact kC v = fun w : ↥W4 => chiA (w : P6) := by
      funext w0
      rw [norm_apply, h1, hb, zero_mul, add_zero, one_mul]
    rwa [heq] at hnorm

theorem pair_mem (hN : ∀ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) → ∀ u ∈ N, uact σ u ∈ N)
    (hA : (fun w : ↥W4 => chiA (w : P6)) ∈ N) : Pi.single d34 1 + Pi.single d45 1 ∈ N := by
  have h := N.add_mem hA (hN _ gens_mem.2.2.2.2 _ hA)
  convert h using 1
  funext w
  simp only [Pi.add_apply, uact]
  rw [single_apply_coe, single_apply_coe]
  exact (chiA_hStep w w.2).symm

theorem meet_mem (hN : ∀ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) → ∀ u ∈ N, uact σ u ∈ N)
    (h : Pi.single d34 1 + Pi.single d45 1 ∈ N) (a b : ↥W4) (hab : dot (a : P6) b = 1) :
    Pi.single a 1 + Pi.single b 1 ∈ N := by
  obtain ⟨σ₁, hs₁, h₁a, h₁b⟩ := trans_tri (dv 3 4) (dv 4 5) (dv_mem 3 4) (dv_mem 4 5) dot_34_45
  obtain ⟨σ₂, hs₂, h₂a, h₂b⟩ := trans_tri a b a.2 b.2 hab
  have hg : σ₂ * σ₁⁻¹ ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs₁, hs₂, inv_one, mul_one]
  have h' := hN _ hg _ h
  rw [uact_add, uact_single, uact_single] at h'
  have e1 : act4 (σ₂ * σ₁⁻¹) d34 = a := by
    have h1 : act4 σ₁ d01 = d34 := Subtype.ext h₁a
    rw [act4_mul_apply, ← h1, act4_inv_apply]
    exact Subtype.ext h₂a
  have e2 : act4 (σ₂ * σ₁⁻¹) d45 = b := by
    have h1 : act4 σ₁ d02 = d45 := Subtype.ext h₁b
    rw [act4_mul_apply, ← h1, act4_inv_apply]
    exact Subtype.ext h₂b
  rwa [e1, e2] at h'

theorem all_mem (hN : ∀ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) → ∀ u ∈ N, uact σ u ∈ N)
    (h : Pi.single d34 1 + Pi.single d45 1 ∈ N) (w : ↥W4) (hw : w ≠ 1) :
    Pi.single w 1 + Pi.single d45 1 ∈ N := by
  by_cases hd : w = d45
  · rw [hd, add_self_fun]
    exact N.zero_mem
  rcases zmod_two_cases (dot (w : P6) (dv 4 5)) with h0 | h1
  · have hw1 : (w : P6) ≠ 1 := fun h' => hw (Subtype.ext h')
    have hw2 : (w : P6) ≠ dv 4 5 := fun h' => hd (Subtype.ext h')
    obtain ⟨c, hc, hwc, hcd⟩ := exists_common _ w.2 hw1 hw2 h0
    have hc' : c ∈ W4 := hc
    have m := N.add_mem (meet_mem N hN h w ⟨c, hc'⟩ hwc) (meet_mem N hN h ⟨c, hc'⟩ d45 hcd)
    have e : (Pi.single w 1 + Pi.single ⟨c, hc'⟩ 1 + (Pi.single ⟨c, hc'⟩ 1 + Pi.single d45 1) :
        ↥W4 → ZMod 2) = Pi.single w 1 + Pi.single d45 1 +
          (Pi.single ⟨c, hc'⟩ 1 + Pi.single ⟨c, hc'⟩ 1) := by abel
    rwa [e, add_self_fun, add_zero] at m
  · exact meet_mem N hN h w d45 h1

end Core

section Main

variable {M : Type} [AddCommGroup M] {ρ : ↥(alternatingGroup (Fin 6)) →* AddMonoid.End M} {x : M}

theorem eps_eq_one_of_phi (h2 : ∀ m : M, m + m = 0)
    (hx : ∀ g : ↥(alternatingGroup (Fin 6)), (g : Perm (Fin 6)) ∈ P1sub → ρ g x = x)
    (hnf : ∃ g : ↥(alternatingGroup (Fin 6)), ρ g x ≠ x) (u : ↥W4 → ZMod 2)
    (hu : phiF ρ x u = 0) : epsM u = 1 := by
  by_contra hne
  set N := (phiHom ρ x h2).ker with hNdef
  have hN : ∀ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) → ∀ u ∈ N, uact σ u ∈ N := by
    intro σ hσ u' hu'
    rw [AddMonoidHom.mem_ker, phiHom_apply] at hu' ⊢
    have e : phiF ρ x (uact σ u') = ρ ⟨σ, hσ⟩ (phiF ρ x u') := phiF_uact hx ⟨σ, hσ⟩ u'
    rw [e, hu', map_zero]
  have hpair := pair_mem N hN (cA_mem N hN (show u ∈ N from hu) hne)
  obtain ⟨g, hg⟩ := hnf
  apply hg
  have hgd : act4 (g : Perm (Fin 6)) d45 ≠ 1 := by
    intro h
    apply d45_ne_one
    rw [← act4_inv_apply (g : Perm (Fin 6)) d45, h, map_one]
  have h1 := all_mem N hN hpair _ hgd
  rw [AddMonoidHom.mem_ker, map_add, phiHom_apply, phiHom_apply, phiF_single, phiF_single] at h1
  have hd : xw ρ x d45 = x := by
    have := rho_eq_xw hx 1
    rw [rho_one, Subgroup.coe_one, map_one, MulAut.one_apply] at this
    exact this.symm
  rw [rho_eq_xw hx g]
  calc xw ρ x (act4 (g : Perm (Fin 6)) d45)
      = xw ρ x (act4 (g : Perm (Fin 6)) d45) + (xw ρ x d45 + xw ρ x d45) := by
        rw [h2, add_zero]
    _ = xw ρ x d45 := by rw [← add_assoc, h1, zero_add]
    _ = x := hd

theorem top_core (h2 : ∀ m : M, m + m = 0)
    (hx : ∀ g : ↥(alternatingGroup (Fin 6)), (g : Perm (Fin 6)) ∈ P1sub → ρ g x = x)
    (hnf : ∃ g : ↥(alternatingGroup (Fin 6)), ρ g x ≠ x)
    (hgen : AddSubgroup.closure (Set.range fun g : ↥(alternatingGroup (Fin 6)) => ρ g x) = ⊤) :
    ∃ f : M →+ Additive ↥W4, Function.Surjective f ∧
      ∀ (g : ↥(alternatingGroup (Fin 6))) (m : M),
        f (ρ g m) = Additive.ofMul (act4 (g : Perm (Fin 6)) (Additive.toMul (f m))) := by
  set Φ := phiHom ρ x h2 with hΦ
  have hsurj : Function.Surjective Φ := by
    rw [← AddMonoidHom.range_eq_top, eq_top_iff, ← hgen, AddSubgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨Pi.single (act4 (g : Perm (Fin 6)) d45) 1, by
      rw [hΦ, phiHom_apply, phiF_single, ← rho_eq_xw hx]⟩
  have hle : Φ.ker ≤ epsHom.ker := fun u hu => by
    rw [AddMonoidHom.mem_ker] at hu ⊢
    have := eps_eq_one_of_phi h2 hx hnf u hu
    show Additive.ofMul (epsM u) = 0
    rw [this]
    rfl
  set q := QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurj with hq
  set f : M →+ Additive ↥W4 :=
    (QuotientAddGroup.lift Φ.ker epsHom hle).comp q.symm.toAddMonoidHom with hf
  have hfΦ : ∀ u, f (Φ u) = Additive.ofMul (epsM u) := by
    intro u
    have h1 : q.symm (Φ u) = (u : (↥W4 → ZMod 2) ⧸ Φ.ker) := by
      rw [AddEquiv.symm_apply_eq]
      rfl
    simp only [hf, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h1,
      QuotientAddGroup.lift_mk]
    rfl
  refine ⟨f, fun a => ⟨Φ (Pi.single (Additive.toMul a) 1), by rw [hfΦ, epsM_single]; rfl⟩,
    fun g m => ?_⟩
  obtain ⟨u, rfl⟩ := hsurj m
  have h1 : ρ g (Φ u) = Φ (uact (g : Perm (Fin 6)) u) := by
    rw [hΦ, phiHom_apply, phiHom_apply, phiF_uact hx]
  rw [h1, hfΦ, hfΦ, epsM_uact]
  rfl

end Main

end G53

theorem AS_I_G_5_3_top_holds :
    ∀ (M : Type) [AddCommGroup M] [Finite M] (ρ : ↥(alternatingGroup (Fin 6)) →* AddMonoid.End M),
      (∀ m : M, m + m = 0) → ∀ x : M,
      (∀ g : ↥(alternatingGroup (Fin 6)),
        (g : Equiv.Perm (Fin 6)) ∈ CFSG.Quasithin.H13.A6.P1sub → ρ g x = x) →
      (∃ g, ρ g x ≠ x) →
      AddSubgroup.closure (Set.range fun g => ρ g x) = ⊤ →
      ∃ f : M →+ Additive ↥CFSG.Quasithin.H13.A6.W4, Function.Surjective f ∧
        ∀ (g : ↥(alternatingGroup (Fin 6))) (m : M),
          f (ρ g m) = Additive.ofMul
            (CFSG.Quasithin.H13.A6.act4 (g : Equiv.Perm (Fin 6)) (Additive.toMul (f m))) := by
  intro M _ _ ρ h2 x hx hnf hgen
  exact G53.top_core h2 hx hnf hgen

end CFSG.Quasithin.VolI
