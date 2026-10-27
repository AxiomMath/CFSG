module

public import CFSG.LocalAnalysis.StandardType.GGHalfGraphAgree
public import CFSG.LocalAnalysis.StandardType.GGHalfGraphTheta
public import CFSG.LieType.Universal.SpecialLinearRoots.SignedPerm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement

namespace GGHalfCtx

private abbrev I6 := Fin (Tag.rank .E6)
private abbrev J6 := Fin 6

private theorem ggHalfGraphClosure_cartan_symm (i j : I6) : Tag.cartan .E6 i j = Tag.cartan .E6 j i := by
  fin_cases i <;> fin_cases j <;> decide

private theorem ggHalfGraphClosure_ggE6ip_symm (u v : GGE6Root) : ggE6ip u v = ggE6ip v u := by
  simp only [ggE6ip]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [ggHalfGraphClosure_cartan_symm b a]
  ring

private theorem ggHalfGraphClosure_ggE6ip_add_left (u u' v : GGE6Root) :
    ggE6ip (u + u') v = ggE6ip u v + ggE6ip u' v := by
  simp only [ggE6ip, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem ggHalfGraphClosure_ggE6ip_add_right (u v v' : GGE6Root) :
    ggE6ip u (v + v') = ggE6ip u v + ggE6ip u v' := by
  simp only [ggE6ip, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem ggHalfGraphClosure_ggE6ip_smul_left (c : ℤ) (u v : GGE6Root) :
    ggE6ip (c • u) v = c * ggE6ip u v := by
  simp only [ggE6ip, Pi.smul_apply, smul_eq_mul]
  trans ∑ x, c * (∑ i, u x * Tag.cartan .E6 x i * v i)
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [← Finset.mul_sum]

private theorem ggHalfGraphClosure_ggE6ip_smul_right (c : ℤ) (u v : GGE6Root) :
    ggE6ip u (c • v) = c * ggE6ip u v := by
  rw [ggHalfGraphClosure_ggE6ip_symm, ggHalfGraphClosure_ggE6ip_smul_left, ggHalfGraphClosure_ggE6ip_symm]

private theorem ggHalfGraphClosure_ggE6ip_neg_left (u v : GGE6Root) : ggE6ip (-u) v = - ggE6ip u v := by
  simpa using ggHalfGraphClosure_ggE6ip_smul_left (-1) u v

private theorem ggHalfGraphClosure_ggE6ip_neg_right (u v : GGE6Root) : ggE6ip u (-v) = - ggE6ip u v := by
  simpa using ggHalfGraphClosure_ggE6ip_smul_right (-1) u v

private theorem ggHalfGraphClosure_ggE6ip_single_right (v : GGE6Root) (i : I6) :
    ggE6ip v (Pi.single i 1) = ∑ j, Tag.cartan .E6 i j * v j := by
  simp only [ggE6ip]
  trans ∑ a, v a * Tag.cartan .E6 a i
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_eq_of_ne hb])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp [Pi.single_eq_same]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [ggHalfGraphClosure_cartan_symm a i]; ring

private theorem ggHalfGraphClosure_ggE6Refl_single (i : I6) (v : GGE6Root) :
    ggE6Refl (Pi.single i 1) v = reflect .E6 i v := by
  simp only [ggE6Refl, reflect, ggHalfGraphClosure_ggE6ip_single_right]

private theorem ggHalfGraphClosure_ggE6ip_reflect_left (i : I6) (u v : GGE6Root) :
    ggE6ip (reflect .E6 i u) v = ggE6ip u (reflect .E6 i v) := by
  simp only [reflect]
  rw [sub_eq_add_neg, sub_eq_add_neg, ggHalfGraphClosure_ggE6ip_add_left, ggHalfGraphClosure_ggE6ip_add_right]
  congr 1
  rw [ggHalfGraphClosure_ggE6ip_neg_left, ggHalfGraphClosure_ggE6ip_neg_right, ggHalfGraphClosure_ggE6ip_smul_left, ggHalfGraphClosure_ggE6ip_smul_right]
  rw [ggHalfGraphClosure_ggE6ip_symm (Pi.single i 1) v, ggHalfGraphClosure_ggE6ip_single_right v i, ggHalfGraphClosure_ggE6ip_single_right u i]
  ring

private theorem ggHalfGraphClosure_reflect_sub (i : I6) (u v : GGE6Root) :
    reflect .E6 i (u - v) = reflect .E6 i u - reflect .E6 i v := by
  rw [← reflectHom_apply, ← reflectHom_apply, ← reflectHom_apply, map_sub]

private theorem ggHalfGraphClosure_reflect_smul (i : I6) (c : ℤ) (u : GGE6Root) :
    reflect .E6 i (c • u) = c • reflect .E6 i u := by
  rw [← reflectHom_apply, ← reflectHom_apply, map_zsmul]

private theorem ggHalfGraphClosure_ggE6Refl_reflect (i : I6) (g r : GGE6Root) :
    ggE6Refl (reflect .E6 i g) r = reflect .E6 i (ggE6Refl g (reflect .E6 i r)) := by
  rw [ggE6Refl, ggE6Refl]
  rw [ggHalfGraphClosure_reflect_sub, ggHalfGraphClosure_reflect_smul, reflect_reflect, ggHalfGraphClosure_ggE6ip_reflect_left]

private theorem ggHalfGraphClosure_isRoot_refl (g r : GGE6Root) (hg : IsRoot .E6 g) (hr : IsRoot .E6 r) :
    IsRoot .E6 (ggE6Refl g r) := by
  induction hg generalizing r with
  | basis j =>
    rw [ggHalfGraphClosure_ggE6Refl_single]
    exact hr.reflect j
  | @reflect i g' hg' ih =>
    rw [ggHalfGraphClosure_ggE6Refl_reflect]
    exact (ih (reflect .E6 i r) (hr.reflect i)).reflect i

private theorem ggHalfGraphClosure_isRoot_neg (g : GGE6Root) (hg : IsRoot .E6 g) : IsRoot .E6 (-g) := by
  induction hg with
  | basis i => exact isRoot_neg_single .E6 i
  | @reflect i v hv ih =>
    rw [show -reflect .E6 i v = reflect .E6 i (-v) by
      rw [← reflectHom_apply, ← reflectHom_apply, map_neg]]
    exact ih.reflect i

private theorem ggHalfGraphClosure_isSign_eq_one_f2 {σ : F2} (h : IsSign σ) : σ = 1 := by
  rcases h with h | h
  · exact h
  · rw [h, CharTwo.neg_eq]

private theorem ggHalfGraphClosure_nt_one (i : I6) :
    e6Data_valid.nt F2 i 1 =
      ggE6x (Pi.single i 1) * ggE6x (-Pi.single i 1) * ggE6x (Pi.single i 1) := by
  unfold CFSG.LieType.Steinberg.Minuscule.MinData.Valid.nt
  simp only [ggE6x, inv_one, Units.val_one]
  rw [CharTwo.neg_eq (1 : F2)]

private theorem ggHalfGraphClosure_nm_eq (i : I6) :
    e6Data_valid.nm F2 i =
      ggE6x (Pi.single i 1) * ggE6x (-Pi.single i 1) * ggE6x (Pi.single i 1) := by
  unfold CFSG.LieType.Steinberg.Minuscule.MinData.Valid.nm
  exact ggHalfGraphClosure_nt_one i

private theorem ggHalfGraphClosure_nm_conj_one (i : I6) (r : GGE6Root) (hr : IsRoot .E6 r) :
    e6Data_valid.nm F2 i * ggE6x r * (e6Data_valid.nm F2 i)⁻¹
      = ggE6x (reflect .E6 i r) := by
  obtain ⟨σ, hσ, h⟩ := e6Data_valid.nm_conj_xm F2 hr i
  have hσ1 : σ = 1 := ggHalfGraphClosure_isSign_eq_one_f2 hσ
  simpa [hσ1, ggE6x] using h 1

private theorem ggHalfGraphClosure_nm_conj_inv (i : I6) (r : GGE6Root) (hr : IsRoot .E6 r) :
    (e6Data_valid.nm F2 i)⁻¹ * ggE6x r * e6Data_valid.nm F2 i
      = ggE6x (reflect .E6 i r) := by
  have h := ggHalfGraphClosure_nm_conj_one i (reflect .E6 i r) (hr.reflect i)
  rw [reflect_reflect] at h
  rw [← h]
  group

private theorem ggHalfGraphClosure_n_reflect (i : I6) (g : GGE6Root) (hg : IsRoot .E6 g) :
    ggE6x (reflect .E6 i g) * ggE6x (-reflect .E6 i g) * ggE6x (reflect .E6 i g) =
      e6Data_valid.nm F2 i * (ggE6x g * ggE6x (-g) * ggE6x g) * (e6Data_valid.nm F2 i)⁻¹ := by
  have hneg : -reflect .E6 i g = reflect .E6 i (-g) := by
    rw [← reflectHom_apply, ← reflectHom_apply, map_neg]
  rw [hneg, ← ggHalfGraphClosure_nm_conj_one i g hg, ← ggHalfGraphClosure_nm_conj_one i (-g) (ggHalfGraphClosure_isRoot_neg g hg)]
  group

private theorem ggHalfGraphClosure_conj_refl (g r : GGE6Root) (hg : IsRoot .E6 g) (hr : IsRoot .E6 r) :
    (ggE6x g * ggE6x (-g) * ggE6x g) * ggE6x r * (ggE6x g * ggE6x (-g) * ggE6x g)⁻¹
      = ggE6x (ggE6Refl g r) := by
  induction hg generalizing r with
  | basis i =>
    rw [ggHalfGraphClosure_ggE6Refl_single, ← ggHalfGraphClosure_nm_eq i]
    exact ggHalfGraphClosure_nm_conj_one i r hr
  | @reflect i g' hg' ih =>
    rw [ggHalfGraphClosure_ggE6Refl_reflect, ggHalfGraphClosure_n_reflect i g' hg']
    have hgrp : (e6Data_valid.nm F2 i * (ggE6x g' * ggE6x (-g') * ggE6x g') *
          (e6Data_valid.nm F2 i)⁻¹) * ggE6x r *
          (e6Data_valid.nm F2 i * (ggE6x g' * ggE6x (-g') * ggE6x g') *
            (e6Data_valid.nm F2 i)⁻¹)⁻¹ =
        e6Data_valid.nm F2 i *
          ((ggE6x g' * ggE6x (-g') * ggE6x g') * ggE6x (reflect .E6 i r) *
            (ggE6x g' * ggE6x (-g') * ggE6x g')⁻¹) *
          (e6Data_valid.nm F2 i)⁻¹ := by
      rw [show (e6Data_valid.nm F2 i * (ggE6x g' * ggE6x (-g') * ggE6x g') *
            (e6Data_valid.nm F2 i)⁻¹) * ggE6x r *
            (e6Data_valid.nm F2 i * (ggE6x g' * ggE6x (-g') * ggE6x g') *
              (e6Data_valid.nm F2 i)⁻¹)⁻¹ =
          e6Data_valid.nm F2 i *
            ((ggE6x g' * ggE6x (-g') * ggE6x g') *
              ((e6Data_valid.nm F2 i)⁻¹ * ggE6x r * e6Data_valid.nm F2 i) *
              (ggE6x g' * ggE6x (-g') * ggE6x g')⁻¹) *
            (e6Data_valid.nm F2 i)⁻¹ by group]
      rw [ggHalfGraphClosure_nm_conj_inv i r hr]
    rw [hgrp, ih (reflect .E6 i r) (hr.reflect i)]
    exact ggHalfGraphClosure_nm_conj_one i (ggE6Refl g' (reflect .E6 i r))
      (ggHalfGraphClosure_isRoot_refl g' (reflect .E6 i r) hg' (hr.reflect i))

private theorem ggHalfGraphClosure_slE_eq (c d : Fin 6) (hcd : c ≠ d) :
    slE c d = SpecialLinearGroup.transvection hcd (1 : F2) := by
  rw [slE, dif_neg hcd]

private theorem ggHalfGraphClosure_slE_swap_mul (a b : Fin 6) (hab : a ≠ b) :
    slE a b * slE b a * slE a b = slPerm gf2_two (Equiv.swap a b) := by
  rw [ggHalfGraphClosure_slE_eq a b hab, ggHalfGraphClosure_slE_eq b a hab.symm,
    slPerm_swap_eq_transvections gf2_two hab]

private theorem ggHalfGraphClosure_slPerm_conj_slE (π : Equiv.Perm (Fin 6)) (a b : Fin 6) (hab : a ≠ b) :
    slPerm gf2_two π * slE a b * (slPerm gf2_two π)⁻¹ = slE (π a) (π b) := by
  rw [ggHalfGraphClosure_slE_eq a b hab, ggHalfGraphClosure_slE_eq (π a) (π b) (π.injective.ne hab)]
  have h := conj_transvection_of_coe_eq_signedPerm (g := slPerm gf2_two π)
    (coe_slPerm gf2_two π) (fun s => by simp) hab (1 : F2)
  simpa using h

private theorem ggHalfGraphClosure_lab_self (b : GGHalfBlk) (c : Fin 6) : b.Lab (b.lab c) := by
  cases b <;> simp only [GGHalfBlk.Lab, GGHalfBlk.lab, GGHalfBlk.off] <;> omega

private theorem ggHalfGraphClosure_lab_inj (b : GGHalfBlk) : Function.Injective (b.lab) := by
  intro c d h
  have hv := congrArg Fin.val h
  simp only [GGHalfBlk.lab, GGHalfBlk.off] at hv
  exact Fin.ext (by omega)

private def ggHalfGraphClosure_labInv : (b : GGHalfBlk) → (a : Fin 8) → b.Lab a → Fin 6
  | .L, a, ha => ⟨a.val, ha⟩
  | .K, a, ha => ⟨a.val - 2, by have := a.isLt; simp only [GGHalfBlk.Lab] at ha; omega⟩
  | .M, a, ha => ⟨a.val - 2, by have := a.isLt; simp only [GGHalfBlk.Lab] at ha; omega⟩

private theorem ggHalfGraphClosure_lab_labInv (b : GGHalfBlk) (a : Fin 8) (ha : b.Lab a) :
    b.lab (ggHalfGraphClosure_labInv b a ha) = a := by
  cases b
  · apply Fin.ext; simp only [ggHalfGraphClosure_labInv, GGHalfBlk.lab, GGHalfBlk.off, Fin.val_mk]; omega
  · apply Fin.ext
    simp only [ggHalfGraphClosure_labInv, GGHalfBlk.lab, GGHalfBlk.off, Fin.val_mk]
    have h2 : 2 ≤ a.val := ha
    omega
  · apply Fin.ext
    simp only [ggHalfGraphClosure_labInv, GGHalfBlk.lab, GGHalfBlk.off, Fin.val_mk]
    have h2 : 2 ≤ a.val := ha
    omega

private theorem ggHalfGraphClosure_S_lab (c : Fin 6) :
    ggHalfS (GGHalfBlk.M.lab c) = GGHalfBlk.L.lab (ggHalfSLoc c) := by
  fin_cases c <;> decide

private theorem ggHalfGraphClosure_ip_sub_left (u u' v : GGE6Root) :
    ggE6ip (u - u') v = ggE6ip u v - ggE6ip u' v := by
  rw [sub_eq_add_neg, ggHalfGraphClosure_ggE6ip_add_left, ggHalfGraphClosure_ggE6ip_neg_left, sub_eq_add_neg]

private theorem ggHalfGraphClosure_ip_sub_right (u v v' : GGE6Root) :
    ggE6ip u (v - v') = ggE6ip u v - ggE6ip u v' := by
  rw [sub_eq_add_neg, ggHalfGraphClosure_ggE6ip_add_right, ggHalfGraphClosure_ggE6ip_neg_right, sub_eq_add_neg]

private theorem ggHalfGraphClosure_ip_self_root (r : GGE6Root) (hr : IsRoot .E6 r) : ggE6ip r r = 2 := by
  induction hr with
  | basis i => rw [ggHalfGraphClosure_ggE6ip_single_right, sum_cartan_mul_single]
  | @reflect i v hv ih => rw [ggHalfGraphClosure_ggE6ip_reflect_left i v (reflect .E6 i v), reflect_reflect, ih]

private noncomputable def ggHalfGraphClosure_hvec  (m : GGHalfE6Model) (b : GGHalfBlk) (x : J6) : GGE6Root :=
  if x = 0 then 0 else m.frame b (b.lab x) (b.lab 0)

private theorem ggHalfGraphClosure_hvec_zero (m : GGHalfE6Model) (b : GGHalfBlk) : ggHalfGraphClosure_hvec m b 0 = 0 := by
  simp [ggHalfGraphClosure_hvec]

private theorem ggHalfGraphClosure_hvec_self (m : GGHalfE6Model) (b : GGHalfBlk) (hm : m.FrameOK b)
    (x : J6) (hx : x ≠ 0) : ggE6ip (ggHalfGraphClosure_hvec m b x) (ggHalfGraphClosure_hvec m b x) = 2 := by
  rw [show ggHalfGraphClosure_hvec m b x = m.frame b (b.lab x) (b.lab 0) by simp [ggHalfGraphClosure_hvec, hx]]
  exact ggHalfGraphClosure_ip_self_root _ ((mem_rootFinset (τ := .E6)).1 (hm.1 (b.lab x) (b.lab 0)
    (ggHalfGraphClosure_lab_self b x) (ggHalfGraphClosure_lab_self b 0) (fun h => hx (ggHalfGraphClosure_lab_inj b h))))

private theorem ggHalfGraphClosure_hvec_zero_left (m : GGHalfE6Model) (b : GGHalfBlk) (v : GGE6Root) :
    ggE6ip (ggHalfGraphClosure_hvec m b 0) v = 0 := by
  rw [ggHalfGraphClosure_hvec_zero]; simp [ggE6ip]

private theorem ggHalfGraphClosure_frame_eq_hvec (m : GGHalfE6Model) (b : GGHalfBlk) (hm : m.FrameOK b)
    (a a' : J6) (haa : a ≠ a') :
    m.frame b (b.lab a) (b.lab a') = ggHalfGraphClosure_hvec m b a - ggHalfGraphClosure_hvec m b a' := by
  by_cases ha : a = 0
  · subst ha
    have ha' : a' ≠ 0 := fun h => haa h.symm
    rw [ggHalfGraphClosure_hvec_zero,
      show ggHalfGraphClosure_hvec m b a' = m.frame b (b.lab a') (b.lab 0) by simp [ggHalfGraphClosure_hvec, ha'],
      zero_sub]
    exact hm.2.1 (b.lab a') (b.lab 0) (ggHalfGraphClosure_lab_self b a') (ggHalfGraphClosure_lab_self b 0)
      (fun h => ha' (ggHalfGraphClosure_lab_inj b h))
  · by_cases ha' : a' = 0
    · subst ha'
      rw [show ggHalfGraphClosure_hvec m b a = m.frame b (b.lab a) (b.lab 0) by simp [ggHalfGraphClosure_hvec, ha],
        ggHalfGraphClosure_hvec_zero, sub_zero]
    · rw [show ggHalfGraphClosure_hvec m b a = m.frame b (b.lab a) (b.lab 0) by simp [ggHalfGraphClosure_hvec, ha],
        show ggHalfGraphClosure_hvec m b a' = m.frame b (b.lab a') (b.lab 0) by simp [ggHalfGraphClosure_hvec, ha']]
      have h := hm.2.2.1 (b.lab a) (b.lab 0) (b.lab a') (ggHalfGraphClosure_lab_self b a)
        (ggHalfGraphClosure_lab_self b 0) (ggHalfGraphClosure_lab_self b a')
        (fun h => ha (ggHalfGraphClosure_lab_inj b h)) (fun h => ha' (ggHalfGraphClosure_lab_inj b h.symm))
        (fun h => haa (ggHalfGraphClosure_lab_inj b h))
      have hneg := hm.2.1 (b.lab a') (b.lab 0) (ggHalfGraphClosure_lab_self b a') (ggHalfGraphClosure_lab_self b 0)
        (fun h => ha' (ggHalfGraphClosure_lab_inj b h))
      rw [hneg] at h
      rw [← h]
      abel

private theorem ggHalfGraphClosure_ip_hvec_of_ne (m : GGHalfE6Model) (b : GGHalfBlk) (hm : m.FrameOK b)
    (x y : J6) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    ggE6ip (ggHalfGraphClosure_hvec m b x) (ggHalfGraphClosure_hvec m b y) = 1 := by
  have hxr := ggHalfGraphClosure_hvec_self m b hm x hx
  have hyr := ggHalfGraphClosure_hvec_self m b hm y hy
  have hdiff : ggHalfGraphClosure_hvec m b x - ggHalfGraphClosure_hvec m b y = m.frame b (b.lab x) (b.lab y) := by
    rw [← ggHalfGraphClosure_frame_eq_hvec m b hm x y hxy]
  have hroot : ggE6ip (m.frame b (b.lab x) (b.lab y)) (m.frame b (b.lab x) (b.lab y)) = 2 :=
    ggHalfGraphClosure_ip_self_root _ ((mem_rootFinset (τ := .E6)).1 (hm.1 (b.lab x) (b.lab y)
      (ggHalfGraphClosure_lab_self b x) (ggHalfGraphClosure_lab_self b y) (fun h => hxy (ggHalfGraphClosure_lab_inj b h))))
  rw [← hdiff] at hroot
  rw [ggHalfGraphClosure_ip_sub_left, ggHalfGraphClosure_ip_sub_right, ggHalfGraphClosure_ip_sub_right, hxr, hyr,
    ggHalfGraphClosure_ggE6ip_symm (ggHalfGraphClosure_hvec m b y) (ggHalfGraphClosure_hvec m b x)] at hroot
  omega

private theorem ggHalfGraphClosure_ip_L_02_13 (m : GGHalfE6Model) (hm : m.FrameOK .L) :
    ggE6ip (m.frame .L 0 2) (m.frame .L 1 3) = 0 := by
  have h02 : m.frame .L 0 2 = ggHalfGraphClosure_hvec m .L 0 - ggHalfGraphClosure_hvec m .L 2 := by
    simpa [GGHalfBlk.lab, GGHalfBlk.off] using ggHalfGraphClosure_frame_eq_hvec m .L hm 0 2 (by decide)
  have h13 : m.frame .L 1 3 = ggHalfGraphClosure_hvec m .L 1 - ggHalfGraphClosure_hvec m .L 3 := by
    simpa [GGHalfBlk.lab, GGHalfBlk.off] using ggHalfGraphClosure_frame_eq_hvec m .L hm 1 3 (by decide)
  rw [h02, h13, ggHalfGraphClosure_ip_sub_left, ggHalfGraphClosure_ip_sub_right, ggHalfGraphClosure_ip_sub_right,
    ggHalfGraphClosure_ip_hvec_of_ne m .L hm 2 1 (by decide) (by decide) (by decide),
    ggHalfGraphClosure_ip_hvec_of_ne m .L hm 2 3 (by decide) (by decide) (by decide),
    ggHalfGraphClosure_hvec_zero_left, ggHalfGraphClosure_hvec_zero_left]
  norm_num

private theorem ggHalfGraphClosure_ip_L_02_self (m : GGHalfE6Model) (hm : m.FrameOK .L) :
    ggE6ip (m.frame .L 0 2) (m.frame .L 0 2) = 2 :=
  ggHalfGraphClosure_ip_self_root _ ((mem_rootFinset (τ := .E6)).1 (hm.1 0 2 (by simp [GGHalfBlk.Lab]) (by simp [GGHalfBlk.Lab]) (by simp [GGHalfBlk.Lab])))

private theorem ggHalfGraphClosure_ip_L_13_self (m : GGHalfE6Model) (hm : m.FrameOK .L) :
    ggE6ip (m.frame .L 1 3) (m.frame .L 1 3) = 2 :=
  ggHalfGraphClosure_ip_self_root _ ((mem_rootFinset (τ := .E6)).1 (hm.1 1 3 (by simp [GGHalfBlk.Lab]) (by simp [GGHalfBlk.Lab]) (by simp [GGHalfBlk.Lab])))

private theorem ggHalfGraphClosure_ggE6Refl_comm (a b r : GGE6Root) (h : ggE6ip a b = 0) :
    ggE6Refl a (ggE6Refl b r) = ggE6Refl b (ggE6Refl a r) := by
  simp only [ggE6Refl]
  rw [ggHalfGraphClosure_ip_sub_left, ggHalfGraphClosure_ip_sub_left, ggHalfGraphClosure_ggE6ip_smul_left, ggHalfGraphClosure_ggE6ip_smul_left,
    ggHalfGraphClosure_ggE6ip_symm b a, h, mul_zero, sub_zero]
  module

private theorem ggHalfGraphClosure_ggE6Refl_self (a r : GGE6Root) (h : ggE6ip a a = 2) :
    ggE6Refl a (ggE6Refl a r) = r := by
  simp only [ggE6Refl]
  rw [ggHalfGraphClosure_ip_sub_left, ggHalfGraphClosure_ggE6ip_smul_left, ggHalfGraphClosure_ggE6ip_symm r a, h]
  module

private theorem ggHalfGraphClosure_wg_wg (m : GGHalfE6Model) (hm : m.FrameOK .L) (r : GGE6Root) :
    m.wg (m.wg r) = r := by
  rw [GGHalfE6Model.wg, GGHalfE6Model.wg]
  rw [ggHalfGraphClosure_ggE6Refl_comm _ _ _ (ggHalfGraphClosure_ip_L_02_13 m hm)]
  rw [ggHalfGraphClosure_ggE6Refl_self _ _ (ggHalfGraphClosure_ip_L_02_self m hm),
    ggHalfGraphClosure_ggE6Refl_self _ _ (ggHalfGraphClosure_ip_L_13_self m hm)]

private theorem ggHalfGraphClosure_frame_neg (m : GGHalfE6Model) (b : GGHalfBlk)
    (hm : m.FrameOK b) (c d : Fin 6) (hcd : c ≠ d) :
    m.frame b (b.lab d) (b.lab c) = -m.frame b (b.lab c) (b.lab d) :=
  hm.2.1 (b.lab c) (b.lab d) (ggHalfGraphClosure_lab_self b c) (ggHalfGraphClosure_lab_self b d)
    (fun h => hcd (ggHalfGraphClosure_lab_inj b h))

private theorem ggHalfGraphClosure_mem_labels {m : GGHalfE6Model} {b : GGHalfBlk}
    {r : GGE6Root} (hr : r ∈ m.Y b) :
    ∃ c d : Fin 6, c ≠ d ∧ m.frame b (b.lab c) (b.lab d) = r := by
  obtain ⟨a, a', ha, ha', hne, hfr⟩ := hr
  refine ⟨ggHalfGraphClosure_labInv b a ha, ggHalfGraphClosure_labInv b a' ha', ?_, ?_⟩
  · intro hh
    exact hne ((ggHalfGraphClosure_lab_labInv b a ha).symm.trans
      ((congrArg (b.lab) hh).trans (ggHalfGraphClosure_lab_labInv b a' ha')))
  · rw [ggHalfGraphClosure_lab_labInv b a ha, ggHalfGraphClosure_lab_labInv b a' ha', hfr]

private theorem ggHalfGraphClosure_der_mem {m : GGHalfE6Model} {b : GGHalfBlk}
    {r : GGE6Root} (hd : m.Der b r) : r ∈ m.Y b := by
  induction hd with
  | base hr hi => exact hr
  | refl hg hng hh hhg hhn hr => exact hr
  | add hg hh hs hY => exact hY
  | transfer hb hc => exact hc
  | transportG hL hb hbc ihL ih => obtain ⟨rfl, rfl, hh⟩ | ⟨rfl, rfl, hh⟩ := hbc <;> exact hh
  | transportH hK hb hbc ihK ih => obtain ⟨rfl, rfl, hh⟩ | ⟨rfl, rfl, hh⟩ := hbc <;> exact hh

private theorem ggHalfGraphClosure_der_isRoot (m : GGHalfE6Model)
    (hm : ∀ b, m.FrameOK b) {b : GGHalfBlk} {r : GGE6Root} (hd : m.Der b r) :
    IsRoot .E6 r := by
  obtain ⟨c, d, hcd, hfr⟩ := ggHalfGraphClosure_mem_labels (ggHalfGraphClosure_der_mem hd)
  rw [← hfr]
  exact (mem_rootFinset (τ := .E6)).1 (hm b |>.1 (b.lab c) (b.lab d)
    (ggHalfGraphClosure_lab_self b c) (ggHalfGraphClosure_lab_self b d)
    (fun hh => hcd (ggHalfGraphClosure_lab_inj b hh)))

private theorem ggHalfGraphClosure_ip_K_62_73 (m : GGHalfE6Model) (hm : m.FrameOK .K) :
    ggE6ip (m.frame .K 6 2) (m.frame .K 7 3) = 0 := by
  have h62 : m.frame .K 6 2 = ggHalfGraphClosure_hvec m .K 4 - ggHalfGraphClosure_hvec m .K 0 := by
    simpa [GGHalfBlk.lab, GGHalfBlk.off] using
      ggHalfGraphClosure_frame_eq_hvec m .K hm 4 0 (by decide)
  have h73 : m.frame .K 7 3 = ggHalfGraphClosure_hvec m .K 5 - ggHalfGraphClosure_hvec m .K 1 := by
    simpa [GGHalfBlk.lab, GGHalfBlk.off] using
      ggHalfGraphClosure_frame_eq_hvec m .K hm 5 1 (by decide)
  rw [h62, h73, ggHalfGraphClosure_hvec_zero, sub_zero, ggHalfGraphClosure_ip_sub_right,
    ggHalfGraphClosure_ip_hvec_of_ne m .K hm 4 5 (by decide) (by decide) (by decide),
    ggHalfGraphClosure_ip_hvec_of_ne m .K hm 4 1 (by decide) (by decide) (by decide)]
  norm_num

private theorem ggHalfGraphClosure_ip_K_62_self (m : GGHalfE6Model) (hm : m.FrameOK .K) :
    ggE6ip (m.frame .K 6 2) (m.frame .K 6 2) = 2 :=
  ggHalfGraphClosure_ip_self_root _ ((mem_rootFinset (τ := .E6)).1 (hm.1 6 2
    (by simp [GGHalfBlk.Lab]) (by simp [GGHalfBlk.Lab]) (by decide)))

private theorem ggHalfGraphClosure_ip_K_73_self (m : GGHalfE6Model) (hm : m.FrameOK .K) :
    ggE6ip (m.frame .K 7 3) (m.frame .K 7 3) = 2 :=
  ggHalfGraphClosure_ip_self_root _ ((mem_rootFinset (τ := .E6)).1 (hm.1 7 3
    (by simp [GGHalfBlk.Lab]) (by simp [GGHalfBlk.Lab]) (by decide)))

private theorem ggHalfGraphClosure_wh_wh (m : GGHalfE6Model) (hm : m.FrameOK .K)
    (r : GGE6Root) : m.wh (m.wh r) = r := by
  rw [GGHalfE6Model.wh, GGHalfE6Model.wh]
  rw [ggHalfGraphClosure_ggE6Refl_comm _ _ _ (ggHalfGraphClosure_ip_K_62_73 m hm)]
  rw [ggHalfGraphClosure_ggE6Refl_self _ _ (ggHalfGraphClosure_ip_K_62_self m hm),
    ggHalfGraphClosure_ggE6Refl_self _ _ (ggHalfGraphClosure_ip_K_73_self m hm)]

private def ggHalfGraphClosure_Key
    {G : Type} [Group G] (φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G) (φ : GGE6Two →* G)
    (m : GGHalfE6Model) (b : GGHalfBlk) (r : GGE6Root) : Prop :=
  ∃ c d : Fin 6, c ≠ d ∧ m.frame b (b.lab c) (b.lab d) = r ∧
    φ (ggE6x r) = ggHalfBlockHom φ₁ φ₂ b (slE c d)

private theorem ggHalfGraphClosure_key_base
    {G : Type} [Group G] {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (m : GGHalfE6Model) (φ : GGE6Two →* G)
    (hbase : ∀ (b : GGHalfBlk) (c d : Fin 6) (i : Fin (Tag.rank .E6)), c ≠ d →
      (m.frame b (b.lab c) (b.lab d) = GGHalfE6Model.simpleRoot i ∨
        m.frame b (b.lab c) (b.lab d) = -GGHalfE6Model.simpleRoot i) →
      φ (ggE6x (m.frame b (b.lab c) (b.lab d))) = ggHalfBlockHom φ₁ φ₂ b (slE c d))
    {b : GGHalfBlk} {i : Fin (Tag.rank .E6)} {r : GGE6Root} (hr : r ∈ m.Y b)
    (hi : r = GGHalfE6Model.simpleRoot i ∨ r = -GGHalfE6Model.simpleRoot i) :
    ggHalfGraphClosure_Key φ₁ φ₂ φ m b r := by
  obtain ⟨c, d, hcd, hfr⟩ := ggHalfGraphClosure_mem_labels hr
  exact ⟨c, d, hcd, hfr, by
    rw [← hfr]
    exact hbase b c d i hcd (hfr.symm ▸ hi)⟩

private theorem ggHalfGraphClosure_key_transfer
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂) (hg : ¬ GGHalfAlphaInner φ₁ φ₂)
    (m : GGHalfE6Model) (hm : m.Good) (φ : GGE6Two →* G)
    {b c : GGHalfBlk} {r : GGE6Root} (hb : m.Der b r)
    (ih : ggHalfGraphClosure_Key φ₁ φ₂ φ m b r) (hc : r ∈ m.Y c) :
    ggHalfGraphClosure_Key φ₁ φ₂ φ m c r := by
  obtain ⟨c₀, d₀, hc₀d₀, hfr₀, hval₀⟩ := ih
  obtain ⟨c', d', hc'd', hfr'⟩ := ggHalfGraphClosure_mem_labels hc
  refine ⟨c', d', hc'd', hfr', ?_⟩
  rw [hval₀]
  exact frames_agree h hg m hm b c c₀ d₀ c' d' hc₀d₀ hc'd' (hfr₀.trans hfr'.symm)

private theorem ggHalfGraphClosure_key_add
    {G : Type} [Group G] {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (m : GGHalfE6Model) (φ : GGE6Two →* G)
    (hmFrameOK : ∀ b : GGHalfBlk, m.FrameOK b)
    (θ : GGHalfBlk → SpecialLinearGroup (Fin 6) F2 →* GGE6Two)
    (hθinj : ∀ b, Function.Injective (θ b))
    (hθprop : ∀ b c d, c ≠ d → θ b (slE c d) = ggE6x (m.frame b (b.lab c) (b.lab d)))
    {b : GGHalfBlk} {g h : GGE6Root} (hg : m.Der b g) (ihg : ggHalfGraphClosure_Key φ₁ φ₂ φ m b g)
    (hh : m.Der b h) (ihh : ggHalfGraphClosure_Key φ₁ φ₂ φ m b h)
    (hs : g + h ∈ rootFinset .E6) (hY : g + h ∈ m.Y b) :
    ggHalfGraphClosure_Key φ₁ φ₂ φ m b (g + h) := by
  obtain ⟨c₀, d₀, hc₀d₀, hgfr, hgval⟩ := ihg
  obtain ⟨e₀, f₀, he₀f₀, hhfr, hhval⟩ := ihh
  obtain ⟨c, d, hcd, hfr⟩ := ggHalfGraphClosure_mem_labels hY
  have hgr : IsRoot .E6 g := ggHalfGraphClosure_der_isRoot m hmFrameOK hg
  have hhr : IsRoot .E6 h := ggHalfGraphClosure_der_isRoot m hmFrameOK hh
  have hsumr : IsRoot .E6 (g + h) := (mem_rootFinset (τ := .E6)).1 hs
  have hne : g + h ≠ 0 := hsumr.ne_zero
  have hcomm : ⁅ggE6x g, ggE6x h⁆ = ggE6x (g + h) := by
    obtain ⟨σ, hσ, hh'⟩ := (e6Data_valid.commutator_xm F2 hgr hhr hne).1 hsumr
    have hσ1 : σ = 1 := ggHalfGraphClosure_isSign_eq_one_f2 hσ
    have h1 := hh' 1 1
    rw [hσ1] at h1
    simpa [ggE6x] using h1
  refine ⟨c, d, hcd, hfr, ?_⟩
  have hslE : slE c d = ⁅slE c₀ d₀, slE e₀ f₀⁆ := by
    apply hθinj b
    rw [hθprop b c d hcd, hfr, ← hcomm, map_commutatorElement, hθprop b c₀ d₀ hc₀d₀,
      hθprop b e₀ f₀ he₀f₀, hgfr, hhfr]
  rw [hslE, map_commutatorElement, ← hcomm, map_commutatorElement, hgval, hhval]

private theorem ggHalfGraphClosure_key_refl
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂) (hg : ¬ GGHalfAlphaInner φ₁ φ₂)
    (m : GGHalfE6Model) (hm : m.Good) (φ : GGE6Two →* G)
    (hmFrameOK : ∀ b : GGHalfBlk, m.FrameOK b)
    (θ : GGHalfBlk → SpecialLinearGroup (Fin 6) F2 →* GGE6Two)
    (hθinj : ∀ b, Function.Injective (θ b))
    (hθprop : ∀ b c d, c ≠ d → θ b (slE c d) = ggE6x (m.frame b (b.lab c) (b.lab d)))
    {b : GGHalfBlk} {g h' : GGE6Root}
    (hg' : m.Der b g) (ihg : ggHalfGraphClosure_Key φ₁ φ₂ φ m b g)
    (hng : m.Der b (-g)) (ihng : ggHalfGraphClosure_Key φ₁ φ₂ φ m b (-g))
    (hh' : m.Der b h') (ihh : ggHalfGraphClosure_Key φ₁ φ₂ φ m b h')
    (hhg : h' ≠ g) (hhn : h' ≠ -g) (hr : ggE6Refl g h' ∈ m.Y b) :
    ggHalfGraphClosure_Key φ₁ φ₂ φ m b (ggE6Refl g h') := by
  obtain ⟨c₀, d₀, hc₀d₀, hgfr, hgval⟩ := ihg
  obtain ⟨c₁, d₁, hc₁d₁, hngfr, hngval⟩ := ihng
  obtain ⟨m₀, n₀, hm₀n₀, hhfr, hhval⟩ := ihh
  have hgr : IsRoot .E6 g := ggHalfGraphClosure_der_isRoot m hmFrameOK hg'
  have hhr : IsRoot .E6 h' := ggHalfGraphClosure_der_isRoot m hmFrameOK hh'
  have hnegfr : m.frame b (b.lab d₀) (b.lab c₀) = -g := by
    rw [ggHalfGraphClosure_frame_neg m b (hmFrameOK b) c₀ d₀ hc₀d₀, hgfr]
  have hnegval : φ (ggE6x (-g)) = ggHalfBlockHom φ₁ φ₂ b (slE d₀ c₀) :=
    hngval.trans (frames_agree h hg m hm b b d₀ c₀ c₁ d₁ hc₀d₀.symm hc₁d₁
      (hnegfr.trans hngfr.symm)).symm
  obtain ⟨c, d, hcd, hfr⟩ := ggHalfGraphClosure_mem_labels hr
  refine ⟨c, d, hcd, hfr, ?_⟩
  have hge : ggE6x g = θ b (slE c₀ d₀) := by rw [← hgfr, ← hθprop b c₀ d₀ hc₀d₀]
  have hnege : ggE6x (-g) = θ b (slE d₀ c₀) := by
    rw [← hnegfr, ← hθprop b d₀ c₀ hc₀d₀.symm]
  have hhe : ggE6x h' = θ b (slE m₀ n₀) := by rw [← hhfr, ← hθprop b m₀ n₀ hm₀n₀]
  have hslE : slE c d = slE ((Equiv.swap c₀ d₀) m₀) ((Equiv.swap c₀ d₀) n₀) := by
    apply hθinj b
    rw [hθprop b c d hcd, hfr, ← ggHalfGraphClosure_conj_refl g h' hgr hhr]
    simp only [hge, hnege, hhe, ← map_mul, ← map_inv]
    rw [ggHalfGraphClosure_slE_swap_mul c₀ d₀ hc₀d₀,
      ggHalfGraphClosure_slPerm_conj_slE (Equiv.swap c₀ d₀) m₀ n₀ hm₀n₀]
  rw [hslE, ← ggHalfGraphClosure_conj_refl g h' hgr hhr]
  simp only [map_mul, map_inv, hgval, hnegval, hhval]
  simp only [← map_mul, ← map_inv]
  rw [ggHalfGraphClosure_slE_swap_mul c₀ d₀ hc₀d₀,
    ggHalfGraphClosure_slPerm_conj_slE (Equiv.swap c₀ d₀) m₀ n₀ hm₀n₀]

private theorem ggHalfGraphClosure_isRoot_frame
    (m : GGHalfE6Model) (b : GGHalfBlk) (hm : m.FrameOK b) (c d : Fin 6) (hcd : c ≠ d) :
    IsRoot .E6 (m.frame b (b.lab c) (b.lab d)) :=
  (mem_rootFinset (τ := .E6)).1 (hm.1 (b.lab c) (b.lab d) (ggHalfGraphClosure_lab_self b c)
    (ggHalfGraphClosure_lab_self b d) (fun h => hcd (ggHalfGraphClosure_lab_inj b h)))

private theorem ggHalfGraphClosure_conj_wg
    (m : GGHalfE6Model) (hm : m.FrameOK .L) (r : GGE6Root) (hr : IsRoot .E6 r) :
    ggE6x (m.wg r) =
      (ggE6x (m.frame .L 0 2) * ggE6x (-(m.frame .L 0 2)) * ggE6x (m.frame .L 0 2)) *
      (ggE6x (m.frame .L 1 3) * ggE6x (-(m.frame .L 1 3)) * ggE6x (m.frame .L 1 3)) *
      ggE6x r *
      ((ggE6x (m.frame .L 0 2) * ggE6x (-(m.frame .L 0 2)) * ggE6x (m.frame .L 0 2)) *
       (ggE6x (m.frame .L 1 3) * ggE6x (-(m.frame .L 1 3)) * ggE6x (m.frame .L 1 3)))⁻¹ := by
  rw [GGHalfE6Model.wg,
    ← ggHalfGraphClosure_conj_refl (m.frame .L 0 2) (ggE6Refl (m.frame .L 1 3) r)
      (ggHalfGraphClosure_isRoot_frame m .L hm 0 2 (by decide))
      (ggHalfGraphClosure_isRoot_refl (m.frame .L 1 3) r
        (ggHalfGraphClosure_isRoot_frame m .L hm 1 3 (by decide)) hr),
    ← ggHalfGraphClosure_conj_refl (m.frame .L 1 3) r
      (ggHalfGraphClosure_isRoot_frame m .L hm 1 3 (by decide)) hr]
  group

private theorem ggHalfGraphClosure_conj_wh
    (m : GGHalfE6Model) (hm : m.FrameOK .K) (r : GGE6Root) (hr : IsRoot .E6 r) :
    ggE6x (m.wh r) =
      (ggE6x (m.frame .K 6 2) * ggE6x (-(m.frame .K 6 2)) * ggE6x (m.frame .K 6 2)) *
      (ggE6x (m.frame .K 7 3) * ggE6x (-(m.frame .K 7 3)) * ggE6x (m.frame .K 7 3)) *
      ggE6x r *
      ((ggE6x (m.frame .K 6 2) * ggE6x (-(m.frame .K 6 2)) * ggE6x (m.frame .K 6 2)) *
       (ggE6x (m.frame .K 7 3) * ggE6x (-(m.frame .K 7 3)) * ggE6x (m.frame .K 7 3)))⁻¹ := by
  rw [GGHalfE6Model.wh,
    ← ggHalfGraphClosure_conj_refl (m.frame .K 6 2) (ggE6Refl (m.frame .K 7 3) r)
      (ggHalfGraphClosure_isRoot_frame m .K hm 4 0 (by decide))
      (ggHalfGraphClosure_isRoot_refl (m.frame .K 7 3) r
        (ggHalfGraphClosure_isRoot_frame m .K hm 5 1 (by decide)) hr),
    ← ggHalfGraphClosure_conj_refl (m.frame .K 7 3) r
      (ggHalfGraphClosure_isRoot_frame m .K hm 5 1 (by decide)) hr]
  group

private theorem ggHalfGraphClosure_gElt_mul_self
    {G : Type} [Group G] (φ₁ : SpecialLinearGroup (Fin 6) F2 →* G) : gElt φ₁ * gElt φ₁ = 1 := by
  have h : sigmaPerm 3 * sigmaPerm 3 = 1 := by decide
  rw [gElt, ← map_mul, ← map_mul, h, map_one, map_one]

private theorem ggHalfGraphClosure_hElt_mul_self
    {G : Type} [Group G] (φ₂ : SpecialLinearGroup (Fin 6) F2 →* G) : hElt φ₂ * hElt φ₂ = 1 := by
  have h : tauPerm 3 * tauPerm 3 = 1 := by decide
  rw [hElt, ← map_mul, ← map_mul, h, map_one, map_one]

private theorem ggHalfGraphClosure_SLoc_invol (c : Fin 6) : ggHalfSLoc (ggHalfSLoc c) = c := by
  fin_cases c <;> decide

private theorem ggHalfGraphClosure_tauPerm_eq :
    tauPerm 3 = Equiv.swap (4 : Fin 6) 0 * Equiv.swap 5 1 := by decide

private theorem ggHalfGraphClosure_key_transportG
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂) (hg : ¬ GGHalfAlphaInner φ₁ φ₂)
    (m : GGHalfE6Model) (hm : m.Good) (φ : GGE6Two →* G)
    (hmFrameOK : ∀ b : GGHalfBlk, m.FrameOK b) (hmWeyl : m.Weyl)
    {b c : GGHalfBlk} {r : GGE6Root}
    (ihL : ∀ s ∈ m.Y .L, ggHalfGraphClosure_Key φ₁ φ₂ φ m .L s)
    (hb : m.Der b r) (ihb : ggHalfGraphClosure_Key φ₁ φ₂ φ m b r)
    (hbc : (b = GGHalfBlk.K ∧ c = GGHalfBlk.M ∧ m.wg r ∈ m.Y GGHalfBlk.M) ∨
      (b = GGHalfBlk.M ∧ c = GGHalfBlk.K ∧ m.wg r ∈ m.Y GGHalfBlk.K)) :
    ggHalfGraphClosure_Key φ₁ φ₂ φ m c (m.wg r) := by
  obtain ⟨c₀, d₀, hc₀d₀, hfr, hval⟩ := ihb
  have hgr : IsRoot .E6 r := ggHalfGraphClosure_der_isRoot m hmFrameOK hb
  have hvalL : ∀ (i j : Fin 6) (hij : i ≠ j),
      φ (ggE6x (m.frame .L (GGHalfBlk.L.lab i) (GGHalfBlk.L.lab j)))
        = ggHalfBlockHom φ₁ φ₂ .L (slE i j) := by
    intro i j hij
    have hmem : m.frame .L (GGHalfBlk.L.lab i) (GGHalfBlk.L.lab j) ∈ m.Y .L :=
      ⟨GGHalfBlk.L.lab i, GGHalfBlk.L.lab j, ggHalfGraphClosure_lab_self .L i,
        ggHalfGraphClosure_lab_self .L j, (fun hh => hij (ggHalfGraphClosure_lab_inj .L hh)), rfl⟩
    obtain ⟨ci, dj, hcd, hfr', hval'⟩ := ihL _ hmem
    exact hval'.trans (frames_agree h hg m hm .L .L i j ci dj hij hcd hfr'.symm).symm
  have hnL : φ (ggE6x (m.frame .L 0 2) * ggE6x (-(m.frame .L 0 2)) * ggE6x (m.frame .L 0 2) *
        (ggE6x (m.frame .L 1 3) * ggE6x (-(m.frame .L 1 3)) * ggE6x (m.frame .L 1 3)))
      = gElt φ₁ := by
    have e02 : φ (ggE6x (m.frame .L 0 2)) = ggHalfBlockHom φ₁ φ₂ .L (slE 0 2) := by
      simpa [GGHalfBlk.lab, GGHalfBlk.off] using hvalL 0 2 (by decide)
    have e20 : φ (ggE6x (m.frame .L 2 0)) = ggHalfBlockHom φ₁ φ₂ .L (slE 2 0) := by
      simpa [GGHalfBlk.lab, GGHalfBlk.off] using hvalL 2 0 (by decide)
    have e13 : φ (ggE6x (m.frame .L 1 3)) = ggHalfBlockHom φ₁ φ₂ .L (slE 1 3) := by
      simpa [GGHalfBlk.lab, GGHalfBlk.off] using hvalL 1 3 (by decide)
    have e31 : φ (ggE6x (m.frame .L 3 1)) = ggHalfBlockHom φ₁ φ₂ .L (slE 3 1) := by
      simpa [GGHalfBlk.lab, GGHalfBlk.off] using hvalL 3 1 (by decide)
    rw [show -(m.frame .L 0 2) = m.frame .L 2 0 by
        simpa [GGHalfBlk.lab, GGHalfBlk.off] using
          (ggHalfGraphClosure_frame_neg m .L (hmFrameOK .L) 0 2 (by decide)).symm,
      show -(m.frame .L 1 3) = m.frame .L 3 1 by
        simpa [GGHalfBlk.lab, GGHalfBlk.off] using
          (ggHalfGraphClosure_frame_neg m .L (hmFrameOK .L) 1 3 (by decide)).symm]
    simp only [map_mul, map_inv, e02, e20, e13, e31]
    simp only [← map_mul, ← map_inv]
    rw [ggHalfGraphClosure_slE_swap_mul 0 2 (by decide),
      ggHalfGraphClosure_slE_swap_mul 1 3 (by decide)]
    rw [show slPerm gf2_two (Equiv.swap 0 2) * slPerm gf2_two (Equiv.swap 1 3)
        = slPerm gf2_two (sigmaPerm 3) by rw [← map_mul]; rfl]
    rfl
  rcases hbc with ⟨rfl, rfl, hmwg⟩ | ⟨rfl, rfl, hmwg⟩
  · refine ⟨c₀, d₀, hc₀d₀, ?_, ?_⟩
    · have hw : m.frame .M (GGHalfBlk.K.lab c₀) (GGHalfBlk.K.lab d₀)
          = m.wg (m.frame .K (GGHalfBlk.K.lab c₀) (GGHalfBlk.K.lab d₀)) := by
        simpa [GGHalfBlk.lab, GGHalfBlk.off] using
          hmWeyl.1 (GGHalfBlk.M.lab c₀) (GGHalfBlk.M.lab d₀)
            (by simp [GGHalfBlk.lab, GGHalfBlk.off]) (by simp [GGHalfBlk.lab, GGHalfBlk.off])
            (fun hh => hc₀d₀ (ggHalfGraphClosure_lab_inj .M hh))
      rw [show m.frame .M (GGHalfBlk.M.lab c₀) (GGHalfBlk.M.lab d₀)
          = m.frame .M (GGHalfBlk.K.lab c₀) (GGHalfBlk.K.lab d₀) by rfl]
      rw [hw, hfr]
    · rw [ggHalfGraphClosure_conj_wg m (hmFrameOK .L) r hgr]
      nth_rewrite 1 [map_mul]
      nth_rewrite 1 [map_mul]
      nth_rewrite 1 [map_inv]
      rw [hnL, hval]
      rfl
  · refine ⟨c₀, d₀, hc₀d₀, ?_, ?_⟩
    · have hw : m.frame .M (GGHalfBlk.M.lab c₀) (GGHalfBlk.M.lab d₀)
          = m.wg (m.frame .K (GGHalfBlk.M.lab c₀) (GGHalfBlk.M.lab d₀)) :=
        hmWeyl.1 (GGHalfBlk.M.lab c₀) (GGHalfBlk.M.lab d₀)
          (by simp [GGHalfBlk.lab, GGHalfBlk.off]) (by simp [GGHalfBlk.lab, GGHalfBlk.off])
          (fun hh => hc₀d₀ (ggHalfGraphClosure_lab_inj .M hh))
      rw [← hfr, hw, ggHalfGraphClosure_wg_wg m (hmFrameOK .L)]
      rfl
    · rw [ggHalfGraphClosure_conj_wg m (hmFrameOK .L) r hgr]
      nth_rewrite 1 [map_mul]
      nth_rewrite 1 [map_mul]
      nth_rewrite 1 [map_inv]
      rw [hnL, hval]
      rw [show ggHalfBlockHom φ₁ φ₂ .M (slE c₀ d₀)
          = gElt φ₁ * ggHalfBlockHom φ₁ φ₂ .K (slE c₀ d₀) * (gElt φ₁)⁻¹ by
        simp [ggHalfBlockHom, MulAut.conj_apply]]
      calc gElt φ₁ * (gElt φ₁ * ggHalfBlockHom φ₁ φ₂ .K (slE c₀ d₀) * (gElt φ₁)⁻¹) * (gElt φ₁)⁻¹
          = (gElt φ₁ * gElt φ₁) * ggHalfBlockHom φ₁ φ₂ .K (slE c₀ d₀) * (gElt φ₁ * gElt φ₁)⁻¹ := by group
        _ = ggHalfBlockHom φ₁ φ₂ .K (slE c₀ d₀) := by
            rw [ggHalfGraphClosure_gElt_mul_self φ₁]; group

private theorem ggHalfGraphClosure_key_transportH
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂) (hg : ¬ GGHalfAlphaInner φ₁ φ₂)
    (m : GGHalfE6Model) (hm : m.Good) (φ : GGE6Two →* G)
    (hmFrameOK : ∀ b : GGHalfBlk, m.FrameOK b) (hmWeyl : m.Weyl)
    {b c : GGHalfBlk} {r : GGE6Root}
    (ihK : ∀ s ∈ m.Y .K, ggHalfGraphClosure_Key φ₁ φ₂ φ m .K s)
    (hb : m.Der b r) (ihb : ggHalfGraphClosure_Key φ₁ φ₂ φ m b r)
    (hbc : (b = GGHalfBlk.L ∧ c = GGHalfBlk.M ∧ m.wh r ∈ m.Y GGHalfBlk.M) ∨
      (b = GGHalfBlk.M ∧ c = GGHalfBlk.L ∧ m.wh r ∈ m.Y GGHalfBlk.L)) :
    ggHalfGraphClosure_Key φ₁ φ₂ φ m c (m.wh r) := by
  obtain ⟨c₀, d₀, hc₀d₀, hfr, hval⟩ := ihb
  have hgr : IsRoot .E6 r := ggHalfGraphClosure_der_isRoot m hmFrameOK hb
  have hvalK : ∀ (i j : Fin 6) (hij : i ≠ j),
      φ (ggE6x (m.frame .K (GGHalfBlk.K.lab i) (GGHalfBlk.K.lab j)))
        = ggHalfBlockHom φ₁ φ₂ .K (slE i j) := by
    intro i j hij
    have hmem : m.frame .K (GGHalfBlk.K.lab i) (GGHalfBlk.K.lab j) ∈ m.Y .K :=
      ⟨GGHalfBlk.K.lab i, GGHalfBlk.K.lab j, ggHalfGraphClosure_lab_self .K i,
        ggHalfGraphClosure_lab_self .K j, (fun hh => hij (ggHalfGraphClosure_lab_inj .K hh)), rfl⟩
    obtain ⟨ci, dj, hcd, hfr', hval'⟩ := ihK _ hmem
    exact hval'.trans (frames_agree h hg m hm .K .K i j ci dj hij hcd hfr'.symm).symm
  have hnH : φ (ggE6x (m.frame .K 6 2) * ggE6x (-(m.frame .K 6 2)) * ggE6x (m.frame .K 6 2) *
        (ggE6x (m.frame .K 7 3) * ggE6x (-(m.frame .K 7 3)) * ggE6x (m.frame .K 7 3)))
      = hElt φ₂ := by
    have e62 : φ (ggE6x (m.frame .K 6 2)) = ggHalfBlockHom φ₁ φ₂ .K (slE 4 0) := by
      simpa [GGHalfBlk.lab, GGHalfBlk.off] using hvalK 4 0 (by decide)
    have e26 : φ (ggE6x (m.frame .K 2 6)) = ggHalfBlockHom φ₁ φ₂ .K (slE 0 4) := by
      simpa [GGHalfBlk.lab, GGHalfBlk.off] using hvalK 0 4 (by decide)
    have e73 : φ (ggE6x (m.frame .K 7 3)) = ggHalfBlockHom φ₁ φ₂ .K (slE 5 1) := by
      simpa [GGHalfBlk.lab, GGHalfBlk.off] using hvalK 5 1 (by decide)
    have e37 : φ (ggE6x (m.frame .K 3 7)) = ggHalfBlockHom φ₁ φ₂ .K (slE 1 5) := by
      simpa [GGHalfBlk.lab, GGHalfBlk.off] using hvalK 1 5 (by decide)
    rw [show -(m.frame .K 6 2) = m.frame .K 2 6 by
        simpa [GGHalfBlk.lab, GGHalfBlk.off] using
          (ggHalfGraphClosure_frame_neg m .K (hmFrameOK .K) 4 0 (by decide)).symm,
      show -(m.frame .K 7 3) = m.frame .K 3 7 by
        simpa [GGHalfBlk.lab, GGHalfBlk.off] using
          (ggHalfGraphClosure_frame_neg m .K (hmFrameOK .K) 5 1 (by decide)).symm]
    simp only [map_mul, map_inv, e62, e26, e73, e37]
    simp only [← map_mul, ← map_inv]
    rw [ggHalfGraphClosure_slE_swap_mul 4 0 (by decide),
      ggHalfGraphClosure_slE_swap_mul 5 1 (by decide)]
    rw [show slPerm gf2_two (Equiv.swap 4 0) * slPerm gf2_two (Equiv.swap 5 1)
        = slPerm gf2_two (tauPerm 3) by rw [← map_mul, ← ggHalfGraphClosure_tauPerm_eq]]
    rfl
  have hne : ggHalfSLoc d₀ ≠ ggHalfSLoc c₀ := by
    intro hh
    exact hc₀d₀ (by
      have hh' := congrArg ggHalfSLoc hh
      rw [ggHalfGraphClosure_SLoc_invol, ggHalfGraphClosure_SLoc_invol] at hh'
      exact hh'.symm)
  rcases hbc with ⟨rfl, rfl, hmwh⟩ | ⟨rfl, rfl, hmwh⟩
  · refine ⟨ggHalfSLoc d₀, ggHalfSLoc c₀, hne, ?_, ?_⟩
    · have hw : m.frame .M (GGHalfBlk.M.lab (ggHalfSLoc d₀)) (GGHalfBlk.M.lab (ggHalfSLoc c₀))
          = m.wh (m.frame .L (GGHalfBlk.L.lab c₀) (GGHalfBlk.L.lab d₀)) := by
        have hw0 := hmWeyl.2 (GGHalfBlk.M.lab (ggHalfSLoc d₀)) (GGHalfBlk.M.lab (ggHalfSLoc c₀))
            (by simp [GGHalfBlk.lab, GGHalfBlk.off]) (by simp [GGHalfBlk.lab, GGHalfBlk.off])
            (fun hh => hne (ggHalfGraphClosure_lab_inj .M hh))
        rw [hw0]
        congr 1
        rw [ggHalfGraphClosure_S_lab (ggHalfSLoc c₀), ggHalfGraphClosure_S_lab (ggHalfSLoc d₀),
          ggHalfGraphClosure_SLoc_invol, ggHalfGraphClosure_SLoc_invol]
      rw [hw, hfr]
    · rw [ggHalfGraphClosure_conj_wh m (hmFrameOK .K) r hgr]
      nth_rewrite 1 [map_mul]
      nth_rewrite 1 [map_mul]
      nth_rewrite 1 [map_inv]
      rw [hnH, hval]
      rw [show ggHalfBlockHom φ₁ φ₂ .M (slE (ggHalfSLoc d₀) (ggHalfSLoc c₀))
          = hElt φ₂ * ggHalfBlockHom φ₁ φ₂ .L (slE c₀ d₀) * (hElt φ₂)⁻¹ by
        rw [show ggHalfBlockHom φ₁ φ₂ .M (slE (ggHalfSLoc d₀) (ggHalfSLoc c₀))
            = gElt φ₁ * φ₂ (slE (ggHalfSLoc d₀) (ggHalfSLoc c₀)) * (gElt φ₁)⁻¹ by
          simp [ggHalfBlockHom, MulAut.conj_apply]]
        rw [graph_I1 h hg (ggHalfSLoc d₀) (ggHalfSLoc c₀) hne]
        rw [ggHalfGraphClosure_SLoc_invol, ggHalfGraphClosure_SLoc_invol]
        rfl]
  · refine ⟨ggHalfSLoc d₀, ggHalfSLoc c₀, hne, ?_, ?_⟩
    · have hw : m.frame .M (GGHalfBlk.M.lab c₀) (GGHalfBlk.M.lab d₀)
          = m.wh (m.frame .L (GGHalfBlk.L.lab (ggHalfSLoc d₀)) (GGHalfBlk.L.lab (ggHalfSLoc c₀))) := by
        have hw0 := hmWeyl.2 (GGHalfBlk.M.lab c₀) (GGHalfBlk.M.lab d₀)
            (by simp [GGHalfBlk.lab, GGHalfBlk.off]) (by simp [GGHalfBlk.lab, GGHalfBlk.off])
            (fun hh => hc₀d₀ (ggHalfGraphClosure_lab_inj .M hh))
        rw [hw0]
        congr 1
        rw [ggHalfGraphClosure_S_lab d₀, ggHalfGraphClosure_S_lab c₀]
      rw [← hfr, hw, ggHalfGraphClosure_wh_wh m (hmFrameOK .K)]
    · rw [ggHalfGraphClosure_conj_wh m (hmFrameOK .K) r hgr]
      nth_rewrite 1 [map_mul]
      nth_rewrite 1 [map_mul]
      nth_rewrite 1 [map_inv]
      rw [hnH, hval]
      rw [show ggHalfBlockHom φ₁ φ₂ .M (slE c₀ d₀)
          = hElt φ₂ * ggHalfBlockHom φ₁ φ₂ .L (slE (ggHalfSLoc d₀) (ggHalfSLoc c₀)) * (hElt φ₂)⁻¹ by
        rw [show ggHalfBlockHom φ₁ φ₂ .M (slE c₀ d₀)
            = gElt φ₁ * φ₂ (slE c₀ d₀) * (gElt φ₁)⁻¹ by
          simp [ggHalfBlockHom, MulAut.conj_apply]]
        rw [graph_I1 h hg c₀ d₀ hc₀d₀]
        rfl]
      calc hElt φ₂ * (hElt φ₂ * ggHalfBlockHom φ₁ φ₂ .L (slE (ggHalfSLoc d₀) (ggHalfSLoc c₀)) * (hElt φ₂)⁻¹) * (hElt φ₂)⁻¹
          = (hElt φ₂ * hElt φ₂) * ggHalfBlockHom φ₁ φ₂ .L (slE (ggHalfSLoc d₀) (ggHalfSLoc c₀)) * (hElt φ₂ * hElt φ₂)⁻¹ := by group
        _ = ggHalfBlockHom φ₁ φ₂ .L (slE (ggHalfSLoc d₀) (ggHalfSLoc c₀)) := by
            rw [ggHalfGraphClosure_hElt_mul_self φ₂]; group

theorem closure_sound
   
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂) (hg : ¬ GGHalfAlphaInner φ₁ φ₂)
    (m : GGHalfE6Model) (hm : m.Good) (φ : GGE6Two →* G)
    (hbase : ∀ (b : GGHalfBlk) (c d : Fin 6) (i : Fin (Tag.rank .E6)), c ≠ d →
      (m.frame b (b.lab c) (b.lab d) = GGHalfE6Model.simpleRoot i ∨
        m.frame b (b.lab c) (b.lab d) = -GGHalfE6Model.simpleRoot i) →
      φ (ggE6x (m.frame b (b.lab c) (b.lab d))) = ggHalfBlockHom φ₁ φ₂ b (slE c d)) :
    ∀ (b : GGHalfBlk) (c d : Fin 6), c ≠ d →
      φ (ggE6x (m.frame b (b.lab c) (b.lab d))) = ggHalfBlockHom φ₁ φ₂ b (slE c d) := by
  have hmFrameOK : ∀ b : GGHalfBlk, m.FrameOK b := by
    intro b
    cases b
    · exact hm.1
    · exact hm.2.1
    · exact hm.2.2.1
  have hmWeyl : m.Weyl := hm.2.2.2.2.2.2.2.1
  have hmDer : ∀ b r, r ∈ m.Y b → m.Der b r := hm.2.2.2.2.2.2.2.2.2
  choose θ hθ using fun b => m.exists_theta b (hmFrameOK b)
  have hθinj : ∀ b, Function.Injective (θ b) := fun b => (hθ b).1
  have hθprop : ∀ b c d, c ≠ d →
      θ b (slE c d) = ggE6x (m.frame b (b.lab c) (b.lab d)) := fun b => (hθ b).2
  have key : ∀ b r, m.Der b r → ggHalfGraphClosure_Key φ₁ φ₂ φ m b r := by
    intro b r hd
    induction hd with
    | base hr hi => exact ggHalfGraphClosure_key_base m φ hbase hr hi
    | refl dg dng dh dhhg dhhn hr ihg ihng ihh =>
        exact ggHalfGraphClosure_key_refl h hg m hm φ hmFrameOK θ hθinj hθprop
          dg ihg dng ihng dh ihh dhhg dhhn hr
    | add dg dh hs hY ihg ihh =>
        exact ggHalfGraphClosure_key_add m φ hmFrameOK θ hθinj hθprop dg ihg dh ihh hs hY
    | transfer hb hc ih => exact ggHalfGraphClosure_key_transfer h hg m hm φ hb ih hc
    | transportG hL hb hbc ihL ih =>
        exact ggHalfGraphClosure_key_transportG h hg m hm φ hmFrameOK hmWeyl ihL hb ih hbc
    | transportH hK hb hbc ihK ih =>
        exact ggHalfGraphClosure_key_transportH h hg m hm φ hmFrameOK hmWeyl ihK hb ih hbc
  intro b c d hcd
  have hrY : m.frame b (b.lab c) (b.lab d) ∈ m.Y b :=
    ⟨b.lab c, b.lab d, ggHalfGraphClosure_lab_self b c, ggHalfGraphClosure_lab_self b d,
      (fun hh => hcd (ggHalfGraphClosure_lab_inj b hh)), rfl⟩
  obtain ⟨c', d', hc'd', hframe, hval⟩ := key b _ (hmDer b _ hrY)
  rw [hval]
  exact (frames_agree h hg m hm b b c d c' d' hcd hc'd' hframe.symm).symm

end GGHalfCtx

end CFSG.StandardType

end
