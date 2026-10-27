module

public import CFSG.Quasithin.Background.RonanH49YMat
public import CFSG.Quasithin.Background.HL3WrWreath

public section

namespace CFSG.Quasithin.RonanH49

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr
open scoped Matrix IsMulCommutative

theorem mem_P2_iff (a : ↥SL32) :
    a ∈ P2 ↔ (mat a 2 0 = 0 ∧ mat a 2 1 = 0 ∧ mat a 2 2 = 1) := e2_vecMul_iff (mat a)

theorem card_P2 : Nat.card ↥P2 = 24 := by
  have h : Nat.card ↥P2 =
      Nat.card {a : ↥SL32 // mat a 2 0 = 0 ∧ mat a 2 1 = 0 ∧ mat a 2 2 = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => e2_vecMul_iff (mat a))
  rw [h]
  exact (card_SL32_subtype (fun M => M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 2 2 = 1)).trans (by decide)

theorem card_G2 : Nat.card ↥G2 = 1152 := by
  have h := card_map_prod_sup_tau P2
  rw [card_P2] at h
  exact h.trans (by norm_num)

theorem det_mat_ne_zero' (g : ↥SL32) : (mat g).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.1.isUnit).ne_zero

theorem toAdd_tau_yW : Multiplicative.toAdd (tau yW) = YMat := by
  rw [toAdd_tau, toAdd_yW, YMat_symm]

theorem tau_yW : tau yW = yW := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_tau_yW, toAdd_yW]

abbrev Tw (i : Fin 3) : WMod := Multiplicative.ofAdd (tMat i)

theorem Tw_injective : Function.Injective Tw := fun i j h =>
  tMat_injective (congrArg Multiplicative.toAdd h)

theorem tau_Tw (i : Fin 3) : tau (Tw i) = Tw i := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_tau]
  exact tMat_symm i

theorem Cy_decomp {x : MulAut WMod} (hx : x ∈ Cy) :
    ∃ a b : ↥SL32, a ∈ P2 ∧ b ∈ P2 ∧ mat a * YMat * (mat b)ᵀ = YMat ∧
      (x = rho (a, b) ∨ x = rho (a, b) * tau) := by
  obtain ⟨hn, hy⟩ := mem_Cy.1 hx
  obtain ⟨⟨a, b⟩, hg | hg⟩ := mem_norm_iff.1 hn
  · have h : mat a * YMat * (mat b)ᵀ = YMat := by
      have := congrArg Multiplicative.toAdd hy
      rw [hg, toAdd_rho, toAdd_yW] at this
      exact this
    obtain ⟨ha, hb⟩ := P2_of_Y_stab (det_mat_ne_zero' a) (det_mat_ne_zero' b) h
    exact ⟨a, b, (mem_P2_iff a).2 ha, (mem_P2_iff b).2 hb, h, Or.inl hg⟩
  · have h : mat a * YMat * (mat b)ᵀ = YMat := by
      have := congrArg Multiplicative.toAdd hy
      rw [hg, MulAut.mul_apply, tau_yW, toAdd_rho, toAdd_yW] at this
      exact this
    obtain ⟨ha, hb⟩ := P2_of_Y_stab (det_mat_ne_zero' a) (det_mat_ne_zero' b) h
    exact ⟨a, b, (mem_P2_iff a).2 ha, (mem_P2_iff b).2 hb, h, Or.inr hg⟩

theorem Cy_le_G2 : Cy ≤ G2 := by
  intro x hx
  obtain ⟨a, b, ha, hb, -, rfl | rfl⟩ := Cy_decomp hx
  · exact Subgroup.mem_sup_left ⟨(a, b), ⟨ha, hb⟩, rfl⟩
  · exact mul_mem (Subgroup.mem_sup_left ⟨(a, b), ⟨ha, hb⟩, rfl⟩)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers tau))

theorem exists_act_Tw {x : MulAut WMod} (hx : x ∈ Cy) (i : Fin 3) : ∃ j, x (Tw i) = Tw j := by
  obtain ⟨a, b, ha, hb, h, rfl | rfl⟩ := Cy_decomp hx
  · obtain ⟨j, hj⟩ := Y_stab_perm ((mem_P2_iff a).1 ha) ((mem_P2_iff b).1 hb) h i
    refine ⟨j, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_rho]
    exact hj
  · obtain ⟨j, hj⟩ := Y_stab_perm ((mem_P2_iff a).1 ha) ((mem_P2_iff b).1 hb) h i
    refine ⟨j, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [MulAut.mul_apply, tau_Tw, toAdd_rho]
    exact hj

noncomputable def decodeT (Z : WMod) : Fin 3 :=
  if Z = Tw 0 then 0 else if Z = Tw 1 then 1 else 2

theorem decodeT_Tw (j : Fin 3) : decodeT (Tw j) = j := by
  have h01 : Tw 0 ≠ Tw 1 := fun h => by simpa using Tw_injective h
  have h02 : Tw 0 ≠ Tw 2 := fun h => by simpa using Tw_injective h
  have h12 : Tw 1 ≠ Tw 2 := fun h => by simpa using Tw_injective h
  fin_cases j
  · simp [decodeT]
  · simp [decodeT, h01.symm]
  · simp [decodeT, h02.symm, h12.symm]

noncomputable def sigFun (x : MulAut WMod) (i : Fin 3) : Fin 3 := decodeT (x (Tw i))

theorem Tw_sigFun {x : MulAut WMod} (hx : x ∈ Cy) (i : Fin 3) : Tw (sigFun x i) = x (Tw i) := by
  obtain ⟨j, hj⟩ := exists_act_Tw hx i
  rw [sigFun, hj, decodeT_Tw]

@[expose] noncomputable def sigC : ↥Cy →* Equiv.Perm (Fin 3) where
  toFun x :=
    { toFun := sigFun (x : MulAut WMod)
      invFun := sigFun ((x⁻¹ : ↥Cy) : MulAut WMod)
      left_inv := fun i => by
        apply Tw_injective
        rw [Tw_sigFun (x⁻¹ : ↥Cy).2, Tw_sigFun x.2]
        change ((x⁻¹ : ↥Cy) : MulAut WMod) ((x : MulAut WMod) (Tw i)) = Tw i
        rw [Subgroup.coe_inv, ← MulAut.mul_apply, inv_mul_cancel]
        rfl
      right_inv := fun i => by
        apply Tw_injective
        rw [Tw_sigFun x.2, Tw_sigFun (x⁻¹ : ↥Cy).2]
        change (x : MulAut WMod) (((x⁻¹ : ↥Cy) : MulAut WMod) (Tw i)) = Tw i
        rw [Subgroup.coe_inv, ← MulAut.mul_apply, mul_inv_cancel]
        rfl }
  map_one' := Equiv.ext fun i => by
    apply Tw_injective
    rw [Equiv.Perm.one_apply]
    exact (Tw_sigFun (one_mem Cy) i).trans (by rfl)
  map_mul' x y := Equiv.ext fun i => by
    apply Tw_injective
    change Tw (sigFun ((x : MulAut WMod) * (y : MulAut WMod)) i) =
      Tw (sigFun (x : MulAut WMod) (sigFun (y : MulAut WMod) i))
    rw [Tw_sigFun (Cy.mul_mem x.2 y.2), Tw_sigFun x.2, Tw_sigFun y.2]
    rfl

theorem Tw_sigC (x : ↥Cy) (i : Fin 3) : Tw (sigC x i) = (x : MulAut WMod) (Tw i) :=
  Tw_sigFun x.2 i

theorem mul_mem_img_iff {x y : MulAut WMod} (hx : x ∈ CFSG.Quasithin.H.L3Wr.norm)
    (hy : y ∈ CFSG.Quasithin.H.L3Wr.norm) : x * y ∈ img ↔ (x ∈ img ↔ y ∈ img) := by
  by_cases hxi : x ∈ img <;> by_cases hyi : y ∈ img
  · exact ⟨fun _ => iff_of_true hxi hyi, fun _ => img.mul_mem hxi hyi⟩
  · refine ⟨fun h => ?_, fun h => absurd (h.1 hxi) hyi⟩
    exact absurd (by simpa using img.mul_mem (img.inv_mem hxi) h) hyi
  · refine ⟨fun h => ?_, fun h => absurd (h.2 hyi) hxi⟩
    exact absurd (by simpa using img.mul_mem h (img.inv_mem hyi)) hxi
  · refine ⟨fun h => iff_of_false hxi hyi, fun _ => ?_⟩
    have := mul_inv_mem_img hx (CFSG.Quasithin.H.L3Wr.norm.inv_mem hy) hxi
      (fun h => hyi (by simpa using img.inv_mem h))
    simpa using this

open Classical in
@[expose] noncomputable def epsC : ↥Cy →* Multiplicative (ZMod 2) where
  toFun x := if (x : MulAut WMod) ∈ img then 1 else tq
  map_one' := by simp
  map_mul' x y := by
    have hx : (x : MulAut WMod) ∈ CFSG.Quasithin.H.L3Wr.norm := (mem_Cy.1 x.2).1
    have hy : (y : MulAut WMod) ∈ CFSG.Quasithin.H.L3Wr.norm := (mem_Cy.1 y.2).1
    have h := mul_mem_img_iff hx hy
    by_cases hxi : (x : MulAut WMod) ∈ img <;> by_cases hyi : (y : MulAut WMod) ∈ img
    · have : (x : MulAut WMod) * (y : MulAut WMod) ∈ img := h.2 (iff_of_true hxi hyi)
      simp [hxi, hyi, this]
    · have : (x : MulAut WMod) * (y : MulAut WMod) ∉ img := fun hm => hyi ((h.1 hm).1 hxi)
      simp [hxi, hyi, this]
    · have : (x : MulAut WMod) * (y : MulAut WMod) ∉ img := fun hm => hxi ((h.1 hm).2 hyi)
      simp [hxi, hyi, this]
    · have : (x : MulAut WMod) * (y : MulAut WMod) ∈ img := h.2 (iff_of_false hxi hyi)
      simp [hxi, hyi, this, tq_mul_tq]

open Classical in
theorem epsC_eq_one_iff (x : ↥Cy) : epsC x = 1 ↔ (x : MulAut WMod) ∈ img := by
  change (if (x : MulAut WMod) ∈ img then (1 : Multiplicative (ZMod 2)) else tq) = 1 ↔ _
  by_cases h : (x : MulAut WMod) ∈ img
  · simp [h]
  · simp [h, tq_ne_one]

@[expose] noncomputable def fC : ↥Cy →* Equiv.Perm (Fin 3) × Multiplicative (ZMod 2) :=
  sigC.prod epsC

@[expose] noncomputable def Eyy : Subgroup (MulAut WMod) := (R1.prod R1).map rho

theorem R1_comm {a a' : ↥SL32} (ha : a ∈ R1) (ha' : a' ∈ R1) : a * a' = a' * a := by
  obtain ⟨x, y, hx⟩ := ha
  obtain ⟨x', y', hx'⟩ := ha'
  apply eq_of_mat_eq
  rw [mat_mul, mat_mul, hx, hx', axMat_mul, axMat_mul, add_comm x x', add_comm y y']

theorem R1_mul_self {a : ↥SL32} (ha : a ∈ R1) : a * a = 1 := by
  obtain ⟨x, y, hx⟩ := ha
  apply eq_of_mat_eq
  rw [mat_mul, hx, axMat_mul_self, mat_one]

theorem Eyy_le_Cy : Eyy ≤ Cy := by
  rintro _ ⟨⟨a, b⟩, ⟨⟨x, y, ha⟩, ⟨x', y', hb⟩⟩, rfl⟩
  rw [mem_Cy]
  refine ⟨img_le_norm (rho_mem_img _), ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_rho, toAdd_yW]
  change mat a * YMat * (mat b)ᵀ = YMat
  rw [ha, hb]
  exact (axMat_stab x y x' y').1

theorem Eyy_elemAbelian : CFSG.Open.IsElemAbelian 2 Eyy := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hu⟩ := u.2
    obtain ⟨⟨a', b'⟩, ⟨ha', hb'⟩, hv⟩ := v.2
    apply Subtype.ext
    change (u : MulAut WMod) * (v : MulAut WMod) = (v : MulAut WMod) * (u : MulAut WMod)
    rw [← hu, ← hv, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, R1_comm ha ha',
      R1_comm hb hb']
  · obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hx
    rw [pow_two, ← map_mul, Prod.mk_mul_mk, R1_mul_self ha, R1_mul_self hb]
    exact map_one rho

theorem card_Eyy : Nat.card ↥Eyy = 16 := by
  rw [Eyy, Subgroup.card_map_of_injective rho_injective, card_prod_subgroup, card_R1]

theorem fC_apply (x : ↥Cy) : fC x = (sigC x, epsC x) := rfl

theorem fC_ker : fC.ker = Eyy.subgroupOf Cy := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, fC_apply, Prod.mk_eq_one]
  constructor
  · rintro ⟨hs, he⟩
    have hxi : (x : MulAut WMod) ∈ img := (epsC_eq_one_iff x).1 he
    obtain ⟨a, b, ha, hb, h, hx | hx⟩ := Cy_decomp x.2
    · have hfix : ∀ i : Fin 3, mat a * tMat i * (mat b)ᵀ = tMat i := fun i => by
        have h1 := Tw_sigC x i
        rw [hs, Equiv.Perm.one_apply, hx] at h1
        have h2 := congrArg Multiplicative.toAdd h1
        rw [toAdd_rho] at h2
        exact h2.symm
      obtain ⟨⟨x₁, y₁, hxa⟩, ⟨x₂, y₂, hxb⟩⟩ := Y_stab_kernel ((mem_P2_iff a).1 ha)
        ((mem_P2_iff b).1 hb) h (hfix 0) (hfix 1)
      rw [hx]
      exact ⟨(a, b), ⟨⟨x₁, y₁, hxa⟩, ⟨x₂, y₂, hxb⟩⟩, rfl⟩
    · exfalso
      apply tau_not_mem_img
      have h1 : tau = (rho (a, b))⁻¹ * (x : MulAut WMod) := by rw [hx, inv_mul_cancel_left]
      rw [h1]
      exact img.mul_mem (img.inv_mem (rho_mem_img _)) hxi
  · intro hx
    obtain ⟨⟨a, b⟩, ⟨⟨x₁, y₁, ha⟩, ⟨x₂, y₂, hb⟩⟩, hxe⟩ := hx
    refine ⟨?_, (epsC_eq_one_iff x).2 (hxe ▸ rho_mem_img _)⟩
    refine Equiv.ext fun i => Tw_injective ?_
    rw [Tw_sigC, Equiv.Perm.one_apply, ← hxe]
    apply Multiplicative.toAdd.injective
    rw [toAdd_rho]
    change mat a * tMat i * (mat b)ᵀ = tMat i
    rw [ha, hb]
    exact (axMat_stab x₁ y₁ x₂ y₂).2 i

theorem fC_surjective : Function.Surjective fC := by
  classical
  rintro ⟨π, e⟩
  obtain ⟨A, hA2, hAdet, hAY, hAt⟩ := Y_stab_surj π
  let a : ↥SL32 := slOfMat A hAdet
  have hx0 : rho (a, a) ∈ Cy := by
    rw [mem_Cy]
    refine ⟨img_le_norm (rho_mem_img _), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_rho, toAdd_yW]
    exact hAY
  let x0 : ↥Cy := ⟨rho (a, a), hx0⟩
  have hs0 : sigC x0 = π := Equiv.ext fun i => Tw_injective (by
    rw [Tw_sigC]
    apply Multiplicative.toAdd.injective
    change mat a * tMat i * (mat a)ᵀ = tMat (π i)
    exact hAt i)
  have he0 : epsC x0 = 1 := (epsC_eq_one_iff x0).2 (rho_mem_img _)
  have hτ : tau ∈ Cy := mem_Cy.2 ⟨tau_mem_norm, tau_yW⟩
  let t : ↥Cy := ⟨tau, hτ⟩
  have hst : sigC t = 1 := Equiv.ext fun i => Tw_injective (by
    rw [Tw_sigC, Equiv.Perm.one_apply]
    exact tau_Tw i)
  have het : epsC t = tq := by
    change (if tau ∈ img then (1 : Multiplicative (ZMod 2)) else tq) = tq
    simp [tau_not_mem_img]
  rcases mz2_cases e with rfl | rfl
  · exact ⟨x0, Prod.ext hs0 he0⟩
  · refine ⟨x0 * t, ?_⟩
    rw [map_mul, fC_apply x0, fC_apply t, hs0, he0, hst, het]
    simp

theorem card_Cy : Nat.card ↥Cy = 192 := by
  have h1 := Subgroup.card_mul_index fC.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr fC_surjective, Subgroup.card_top, fC_ker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Eyy_le_Cy).toEquiv, card_Eyy] at h1
  have h2 : Nat.card (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) = 12 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide
  rw [h2] at h1
  omega

theorem Cy_relIndex : Cy.relIndex G2 = 6 := by
  have h1 := Subgroup.card_mul_index (Cy.subgroupOf G2)
  have h2 : Nat.card ↥(Cy.subgroupOf G2) = 192 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Cy_le_G2).toEquiv).trans card_Cy
  rw [h2, card_G2] at h1
  show (Cy.subgroupOf G2).index = 6
  omega

theorem Cy_isExt : ∃ E : Subgroup (MulAut WMod), CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
    E ≤ Cy ∧ ∃ f : ↥Cy →* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)),
      Function.Surjective f ∧ f.ker = E.subgroupOf Cy :=
  ⟨Eyy, Eyy_elemAbelian, card_Eyy, Eyy_le_Cy, fC, fC_surjective, fC_ker⟩

end CFSG.Quasithin.RonanH49
