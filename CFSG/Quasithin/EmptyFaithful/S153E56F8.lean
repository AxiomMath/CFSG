module

public import CFSG.Quasithin.EmptyFaithful.S153E56F7

public section

namespace CFSG.Quasithin

namespace S153E56f

open CFSG.Quasithin.S153E

section Geometry

variable {W : Type} [CommGroup W] {q : W → ZMod 2}

theorem final_geom [Finite W] (hq : IsQuadraticFormOn q) (hn : IsNondegQuadratic q)
    (hexp : ∀ w : W, w * w = 1) (hcard : Nat.card W = 16) {yb tb a b : MulAut W}
    {Ub : Subgroup (MulAut W)} {zW kW : W} (hybO : yb ∈ orthogonalGroupOf q)
    (htbO : tb ∈ orthogonalGroupOf q) (hyb3 : yb ^ 3 = 1) (hybfix : fixV (Subgroup.zpowers yb) = ⊥)
    (hzW1 : zW ≠ 1) (hqz : q zW = 0) (htbz : tb zW = zW) (haU : a ∈ Ub)
    (hUb : ∀ x ∈ Ub, x = 1 ∨ x = a ∨ x = b ∨ x = a * b) (hUz : ∀ x ∈ Ub, x zW = zW)
    (hbz' : b (yb⁻¹ zW) = yb⁻¹ zW) (hall : (∀ x ∈ Ub, x (yb⁻¹ zW) = yb⁻¹ zW) → False)
    (hta : tb * a * tb⁻¹ = b) (hk1 : quadPolar q zW kW = 0) (hk2 : quadPolar q zW (yb kW) = 0)
    (hk3 : quadPolar q zW ((yb * tb) kW) = 0) : kW = 1 ∨ kW = zW := by
  obtain ⟨hz'1, hz'z, hqz', hzz', hqzz', h0⟩ := pair_of_order_three hexp hybO hyb3 hybfix hzW1 hqz
  have hybinv : yb⁻¹ ∈ orthogonalGroupOf q := (orthogonalGroupOf q).inv_mem hybO
  have hybtbinv : (yb * tb)⁻¹ ∈ orthogonalGroupOf q :=
    (orthogonalGroupOf q).inv_mem ((orthogonalGroupOf q).mul_mem hybO htbO)
  have hk2' : quadPolar q (yb⁻¹ zW) kW = 0 := by
    have h := quadPolar_apply_isometry hybinv zW (yb kW)
    have e : yb⁻¹ (yb kW) = kW := by simp
    rw [e] at h
    rw [h]
    exact hk2
  have hk3' : quadPolar q (tb⁻¹ (yb⁻¹ zW)) kW = 0 := by
    have h := quadPolar_apply_isometry hybtbinv zW ((yb * tb) kW)
    have e1 : (yb * tb)⁻¹ ((yb * tb) kW) = kW := by simp
    have e2 : (yb * tb)⁻¹ zW = tb⁻¹ (yb⁻¹ zW) := by rw [mul_inv_rev]; rfl
    rw [e1, e2] at h
    rw [h]
    exact hk3
  have hatb : a * tb⁻¹ = tb⁻¹ * b := by
    calc a * tb⁻¹ = tb⁻¹ * (tb * a * tb⁻¹) := by group
      _ = tb⁻¹ * b := by rw [hta]
  have haz : a zW = zW := hUz a haU
  have haz'' : a (tb⁻¹ (yb⁻¹ zW)) = tb⁻¹ (yb⁻¹ zW) := by
    calc a (tb⁻¹ (yb⁻¹ zW)) = (a * tb⁻¹) (yb⁻¹ zW) := rfl
      _ = (tb⁻¹ * b) (yb⁻¹ zW) := by rw [hatb]
      _ = tb⁻¹ (b (yb⁻¹ zW)) := rfl
      _ = tb⁻¹ (yb⁻¹ zW) := by rw [hbz']
  have hz''1 : tb⁻¹ (yb⁻¹ zW) ≠ 1 := by
    intro h
    apply hz'1
    have h' := congrArg tb h
    simpa using h'
  have hz''z : tb⁻¹ (yb⁻¹ zW) ≠ zW := by
    intro h
    apply hz'z
    have h' := congrArg tb h
    rw [MulAut.apply_inv_self, htbz] at h'
    exact h'
  have hz''z' : tb⁻¹ (yb⁻¹ zW) ≠ yb⁻¹ zW := by
    intro h
    apply hall
    apply fix_all hUb _ hbz'
    rw [h] at haz''
    exact haz''
  have hz''zz' : tb⁻¹ (yb⁻¹ zW) ≠ zW * yb⁻¹ zW := by
    intro h
    apply hall
    have hz'a : a (yb⁻¹ zW) = yb⁻¹ zW := by
      have h1 := haz''
      rw [h, map_mul, haz] at h1
      exact mul_left_cancel h1
    exact fix_all hUb hz'a hbz'
  have h0'' : quadPolar q zW (tb⁻¹ (yb⁻¹ zW)) = 0 := by
    have h := quadPolar_apply_isometry htbO zW (tb⁻¹ (yb⁻¹ zW))
    rw [htbz, MulAut.apply_inv_self] at h
    rw [← h]
    exact h0
  exact triple_perp hq hn hexp hcard hzW1 hz'1 (Ne.symm hz'z) h0 h0'' hz''1 hz''z hz''z' hz''zz'
    hk1 hk2' hk3'

end Geometry

end S153E56f

namespace S153E

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open CFSG.Quasithin.S153E56f
open scoped commutatorElement Pointwise

section Lemma

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem geo56_EEt (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} (c : Chain15355 cx N₁ N₂ g s) {y t₁ : G}
    (hy : y ∈ Yi153 T Mc M V₁ N₁ ∧ y ∉ pCoreOf 2 (Yi153 T Mc M V₁ N₁))
    (ht₁ : t₁ ∈ T ∧ t₁ ∉ UCT153 T M V₁ Mc) (iJ : JStruct56 T Mc M V₁ N₁ y) :
    Egp153 T M V₁ Mc y ⊓ conjSubgroup (Egp153 T M V₁ Mc y) t₁ ≤ quasithinOmegaOneCenter T := by
  intro k hk
  have hV := cx.c.hyp.elemAbelian
  have c' : Chain15353 cx N₁ N₂ := c.toChain15354.toChain15353
  have pd := S153E55.pdecomp cx c.toChain15354
  obtain ⟨hyN, hybN₁, hyb1, hyb3, hybfix⟩ := yb_facts h113 cx c hy
  obtain ⟨z, hzZ, hz1, hzu⟩ := exists_z cx
  obtain ⟨a, b, haU, hbU, haN, hbN, ha1, hb1, haa, hbb, hUb, hswap⟩ := ubdata cx c'
  obtain ⟨ht1N, htbT, htbU⟩ := tb_facts cx ht₁
  have hzV : z ∈ VZ T M := cx.c.hyp.Z_le_VZ hzZ
  have hexp : ∀ w : Wd cx, w * w = 1 := fun w => by rw [← pow_two]; exact IntMod.sq_eq_one w
  have hcard : Nat.card (Wd cx) = 16 := cx.c.hyp.card_VZ
  have hyNi : y ∈ Ni153 T Mc M V₁ N₁ := ((oTwoUpper_le _ hy.1 : y ∈ Y153 Mc M ⊓ Ni153 T Mc M V₁ N₁)).2
  have hyY : y ∈ Y153 Mc M := (oTwoUpper_le _ hy.1).1
  have hyYU : y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.mem_sup_left hyY
  have hyM : y ∈ M := Y153_le Mc M hyY
  have hzW1 : (IntMod.mk hV ⟨z, hzV⟩ : Wd cx) ≠ 1 := fun h => hz1 (congrArg IntMod.val h)
  have hqz : qW cx (IntMod.mk hV ⟨z, hzV⟩) = 0 := qW_Z cx hzZ
  obtain ⟨hta, htb'⟩ := hswap _ htbT htbU
  have hkE : k ∈ Egp153 T M V₁ Mc y := hk.1
  have hkEt : t₁ * k * t₁⁻¹ ∈ Egp153 T M V₁ Mc y := mem_conjSubgroup_iff.1 hk.2
  have hkF : k ∈ Fgp153 T M V₁ Mc y := hkE.1
  have hkP : k ∈ Pgp153 T M V₁ Mc g :=
    inf_F_le_P h113 cx c hy ht₁ k ⟨hkF, mem_conjSubgroup_iff.2 hkEt.1⟩
  have hcomm₁ := comm_y_mem_V h113 cx c hy iJ k ⟨hkE, hkP⟩
  have hkP₂ : k ∈ Pi153 T Mc M V₁ N₂ g :=
    fpf_mem pd c.h54.four_nat₁ hyNi (not_mem_P c.toChain15354 hyN hyb1)
      (pow_three_mem_P cx c.toChain15354 hyYU hyN hyb3) hkP hcomm₁
  have hkP' : t₁ * k * t₁⁻¹ ∈ Pgp153 T M V₁ Mc g :=
    (Subgroup.mem_normalizer_iff.1 (S153E55.T_le_normalizer_P c.h54.one cx ht₁.1) k).1 hkP
  have hcomm₂ := comm_y_mem_V h113 cx c hy iJ _ ⟨hkEt, hkP'⟩
  obtain ⟨hwNi, hwP, hw3P⟩ := w_facts h113 cx c hy ht₁
  have hcomm₂' : k * (t₁⁻¹ * y * t₁) * k⁻¹ * (t₁⁻¹ * y * t₁)⁻¹ ∈ VZ T M := by
    have e : k * (t₁⁻¹ * y * t₁) * k⁻¹ * (t₁⁻¹ * y * t₁)⁻¹ =
        t₁⁻¹ * ((t₁ * k * t₁⁻¹) * y * (t₁ * k * t₁⁻¹)⁻¹ * y⁻¹) * t₁ := by group
    rw [e]
    exact conj_inv_mem_V ht1N hcomm₂
  have hkP₁ : k ∈ Pi153 T Mc M V₁ N₁ g :=
    fpf_mem pd.symm c.h54.four_nat₂ hwNi hwP hw3P hkP hcomm₂'
  have hkV : k ∈ VZ T M := by
    have h : k ∈ Pi153 T Mc M V₁ N₁ g ⊓ Pi153 T Mc M V₁ N₂ g := ⟨hkP₁, hkP₂⟩
    rw [c.h54.four_inf] at h
    exact h
  have hkU : k ∈ UH153 T M V₁ Mc := hkF.1
  have hk1 := orth_z_of_mem cx c' hzZ (v := k) ⟨hkV, hkU⟩
  have hyk : y * k * y⁻¹ ∈ VZ T M ⊓ UH153 T M V₁ Mc :=
    ⟨conj_mem_V hyN hkV, (mem_conjSubgroup_iff.1 hkE.2).1⟩
  have hk2 := orth_z_of_mem cx c' hzZ hyk
  have hyt : y * (t₁ * k * t₁⁻¹) * y⁻¹ ∈ VZ T M ⊓ UH153 T M V₁ Mc :=
    ⟨conj_mem_V hyN (conj_mem_V ht1N hkV), (mem_conjSubgroup_iff.1 hkEt.2).1⟩
  have hk3 := orth_z_of_mem cx c' hzZ hyt
  have hUz : ∀ x ∈ autI hV (UH153 T M V₁ Mc),
      x (IntMod.mk hV ⟨z, hzV⟩) = IntMod.mk hV ⟨z, hzV⟩ :=
    fun x hx => (mem_fixV_autI_T_iff cx (IntMod.mk hV ⟨z, hzV⟩)).2 hzZ x (autI_U_le_T cx hx)
  have hbz' : b ((cb cx y hyN)⁻¹ (IntMod.mk hV ⟨z, hzV⟩)) =
      (cb cx y hyN)⁻¹ (IntMod.mk hV ⟨z, hzV⟩) := by
    have hcomm : Commute (cb cx y hyN) b := c.h53one.comm _ hybN₁ b hbN
    have hcomm' : b * (cb cx y hyN)⁻¹ = (cb cx y hyN)⁻¹ * b := hcomm.inv_left.eq.symm
    calc b ((cb cx y hyN)⁻¹ (IntMod.mk hV ⟨z, hzV⟩))
        = (b * (cb cx y hyN)⁻¹) (IntMod.mk hV ⟨z, hzV⟩) := rfl
      _ = ((cb cx y hyN)⁻¹ * b) (IntMod.mk hV ⟨z, hzV⟩) := by rw [hcomm']
      _ = (cb cx y hyN)⁻¹ (b (IntMod.mk hV ⟨z, hzV⟩)) := rfl
      _ = (cb cx y hyN)⁻¹ (IntMod.mk hV ⟨z, hzV⟩) := by rw [hUz b hbU]
  obtain ⟨hz'1, hz'z, -, -, -, -⟩ :=
    pair_of_order_three hexp (cb_mem_O cx hyM hyN) hyb3 hybfix hzW1 hqz
  have hall : (∀ x ∈ autI hV (UH153 T M V₁ Mc),
      x ((cb cx y hyN)⁻¹ (IntMod.mk hV ⟨z, hzV⟩)) = (cb cx y hyN)⁻¹ (IntMod.mk hV ⟨z, hzV⟩)) →
      False := by
    intro hall
    have hmem := fixed_by_Ub_mem_Z cx c' hall
    rcases hzu _ hmem with h | h
    · exact hz'1 (IntMod.val_injective h)
    · exact hz'z (IntMod.val_injective h)
  have htbz : cb cx t₁ ht1N (IntMod.mk hV ⟨z, hzV⟩) = IntMod.mk hV ⟨z, hzV⟩ :=
    (mem_fixV_autI_T_iff cx (IntMod.mk hV ⟨z, hzV⟩)).2 hzZ _ htbT
  have hgeo := final_geom (W := Wd cx) (q := qW cx) (qW_spec cx).1 (qW_spec cx).2.1 hexp hcard
    (kW := IntMod.mk hV ⟨k, hkV⟩) (cb_mem_O cx hyM hyN)
    (cb_mem_O cx (T_le_M cx ht₁.1) ht1N) hyb3 hybfix hzW1 hqz htbz haU hUb hUz hbz' hall hta
    hk1 (by
      have e : cb cx y hyN (IntMod.mk hV ⟨k, hkV⟩) = IntMod.mk hV ⟨y * k * y⁻¹, hyk.1⟩ :=
        IntMod.val_injective (by rw [cb_val]; rfl)
      rw [e]
      exact hk2)
    (by
      have e : (cb cx y hyN * cb cx t₁ ht1N) (IntMod.mk hV ⟨k, hkV⟩) =
          IntMod.mk hV ⟨y * (t₁ * k * t₁⁻¹) * y⁻¹, hyt.1⟩ :=
        IntMod.val_injective (by rw [MulAut.mul_apply, cb_val, cb_val]; rfl)
      rw [e]
      exact hk3)
  rcases hgeo with h | h
  · have : k = 1 := congrArg IntMod.val h
    rw [this]
    exact Subgroup.one_mem _
  · have : k = z := congrArg IntMod.val h
    rw [this]
    exact hzZ

end Lemma

end S153E

end CFSG.Quasithin
