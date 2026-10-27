module

public import CFSG.Sporadic.SuzRecog.MixedCellGen
public import CFSG.Sporadic.SuzRecog.MixedCellTwist
public import CFSG.Sporadic.SuzRecog.LevelTwoCoverCells
public import CFSG.Sporadic.SuzRecog.Rigid

public section

namespace CFSG.Sporadic.SuzRecog.MixedCell

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.CosetEnumeration CFSG.Sporadic.SuzRecog.MixedCellData
  CFSG.Sporadic.SuzRecog.MixedCellCheck LevelTwoCover

local notation "Pm" => Equiv.Perm (Fin 1782)
section BoundZ


variable {G : Type} [Group G] [Finite G] {S : CFSG.LargeExtraspecial.Setting G}

omit
  [Finite G] in
theorem sig_t1 (σ : S.M ≃* invE 1) : sig σ ⟨suzInv 1, t1_mem_C1⟩ = S.z := by
  have hc : (⟨suzInv 1, t1_mem_C1⟩ : ↥(invE 1)) ∈ center ↥(invE 1) :=
    mem_center_iff.2 fun g => Subtype.ext (comm_t1' g.2)
  have h1 : (⟨suzInv 1, t1_mem_C1⟩ : ↥(invE 1)) ≠ 1 := fun h =>
    suzInv_ne_one (by norm_num : 1 < 4) (congrArg Subtype.val h)
  have e : σ.symm ⟨suzInv 1, t1_mem_C1⟩ = S.zM := by
    rw [← map_zM_eq S σ hc h1, MulEquiv.symm_apply_apply]
  rw [sig_apply, e]
  rfl

theorem bound_mem (j : Fin 2) (n : ℕ) (hn : n < (boundW (2 * j.val)).length) :
    (boundW (2 * j.val)).getD n [] ∈ boundW (2 * j.val) := by
  rw [List.getD_eq_getElem _ _ hn]
  exact List.getElem_mem hn

theorem bound_length (j : Fin 2) : 2 ≤ (boundW (2 * j.val)).length := by
  fin_cases j <;> decide

omit [Finite G] in
theorem disc_bound {σ : S.M ≃* invE 1} {ψ : Model.NR0 →* G} {ζ : centM wP →* G}
    (hB : B0Agree σ ψ) (hζ : ChartAgree σ ζ) (j : Fin 2) :
    ∃ n < 16, cellG σ ψ j = ζ ⟨sP, sP_mem_centM⟩ * sig σ ⟨candP j n, candP_mem j n⟩ := by
  set D := (ζ ⟨sP, sP_mem_centM⟩)⁻¹ * cellG σ ψ j with hD
  have hbm : ∀ w ∈ boundW (2 * j.val), evalWord genM w ∈ invE 1 := fun w hw =>
    evalWord_mem_of _ _ fun c hc => genM_mem_invE c (bound_codes j w hw c hc)
  have hcomm : ∀ w (hw : w ∈ boundW (2 * j.val)),
      D * sig σ ⟨evalWord genM w, hbm w hw⟩ = sig σ ⟨evalWord genM w, hbm w hw⟩ * D := by
    intro w hw
    obtain ⟨hp, hN, h2, h3⟩ := bound_facts j w hw
    exact disc_comm hB hζ j (hbm w hw) hp hN h2 h3
  have hlen := bound_length j
  have hw1 := bound_mem j 1 (by omega)
  have hz : D * S.z = S.z * D := by
    have h := hcomm _ hw1
    have e : (⟨evalWord genM ((boundW (2 * j.val)).getD 1 []), hbm _ hw1⟩ : ↥(invE 1)) =
        ⟨suzInv 1, t1_mem_C1⟩ := Subtype.ext (bound_one_val j)
    rwa [e, sig_t1] at h
  have hDM : D ∈ S.M := (S.mem_M_iff).2 hz
  set d := σ ⟨D, hDM⟩ with hd
  have hdc : ∀ w (hw : w ∈ boundW (2 * j.val)),
      (d : Pm) * evalWord genM w = evalWord genM w * d := by
    intro w hw
    have h := hcomm w hw
    have h' : (⟨D, hDM⟩ : S.M) * σ.symm ⟨evalWord genM w, hbm w hw⟩ =
        σ.symm ⟨evalWord genM w, hbm w hw⟩ * ⟨D, hDM⟩ := Subtype.ext h
    have h'' := congrArg σ h'
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h''
    exact congrArg Subtype.val h''
  have hw0 := bound_mem j 0 (by omega)
  have hρ : (d : Pm) * Model.rho1 = Model.rho1 * d := by
    have h := hdc _ hw0
    rwa [bound_zero j, show evalWord genM [4] = Model.rho1 by
      simp [evalWord_cons, evalWord_nil, genM, letter]] at h
  have hK : (d : Pm) ∈ invE 1 ⊓ Model.Crho1 :=
    mem_inf.2 ⟨d.2, ModelGroups.mem_Crho1_iff.2 ⟨hρ, invE_le_suzM' d.2⟩⟩
  rw [RootTwist.K_eq_closure] at hK
  obtain ⟨i, hi, hdi⟩ := RootTwist.exists_eq_kElt hK
  obtain ⟨n, hn, hni⟩ := bound_cut j i hi fun w hw => by
    rw [← hdi]
    exact hdc w hw
  refine ⟨n, hn, ?_⟩
  have hdn : d = ⟨candP j n, candP_mem j n⟩ := Subtype.ext (hdi.trans hni)
  have hDs : D = sig σ ⟨candP j n, candP_mem j n⟩ := by
    rw [sig_apply, ← hdn, hd, MulEquiv.symm_apply_apply]
  rw [← hDs, hD, mul_inv_cancel_left]

end BoundZ


section Collapse


variable {G : Type} [Group G] {M : Subgroup G}

theorem false_of_closure {σ : M ≃* invE 1} {ψ : Model.NR0 →* G} {ζ : centM wP →* G}
    (hB : B0Agree σ ψ)
    (hcl : ∀ x < 4, gGen σ ψ ζ x ∈ closure {gGen σ ψ ζ 4, gGen σ ψ ζ 6, gGen σ ψ ζ 8}) :
    False := by
  set Q : Subgroup ↥Model.NR0 := (Model.Crho1 ⊓ Model.NR0).subgroupOf Model.NR0 with hQ
  have hle : closure {gGen σ ψ ζ 4, gGen σ ψ ζ 6, gGen σ ψ ζ 8} ≤ Q.map ψ := by
    rw [closure_le]
    have h4 : gGen σ ψ ζ 4 = ψ ⟨Model.rho1, ModelGroups.rho1_mem_NR0⟩ := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, gGen_even]; rfl
    have h6 : gGen σ ψ ζ 6 = ψ ⟨ja, ja_mem.2⟩ := by
      rw [show (6 : ℕ) = 2 * 3 by rfl, gGen_even]; rfl
    have h8 : gGen σ ψ ζ 8 = ψ ⟨jb, jb_mem.2⟩ := by
      rw [show (8 : ℕ) = 2 * 4 by rfl, gGen_even]; rfl
    rintro x (rfl | rfl | rfl)
    · rw [h4]
      exact ⟨_, mem_subgroupOf.2 (mem_inf.2 ⟨ModelGroups.mem_Crho1_iff.2 ⟨rfl,
        ModelGroups.rho1_mem_suzM⟩, ModelGroups.rho1_mem_NR0⟩), rfl⟩
    · rw [h6]
      exact ⟨_, mem_subgroupOf.2 ja_mem, rfl⟩
    · rw [h8]
      exact ⟨_, mem_subgroupOf.2 jb_mem, rfl⟩
  have hlet : ∀ c < 4, gGen σ ψ ζ c ∈ Q.map ψ := fun c hc => hle (hcl c hc)
  have hgen : ∀ (w : List ℕ) (hw : ∀ c ∈ w, c < 4) (e : Pm) (he : evalWord genM w = e)
      (h : e ∈ invE 1), sig σ ⟨e, h⟩ ∈ Q.map ψ := by
    intro w hw e he h
    have hw6 : ∀ c ∈ w, c < 6 := fun c hc => by have := hw c hc; omega
    subst he
    rw [← evalWord_sig ζ hB hw6 h]
    exact evalWord_mem_of _ _ fun c hc => hlet c (hw c hc)
  set K₁ : Subgroup ↥(invE 1) := (invE 1 ⊓ Model.Crho1).subgroupOf (invE 1) with hK₁
  have hK : K₁.map (sig σ) ≤ Q.map ψ := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : Pm) ∈ closure {RootTwist.kGenA, RootTwist.kGenB} := by
      rw [← RootTwist.K_eq_closure]
      exact mem_subgroupOf.1 hy
    have key : ∀ g (hg : g ∈ closure {RootTwist.kGenA, RootTwist.kGenB}) (h : g ∈ invE 1),
        sig σ ⟨g, h⟩ ∈ Q.map ψ := by
      intro g hg
      induction hg using closure_induction with
      | mem x hx =>
        intro h
        rcases hx with rfl | rfl
        · exact hgen kGenAW kGen_codes.1 _ kGenA_val h
        · exact hgen kGenBW kGen_codes.2 _ kGenB_val h
      | one =>
        intro h
        have e : (⟨1, h⟩ : ↥(invE 1)) = 1 := rfl
        rw [e, map_one]
        exact one_mem _
      | mul x y hx hy ihx ihy =>
        intro h
        have hxK : x ∈ invE 1 := (mem_inf.1 (RootTwist.K_eq_closure ▸ hx)).1
        have hyK : y ∈ invE 1 := (mem_inf.1 (RootTwist.K_eq_closure ▸ hy)).1
        have e : (⟨x * y, h⟩ : ↥(invE 1)) = ⟨x, hxK⟩ * ⟨y, hyK⟩ := rfl
        rw [e, map_mul]
        exact mul_mem (ihx hxK) (ihy hyK)
      | inv x hx ihx =>
        intro h
        have hxK : x ∈ invE 1 := (mem_inf.1 (RootTwist.K_eq_closure ▸ hx)).1
        have e : (⟨x⁻¹, h⟩ : ↥(invE 1)) = (⟨x, hxK⟩)⁻¹ := rfl
        rw [e, map_inv]
        exact inv_mem (ihx hxK)
    exact key _ hy' y.2
  have hinj : Function.Injective (sig σ) := fun a b h =>
    σ.symm.injective (Subtype.ext h)
  have hcK : Nat.card (K₁.map (sig σ)) = 3456 := by
    rw [card_map_of_injective hinj, hK₁,
      Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv, RootTwist.card_K]
  have hcQ : Nat.card Q = 60480 := by
    rw [hQ, Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv,
      ModelGroups.card_Crho1_inf_NR0]
  have h1 := card_dvd_of_le hK
  have h2 := card_map_dvd Q ψ
  rw [hcK] at h1
  rw [hcQ] at h2
  have := h1.trans h2
  norm_num at this

end Collapse


@[expose] def twistCase (a b : ℕ) : Bool :=
  singleChecks.any (fun t => t.1 == 0 && t.2.1 == a) ||
    singleChecks.any (fun t => t.1 == 2 && t.2.1 == b) ||
    pairChecks.any (fun t => t.1 == a && t.2.1 == b) ||
    (a == 0 && b == 0) || (a == 1 && b == 1) || (a == 15 && b == 7) || (a == 8 && b == 8)

theorem twistCase_all : ∀ a < 16, ∀ b < 16, twistCase a b = true := by
  decide

theorem twist_cases {a b : ℕ} (ha : a < 16) (hb : b < 16) :
    (∃ t ∈ singleChecks, t.1 = 0 ∧ t.2.1 = a) ∨ (∃ t ∈ singleChecks, t.1 = 2 ∧ t.2.1 = b) ∨
      (∃ t ∈ pairChecks, t.1 = a ∧ t.2.1 = b) ∨ (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) ∨
      (a = 15 ∧ b = 7) ∨ (a = 8 ∧ b = 8) := by
  have h := twistCase_all a ha b hb
  simp only [twistCase, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with (((((h | h) | h) | h) | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))


section Final


variable {G : Type} [Group G] {M : Subgroup G}

theorem cellRel_of {σ : M ≃* invE 1} {ψ : Model.NR0 →* G} {ζ : centM wP →* G}
    (h : ∀ j : Fin 2, ψ ⟨eP j, eP_mem j⟩ = (sig σ ⟨cP j, cP_mem j⟩)⁻¹ * ζ ⟨sP, sP_mem_centM⟩ *
      sig σ ⟨cP' j, cP'_mem j⟩) :
    CellRel coverData proj σ ψ ζ := by
  intro k h₁ h₂ h₃ h₄
  have e1 : ((proj ((coverData.c k)⁻¹ * coverData.s * coverData.c' k) : Model.Crho1) : Pm) =
      eP k := by
    have := proj_cell k
    refine this.trans ?_
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, coe_sX, coe_cX, coe_c'X, eP]
  have e2 : ((proj (coverData.c k) : Model.Crho1) : Pm) = cP k := (proj_cC k).trans (coe_cX k)
  have e3 : ((proj coverData.s : Model.Crho1) : Pm) = sP := proj_sC.trans coe_sX
  have e4 : ((proj (coverData.c' k) : Model.Crho1) : Pm) = cP' k :=
    (proj_c'C k).trans (coe_c'X k)
  have f1 : ψ ⟨_, h₁⟩ = ψ ⟨eP k, eP_mem k⟩ := congrArg ψ (Subtype.ext e1)
  have f2 : (⟨_, h₂⟩ : ↥(invE 1)) = ⟨cP k, cP_mem k⟩ := Subtype.ext e2
  have f3 : ζ ⟨_, h₃⟩ = ζ ⟨sP, sP_mem_centM⟩ := congrArg ζ (Subtype.ext e3)
  have f4 : (⟨_, h₄⟩ : ↥(invE 1)) = ⟨cP' k, cP'_mem k⟩ := Subtype.ext e4
  rw [f1, f2, f3, f4]
  exact h k

end Final


section Cases


variable {G : Type} [Group G] {M : Subgroup G}

theorem psi_eP_eq {σ : M ≃* invE 1} {ψ : Model.NR0 →* G} (j : Fin 2) {g : G}
    (h : cellG σ ψ j = g) :
    ψ ⟨eP j, eP_mem j⟩ = (sig σ ⟨cP j, cP_mem j⟩)⁻¹ * g * sig σ ⟨cP' j, cP'_mem j⟩ := by
  rw [← h, cellG]
  group

theorem sig_remark (σ : M ≃* invE 1) (x : ↥(invE 1)) (c : ↥(invE 1)) :
    sig (remark σ x) c = sig σ x * sig σ c * (sig σ x)⁻¹ := by
  rw [sig_apply, remark_symm_apply, map_mul, map_mul, map_inv]
  rfl

theorem wP_mem : wP ∈ invE 1 := by
  have h := candP_mem 0 1
  rwa [candP, delta_one_val] at h

theorem wP_mem_centM : wP ∈ centM wP :=
  mem_inf.2 ⟨mem_centralizer_singleton_iff.2 rfl, invE_le_suzM' wP_mem⟩

theorem t1_mem_centM : suzInv 1 ∈ centM wP := by
  refine mem_centM_wP t1_mem_C1 ?_
  exact (LevelTwo.commute_aP_p1).symm

theorem t1_conj_sP : suzInv 1 * sP * (suzInv 1)⁻¹ = sP * wP := by
  have h := sP_conj_p1
  have ht : suzInv 1 * suzInv 1 = 1 := suzInv_sq (by norm_num : 1 < 4)
  have hti : (suzInv 1)⁻¹ = suzInv 1 := inv_eq_of_mul_eq_one_right ht
  have hc : p1P * suzInv 1 = suzInv 1 * p1P := LevelTwo.commute_aP_p1.eq
  have e : suzInv 1 * sP = sP * p1P := by
    rw [← h]; group
  rw [hti, e, mul_assoc, hc]
  rfl

theorem conj_z_sP {S : CFSG.LargeExtraspecial.Setting G} [Finite G] {σ : S.M ≃* invE 1}
    {ζ : centM wP →* G} (hζ : ChartAgree σ ζ) :
    ((MulAut.conj S.z).toMonoidHom.comp ζ) ⟨sP, sP_mem_centM⟩ =
      ζ ⟨sP, sP_mem_centM⟩ * sig σ ⟨wP, wP_mem⟩ := by
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← sig_t1 σ, sig_apply,
    ← hζ _ t1_mem_C1 t1_mem_centM, sig_apply, ← hζ _ wP_mem wP_mem_centM, ← map_inv, ← map_mul,
    ← map_mul, ← map_mul]
  refine congrArg ζ (Subtype.ext ?_)
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
  exact t1_conj_sP

theorem chartAgree_conj_z {S : CFSG.LargeExtraspecial.Setting G} {σ : S.M ≃* invE 1}
    {ζ : centM wP →* G} (hζ : ChartAgree σ ζ) :
    ChartAgree σ ((MulAut.conj S.z).toMonoidHom.comp ζ) := by
  intro y hy hyw
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hζ y hy hyw]
  have h := (S.mem_M_iff).1 (σ.symm ⟨y, hy⟩).2
  rw [← h, mul_inv_cancel_right]

theorem bad_cell {σ : M ≃* invE 1} {ψ : Model.NR0 →* G} {ζ₀ ζ₁ : centM wP →* G}
    (hζ₀ : ChartAgree σ ζ₀) (j : Fin 2) {δ u : Pm} (hδ : δ ∈ invE 1) (hu : u ∈ invE 1)
    (hcell : cellG σ ψ j = ζ₀ ⟨sP, sP_mem_centM⟩ * sig σ ⟨δ, hδ⟩)
    (hζ₁ : ζ₁ ⟨sP, sP_mem_centM⟩ = ζ₀ ⟨sP, sP_mem_centM⟩ * sig σ ⟨u, hu⟩)
    (hid : sP⁻¹ * (cP j * xM * (cP j)⁻¹) * sP * δ * (cP' j * xM * (cP' j)⁻¹) = u) :
    ψ ⟨eP j, eP_mem j⟩ = (sig (remark σ ⟨xM, xM_mem.1⟩) ⟨cP j, cP_mem j⟩)⁻¹ *
      ((MulAut.conj ((σ.symm ⟨xM, xM_mem.1⟩ : M) : G)).toMonoidHom.comp ζ₁) ⟨sP, sP_mem_centM⟩ *
      sig (remark σ ⟨xM, xM_mem.1⟩) ⟨cP' j, cP'_mem j⟩ := by
  have hx := xM_mem.1
  have hC := cP_mem j
  have hC' := cP'_mem j
  have hsP := sP_mem_centM
  obtain ⟨hap, hat⟩ := bad_comm j
  set a := cP j * xM * (cP j)⁻¹ with ha
  set b := cP' j * xM * (cP' j)⁻¹ with hb
  have ha1 : a ∈ invE 1 := mul_mem (mul_mem hC hx) (inv_mem hC)
  have hb1 : b ∈ invE 1 := mul_mem (mul_mem hC' hx) (inv_mem hC')
  have haw : a ∈ centM wP := mem_centM_wP ha1 hap
  have has1 : sP⁻¹ * a * sP ∈ invE 1 :=
    ModelGroups.mem_invE_one_iff.2 ⟨hat.eq, (mem_inf.1 (mul_mem (mul_mem (inv_mem hsP) haw)
      hsP)).2⟩
  have hasw : sP⁻¹ * a * sP ∈ centM wP := mul_mem (mul_mem (inv_mem hsP) haw) hsP
  set X := sig σ ⟨xM, hx⟩ with hX
  have k1 : ζ₀ ⟨sP, hsP⟩ * sig σ ⟨sP⁻¹ * a * sP, has1⟩ = sig σ ⟨a, ha1⟩ * ζ₀ ⟨sP, hsP⟩ := by
    rw [sig_apply, sig_apply, ← hζ₀ _ has1 hasw, ← hζ₀ _ ha1 haw]
    exact hom_mul_eq ζ₀ hsP hasw haw hsP (by group)
  have k2 : X * (sig σ ⟨cP j, hC⟩)⁻¹ * sig σ ⟨a, ha1⟩ = (sig σ ⟨cP j, hC⟩)⁻¹ := by
    have e : (⟨xM, hx⟩ : ↥(invE 1)) * (⟨cP j, hC⟩)⁻¹ * ⟨a, ha1⟩ = (⟨cP j, hC⟩)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, ha]
      calc xM * (cP j)⁻¹ * (cP j * xM * (cP j)⁻¹) = xM * xM * (cP j)⁻¹ := by group
        _ = (cP j)⁻¹ := by rw [xM_mul_self, one_mul]
    have h2 := congrArg (sig σ) e
    rw [map_mul, map_mul, map_inv] at h2
    exact h2
  have k3 : sig σ ⟨b, hb1⟩ * sig σ ⟨cP' j, hC'⟩ * X⁻¹ = sig σ ⟨cP' j, hC'⟩ := by
    rw [hX, ← map_inv, ← map_mul, ← map_mul]
    refine congrArg (sig σ) (Subtype.ext ?_)
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hb]
    group
  have k4 : sig σ ⟨u, hu⟩ = sig σ ⟨sP⁻¹ * a * sP, has1⟩ * sig σ ⟨δ, hδ⟩ * sig σ ⟨b, hb1⟩ := by
    rw [← map_mul, ← map_mul]
    refine congrArg (sig σ) (Subtype.ext ?_)
    simp only [Subgroup.coe_mul]
    rw [← hid]
  rw [psi_eP_eq j hcell, sig_remark, sig_remark, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, hζ₁, k4]
  rw [show ((σ.symm ⟨xM, xM_mem.1⟩ : M) : G) = X from rfl,
    show sig σ ⟨xM, xM_mem.1⟩ = X from rfl]
  calc (sig σ ⟨cP j, hC⟩)⁻¹ * (ζ₀ ⟨sP, hsP⟩ * sig σ ⟨δ, hδ⟩) * sig σ ⟨cP' j, hC'⟩ =
        (X * (sig σ ⟨cP j, hC⟩)⁻¹ * sig σ ⟨a, ha1⟩) * ζ₀ ⟨sP, hsP⟩ * sig σ ⟨δ, hδ⟩ *
          (sig σ ⟨b, hb1⟩ * sig σ ⟨cP' j, hC'⟩ * X⁻¹) := by rw [k2, k3]; group
    _ = X * (sig σ ⟨cP j, hC⟩)⁻¹ * (sig σ ⟨a, ha1⟩ * ζ₀ ⟨sP, hsP⟩) * sig σ ⟨δ, hδ⟩ *
          sig σ ⟨b, hb1⟩ * sig σ ⟨cP' j, hC'⟩ * X⁻¹ := by group
    _ = _ := by rw [← k1]; group

end Cases


section Main


theorem mixedCellDichotomy_wP : MixedCellDichotomy coverData proj wP := by
  intro G _ _ _ S _ σ ψ ζ₀ hB hζ₀
  have hinv := gGen_inv σ ψ ζ₀
  have hbase := baseRels_val hB hζ₀
  obtain ⟨n₀, hn₀, e₀⟩ := disc_bound hB hζ₀ 0
  obtain ⟨n₂, hn₂, e₂⟩ := disc_bound hB hζ₀ 1
  have hc₀ : evalWord (gGen σ ψ ζ₀) (cellRel 0 n₀) = 1 := cellRel_val hB 0 n₀ e₀
  have hc₂ : evalWord (gGen σ ψ ζ₀) (cellRel 2 n₂) = 1 := cellRel_val hB 1 n₂ e₂
  rcases twist_cases hn₀ hn₂ with ⟨t, ht, h1, h2⟩ | ⟨t, ht, h1, h2⟩ | ⟨t, ht, h1, h2⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exfalso
    have hc := collapseMem_of_singleMem single_checks t ht
    rw [h1, h2] at hc
    refine false_of_closure hB (mem_closure_of_collapseMem hinv hbase ?_ hc)
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hc₀
  · exfalso
    have hc := collapseMem_of_singleMem single_checks t ht
    rw [h1, h2] at hc
    refine false_of_closure hB (mem_closure_of_collapseMem hinv hbase ?_ hc)
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hc₂
  · exfalso
    have hc := collapseMem_of_pairMem pair_checks t ht
    rw [h1, h2] at hc
    refine false_of_closure hB (mem_closure_of_collapseMem hinv hbase ?_ hc)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hc₀
    · exact hc₂
  ·
    refine ⟨σ, ζ₀, Or.inl hB, hζ₀, cellRel_of fun j => ?_⟩
    have e : ∀ j : Fin 2, cellG σ ψ j = ζ₀ ⟨sP, sP_mem_centM⟩ * sig σ ⟨candP j 0, candP_mem j 0⟩ :=
      fun j => by
        fin_cases j
        · exact e₀
        · exact e₂
    have h1 : (⟨candP j 0, candP_mem j 0⟩ : ↥(invE 1)) = 1 := by
      apply Subtype.ext
      show evalWord genM ((deltaW (2 * j.val)).getD 0 []) = 1
      rw [delta_zero j]
      rfl
    rw [psi_eP_eq j (e j), h1, map_one, mul_one]
  ·
    refine ⟨σ, (MulAut.conj S.z).toMonoidHom.comp ζ₀, Or.inl hB, chartAgree_conj_z hζ₀,
      cellRel_of fun j => ?_⟩
    have e : ∀ j : Fin 2, cellG σ ψ j = ζ₀ ⟨sP, sP_mem_centM⟩ * sig σ ⟨candP j 1, candP_mem j 1⟩ :=
      fun j => by
        fin_cases j
        · exact e₀
        · exact e₂
    have h1 : (⟨candP j 1, candP_mem j 1⟩ : ↥(invE 1)) = ⟨wP, wP_mem⟩ :=
      Subtype.ext (delta_one_val j)
    rw [psi_eP_eq j (e j), h1, conj_z_sP hζ₀]
  ·
    have hxρ : xM * Model.rho1 = Model.rho1 * xM := (ModelGroups.mem_Crho1_iff.1 xM_mem.2).1
    refine ⟨remark σ ⟨xM, xM_mem.1⟩,
      (MulAut.conj ((σ.symm ⟨xM, xM_mem.1⟩ : S.M) : G)).toMonoidHom.comp ζ₀,
      Or.inr (b0TwistAgree_remark hB ⟨xM, xM_mem.1⟩ hxρ xM_V0 xM_tau0),
      chartAgree_remark hζ₀ _, cellRel_of fun j => ?_⟩
    have ht : ((15 : ℕ), (7 : ℕ), (0 : ℕ)) ∈ badPairs := by decide
    have e : ∀ j : Fin 2, cellG σ ψ j = ζ₀ ⟨sP, sP_mem_centM⟩ *
        sig σ ⟨candP j (if j.val = 0 then 15 else 7), candP_mem j _⟩ :=
      fun j => by
        fin_cases j
        · exact e₀
        · exact e₂
    refine bad_cell hζ₀ j (candP_mem j _) (one_mem _) (e j) ?_ ?_
    · rw [show (⟨1, one_mem _⟩ : ↥(invE 1)) = 1 from rfl, map_one, mul_one]
    · exact bad_val j ht
  ·
    have hxρ : xM * Model.rho1 = Model.rho1 * xM := (ModelGroups.mem_Crho1_iff.1 xM_mem.2).1
    refine ⟨remark σ ⟨xM, xM_mem.1⟩,
      (MulAut.conj ((σ.symm ⟨xM, xM_mem.1⟩ : S.M) : G)).toMonoidHom.comp
        ((MulAut.conj S.z).toMonoidHom.comp ζ₀),
      Or.inr (b0TwistAgree_remark hB ⟨xM, xM_mem.1⟩ hxρ xM_V0 xM_tau0),
      chartAgree_remark (chartAgree_conj_z hζ₀) _, cellRel_of fun j => ?_⟩
    have ht : ((8 : ℕ), (8 : ℕ), (1 : ℕ)) ∈ badPairs := by decide
    have e : ∀ j : Fin 2, cellG σ ψ j = ζ₀ ⟨sP, sP_mem_centM⟩ *
        sig σ ⟨candP j (if j.val = 0 then 8 else 8), candP_mem j _⟩ :=
      fun j => by
        fin_cases j
        · exact e₀
        · exact e₂
    exact bad_cell hζ₀ j (candP_mem j _) wP_mem (e j) (conj_z_sP hζ₀) (bad_val j ht)

theorem mixedCellDichotomy :
    MixedCellDichotomy coverData proj (suzInv 1 * LevelTwo.aP LevelTwo.p1) :=
  mixedCellDichotomy_wP

end Main

end CFSG.Sporadic.SuzRecog.MixedCell
