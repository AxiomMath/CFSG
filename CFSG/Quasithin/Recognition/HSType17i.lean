module

public import CFSG.Quasithin.Recognition.HSType17j
public import CFSG.Quasithin.Recognition.HSTypeFactAut2
public import CFSG.Quasithin.Recognition.HSType154

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin MulAction
open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

theorem eq_zero_of_lamS_fix : ∀ u : SpV, actS6 αS u = u → actS6 βS u = u → u = 0 := by
  decide

namespace HSCtx

variable {G : Type} [Group G] [Finite G] (C : HSCtx G)

theorem eq_one_of_comm_L1 {x : G} (hx : ∀ k ∈ C.L1, x * k = k * x) : x = 1 := by
  have hxB : x ∈ hsB C.z C.s := by
    rw [← C.h.centralizer_hsB C.hsmemH C.hsnotK C.hss C.hg₀]
    exact Subgroup.mem_centralizer_iff.mpr fun b hb => (hx b (C.M.hsB_le_pre lamS hb)).symm
  obtain ⟨u, rfl⟩ := C.M.surj x hxB
  obtain ⟨a, ha⟩ := C.M.π_surj αS
  obtain ⟨b, hb⟩ := C.M.π_surj βS
  have haL : (a : G) ∈ C.L1 := C.M.mem_pre.mpr ⟨a.2, by
    rw [show (⟨(a : G), a.2⟩ : ↥(HSSetting.hsNB C.z C.s)) = a from rfl, ha]; exact αS_mem⟩
  have hbL : (b : G) ∈ C.L1 := C.M.mem_pre.mpr ⟨b.2, by
    rw [show (⟨(b : G), b.2⟩ : ↥(HSSetting.hsNB C.z C.s)) = b from rfl, hb]; exact βS_mem⟩
  have e1 := C.M.act a u
  have e2 := C.M.act b u
  rw [ha] at e1
  rw [hb] at e2
  have ha' : (a : G) * C.M.Φ u * (a : G)⁻¹ = C.M.Φ u := by
    rw [← hx _ haL, mul_inv_cancel_right]
  have hb' : (b : G) * C.M.Φ u * (b : G)⁻¹ = C.M.Φ u := by
    rw [← hx _ hbL, mul_inv_cancel_right]
  rw [eq_zero_of_lamS_fix u (C.M.inj (e1.symm.trans ha')) (C.M.inj (e2.symm.trans hb')),
    C.M.Φ_zero]

theorem eq_one_of_comm_L {x : G} (hx : ∀ k ∈ C.L, x * k = k * x) : x = 1 :=
  C.eq_one_of_comm_L1 fun k hk => hx k (C.L1_le_L hk)

@[expose] def conjL {c : G} (hc : c ∈ Subgroup.normalizer (C.L : Set G)) : ↥C.L ≃* ↥C.L where
  toFun x := ⟨c * x * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc x).mp x.2⟩
  invFun x := ⟨c⁻¹ * x * c, by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hc) x).mp x.2
    rwa [inv_inv] at this⟩
  left_inv x := Subtype.ext (by simp only; group)
  right_inv x := Subtype.ext (by simp only; group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjL_apply {c : G} (hc : c ∈ Subgroup.normalizer (C.L : Set G)) (x : ↥C.L) :
    ((C.conjL hc x : ↥C.L) : G) = c * x * c⁻¹ := rfl

include C in
theorem exists_graph_field
    (hfact : FactAutL34GraphField) :
    ∃ c : G, c * c = 1 ∧ c ≠ 1 ∧
      (∃ E : Subgroup G, E ≤ Subgroup.centralizer ({c} : Set G) ∧
        Nonempty (↥E ≃* QuaternionGroup 2)) ∧
      ∃ F : Subgroup G, F ≤ Subgroup.centralizer ({c} : Set G) ∧ Nat.card F = 9 := by
  classical
  obtain ⟨c₀, hc₀N, hc₀NN, h1, h2⟩ := C.exists_c
  have hc₀L : c₀ ∈ Subgroup.normalizer (C.L : Set G) := C.mem_normalizer_of_swap h1 h2
  have hcc₀ : c₀ * c₀ ∈ C.L := by
    rcases C.normalizer_L_cases hc₀N hc₀NN hc₀L ((Subgroup.normalizer _).mul_mem hc₀L hc₀L) with
      h | h
    · exact h
    · rw [mul_inv_cancel_right] at h
      exact C.L.mul_mem h h
  set γ := C.conjL hc₀L with hγ
  set β₀ := C.Φ.symm.trans (γ.trans C.Φ) with hβ₀
  have hβ₀x : ∀ x, β₀ x = C.Φ (γ (C.Φ.symm x)) := fun _ => rfl
  have hswap : ∀ x : ↥(stabilizer M22 (0 : Fin 22)),
      ((x : M22) ∈ m22TwoStab ↔
          ((β₀ x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22PtHexStab) ∧
        ((x : M22) ∈ m22PtHexStab ↔
          ((β₀ x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab) := by
    intro x
    set y := C.Φ.symm x with hy
    have k1 : ((x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab ↔ (y : G) ∈ C.L1 := by
      rw [C.hΦ1 y, hy, C.Φ.apply_symm_apply]
    have k2 : ((x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22PtHexStab ↔ (y : G) ∈ C.L2 := by
      rw [C.hΦ2 y, hy, C.Φ.apply_symm_apply]
    have k3 : ((β₀ x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22PtHexStab ↔
        ((γ y : ↥C.L) : G) ∈ C.L2 := (C.hΦ2 (γ y)).symm
    have k4 : ((β₀ x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab ↔
        ((γ y : ↥C.L) : G) ∈ C.L1 := (C.hΦ1 (γ y)).symm
    exact ⟨k1.trans ((h1 y).trans k3.symm), k2.trans ((h2 y).trans k4.symm)⟩
  have hsq : ∃ ℓ : ↥(stabilizer M22 (0 : Fin 22)), ∀ x, β₀ (β₀ x) = ℓ * x * ℓ⁻¹ := by
    refine ⟨C.Φ ⟨c₀ * c₀, hcc₀⟩, fun x => ?_⟩
    have e : γ (γ (C.Φ.symm x)) = ⟨c₀ * c₀, hcc₀⟩ * C.Φ.symm x * (⟨c₀ * c₀, hcc₀⟩)⁻¹ :=
      Subtype.ext (by
        rw [C.conjL_apply, C.conjL_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        group)
    rw [hβ₀x, hβ₀x, C.Φ.symm_apply_apply, e, map_mul, map_mul, map_inv, C.Φ.apply_symm_apply]
  obtain ⟨m, hm1, hm2, hminv⟩ := (hfact β₀ hswap).1 hsq
  set μL := C.Φ.symm m with hμL
  have hμm : C.Φ μL = m := C.Φ.apply_symm_apply m
  have hμL1 : (μL : G) ∈ C.L1 := (C.hΦ1 μL).mpr (by rw [hμm]; exact hm1)
  have hμL2 : (μL : G) ∈ C.L2 := (C.hΦ2 μL).mpr (by rw [hμm]; exact hm2)
  obtain ⟨-, -, -, -, -, -, -, hRX, -⟩ :=
    C.M.parabolics_of_g C.h C.hsmemH C.hsnotK C.hss C.hg₀ C.hg C.hgNN
  have hμRX : (μL : G) ∈ C.M.RX := by
    rw [← hRX]
    exact ⟨hμL1, hμL2⟩
  have hμNN : (μL : G) ∈ C.M.NN := C.M.pre_mono inf_le_right hμRX
  set c := (μL : G) * c₀ with hc
  have hcN : c ∈ Subgroup.normalizer (C.M.V2 : Set G) :=
    (Subgroup.normalizer _).mul_mem (C.M.NN_le_normalizer hμNN) hc₀N
  have hcNN : c ∉ C.M.NN := fun h' => hc₀NN (by
    have := C.M.NN.mul_mem (C.M.NN.inv_mem hμNN) h'
    rwa [hc, ← mul_assoc, inv_mul_cancel, one_mul] at this)
  have hcL : c ∈ Subgroup.normalizer (C.L : Set G) :=
    (Subgroup.normalizer _).mul_mem (C.L_le_normalizer μL.2) hc₀L
  set γ' := C.conjL hcL with hγ'
  set β' := β₀.trans (MulAut.conj m) with hβ'
  have hβ'x : ∀ x, β' x = m * β₀ x * m⁻¹ := fun _ => rfl
  have hγ'Φ : ∀ w : ↥C.L, C.Φ (γ' w) = β' (C.Φ w) := by
    intro w
    have e : γ' w = μL * γ w * μL⁻¹ := Subtype.ext (by
      rw [C.conjL_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, C.conjL_apply,
        hc]
      group)
    rw [e, map_mul, map_mul, map_inv, hμm, hβ'x, hβ₀x, C.Φ.symm_apply_apply]
  have hcc : c * c = 1 := by
    refine C.eq_one_of_comm_L fun k hk => ?_
    have e : γ' (γ' ⟨k, hk⟩) = ⟨k, hk⟩ := by
      apply C.Φ.injective
      rw [hγ'Φ, hγ'Φ, hβ'x, hβ'x]
      exact hminv _
    have e' := congrArg Subtype.val e
    rw [C.conjL_apply, C.conjL_apply] at e'
    calc c * c * k = c * (c * k * c⁻¹) * c⁻¹ * (c * c) := by group
      _ = k * (c * c) := by rw [e']
  have hc1 : c ≠ 1 := fun h' => hcNN (h' ▸ C.M.NN.one_mem)
  have hfix : ∀ x : ↥(stabilizer M22 (0 : Fin 22)), β' x = x →
      ((C.Φ.symm x : ↥C.L) : G) ∈ Subgroup.centralizer ({c} : Set G) := by
    intro x hx
    have e : γ' (C.Φ.symm x) = C.Φ.symm x := by
      apply C.Φ.injective
      rw [hγ'Φ, C.Φ.apply_symm_apply, hx]
    have e' := congrArg Subtype.val e
    rw [C.conjL_apply] at e'
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc ((C.Φ.symm x : ↥C.L) : G) * c = c * (C.Φ.symm x : ↥C.L) * c⁻¹ * c := by rw [e']
      _ = c * (C.Φ.symm x : ↥C.L) := by group
  have hswap' : ∀ x : ↥(stabilizer M22 (0 : Fin 22)),
      ((x : M22) ∈ m22TwoStab ↔
          ((β' x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22PtHexStab) ∧
        ((x : M22) ∈ m22PtHexStab ↔
          ((β' x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab) := by
    intro x
    have e : ((β' x : ↥(stabilizer M22 (0 : Fin 22))) : M22) =
        (m : M22) * (β₀ x : M22) * (m : M22)⁻¹ := by
      rw [hβ'x, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e, Subgroup.mul_mem_cancel_right _ (m22PtHexStab.inv_mem hm2),
      Subgroup.mul_mem_cancel_left _ hm2, Subgroup.mul_mem_cancel_right _ (m22TwoStab.inv_mem hm1),
      Subgroup.mul_mem_cancel_left _ hm1]
    exact hswap x
  have hinv' : ∀ x, β' (β' x) = x := fun x => hminv x
  set ψ : ↥(stabilizer M22 (0 : Fin 22)) →* G := C.L.subtype.comp C.Φ.symm.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := C.L.subtype_injective.comp C.Φ.symm.injective
  rcases (hfact β' hswap').2 hinv' with ⟨⟨E, ⟨eE⟩, hE⟩, F, hF9, hF⟩ |
      ⟨y, hy1, hy2, hy3, hyfix⟩
  · refine ⟨c, hcc, hc1, ⟨E.map ψ, ?_, ⟨(Subgroup.equivMapOfInjective E ψ hψinj).symm.trans eE⟩⟩,
      F.map ψ, ?_, ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      exact hfix e (hE e he)
    · rintro _ ⟨f, hf, rfl⟩
      exact hfix f (hF f hf)
    · rw [Subgroup.card_map_of_injective hψinj, hF9]
  ·
    exfalso
    set yL := C.Φ.symm y with hyL
    have hyΦ : C.Φ yL = y := C.Φ.apply_symm_apply y
    have hyL1 : (yL : G) ∈ C.L1 := (C.hΦ1 yL).mpr (by rw [hyΦ]; exact hy1)
    have hyL2 : (yL : G) ∈ C.L2 := (C.hΦ2 yL).mpr (by rw [hyΦ]; exact hy2)
    have hyRX : (yL : G) ∈ C.M.RX := by
      rw [← hRX]
      exact ⟨hyL1, hyL2⟩
    have hyo : orderOf (yL : G) = 3 := by
      rw [Subgroup.orderOf_coe, hyL, MulEquiv.orderOf_eq, hy3]
    have hcy := Subgroup.mem_centralizer_singleton_iff.mp (hfix y hyfix)
    exact C.not_graph hcN hcNN hcc hyRX hyo hcy.symm

end HSCtx

end CFSG.Quasithin.HSType
