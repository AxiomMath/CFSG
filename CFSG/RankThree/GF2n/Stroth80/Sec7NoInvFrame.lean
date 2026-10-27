module

public import CFSG.RankThree.GF2n.Stroth80.Sec7NoInvGom
public import CFSG.ClassicalGroups.Orthogonal.Transitive
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Open QuadraticMap
open scoped Matrix MatrixGroups

variable {K : Type} [Field K]

theorem polar_quadPlus_three (x y : Fin 3 ⊕ Fin 3 → K) :
    polar (quadPlus 3 K) x y =
      x (Sum.inl 0) * y (Sum.inr 0) + x (Sum.inr 0) * y (Sum.inl 0) +
      (x (Sum.inl 1) * y (Sum.inr 1) + x (Sum.inr 1) * y (Sum.inl 1)) +
      (x (Sum.inl 2) * y (Sum.inr 2) + x (Sum.inr 2) * y (Sum.inl 2)) := by
  rw [show ⇑(quadPlus 3 K) = StatedQuadPlus 3 K from coe_quadPlus 3 K]
  simp [QuadraticMap.polar, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_three]
  ring

theorem quadPlus_three (x : Fin 3 ⊕ Fin 3 → K) :
    quadPlus 3 K x = x (Sum.inl 0) * x (Sum.inr 0) + x (Sum.inl 1) * x (Sum.inr 1) +
      x (Sum.inl 2) * x (Sum.inr 2) := by
  rw [show ⇑(quadPlus 3 K) = StatedQuadPlus 3 K from coe_quadPlus 3 K]
  simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_three]

theorem exists_orth_hypPairs :
    ∃ P P' : HypPair (quadPlus 3 K), P.Orth P' ∧
      P.e = (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K) ∧
      P.f = (Pi.single (Sum.inr 0) 1 : Fin 3 ⊕ Fin 3 → K) := by
  refine ⟨⟨Pi.single (Sum.inl 0) 1, Pi.single (Sum.inr 0) 1, ?_, ?_, ?_⟩,
    ⟨Pi.single (Sum.inl 1) 1, Pi.single (Sum.inr 1) 1, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, rfl, rfl⟩ <;>
  simp [polar_quadPlus_three, quadPlus_three, Pi.single_apply]


theorem exists_gom_frame [Finite K] [CharP K 2] {u u' : Fin 3 ⊕ Fin 3 → K}
    (hu : quadPlus 3 K u = 0) (hu' : quadPlus 3 K u' = 0) (hu0 : u ≠ 0)
    (huu' : polar (quadPlus 3 K) u u' ≠ 0) :
    ∃ g : Gom (quadPlus 3 K), g.app (Pi.single (Sum.inl 0) 1) = u ∧
      g.app (Pi.single (Sum.inr 0) 1) = (polar (quadPlus 3 K) u u')⁻¹ • u' := by
  classical
  obtain ⟨P, P', hPP', hPe, hPf⟩ := exists_orth_hypPairs (K := K)
  have hQ : (polarBilin (quadPlus 3 K)).Nondegenerate := nondegenerate_polarBilin_quadPlus 3 K
  have he₀ : quadPlus 3 K (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K) = 0 := by
    rw [← hPe]
    exact P.Q_e
  have he₀' : quadPlus 3 K (Pi.single (Sum.inr 0) 1 : Fin 3 ⊕ Fin 3 → K) = 0 := by
    rw [← hPf]
    exact P.Q_f
  have hee' : polar (quadPlus 3 K) (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K)
      (Pi.single (Sum.inr 0) 1) = 1 := by
    rw [← hPe, ← hPf]
    exact P.polar_ef
  have he0 : (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl 0)
    simp at this
  obtain ⟨g₁, hg₁, hg₁u⟩ := exists_mem_elementaryGroup_apply_eq hQ hPP' he0 hu0
    (by rw [he₀, hu])
  set G₁ : Gom (quadPlus 3 K) := ⟨g₁, hg₁⟩ with hG₁
  have hG₁e : G₁.app (Pi.single (Sum.inl 0) 1) = u := hg₁u
  set p := polar (quadPlus 3 K) u u' with hp
  set u'' : Fin 3 ⊕ Fin 3 → K := p⁻¹ • u' with hu''
  have hQu'' : quadPlus 3 K u'' = 0 := by
    rw [hu'', map_smul_eq_sq, hu', mul_zero]
  have hpol : polar (quadPlus 3 K) u u'' = 1 := by
    rw [hu'', polar_smul_right_eq, inv_mul_cancel₀ huu']
  set v' : Fin 3 ⊕ Fin 3 → K := G₁⁻¹.app u'' with hv'
  have hQv' : quadPlus 3 K v' = 0 := by
    rw [hv', Gom.map_of_mem, hQu'']
  have h1 : G₁⁻¹.app u = Pi.single (Sum.inl 0) 1 := by
    rw [← hG₁e, Gom.app_inv_app]
  have hev' : polar (quadPlus 3 K) (Pi.single (Sum.inl 0) 1) v' = 1 := by
    have := Gom.polar_app G₁⁻¹ u u''
    rw [h1] at this
    rw [hv', this, hpol]
  set w : Fin 3 ⊕ Fin 3 → K := v' + Pi.single (Sum.inr 0) 1 with hw
  have hw0 : polar (quadPlus 3 K) (Pi.single (Sum.inl 0) 1) w = 0 := by
    rw [hw, polar_add_right, hev', hee']
    exact CharTwo.add_self_eq_zero _
  have hee : polar (quadPlus 3 K) (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K)
      (Pi.single (Sum.inl 0) 1) = 0 := polar_self_eq_zero he₀
  have hee'' : polar (quadPlus 3 K) (Pi.single (Sum.inr 0) 1 : Fin 3 ⊕ Fin 3 → K)
      (Pi.single (Sum.inl 0) 1) = 1 := by
    rw [polar_comm]
    exact hee'
  have hff : polar (quadPlus 3 K) (Pi.single (Sum.inr 0) 1 : Fin 3 ⊕ Fin 3 → K)
      (Pi.single (Sum.inr 0) 1) = 0 := polar_self_eq_zero he₀'
  set G₂ : Gom (quadPlus 3 K) := eichlerG (quadPlus 3 K) (Pi.single (Sum.inl 0) 1) w with hG₂
  have hG₂e : G₂.app (Pi.single (Sum.inl 0) 1) = Pi.single (Sum.inl 0) 1 := by
    rw [hG₂, eichlerG_app he₀ hw0, hee, hw0]
    simp
  have hG₂e' : G₂.app (Pi.single (Sum.inr 0) 1) = v' := by
    rw [hG₂, eichlerG_app he₀ hw0, hee'']
    have hc : polar (quadPlus 3 K) (Pi.single (Sum.inr 0) 1) w +
        quadPlus 3 K w * 1 = 0 := by
      have e1 : polar (quadPlus 3 K) (Pi.single (Sum.inr 0) 1) w =
          polar (quadPlus 3 K) (Pi.single (Sum.inr 0) 1) v' := by
        rw [hw, polar_add_right, hff, add_zero]
      have e2 : quadPlus 3 K w = polar (quadPlus 3 K) v' (Pi.single (Sum.inr 0) 1) := by
        rw [hw, QuadraticMap.map_add (quadPlus 3 K), hQv', he₀', zero_add, zero_add]
      rw [mul_one, e1, e2, polar_comm]
      exact CharTwo.add_self_eq_zero _
    rw [one_smul, hc, zero_smul, sub_zero, hw]
    have h11 : (Pi.single (Sum.inr 0) 1 : Fin 3 ⊕ Fin 3 → K) + Pi.single (Sum.inr 0) 1 = 0 := by
      rw [← Pi.single_add, CharTwo.add_self_eq_zero, Pi.single_zero]
    calc (Pi.single (Sum.inr 0) 1 : Fin 3 ⊕ Fin 3 → K) + (v' + Pi.single (Sum.inr 0) 1) =
        v' + (Pi.single (Sum.inr 0) 1 + Pi.single (Sum.inr 0) 1) := by abel
      _ = v' := by rw [h11, add_zero]
  refine ⟨G₁ * G₂, ?_, ?_⟩
  · rw [Gom.app_mul, hG₂e, hG₁e]
  · rw [Gom.app_mul, hG₂e', hv', Gom.app_app_inv]


@[expose, instance_reducible] noncomputable def twistAction {Γ : Type*} [Group Γ] {Y : Type*}
    [AddCommGroup Y] [DistribMulAction Γ Y] (g : Γ) : DistribMulAction Γ Y :=
  DistribMulAction.compHom Y (MulAut.conj g).toMonoidHom

theorem noInvariantForm_frame [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {u u' : Fin 3 ⊕ Fin 3 → K} (hu : quadPlus 3 K u = 0) (hu' : quadPlus 3 K u' = 0)
    (hu0 : u ≠ 0) (huu' : polar (quadPlus 3 K) u u' ≠ 0) (Y : Type) [AddCommGroup Y] [Finite Y]
    [DistribMulAction (Gom (quadPlus 3 K)) Y] (h2 : ∀ a : Y, a + a = 0)
    (hdec : IsCompl (fixedSub Y (Lom (quadPlus 3 K) u : Set (Gom (quadPlus 3 K))))
      (fixedSub Y (Lom (quadPlus 3 K) u' : Set (Gom (quadPlus 3 K)))))
    (hcard : Nat.card Y = Nat.card K ^ 4) (β : Y →+ Y →+ ZMod 2)
    (hinv : ∀ (g : Gom (quadPlus 3 K)) a b, β (g • a) (g • b) = β a b)
    (hnd : ∀ a : Y, (∀ b : Y, β a b = 0) → a = 0) : False := by
  classical
  obtain ⟨g, hgu, hgu'⟩ := exists_gom_frame hu hu' hu0 huu'
  have hc : (polar (quadPlus 3 K) u u')⁻¹ ≠ 0 := inv_ne_zero huu'
  refine @noInvariantForm_gom K _ _ _ hK Y _ _ (twistAction g) h2 ?_ hcard β ?_ hnd
  · unfold twistAction
    rw [fixedSub_compHom, fixedSub_compHom]
    have e1 : ((MulAut.conj g).toMonoidHom '' (Lom (quadPlus 3 K) (Pi.single (Sum.inl 0) 1) :
        Set (Gom (quadPlus 3 K)))) = (Lom (quadPlus 3 K) u : Set (Gom (quadPlus 3 K))) := by
      rw [← hgu]
      exact image_conj_Lom g _
    have e2 : ((MulAut.conj g).toMonoidHom '' (Lom (quadPlus 3 K) (Pi.single (Sum.inr 0) 1) :
        Set (Gom (quadPlus 3 K)))) = (Lom (quadPlus 3 K) u' : Set (Gom (quadPlus 3 K))) := by
      have := image_conj_Lom g (Pi.single (Sum.inr 0) 1)
      rw [hgu', Lom_smul hc] at this
      exact this
    rw [e1, e2]
    exact hdec
  · intro h a b
    exact hinv (g * h * g⁻¹) a b

end CFSG.RankThree.GF2n.Stroth80
