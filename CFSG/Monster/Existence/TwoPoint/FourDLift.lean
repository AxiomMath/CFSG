module

public import CFSG.Monster.Existence.TwoPoint.ShapeSixLift
public import CFSG.Monster.Existence.TwoPoint.EvenShapes
public import CFSG.Monster.Existence.TwoPoint.PartFour
public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphLocal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.GMS

theorem fd_xGriess_mem_cent : xGriess ∈ cent tGriess := by
  have h := Subgroup.mem_centralizer_iff.1 xGriess_mem_centralizer_FE tGriess
    (mem_FE.2 (Or.inr (Or.inl rfl)))
  exact Subgroup.mem_centralizer_singleton_iff.2 h.symm

@[expose] noncomputable def fdXCent : cent tGriess := ⟨xGriess, fd_xGriess_mem_cent⟩

@[expose] noncomputable def fdTCent : cent tGriess :=
  ⟨tGriess, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem fd_centToShat_tCent
    (hG : Gmat = AutO) : centToShat hG fdTCent = 1 :=
  (centToShat_eq_one_iff hG _).2 (Or.inr rfl)

theorem fd_centToShat_xCent
    (hG : Gmat = AutO) :
    ((centToShat hG fdXCent : Shat) : Dfull) = xhat := rfl

structure FourDGammaData
    (hG : Gmat = AutO) (w : CVert) (γ : MGriess) : Prop where
  mem_cent : γ ∈ cent tGriess
  pi_eq : ((centToShat hG ⟨γ, mem_cent⟩ : Shat) : Dfull) = clabel w
  isConj : IsConj tGriess γ
  isConj_t : IsConj tGriess (tGriess * γ)
  comm_u : uGriess * γ = γ * uGriess
  isConj_u : IsConj tGriess (uGriess * γ)
  not_isConj_ut : ¬ IsConj tGriess (uGriess * γ * tGriess)

theorem fd_isConj_conj {a : MGriess} (h : MGriess) (ha : IsConj tGriess a) :
    IsConj tGriess (h⁻¹ * a * h) :=
  ha.trans (isConj_iff.2 ⟨h⁻¹, by rw [inv_inv]⟩)

theorem fd_isConj_xGriess_conj (h : MGriess) : IsConj xGriess (h⁻¹ * xGriess * h) :=
  isConj_iff.2 ⟨h⁻¹, by rw [inv_inv]⟩

theorem fd_isConj_tGriess_mul_xGriess :
    IsConj tGriess (xGriess * tGriess) := by
  have h : xGriess * tGriess = tGriess * xGriess :=
    Subgroup.mem_centralizer_singleton_iff.1 fd_xGriess_mem_cent
  rw [h]
  exact tGriess_mul_xGriess_mem_twoBNbr.1

theorem fd_isConj_tGriess_mul_uGriess :
    IsConj tGriess (uGriess * tGriess) := by
  rw [← tGriess_mul_uGriess]
  exact uGriess_mem_twoANbr.2

theorem exists_fourD_gammaData
    (hG : Gmat = AutO) {w : CVert} (hw : cgraph.Adj cv0 w) :
    ∃ γ : MGriess, FourDGammaData hG w γ := by
  obtain ⟨-, -, -, -, s, hs⟩ := clabel_adj hw
  obtain ⟨g, rfl⟩ := cvOf_surjective w
  obtain ⟨ĝ, hĝ⟩ := centToShat_surjective hG g
  obtain ⟨ŝ, hŝ⟩ := centToShat_surjective hG s
  have htt : fdTCent * fdTCent = 1 := Subtype.ext tGriess_mul_self
  have hĝt : (ĝ : MGriess) * tGriess = tGriess * ĝ :=
    Subgroup.mem_centralizer_singleton_iff.1 ĝ.2
  have hŝt : (ŝ : MGriess) * tGriess = tGriess * ŝ :=
    Subgroup.mem_centralizer_singleton_iff.1 ŝ.2
  have hxt : xGriess * tGriess = tGriess * xGriess :=
    Subgroup.mem_centralizer_singleton_iff.1 fd_xGriess_mem_cent
  have hxx : xGriess * xGriess = 1 := mul_self_of_isConj orderOf_xGriess (IsConj.refl _)
  have htu : tGriess * uGriess = uGriess * tGriess := tGriess_mul_uGriess
  set c : cent tGriess := ĝ⁻¹ * uGriessCent * ĝ with hc
  set y : cent tGriess := ŝ⁻¹ * fdXCent * ŝ with hy
  have hπc : ((centToShat hG c : Shat) : Dfull) = (g : Dfull)⁻¹ * cQ * g := by
    rw [hc, map_mul, map_mul, map_inv, hĝ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, centToShat_uGriessCent]
  have hπy : ((centToShat hG y : Shat) : Dfull) = (s : Dfull)⁻¹ * xhat * s := by
    rw [hy, map_mul, map_mul, map_inv, hŝ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, fd_centToShat_xCent]
  have hν : centToShat hG (uGriessCent * c) = centToShat hG y := by
    apply Subtype.ext
    rw [map_mul (centToShat hG) uGriessCent c, Subgroup.coe_mul, hπc, centToShat_uGriessCent, hπy,
      ← hs, clabel_cv0, clabel_cvOf]
  have hker : (uGriessCent * c)⁻¹ * y = 1 ∨ (uGriessCent * c)⁻¹ * y = fdTCent := by
    have h1 : centToShat hG ((uGriessCent * c)⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hν, inv_mul_cancel]
    rcases (centToShat_eq_one_iff hG _).1 h1 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  obtain ⟨γ', hγ'c, huγ'⟩ : ∃ γ' : cent tGriess, (γ' = c ∨ γ' = c * fdTCent) ∧
      uGriessCent * γ' = y * fdTCent := by
    rcases hker with h | h
    · refine ⟨c * fdTCent, Or.inr rfl, ?_⟩
      rw [← mul_assoc, inv_mul_eq_one.1 h]
    · refine ⟨c, Or.inl rfl, ?_⟩
      have h' := inv_mul_eq_iff_eq_mul.1 h
      calc uGriessCent * c = (uGriessCent * c * fdTCent) * fdTCent := by
            rw [mul_assoc _ fdTCent, htt, mul_one]
        _ = y * fdTCent := by rw [← h']
  have hγ'form : ∃ a : MGriess, (a = uGriess ∨ a = uGriess * tGriess) ∧
      (γ' : MGriess) = (ĝ : MGriess)⁻¹ * a * ĝ := by
    rcases hγ'c with rfl | rfl
    · exact ⟨uGriess, Or.inl rfl, rfl⟩
    · refine ⟨uGriess * tGriess, Or.inr rfl, ?_⟩
      show (ĝ : MGriess)⁻¹ * uGriess * ĝ * tGriess = (ĝ : MGriess)⁻¹ * (uGriess * tGriess) * ĝ
      calc (ĝ : MGriess)⁻¹ * uGriess * ĝ * tGriess
          = (ĝ : MGriess)⁻¹ * uGriess * ((ĝ : MGriess) * tGriess) := by group
        _ = (ĝ : MGriess)⁻¹ * uGriess * (tGriess * ĝ) := by rw [hĝt]
        _ = (ĝ : MGriess)⁻¹ * (uGriess * tGriess) * ĝ := by group
  obtain ⟨a, ha, haγ⟩ := hγ'form
  have haA : IsConj tGriess a ∧ IsConj tGriess (tGriess * a) := by
    rcases ha with rfl | rfl
    · exact ⟨uGriess_mem_twoANbr.1, uGriess_mem_twoANbr.2⟩
    · refine ⟨fd_isConj_tGriess_mul_uGriess, ?_⟩
      rw [← mul_assoc, tGriess_mul_uGriess, mul_assoc, tGriess_mul_self, mul_one]
      exact uGriess_mem_twoANbr.1
  have hγA : IsConj tGriess (γ' : MGriess) := by rw [haγ]; exact fd_isConj_conj _ haA.1
  have hγtA : IsConj tGriess (tGriess * (γ' : MGriess)) := by
    have e : tGriess * ((ĝ : MGriess)⁻¹ * a * ĝ) = (ĝ : MGriess)⁻¹ * (tGriess * a) * ĝ :=
      calc tGriess * ((ĝ : MGriess)⁻¹ * a * ĝ) = (tGriess * (ĝ : MGriess)⁻¹) * a * ĝ := by group
        _ = ((ĝ : MGriess)⁻¹ * tGriess) * a * ĝ := by
            rw [show tGriess * (ĝ : MGriess)⁻¹ = (ĝ : MGriess)⁻¹ * tGriess by
              rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hĝt]; group]
        _ = (ĝ : MGriess)⁻¹ * (tGriess * a) * ĝ := by group
    rw [haγ, e]
    exact fd_isConj_conj _ haA.2
  have huy : uGriess * (γ' : MGriess) = (ŝ : MGriess)⁻¹ * xGriess * ŝ * tGriess :=
    congrArg Subtype.val huγ'
  have hux : uGriess * (γ' : MGriess) = (ŝ : MGriess)⁻¹ * (xGriess * tGriess) * ŝ := by
    rw [huy]
    calc (ŝ : MGriess)⁻¹ * xGriess * ŝ * tGriess
        = (ŝ : MGriess)⁻¹ * xGriess * ((ŝ : MGriess) * tGriess) := by group
      _ = (ŝ : MGriess)⁻¹ * xGriess * (tGriess * ŝ) := by rw [hŝt]
      _ = (ŝ : MGriess)⁻¹ * (xGriess * tGriess) * ŝ := by group
  have hγγ : (γ' : MGriess) * γ' = 1 := mul_self_of_isConj orderOf_tGriess hγA
  have huu : uGriess * uGriess = 1 := uGriess_mul_self
  have huγu : (uGriess * (γ' : MGriess)) * (uGriess * γ') = 1 := by
    rw [hux]
    calc (ŝ : MGriess)⁻¹ * (xGriess * tGriess) * ŝ * ((ŝ : MGriess)⁻¹ * (xGriess * tGriess) * ŝ)
        = (ŝ : MGriess)⁻¹ * ((xGriess * tGriess) * (xGriess * tGriess)) * ŝ := by group
      _ = 1 := by
        rw [show (xGriess * tGriess) * (xGriess * tGriess) = 1 by
          calc (xGriess * tGriess) * (xGriess * tGriess)
              = xGriess * (tGriess * xGriess) * tGriess := by group
            _ = xGriess * (xGriess * tGriess) * tGriess := by rw [hxt]
            _ = 1 := by rw [← mul_assoc, hxx, one_mul, tGriess_mul_self]]
        group
  refine ⟨(γ' : MGriess), ⟨γ'.2, ?_, hγA, hγtA, ?_, ?_, ?_⟩⟩
  ·
    have : ((centToShat hG γ' : Shat) : Dfull) = (g : Dfull)⁻¹ * cQ * g := by
      rcases hγ'c with rfl | rfl
      · exact hπc
      · rw [map_mul, fd_centToShat_tCent, mul_one]
        exact hπc
    rw [clabel_cvOf]
    exact this
  ·
    have h1 : (uGriess * (γ' : MGriess))⁻¹ = uGriess * γ' := inv_eq_of_mul_eq_one_right huγu
    calc uGriess * (γ' : MGriess) = (uGriess * (γ' : MGriess))⁻¹ := h1.symm
      _ = (γ' : MGriess) * uGriess := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hγγ, inv_eq_of_mul_eq_one_right huu]
  · rw [hux]
    exact fd_isConj_conj _ fd_isConj_tGriess_mul_xGriess
  · rw [huy, mul_assoc, tGriess_mul_self, mul_one]
    intro h
    exact not_isConj_xGriess_tGriess ((fd_isConj_xGriess_conj (ŝ : MGriess)).trans h.symm)

theorem isLongTriangle_of_fourD_gammaData
    (hG : Gmat = AutO) {w : CVert} {γ : MGriess}
    (hw : cgraph.Adj cv0 w) (hγ : FourDGammaData hG w γ) :
    IsLongTriangle tGriess {tGriess, uGriess, γ} := by
  obtain ⟨hne, -⟩ := clabel_adj hw
  have hγu : γ ≠ uGriess := by
    rintro rfl
    apply hne
    rw [clabel_cv0, ← hγ.pi_eq]
    exact (centToShat_uGriessCent hG).symm
  have hγtu : γ ≠ tGriess * uGriess := by
    rintro rfl
    apply hne
    rw [clabel_cv0, ← hγ.pi_eq]
    have e : (⟨tGriess * uGriess, hγ.mem_cent⟩ : cent tGriess) = fdTCent * uGriessCent := rfl
    rw [e, map_mul, fd_centToShat_tCent, one_mul]
    exact (centToShat_uGriessCent hG).symm
  have hγt : γ ≠ tGriess := by
    rintro rfl
    apply hγ.not_isConj_ut
    rw [mul_assoc, tGriess_mul_self, mul_one]
    exact uGriess_mem_twoANbr.1
  refine ⟨isTriangle_insert orderOf_tGriess (IsConj.refl _) uGriess_mem_twoANbr.1 hγ.isConj
    uGriess_ne_tGriess.symm hγt hγu uGriess_mem_twoANbr.2 hγ.isConj_t hγ.isConj_u,
    fun hS => hγtu ?_⟩
  have hab := hS.2 tGriess (by simp) uGriess (by simp) uGriess_ne_tGriess.symm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hab
  rcases hab with h | h | h
  · exact absurd (mul_left_cancel (h.trans (mul_one tGriess).symm)) uGriess_ne_one
  · exact absurd (mul_right_cancel (h.trans (one_mul uGriess).symm)) tGriess_ne_one
  · exact h.symm

end CFSG.Monster.Existence
