module

public import CFSG.Quasithin.Background.G11Six
public import CFSG.Quasithin.Background.G116IIIConfig
public import CFSG.Quasithin.Background.G116IIIFStar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

theorem g116_III : G116IIIStmt := by
  intro V _ _ _ B Γ v₁ W X X₀ L h108 _hSQ I hI _hone htwo _hthree
  obtain ⟨-, -, -, -, hd8, x, hx, hxI, hH, hX8, hXH, hIL, hA5, hfix⟩ := htwo
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr h108.fixedSpace_H
  have hxΓ : x ∈ Γ := h108.X_le hx
  have hx2 : x * x = 1 := h108.X_sq x hx
  have hLΓ : L ≤ Γ := h108.L_le
  have hLH : L ≤ normalClosure Γ L := le_normalClosure Γ L
  have hLxH : L.map (MulAut.conj x).toMonoidHom ≤ normalClosure Γ L := by
    rw [hH]
    exact le_sup_right
  have hdim4 : Module.finrank (ZMod 2) I = 4 := hA5.finrank_eq
  have hcompl : IsCompl I (conjSub x I) :=
    isCompl_conjSub_of_irr (normalClosure_normal Γ L) hirr hxΓ hxI (by omega)
  have hinvL : Invariant L I := hirr.1.mono hLH
  have hLxI : ∀ b ∈ L.map (MulAut.conj x).toMonoidHom, ∀ v ∈ I, b v = v :=
    conj_map_trivial_on hx2 hfix
  have hLJ : ∀ a ∈ L, ∀ v ∈ conjSub x I, a v = v := fun a ha v hv => by
    rw [hfix] at hv
    exact hv a ha
  have hinvJ : Invariant (normalClosure Γ L) (conjSub x I) :=
    hirr.1.conj_of_normal (normalClosure_normal Γ L) hxΓ
  have hinf : L ⊓ L.map (MulAut.conj x).toMonoidHom = ⊥ :=
    inf_map_conj_eq_bot_of_isCompl hcompl hLJ hLxI
  have hcomm : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj x).toMonoidHom, a * b = b * a :=
    fun a ha b hb => mul_comm_of_isCompl_fixes hcompl (hirr.1 a (hLH ha)) (hinvJ b (hLxH hb))
      (hLJ a ha) (hLxI b hb)
  have hF : (genFittingFStar ↥Γ).map Γ.subtype = L ⊔ L.map (MulAut.conj x).toMonoidHom :=
    fstar_map_eq_of_components hxΓ h108.component fun c _ hcL hcLx =>
      eq_one_of_commute_L_Lx hA5 hIL hinvL hcompl hcL hcLx
  have e : commSpanOf L = I := by rw [commSpanOf_eq_commSpace_top, ← hIL]
  refine ⟨hd8, x, L, hx, hLΓ, hF, hinf, hcomm, ?_, ?_, hX8, ?_⟩
  · rw [e, commSpanOf_eq_commSpace_top, commSpace_map_conj_top, ← hIL]
    exact hcompl
  · rw [e]
    exact hA5
  · rw [hH] at hXH
    exact hXH.trans (sup_comm _ _)

end G11

end CFSG.Quasithin
