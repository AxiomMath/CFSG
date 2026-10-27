module

public import CFSG.Quasithin.Vol2.Ch10SecFH
public import CFSG.Quasithin.Vol2.Ch10SecFS4

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {hyp : Hyp10 G T L I} {t : G}
  (D : SecE.Case2Data hyp t)

theorem not_mem_centralizer_VZ
    (h311 : Theorem311Stmt) (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hshape : Stmt7_0_1_shape)
    (h113 : ASInputs.AS_C_1_13) (h322 : Ch10.TmpL6_3_2_2_two) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (h2 : Ch10.Case10_1_1Two T L I) (hb : IsShort2 L ∧ IsAltType L 5)
    (hCZ : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) ≠ ⊥)
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hHS : H ≤ Subgroup.normalizer (baum T : Set G))
    {ρ : Subgroup.normalizer (fsuVM T L I : Set G)} (hρL : (ρ : G) ∈ T ⊓ L)
    (hρ : convI (SecA.isElemAbelian_fsuVM hyp) ρ = (D.θ₁.symm SecE.rA).1) :
    (ρ : G) ∉ Subgroup.centralizer (VZ T H : Set G) := by
  intro hρC
  have hVH := VZ_le_omegaOneCenterOf_baum hHS
  have hTH : T ≤ H := hH.1.1
  have hTVH : T ≤ Subgroup.normalizer (VZ T H : Set G) :=
    hTH.trans (le_normalizer_conjClosure _ H)
  have h1 : T ⊓ L ≤ Subgroup.centralizer (VZ T H : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : (ρ : G) * z * (ρ : G)⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hρC z hz]
      group
    have hxz : x * z * x⁻¹ = z := by
      rcases conj_of_mem_inf_L_of_mem_E D h113 h37 h38 h322 h3228 h2 hb ht htn hρL hρ hx
        (hVH hz) with h | h
      · exact h
      · exact h.trans hz'
    calc z * x = (x * z * x⁻¹) * x := by rw [hxz]
      _ = x * z := by group
  have hCN : T ≤ Subgroup.normalizer (Subgroup.centralizer (VZ T H : Set G) : Set G) :=
    SecA.le_normalizer_centralizer hTVH
  have h2' : T ⊓ CFSG.conjugate L t ≤ Subgroup.centralizer (VZ T H : Set G) := by
    intro y hy
    have hty : t * y * t⁻¹ ∈ T ⊓ L :=
      ⟨T.mul_mem (T.mul_mem ht hy.1) (T.inv_mem ht), mem_conjugate_iff'.mp hy.2⟩
    have h3 := (Subgroup.mem_normalizer_iff.mp (hCN (T.inv_mem ht)) _).mp (h1 hty)
    simpa [mul_assoc] using h3
  have h3 : pCoreOf 2 (fsuL0 T L) ≤ Subgroup.centralizer (VZ T H : Set G) := by
    intro o ho
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hoz := conj_of_mem_pCoreOf_fsuL0_of_mem_E D h113 h37 h38 h322 h3228 h2 hb ht htn ho
      (hVH hz)
    calc z * o = (o * z * o⁻¹) * o := by rw [hoz]
      _ = o * z := by group
  have hT0 : Ch10.T0 T L ≤ T ⊓ Subgroup.centralizer (VZ T H : Set G) :=
    le_inf inf_le_left ((SecA.T0_le_sup h37 h38 hyp ht htn).trans (sup_le (sup_le h1 h2') h3))
  have hTR : T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (VZ T H : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_of_le Subgroup.le_normalizer hCN
  have hNR := SecE.normalizer_le_fsuM_of_T0_le h311 h331 h37 h38 hshape hyp (Or.inr h2) hT0
    inf_le_left hTR
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTH
  have hHC : H ≤ Subgroup.normalizer
      ((H ⊓ Subgroup.centralizer (VZ T H : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_of_le Subgroup.le_normalizer
      (SecA.le_normalizer_centralizer (le_normalizer_conjClosure _ H))
  have hRsyl := B6.isSylowTwoOf_inf_normal hTsyl inf_le_left hHC
  have hTC : T ⊓ (H ⊓ Subgroup.centralizer (VZ T H : Set G)) =
      T ⊓ Subgroup.centralizer (VZ T H : Set G) := by
    rw [← inf_assoc, inf_eq_left.mpr hTH]
  have hfr := B6.frattini_two inf_le_left hHC hRsyl
  rw [hTC] at hfr
  apply hH.2.1
  refine hfr.trans (sup_le ?_ ?_)
  · exact inf_le_right.trans (centralizer_VZ_le h331 hyp hCZ H)
  · exact inf_le_right.trans hNR

theorem vOne_mem_VZ
    (h311 : Theorem311Stmt) (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hshape : Stmt7_0_1_shape)
    (h113 : ASInputs.AS_C_1_13) (h322 : Ch10.TmpL6_3_2_2_two) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (h2 : Ch10.Case10_1_1Two T L I) (hb : IsShort2 L ∧ IsAltType L 5)
    (hCZ : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) ≠ ⊥)
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hHS : H ≤ Subgroup.normalizer (baum T : Set G))
    {ρ : Subgroup.normalizer (fsuVM T L I : Set G)} (hρL : (ρ : G) ∈ T ⊓ L)
    (hρ : convI (SecA.isElemAbelian_fsuVM hyp) ρ = (D.θ₁.symm SecE.rA).1) :
    vOne D ∈ VZ T H ∧
      ∀ x ∈ VZ T H, (ρ : G) * x * (ρ : G)⁻¹ = x ∨ (ρ : G) * x * (ρ : G)⁻¹ = x * vOne D := by
  have hVH := VZ_le_omegaOneCenterOf_baum hHS
  have hact : ∀ x ∈ VZ T H, (ρ : G) * x * (ρ : G)⁻¹ = x ∨
      (ρ : G) * x * (ρ : G)⁻¹ = x * vOne D := fun x hx =>
    conj_rho_of_mem_E D h113 h37 h38 h3228 h2 hb ht htn hρL hρ (hVH hx)
  refine ⟨?_, hact⟩
  by_contra hv
  apply not_mem_centralizer_VZ D h311 h331 h37 h38 hshape h113 h322 h3228 h2 hb hCZ ht htn hH
    hHS hρL hρ
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rcases hact z hz with h | h
  · calc z * (ρ : G) = ((ρ : G) * z * (ρ : G)⁻¹) * (ρ : G) := by rw [h]
      _ = (ρ : G) * z := by group
  · exfalso
    have hmem : (ρ : G) * z * (ρ : G)⁻¹ ∈ VZ T H :=
      (Subgroup.mem_normalizer_iff.mp
        ((hH.1.1.trans (le_normalizer_conjClosure _ H)) hρL.1) z).mp hz
    rw [h] at hmem
    apply hv
    have := (VZ T H).mul_mem ((VZ T H).inv_mem hz) hmem
    simpa using this

end CFSG.Quasithin.Vol2.Ch10.SecF
