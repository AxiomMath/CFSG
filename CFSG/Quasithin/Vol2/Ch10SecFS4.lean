module

public import CFSG.Quasithin.Vol2.Ch10SecFS3
public import CFSG.Quasithin.Vol2.Ch10SecEBlockA5
public import CFSG.Quasithin.Vol2.Ch10SecFComm
public import CFSG.Quasithin.Vol2.Ch10SecFS1
public import CFSG.Quasithin.Vol2.Ch10SecFS2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {hyp : Hyp10 G T L I} {t : G}
  (D : SecE.Case2Data hyp t)

@[expose] noncomputable def vOne : G := IntMod.val (vOneW D).1

theorem vOne_ne_one : vOne D ≠ 1 := by
  intro h
  apply vOneW_ne_one D
  apply Subtype.ext
  exact IntMod.val_injective (h.trans IntMod.val_one.symm)

theorem val_mem_fsuUL_of_mem_commV (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h2 : Ch10.Case10_1_1Two T L I) (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {w : IntMod (fsuVM T L I)
      (SecA.isElemAbelian_fsuVM hyp)} (hw : w ∈ commV D.K₁) : w.val ∈ fsuUL T L I := by
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hwC : w.val ∈ Subgroup.centralizer (CFSG.conjugate L t : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlN : l ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
      SecA.fsuL0_le_normalizer_fsuVM T L I (SecA.conjugate_le_fsuL0 ht hl)
    have hK : convI hV ⟨l, hlN⟩ ∈ D.K₂ := by
      have := convI_mem_autI hV hl hlN
      rw [← D.oTwo₂] at this
      exact oTwoUpper_le _ this
    have h1 := (SecE.convI_fix_iff hV ⟨l, hlN⟩ w).mp (D.triv₂ hK hw)
    calc l * w.val = (l * w.val * l⁻¹) * l := by group
      _ = w.val * l := by rw [h1]
  obtain ⟨a, ha, b, hb, hab⟩ := SecA.exists_mul_of_mem_fsuVM h37 h38 hyp ht htn w.val_mem
  obtain ⟨_, -, -, hA, -⟩ := hyp.three
  have haC : a ∈ Subgroup.centralizer (CFSG.conjugate L t : Set G) := (hA t ht htn).2.2 ha
  have hbC : b ∈ Subgroup.centralizer (CFSG.conjugate L t : Set G) := by
    have : b = a⁻¹ * w.val := by rw [← hab]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haC) hwC
  have hb1 : b = 1 := by
    have htb : t * b * t⁻¹ ∈ fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨mem_conjugate_iff'.mp hb, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      have hl' : t⁻¹ * l * t ∈ CFSG.conjugate L t := by
        rw [mem_conjugate_iff']
        simpa [mul_assoc] using hl
      have hc := Subgroup.mem_centralizer_iff.mp hbC _ hl'
      calc l * (t * b * t⁻¹) = t * ((t⁻¹ * l * t) * b) * t⁻¹ := by group
        _ = t * (b * (t⁻¹ * l * t)) * t⁻¹ := by rw [hc]
        _ = t * b * t⁻¹ * l := by group
    rw [fsuUL_inf_centralizer_eq_bot h2, Subgroup.mem_bot] at htb
    calc b = t⁻¹ * (t * b * t⁻¹) * t := by group
      _ = 1 := by rw [htb]; group
  rw [← hab, hb1, mul_one]
  exact ha

theorem vOne_mem_fsuUL (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h2 : Ch10.Case10_1_1Two T L I) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    vOne D ∈ fsuUL T L I :=
  val_mem_fsuUL_of_mem_commV D h37 h38 h2 ht htn (vOneW D).2

include D in
theorem mem_fixV_of_mem_centralizer_baum {v : G} (hv : v ∈ fsuVM T L I)
    (hvS : v ∈ Subgroup.centralizer (baum T : Set G)) :
    IntMod.mk (SecA.isElemAbelian_fsuVM hyp) ⟨v, hv⟩ ∈
      fixV (autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T)) := by
  intro p hp
  rw [← D.baum_eq] at hp
  obtain ⟨s, hs, rfl⟩ := (mem_autI _).mp hp
  apply IntMod.val_injective
  rw [convI_apply_val]
  show (s : G) * v * (s : G)⁻¹ = v
  rw [Subgroup.mem_centralizer_iff.mp hvS s hs]
  group

theorem exists_mul_of_mem_fixV_thompsonJ (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h2 : Ch10.Case10_1_1Two T L I)
    {w : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)}
    (hw : w ∈ fixV (autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T))) :
    ∃ w₁ : ↥(commV D.K₁), ∃ w₂ ∈ commV D.K₂, w = w₁.1 * w₂ ∧
      ∀ p ∈ D.K₁ ⊓ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T), p w₁.1 = w₁.1 := by
  have hmem : w ∈ commV D.K₁ ⊔ commV D.K₂ := by
    rw [commV_sup_eq_top_case2 h37 h38 h2 D]
    exact Subgroup.mem_top w
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.mp hmem
  refine ⟨⟨w₁, hw₁⟩, w₂, hw₂, rfl, fun p hp => ?_⟩
  have h1 := hw p hp.2
  rw [map_mul, D.triv₁ hp.1 hw₂] at h1
  exact mul_right_cancel h1

include D in
theorem fsuVM_le_baum' (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h2 : Ch10.Case10_1_1Two T L I) : fsuVM T L I ≤ baum T :=
  (fsuVM_le_thompsonJ h37 h38 h2 D).trans (B2F.thompsonJ_le_baum T)

theorem vOne_comm (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h2 : Ch10.Case10_1_1Two T L I) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {c : G} (hc : c ∈ Subgroup.centralizer (fsuL0 T L : Set G)) : c * vOne D = vOne D * c :=
  (Subgroup.mem_centralizer_iff.mp hc _ (SecA.le_fsuL0 T L (CFSG.LieType.BorelTits.pCoreOf_le 2 L
    (SecE.fsuUL_le_pCoreOf_L hyp (vOne_mem_fsuUL D h37 h38 h2 ht htn))))).symm

theorem conj_rho_of_mem_E
    (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (h2 : Ch10.Case10_1_1Two T L I) (hb : IsShort2 L ∧ IsAltType L 5) (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {ρ : Subgroup.normalizer (fsuVM T L I : Set G)}
    (hρL : (ρ : G) ∈ T ⊓ L) (hρ : convI (SecA.isElemAbelian_fsuVM hyp) ρ = (D.θ₁.symm SecE.rA).1)
    {e : G} (he : e ∈ omegaOneCenterOf (baum T)) :
    (ρ : G) * e * (ρ : G)⁻¹ = e ∨ (ρ : G) * e * (ρ : G)⁻¹ = e * vOne D := by
  have hV := SecA.isElemAbelian_fsuVM hyp
  obtain ⟨v, hv, c, hc, rfl, hvS⟩ := exists_mul_of_mem_omegaOneCenterOf h113 h37 h38 h3228 hyp
    h2 hb ht htn (fsuVM_le_baum' D h37 h38 h2) he
  obtain ⟨w₁, w₂, hw₂, hw, hfix⟩ := exists_mul_of_mem_fixV_thompsonJ D h37 h38 h2
    (mem_fixV_of_mem_centralizer_baum D hv hvS)
  have hρc : (ρ : G) * c * (ρ : G)⁻¹ = c := by
    rw [Subgroup.mem_centralizer_iff.mp hc.2 (ρ : G) (SecA.le_fsuL0 T L hρL.2)]
    group
  have hρw₂ : (D.θ₁.symm SecE.rA).1 w₂ = w₂ := D.triv₁ (D.θ₁.symm SecE.rA).2 hw₂
  have hval : ∀ y, (convI hV ρ y).val = (ρ : G) * y.val * (ρ : G)⁻¹ :=
    fun y => convI_apply_val hV ρ y
  rcases rho_apply_of_fix D w₁ hfix with h | h
  · left
    have h1 : convI hV ρ (IntMod.mk hV ⟨v, hv⟩) = IntMod.mk hV ⟨v, hv⟩ := by
      rw [hw, map_mul, hρ, h, hρw₂]
    have h3 := congrArg IntMod.val h1
    rw [hval] at h3
    calc (ρ : G) * (v * c) * (ρ : G)⁻¹ = ((ρ : G) * v * (ρ : G)⁻¹) * ((ρ : G) * c * (ρ : G)⁻¹) :=
          by group
      _ = v * c := by rw [show (ρ : G) * v * (ρ : G)⁻¹ = v from h3, hρc]
  · right
    have h1 : convI hV ρ (IntMod.mk hV ⟨v, hv⟩) = IntMod.mk hV ⟨v, hv⟩ * (vOneW D).1 := by
      rw [hw, map_mul, hρ, h, hρw₂, Subgroup.coe_mul, mul_right_comm]
    have h3 := congrArg IntMod.val h1
    rw [hval, IntMod.val_mul] at h3
    calc (ρ : G) * (v * c) * (ρ : G)⁻¹ = ((ρ : G) * v * (ρ : G)⁻¹) * ((ρ : G) * c * (ρ : G)⁻¹) :=
          by group
      _ = v * vOne D * c := by rw [show (ρ : G) * v * (ρ : G)⁻¹ = v * vOne D from h3, hρc]
      _ = v * c * vOne D := by rw [mul_assoc, ← vOne_comm D h37 h38 h2 ht htn hc.2, ← mul_assoc]

theorem conj_of_mem_inf_L_of_mem_E
    (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (h2 : Ch10.Case10_1_1Two T L I)
    (hb : IsShort2 L ∧ IsAltType L 5) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {ρ : Subgroup.normalizer (fsuVM T L I : Set G)} (hρL : (ρ : G) ∈ T ⊓ L)
    (hρ : convI (SecA.isElemAbelian_fsuVM hyp) ρ = (D.θ₁.symm SecE.rA).1) {x : G}
    (hx : x ∈ T ⊓ L) {e : G} (he : e ∈ omegaOneCenterOf (baum T)) :
    x * e * x⁻¹ = e ∨ x * e * x⁻¹ = (ρ : G) * e * (ρ : G)⁻¹ := by
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hxN : x ∈ Subgroup.normalizer (fsuVM T L I : Set G) := SecA.le_normalizer_fsuVM T L I hx.1
  set xg : Subgroup.normalizer (fsuVM T L I : Set G) := ⟨x, hxN⟩
  have hxg : convI hV xg ∈ autI hV (T ⊓ L) := convI_mem_autI hV hx hxN
  have hxK : convI hV xg ∈ D.K₁ := oTwoUpper_le _ (D.autI_inf_L_le hxg)
  obtain ⟨v, hv, c, hc, rfl, hvS⟩ := exists_mul_of_mem_omegaOneCenterOf h113 h37 h38 h3228 hyp
    h2 hb ht htn (fsuVM_le_baum' D h37 h38 h2) he
  obtain ⟨w₁, w₂, hw₂, hw, hfix⟩ := exists_mul_of_mem_fixV_thompsonJ D h37 h38 h2
    (mem_fixV_of_mem_centralizer_baum D hv hvS)
  have hcomm : ∀ y ∈ L, y * c * y⁻¹ = c := fun y hy => by
    rw [Subgroup.mem_centralizer_iff.mp hc.2 y (SecA.le_fsuL0 T L hy)]
    group
  have hxw₂ : convI hV xg w₂ = w₂ := D.triv₁ hxK hw₂
  have hρw₂ : (D.θ₁.symm SecE.rA).1 w₂ = w₂ := D.triv₁ (D.θ₁.symm SecE.rA).2 hw₂
  have hsplit : ∀ y : Subgroup.normalizer (fsuVM T L I : Set G), (y : G) ∈ L →
      (y : G) * (v * c) * (y : G)⁻¹ = (convI hV y (IntMod.mk hV ⟨v, hv⟩)).val * c := by
    intro y hy
    rw [convI_apply_val]
    calc (y : G) * (v * c) * (y : G)⁻¹ = ((y : G) * v * (y : G)⁻¹) * ((y : G) * c * (y : G)⁻¹) :=
          by group
      _ = _ := by rw [hcomm _ hy]; rfl
  rcases apply_of_mem_autI_inf_L D h37 h38 h322 h2 hxg w₁ hfix with h | h
  · left
    rw [show x = (xg : G) from rfl, hsplit xg hx.2, hw, map_mul, h, hxw₂, ← hw]
    rfl
  · right
    rw [show x = (xg : G) from rfl, hsplit xg hx.2, hsplit ρ hρL.2, hw, map_mul, map_mul, h, hxw₂,
      hρ, hρw₂]

include D in
theorem conj_of_mem_pCoreOf_fsuL0_of_mem_E (h113 : ASInputs.AS_C_1_13)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (h2 : Ch10.Case10_1_1Two T L I) (hb : IsShort2 L ∧ IsAltType L 5) (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {o : G} (ho : o ∈ pCoreOf 2 (fsuL0 T L))
    {e : G} (he : e ∈ omegaOneCenterOf (baum T)) : o * e * o⁻¹ = e := by
  obtain ⟨v, hv, c, hc, rfl, -⟩ := exists_mul_of_mem_omegaOneCenterOf h113 h37 h38 h3228 hyp
    h2 hb ht htn (fsuVM_le_baum' D h37 h38 h2) he
  have hoV := Subgroup.mem_centralizer_iff.mp (SecA.pCoreOf_fsuL0_le_centralizer h322 hyp ho) v hv
  have hoc := Subgroup.mem_centralizer_iff.mp hc.2 o (CFSG.LieType.BorelTits.pCoreOf_le 2 _ ho)
  have h1 : o * v * o⁻¹ = v := by rw [← hoV]; group
  have h2' : o * c * o⁻¹ = c := by rw [hoc]; group
  calc o * (v * c) * o⁻¹ = (o * v * o⁻¹) * (o * c * o⁻¹) := by group
    _ = v * c := by rw [h1, h2']

end CFSG.Quasithin.Vol2.Ch10.SecF
