module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Lift

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem conjugate_centralizer_eq (X : Subgroup G) (g : G) :
    CFSG.conjugate (Subgroup.centralizer (X : Set G)) g =
      Subgroup.centralizer (CFSG.conjugate X g : Set G) := by
  ext x
  rw [SecA.mem_conjugate_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have h1 := h _ (SecA.mem_conjugate_iff.mp hy)
    calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h1]
      _ = x * y := by group
  · intro h y hy
    have hy' : g⁻¹ * y * g ∈ CFSG.conjugate X g := by
      rw [SecA.mem_conjugate_iff]
      simpa [mul_assoc] using hy
    have h1 := h _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * y := by group

variable [Finite G] {T L I : Subgroup G}

theorem T1_le_normalizer_conjugate (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) :
    Ch10.T1 T L ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G) :=
  SecA.le_normalizer_conjugate_of (le_normalizer_T1 h37 h38 hyp ht) inf_le_right

theorem conjugate_T1 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) :
    CFSG.conjugate (Ch10.T1 T L) t = Ch10.T1 T L :=
  SecA.conjugate_eq_self_iff.mpr (le_normalizer_T1 h37 h38 hyp ht)

theorem pCoreOf_conjugate_sup_T1 (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    (hb : IsShort2 L ∧ IsAltType L 5) {t : G} (ht : t ∈ T) :
    pCoreOf 2 (CFSG.conjugate L t ⊔ Ch10.T1 T L) = ⁅fsuVM T L I, CFSG.conjugate L t⁆ ⊔
      (Ch10.T1 T L ⊓ Subgroup.centralizer (CFSG.conjugate L t : Set G)) := by
  obtain ⟨-, hO, -⟩ := blockU_eq_fsuUL h113 hyp h2 hb
  have hT := conjugate_T1 h37 h38 hyp ht
  have hsup : ∀ X Y : Subgroup G, CFSG.conjugate (X ⊔ Y) t =
      CFSG.conjugate X t ⊔ CFSG.conjugate Y t := fun X Y => Subgroup.map_sup X Y _
  have hinf : ∀ X Y : Subgroup G, CFSG.conjugate (X ⊓ Y) t =
      CFSG.conjugate X t ⊓ CFSG.conjugate Y t := fun X Y =>
    Subgroup.map_inf X Y _ (MulAut.conj t⁻¹).injective
  calc pCoreOf 2 (CFSG.conjugate L t ⊔ Ch10.T1 T L)
      = pCoreOf 2 (CFSG.conjugate (L ⊔ Ch10.T1 T L) t) := by rw [hsup, hT]
    _ = CFSG.conjugate (pCoreOf 2 (L ⊔ Ch10.T1 T L)) t := SecA.pCoreOf_conjugate _ _
    _ = CFSG.conjugate (fsuUL T L I ⊔
          (Ch10.T1 T L ⊓ Subgroup.centralizer (L : Set G))) t := by rw [hO]
    _ = _ := by
      rw [hsup, hinf, hT, conjugate_centralizer_eq,
        SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)]

namespace Case2Data

variable {hyp : Hyp10 G T L I} {t : G} (D : Case2Data hyp t)
include D

theorem exists_lift₁
    (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    (h2 : Ch10.Case10_1_1Two T L I) (hb : IsShort2 L ∧ IsAltType L 5)
    (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    (hCV : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ = sA ∨ σ = sB) :
    ∃ c : Subgroup.normalizer (fsuVM T L I : Set G),
      (c : G) ∈ Ch10.T1 T L ⊓ Subgroup.centralizer (CFSG.conjugate L t : Set G) ∧
        (c : G) ^ 2 = 1 ∧
        convI (SecA.isElemAbelian_fsuVM hyp) c = ((D.θ₁.symm σ : ↥D.K₁) : MulAut _) := by
  obtain ⟨x, hxT, hx2, hxθ⟩ := D.exists_involution₁ hC0 hCV hσ
  have hxK : convI (SecA.isElemAbelian_fsuVM hyp) x ∈ D.K₁ := hxθ ▸ (D.θ₁.symm σ).2
  have hxN := D.mem_normalizer_L h37 h38 ht htn hxT (D.map_autI_L_eq (Or.inl hxK))
  have hT₁B := T1_le_normalizer_conjugate h37 h38 hyp ht
  have hLN : CFSG.conjugate L t ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hUV : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  have hO := pCoreOf_conjugate_sup_T1 h113 h37 h38 hyp h2 hb ht
  have hUN : Ch10.T1 T L ⊓ Subgroup.centralizer (CFSG.conjugate L t : Set G) ≤
      Subgroup.normalizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G) :=
    SecA.le_normalizer_commutator (inf_le_left.trans (inf_le_left.trans
      (SecA.le_normalizer_fsuVM T L I))) (inf_le_left.trans hT₁B)
  have hx1 : (x : G) ∈ Ch10.T1 T L := ⟨hxT, hxN⟩
  have hinner : (x : G) ∈ innerLike (Ch10.T1 T L) (CFSG.conjugate L t) hT₁B := by
    refine mem_innerLike.mpr ⟨hx1, fun l hl => ?_⟩
    have hlN := hLN hl
    have hlL : (x : G) * l * (x : G)⁻¹ * l⁻¹ ∈ CFSG.conjugate L t :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hT₁B hx1) l).mp hl)
        (Subgroup.inv_mem _ hl)
    have hlK : convI (SecA.isElemAbelian_fsuVM hyp) ⟨l, hlN⟩ ∈ D.K₂ := by
      have h1 := convI_mem_autI (SecA.isElemAbelian_fsuVM hyp) hl hlN
      rw [← D.oTwo₂] at h1
      exact oTwoUpper_le _ h1
    have hc : convI (SecA.isElemAbelian_fsuVM hyp) (x * ⟨l, hlN⟩ * x⁻¹ * ⟨l, hlN⟩⁻¹) = 1 := by
      have hcomm := D.comm _ hxK _ hlK
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    have hcV := (convI_eq_one_iff _ _).mp hc
    exact inf_centralizer_le_pCoreOf h37 h38 hyp ((SecA.conjugate_le_fsuL0 ht).trans le_sup_left)
      ⟨hlL, hcV⟩
  have hxU : ∀ u ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆, (x : G) * u = u * x := by
    intro u hu
    have h1 : convI (SecA.isElemAbelian_fsuVM hyp) x
        (IntMod.mk (SecA.isElemAbelian_fsuVM hyp) ⟨u, hUV hu⟩) =
        IntMod.mk (SecA.isElemAbelian_fsuVM hyp) ⟨u, hUV hu⟩ :=
      D.triv₁ hxK ((D.mem_commV₂_iff ht _).mpr hu)
    have h2 := (convI_fix_iff _ x _).mp h1
    calc (x : G) * u = ((x : G) * u * (x : G)⁻¹) * x := by group
      _ = u * x := by rw [show (x : G) * u * (x : G)⁻¹ = u from h2]
  have hU2 : ∀ u ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆, u ^ 2 = 1 := fun u hu =>
    (SecA.isElemAbelian_fsuVM hyp).2 u (hUV hu)
  obtain ⟨c, hc, hc2, hxc⟩ := exists_centralizer_lift hT₁B
    (hyp.fsu.sylow.1.to_le inf_le_left) hO hUN hU2 hinner hx2 hxU
  have hcN : c ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
    SecA.le_normalizer_fsuVM T L I hc.1.1
  refine ⟨⟨c, hcN⟩, hc, hc2, ?_⟩
  rw [← hxθ]
  have h1 : convI (SecA.isElemAbelian_fsuVM hyp) (x * (⟨c, hcN⟩ : Subgroup.normalizer
      (fsuVM T L I : Set G))⁻¹) = 1 := by
    have hVab := (SecA.isElemAbelian_fsuVM hyp).1
    rw [convI_eq_one_iff]
    exact Subgroup.mem_centralizer_iff.mpr fun v hv => setLike_mul_comm hv (hUV hxc)
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1.symm

end Case2Data

end CFSG.Quasithin.Vol2.Ch10.SecE
