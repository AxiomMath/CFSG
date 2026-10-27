module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Adj
public import CFSG.Quasithin.Vol2.Ch10SecEN3d
public import CFSG.Quasithin.Vol2.Ch10SecEE3C
public import CFSG.Quasithin.Vol2.Ch10SecEE3Inv2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem inf_centralizer_le_pCoreOf
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {X : Subgroup G}
    (hX : X ≤ fsuL0 T L ⊔ T) :
    X ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXN : X ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    hX.trans (fsuL0_sup_le_normalizer T L I)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    (hyp.fsu.sylow.1.to_le ((inf_le_inf_right _ hX).trans (inf_centralizer_le_T h37 h38 hyp)))
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  have hxC := normalizer_le_normalizer_centralizer' (fsuVM T L I) (hXN hx)
  intro y
  constructor
  · intro hy
    exact ⟨X.mul_mem (X.mul_mem hx hy.1) (X.inv_mem hx),
      (Subgroup.mem_normalizer_iff.mp hxC y).mp hy.2⟩
  · intro hy
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hxC y).mpr hy.2⟩
    have h1 := X.mul_mem (X.mul_mem (X.inv_mem hx) hy.1) hx
    simpa [mul_assoc] using h1

namespace Case2Data

variable {hyp : Hyp10 G T L I} {t : G} (D : Case2Data hyp t)
include D

theorem autI_L_ne_bot : autI (SecA.isElemAbelian_fsuVM hyp) L ≠ ⊥ := by
  intro h
  have h1 := symm_mem_oTwoUpper D.θ₁ cThree_mem_alt
  rw [D.oTwo₁, h, Subgroup.mem_bot] at h1
  have h2 : D.θ₁.symm cThree = 1 := Subtype.ext h1
  have h3 := congrArg D.θ₁ h2
  rw [MulEquiv.apply_symm_apply, map_one] at h3
  exact cThree_ne_one h3

theorem mem_normalizer_L (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {x : Subgroup.normalizer
      (fsuVM T L I : Set G)} (hxT : (x : G) ∈ T)
    (hx : (autI (SecA.isElemAbelian_fsuVM hyp) L).map
      (MulAut.conj (convI (SecA.isElemAbelian_fsuVM hyp) x)⁻¹).toMonoidHom =
        autI (SecA.isElemAbelian_fsuVM hyp) L) :
    (x : G) ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hxn
  have e := SecA.conjugate_eq_of_not_mem h37 h38 hyp ht htn hxT hxn
  have h1 := SecA.autOn_conjugate (V := fsuVM T L I) (X := L) x.2
  rw [e] at h1
  have h2 : autI (SecA.isElemAbelian_fsuVM hyp) (CFSG.conjugate L t) =
      autI (SecA.isElemAbelian_fsuVM hyp) L := h1.trans hx
  have h3 : autI (SecA.isElemAbelian_fsuVM hyp) L ≤ D.K₁ ⊓ D.K₂ :=
    le_inf (D.oTwo₁ ▸ oTwoUpper_le D.K₁) (h2 ▸ D.oTwo₂ ▸ oTwoUpper_le D.K₂)
  rw [D.inf] at h3
  exact D.autI_L_ne_bot (le_bot_iff.mp h3)

theorem map_autI_L_eq {g : MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))}
    (hg : g ∈ D.K₁ ∨ g ∈ D.K₂) :
    (autI (SecA.isElemAbelian_fsuVM hyp) L).map (MulAut.conj g⁻¹).toMonoidHom =
      autI (SecA.isElemAbelian_fsuVM hyp) L := by
  rw [← D.oTwo₁]
  rcases hg with hg | hg
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (le_normalizer_oTwoUpper D.K₁ (D.K₁.inv_mem hg))
  · apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      have hc := D.comm a (oTwoUpper_le _ ha) g⁻¹ (D.K₂.inv_mem hg)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [← hc, inv_mul_cancel_right]
      exact ha
    · intro a ha
      refine ⟨a, ha, ?_⟩
      have hc := D.comm a (oTwoUpper_le _ ha) g⁻¹ (D.K₂.inv_mem hg)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [← hc, inv_mul_cancel_right]

theorem exists_lift₂
    (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    (h2 : Ch10.Case10_1_1Two T L I) (hb : IsShort2 L ∧ IsAltType L 5)
    (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    (hCV : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ = sA ∨ σ = sB) :
    ∃ c : Subgroup.normalizer (fsuVM T L I : Set G),
      (c : G) ∈ Ch10.T1 T L ⊓ Subgroup.centralizer (L : Set G) ∧ (c : G) ^ 2 = 1 ∧
        convI (SecA.isElemAbelian_fsuVM hyp) c = ((D.θ₂.symm σ : ↥D.K₂) : MulAut _) := by
  obtain ⟨x, hxT, hx2, hxθ⟩ := D.exists_involution₂ hC0 hCV hσ
  have hxK : convI (SecA.isElemAbelian_fsuVM hyp) x ∈ D.K₂ := hxθ ▸ (D.θ₂.symm σ).2
  have hxN := D.mem_normalizer_L h37 h38 ht htn hxT (D.map_autI_L_eq (Or.inr hxK))
  have hT₁B : Ch10.T1 T L ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hUV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  obtain ⟨hU, hO, -⟩ := blockU_eq_fsuUL h113 hyp h2 hb
  have hUN : Ch10.T1 T L ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.normalizer (fsuUL T L I : Set G) := hU ▸ inf_le_left.trans T1_le_normalizer_blockU
  have hinner : (x : G) ∈ innerLike (Ch10.T1 T L) L hT₁B := by
    refine mem_innerLike.mpr ⟨⟨hxT, hxN⟩, fun l hl => ?_⟩
    have hlN := hLN hl
    have hlL : (x : G) * l * (x : G)⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN l).mp hl) (L.inv_mem hl)
    have hlK : convI (SecA.isElemAbelian_fsuVM hyp) ⟨l, hlN⟩ ∈ D.K₁ := by
      have h1 := convI_mem_autI (SecA.isElemAbelian_fsuVM hyp) hl hlN
      rw [← D.oTwo₁] at h1
      exact oTwoUpper_le _ h1
    have hc : convI (SecA.isElemAbelian_fsuVM hyp) (x * ⟨l, hlN⟩ * x⁻¹ * ⟨l, hlN⟩⁻¹) = 1 := by
      have hcomm := D.comm _ hlK _ hxK
      simp only [map_mul, map_inv]
      rw [← hcomm]
      group
    have hcV := (convI_eq_one_iff _ _).mp hc
    exact inf_centralizer_le_pCoreOf h37 h38 hyp ((SecA.le_fsuL0 T L).trans le_sup_left)
      ⟨hlL, hcV⟩
  have hxU : ∀ u ∈ fsuUL T L I, (x : G) * u = u * x := by
    intro u hu
    have h1 : convI (SecA.isElemAbelian_fsuVM hyp) x
        (IntMod.mk (SecA.isElemAbelian_fsuVM hyp) ⟨u, hUV hu⟩) =
        IntMod.mk (SecA.isElemAbelian_fsuVM hyp) ⟨u, hUV hu⟩ :=
      D.triv₂ hxK ((D.mem_commV₁_iff _).mpr hu)
    have h2 := (convI_fix_iff _ x _).mp h1
    calc (x : G) * u = ((x : G) * u * (x : G)⁻¹) * x := by group
      _ = u * x := by rw [show (x : G) * u * (x : G)⁻¹ = u from h2]
  have hU2 : ∀ u ∈ fsuUL T L I, u ^ 2 = 1 := fun u hu => (SecA.isElemAbelian_fsuVM hyp).2 u (hUV hu)
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
