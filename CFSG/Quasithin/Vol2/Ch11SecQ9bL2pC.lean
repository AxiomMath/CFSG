module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bL2pB
public import CFSG.Quasithin.Vol2.Ch11SecA12Cart
public import CFSG.Quasithin.Vol2.Ch11SecA15Fix
public import CFSG.Quasithin.Vol2.Ch11SecA15Kind
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
public import CFSG.Quasithin.Vol2.Ch11SecSQuot
public import CFSG.Quasithin.Vol2.KGNatG2Order

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

namespace C11P9B

theorem commutator_mem_of_isSL3 (hFb : Facts12b) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁) (hV₂ : IsVi T L I 2 2 V₂)
    (hX : IsCartanX T L X) (hSL : IsSL3 4 (↥L ⧸ CFSG.pCore 2 ↥L)) {x : G}
    (hx : x ∈ xOne X (LOf L V₁)) {l : G} (hl : l ∈ L) : x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  obtain ⟨F, _, _, hF4, ⟨eF⟩⟩ := hSL
  let : Fintype F := Fintype.ofFinite F
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := L_le_normalizer_fsuV h
  have hα : IsModO2Surj L (eF.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) := by
    refine ⟨eF.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
    ext y
    simp
  have hk := (kindSL3_of_modO2Surj KGNat.factG2DerivedOrder_holds h1102 h (m := 2)
    (by rw [← Nat.card_eq_fintype_card, hF4]; norm_num) hα).1
  obtain ⟨_, K', _, _, π, hK', hπ⟩ := sl3_realization KGNat.factG2DerivedOrder_holds h1102 h hk
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hU₁ : IsFlagW (autOn L (fsuV T I)) (autOn (T ⊓ L) (fsuV T I))
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) 4 1
      (V₁.subgroupOf (fsuV T I)) := isFlagW_of_isVi h hV₁
  have hcent := (hFb.sl34 K' (hK'.trans (by norm_num)) _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _
    hU₁ _ (isHall_autOn_cartan h1102 h hX)).1
  have hxL : x ∈ L := (hX.1 hx.1).1
  have hxV := hLV hxL
  have hlV := hLV hl
  have hmem : conjV (fsuV T I) x hxV ∈ centW (autOn X (fsuV T I))
      (gammaW (autOn L (fsuV T I)) (V₁.subgroupOf (fsuV T I))) := by
    rw [← (transportData hN h1102 h hV₁ hV₂ hX).f₁]
    exact conjV_mem_autOn hx hxV
  have hc := hcent _ hmem _ (conjV_mem_autOn hl hlV)
  have h1 : conjV (fsuV T I) x hxV * conjV (fsuV T I) l hlV * (conjV (fsuV T I) x hxV)⁻¹ *
      (conjV (fsuV T I) l hlV)⁻¹ = 1 := by
    rw [hc]
    group
  rw [SecS.conjV_commutator] at h1
  rw [← centralizer_eq_pCoreOf h1102 h]
  refine ⟨L.mul_mem (L.mul_mem (L.mul_mem hxL hl) (L.inv_mem hxL)) (L.inv_mem hl),
    Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  have h2 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨v, hv⟩ : ↥(fsuV T I)) : G)) h1
  simp only [conjV_apply_coe, MulAut.one_apply] at h2
  calc v * (x * l * x⁻¹ * l⁻¹)
      = (x * l * x⁻¹ * l⁻¹) * v * (x * l * x⁻¹ * l⁻¹)⁻¹ * (x * l * x⁻¹ * l⁻¹) := by rw [h2]
    _ = (x * l * x⁻¹ * l⁻¹) * v := by group

theorem zL_le_of_isSL3 (hFb : Facts12b) (hC : CartanFacts) (hF : Facts12) (hN : NatFacts)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁)
    (hV₂ : IsVi T L I 2 2 V₂) (hX : IsCartanX T L X) (hSL : IsSL3 4 (↥L ⧸ CFSG.pCore 2 ↥L)) :
    xOne X (LOf L V₁) ≤ L ⊓ sectionCentralizer L (pCoreOf 2 L) ∧
      L ⊓ sectionCentralizer L (pCoreOf 2 L) ≤ xOne X (LOf L V₁) ⊔ pCoreOf 2 L := by
  have hX1L : xOne X (LOf L V₁) ≤ L := fun x hx => (hX.1 hx.1).1
  have hX1N : xOne X (LOf L V₁) ≤ L ⊓ sectionCentralizer L (pCoreOf 2 L) := fun x hx =>
    ⟨hX1L hx, Subgroup.le_normalizer (hX1L hx),
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (hX1L hx),
      fun l hl => commutator_mem_of_isSL3 hFb hN h1102 h hV₁ hV₂ hX hSL hx hl⟩
  refine ⟨hX1N, ?_⟩
  obtain ⟨F, _, _, hF4, ⟨eF⟩⟩ := hSL
  have hZ := (hF.table _ 2 le_rfl
    (Or.inl ⟨F, inferInstance, inferInstance, by rw [hF4]; norm_num, ⟨eF⟩⟩)).2.1
  have hNZ : modO2Image L (L ⊓ sectionCentralizer L (pCoreOf 2 L)) ≤
      Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rintro _ ⟨n, hn, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hc := (Subgroup.mem_subgroupOf.mp hn).2.2.2 l l.2
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (n * l * n⁻¹ * l⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (mem_pCore_of_mem_pCoreOf hc)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hX1c : Nat.card ↥(modO2Image L (xOne X (LOf L V₁))) = 3 := by
    rw [card_modO2Image_of_odd hX1L, card_xOne hC hF hN h1102 h hV₁ hV₂ hX]
    · norm_num
    · rw [card_xOne hC hF hN h1102 h hV₁ hV₂ hX]
      exact ⟨1, rfl⟩
  have heq : modO2Image L (xOne X (LOf L V₁)) =
      modO2Image L (L ⊓ sectionCentralizer L (pCoreOf 2 L)) := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono fun y hy =>
      Subgroup.mem_subgroupOf.mpr (hX1N (Subgroup.mem_subgroupOf.mp hy))) ?_
    rw [hX1c]
    exact Nat.le_of_dvd (by norm_num) ((Subgroup.card_dvd_of_le hNZ).trans hZ)
  rw [sup_eq_of_modO2Image_eq hX1L inf_le_left heq]
  exact le_sup_left

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
