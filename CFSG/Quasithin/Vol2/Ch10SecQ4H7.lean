module

public import CFSG.Quasithin.Vol2.Ch10SecQ4H6
public import CFSG.Quasithin.Vol2.Ch10SecGFact
public import CFSG.Quasithin.Vol2.Ch10SecFObl
public import CFSG.Quasithin.Vol2.Ch10SecFComm
public import CFSG.Quasithin.Background.G64Proof
public import CFSG.Quasithin.Vol2.Ch10SecQ4H4
public import CFSG.Quasithin.Vol2.Ch10SecQ4H5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem obl10_2_1E4HStar_of (h56 : AsB56) (hF : SecG.G64CommTransvFact) (h331 : Stmt3_3_1)
    (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) : Obl10_2_1E4HStar := by
  intro G _ _ T L I hyp h2 _ _ _ hb1 hb2 H hH _ t ht htn t₁ ht₁ v₁ hv₁ hv₁1 hv₁H htr ht₁C
  have := hyp.fsu.simple
  have hTH : T ≤ H := hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTH
  have hchar : CharTwo H := charTwo_of_inH' hyp.fsu.qtke hyp.fsu.sylow hH.1
  have hR : IsTwoReducedIn H (VZ T H) :=
    (conjClosure_isTwoReducedIn_of_charTwo hTsyl hchar le_rfl).2.2
  have ht₁H : t₁ ∈ H := hTH ht₁.1
  have hUR := C10E4.isTwoReducedIn_conjClosure hR ht₁H hv₁H hv₁1 htr ht₁C
  have hUe := hUR.2.2.1
  have hsq : CFSG.SectionRank.IsSQTKCat ↥H :=
    (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1 H hH.1.2
  have h61 := C10E4.hyp61_autI hUe hsq hR ht₁H hv₁H hv₁1 htr ht₁C
  have hcard := C10E4.card_commV_transvI hUe hR ht₁H hv₁H hv₁1 htr ht₁C
  have hconc := G64.lemmaG64_of_b5 h56 _ IntMod.sq_eq_one _ _ h61 hcard
  have hHU := le_normalizer_conjClosure (Subgroup.zpowers v₁) H
  set g := convI hUe ⟨t, hHU (hTH ht)⟩ with hg
  have hgG : g ∈ autI hUe H := convI_mem_autI hUe (hTH ht) _
  have hLC : L ≤ Subgroup.centralizer (CFSG.conjugate L t : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (commutator_conjugate_eq_bot h113 h37 hyp h2 ⟨hb1, hb2⟩ ht htn)
  have hct : t⁻¹ * t₁ * t ∈ CFSG.conjugate L t := by
    rw [mem_conjugate_iff']
    simpa [mul_assoc] using ht₁.2
  have hc : (t⁻¹ * t₁ * t) * t₁ = t₁ * (t⁻¹ * t₁ * t) :=
    Subgroup.mem_centralizer_iff.mp (hLC ht₁.2) _ hct
  have hcomm : C10E4.transvI hUe ht₁H * (g⁻¹ * C10E4.transvI hUe ht₁H * g) =
      g⁻¹ * C10E4.transvI hUe ht₁H * g * C10E4.transvI hUe ht₁H := by
    simp only [C10E4.transvI, hg, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hc.symm
  have hval : (g⁻¹ (C10E4.centreI hUe)).val = t⁻¹ * v₁ * t := by
    rw [hg, ← map_inv, convI_apply_val]
    simp [C10E4.centreI_val]
  have hmove : g⁻¹ (C10E4.centreI hUe) ≠ C10E4.centreI hUe := by
    intro h
    have h1 : t⁻¹ * v₁ * t = v₁ := by rw [← hval, h]; rfl
    have hmem : v₁ ∈ fsuUL T L I ⊓ CFSG.conjugate (fsuUL T L I) t := by
      refine Subgroup.mem_inf.mpr ⟨hv₁, ?_⟩
      rw [mem_conjugate_iff']
      have h2 : t * v₁ * t⁻¹ = v₁ := by
        calc t * v₁ * t⁻¹ = t * (t⁻¹ * v₁ * t) * t⁻¹ := by rw [h1]
          _ = v₁ := by group
      rw [h2]
      exact hv₁
    rw [fsuUL_inf_conjugate_eq_bot h37 h38 hyp h2 ht htn] at hmem
    exact hv₁1 hmem
  rcases hF _ IntMod.sq_eq_one _ _ h61 hcard hconc (autI hUe T)
      (Setup.isSylowTwoOf_autOn hTsyl hHU) (C10E4.centreI hUe)
      (C10E4.commV_zpowers_transvI hUe hR ht₁H hv₁H hv₁1 htr ht₁C) g hgG hcomm hmove with
    ⟨X, hTX, hXlt, x, hxX, hx3⟩ | ⟨y, hyG, hy2, hy3, hy1, hodd⟩
  · right
    exact C10E4.exists_orderOf_three_of_lt hUe hTH (SecB.isUniqueMaxOver_of_isHStar h331 hyp hH)
      hTX hXlt hxX hx3
  · left
    exact C10E4.relIndex_eq_three hUe hval hyG hy2 hy3 hy1 hodd

end CFSG.Quasithin.Vol2.Ch10.SecF
