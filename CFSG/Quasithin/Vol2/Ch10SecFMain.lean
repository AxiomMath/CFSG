module

public import CFSG.Quasithin.Vol2.Ch10SecF3
public import CFSG.Quasithin.Vol2.Ch10SecFElts
public import CFSG.Quasithin.Vol2.Ch10SecQ4C3
public import CFSG.Quasithin.Vol2.Ch10SecFObl
public import CFSG.Quasithin.Vol2.Ch10SecFS6

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem normalizer_baum_le_case2_ne
    (he23 : E2.E23Statement) (he234 : E2.E23FourStatement)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (h311 : Theorem311Stmt) (h331 : Stmt3_3_1)
    (h113 : ASInputs.AS_C_1_13) (h1013 : Ch10.Stmt10_1_3) (hO1 : Obl10_2_1E4HStar)
    (hO2 : Obl10_2_1E4A314) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G))
    (hCZ : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) ≠ ⊥) :
    Subgroup.normalizer (baum T : Set G) ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hNS
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hb := SecE.isA5Block_case2 he234 h37 h38 hshape h3228 h331 hyp h2 hJ hNS
  obtain ⟨D⟩ := SecE.exists_case2Data he23 h37 h38 h322 hshape h3228 hyp h2 ht htn hJ
  obtain ⟨H, hH, hHS⟩ := exists_isHStar_le_normalizer_baum hyp hNS
  obtain ⟨ρ, hρL, hρ⟩ := D.exists_rho h37 h38 h322 h2
  obtain ⟨hvH, htr⟩ := vOne_mem_VZ D h311 h331 h37 h38 hshape h113 h322 h3228 h2 hb hCZ ht htn
    hH hHS hρL hρ
  have hρC := not_mem_centralizer_VZ D h311 h331 h37 h38 hshape h113 h322 h3228 h2 hb hCZ ht htn
    hH hHS hρL hρ
  have hv₁ := vOne_mem_fsuUL D h37 h38 h2 ht htn
  rcases hO1 G T L I hyp h2 hJ hNS hCZ hb.1 hb.2 H hH hHS t ht htn (ρ : G) hρL (vOne D) hv₁
      (vOne_ne_one D) hvH htr hρC with hY | ⟨x, hx, hx3⟩
  · set w := t⁻¹ * vOne D * t with hw
    have hwV : w ∈ CFSG.conjugate (fsuUL T L I) t := by
      rw [mem_conjugate_iff']
      simpa [hw, mul_assoc] using hv₁
    have hw1 : w ≠ 1 := by
      intro h
      apply vOne_ne_one D
      calc vOne D = t * w * t⁻¹ := by rw [hw]; group
        _ = 1 := by rw [h]; group
    have hsyl := isSylowTwoOf_T1_centralizer h311 h331 h37 h38 hshape hyp h2 ht htn hwV hw1
      (T1_le_centralizer_vTwo D h37 h38 h322 h2 ht htn)
    obtain ⟨hXs, hLX, J, hJX, hLJ, hT1J⟩ :=
      exists_cComp_centralizer h37 h38 h39 hyp ht htn hwV hw1 hsyl
    rcases eq_or_lt_of_le hLJ with hLJ' | hLJ'
    ·
      subst hLJ'
      have hs := hyp.fsu.simple
      have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
      have hwVM : w ∈ fsuVM T L I := SecA.conjugate_fsuUL_le (SecA.le_fsuM T L ht) hwV
      have hw2 : IsPGroup 2 (Subgroup.zpowers w) :=
        (SecA.isPGroup_fsuVM hyp).to_le (Subgroup.zpowers_le.mpr hwVM)
      have hX2 : pCoreOf 2 (Subgroup.centralizer ({w} : Set G)) ≠ ⊥ := by
        intro hbot
        apply hw1
        have := SecB.mem_pCoreOf_centralizer hw2
        rw [hbot] at this
        exact this
      have hcl : conjClosure L (Ch10.T1 T L) = L := le_antisymm
        (conjClosure_le fun s hs l hl => (Subgroup.mem_normalizer_iff.mp hs.2 l).mp hl)
        (le_conjClosure L _)
      have hXL : Subgroup.centralizer ({w} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
        have := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hK h37 h38 hX2 hsyl hJX
        rwa [hcl] at this
      have hYL : oTwoUpper (H ⊓ Subgroup.centralizer ({w} : Set G)) ≤
          Subgroup.normalizer (L : Set G) := ((oTwoUpper_le _).trans inf_le_right).trans hXL
      have hPY : T ⊓ L ≤ Subgroup.normalizer
          (oTwoUpper (H ⊓ Subgroup.centralizer ({w} : Set G)) : Set G) :=
        (inf_le_inf hH.1.1 hLX).trans (le_normalizer_oTwoUpper _)
      have hU := (SecE.blockU_eq_fsuUL h113 hyp h2 hb).1
      have hZ : blockZ L = ⊥ := by
        rw [blockZ, hU]
        exact fsuUL_inf_centralizer_eq_bot h2
      exact false_of_relIndex_eq_three hb.2 hZ hYL (SecA.isSylowTwoOf_inf hyp.fsu.maximal.1) hPY
        (hU ▸ hv₁) hY
    ·
      obtain ⟨x₅, hx₅L, hx₅⟩ := exists_orderOf_eq_five h2
      obtain ⟨z, hzLt, hz3, hzL, hzw⟩ :=
        exists_orderOf_eq_three_conjugate D h113 h37 h2 hb ht htn
      rcases (hO2 G T L I hyp h2 L (Or.inl rfl) hb.1 hb.2 _ J hXs hsyl hJX hLJ' hT1J).2 with
        ⟨⟨e⟩, hJ3⟩ | ⟨hhat, ⟨z₀, hz₀J, hz₀C, hz₀3⟩, h3J⟩
      · exact false_of_oPrimeResidual_eq e hJ3 hLJ hx₅L hx₅ hzw hz3 hzL
      ·
        have hLtC : CFSG.conjugate L t ≤ Subgroup.centralizer (L : Set G) :=
          Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (commutator_conjugate_eq_bot h113 h37 hyp h2 hb ht htn))
        refine C10E4.false_of_isHat hhat hz₀J hz₀C hz₀3 h3J hT1J hb.2
          (SecA.isSylowTwoOf_inf hyp.fsu.maximal.1) (fun s hs => ?_) hLJ hx₅L hx₅ hzw hz3 hzL
          (mem_conjugate_iff'.mp hzLt)
        refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hs.1) ht, ?_⟩
        apply Subgroup.centralizer_le_normalizer
        apply hLtC
        rw [mem_conjugate_iff']
        simpa [mul_assoc] using hs.2
  · exact false_of_orderOf_eq_three D h1013 h113 h37 h38 h3228 h2 hb ht htn hx.2 (hHS hx.1) hx3

end CFSG.Quasithin.Vol2.Ch10.SecF
