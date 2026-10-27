module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagFinalDefs
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagN02
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagI04a1
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagI05core
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagN05
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagN06
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagMovedComponent

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)


section Certs


theorem ys03_I04a_not_Z3L34 {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G}
    {L J : Subgroup G} (h : DiagSetting G A M H s L)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hJ : J ∈ thetaComponents 3 G)
    (h3J : 3 ∣ Nat.card J) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hJL : ¬ J.map (starQuot G) ≤ L.map (starQuot G)) (hrk : 1 < CFSG.Open.pRank 3 J) :
    ¬ Nonempty (↥((A ⊔ L).map (starQuot G)) ≃*
      Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) := by
  rintro ⟨eX⟩
  have hE27 := h.ctx.ctx444.isE27
  have hA3 : IsPGroup 3 A := hE27.isPGroup
  have hA27 : Nat.card (A.map (starQuot G)) = 27 :=
    (ys03_N12_card_map_starQuot hA3).trans hE27.2
  have hLp : Group.IsPerfect ↥(L.map (starQuot G)) :=
    (isComponent_map_starQuot h.mem h.three_dvd).1.1
  obtain ⟨hC3, hdec⟩ := ys03_I04a1_Z3L34_structure
    ((Subgroup.map_mono hAL).trans (Subgroup.le_normalizer_map (starQuot G))) hLp
    (CFSG.Open.IsElemAbelian.map hE27.1 _) hA27 (Subgroup.map_mono le_sup_left)
    (Subgroup.map_mono le_sup_right) (Subgroup.map_sup A L (starQuot G)).le ⟨eX⟩
  obtain ⟨T, hTJ, hT3, hAT, hconj, z, hzAJ, hz1, hTz⟩ :=
    ys03_N02_sylow_center h.ctx.ctx444 hAJ h3J
  have hTC : T ≤ Subgroup.centralizer (A : Set G) :=
    ys03_I04a2_T_le_centralizer h.mem h.three_dvd hJ h3J hJL hA3 hT3 hAT hTJ hzAJ.1 hz1 hzAJ.2 hTz
      hC3 hdec
  have hAJ3 := ys03_I04a3_card_inf_le h.mem h.three_dvd hJ h3J hJL hA3 hC3
  obtain ⟨E, hEJ, hEab, hEcard⟩ :=
    Sec5.exists_elemAbelian_le_of_le_pRank Nat.prime_three (show 2 ≤ CFSG.Open.pRank 3 J from hrk)
  obtain ⟨j, hjJ, hjT⟩ := hconj E hEJ (Sec5.isPGroup_of_isElemAbelian hEab)
  have hEab' : CFSG.Assembly.IsElemAbelian 3 (E.map (MulAut.conj j).toMonoidHom) :=
    CFSG.Open.IsElemAbelian.map hEab _
  have hE9 : 9 ≤ Nat.card (E.map (MulAut.conj j).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj j).injective, hEcard]
    norm_num
  have hEA : E.map (MulAut.conj j).toMonoidHom ≤ Subgroup.centralizer (A : Set G) := hjT.trans hTC
  have hcap : Nat.card (A ⊓ E.map (MulAut.conj j).toMonoidHom : Subgroup G) ≤ 3 :=
    (Subgroup.card_le_of_le (inf_le_inf_left A (hjT.trans hTJ))).trans hAJ3
  have hNM : Subgroup.normalizer (A : Set G) ≤ M :=
    (normalizer_le_gamma le_rfl (by rw [hE27.pRank_eq]; norm_num)).trans h.ctx.ctx444.gamma_le
  exact ys03_I04a4_rank hE27.1 hE27.2 hEab' hE9 hEA hcap
    (sup_le (Subgroup.le_normalizer.trans hNM)
      (hEA.trans ((Subgroup.centralizer_le_normalizer (A : Set G)).trans hNM)))
    h.ctx.ctx444.pRank_eq

theorem ys03_I05_center_le {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G}
    {L J : Subgroup G} (h : DiagSetting G A M H s L) (hJ : J ∈ thetaComponents 3 G)
    (h3J : 3 ∣ Nat.card J) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hJL : ¬ J.map (starQuot G) ≤ L.map (starQuot G))
    {U V : Subgroup ↥((A ⊔ L).map (starQuot G))} (hUV : U ⊔ V = ⊤)
    (hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hU : IsHeisThree U)
    (hVe : Nonempty (↥V ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (h3 : Nat.card (U ⊓ V : Subgroup ↥((A ⊔ L).map (starQuot G))) = 3)
    (hVL : V.map ((A ⊔ L).map (starQuot G)).subtype = L.map (starQuot G)) :
    (Subgroup.center ↥(L.map (starQuot G))).map (L.map (starQuot G)).subtype ≤
      J.map (starQuot G) := by
  obtain ⟨-, -, -, -, -, z, hzAJ, hz1, -⟩ := ys03_N02_sylow_center h.ctx.ctx444 hAJ h3J
  have hLc : IsComponent (L.map (starQuot G)) := isComponent_map_starQuot h.mem h.three_dvd
  have hJc : IsComponent (J.map (starQuot G)) := isComponent_map_starQuot hJ h3J
  have hLJ : ∀ x ∈ L.map (starQuot G), ∀ y ∈ J.map (starQuot G), Commute x y := by
    rcases CFSG.LocalCores.distinct_components_commute hLc hJc with hEq | hc
    · exact absurd (le_of_eq hEq.symm) hJL
    · exact ys03_I22_commute_of_bot hc
  exact ys03_I05core (A' := A.map (starQuot G)) hLJ
    ((Subgroup.map_mono hAJ).trans (Subgroup.le_normalizer_map (starQuot G)))
    (Subgroup.map_mono le_sup_left) (Subgroup.map_mono le_sup_right)
    (Subgroup.map_sup A L (starQuot G)).le hUV hcomm hU hVe h3 hVL
    ⟨Subgroup.mem_map_of_mem _ hzAJ.1, Subgroup.mem_map_of_mem _ hzAJ.2⟩
    (ys03_N13_map_ne_one h.ctx.ctx444.isE27.isPGroup hzAJ.1 hz1)

section Assembly


theorem ys03_I17_assembly (hI : DiagInputs) {G : Type} [Group G] [Finite G] {A M H : Subgroup G}
    {s : G} {L : Subgroup G} (h : DiagSetting G A M H s L) : Concl4443 M H := by
  have hG : SectionFourHyp G := h.ctx.ctx444.sectionFourHyp
  obtain ⟨J, hJ, h3J, hAJ, hIJ, hJc, hJL⟩ :=
    ys03_I02_exists_J hI.kpSz hI.schreier hI.item45 h
  have hJcomp : IsComponent (J.map (starQuot G)) := isComponent_map_starQuot hJ h3J
  have hmov : ¬ (inSubgroup perfectResidual H).map (starQuot G) ≤
      Subgroup.centralizer ((J.map (starQuot G) : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) :
        Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
    not_map_le_centralizer_of_commutator_eq hJ h3J hJc
  obtain ⟨hsecJ, hrkJs⟩ := ys03_I03_moved_component hI.schreier hI.item45 h _ hJcomp hmov
  have hrkJ : 1 < CFSG.Open.pRank 3 J :=
    lt_of_lt_of_le hrkJs (pRank_map_le_of_not_dvd Nat.prime_three (starQuot G)
      (by rw [starQuot, QuotientGroup.ker_mk']; exact not_three_dvd_card_pPrimeCore) J)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Ctx444.le_normalizer_of_mem_thetaComponents hI.item45 h.ctx.ctx444 h.mem
  have hZ := Item4443SL.Ctx4443.isZ3L34OrHeisSL34_map hI.item434Sec hI.item45 h.ctx h.mem h.not_le
    h.s_norm h.s_nc
  have hHeis : IsHeisSLThreeFour ↥((A ⊔ L).map (starQuot G)) := by
    rcases hZ with hZ3 | hHeis
    · exact (ys03_I04a_not_Z3L34 h hAL hJ h3J hAJ hJL hrkJ hZ3).elim
    · exact hHeis
  obtain ⟨U, V, hUV, hcommUV, hU, hVe, h3UV⟩ := hHeis
  have hVL : V.map ((A ⊔ L).map (starQuot G)).subtype = L.map (starQuot G) :=
    ys03_I04b_V_eq (A' := A.map (starQuot G)) (L' := L.map (starQuot G))
      ((Subgroup.map_mono hAL).trans (Subgroup.le_normalizer_map (starQuot G)))
      (isComponent_map_starQuot h.mem h.three_dvd).1.1
      (CFSG.Open.IsElemAbelian.map h.ctx.ctx444.isE27.1 _).1
      (Subgroup.map_mono le_sup_left) (Subgroup.map_mono le_sup_right)
      (Subgroup.map_sup A L (starQuot G)).le hUV hcommUV hU hVe h3UV
  have hL4 := ys03_N15_equiv_of_map_eq hVL hVe
  have hZLJ := ys03_I05_center_le h hJ h3J hAJ hJL hUV hcommUV hU hVe h3UV hVL
  have h3Z := ys03_N05_three_dvd_center_J h hJ h3J hJL hL4 hZLJ
  have hcl := ys03_I08_classify hI h hJ h3J hL4 hJL h3Z hsecJ
  have hZJ3 : Nat.card (Subgroup.center ↥(J.map (starQuot G))) = 3 := by
    rcases hcl with ⟨m, hm, -, ⟨eSL⟩⟩ | ⟨-, hc⟩
    · exact ys03_N06_card_center_SL hm eSL
    · exact hc
  obtain ⟨hLC, ⟨eL⟩⟩ := ys03_D0_generic hG h.mem h.three_dvd
    (KFacts.L34.card_center_of_mulEquiv hL4.some) (ys03_N10_quotient_center_projSL hL4.some).some
    hI.residualL34 hI.centerL34
  have hJD : J ∈ oTwoComponents G ∧
      ((∃ n : ℕ, 1 ≤ n ∧ Nonempty (J ⧸ CFSG.pCore 2 J ≃*
          Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * n)))) ∨
        IsExtOf (J ⧸ CFSG.pCore 2 J) Blueprint.NativeSporadic.M22 (Multiplicative (ZMod 3))) := by
    rcases hcl with ⟨m, hm, ⟨ePSL⟩, ⟨eSL⟩⟩ | ⟨⟨eM⟩, hc⟩
    · have hres : ResidualAt (projSL 3 (GaloisField 2 (2 * m))) ∧
          CenterThreePrimeTwoAt (projSL 3 (GaloisField 2 (2 * m))) := by
        rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
        · exact ⟨hI.residualL34, hI.centerL34⟩
        · exact ⟨hI.residualSL3 m hm2, hI.centerSL3 m hm2⟩
      obtain ⟨hJC, ⟨eJ⟩⟩ := ys03_D0_generic hG hJ h3J hZJ3 ePSL hres.1 hres.2
      exact ⟨hJC, Or.inl ⟨m, hm, ⟨eJ.trans eSL⟩⟩⟩
    · obtain ⟨hJC, ⟨eJ⟩⟩ := ys03_D0_generic hG hJ h3J hc eM hI.residualM22 hI.centerM22
      exact ⟨hJC, Or.inr (ys03_N11_isExtOf_of_mulEquiv eJ
        (ys03_isExtOf_of_center_card_three hc eM))⟩
  have hmv : ∀ K : Subgroup (G ⧸ CFSG.pPrimeCore 3 G), IsComponent K →
      ¬ (inSubgroup perfectResidual H).map (starQuot G) ≤
        Subgroup.centralizer (K : Set (G ⧸ CFSG.pPrimeCore 3 G)) → 1 < CFSG.Open.pRank 3 K :=
    fun K hK hmovK => (ys03_I03_moved_component hI.schreier hI.item45 h K hK hmovK).2
  have hmap := ys03_I14b_map_I_le h hI.kpSz hI.schreier hI.item45 hL4 hJcomp hJL hZJ3 hrkJs hmv
  have hIle := ys03_I14c_I_le h hIJ hmap
  have hN := ys03_I15_LJ_normal h hL4 hJ h3J hJL hZJ3 (ys03_N14_two_le_pRank_of_SL34 hL4) hrkJs
  have hcomm := ys03_I16_commutator_eq h hN hIle hJc
  exact ⟨L, hLC, h.not_le, Or.inr ⟨h.I_iso, J, hJD.1, hcomm, ⟨eL.trans hL4.some⟩, hJD.2⟩⟩

theorem item4_44_3Diag_of_inputs (hI : DiagInputs) : Item4_44_3Diag :=
  item4_44_3Diag_iff.mpr fun _ _ _ _ _ _ _ _ h => ys03_I17_assembly hI h

end Assembly

end Certs

end CFSG.RankThree.PartTwo.Sec4

end
