module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallApply
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.CaseTwoBasics
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.NaturalTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.RankOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.NParamMap
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.RankOneCaseSum
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.RankOneCaseOm4m
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeAEqVInvolN
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
import CFSG.Quasithin.Background.FFC4Res
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Blueprint (LieModel)

variable {W : Type} [CommGroup W]

private theorem center_eq_bot_of_simple {X : Type} [Group X] [IsSimpleGroup X]
    (hX : CFSG.Open.IsQuasisimple X) : center X = ⊥ := by
  rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hcomm : commutator X = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x).symm
    obtain ⟨x, hx⟩ := exists_ne (1 : X)
    have hxt : x ∈ commutator X := hX.1 ▸ Subgroup.mem_top x
    rw [hcomm, Subgroup.mem_bot] at hxt
    exact hx hxt

private theorem isSimpleGroup_of_isL2_autSub [Finite W] {L : Subgroup (MulAut W)} {I : Subgroup W} {e j : ℕ}
    (hshape : IsL2 ↥L e ∨ IsSz ↥L e ∨ IsU3 ↥L e ∨ IsSU3 ↥L e) (hLI : L ≤ stabSub I)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hne : ¬ L ≤ centSub I) (hj : IsL2 ↥(autSub L I) j) :
    IsSimpleGroup ↥L := by
  rcases hshape with h | h | h | h
  · exact uc22p22r_lieModel_isSimple_classical (Or.inl rfl) h
  · exact uc22p22r_lieModel_isSimple_twistedB2 h
  · exact uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inl rfl)) h
  · exfalso
    have hSU := isSU3_of_surjective_central h (resTo hLI) (resTo_surjective hLI)
      (ker_resTo_le_center hq hLI hne) (nontrivial_autSub hLI hne)
    have : IsSimpleGroup ↥(autSub L I) := uc22p22r_lieModel_isSimple_classical (Or.inl rfl) hj
    have hZ := center_eq_bot_of_simple hSU.1
    let χ : ↥(autSub L I) ⧸ center ↥(autSub L I) ≃* ↥(autSub L I) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact not_isL2_of_isU3 (LieModel.of_mulEquiv χ hSU.2) hj

private theorem faithful_of_isSimpleGroup {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hs : IsSimpleGroup ↥L) (hLJ : L ≤ stabSub J) (hne : ¬ L ≤ centSub J) :
    ∀ l ∈ L, (∀ u ∈ J, l u = u) → l = 1 := by
  intro l hl hfix
  rcases (MonoidHom.normal_ker (resTo hLJ)).eq_bot_or_eq_top with h | h
  · have hk : (⟨l, hl⟩ : ↥L) ∈ (resTo hLJ).ker := by
      rw [MonoidHom.mem_ker, resTo_eq_one_iff]
      exact hfix
    rw [h, Subgroup.mem_bot] at hk
    exact congrArg Subtype.val hk
  · exfalso
    apply hne
    intro x hx
    have hk : (⟨x, hx⟩ : ↥L) ∈ (resTo hLJ).ker := h ▸ Subgroup.mem_top _
    exact mem_centSub.mpr ((resTo_eq_one_iff hLJ _).mp hk)

private theorem shape_autSub [Finite W] {L : Subgroup (MulAut W)} {I : Subgroup W} {e : ℕ}
    (hshape : IsL2 ↥L e ∨ IsSz ↥L e ∨ IsU3 ↥L e ∨ IsSU3 ↥L e) (hLI : L ≤ stabSub I)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hne : ¬ L ≤ centSub I) :
    IsL2 ↥(autSub L I) e ∨ IsSz ↥(autSub L I) e ∨ IsU3 ↥(autSub L I) e ∨
      IsSU3 ↥(autSub L I) e := by
  have hs := resTo_surjective hLI
  have hnt := nontrivial_autSub hLI hne
  rcases hshape with h | h | h | h
  · exact Or.inl (lieModel_of_surjective_of_isSimple
      (uc22p22r_lieModel_isSimple_classical (Or.inl rfl) h) (resTo hLI) hs hnt h)
  · exact Or.inr (Or.inl (lieModel_of_surjective_of_isSimple
      (uc22p22r_lieModel_isSimple_twistedB2 h) (resTo hLI) hs hnt h))
  · exact Or.inr (Or.inr (Or.inl (lieModel_of_surjective_of_isSimple
      (uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inl rfl)) h) (resTo hLI) hs hnt h)))
  · exact Or.inr (Or.inr (Or.inr
      (isSU3_of_surjective_central h (resTo hLI) hs (ker_resTo_le_center hq hLI hne) hnt)))

theorem rankOne_case
    (hSz : ∀ (X : Type) [Group X] (f : ℕ), IsSz X f → Nat.card X = CFSG.Open.ordSuzuki (2 ^ f))
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L T P : Subgroup (MulAut W)} {e n : ℕ}
    (hO2 : O2Trivial Y) (hirr : IsIrrOn Y ⊤ ⊥) (hL : IsComponentOf L Y) (hTY : T ≤ Y)
    (hT : IsSylowIn 2 T Y) (hncard : (conjSet L T).ncard ≤ 2)
    (hshape : IsL2 ↥L e ∨ IsSz ↥L e ∨ IsU3 ↥L e ∨ IsSU3 ↥L e)
    (hPL : P ≤ L) (hinf : Hinf P ≠ ⊥) (hnorm : normIn T L ≤ normalizer (P : Set (MulAut W)))
    (hN : NParam (Hinf P) n) (hn : 2 < n)
    {K : Subgroup (MulAut W)} (hK : K = ⨆ t ∈ T, (Hinf P).map (MulAut.conj t).toMonoidHom)
    {W₀ : Subgroup W} (hW₀ : W₀ = ⨆ k ∈ K, (fixV T).map (k : MulAut W).toMonoidHom)
    (hma : E3.mParam Y ≤ E3.aParam (autSub (K ⊔ T) W₀) + 1) (hmY : E3.mParam Y ≤ n + 1)
    (hsum : IsDirSumOver (conjSet L Y) commV) (hfixH : fixV (⨆ X ∈ conjSet L Y, X) = ⊥)
    {I : Subgroup W} (hI : I ∈ irrSet L) (hIfix : I ⊓ fixV L = ⊥)
    (hineq : E3.mParam (autSub Y I) * rk ↥(commV L) ≤ E3.mParam Y * rk ↥I)
    (hsmall : (∃ k : ℕ, IsNaturalClassicalModule (autSub L I) k ∧ (n = k ∨ n = 2 * k)) ∨
      (IsL2 ↥(autSub L I) 3 ∧ n = 3 ∧ E3.mParam (autSub Y I) = 4 ∧
        E3.aParam (autSub Y I) ≤ 1)) :
    (IsL2 ↥L n ∧ BinaryNaturalSL L (commV L) ⊥ 2 n) ∨
      (Even n ∧ IsOmegaMinus ↥L 4 (n / 2) ∧ NatOmegaMinus L (commV L) ⊥ 4 (n / 2)) := by
  classical
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hPeq : P = L := eq_of_rankOne hO2 hL hT hshape hPL hinf hnorm
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have : Finite (MulAut ↥I) :=
    Finite.of_injective (fun f : MulAut ↥I => (f : ↥I → ↥I)) DFunLike.coe_injective
  have hHinf : Hinf P = L := by
    rw [hPeq]
    exact hinf_eq_self hq
  rw [hHinf] at hK hN
  have hLI : L ≤ stabSub I := le_stabSub_of_mem_irrSet hI
  have hne : ¬ L ≤ centSub I := not_le_centSub_of_mem_irrSet hI hIfix
  have hqI : CFSG.Open.IsQuasisimple ↥(autSub L I) := B1Red.isQuasisimple_autSub hLI hq hne
  have hshapeI := shape_autSub hshape hLI hq hne
  have hNI : NParam (autSub L I) n := by
    have h := uc22p21c_Hinf_perfect (autSub L I)
    rw [hinf_eq_self hqI] at h
    exact nParam_of_surjective_central (resTo hLI) (resTo_surjective hLI)
      (ker_resTo_le_center hq hLI hne) h
      ((Subgroup.nontrivial_iff_ne_bot _).mp (nontrivial_autSub hLI hne)) hN
  have hnormI : ∀ y ∈ Y, y ∈ stabSub I → y ∈ normalizer (L : Set (MulAut W)) :=
    fun y hy hyI => mem_normalizer_of_mem_stabSub hsum hI hy hyI
  have hIne : I ≠ ⊥ := WeakClosure81.ne_bot_of_mem_irrSet hI
  have hrkI : 0 < rk ↥I := by
    rw [Nat.pos_iff_ne_zero]
    exact fun h => hIne ((rk_eq_zero_iff hW).mp h)
  have hcinf : commV L ⊓ fixV L = ⊥ := commV_inf_fixV_eq_bot_of_dirSum hL.1 hsum hfixH
  have hIc : I ≤ commV L := by
    rw [commV_eq_commSub, ← hI.1]
    exact commSub_mono le_top le_rfl
  have hKTY : K ⊔ T ≤ Y := iSup_conj_sup_le hL.1 hTY hK
  have hMinv : StableUnder L (W₀ ⊓ commV L) := stableUnder_inf_commV hK hW₀
  have hcommW₀ : ∀ u ∈ commV L, (∀ l ∈ L, l u * u⁻¹ ∈ W₀) →
      ∀ l ∈ L, l u * u⁻¹ ∈ W₀ ⊓ commV L := fun u _ h l hl =>
    ⟨h l hl, Subgroup.subset_closure ⟨l, hl, u, rfl⟩⟩
  rcases hsmall with ⟨k, hnat, hnk⟩ | ⟨hL8, hn3, hm4, ha1⟩
  ·
    have hk2 : 2 ≤ k := by omega
    have hkm : k ≤ E3.mParam (autSub Y I) :=
      le_mParam_autSub_of_natural hW hL hI hIfix hnormI hnat
    rcases natural_of_rankOne hshapeI hk2 hnat with ⟨hL2, hBin⟩ | ⟨hΩ, hNat⟩
    ·
      have hnk' : n = k := nParam_eq_of_isL2 hSz hqI hL2 hNI
      have hs := isSimpleGroup_of_isL2_autSub hshape hLI hq hne hL2
      have hinj := faithful_of_isSimpleGroup hs hLI hne
      have hcI : commV L = I := by
        rcases commV_eq_or_exists_two hW hO2 hirr hL hfixH hsum hI with h | ⟨J, -, -, h2, -⟩
        · exact h
        · exfalso
          have h1 : k * (2 * rk ↥I) ≤ E3.mParam (autSub Y I) * rk ↥(commV L) :=
            Nat.mul_le_mul hkm h2
          have h3 : E3.mParam Y * rk ↥I ≤ (k + 1) * rk ↥I := Nat.mul_le_mul_right _ (by omega)
          have h4 : k * (2 * rk ↥I) ≤ (k + 1) * rk ↥I := h1.trans (hineq.trans h3)
          have h5 : 2 * k ≤ k + 1 := by
            have : (2 * k) * rk ↥I ≤ (k + 1) * rk ↥I := by linarith
            exact Nat.le_of_mul_le_mul_right this hrkI
          omega
      left
      refine ⟨?_, ?_⟩
      · rw [hnk']
        exact LieModel.of_mulEquiv (FFC.resEquiv hLI hinj).symm hL2
      · rw [hnk', hcI]
        exact binaryNaturalSL_of_autSub hLI hinj hBin
    ·
      have hL2' : IsL2 ↥(autSub L I) (2 * k) := isL2_two_mul_of_isOmegaMinus_four (by omega) hΩ
      have hnk' : n = 2 * k := nParam_eq_of_isL2 hSz hqI hL2' hNI
      have hs := isSimpleGroup_of_isL2_autSub hshape hLI hq hne hL2'
      have hinj := faithful_of_isSimpleGroup hs hLI hne
      have hΩL : IsOmegaMinus ↥L 4 k := IsOmegaMinus.of_mulEquiv (FFC.resEquiv hLI hinj).symm hΩ
      have hNatI : NatOmegaMinus L I ⊥ 4 k := natOmegaMinus_of_autSub hLI hinj hNat
      rcases commV_eq_or_exists_two hW hO2 hirr hL hfixH hsum hI with hcI | ⟨J, hJ, hIJ, h2, h3⟩
      · right
        refine ⟨⟨k, by omega⟩, ?_, ?_⟩
        · rw [show n / 2 = k by omega]
          exact hΩL
        · rw [show n / 2 = k by omega, hcI]
          exact hNatI
      · exfalso
        have hlt : rk ↥(commV L) < 3 * rk ↥I := by
          by_contra hge
          push Not at hge
          have h1 : k * (3 * rk ↥I) ≤ E3.mParam (autSub Y I) * rk ↥(commV L) :=
            Nat.mul_le_mul hkm hge
          have h4 : E3.mParam Y * rk ↥I ≤ (2 * k + 1) * rk ↥I := Nat.mul_le_mul_right _ (by omega)
          have h5 : (3 * k) * rk ↥I ≤ (2 * k + 1) * rk ↥I := by
            have := h1.trans (hineq.trans h4)
            linarith
          have := Nat.le_of_mul_le_mul_right h5 hrkI
          omega
        have hcIJ : commV L = I ⊔ J := h3 hlt
        have hJfix : J ⊓ fixV L = ⊥ := by
          rw [eq_bot_iff, ← hcinf]
          exact inf_le_inf_right _ (hcIJ ▸ le_sup_right)
        have hLJ : L ≤ stabSub J := le_stabSub_of_mem_irrSet hJ
        have hneJ : ¬ L ≤ centSub J := not_le_centSub_of_mem_irrSet hJ hJfix
        have hinjJ := faithful_of_isSimpleGroup hs hLJ hneJ
        obtain ⟨g, hgY, hsec⟩ := exists_secIsoOn_of_mem_irrSet hW hO2 hirr hL hfixH hsum hI hJ
        have hg := map_conj_eq_of_secIsoOn hL.1 hsum hI hJ hJfix hgY hsec
        obtain ⟨ψ, hψ⟩ := exists_mulEquiv_autSub_eq_map hg hLI hLJ hsec
        have hNatJ' : NatOmegaMinus (autSub L J) ⊤ ⊥ 4 k := by
          refine natOmegaMinus_of_map_congrHom ψ.symm ?_ hNat
          rw [hψ, Subgroup.map_map, H.LU.congrHom_symm_comp, Subgroup.map_id]
        have hNatJ : NatOmegaMinus L J ⊥ 4 k := natOmegaMinus_of_autSub hLJ hinjJ hNatJ'
        have hrkJ : rk ↥J = rk ↥I := rk_eq_of_mem_irrSet hW hO2 hirr hL hfixH hsum hI hJ
        have hrkc : rk ↥(commV L) = 2 * rk ↥I := by
          have h := rk_sup_add_rk_inf I J
          rw [hIJ, rk_bot, add_zero, hrkJ, ← hcIJ] at h
          omega
        have hmY2 : 2 * E3.mParam (autSub Y I) ≤ E3.mParam Y := by
          rw [hrkc] at hineq
          have : (2 * E3.mParam (autSub Y I)) * rk ↥I ≤ E3.mParam Y * rk ↥I := by linarith
          exact Nat.le_of_mul_le_mul_right this hrkI
        have hMle : W₀ ⊓ commV L ≤ I ⊔ J := hcIJ ▸ inf_le_right
        obtain ⟨M', hM'inv, hMM', hMM'sup, hM'fix⟩ :=
          exists_compl_of_natOmegaMinus_sum hΩL hNatI hNatJ hIJ hMinv hMle
        have hclosed : ∀ u ∈ commV L, (∀ l ∈ L, l u * u⁻¹ ∈ W₀) → u ∈ W₀ := by
          intro u hu h
          have hu' : u ∈ (W₀ ⊓ commV L) ⊔ M' := by
            rw [hMM'sup, ← hcIJ]
            exact hu
          exact (mem_of_forall_mul_inv_mem hMinv hM'inv hMM' hM'fix hu' (hcommW₀ u hu h)).1
        have hpiece : E3.aParam (autSub (K ⊔ T) (W₀ ⊓ commV L)) ≤ k := by
          by_cases hM0 : W₀ ⊓ commV L = ⊥
          · rw [aParam_autSub_eq_zero_of_fix]
            · omega
            · intro x _ u hu
              rw [hM0, Subgroup.mem_bot] at hu
              rw [hu, map_one]
          · exact aParam_autSub_le_of_natOmegaMinus_sum hΩL hNatI hNatJ hIJ hMinv hMle
              fun g hg => mem_normalizer_of_mem_stabSub_of_le_commV hL.1 hTY hK hsum
                inf_le_right hM0 hg.1 hg.2
        have ha := aParam_autSub_le_of_inf_commV hW hL.1 hTY hsum hncard hK hW₀ hclosed
          (by omega) hpiece
        omega
  ·
    exfalso
    have hcI : commV L = I := by
      rcases commV_eq_or_exists_two hW hO2 hirr hL hfixH hsum hI with h | ⟨J, -, -, h2, -⟩
      · exact h
      · exfalso
        rw [hm4] at hineq
        have h4 : E3.mParam Y * rk ↥I ≤ 4 * rk ↥I := Nat.mul_le_mul_right _ (by omega)
        have : 4 * (2 * rk ↥I) ≤ 4 * rk ↥I :=
          (Nat.mul_le_mul_left 4 h2).trans (hineq.trans h4)
        omega
    have hm4Y : 4 ≤ E3.mParam Y := by
      rw [hm4, hcI] at hineq
      exact Nat.le_of_mul_le_mul_right hineq hrkI
    have hirrI : W₀ ⊓ commV L = ⊥ ∨ W₀ ⊓ commV L = I := by
      have h := hI.2.2.2.2 (W₀ ⊓ commV L) hMinv (by rw [hIfix]; exact bot_le)
        (hcI ▸ inf_le_right)
      rwa [hIfix] at h
    have hclosed : ∀ u ∈ commV L, (∀ l ∈ L, l u * u⁻¹ ∈ W₀) → u ∈ W₀ := by
      intro u hu h
      rcases hirrI with h0 | hI'
      · have hu' := mem_of_forall_mul_inv_mem hMinv hI.2.2.1 (by rw [h0]; exact bot_inf_eq _)
          hIfix (show u ∈ W₀ ⊓ commV L ⊔ I by rw [h0, bot_sup_eq]; exact hcI ▸ hu)
          (hcommW₀ u hu h)
        exact hu'.1
      · have hu' : u ∈ W₀ ⊓ commV L := by
          rw [hI', ← hcI]
          exact hu
        exact hu'.1
    have hpiece : E3.aParam (autSub (K ⊔ T) (W₀ ⊓ commV L)) ≤ 1 := by
      rcases hirrI with h0 | hI'
      · rw [aParam_autSub_eq_zero_of_fix]
        · omega
        · intro x _ u hu
          rw [h0, Subgroup.mem_bot] at hu
          rw [hu, map_one]
      · rw [hI']
        exact (E3.aParam_mono (autSub_mono hKTY I)).trans ha1
    have ha := aParam_autSub_le_of_inf_commV hW hL.1 hTY hsum hncard hK hW₀ hclosed le_rfl hpiece
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
