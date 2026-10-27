module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBOrthPlus

import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBRefl
import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBAutCard
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.GGTorusWeylTypeEven
import CFSG.LocalAnalysis.StandardType.GGTorusWeylTypePerm
import CFSG.LocalAnalysis.StandardType.GGTDAutomizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private lemma ggWTSD_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

private theorem ggWTSD_ggTorusWeylTypeW_PSL {d p : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) :
    GGTorusWeylTypeW p (d - 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  have hp2 : p ≠ 2 := by
    rintro rfl
    have := Fintype.ofFinite K
    have h0 : ((Fintype.card K : ℕ) : K) = 0 := by simp
    have h2 : 2 ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff K 2 _).mp h0
    have h1 : 0 < Nat.card K := Nat.card_pos
    omega
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  intro L' _ _ ψ A hA
  obtain ⟨φ', hφ's, hφ'ker, hdiag⟩ :=
    exists_actsDiag_model_of_tbGroup hp hpK (by omega : 4 ≤ n + 1) le_rfl hA
  have hAI : IsElemAbelian p A := hA.2.2.2.1
  have hsc : GGTorusSelfCent p A := hA.2.2.2.2.2.2.2
  have hN : ∀ σ : Equiv.Perm (Fin (n + 1)),
      NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun σ => TypeANbrDvd.permConj_mem_normalizer_of_selfCent hφ's hφ'ker hAI.2 hsc hdiag σ
  have hAut : (TypeANbrDvd.permAut φ' A hN).range =
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
    (TypeANbrDvd.ggAutomizer_eq_range_permAut hp hp2 hpK hφ's hφ'ker hAI hsc hdiag hN).symm
  have hinj : Function.Injective (TypeANbrDvd.permAut φ' A hN) :=
    TypeANbrDvd.permAut_injective hp hp2 hpK (by omega : 4 ≤ n + 1) hφ's hφ'ker hAI hsc hdiag hN
  let eΦ : Equiv.Perm (Fin (n + 1)) ≃*
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hAut)
  obtain ⟨e0, he0⟩ := ggCoxeterA_mulEquivPerm n
  let f : (CoxeterMatrix.A n).Group ≃*
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) := e0.trans eΦ
  have hgen : ∀ σ : Equiv.Perm (Fin (n + 1)),
      ((eΦ σ : ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) : MulAut ↥A) =
        TypeANbrDvd.permAut φ' A hN σ := by
    intro σ
    dsimp only [eΦ]
    simp only [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  have hcard : Nat.card
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = (n + 1).factorial := by
    rw [← Nat.card_congr f.toEquiv, Nat.card_congr e0.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
  have hcard12 : Nat.card
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ≠ 12 := by
    rw [hcard]
    have h4 : 4 ≤ n + 1 := by omega
    have hf : 24 ≤ (n + 1).factorial := by
      have := Nat.factorial_le h4
      norm_num at this
      exact this
    omega
  refine ⟨Fin n, CoxeterMatrix.A n, f, ?_, hcard12, ?_⟩
  · refine Or.inl ⟨n, Equiv.refl (Fin n), by omega, Or.inl ?_⟩
    exact (ggWTSD_reindex_refl (CoxeterMatrix.A n)).symm
  · intro k
    have hfk : (f ((CoxeterMatrix.A n).simple k) :
        ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) =
        eΦ (Equiv.swap k.castSucc k.succ) := by
      dsimp only [f]
      rw [MulEquiv.trans_apply, he0 k]
    rw [hfk, hgen (Equiv.swap k.castSucc k.succ)]
    exact TypeANbrDvd.permAut_swap_mem_reflSet hp hp2 hpK (by omega : 3 ≤ n + 1)
      hφ's hφ'ker hAI hsc hdiag hN (ne_of_lt (Fin.castSucc_lt_succ (i := k)))

private theorem ggWTSD_ggTorusWeylTypeW_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (e : R ≃* R')
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTorusWeylTypeW p r R' I') :
    GGTorusWeylTypeW p r R I := by
  intro L' _ _ ψ A hA
  exact h L' (e.toMonoidHom.comp ψ) A (hA.mulEquiv e hI)

private theorem ggWTSD_recipeLinear_weylTypeW {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1)
    (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (TypeA.recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    TypeA.congr_recipeEquiv_mem hφ
  rcases (show d ≤ 3 ∨ 4 ≤ d by omega) with hd3 | hd4
  · exact ⟨0, TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv d K)
        (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL hd)),
      ggWTSD_ggTorusWeylTypeW_of_mulEquiv (TypeA.recipeEquiv d K) hI
        (fun L' _ _ ψ A hA =>
          absurd hA (not_ggTorusTBGroup_small hp hp2 hpK (by omega) hd3))⟩
  · exact ⟨d - 2, TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv d K)
        (TypeA.ggTorusLift_sub_two hp hpK (by omega) (slHasSections_of_four_le hp hpK hd4)),
      ggWTSD_ggTorusWeylTypeW_of_mulEquiv (TypeA.recipeEquiv d K) hI
        (ggWTSD_ggTorusWeylTypeW_PSL hp hpK hd4)⟩

private theorem ggWTSD_recipeOmegaPlus_weylTypeW
    {l n p : ℕ} (hp : p.Prime)
    (hn : 1 ≤ n) (hpn : p ∣ 2 ^ n - 1) (hl : 4 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l,
    TableBSymp.ggTorusLift_omegaPlus hp hp2 hpK (by omega),
    ggTorusWeylTypeW_of_evenSignedPermEltSC hp hp2 (fun _ h => h) hZ hcp
      (fun k hk => by omega)
      (ggOrthEvenTorusInput_holds.1 K l p hl hp (Or.inl hpK))⟩

theorem ggNbrTableBWeylTypeSplitOn_typeD :
    GGNbrTableBWeylTypeSplitOn fun _ lab => lab.tag = .D := by
  rintro p hp hp2 ⟨tag, l, n⟩ hlab htag - hsp Q hQ
  dsimp only at htag
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hl3 : 3 ≤ l := hlab.2
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h3
  · exact ggWTSD_recipeLinear_weylTypeW (d := 4) (N := 2 ^ n) hp hsp.2.2 ⟨n, rfl⟩
      (by norm_num) hQ
  · exact ggWTSD_recipeOmegaPlus_weylTypeW hp hn hsp.2.2 (by omega) hQ

end CFSG.StandardType

end
