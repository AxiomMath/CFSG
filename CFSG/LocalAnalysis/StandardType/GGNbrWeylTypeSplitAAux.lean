module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBWeyl
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBRefl
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGResIICell
public import CFSG.LocalAnalysis.StandardType.GGTDAutomizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification TypeA

private theorem ggWTSA_permCongr_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (a b : α) :
    Equiv.permCongrHom e (Equiv.swap a b) = Equiv.swap (e a) (e b) := by
  ext x
  rw [Equiv.permCongrHom_coe, Equiv.permCongr_apply]
  by_cases hxa : x = e a
  · subst hxa
    simp
  · by_cases hxb : x = e b
    · subst hxb
      simp
    · have ha : e.symm x ≠ a := fun h => hxa (by rw [← h, Equiv.apply_symm_apply])
      have hb : e.symm x ≠ b := fun h => hxb (by rw [← h, Equiv.apply_symm_apply])
      rw [Equiv.swap_apply_of_ne_of_ne ha hb, Equiv.swap_apply_of_ne_of_ne hxa hxb,
        Equiv.apply_symm_apply]

theorem ggWTSA_ggTorusWeylTypeW_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (e : R ≃* R')
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTorusWeylTypeW p r R' I') :
    GGTorusWeylTypeW p r R I := by
  intro L' _ _ ψ A hA
  exact h L' (e.toMonoidHom.comp ψ) A (hA.mulEquiv e hI)

theorem ggWTSA_ggTorusWeylTypeW_PSL {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) :
    GGTorusWeylTypeW p (d - 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ A hA
  have hp2 : p ≠ 2 := by
    rintro rfl
    have := Fintype.ofFinite K
    have h0 : ((Fintype.card K : ℕ) : K) = 0 := by simp
    have h2 : 2 ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff K 2 _).mp h0
    have h1 : 0 < Nat.card K := Nat.card_pos
    omega
  obtain ⟨φ', hφ's, hφ'ker, hdiag⟩ :=
    exists_actsDiag_model_of_tbGroup hp hpK hd le_rfl hA
  have hN : ∀ σ, NbrInnerWeylA.permConj φ' σ ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun σ => TypeANbrDvd.permConj_mem_normalizer_of_selfCent hφ's hφ'ker hA.2.2.2.1.2
      hA.2.2.2.2.2.2.2 hdiag σ
  have hrange : (TypeANbrDvd.permAut φ' A hN).range =
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
    (TypeANbrDvd.ggAutomizer_eq_range_permAut hp hp2 hpK hφ's hφ'ker hA.2.2.2.1
      hA.2.2.2.2.2.2.2 hdiag hN).symm
  have hinj : Function.Injective (TypeANbrDvd.permAut φ' A hN) :=
    TypeANbrDvd.permAut_injective hp hp2 hpK hd hφ's hφ'ker hA.2.2.2.1
      hA.2.2.2.2.2.2.2 hdiag hN
  obtain ⟨e0, he0⟩ := ggCoxeterA_mulEquivPerm (d - 1)
  let hc : (d - 1) + 1 = d := by omega
  let pc : Equiv.Perm (Fin ((d - 1) + 1)) ≃* Equiv.Perm (Fin d) :=
    Equiv.permCongrHom (finCongr hc)
  let eσ : Equiv.Perm (Fin d) ≃* ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let f : (CoxeterMatrix.A (d - 1)).Group ≃*
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
    e0.trans (pc.trans eσ)
  have heσ : ∀ σ : Equiv.Perm (Fin d),
      ((eσ σ : ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) : MulAut ↥A) =
        TypeANbrDvd.permAut φ' A hN σ := by
    intro σ
    simp [eσ, MonoidHom.ofInjective_apply]
  have hcard : Nat.card ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ≠ 12 := by
    have hfac : Nat.card ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) =
        Nat.factorial d := by
      rw [← Nat.card_congr eσ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
    have h24 : 24 ≤ Nat.factorial d := by
      have h := Nat.factorial_le (by omega : 4 ≤ d)
      norm_num at h ⊢
      exact h
    omega
  refine ⟨Fin (d - 1), CoxeterMatrix.A (d - 1), f, ggResII_isWeyl_A (by omega), hcard, ?_⟩
  intro k
  have hpc : pc (Equiv.swap k.castSucc k.succ) =
      Equiv.swap (finCongr hc k.castSucc) (finCongr hc k.succ) :=
    ggWTSA_permCongr_swap (finCongr hc) k.castSucc k.succ
  have hfin : finCongr hc k.castSucc ≠ finCongr hc k.succ := fun h =>
    ne_of_lt (Fin.castSucc_lt_succ (i := k)) ((finCongr hc).injective h)
  have hsimple : ((f ((CoxeterMatrix.A (d - 1)).simple k) :
        ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) : MulAut ↥A) =
      TypeANbrDvd.permAut φ' A hN (Equiv.swap (finCongr hc k.castSucc) (finCongr hc k.succ)) := by
    simp only [f, MulEquiv.trans_apply, he0, hpc, heσ]
  rw [hsimple]
  exact TypeANbrDvd.permAut_swap_mem_reflSet hp hp2 hpK (by omega) hφ's hφ'ker hA.2.2.2.1
    hA.2.2.2.2.2.2.2 hdiag hN hfin

theorem ggWTSA_recipeLinear_weylTypeW {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1)
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
      ggWTSA_ggTorusWeylTypeW_of_mulEquiv (TypeA.recipeEquiv d K) hI
        (fun L' _ _ ψ A hA =>
          absurd hA (not_ggTorusTBGroup_small hp hp2 hpK (by omega) hd3))⟩
  · exact ⟨d - 2, TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv d K)
        (TypeA.ggTorusLift_sub_two hp hpK (by omega) (slHasSections_of_four_le hp hpK hd4)),
      ggWTSA_ggTorusWeylTypeW_of_mulEquiv (TypeA.recipeEquiv d K) hI
        (ggWTSA_ggTorusWeylTypeW_PSL hp hpK hd4)⟩

end CFSG.StandardType

end
