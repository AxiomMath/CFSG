module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusLinear
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusFieldTwo
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusOmegaSel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusOmegaNonsplit
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1DSmall
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTypeDet
import CFSG.RankThree.GF2n.Stroth80.Sec1110CMLmConsumer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial


private theorem q2cOP_labelAll_D3_A3 {n : ℕ} {P P' : LargeEvenRawCont}
    (himp : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P' R I F → P R I F)
    (h : LargeEvenLabelAll (⟨.A, 3, n⟩ : LargeEvenLabel) P') :
    LargeEvenLabelAll (⟨.D, 3, n⟩ : LargeEvenLabel) P := by
  intro Q hQ
  have hQ' : LargeEvenRawDatum (⟨.A, 3, n⟩ : LargeEvenLabel) Q :=
    (Q1DSmall.rawDatum_D3_iff_A3 n Q).1 hQ
  have hres := h Q hQ'
  refine largeEvenRawDatum_mono ?_ ((Q1DSmall.rawDatum_D3_iff_A3 n _).2 hres)
  rintro R _ I F ⟨hQr, hP'⟩
  exact ⟨hQr, himp R I F hP'⟩

private theorem q2cOP_rank_three :
    Q2CensusRLevel (fun lab => lab.tag = .D ∧ lab.rank = 3)
      (fun kind => kind = .orthogonalPlus) := by
  intro p d m lab hp hp2 hΛ hsplit hS hd hm hpd hpm Q hQ
  obtain ⟨htag, hrank⟩ := hS
  obtain ⟨t, l, n⟩ := lab
  dsimp only [LargeEvenLabel.tag, LargeEvenLabel.rank] at htag hrank
  subst htag
  subst hrank
  by_cases h2n : 2 ≤ n
  · have hΛ' : LargeEvenInLambda2 (⟨.A, 3, n⟩ : LargeEvenLabel) :=
      ⟨hΛ.1, by norm_num, fun h => by omega⟩
    have hsplit' : LargeEvenSplit p (⟨.A, 3, n⟩ : LargeEvenLabel) := by
      rcases hsplit with ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | ⟨hn1, hp3'⟩
      · exact Or.inl ⟨trivial, h⟩
      · exact absurd trivial h
      · rcases h with h | h <;> cases h
      · exact Or.inr (Or.inr (Or.inr ⟨hn1, hp3'⟩))
    have hlin := q2c_rLevel_linear p d m (⟨.A, 3, n⟩ : LargeEvenLabel) hp hp2 hΛ' hsplit'
      ⟨rfl, h2n⟩ hd hm hpd hpm
    refine q2cOP_labelAll_D3_A3 ?_ hlin Q hQ
    intro R _ I F hP' A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K _ _ hK hne
    obtain ⟨kind, hk, hfit⟩ :=
      hP' A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K hK hne
    subst hk
    rw [q2RowFits.eq_def] at hfit
    obtain ⟨hpp, hp2', hpd', hpm', -, hrank', hQ'⟩ := hfit
    exact ⟨.orthogonalPlus, rfl, by
      rw [q2RowFits.eq_def]
      exact ⟨hpp, hp2', hpd', hpm', rfl, hrank', hQ'⟩⟩
  · have hn1 : n = 1 := le_antisymm (by omega) hΛ.1
    subst hn1
    have hp3 : p = 3 := by
      rcases hsplit with ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
      · norm_num at h; exact absurd h hp.ne_one
      · exact absurd trivial h
      · rcases h with h | h <;> cases h
      · exact h
    have hΛ' : LargeEvenInLambda2 (⟨.A, 3, 1⟩ : LargeEvenLabel) :=
      ⟨le_refl 1, by norm_num, fun h => by simp at h⟩
    have hsplit' : LargeEvenSplit p (⟨.A, 3, 1⟩ : LargeEvenLabel) :=
      Or.inr (Or.inr (Or.inr ⟨rfl, hp3⟩))
    have hf2 := q2c_rLevel_fieldTwo p d m (⟨.A, 3, 1⟩ : LargeEvenLabel) hp hp2 hΛ' hsplit'
      ⟨rfl, rfl⟩ hd hm hpd hpm
    refine q2cOP_labelAll_D3_A3 ?_ hf2 Q hQ
    intro R _ I F hP' A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K _ _ hK hne
    obtain ⟨kind, hk, hfit⟩ :=
      hP' A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K hK hne
    subst hk
    rw [q2RowFits.eq_def] at hfit
    obtain ⟨-, -, -, -, -, -, hrankor, -, -⟩ := hfit
    exfalso
    rcases hrankor with h | h <;> (simp at h; omega)

private theorem q2cOP_torusLift {p : ℕ} {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (htag : lab.tag = .D) (h4 : 4 ≤ lab.rank)
    (hp : p.Prime) (hp2 : p ≠ 2) (hsplit : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab (fun R _ _ _ => 2 ≤ lab.n → GGTorusLift p lab.rank R) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only [LargeEvenLabel.tag, LargeEvenLabel.rank] at htag h4
  subst htag
  simp only [LargeEvenRawDatum, if_neg (show ¬ l = 3 by omega)] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  refine ⟨K, i1, i2, hK, hQ', ?_⟩
  intro h2n
  have hpq : p ∣ 2 ^ n - 1 := by
    rcases hsplit with ⟨-, hpq⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | ⟨hn1, -⟩
    · exact hpq
    · exact absurd trivial h
    · rcases h with h | h <;> cases h
    · have hn1' : n = 1 := hn1
      exact absurd hn1' (by omega)
  haveI : CharP K 2 := charP_two_of_card hK
  have hpqK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
  exact TableBSymp.ggTorusLift_omegaPlus (K := K) (m := l) hp hp2 hpqK (by omega)

private theorem q2cOP_natural_component
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
    (Q : (ι → K) → K) (Φ : QuadraticForm K (ι → K)) (hΦfun : ⇑Φ = Q)
    (hscal : (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q) = ⊥)
    (hconj : Function.Injective
      (MulAut.conj : LargeEvenProj (LargeEvenOmega Q) →*
        MulAut (LargeEvenProj (LargeEvenOmega Q))))
    {p d m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 2 ≤ m)
    (A : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega Q))))
    (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, a ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega Q)))
    (u : MulAut (LargeEvenProj (LargeEvenOmega Q))) (hu : u ∈ A) (huo : orderOf u = p)
    (J : Subgroup (LargeEvenProj (LargeEvenOmega Q)))
    (hJ : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u))
    (K' : Type) [Field K'] [Finite K'] (hK' : Nat.card K' = 2 ^ m)
    (hne : Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K'))) :
    ∃ (s : ↥(LargeEvenOmega ⇑Φ)) (C : Subgroup ↥(LargeEvenOmega ⇑Φ)),
      orderOf s = p ∧ CFSG.Assembly.IsComponentOf C (Subgroup.centralizer {s}) ∧
      Nonempty (↥C ⧸ Subgroup.center ↥C ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin d) K')) := by
  subst Q
  let e : LargeEvenProj (LargeEvenOmega ⇑Φ) ≃* ↥(LargeEvenOmega ⇑Φ) :=
    (TableBOrth.projMkEquiv hscal).symm
  have hAinn : (A : Set (MulAut (LargeEvenProj (LargeEvenOmega ⇑Φ)))) ⊆
      Set.range (MulAut.conj : LargeEvenProj (LargeEvenOmega ⇑Φ) →*
        MulAut (LargeEvenProj (LargeEvenOmega ⇑Φ))) := hAI
  obtain ⟨s, hs⟩ := hAinn hu
  have hord : orderOf u = orderOf s := by
    rw [← hs]; exact orderOf_injective _ hconj s
  have hfix : ggAutFixedSubgroup u = Subgroup.centralizer ({s} : Set _) := by
    rw [← hs]; exact ggAutFixedSubgroup_mulAut_conj s
  let C : Subgroup ↥(LargeEvenOmega ⇑Φ) := J.map e.toMonoidHom
  have hJO : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({s} : Set (LargeEvenProj (LargeEvenOmega ⇑Φ)))) := by
    rw [← hfix]
    exact CFSG.Assembly.isComponentOf_iff_open.mpr hJ
  have hC : CFSG.Assembly.IsComponentOf C
      (Subgroup.centralizer ({e s} : Set ↥(LargeEvenOmega ⇑Φ))) := by
    have hmap : CFSG.Assembly.IsComponentOf (J.map e.toMonoidHom)
        ((Subgroup.centralizer ({s} : Set (LargeEvenProj (LargeEvenOmega ⇑Φ)))).map
          e.toMonoidHom) :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
        (f := e.toMonoidHom) e.injective).mpr hJO
    have hcentmap : (Subgroup.centralizer
        ({s} : Set (LargeEvenProj (LargeEvenOmega ⇑Φ)))).map e.toMonoidHom =
        Subgroup.centralizer ({e s} : Set ↥(LargeEvenOmega ⇑Φ)) :=
      CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv e s
    rw [hcentmap] at hmap
    exact hmap
  have hesord : orderOf (e s) = p := by
    change orderOf (e.toMonoidHom s) = p
    rw [orderOf_injective e.toMonoidHom e.injective s, ← hord, huo]
  have hcenter : (Subgroup.center ↥J).map (e.subgroupMap J).toMonoidHom =
      Subgroup.center ↥C := Subgroup.map_center_eq (e.subgroupMap J)
  let eQ : (↥J ⧸ Subgroup.center ↥J) ≃* (↥C ⧸ Subgroup.center ↥C) :=
    QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥C) (e.subgroupMap J) hcenter
  have hneC : Nonempty (↥C ⧸ Subgroup.center ↥C ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K')) := ⟨eQ.symm.trans hne.some⟩
  exact ⟨e s, C, hesord, hC, hneC⟩

theorem q2cOP_block_structure {p d m : ℕ} {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (htag : lab.tag = .D) (h4 : 4 ≤ lab.rank)
    (hp : p.Prime) (hp2 : p ≠ 2) (hsplit : LargeEvenSplit p lab) (hpd : p ∣ d) (hm : 2 ≤ m) :
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ A : Subgroup (MulAut R), IsElemAbelian p A → (∀ a ∈ A, a ∈ I) →
      (∀ r : ℕ, GGTorusLift p r R → p ^ r ≤ Nat.card A) →
      p ^ 3 ≤ Nat.card A → p ^ (d - 1) ≤ Nat.card A → Nat.card A ≤ p ^ d →
      ∀ u ∈ A, orderOf u = p →
      ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) →
        (∀ J' : Subgroup R, CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup u) → J' = J) →
        (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) →
        ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ m →
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin d) K)) →
          (2 ≤ lab.n →
            ∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F),
              Nat.card F = 2 ^ lab.n ∧ 3 ≤ a ∧ a ≤ lab.rank ∧
              Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
                LargeEvenProj (LargeEvenSLGroup (Fin a) F)))
          ∧ (lab.n = 1 → False)) := by
  intro P₀ hP₀
  obtain ⟨tag, l, n⟩ := lab
  dsimp only [LargeEvenLabel.tag, LargeEvenLabel.rank] at htag h4
  subst htag
  simp only [LargeEvenRawDatum, if_neg (show ¬ l = 3 by omega)] at hP₀ ⊢
  obtain ⟨K, iK, iFinK, hK, hP₀'⟩ := hP₀
  refine ⟨K, iK, iFinK, hK, hP₀', ?_⟩
  intro A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K' iK' iFinK' hK' hne
  haveI : CharP K 2 := charP_two_of_card hK
  have hd : 3 ≤ d := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans hup)
  have hscal : (LargeEvenScalars (Fin l ⊕ Fin l) K).subgroupOf
      (LargeEvenOmega (LargeEvenQPlus K l)) = ⊥ :=
    TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := K) (m := l) (by omega)
  have hZΩ : Subgroup.center ↥(LargeEvenOmega (LargeEvenQPlus K l)) = ⊥ :=
    CFSG.RankThree.GF2n.Stroth80.center_statedOmega_quadPlus_eq_bot (m := l) (by omega)
  have hZR : Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K l))) = ⊥ := by
    let e0 := TableBOrth.projMkEquiv (Q := LargeEvenQPlus K l) hscal
    have h := Subgroup.map_center_eq e0
    rw [hZΩ, Subgroup.map_bot] at h
    exact h.symm
  have hconj : Function.Injective
      (MulAut.conj : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K l)) →*
        MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K l)))) :=
    mulAut_conj_injective hZR
  obtain ⟨s, C, hs, hC, hneC⟩ := q2cOP_natural_component
    (Q := LargeEvenQPlus K l) (Φ := TableBOrth.qPlusForm K l)
    (TableBOrth.coe_qPlusForm l) hscal hconj hp hp2 hm A hA hAI u hu huo J hJ K' hK' hne
  refine ⟨fun h2n => ?_, fun hn1 => ?_⟩
  · have hpK : p ∣ Nat.card K - 1 := by
      rcases hsplit with hh | hh | hh | hh
      · rw [hK]; exact hh.2
      · exact absurd trivial hh.1
      · rcases hh.1 with h' | h' <;> cases h'
      · obtain ⟨hn1, -⟩ := hh
        have hn1' : n = 1 := hn1
        exfalso
        omega
    have h8 : 8 ≤ Fintype.card (Fin l ⊕ Fin l) := by simp; omega
    obtain ⟨hcard, hdle⟩ := q2cOS_selected_block (Φ := TableBOrth.qPlusForm K l)
      (TableBOrth.nondegenerate_qPlusForm l) h8 hp hp2 hd hpd hpK hm hK'
      (fun W hW => TableBOrth.finrank_le_of_singular_qPlus W hW) s hs C hC hneC.some
    haveI : Fintype K' := Fintype.ofFinite K'
    haveI : Fintype K := Fintype.ofFinite K
    have hcardFF : Fintype.card K' = Fintype.card K := by
      simpa [Nat.card_eq_fintype_card] using hcard
    let τ : K' ≃+* K := FiniteField.ringEquivOfCardEq hcardFF
    let pslCongr : LargeEvenProj (LargeEvenSLGroup (Fin d) K') ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin d) K) :=
      (TypeA.recipeEquiv d K').trans
        ((kgLangS1A_pslRingCongr d (by omega) τ).trans (TypeA.recipeEquiv d K).symm)
    exact ⟨d, K, iK, iFinK, hK, hd, hdle, ⟨hne.some.trans pslCongr⟩⟩
  · have hn1' : n = 1 := hn1
    have hp3 : p = 3 := by
      rcases hsplit with hh | hh | hh | hh
      · exact absurd (Nat.dvd_one.mp (by simpa [hn1'] using hh.2)) hp.ne_one
      · exact absurd trivial hh.1
      · rcases hh.1 with h' | h' <;> cases h'
      · exact hh.2
    have hK2 : Nat.card K = 2 := by norm_num [hK, hn1']
    have hpF : p ∣ Nat.card K + 1 := by norm_num [hp3, hK2]
    have h8 : 8 ≤ Fintype.card (Fin l ⊕ Fin l) := by simp; omega
    exact (q2cON_nonsplit (Φ := TableBOrth.qPlusForm K l)
      (TableBOrth.nondegenerate_qPlusForm l) h8 hp hp2 hpF hd hpd hm hK' s hs C hC
      hneC.some).elim

private theorem q2cOP_rank_ge_four :
    Q2CensusRLevel (fun lab => lab.tag = .D ∧ 4 ≤ lab.rank)
      (fun kind => kind = .orthogonalPlus) := by
  intro p d m lab hp hp2 hΛ hsplit hS hd hm hpd hpm Q hQ
  obtain ⟨htag, h4⟩ := hS
  have hstruct := q2cOP_block_structure (p := p) (d := d) (m := m) hΛ htag h4 hp hp2 hsplit hpd hm
  have htor := q2cOP_torusLift (p := p) hΛ htag h4 hp hp2 hsplit
  have hall := largeEvenLabelAll_and hstruct htor
  refine largeEvenRawDatum_mono ?_ (hall Q hQ)
  rintro R _ I F ⟨hq, hstruct', htor'⟩
  refine ⟨hq, fun A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K _ _ hK hne => ?_⟩
  have hne' : ↥J ⧸ Subgroup.center ↥J ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K) := hne.some
  have hconj := hstruct' A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K hK hne
  by_cases h2n : 2 ≤ lab.n
  · obtain ⟨a, F, iF, iFin, hF, ha3, hale, hJiso⟩ := hconj.1 h2n
    obtain ⟨hJiso'⟩ := hJiso
    have hψ : LinearFlag.projectiveSL d K ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin a) F) :=
      (TypeA.recipeEquiv d K).symm.trans (hne'.symm.trans hJiso')
    obtain ⟨hda, hcardKF⟩ :=
      kgLangS1A_psl_typeDet (d := d) (d₁ := a) (m := m) (F₀ := K) (E := F)
        hd hm hK hψ
    have hlift : GGTorusLift p lab.rank R := htor' h2n
    have hpow : p ^ lab.rank ≤ Nat.card A := hbig lab.rank hlift
    have hrank_le : lab.rank ≤ d :=
      (Nat.pow_le_pow_iff_right hp.one_lt).mp (hpow.trans hup)
    have hd_le : d ≤ lab.rank := by rw [← hda]; exact hale
    have hrank_eq : lab.rank = d := le_antisymm hrank_le hd_le
    have hfield : 2 ^ m = 2 ^ lab.n := by rw [← hK, ← hcardKF, hF]
    exact ⟨.orthogonalPlus, rfl, hp, hp2, hpd, hpm, htag, hrank_eq, hfield⟩
  · exact (hconj.2 (le_antisymm (by omega) hΛ.1)).elim

theorem q2c_rLevel_orthogonalPlus :
    Q2CensusRLevel (fun lab => lab.tag = .D) (fun kind => kind = .orthogonalPlus) := by
  refine Q2CensusRLevel.mono ?_ (fun kind hk => hk.elim id id)
    (Q2CensusRLevel.or q2cOP_rank_three q2cOP_rank_ge_four)
  intro lab hΛ hS
  have h3 : 3 ≤ lab.rank := by
    have h := hΛ
    simp only [LargeEvenInLambda2, hS] at h
    exact h.2
  by_cases h : lab.rank = 3
  · exact Or.inl ⟨hS, h⟩
  · exact Or.inr ⟨hS, by omega⟩

end CFSG.StandardType
