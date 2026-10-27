module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusF4Rank
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusF4Lang
import CFSG.Assembly.ComponentFreeOddCores
import CFSG.LocalAnalysis.StandardType.GGTablePThreeF4Comp
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA.CanonTriL
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple


private theorem q2cF4_inLambda2_C_three {n : ℕ} (hn : 1 ≤ n) :
    LargeEvenInLambda2 (⟨.C, 3, n⟩ : LargeEvenLabel) := by
  refine ⟨hn, by norm_num, ?_⟩
  intro h
  norm_num at h

private theorem q2cF4_labelIso_CA_false {n m : ℕ} :
    ¬ GGLabelIso (⟨.C, 3, n⟩ : LargeEvenLabel) ⟨.A, 2, m⟩ := by
  intro h
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all [LargeEvenLabel.mk.injEq]

private theorem q2cF4T_adjoint_five_false {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2)
    {β : MulAut ↥(adjointGroup .F4 K)}
    (hβmem : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
      ↥(adjointGroup .F4 K))
    (hβ5 : β ^ 5 = 1) (hβ1 : β ≠ 1)
    {J : Subgroup ↥(adjointGroup .F4 K)} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β))
    {m : ℕ} (hm : 2 ≤ m) {K' : Type} [Field K'] [Finite K']
    (hK' : Nat.card K' = 2 ^ m)
    (he : Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 5) K'))) : False := by
  classical
  obtain ⟨h, hh, hβh, hp1, hh1⟩ :=
    exists_inndiag_of_mem_innAutDerived_F4 β hβmem hβ5 hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpℓ : 5 ≠ ringChar K := by rw [hK2]; norm_num
  have hpK : ¬ 5 ∣ Nat.card K := fun h' =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hℓ).1
      (Nat.prime_five.dvd_of_dvd_pow (hK ▸ h')))
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
    exists_setup_prime hℓ f.pos Nat.prime_five (by norm_num) hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hK ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt .F4 5 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp)
      Nat.prime_five (by norm_num)
  have hperf : commutator ↥(adjointGroup .F4 K) = ⊤ := single_edge_perfect .F4 K (by simp)
  obtain ⟨S, a, ι, _hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime (τ := .F4) (Or.inr (Or.inl rfl)) Nat.prime_five
      hpK hp₀ hp₀K hq₀' hmon hperf β h
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hpL : ((5 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne
      Nat.prime_five (by rw [hℓL]; exact hpℓ.symm)
  have hsmall : Tag.F4 = .G2 → 5 ≤ 5 ∨ 4 ≤ S.D.q := fun h => absurd h (by decide)
  have hTame := langSetup_hTame_of_prime S Nat.prime_five hpL hsmall hT hap h1
  obtain ⟨i, hqs, hJR⟩ :=
    components_of_langSetup S Nat.prime_five ι hinj hrange β hconj hT hap h1 hTame hJ
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  have hch : ringChar (AlgebraicClosure K) = 2 := by rw [hℓL, hK2]
  obtain ⟨heK⟩ := he
  let eQ : ↥J ⧸ Subgroup.center ↥J ≃*
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)
  exact q2cF4_lang_not_psl5 S hch hT hap h1 i hqs hm hK' ⟨eQ.symm.trans heK⟩

theorem q2c_F4_five_false {m : ℕ} {lab : LargeEvenLabel} (hlab : lab.tag = .F4) (hm : 2 ≤ m) :
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ u ∈ I, orderOf u = 5 →
      ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) →
        (∀ J' : Subgroup R, CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup u) → J' = J) →
        ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ m →
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin 5) K)) → False) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  have htag : t = .F4 := by simpa using hlab
  subst htag
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K₀, iF, iFin, hK₀, hq⟩ := hQ
  refine ⟨K₀, iF, iFin, hK₀, hq, ?_⟩
  intro u hu huo J hJ huniq K iK iFinK hK he
  letI : Field K₀ := iF
  letI : Finite K₀ := iFin
  set R : Type := LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K₀ false) with hR
  set I : Set (MulAut R) := LargeEvenChevIDImage LargeEvenCartanF4 K₀ _ with hI
  let e : R ≃* ↥(adjointGroup .F4 K₀) := TableBF4.recipeEquiv K₀
  have huI : u ∈ LargeEvenChevIDImage LargeEvenCartanF4 K₀
      (LargeEvenChevH LargeEvenCartanF4 K₀ false) := by
    rw [← hI]
    exact hu
  obtain ⟨g, hg⟩ := TableBF4.idImage_subset_inn K₀ huI
  let β : MulAut ↥(adjointGroup .F4 K₀) := MulAut.congr e u
  have hβconj : β = MulAut.conj (e g) := by
    dsimp [β]
    rw [← hg]
    exact CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e g
  have hβmem : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
      ↥(adjointGroup .F4 K₀) := by
    rw [hβconj]
    exact CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _
      ⟨e g, rfl⟩
  have hβ5 : β ^ 5 = 1 := by
    dsimp [β]
    rw [← map_pow, show u ^ 5 = 1 by rw [← huo]; exact pow_orderOf_eq_one u, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    have hu1 : u = 1 := by
      apply (MulAut.congr e).injective
      have h' : MulAut.congr e u = MulAut.congr e 1 := by
        rw [map_one]
        dsimp [β] at h
        exact h
      exact h'
    rw [hu1, orderOf_one] at huo
    omega
  have hfix : ggAutFixedSubgroup u = fixSubgroup u := Subgroup.ext fun _ => Iff.rfl
  have hJ0 : CFSG.Open.IsComponentOf J (fixSubgroup u) := by
    rw [← hfix]
    exact hJ
  have hJmap : CFSG.Open.IsComponentOf (J.map e.toMonoidHom) (fixSubgroup β) := by
    dsimp [β]
    exact isComponentOf_transport e u hJ0
  have hJZ : Nonempty (↥(J.map e.toMonoidHom) ⧸
      Subgroup.center ↥(J.map e.toMonoidHom) ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin 5) K)) := by
    obtain ⟨heK⟩ := he
    let eJ : ↥J ≃* ↥(J.map e.toMonoidHom) :=
      Subgroup.equivMapOfInjective J e.toMonoidHom e.injective
    exact ⟨(QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)).symm.trans heK⟩
  haveI : CharP K₀ 2 := charP_two_of_card hK₀
  have hK2 : ringChar K₀ = 2 := ringChar.eq K₀ 2
  exact q2cF4T_adjoint_five_false (K' := K) hK2 hβmem hβ5 hβ1 hJmap hm hK hJZ

theorem q2c_F4_three_false {m : ℕ} {lab : LargeEvenLabel} (hlab : lab.tag = .F4) (hm : 2 ≤ m) :
    LargeEvenLabelAll lab (fun R _ I _ => lab.n = 1 →
      ∀ u ∈ I, orderOf u = 3 →
      ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) →
        (∀ J' : Subgroup R, CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup u) → J' = J) →
        ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ m →
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) → False) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  have htag : t = .F4 := by simpa using hlab
  subst htag
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K₀, iF, iFin, hK₀, hq⟩ := hQ
  refine ⟨K₀, iF, iFin, hK₀, hq, ?_⟩
  intro hn u hu huo J hJ huniq K iK iFinK hK he
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hK₀
    have : 2 ≤ Nat.card K₀ := Finite.one_lt_card
    omega
  letI : Field K₀ := iF
  letI : Finite K₀ := iFin
  set R : Type := LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K₀ false) with hR
  set I : Set (MulAut R) := LargeEvenChevIDImage LargeEvenCartanF4 K₀ _ with hI
  haveI : IsSimpleGroup R := by
    have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 (K := K₀)
    haveI : IsSimpleGroup (CFSG.Blueprint.AdjointQuotient .F4 K₀) := hq.2.1
    obtain ⟨eR'⟩ := centerQuot_chevGroup_equiv K₀ .F4
    exact eR'.isSimpleGroup
  have hna : ∃ a b : R, a * b ≠ b * a := by
    obtain ⟨eR'⟩ := centerQuot_chevGroup_equiv K₀ .F4
    have hZ : Subgroup.center ↥(adjointGroup .F4 K₀) = ⊥ := center_adjointGroup_eq_bot
    let eZ : CFSG.Blueprint.AdjointQuotient .F4 K₀ ≃* ↥(adjointGroup .F4 K₀) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    let e : R ≃* ↥(adjointGroup .F4 K₀) := eR'.trans eZ
    exact exists_ne_comm_of_mulEquiv_adjointGroup_F4 (k := K₀) (H := R)
      (by haveI : CharP K₀ 2 := charP_two_of_card hK₀
          exact CharP.cast_eq_zero K₀ 2) e
  have hcomm : commutator R = ⊤ := CFSG.Assembly.Dichotomy.commutator_eq_top_of_isSimpleGroup hna
  have hZbot : Subgroup.center R = ⊥ := center_eq_bot_of_isSimpleGroup_of_nonabelian hna
  let θ : R ⧸ Subgroup.center R ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot
  have hθ_mk : ∀ x : R, θ (QuotientGroup.mk x) = x := by
    intro x
    change QuotientGroup.quotientBot
      (QuotientGroup.quotientMulEquivOfEq hZbot (QuotientGroup.mk x)) = x
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hθu : ggInducedAut θ u = u := by
    ext x
    have h := ggInducedAut_apply θ u x
    rw [hθ_mk x] at h
    rw [h, hθ_mk (u x)]
  have hlamF4 : LargeEvenInLambda2 (⟨.F4, 0, n⟩ : LargeEvenLabel) := by
    refine ⟨hn1, ?_⟩
    rfl
  have hmark : LargeEvenMarking R
      (fun lab' _ _ I' _ θ' => lab'.tag = .F4 ∧ ggInducedAut θ' u ∈ I') := by
    refine ⟨hcomm, ⟨⟨.F4, 0, n⟩, hlamF4, ?_⟩⟩
    dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeChevalley]
    refine ⟨K₀, iF, iFin, hK₀, ?_⟩
    refine ⟨inferInstance, hna, θ, rfl, ?_⟩
    rw [hθu]
    exact hu
  have hdat : GGTorsionDatum (fun lab => lab.tag = .F4) 3 u J := by
    refine ⟨Nat.prime_three, by norm_num, ?_, ?_,
      CFSG.Assembly.isComponentOf_iff_open.mpr hJ, hmark⟩
    · rw [← huo]
      exact pow_orderOf_eq_one u
    · intro h1
      rw [h1, orderOf_one] at huo
      omega
  haveI : Finite R := by
    obtain ⟨e0⟩ := centerQuot_chevGroup_equiv K₀ .F4
    exact Finite.of_equiv _ e0.symm.toEquiv
  have hF4 := ggTorsion_f4_comp hdat
  obtain ⟨-, labX, hlabX, hrawX⟩ := hF4
  have hcompX : GGCompF4BC u J labX.n := by
    rcases largeEvenRawDatum_exists hrawX with ⟨R, hR, I, F, hQX⟩
    obtain ⟨θ, -, hcomp⟩ := hQX.2.2
    exact hcomp
  rcases hcompX with ⟨J', hJ'comp, hJ'ne⟩ | hC3
  · exact absurd (huniq J' (isComponentOf_iff_open.mp hJ'comp)) hJ'ne
  · have hlamC : LargeEvenInLambda2 (⟨.C, 3, labX.n⟩ : LargeEvenLabel) :=
      q2cF4_inLambda2_C_three hlabX.1
    have hlamA : LargeEvenInLambda2 (⟨.A, 2, m⟩ : LargeEvenLabel) := by
      refine ⟨le_trans (by norm_num) hm, by norm_num, ?_⟩
      intro h
      norm_num at h
    have hHasA : GGHasLabel (⟨.A, 2, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
      unfold GGHasLabel
      dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear]
      refine ⟨K, iK, iFinK, hK, ?_⟩
      exact he
    have hIso := ggLabelRigidInput_holds (⟨.C, 3, labX.n⟩ : LargeEvenLabel)
      (⟨.A, 2, m⟩ : LargeEvenLabel)
      (↥J ⧸ Subgroup.center ↥J) hlamC hlamA hC3 hHasA
    exact (q2cF4_labelIso_CA_false hIso).elim

theorem q2c_rLevel_F4 :
    Q2CensusRLevel (fun lab => lab.tag = .F4) (fun _ => False) := by
  intro p d m lab hp hp2 hΛ hsplit hS hd hm hpd hpm Q hQ
  have hall := largeEvenLabelAll_and (q2c_F4_rank hS hp hp2 hsplit hpd)
    (largeEvenLabelAll_and (q2c_F4_five_false (m := m) hS hm)
      (q2c_F4_three_false (m := m) hS hm))
  refine largeEvenRawDatum_mono ?_ (hall Q hQ)
  rintro R _ I F ⟨hq, hrank, hfive, hthree⟩
  refine ⟨hq, fun A hA hAI hbig _ hlo hup u hu huo J hJ huniq _ K _ _ hK he => ?_⟩
  exfalso
  rcases hrank A hA hAI hbig hlo hup with ⟨hp5, hd5⟩ | ⟨hn1, hp3, hd3⟩
  · subst hp5
    subst hd5
    exact hfive u (hAI u hu) huo J hJ huniq K hK he
  · subst hp3
    subst hd3
    exact hthree hn1 u (hAI u hu) huo J hJ huniq K hK he

end CFSG.StandardType
