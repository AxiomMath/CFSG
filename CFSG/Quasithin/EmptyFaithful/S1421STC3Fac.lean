module

public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.EmptyFaithful.S1421Hyp111
public import CFSG.Quasithin.EmptyFaithful.S1421L11

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem omegaOneCenterOf_ne_bot_of_isPGroup {P : Subgroup G} (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    omegaOneCenterOf P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  have hZ : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  have hdvd : 2 ∣ Nat.card (Subgroup.center P) := by
    obtain ⟨k, hk⟩ := (hP.to_subgroup (Subgroup.center P)).exists_card_eq
    have h1 : 1 < Nat.card (Subgroup.center P) := Finite.one_lt_card_iff_nontrivial.mpr hZ
    rw [hk] at h1 ⊢
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at h1
      exact lt_irrefl 1 h1
    exact dvd_pow_self 2 hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 2 hdvd
  intro h
  have hmem : (((z : Subgroup.center P) : P) : G) ∈ omegaOneCenterOf P := by
    apply Subgroup.subset_closure
    refine ⟨⟨(z : P).2, ?_⟩, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩))
    · have h1 := pow_orderOf_eq_one z
      rw [hz] at h1
      have h2 := congrArg (fun w : Subgroup.center P => ((w : P) : G)) h1
      simpa using h2
  rw [h, Subgroup.mem_bot] at hmem
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hmem)
  rw [hz1, orderOf_one] at hz
  exact Nat.prime_two.one_lt.ne hz

theorem pCoreOf_mcOf_le_pCoreOf_sup (st : Setting1427 T M H K1) {Kc : Subgroup G}
    (hKc : Kc ≤ mcOf T) : pCoreOf 2 (mcOf T) ≤ pCoreOf 2 (Kc ⊔ T) := by
  have hyp := st.hyp
  have hTMc : T ≤ mcOf T := hyp.toQTFE14.t_le_mc
  have hTSyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_isSylowTwo hyp.sylow hTMc
  have hOT : pCoreOf 2 (mcOf T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTSyl
  exact le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right)
    ((sup_le hKc hTMc).trans (le_normalizer_pCoreOf 2 (mcOf T))) (pCoreOf_isPGroup 2 _)

theorem pCoreOf_sup_ne_bot (st : Setting1427 T M H K1) {Kc : Subgroup G} (hKc : Kc ≤ mcOf T) :
    pCoreOf 2 (Kc ⊔ T) ≠ ⊥ := by
  intro h
  have h1 := pCoreOf_mcOf_le_pCoreOf_sup st hKc
  rw [h] at h1
  exact pCoreOf_ne_bot_of_isTwoLocal st.hyp.mc_max.1 (le_bot_iff.mp h1)

theorem pCoreOf_sup_le_sOf (st : Setting1427 T M H K1) {Kc : Subgroup G}
    (hKT : oTwoUpper H ≤ Kc ⊔ T) : pCoreOf 2 (Kc ⊔ T) ≤ sOf T K1 := by
  have hyp := st.hyp
  have N := st.notation_
  have hTH : T ≤ H := st.hStar.1.1
  have hTJ : T ≤ Kc ⊔ T := le_sup_right
  have hHJ : H ≤ Kc ⊔ T := by
    rw [← sup_oTwoUpper_eq st]
    exact sup_le hKT hTJ
  have hRT : pCoreOf 2 (Kc ⊔ T) ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_isSylowTwo hyp.sylow hTJ)
  have hRH : pCoreOf 2 (Kc ⊔ T) ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hRT.trans hTH) (hHJ.trans (le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  exact hRH.trans (le_inf (pCoreOf_two_le_of_isSylowTwoOf
    (isSylowTwoOf_of_isSylowTwo hyp.sylow hTH)) N.pCore_le)

theorem omegaOneCenterOf_sOf_le (st : Setting1427 T M H K1) {Kc : Subgroup G}
    (hKc : Kc ≤ mcOf T) (hKT : oTwoUpper H ≤ Kc ⊔ T) :
    omegaOneCenterOf (sOf T K1) ≤ omegaOneCenterOf (pCoreOf 2 (Kc ⊔ T)) := by
  have hyp := st.hyp
  have hJchar : CharTwo (Kc ⊔ T) :=
    charTwo_of_inH' hyp.qtke hyp.sylow ⟨le_sup_right, pCoreOf_sup_ne_bot st hKc⟩
  have hRS := pCoreOf_sup_le_sOf st hKT
  have hZ : centerOf (sOf T K1) ≤ centerOf (pCoreOf 2 (Kc ⊔ T)) := by
    intro z hz
    have hzC : z ∈ Subgroup.centralizer (pCoreOf 2 (Kc ⊔ T) : Set G) :=
      Subgroup.centralizer_le (fun x hx => hRS hx) hz.2
    have hzJ : z ∈ Kc ⊔ T := (le_sup_right : T ≤ Kc ⊔ T) (sOf_le_T hz.1)
    exact ⟨hJchar ⟨hzJ, hzC⟩, hzC⟩
  exact Subgroup.closure_mono fun x hx => ⟨hZ hx.1, hx.2⟩

theorem VYR_eq_bot_of_mem_cComp (st : Setting1427 T M H K1) {Kc : Subgroup G}
    (hKc : Kc ∈ cComp (mcOf T)) : VYR Kc (pCoreOf 2 (Kc ⊔ T)) = ⊥ := by
  have hyp := st.hyp
  have hTMc : T ≤ mcOf T := hyp.toQTFE14.t_le_mc
  have hMcO : pCoreOf 2 (mcOf T) ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hyp.mc_max.1
  have hKcMc : Kc ≤ mcOf T := le_of_mem_cComp hKc
  have hTSyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_isSylowTwo hyp.sylow hTMc
  have hloc : quasithinIsLocal T Kc := isLocal_of_mem_cComp_of_sylow hTSyl hMcO hKc
  have hsub : IsSubnormal Kc (mcOf T) := subnormal_of_mem_cComp hKc
  have hMcchar : CharTwo (mcOf T) := charTwo_of_inH' hyp.qtke hyp.sylow ⟨hTMc, hMcO⟩
  have hX : IsXClass Kc :=
    ⟨ne_bot_of_mem_cComp hKc, eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hKc),
      A4.charTwo_of_subnormal hsub hMcchar⟩
  have hVY : VY Kc = ⊥ := by
    by_contra hne
    exact hyp.faithful_empty Kc (isFaithfulLocal_iff_isXf.mpr ⟨hloc, hX, hne⟩)
  have hJMc : Kc ⊔ T ≤ mcOf T := sup_le hKcMc hTMc
  have hsig : IsSignalizer (mcOf T) Kc (pCoreOf 2 (Kc ⊔ T)) :=
    ⟨(pCoreOf_le 2 _).trans hJMc, pCoreOf_isPGroup 2 _,
      (le_sup_left : Kc ≤ Kc ⊔ T).trans (le_normalizer_pCoreOf 2 _)⟩
  have hO2 : pCoreOf 2 Kc ≤ pCoreOf 2 (Kc ⊔ T) :=
    (A4.pCoreOf_le_of_subnormal 2 hsub).trans (pCoreOf_mcOf_le_pCoreOf_sup st hKcMc)
  by_contra hne
  exact (a4_8_5 (A48Hyp.of_self hX hsub hsig hO2)).mp hne hVY

theorem commutator_omegaOneCenter_sOf_eq_bot (st : Setting1427 T M H K1) {Kc : Subgroup G}
    (hKc : Kc ∈ cComp (mcOf T)) (hKT : oTwoUpper H ≤ Kc ⊔ T) :
    ⁅omegaOneCenterOf (sOf T K1), Kc⁆ = ⊥ := by
  have h1 := Subgroup.commutator_mono (omegaOneCenterOf_sOf_le st (le_of_mem_cComp hKc) hKT)
    (le_refl Kc)
  exact le_bot_iff.mp (h1.trans (le_of_eq (VYR_eq_bot_of_mem_cComp st hKc)))

theorem le_centralizer_omegaOneCenter_sOf (st : Setting1427 T M H K1) {Kc : Subgroup G}
    (hKc : Kc ∈ cComp (mcOf T)) (hKT : oTwoUpper H ≤ Kc ⊔ T) :
    Kc ≤ Subgroup.centralizer (omegaOneCenterOf (sOf T K1) : Set G) :=
  Subgroup.le_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (commutator_omegaOneCenter_sOf_eq_bot st hKc hKT))

end S1421

end CFSG.Quasithin
