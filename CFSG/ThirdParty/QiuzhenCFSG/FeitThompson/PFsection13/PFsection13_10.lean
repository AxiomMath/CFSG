module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_a

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_10
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.10) -/

/- The combined estimate obtained in the proof of Peterfalvi `(13.10)` from
`(13.10.1)`, `(13.10.2)`, `(13.10.3)`, and `(13.9)(b)`. -/


private theorem section13_theorem_13_10_v_real_formula_of_hypothesis
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u) :
    (v : ℝ) = ((q : ℝ) ^ p - 1) / ((q - 1 : ℕ) : ℝ) := by
  rcases section13_theorem_13_10_rawSourcePositivity_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource with
    ⟨_hp, hq1, _hc⟩
  have h4 := theorem_13_4 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsource h10
  have hvNat : v = (q ^ p - 1) / (q - 1) := h4.2.2
  have hvReal := congrArg (fun n : ℕ => (n : ℝ)) hvNat
  simpa [section13_real_geom_quotient_cast (p := p) hq1] using hvReal

private theorem section13_theorem_13_10_d_eq_one_of_hypothesis
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u) :
    d = 1 := by
  have hsourceOrig := hsource
  rcases hsource with
    ⟨_hcaseB, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  have h4 := theorem_13_4 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d
  have hD : D = ⊥ := (h4 hsourceOrig h10).1
  rw [hd_card, hD]
  exact Subgroup.card_bot

private theorem section13_theorem_13_10_v_card_formula_of_hypothesis
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u) :
    Nat.card V = v := by
  have hsourceOrig := hsource
  rcases hsource with
    ⟨_hcaseB, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  have hd_one : d = 1 :=
    section13_theorem_13_10_d_eq_one_of_hypothesis
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig h10
  rw [hV_card, hd_one, Nat.mul_one]

private theorem section13_theorem_13_10_q_card_formula_of_hypothesis
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u) :
    Nat.card Q = q ^ p := by
  have h4 := theorem_13_4 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsource h10
  rcases h4 with ⟨_hD, hcaseT, _hvNat⟩
  dsimp [case_9_7_b_sourceDataForSection13] at hcaseT
  rcases hcaseT with
    ⟨_hhyp92, _hH0, _hcent, _hqPrime, _hpPrime, _hho, hquot,
      _hCcent, _hUbar, _hirr, _hfield, _hcop, _hdvd⟩
  rcases hquot with ⟨hnormal, hcardQuot⟩
  letI : ((⊥ : Subgroup G).subgroupOf Q).Normal := hnormal
  have hbot : ((⊥ : Subgroup G).subgroupOf Q) = (⊥ : Subgroup Q) := by
    ext x
    simp
  have hcardBot :
      Nat.card (Q ⧸ (⊥ : Subgroup G).subgroupOf Q) = Nat.card Q := by
    rw [hbot]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := Q)).toEquiv
  exact hcardBot.symm.trans hcardQuot

private theorem section13_theorem_13_10_qSharp_card_formula_of_hypothesis
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u) :
    Nat.card (Section7.puncturedSubgroupSet Q) = q ^ p - 1 := by
  rw [section13_natCard_puncturedSubgroupSet Q]
  rw [section13_theorem_13_10_q_card_formula_of_hypothesis
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d hsource h10]

private theorem section13_theorem_13_10_p_card_formula_of_hypothesis
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Nat.card P = p ^ q := by
  rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with
    ⟨_hMF, _htype, _hlarge, _hUcomm, _hFrob, _hPelem, hPcard, _huBound,
      _hcoh, _hTI, _hTau⟩
  exact hPcard


private def theorem_13_10_lambdaTotalNormPieceSourceData
    {G : Type u} [Group G] [Finite G]
    (Smax H : Subgroup G)
    (lamτ : Section1.ClassFunction G) : Prop :=
  Section7.supportEnergy Set.univ lamτ / (Nat.card G : ℝ) ≤ 1 ∧
    1 ≤ Complex.normSq (lamτ 1) ∧
      Section7.supportEnergy
          (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ) lamτ /
          (Nat.card G : ℝ) =
        Section7.supportEnergy (Section7.puncturedSubgroupSet H) lamτ /
          (Nat.card Smax : ℝ)

private theorem section13_theorem_13_10_lambdaTotalNormPieces_from_sourceData
    {G : Type u} [Group G] [Finite G]
    (Smax H Q : Subgroup G)
    (G0 : Set G)
    (lamτ : Section1.ClassFunction G)
    (hG0 : theorem_13_9_G0Data H Q G0)
    (hdata : theorem_13_10_lambdaTotalNormPieceSourceData Smax H lamτ) :
    1 ≥ 1 / (Nat.card G : ℝ) +
      Section7.supportEnergy G0 lamτ / (Nat.card G : ℝ) +
        Section7.supportEnergy (Section7.puncturedSubgroupSet H) lamτ /
          (Nat.card Smax : ℝ) := by
  let oneSet : Set G := {1}
  let Hc : Set G :=
    section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ
  rcases hdata with ⟨hnorm, hχ1, horbit⟩
  have hG0def : G0 =
      section16NonidentityElements (Set.univ : Set G) \
        (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ ∪
          section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ) := by
    simpa [theorem_13_9_G0Data] using hG0
  have hG0_nonid : G0 ⊆ section16NonidentityElements (Set.univ : Set G) := by
    intro x hx
    rw [hG0def] at hx
    exact hx.1
  have hOneG0 : Disjoint oneSet G0 := by
    rw [Set.disjoint_left]
    intro x hx1 hxG0
    have hx_eq : x = 1 := by simpa [oneSet] using hx1
    exact (hG0_nonid hxG0).2 hx_eq
  have hOneHc : Disjoint oneSet Hc := by
    rw [Set.disjoint_left]
    intro x hx1 hxHc
    have hx_eq : x = 1 := by simpa [oneSet] using hx1
    rcases hxHc with ⟨z, hz, y, _hy, hzy⟩
    rcases hz with ⟨_hzH, hz_ne⟩
    have hz_one : (1 : G) = z := by
      simpa [hx_eq, mul_assoc] using congrArg (fun w : G => y⁻¹ * w * y) hzy
    exact hz_ne hz_one.symm
  have hG0Hc : Disjoint G0 Hc := by
    rw [Set.disjoint_left]
    intro x hxG0 hxHc
    rw [hG0def] at hxG0
    exact hxG0.2 (Or.inl hxHc)
  have hUnionHc : Disjoint (oneSet ∪ G0) Hc := by
    rw [Set.disjoint_left]
    intro x hx hxHc
    rcases hx with hx1 | hxG0
    · exact hOneHc.le_bot ⟨hx1, hxHc⟩
    · exact hG0Hc.le_bot ⟨hxG0, hxHc⟩
  have hsum_union :
      Section7.supportEnergy (oneSet ∪ G0 ∪ Hc) lamτ =
        Section7.supportEnergy oneSet lamτ + Section7.supportEnergy G0 lamτ +
          Section7.supportEnergy Hc lamτ := by
    rw [section13_supportEnergy_union_of_disjoint hUnionHc]
    rw [section13_supportEnergy_union_of_disjoint hOneG0]
  have hsum_le_univ :
      Section7.supportEnergy oneSet lamτ + Section7.supportEnergy G0 lamτ +
          Section7.supportEnergy Hc lamτ ≤ Section7.supportEnergy Set.univ lamτ := by
    rw [← hsum_union]
    exact section13_supportEnergy_le_univ (oneSet ∪ G0 ∪ Hc) lamτ
  have hGnonneg : 0 ≤ (Nat.card G : ℝ) := by positivity
  have hdiv := div_le_div_of_nonneg_right hsum_le_univ hGnonneg
  have hsplit :
      (Section7.supportEnergy oneSet lamτ + Section7.supportEnergy G0 lamτ +
          Section7.supportEnergy Hc lamτ) / (Nat.card G : ℝ) =
        Section7.supportEnergy oneSet lamτ / (Nat.card G : ℝ) +
          Section7.supportEnergy G0 lamτ / (Nat.card G : ℝ) +
            Section7.supportEnergy Hc lamτ / (Nat.card G : ℝ) := by
    ring
  rw [hsplit] at hdiv
  have hsum_norm :
      Section7.supportEnergy oneSet lamτ / (Nat.card G : ℝ) +
        Section7.supportEnergy G0 lamτ / (Nat.card G : ℝ) +
          Section7.supportEnergy Hc lamτ / (Nat.card G : ℝ) ≤ 1 := by
    nlinarith
  have hsingle :
      1 / (Nat.card G : ℝ) ≤
        Section7.supportEnergy oneSet lamτ / (Nat.card G : ℝ) := by
    simpa [oneSet] using section13_one_div_card_le_singleton_energy_div lamτ hχ1
  rw [← horbit]
  nlinarith


private theorem section13_theorem_13_10_lambdaTotalNormInequality_from_pieces
    {G : Type u} [Group G] [Finite G]
    (Smax H : Subgroup G)
    (G0 : Set G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (hpieces : 1 ≥ 1 / (Nat.card G : ℝ) +
      Section7.supportEnergy G0 lamτ / (Nat.card G : ℝ) +
        Section7.supportEnergy (Section7.puncturedSubgroupSet H) lamτ /
          (Nat.card Smax : ℝ))
    (h6 : squareSumLowerBound (Section7.puncturedSubgroupSet H) lamτ
      ((Nat.card Smax : ℝ) - Complex.normSq (lam 1))) :
    1 ≥ 1 / (Nat.card G : ℝ) +
      Section7.supportEnergy G0 lamτ / (Nat.card G : ℝ) +
        1 - Complex.normSq (lam 1) / (Nat.card Smax : ℝ) := by
  have hSpos : 0 < (Nat.card Smax : ℝ) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card Smax)
  have hdivraw :
      ((Nat.card Smax : ℝ) - Complex.normSq (lam 1)) / (Nat.card Smax : ℝ) ≤
        Section7.supportEnergy (Section7.puncturedSubgroupSet H) lamτ /
          (Nat.card Smax : ℝ) :=
    div_le_div_of_nonneg_right h6 (le_of_lt hSpos)
  have hrewrite :
      ((Nat.card Smax : ℝ) - Complex.normSq (lam 1)) / (Nat.card Smax : ℝ) =
        1 - Complex.normSq (lam 1) / (Nat.card Smax : ℝ) := by
    field_simp [hSpos.ne']
  have hlower :
      1 - Complex.normSq (lam 1) / (Nat.card Smax : ℝ) ≤
        Section7.supportEnergy (Section7.puncturedSubgroupSet H) lamτ /
          (Nat.card Smax : ℝ) := by
    rw [← hrewrite]
    exact hdivraw
  nlinarith

private theorem section13_theorem_13_10_etaTotalNormInequality_from_pieces
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax H Q : Subgroup G)
    (G0 : Set G)
    (eta10 : Section1.ClassFunction G)
    (v : ℕ)
    (hpieces : 1 ≥ 1 / (Nat.card G : ℝ) +
      Section7.supportEnergy G0 eta10 / (Nat.card G : ℝ) +
        Section7.supportEnergy (Section7.puncturedSubgroupSet H) eta10 /
          (Nat.card Smax : ℝ) +
          Section7.supportEnergy (Section7.puncturedSubgroupSet Q) eta10 /
            (Nat.card Tmax : ℝ))
    (hH : squareSumLowerBound (Section7.puncturedSubgroupSet H) eta10
      (Nat.card (Section7.puncturedSubgroupSet H) : ℝ))
    (hQ : squareSumLowerBound (Section7.puncturedSubgroupSet Q) eta10
      ((Nat.card (ambientDerivedSubgroup Tmax) : ℝ) - (v : ℝ) ^ 2)) :
    1 ≥ 1 / (Nat.card G : ℝ) +
      Section7.supportEnergy G0 eta10 / (Nat.card G : ℝ) +
        (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) / (Nat.card Smax : ℝ) +
          (((Nat.card (ambientDerivedSubgroup Tmax) : ℝ) - (v : ℝ) ^ 2) /
            (Nat.card Tmax : ℝ)) := by
  have hSpos : 0 < (Nat.card Smax : ℝ) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card Smax)
  have hTpos : 0 < (Nat.card Tmax : ℝ) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card Tmax)
  have hHdiv :
      (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) / (Nat.card Smax : ℝ) ≤
        Section7.supportEnergy (Section7.puncturedSubgroupSet H) eta10 /
          (Nat.card Smax : ℝ) :=
    div_le_div_of_nonneg_right hH (le_of_lt hSpos)
  have hQdiv :
      ((Nat.card (ambientDerivedSubgroup Tmax) : ℝ) - (v : ℝ) ^ 2) /
          (Nat.card Tmax : ℝ) ≤
        Section7.supportEnergy (Section7.puncturedSubgroupSet Q) eta10 /
          (Nat.card Tmax : ℝ) :=
    div_le_div_of_nonneg_right hQ (le_of_lt hTpos)
  nlinarith

private theorem section13_theorem_13_10_etaQSharpLowerBound_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (eta10 : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_hH : H = P ⊔ C)
    (heta10 : eta10 = η 1 0)
    (hD : D = ⊥)
    (_hG0 : theorem_13_9_G0Data H Q G0) :
    squareSumLowerBound (Section7.puncturedSubgroupSet Q) eta10
      ((Nat.card (ambientDerivedSubgroup Tmax) : ℝ) - (v : ℝ) ^ 2) := by
  have hsourceT := section13_hypothesis_13_1_sourceData_swap hsource
  have hnotationT := section13_hypothesis_13_1_characterNotationDataFor_swap hnotation
  have h8 := theorem_13_8 Tmax Smax W W2 W1 Q P V U D C (Q ⊔ D) (Q ⊔ V)
    Tfam Sfam τT τS
    (fun i j => ω j i) (fun i j => η j i) (fun i j => ν j i)
    (fun i j => μ j i) νsum μsum δ' δ σ q p v u d c
    hsourceT hnotationT rfl rfl
  rcases hsource with
    ⟨_hcase, _hptypeS, hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hptypeT with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hVle, _hVnil, _hW2norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW1le, _hW1cyc,
      _hW1ne, _hcent, _hnorm⟩
  rcases hDercomp with ⟨_hQDer, _hVDer, hDer_eq, _hdisj⟩
  have hQD : Q ⊔ D = Q := by
    rw [hD, sup_bot_eq]
  have hQV : Q ⊔ V = ambientDerivedSubgroup Tmax := hDer_eq.symm
  simpa [heta10, hQD, hQV] using h8

private def theorem_13_10_etaTotalNormPieceSourceData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax H Q : Subgroup G)
    (eta10 : Section1.ClassFunction G) : Prop :=
  Section7.supportEnergy Set.univ eta10 / (Nat.card G : ℝ) ≤ 1 ∧
    1 ≤ Complex.normSq (eta10 1) ∧
      Disjoint
        (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ)
        (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ) ∧
        Section7.supportEnergy
            (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ) eta10 /
            (Nat.card G : ℝ) =
          Section7.supportEnergy (Section7.puncturedSubgroupSet H) eta10 /
            (Nat.card Smax : ℝ) ∧
        Section7.supportEnergy
            (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ) eta10 /
            (Nat.card G : ℝ) =
          Section7.supportEnergy (Section7.puncturedSubgroupSet Q) eta10 /
            (Nat.card Tmax : ℝ)

private theorem section13_theorem_13_10_etaTotalNormPieces_from_sourceData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax H Q : Subgroup G)
    (G0 : Set G)
    (eta10 : Section1.ClassFunction G)
    (hG0 : theorem_13_9_G0Data H Q G0)
    (hdata : theorem_13_10_etaTotalNormPieceSourceData Smax Tmax H Q eta10) :
    1 ≥ 1 / (Nat.card G : ℝ) +
      Section7.supportEnergy G0 eta10 / (Nat.card G : ℝ) +
        Section7.supportEnergy (Section7.puncturedSubgroupSet H) eta10 /
          (Nat.card Smax : ℝ) +
          Section7.supportEnergy (Section7.puncturedSubgroupSet Q) eta10 /
            (Nat.card Tmax : ℝ) := by
  let oneSet : Set G := {1}
  let Hc : Set G :=
    section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ
  let Qc : Set G :=
    section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ
  rcases hdata with ⟨hnorm, hχ1, hHQ, hHorbit, hQorbit⟩
  have hG0def : G0 =
      section16NonidentityElements (Set.univ : Set G) \
        (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ ∪
          section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ) := by
    simpa [theorem_13_9_G0Data] using hG0
  have hG0_nonid : G0 ⊆ section16NonidentityElements (Set.univ : Set G) := by
    intro x hx
    rw [hG0def] at hx
    exact hx.1
  have hOneG0 : Disjoint oneSet G0 := by
    rw [Set.disjoint_left]
    intro x hx1 hxG0
    have hx_eq : x = 1 := by simpa [oneSet] using hx1
    exact (hG0_nonid hxG0).2 hx_eq
  have hOneConj (K : Subgroup G) :
      Disjoint oneSet
        (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet K) Set.univ) := by
    rw [Set.disjoint_left]
    intro x hx1 hxKc
    have hx_eq : x = 1 := by simpa [oneSet] using hx1
    rcases hxKc with ⟨z, hz, y, _hy, hzy⟩
    rcases hz with ⟨_hzK, hz_ne⟩
    have hz_one : (1 : G) = z := by
      simpa [hx_eq, mul_assoc] using congrArg (fun w : G => y⁻¹ * w * y) hzy
    exact hz_ne hz_one.symm
  have hOneHc : Disjoint oneSet Hc := by
    simpa [Hc] using hOneConj H
  have hOneQc : Disjoint oneSet Qc := by
    simpa [Qc] using hOneConj Q
  have hG0Hc : Disjoint G0 Hc := by
    rw [Set.disjoint_left]
    intro x hxG0 hxHc
    rw [hG0def] at hxG0
    exact hxG0.2 (Or.inl hxHc)
  have hG0Qc : Disjoint G0 Qc := by
    rw [Set.disjoint_left]
    intro x hxG0 hxQc
    rw [hG0def] at hxG0
    exact hxG0.2 (Or.inr hxQc)
  have hUnionHc : Disjoint (oneSet ∪ G0) Hc := by
    rw [Set.disjoint_left]
    intro x hx hxHc
    rcases hx with hx1 | hxG0
    · exact hOneHc.le_bot ⟨hx1, hxHc⟩
    · exact hG0Hc.le_bot ⟨hxG0, hxHc⟩
  have hUnionQc : Disjoint (oneSet ∪ G0 ∪ Hc) Qc := by
    rw [Set.disjoint_left]
    intro x hx hxQc
    rcases hx with hx | hxHc
    · rcases hx with hx1 | hxG0
      · exact hOneQc.le_bot ⟨hx1, hxQc⟩
      · exact hG0Qc.le_bot ⟨hxG0, hxQc⟩
    · exact hHQ.le_bot ⟨hxHc, hxQc⟩
  have hsum_union :
      Section7.supportEnergy (oneSet ∪ G0 ∪ Hc ∪ Qc) eta10 =
        Section7.supportEnergy oneSet eta10 + Section7.supportEnergy G0 eta10 +
          Section7.supportEnergy Hc eta10 + Section7.supportEnergy Qc eta10 := by
    rw [section13_supportEnergy_union_of_disjoint hUnionQc]
    rw [section13_supportEnergy_union_of_disjoint hUnionHc]
    rw [section13_supportEnergy_union_of_disjoint hOneG0]
  have hsum_le_univ :
      Section7.supportEnergy oneSet eta10 + Section7.supportEnergy G0 eta10 +
          Section7.supportEnergy Hc eta10 + Section7.supportEnergy Qc eta10 ≤
        Section7.supportEnergy Set.univ eta10 := by
    rw [← hsum_union]
    exact section13_supportEnergy_le_univ (oneSet ∪ G0 ∪ Hc ∪ Qc) eta10
  have hGnonneg : 0 ≤ (Nat.card G : ℝ) := by positivity
  have hdiv := div_le_div_of_nonneg_right hsum_le_univ hGnonneg
  have hsplit :
      (Section7.supportEnergy oneSet eta10 + Section7.supportEnergy G0 eta10 +
          Section7.supportEnergy Hc eta10 + Section7.supportEnergy Qc eta10) /
          (Nat.card G : ℝ) =
        Section7.supportEnergy oneSet eta10 / (Nat.card G : ℝ) +
          Section7.supportEnergy G0 eta10 / (Nat.card G : ℝ) +
            Section7.supportEnergy Hc eta10 / (Nat.card G : ℝ) +
              Section7.supportEnergy Qc eta10 / (Nat.card G : ℝ) := by
    ring
  rw [hsplit] at hdiv
  have hsum_norm :
      Section7.supportEnergy oneSet eta10 / (Nat.card G : ℝ) +
        Section7.supportEnergy G0 eta10 / (Nat.card G : ℝ) +
          Section7.supportEnergy Hc eta10 / (Nat.card G : ℝ) +
            Section7.supportEnergy Qc eta10 / (Nat.card G : ℝ) ≤ 1 := by
    nlinarith
  have hsingle :
      1 / (Nat.card G : ℝ) ≤
        Section7.supportEnergy oneSet eta10 / (Nat.card G : ℝ) := by
    simpa [oneSet] using section13_one_div_card_le_singleton_energy_div eta10 hχ1
  rw [← hHorbit, ← hQorbit]
  nlinarith

private theorem section13_theorem_13_10_disjointCardinalityIdentity_from_scaled
    (g g0 hRatio qRatio : ℝ)
    (hg : 0 < g)
    (hcard : g = 1 + g0 + g * hRatio + g * qRatio) :
    1 = 1 / g + g0 / g + hRatio + qRatio := by
  have hg0 : g ≠ 0 := hg.ne'
  field_simp [hg0]
  nlinarith

private theorem section13_one_not_mem_conjugatesOf_puncturedSubgroupSet
    {G : Type u} [Group G]
    (H : Subgroup G) :
    (1 : G) ∉
      section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ := by
  intro hmem
  rcases hmem with ⟨x, hx, y, _hy, hxy⟩
  rcases hx with ⟨_hxH, hxne⟩
  have hconj : (1 : G) = x := by
    simpa [mul_assoc] using congrArg (fun z : G => y⁻¹ * z * y) hxy
  exact hxne hconj.symm

private theorem section13_one_not_mem_puncturedSubgroupSet
    {G : Type u} [Group G]
    (H : Subgroup G) :
    (1 : G) ∉ Section7.puncturedSubgroupSet H := by
  intro hmem
  exact hmem.2 rfl

private theorem section13_mem_normalizer_of_conjugateSet_eq
    {G : Type u} [Group G]
    {X : Set G} {g : G}
    (hX : section16ConjugateSet X g = X) :
    g ∈ Subgroup.normalizer X := by
  change ∀ y : G, y ∈ X ↔ g * y * g⁻¹ ∈ X
  intro y
  constructor
  · intro hy
    rw [← hX]
    exact ⟨y, hy, rfl⟩
  · intro hy
    have hmem : g * y * g⁻¹ ∈ section16ConjugateSet X g := by
      simpa [hX] using hy
    rcases hmem with ⟨x, hx, hxy⟩
    have hyx : y = x := by
      simpa [mul_assoc] using congrArg (fun z : G => g⁻¹ * z * g) hxy
    simpa [hyx] using hx

private theorem section13_card_conjugatesOfSetBySet_eq_card_mul_index_of_ti
    {G : Type u} [Group G] [Finite G]
    {X : Set G}
    (hX1 : (1 : G) ∉ X)
    (hXti : section16TISubset X) :
    Nat.card (section16ConjugatesOfSetBySet X Set.univ) =
      Nat.card X * (Subgroup.normalizer X).index := by
  classical
  let N : Subgroup G := Subgroup.normalizer X
  let Ω := Quotient (QuotientGroup.rightRel N)
  let X0 := {x : G // x ∈ X}
  let f : Ω × X0 → {z : G // z ∈ section16ConjugatesOfSetBySet X Set.univ} := fun qx =>
    let a : G := Quotient.out qx.1
    ⟨a⁻¹ * qx.2.1 * a, ⟨qx.2.1, qx.2.2, a⁻¹, Set.mem_univ _, by simp [mul_assoc]⟩⟩
  have hfBij : Function.Bijective f := by
    constructor
    · intro qx1 qx2 hEq
      rcases qx1 with ⟨q1, x1⟩
      rcases qx2 with ⟨q2, x2⟩
      let a1 : G := Quotient.out q1
      let a2 : G := Quotient.out q2
      have hval : a1⁻¹ * x1.1 * a1 = a2⁻¹ * x2.1 * a2 :=
        congrArg Subtype.val hEq
      by_cases hq : q1 = q2
      · have ha : a2 = a1 := by simpa [a1, a2] using congrArg Quotient.out hq.symm
        have hx : x1 = x2 := by
          apply Subtype.ext
          rw [ha] at hval
          have hconj := congrArg (fun z : G => a1 * z * a1⁻¹) hval
          simpa [a1, mul_assoc] using hconj
        cases hq
        cases hx
        rfl
      · have hgNotN : a1 * a2⁻¹ ∉ N := by
          intro hgN
          apply hq
          have hginv : a2 * a1⁻¹ ∈ N := by
            simpa using N.inv_mem hgN
          calc
            q1 = Quotient.mk'' a1 := (Quotient.out_eq' q1).symm
            _ = Quotient.mk'' a2 := Quotient.sound' (QuotientGroup.rightRel_apply.mpr hginv)
            _ = q2 := Quotient.out_eq' q2
        have hx1Conj : x1.1 ∈ section16ConjugateSet X (a1 * a2⁻¹) := by
          refine ⟨x2.1, x2.2, ?_⟩
          have hconj := congrArg (fun z : G => a1 * z * a1⁻¹) hval
          simpa [a1, a2, mul_assoc] using hconj
        rcases hXti (a1 * a2⁻¹) with hsame | hsmall
        · exact False.elim (hgNotN (section13_mem_normalizer_of_conjugateSet_eq hsame))
        · have hx1one : x1.1 = 1 := by
            simpa using hsmall ⟨x1.2, hx1Conj⟩
          exact False.elim (hX1 (hx1one ▸ x1.2))
    · intro z
      rcases z.2 with ⟨x, hxX, y, _hy, hzy⟩
      let q : Ω := Quotient.mk'' y⁻¹
      let a : G := Quotient.out q
      have hyaN : y⁻¹ * a⁻¹ ∈ N := by
        have hqa : (Quotient.mk'' a : Ω) = Quotient.mk'' y⁻¹ := by
          simp [q, a]
        exact QuotientGroup.rightRel_apply.mp (Quotient.exact' hqa)
      let n : G := y⁻¹ * a⁻¹
      have hnInvNorm : n⁻¹ ∈ N := N.inv_mem hyaN
      have hx' : n⁻¹ * x * n ∈ X := by
        change ∀ z : G, z ∈ X ↔ n⁻¹ * z * (n⁻¹)⁻¹ ∈ X at hnInvNorm
        simpa [n] using (hnInvNorm x).1 hxX
      refine ⟨(q, ⟨n⁻¹ * x * n, hx'⟩), ?_⟩
      apply Subtype.ext
      calc
        ((f (q, ⟨n⁻¹ * x * n, hx'⟩)).1) = y * x * y⁻¹ := by
          simp [f, q, a, n, mul_assoc]
        _ = z := by simpa using hzy.symm
  have hcardOmega : Nat.card Ω = N.index := by
    calc
      Nat.card Ω = Nat.card (G ⧸ N) := by
        exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel N)
      _ = N.index := N.index_eq_card.symm
  calc
    Nat.card (section16ConjugatesOfSetBySet X Set.univ) = Nat.card (Ω × X0) := by
      exact Nat.card_congr (Equiv.ofBijective f hfBij).symm
    _ = Nat.card Ω * Nat.card X0 := Nat.card_prod _ _
    _ = Nat.card Ω * Nat.card X := rfl
    _ = Nat.card X * N.index := by rw [hcardOmega, Nat.mul_comm]

public theorem section13_conjugatesOfSetBySet_card_real_eq
    {G : Type u} [Group G] [Finite G]
    {X : Set G} {N : Subgroup G}
    (hX1 : (1 : G) ∉ X)
    (hXti : section16TISubsetWithNormalizer X N) :
    (Nat.card (section16ConjugatesOfSetBySet X Set.univ) : ℝ) =
      (Nat.card G : ℝ) * ((Nat.card X : ℝ) / (Nat.card N : ℝ)) := by
  rcases hXti with ⟨hTI, hNorm⟩
  have hcard := section13_card_conjugatesOfSetBySet_eq_card_mul_index_of_ti
    (X := X) hX1 hTI
  rw [hNorm] at hcard
  have hGcard : (Nat.card G : ℝ) = (Nat.card N : ℝ) * (N.index : ℝ) := by
    exact_mod_cast (Subgroup.card_mul_index (H := N)).symm
  rw [hcard, hGcard]
  have hNpos : (0 : ℝ) < Nat.card N := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card N)
  field_simp [hNpos.ne']
  exact_mod_cast (Nat.mul_comm (Nat.card X) N.index)

private theorem section13_supportEnergy_eq_sum_subtype
    {G : Type u} [Group G] [Finite G]
    (X : Set G) (χ : Section1.ClassFunction G) :
    Section7.supportEnergy X χ =
      ∑ x : {g : G // g ∈ X}, Complex.normSq (χ x.1) := by
  classical
  rw [Section7.supportEnergy]
  have hfilter :
      (∑ g : G, (if g ∈ X then Complex.normSq (χ g) else 0)) =
        ∑ g ∈ (Finset.univ.filter (fun g : G => g ∈ X)), Complex.normSq (χ g) := by
    simp [Finset.sum_filter]
  rw [hfilter]
  exact Finset.sum_subtype (s := Finset.univ.filter (fun g : G => g ∈ X))
    (p := fun g : G => g ∈ X) (f := fun g : G => Complex.normSq (χ g)) (by simp)

private theorem section13_supportEnergy_conjugatesOfSetBySet_eq_index_mul
    {G : Type u} [Group G] [Finite G]
    {X : Set G} {N : Subgroup G}
    (hX1 : (1 : G) ∉ X)
    (hXti : section16TISubsetWithNormalizer X N)
    (χ : Section1.ClassFunction G)
    (hχ : Section1.IsClassFunction χ) :
    Section7.supportEnergy (section16ConjugatesOfSetBySet X Set.univ) χ =
      (N.index : ℝ) * Section7.supportEnergy X χ := by
  classical
  let Ω := Quotient (QuotientGroup.rightRel N)
  let X0 := {x : G // x ∈ X}
  let C0 := {z : G // z ∈ section16ConjugatesOfSetBySet X Set.univ}
  letI : Fintype X0 := Fintype.ofFinite X0
  letI : Fintype C0 := Fintype.ofFinite C0
  let f : Ω × X0 → C0 := fun qx =>
    let a : G := Quotient.out qx.1
    ⟨a⁻¹ * qx.2.1 * a, ⟨qx.2.1, qx.2.2, a⁻¹, Set.mem_univ _, by simp [mul_assoc]⟩⟩
  have hfBij : Function.Bijective f := by
    constructor
    · intro qx1 qx2 hEq
      rcases qx1 with ⟨q1, x1⟩
      rcases qx2 with ⟨q2, x2⟩
      let a1 : G := Quotient.out q1
      let a2 : G := Quotient.out q2
      have hval : a1⁻¹ * x1.1 * a1 = a2⁻¹ * x2.1 * a2 :=
        congrArg Subtype.val hEq
      by_cases hq : q1 = q2
      · have ha : a2 = a1 := by simpa [a1, a2] using congrArg Quotient.out hq.symm
        have hx : x1 = x2 := by
          apply Subtype.ext
          rw [ha] at hval
          have hconj := congrArg (fun z : G => a1 * z * a1⁻¹) hval
          simpa [a1, mul_assoc] using hconj
        cases hq
        cases hx
        rfl
      · have hgNotN : a1 * a2⁻¹ ∉ N := by
          intro hgN
          apply hq
          have hginv : a2 * a1⁻¹ ∈ N := by
            simpa using N.inv_mem hgN
          calc
            q1 = Quotient.mk'' a1 := (Quotient.out_eq' q1).symm
            _ = Quotient.mk'' a2 := Quotient.sound' (QuotientGroup.rightRel_apply.mpr hginv)
            _ = q2 := Quotient.out_eq' q2
        have hx1Conj : x1.1 ∈ section16ConjugateSet X (a1 * a2⁻¹) := by
          refine ⟨x2.1, x2.2, ?_⟩
          have hconj := congrArg (fun z : G => a1 * z * a1⁻¹) hval
          simpa [a1, a2, mul_assoc] using hconj
        rcases hXti.1 (a1 * a2⁻¹) with hsame | hsmall
        · have hmemNorm : a1 * a2⁻¹ ∈ Subgroup.normalizer X :=
            section13_mem_normalizer_of_conjugateSet_eq hsame
          rw [hXti.2] at hmemNorm
          exact False.elim (hgNotN hmemNorm)
        · have hx1one : x1.1 = 1 := by
            simpa using hsmall ⟨x1.2, hx1Conj⟩
          exact False.elim (hX1 (hx1one ▸ x1.2))
    · intro z
      rcases z.2 with ⟨x, hxX, y, _hy, hzy⟩
      let q : Ω := Quotient.mk'' y⁻¹
      let a : G := Quotient.out q
      have hyaN : y⁻¹ * a⁻¹ ∈ N := by
        have hqa : (Quotient.mk'' a : Ω) = Quotient.mk'' y⁻¹ := by
          simp [q, a]
        exact QuotientGroup.rightRel_apply.mp (Quotient.exact' hqa)
      let n : G := y⁻¹ * a⁻¹
      have hnInvN : n⁻¹ ∈ N := N.inv_mem hyaN
      have hnInvNorm : n⁻¹ ∈ Subgroup.normalizer X := by
        simpa [hXti.2] using hnInvN
      have hx' : n⁻¹ * x * n ∈ X := by
        change ∀ z : G, z ∈ X ↔ n⁻¹ * z * (n⁻¹)⁻¹ ∈ X at hnInvNorm
        simpa [n] using (hnInvNorm x).1 hxX
      refine ⟨(q, ⟨n⁻¹ * x * n, hx'⟩), ?_⟩
      apply Subtype.ext
      calc
        ((f (q, ⟨n⁻¹ * x * n, hx'⟩)).1) = y * x * y⁻¹ := by
          simp [f, q, a, n, mul_assoc]
        _ = z := by simpa using hzy.symm
  have hsum :
      (∑ z : C0, Complex.normSq (χ z.1)) =
        ∑ qx : Ω × X0, Complex.normSq (χ (f qx).1) := by
    symm
    exact Fintype.sum_equiv (Equiv.ofBijective f hfBij)
      (fun qx : Ω × X0 => Complex.normSq (χ (f qx).1))
      (fun z : C0 => Complex.normSq (χ z.1)) (by intro qx; rfl)
  have hclass :
      (∑ qx : Ω × X0, Complex.normSq (χ (f qx).1)) =
        ∑ qx : Ω × X0, Complex.normSq (χ qx.2.1) := by
    refine Finset.sum_congr rfl ?_
    intro qx _hmem
    rcases qx with ⟨q, x⟩
    let a : G := Quotient.out q
    have hχa := hχ a⁻¹ x.1
    simpa [f, a] using congrArg Complex.normSq hχa
  have hprod :
      (∑ qx : Ω × X0, Complex.normSq (χ qx.2.1)) =
        (Nat.card Ω : ℝ) * ∑ x : X0, Complex.normSq (χ x.1) := by
    rw [Fintype.sum_prod_type]
    simp [Nat.card_eq_fintype_card, nsmul_eq_mul]
  have hcardOmega : Nat.card Ω = N.index := by
    calc
      Nat.card Ω = Nat.card (G ⧸ N) := by
        exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel N)
      _ = N.index := N.index_eq_card.symm
  calc
    Section7.supportEnergy (section16ConjugatesOfSetBySet X Set.univ) χ =
        ∑ z : C0, Complex.normSq (χ z.1) := by
      simpa [C0] using
        section13_supportEnergy_eq_sum_subtype (section16ConjugatesOfSetBySet X Set.univ) χ
    _ = ∑ qx : Ω × X0, Complex.normSq (χ (f qx).1) := hsum
    _ = ∑ qx : Ω × X0, Complex.normSq (χ qx.2.1) := hclass
    _ = (Nat.card Ω : ℝ) * ∑ x : X0, Complex.normSq (χ x.1) := hprod
    _ = (N.index : ℝ) * Section7.supportEnergy X χ := by
      rw [hcardOmega, section13_supportEnergy_eq_sum_subtype X χ]

private theorem section13_supportEnergy_conjugatesOfSetBySet_div_card_eq_div_normalizer
    {G : Type u} [Group G] [Finite G]
    {X : Set G} {N : Subgroup G}
    (hX1 : (1 : G) ∉ X)
    (hXti : section16TISubsetWithNormalizer X N)
    (χ : Section1.ClassFunction G)
    (hχ : Section1.IsClassFunction χ) :
    Section7.supportEnergy (section16ConjugatesOfSetBySet X Set.univ) χ / (Nat.card G : ℝ) =
      Section7.supportEnergy X χ / (Nat.card N : ℝ) := by
  have henergy := section13_supportEnergy_conjugatesOfSetBySet_eq_index_mul
    (X := X) (N := N) hX1 hXti χ hχ
  have hGcard : (Nat.card G : ℝ) = (Nat.card N : ℝ) * (N.index : ℝ) := by
    exact_mod_cast (Subgroup.card_mul_index (H := N)).symm
  have hNpos : (0 : ℝ) < Nat.card N := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card N)
  have hIndexNe : (N.index : ℝ) ≠ 0 := by
    exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := N))
  rw [henergy, hGcard]
  field_simp [hNpos.ne', hIndexNe]

private theorem section13_conjugatesOf_puncturedSubgroupSet_subset_nonidentity
    {G : Type u} [Group G]
    (H : Subgroup G) :
    section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ ⊆
      section16NonidentityElements (Set.univ : Set G) := by
  intro x hx
  refine ⟨Set.mem_univ x, ?_⟩
  intro hx1
  exact section13_one_not_mem_conjugatesOf_puncturedSubgroupSet H (hx1 ▸ hx)

private theorem section13_nonidentity_eq_G0_union_conjugateClosures_of_G0Data
    {G : Type u} [Group G]
    (H Q : Subgroup G) (G0 : Set G)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    section16NonidentityElements (Set.univ : Set G) =
      G0 ∪
        (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ ∪
          section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ) := by
  rw [theorem_13_9_G0Data] at hG0
  let Hc :=
    section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) (Set.univ : Set G)
  let Qc :=
    section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) (Set.univ : Set G)
  let U := Hc ∪ Qc
  have hUsub : U ⊆ section16NonidentityElements (Set.univ : Set G) := by
    intro x hx
    rcases hx with hx | hx
    · exact section13_conjugatesOf_puncturedSubgroupSet_subset_nonidentity H hx
    · exact section13_conjugatesOf_puncturedSubgroupSet_subset_nonidentity Q hx
  ext x
  constructor
  · intro hxN
    by_cases hxU : x ∈ U
    · exact Or.inr hxU
    · left
      rw [hG0]
      exact ⟨hxN, hxU⟩
  · intro hx
    rcases hx with hxG0 | hxU
    · rw [hG0] at hxG0
      exact hxG0.1
    · exact hUsub hxU

private theorem section13_G0_disjoint_conjugateClosures_of_G0Data
    {G : Type u} [Group G]
    (H Q : Subgroup G) (G0 : Set G)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    Disjoint G0
      (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ ∪
        section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ) := by
  rw [Set.disjoint_left]
  intro x hxG0 hxU
  rw [theorem_13_9_G0Data] at hG0
  rw [hG0] at hxG0
  exact hxG0.2 hxU

private theorem section13_theorem_13_10_totalCardinality_from_G0Data_and_disjoint
    {G : Type u} [Group G] [Finite G]
    (H Q : Subgroup G) (G0 : Set G)
    (hG0 : theorem_13_9_G0Data H Q G0)
    (hdisj : Disjoint
      (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ)
      (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ)) :
    (Nat.card G : ℝ) =
      1 + (Nat.card G0 : ℝ) +
        (Nat.card
          (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ) : ℝ) +
          (Nat.card
            (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ) : ℝ) := by
  let N := section16NonidentityElements (Set.univ : Set G)
  let Hc :=
    section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) (Set.univ : Set G)
  let Qc :=
    section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) (Set.univ : Set G)
  let U := Hc ∪ Qc
  have hN_union : N = G0 ∪ U := by
    simpa [N, Hc, Qc, U] using
      section13_nonidentity_eq_G0_union_conjugateClosures_of_G0Data H Q G0 hG0
  have hG0Udisj : Disjoint G0 U := by
    simpa [Hc, Qc, U] using section13_G0_disjoint_conjugateClosures_of_G0Data H Q G0 hG0
  have hUcard : Nat.card U = Nat.card Hc + Nat.card Qc := by
    have h := Set.ncard_union_eq hdisj
    dsimp [U, Hc, Qc]
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact h
  have hNcard : Nat.card N = Nat.card G0 + Nat.card U := by
    have h := Set.ncard_union_eq hG0Udisj
    dsimp [U]
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hN_union]
    exact h
  have hNcompl : N = ({1} : Set G)ᶜ := by
    ext x
    simp [N, section16NonidentityElements]
  have hGcard_nat : Nat.card G = 1 + Nat.card N := by
    have hcompl := Set.ncard_add_ncard_compl ({1} : Set G)
    have hone : ({1} : Set G).ncard = 1 := by simp
    have htmp : 1 + N.ncard = Nat.card G := by
      simpa [hNcompl, hone, add_comm] using hcompl
    have htmp' : Nat.card G = 1 + N.ncard := htmp.symm
    dsimp [N]
    rw [← Nat.card_coe_set_eq]
    exact htmp'
  rw [hGcard_nat, hNcard, hUcard]
  simp [Hc, Qc]
  ring_nf

private def theorem_13_10_disjointCardinalitySourceData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax H Q : Subgroup G)
    (G0 : Set G) : Prop :=
  (Nat.card G : ℝ) =
    1 + (Nat.card G0 : ℝ) +
      (Nat.card
        (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ) : ℝ) +
        (Nat.card
          (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ) : ℝ) ∧
  (Nat.card
      (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ) : ℝ) =
    (Nat.card G : ℝ) *
      ((Nat.card (Section7.puncturedSubgroupSet H) : ℝ) / (Nat.card Smax : ℝ)) ∧
  (Nat.card
      (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ) : ℝ) =
    (Nat.card G : ℝ) *
      ((Nat.card (Section7.puncturedSubgroupSet Q) : ℝ) / (Nat.card Tmax : ℝ))

private theorem section13_theorem_13_10_scaledDisjointCardinality_from_sourceData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax H Q : Subgroup G)
    (G0 : Set G)
    (hdata : theorem_13_10_disjointCardinalitySourceData Smax Tmax H Q G0) :
    (Nat.card G : ℝ) =
      1 + (Nat.card G0 : ℝ) +
        (Nat.card G : ℝ) *
          ((Nat.card (Section7.puncturedSubgroupSet H) : ℝ) /
            (Nat.card Smax : ℝ)) +
        (Nat.card G : ℝ) *
          ((Nat.card (Section7.puncturedSubgroupSet Q) : ℝ) /
            (Nat.card Tmax : ℝ)) := by
  rcases hdata with ⟨hcard, hH, hQ⟩
  calc
    (Nat.card G : ℝ) =
        1 + (Nat.card G0 : ℝ) +
          (Nat.card
            (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ) : ℝ) +
            (Nat.card
              (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ) : ℝ) := hcard
    _ = 1 + (Nat.card G0 : ℝ) +
        (Nat.card G : ℝ) *
          ((Nat.card (Section7.puncturedSubgroupSet H) : ℝ) / (Nat.card Smax : ℝ)) +
        (Nat.card G : ℝ) *
          ((Nat.card (Section7.puncturedSubgroupSet Q) : ℝ) / (Nat.card Tmax : ℝ)) := by
          rw [hH, hQ]

private theorem section13_theorem_13_10_H_eq_fitting_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C) :
    H = section8FittingSubgroup Smax := by
  rcases hsource with
    ⟨_hcase, hptypeS, _hptypeT, _hp, _hq, hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hnotation⟩
  calc
    H = P ⊔ C := hH
    _ = P ⊔ subgroupCentralizerIn U P := by rw [hC]
    _ = section8FittingSubgroup Smax := by
      exact (Section8.theorem_8_5_a Smax P U W1 W2 hptypeS).symm

private theorem section13_theorem_13_10_Q_eq_fitting_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hD : D = ⊥) :
    Q = section8FittingSubgroup Tmax := by
  rcases hsource with
    ⟨_hcase, _hptypeS, hptypeT, _hp, _hq, _hC, hDsrc, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hnotation⟩
  calc
    Q = Q ⊔ D := by rw [hD, sup_bot_eq]
    _ = Q ⊔ subgroupCentralizerIn V Q := by rw [hDsrc]
    _ = section8FittingSubgroup Tmax := by
      exact (Section8.theorem_8_5_a Tmax Q V W2 W1 hptypeT).symm

private theorem section13_theorem_13_10_fitting_punctured_tiSet_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    section16TISubset
      (section16NonidentityElements (section8FittingSubgroup Smax : Set G)) := by
  rcases
    section13_theorem_13_2_case_9_7_hypothesis92SourceCondition_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with
    ⟨_hUne, _hW1prime, hFittingTI⟩
  exact hFittingTI

private theorem section13_theorem_13_10_fitting_punctured_normalizer_eq_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Subgroup.normalizer
      (section16NonidentityElements (section8FittingSubgroup Smax : Set G)) = Smax := by
  classical
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      _hsource
  haveI : IsMinCE G := hMin
  rcases _hsource with
    ⟨hcase, hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hnotation⟩
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne_case, _hW2ne_case, _hWnorm, hSmax, _hTmax,
      _hSMF, _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hSTeq, _hIIorT,
      _hStypes, _hTtypes, _hclass⟩
  rcases hptypeS with
    ⟨_hSMFsrc, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hPnotCyc, _hSecondLe, hFittingEq, _hFittingLeD,
      hW2le, _hW2cyc, hW2ne, _hCent, _hHatW⟩
  have hW2leF : W2 ≤ section8FittingSubgroup Smax := by
    intro x hx
    rw [← hFittingEq]
    exact (show P ≤ P ⊔ subgroupCentralizerIn Smax P from le_sup_left)
      ((hW2le hx).1)
  have hW2_card_ne_one : Nat.card W2 ≠ 1 := by
    intro hcard
    exact hW2ne ((Subgroup.eq_bot_iff_card (H := W2)).2 hcard)
  rcases Nat.exists_prime_and_dvd (n := Nat.card W2) hW2_card_ne_one with
    ⟨r, hrprime, hrdiv⟩
  let rP : Nat.Primes := ⟨r, hrprime⟩
  have hrW2 : rP ∈ subgroupPrimeSet W2 := by
    rw [subgroupPrimeSet]
    change r ∣ Nat.card W2
    exact hrdiv
  have hrF : rP ∈ subgroupPrimeSet (section8FittingSubgroup Smax) :=
    section8_subgroupPrimeSet_mono hW2leF hrW2
  have hSmax8 : Smax ∈ section8MaximalSubgroups G := by
    simpa [section8MaximalSubgroups, section9MaximalSubgroups] using hSmax
  have hnormF : Subgroup.normalizer (section8FittingSubgroup Smax : Set G) = Smax :=
    section8_normalizer_fittingSubgroup_eq (G := G) (M := Smax) (q := rP) hSmax8 hrF
  have hsharp_norm :
      Subgroup.normalizer
        (section16NonidentityElements (section8FittingSubgroup Smax : Set G)) =
          Subgroup.normalizer (section8FittingSubgroup Smax : Set G) := by
    apply le_antisymm
    · intro g hg
      change ∀ x : G,
        x ∈ section16NonidentityElements (section8FittingSubgroup Smax : Set G) ↔
          g * x * g⁻¹ ∈ section16NonidentityElements
            (section8FittingSubgroup Smax : Set G) at hg
      change ∀ x : G, x ∈ section8FittingSubgroup Smax ↔
        g * x * g⁻¹ ∈ section8FittingSubgroup Smax
      intro x
      constructor
      · intro hxH
        by_cases hx1 : x = 1
        · simp [hx1]
        · have hxSharp :
            x ∈ section16NonidentityElements (section8FittingSubgroup Smax : Set G) :=
            ⟨hxH, hx1⟩
          exact ((hg x).1 hxSharp).1
      · intro hxConjH
        by_cases hx1 : x = 1
        · simp [hx1]
        · have hxConj_ne : g * x * g⁻¹ ≠ 1 := by
            intro h
            apply hx1
            have h' := congrArg (fun y : G => g⁻¹ * y * g) h
            simpa [mul_assoc] using h'
          have hxConjSharp :
            g * x * g⁻¹ ∈
              section16NonidentityElements (section8FittingSubgroup Smax : Set G) :=
            ⟨hxConjH, hxConj_ne⟩
          exact ((hg x).2 hxConjSharp).1
    · intro g hg
      change ∀ x : G, x ∈ section8FittingSubgroup Smax ↔
        g * x * g⁻¹ ∈ section8FittingSubgroup Smax at hg
      change ∀ x : G,
        x ∈ section16NonidentityElements (section8FittingSubgroup Smax : Set G) ↔
          g * x * g⁻¹ ∈ section16NonidentityElements
            (section8FittingSubgroup Smax : Set G)
      intro x
      constructor
      · intro hx
        refine ⟨(hg x).1 hx.1, ?_⟩
        intro h
        exact hx.2 (by
          have h' := congrArg (fun y : G => g⁻¹ * y * g) h
          simpa [mul_assoc] using h')
      · intro hx
        refine ⟨(hg x).2 hx.1, ?_⟩
        intro hx1
        exact hx.2 (by simp [hx1])
  simpa [hsharp_norm] using hnormF

public theorem section13_theorem_13_10_fitting_punctured_tiNormalizer_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    section16TISubsetWithNormalizer
      (section16NonidentityElements (section8FittingSubgroup Smax : Set G)) Smax := by
  exact ⟨
    section13_theorem_13_10_fitting_punctured_tiSet_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource,
    section13_theorem_13_10_fitting_punctured_normalizer_eq_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource⟩

private theorem section13_theorem_13_10_fitting_punctured_ti_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    section16TISubset
      (section16NonidentityElements (section8FittingSubgroup Smax : Set G)) :=
  section13_theorem_13_10_fitting_punctured_tiSet_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d hsource

private theorem section13_theorem_13_10_Hsharp_ti_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C) :
    section16TISubset (Section7.puncturedSubgroupSet H) := by
  have hHfit := section13_theorem_13_10_H_eq_fitting_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
    p q u v c d hsource hH
  have hfitTI := section13_theorem_13_10_fitting_punctured_ti_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d hsource
  simpa [hHfit, Section7.puncturedSubgroupSet, section16NonidentityElements] using hfitTI

public theorem section13_theorem_13_10_Qsharp_ti_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hD : D = ⊥) :
    section16TISubset (Section7.puncturedSubgroupSet Q) := by
  have hsourceT := section13_hypothesis_13_1_sourceData_swap hsource
  have hQfit := section13_theorem_13_10_Q_eq_fitting_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d hsource hD
  have hfitTI := section13_theorem_13_10_fitting_punctured_ti_of_sourceContext
    Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
    q p v u d c hsourceT
  simpa [hQfit, Section7.puncturedSubgroupSet, section16NonidentityElements] using hfitTI

private theorem section13_le_normalizer_puncturedSubgroupSet_of_le_normalizer
    {G : Type u} [Group G]
    (H K : Subgroup G)
    (hK : K ≤ Subgroup.normalizer (H : Set G)) :
    K ≤ Subgroup.normalizer (Section7.puncturedSubgroupSet H) := by
  intro k hk y
  have hnorm : k ∈ Subgroup.normalizer (H : Set G) := hK hk
  change ∀ z : G, z ∈ H ↔ k * z * k⁻¹ ∈ H at hnorm
  constructor
  · intro hy
    refine ⟨(hnorm y).1 hy.1, ?_⟩
    intro hconj
    apply hy.2
    have hback := congrArg (fun z : G => k⁻¹ * z * k) hconj
    simpa [mul_assoc] using hback
  · intro hy
    refine ⟨(hnorm y).2 hy.1, ?_⟩
    intro hy1
    apply hy.2
    simp [hy1]

private theorem section13_theorem_13_10_Smax_le_Hsharp_normalizer_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C) :
    Smax ≤ Subgroup.normalizer (Section7.puncturedSubgroupSet H) := by
  have hHfit := section13_theorem_13_10_H_eq_fitting_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
    p q u v c d hsource hH
  have hSleNorm : Smax ≤ Subgroup.normalizer (H : Set G) := by
    simpa [hHfit] using section10_le_normalizer_fitting Smax
  exact section13_le_normalizer_puncturedSubgroupSet_of_le_normalizer H Smax hSleNorm

private theorem section13_theorem_13_10_Hsharp_normalizer_le_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C)
    (_hG0 : theorem_13_9_G0Data H Q G0) :
    Subgroup.normalizer (Section7.puncturedSubgroupSet H) ≤ Smax := by
  have hHfit := section13_theorem_13_10_H_eq_fitting_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
    p q u v c d hsource hH
  have hfitTINorm :=
    section13_theorem_13_10_fitting_punctured_tiNormalizer_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  have hnorm :
      Subgroup.normalizer (Section7.puncturedSubgroupSet H) = Smax := by
    simpa [hHfit, Section7.puncturedSubgroupSet, section16NonidentityElements] using
      hfitTINorm.2
  exact le_of_eq hnorm

private theorem section13_theorem_13_10_Hsharp_normalizer_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    Subgroup.normalizer (Section7.puncturedSubgroupSet H) = Smax := by
  exact le_antisymm
    (section13_theorem_13_10_Hsharp_normalizer_le_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT
      p q u v c d hsource hH hG0)
    (section13_theorem_13_10_Smax_le_Hsharp_normalizer_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      p q u v c d hsource hH)

private theorem section13_theorem_13_10_Tmax_le_Qsharp_normalizer_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hD : D = ⊥) :
    Tmax ≤ Subgroup.normalizer (Section7.puncturedSubgroupSet Q) := by
  have hQfit := section13_theorem_13_10_Q_eq_fitting_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d hsource hD
  have hTleNorm : Tmax ≤ Subgroup.normalizer (Q : Set G) := by
    simpa [hQfit] using section10_le_normalizer_fitting Tmax
  exact section13_le_normalizer_puncturedSubgroupSet_of_le_normalizer Q Tmax hTleNorm

public theorem section13_theorem_13_10_Qsharp_normalizer_le_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hD : D = ⊥) :
    Subgroup.normalizer (Section7.puncturedSubgroupSet Q) ≤ Tmax := by
  have hsourceT := section13_hypothesis_13_1_sourceData_swap hsource
  have hQfit := section13_theorem_13_10_Q_eq_fitting_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d hsource hD
  have hfitTINorm :=
    section13_theorem_13_10_fitting_punctured_tiNormalizer_of_sourceContext
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
      q p v u d c hsourceT
  have hnorm :
      Subgroup.normalizer (Section7.puncturedSubgroupSet Q) = Tmax := by
    simpa [hQfit, Section7.puncturedSubgroupSet, section16NonidentityElements] using
      hfitTINorm.2
  exact le_of_eq hnorm

private theorem section13_theorem_13_10_Qsharp_normalizer_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hD : D = ⊥)
    (_hH : H = P ⊔ C)
    (_hG0 : theorem_13_9_G0Data H Q G0) :
    Subgroup.normalizer (Section7.puncturedSubgroupSet Q) = Tmax := by
  exact le_antisymm
    (section13_theorem_13_10_Qsharp_normalizer_le_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource hD)
    (section13_theorem_13_10_Tmax_le_Qsharp_normalizer_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource hD)

private theorem section13_theorem_13_10_Hsharp_tiNormalizer_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    section16TISubsetWithNormalizer (Section7.puncturedSubgroupSet H) Smax := by
  exact
    ⟨section13_theorem_13_10_Hsharp_ti_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        p q u v c d hsource hH,
      section13_theorem_13_10_Hsharp_normalizer_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT
        p q u v c d hsource hH hG0⟩

private theorem section13_theorem_13_10_Qsharp_tiNormalizer_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hD : D = ⊥)
    (hH : H = P ⊔ C)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    section16TISubsetWithNormalizer (Section7.puncturedSubgroupSet Q) Tmax := by
  exact
    ⟨section13_theorem_13_10_Qsharp_ti_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsource hD,
      section13_theorem_13_10_Qsharp_normalizer_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT
        p q u v c d hsource hD hH hG0⟩

private theorem section13_theorem_13_10_HConjugateClosure_supportEnergy_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hχ : Section1.IsClassFunction χ)
    (hH : H = P ⊔ C)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    Section7.supportEnergy
        (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ) χ /
        (Nat.card G : ℝ) =
      Section7.supportEnergy (Section7.puncturedSubgroupSet H) χ /
        (Nat.card Smax : ℝ) := by
  exact section13_supportEnergy_conjugatesOfSetBySet_div_card_eq_div_normalizer
    (X := Section7.puncturedSubgroupSet H) (N := Smax)
    (section13_one_not_mem_puncturedSubgroupSet H)
    (section13_theorem_13_10_Hsharp_tiNormalizer_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT
      p q u v c d hsource hH hG0)
    χ hχ

private theorem section13_theorem_13_10_QConjugateClosure_supportEnergy_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hχ : Section1.IsClassFunction χ)
    (hD : D = ⊥)
    (hH : H = P ⊔ C)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    Section7.supportEnergy
        (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ) χ /
        (Nat.card G : ℝ) =
      Section7.supportEnergy (Section7.puncturedSubgroupSet Q) χ /
        (Nat.card Tmax : ℝ) := by
  exact section13_supportEnergy_conjugatesOfSetBySet_div_card_eq_div_normalizer
    (X := Section7.puncturedSubgroupSet Q) (N := Tmax)
    (section13_one_not_mem_puncturedSubgroupSet Q)
    (section13_theorem_13_10_Qsharp_tiNormalizer_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT
      p q u v c d hsource hD hH hG0)
    χ hχ

private theorem section13_theorem_13_10_lambdaTotalNormPieceSourceData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hlam_mem : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    theorem_13_10_lambdaTotalNormPieceSourceData Smax H lamτ := by
  classical
  have hsourceOrig := hsource
  rcases h6hyp with ⟨hH, hlam_irred, _hlam_deg, _hlam_linear, hlamτ_eq⟩
  have hlam_self : Section1.scalarProduct Smax lam lam = 1 :=
    section13_scalarProduct_self_of_irreducibleCharacter hlam_irred
  have hlamτ_self : Section1.scalarProduct G lamτ lamτ = 1 := by
    rw [hlamτ_eq]
    calc
      Section1.scalarProduct G (τ1 lam) (τ1 lam) =
          Section1.scalarProduct Smax lam lam :=
        Section5.isCFLinearIsometryOnSpan_apply_of_mem hcoh.1 hlam_mem hlam_mem
      _ = 1 := hlam_self
  have hlamτ_cfNorm : Section5.cfNormSq lamτ = 1 := by
    unfold Section5.cfNormSq
    rw [hlamτ_self]
    simp
  have htotal :
      Section7.supportEnergy Set.univ lamτ / (Nat.card G : ℝ) ≤ 1 := by
    rw [section13_supportEnergy_univ_div_card_eq_cfNormSq, hlamτ_cfNorm]
  have hlamτ_virtual : Theory.Character.IsVirtualCharacter lamτ := by
    rw [hlamτ_eq]
    exact hcoh.2.1 lam (Section5.integerSpan_of_mem Sfam hlam_mem)
  have hlamτ_signed : Section3.IsSignedIrreducibleCharacter lamτ :=
    Section5.signed_irreducible_of_virtual_norm_one_pf59 hlamτ_virtual hlamτ_self
  have hsingle : 1 ≤ Complex.normSq (lamτ 1) :=
    section13_one_le_normSq_one_of_signedIrreducible hlamτ_signed
  have hclass : Section1.IsClassFunction lamτ :=
    section13_isClassFunction_of_signedIrreducible hlamτ_signed
  have horbit :=
    section13_theorem_13_10_HConjugateClosure_supportEnergy_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT lamτ
      p q u v c d hsourceOrig hclass hH hG0
  exact ⟨htotal, hsingle, horbit⟩

private theorem section13_theorem_13_10_lambdaTotalNormPieces_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hlam_mem : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    1 ≥ 1 / (Nat.card G : ℝ) +
      Section7.supportEnergy G0 lamτ / (Nat.card G : ℝ) +
        Section7.supportEnergy (Section7.puncturedSubgroupSet H) lamτ /
          (Nat.card Smax : ℝ) := by
  exact section13_theorem_13_10_lambdaTotalNormPieces_from_sourceData
    Smax H Q G0 lamτ hG0
    (section13_theorem_13_10_lambdaTotalNormPieceSourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hcoh hnotation
      hlam_mem h6hyp hG0)

private theorem section13_theorem_13_10_lambdaTotalNormInequality_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hlam_mem : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    1 ≥ 1 / (Nat.card G : ℝ) +
      Section7.supportEnergy G0 lamτ / (Nat.card G : ℝ) +
        1 - Complex.normSq (lam 1) / (Nat.card Smax : ℝ) := by
  -- TeX `(13.10.1)`: decompose the total norm of `λ^τ₁` over `{1}`,
  -- `G₀`, and the conjugates of `H#`, then apply `(13.6)`.
  have hpieces :=
    section13_theorem_13_10_lambdaTotalNormPieces_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hcoh hnotation
      hlam_mem h6hyp hG0
  have h6 := theorem_13_6 Smax Tmax W W1 W2 P Q U V C D H
    Sfam Tfam τS τ1 τT lam lamτ p q u v c d hsource hcoh hlam_mem h6hyp
  exact section13_theorem_13_10_lambdaTotalNormInequality_from_pieces
    Smax H G0 lam lamτ hpieces h6

private theorem section13_disjoint_conjugatesOfSetBySet_of_left_disjoint
    {G : Type u} [Group G]
    (X Y : Set G)
    (hdisj : Disjoint X (section16ConjugatesOfSetBySet Y Set.univ)) :
    Disjoint (section16ConjugatesOfSetBySet X Set.univ)
      (section16ConjugatesOfSetBySet Y Set.univ) := by
  rw [Set.disjoint_left] at hdisj ⊢
  intro z hzX hzY
  rcases hzX with ⟨x, hxX, g, _hg, hzXeq⟩
  rcases hzY with ⟨y, hyY, k, _hk, hzYeq⟩
  have hxY : x ∈ section16ConjugatesOfSetBySet Y Set.univ := by
    refine ⟨y, hyY, g⁻¹ * k, Set.mem_univ _, ?_⟩
    calc
      x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = g⁻¹ * (k * y * k⁻¹) * g := by rw [← hzXeq, hzYeq]
      _ = (g⁻¹ * k) * y * (g⁻¹ * k)⁻¹ := by group
  exact hdisj hxX hxY

public theorem section13_le_centralizer_sup_of_le_centralizers
    {G : Type u} [Group G]
    {R A B : Subgroup G}
    (hRA : R ≤ Subgroup.centralizer (A : Set G))
    (hRB : R ≤ Subgroup.centralizer (B : Set G)) :
    R ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro r hr
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  intro x hx
  rcases hx with hxA | hxB
  · exact Subgroup.mem_centralizer_iff.mp (hRA hr) x hxA
  · exact Subgroup.mem_centralizer_iff.mp (hRB hr) x hxB


private theorem section13_centralizer_singleton_le_normalizer_of_ti
    {G : Type u} [Group G]
    {X : Set G} {x : G}
    (hTI : section16TISubset X)
    (hx : x ∈ X)
    (hxne : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer X := by
  intro c hc
  have hxConj : x ∈ section16ConjugateSet X c := by
    refine ⟨x, hx, ?_⟩
    have hcomm : c * x = x * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hc
    have hfix : c * x * c⁻¹ = x := by
      rw [hcomm]
      simp [mul_assoc]
    exact hfix.symm
  rcases hTI c with hsame | hdisj
  · exact section13_mem_normalizer_of_conjugateSet_eq hsame
  · have hxone : x ∈ ({1} : Set G) := hdisj ⟨hx, hxConj⟩
    exact False.elim (hxne (by simpa using hxone))

public theorem section13_normalizer_le_of_punctured_subset_ti
    {G : Type u} [Group G]
    {H N : Subgroup G} {X : Set G}
    (hTI : section16TISubset X)
    (hNorm : Subgroup.normalizer X ≤ N)
    (hHne : H ≠ ⊥)
    (hHsharp : Section7.puncturedSubgroupSet H ⊆ X) :
    Subgroup.normalizer (H : Set G) ≤ N := by
  intro g hg
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hHne with ⟨x, hxne⟩
  have hxH : (x : G) ∈ H := x.2
  have hxneG : (x : G) ≠ 1 := by
    intro hx1
    exact hxne (Subtype.ext hx1)
  have hxX : (x : G) ∈ X := hHsharp ⟨hxH, hxneG⟩
  have hxConjH : g * (x : G) * g⁻¹ ∈ H := by
    change ∀ y : G, y ∈ H ↔ g * y * g⁻¹ ∈ H at hg
    exact (hg (x : G)).1 hxH
  have hxConjNe : g * (x : G) * g⁻¹ ≠ 1 := by
    intro hxConjOne
    apply hxneG
    have hback := congrArg (fun z : G => g⁻¹ * z * g) hxConjOne
    simpa [mul_assoc] using hback
  have hxConjX : g * (x : G) * g⁻¹ ∈ X := hHsharp ⟨hxConjH, hxConjNe⟩
  have hxConjInConj : g * (x : G) * g⁻¹ ∈ section16ConjugateSet X g := by
    exact ⟨x, hxX, rfl⟩
  rcases hTI g with hsame | hsmall
  · exact hNorm (section13_mem_normalizer_of_conjugateSet_eq hsame)
  · have hxone : g * (x : G) * g⁻¹ ∈ ({1} : Set G) :=
      hsmall ⟨hxConjX, hxConjInConj⟩
    exact False.elim (hxConjNe (by simpa using hxone))


private theorem section13_conjBy_le_centralizer_singleton_of_mem_comm
    {G : Type u} [Group G]
    (Q : Subgroup G) [IsMulCommutative Q]
    {x y g : G}
    (hy : y ∈ Q)
    (hxy : x = g * y * g⁻¹) :
    Q.conjBy g ≤ Subgroup.centralizer ({x} : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [hxy]
  rw [Subgroup.conjBy, Subgroup.mem_map] at hz
  rcases hz with ⟨q0, hq0, hz⟩
  rw [← hz]
  have hcomm : q0 * y = y * q0 :=
    setLike_mul_comm (s := Q) hq0 hy
  calc
    (g * q0 * g⁻¹) * (g * y * g⁻¹) = g * (q0 * y) * g⁻¹ := by group
    _ = g * (y * q0) * g⁻¹ := by rw [hcomm]
    _ = (g * y * g⁻¹) * (g * q0 * g⁻¹) := by group

private theorem section13_theorem_13_10_Hsharp_centralizer_le_Smax_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C)
    {x : G} (hx : x ∈ Section7.puncturedSubgroupSet H) :
    Subgroup.centralizer ({x} : Set G) ≤ Smax := by
  have hTI : section16TISubset (Section7.puncturedSubgroupSet H) :=
    section13_theorem_13_10_Hsharp_ti_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      p q u v c d hsource hH
  have hcentNorm :
      Subgroup.centralizer ({x} : Set G) ≤
        Subgroup.normalizer (Section7.puncturedSubgroupSet H) :=
    section13_centralizer_singleton_le_normalizer_of_ti hTI hx hx.2
  have hHfit := section13_theorem_13_10_H_eq_fitting_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
    p q u v c d hsource hH
  have hfitTINorm :=
    section13_theorem_13_10_fitting_punctured_tiNormalizer_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  have hnorm :
      Subgroup.normalizer (Section7.puncturedSubgroupSet H) = Smax := by
    simpa [hHfit, Section7.puncturedSubgroupSet, section16NonidentityElements] using
      hfitTINorm.2
  exact hcentNorm.trans (le_of_eq hnorm)

private theorem section13_q_dvd_index_of_qpow_subgroup_le_hall_prime
    {G : Type u} [Group G] [Finite G]
    {S W R : Subgroup G} {p q : ℕ}
    (hWleS : W ≤ S)
    (hWcard : Nat.card W = q)
    (hRleS : R ≤ S)
    (hRcard : Nat.card R = q ^ p)
    (hqPrime : Nat.Prime q)
    (hpPrime : Nat.Prime p) :
    q ∣ (W.subgroupOf S).index := by
  have hRsub_card : Nat.card (R.subgroupOf S) = q ^ p := by
    rw [natCard_subgroupOf_eq R S hRleS, hRcard]
  have hRsub_dvd_S : q ^ p ∣ Nat.card S := by
    have hdiv : Nat.card (R.subgroupOf S) ∣ Nat.card S :=
      Subgroup.card_subgroup_dvd_card (R.subgroupOf S)
    rwa [hRsub_card] at hdiv
  have hq2_dvd_qp : q ^ 2 ∣ q ^ p :=
    Nat.pow_dvd_pow q hpPrime.two_le
  have hq2_dvd_S : q ^ 2 ∣ Nat.card S := hq2_dvd_qp.trans hRsub_dvd_S
  have hWsub_card : Nat.card (W.subgroupOf S) = q := by
    rw [natCard_subgroupOf_eq W S hWleS, hWcard]
  have hS_card : Nat.card S = (W.subgroupOf S).index * q := by
    calc
      Nat.card S = (W.subgroupOf S).index * Nat.card (W.subgroupOf S) :=
        (Subgroup.index_mul_card (H := W.subgroupOf S)).symm
      _ = (W.subgroupOf S).index * q := by rw [hWsub_card]
  have hq2_dvd_idx_mul : q ^ 2 ∣ (W.subgroupOf S).index * q := by
    rwa [hS_card] at hq2_dvd_S
  have hq_mul_dvd : q * q ∣ q * (W.subgroupOf S).index := by
    simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hq2_dvd_idx_mul
  exact Nat.dvd_of_mul_dvd_mul_left hqPrime.pos hq_mul_dvd

private theorem section13_theorem_13_10_Q_conjBy_not_le_Smax_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (g : G) :
    ¬ Q.conjBy g ≤ Smax := by
  intro hQgS
  have hsourceOrig := hsource
  rcases hsource with
    ⟨_hcase, hptypeS, _hptypeT, _hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hptypeS with
    ⟨_hMF, _hW1cyc, _hW1ne, hW1Hall, _hScomp, _hUle, _hUnil, _hW1norm,
      _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  rcases hW1Hall with ⟨hW1leS, hW1HallSub⟩
  have h4 := theorem_13_4 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsourceOrig h10
  rcases h4 with ⟨_hD, hcaseT, _hvNat⟩
  have hqPrime : Nat.Prime q :=
    Section9.case_9_7_b_p_prime_sec9 hcaseT
  have hpPrime : Nat.Prime p :=
    Section9.case_9_7_b_q_prime_sec9 hcaseT
  have hQcard : Nat.card Q = q ^ p :=
    section13_theorem_13_10_q_card_formula_of_hypothesis
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig h10
  have hQgcard : Nat.card (Q.conjBy g) = q ^ p := by
    rw [section11_card_conjBy (G := G) Q g, hQcard]
  have hq_dvd_index :
      q ∣ (W1.subgroupOf Smax).index :=
    section13_q_dvd_index_of_qpow_subgroup_le_hall_prime
      (S := Smax) (W := W1) (R := Q.conjBy g)
      (p := p) (q := q) hW1leS hq_card.symm hQgS hQgcard
      hqPrime hpPrime
  have hq_mem : (⟨q, hqPrime⟩ : Nat.Primes) ∈ subgroupPrimeSet W1 := by
    change q ∣ Nat.card W1
    rw [← hq_card]
  have hq_not_index : ¬ q ∣ (W1.subgroupOf Smax).index := by
    intro hqidx
    exact (hW1HallSub.p_in_pi_of_p_dvd_index ⟨q, hqPrime⟩ hqidx) hq_mem
  exact hq_not_index hq_dvd_index

private theorem section13_theorem_13_10_Hsharp_disjoint_Qsharp_conjugates_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hD : D = ⊥)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hH : H = P ⊔ C)
    : Disjoint (Section7.puncturedSubgroupSet H)
      (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ) := by
  rw [Set.disjoint_left]
  intro x hxH hxQ
  rcases hxQ with ⟨y, hyQ, g, _hg, hx_eq⟩
  have hsourceT := section13_hypothesis_13_1_sourceData_swap hsource
  have h2T := theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
    Tfam Sfam τT τS q p v u d c hsourceT
  rcases h2T with
    ⟨_hMF, _hType, _hTypeIf, _hVcomm, _hFrob, hQelem, _hQcard,
      _hvBound, _hcoh, _hTI, _hTau, _hNorm⟩
  letI : IsMulCommutative Q := IsElementaryAbelian.toIsMulCommutative q
  have hQcent : Q.conjBy g ≤ Subgroup.centralizer ({x} : Set G) :=
    section13_conjBy_le_centralizer_singleton_of_mem_comm Q hyQ.1 hx_eq
  have hcentS : Subgroup.centralizer ({x} : Set G) ≤ Smax :=
    section13_theorem_13_10_Hsharp_centralizer_le_Smax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      p q u v c d hsource hH hxH
  exact (section13_theorem_13_10_Q_conjBy_not_le_Smax_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d hsource h10 g) (hQcent.trans hcentS)

private theorem section13_theorem_13_10_disjointConjugateClosures_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hD : D = ⊥)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hH : H = P ⊔ C) :
    Disjoint
      (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ)
      (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ) := by
  exact section13_disjoint_conjugatesOfSetBySet_of_left_disjoint
    (Section7.puncturedSubgroupSet H) (Section7.puncturedSubgroupSet Q)
    (section13_theorem_13_10_Hsharp_disjoint_Qsharp_conjugates_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      p q u v c d hsource hD h10 hH)

private theorem section13_theorem_13_10_etaTotalNormPieceSourceData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (eta10 : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (heta10 : eta10 = η 1 0)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hD : D = ⊥)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    theorem_13_10_etaTotalNormPieceSourceData Smax Tmax H Q eta10 := by
  classical
  have hsourceOrig := hsource
  rcases hsource with
    ⟨hcaseB, _hptypeS, _hptypeT, hp_card, hq_card, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hcaseB with
    ⟨_hWprod, _hWcyc, hW1ne, _hW2ne, _hWhat, _hSmax, _hTmax, _hSMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hII,
      _hStype, _hTtype, _hclass⟩
  rcases hnotation with
    ⟨homegaData, hσmap, heta, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμeq, _hνeq, _hμsum,
      _hνsum⟩
  rcases homegaData with ⟨_h31, _hqpos, _hppos, ωFin, hωFin, hωeq⟩
  have h1q : 1 < q := by
    have hW1card : 1 < Nat.card W1 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W1)).2 hW1ne
    simpa [hq_card] using hW1card
  have h0p : 0 < p := by
    simpa [hp_card] using (Nat.card_pos (α := W2))
  let i1 : Fin q := ⟨1, h1q⟩
  let j0 : Fin p := ⟨0, h0p⟩
  have hω_irred : Section1.IsIrreducibleCharacterOnGroup (ω 1 0) := by
    rw [hωeq 1 0 h1q h0p]
    exact hωFin.irreducible i1 j0
  have hω_class : Section1.IsClassFunction (ω 1 0) := by
    rw [hωeq 1 0 h1q h0p]
    exact hωFin.is_class i1 j0
  have hvirtW : Theory.Character.IsVirtualCharacter (ω 1 0) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hω_irred
  have hvirtG : Theory.Character.IsVirtualCharacter (σ (ω 1 0)) :=
    hσmap.2.1 (ω 1 0) hvirtW
  have hself : Section1.scalarProduct G (σ (ω 1 0)) (σ (ω 1 0)) = 1 := by
    calc
      Section1.scalarProduct G (σ (ω 1 0)) (σ (ω 1 0)) =
          Section1.scalarProduct W (ω 1 0) (ω 1 0) :=
        hσmap.1 (ω 1 0) (ω 1 0) hω_class hω_class
      _ = Section1.scalarProduct W (ωFin i1 j0) (ωFin i1 j0) := by
        rw [hωeq 1 0 h1q h0p]
      _ = 1 := by
        simpa using hωFin.orthonormal (i1, j0) (i1, j0)
  have heta10_sigma : eta10 = σ (ω 1 0) := by
    calc
      eta10 = η 1 0 := heta10
      _ = σ (ω 1 0) := heta 1 0 h1q h0p
  have heta_signed : Section3.IsSignedIrreducibleCharacter eta10 := by
    rw [heta10_sigma]
    exact Section5.signed_irreducible_of_virtual_norm_one_pf59 hvirtG hself
  have heta_cfNorm : Section5.cfNormSq eta10 = 1 := by
    rw [heta10_sigma]
    unfold Section5.cfNormSq
    rw [hself]
    simp
  have htotal :
      Section7.supportEnergy Set.univ eta10 / (Nat.card G : ℝ) ≤ 1 := by
    rw [section13_supportEnergy_univ_div_card_eq_cfNormSq, heta_cfNorm]
  have hsingle : 1 ≤ Complex.normSq (eta10 1) :=
    section13_one_le_normSq_one_of_signedIrreducible heta_signed
  have hclass : Section1.IsClassFunction eta10 :=
    section13_isClassFunction_of_signedIrreducible heta_signed
  exact ⟨htotal, hsingle,
    section13_theorem_13_10_disjointConjugateClosures_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      p q u v c d hsourceOrig hD h10 hH,
    section13_theorem_13_10_HConjugateClosure_supportEnergy_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT eta10
      p q u v c d hsourceOrig hclass hH hG0,
    section13_theorem_13_10_QConjugateClosure_supportEnergy_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT eta10
      p q u v c d hsourceOrig hclass hD hH hG0⟩

private theorem section13_theorem_13_10_etaTotalNormPieces_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (eta10 : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (heta10 : eta10 = η 1 0)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hD : D = ⊥)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    1 ≥ 1 / (Nat.card G : ℝ) +
      Section7.supportEnergy G0 eta10 / (Nat.card G : ℝ) +
        Section7.supportEnergy (Section7.puncturedSubgroupSet H) eta10 /
          (Nat.card Smax : ℝ) +
          Section7.supportEnergy (Section7.puncturedSubgroupSet Q) eta10 /
            (Nat.card Tmax : ℝ) := by
  exact section13_theorem_13_10_etaTotalNormPieces_from_sourceData
    Smax Tmax H Q G0 eta10 hG0
    (section13_theorem_13_10_etaTotalNormPieceSourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT eta10
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH heta10 h10 hD hG0)

private theorem section13_theorem_13_10_etaTotalNormSourceFields_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (eta10 : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (heta10 : eta10 = η 1 0)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hD : D = ⊥)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    (1 ≥ 1 / (Nat.card G : ℝ) +
      Section7.supportEnergy G0 eta10 / (Nat.card G : ℝ) +
        Section7.supportEnergy (Section7.puncturedSubgroupSet H) eta10 /
          (Nat.card Smax : ℝ) +
          Section7.supportEnergy (Section7.puncturedSubgroupSet Q) eta10 /
            (Nat.card Tmax : ℝ)) ∧
      squareSumLowerBound (Section7.puncturedSubgroupSet Q) eta10
        ((Nat.card (ambientDerivedSubgroup Tmax) : ℝ) - (v : ℝ) ^ 2) := by
  exact ⟨
    section13_theorem_13_10_etaTotalNormPieces_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT eta10
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH heta10 h10 hD hG0,
    section13_theorem_13_10_etaQSharpLowerBound_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT eta10
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH heta10 hD hG0⟩

private theorem section13_theorem_13_10_etaTotalNormInequality_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (eta10 : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (heta10 : eta10 = η 1 0)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hD : D = ⊥)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    1 ≥ 1 / (Nat.card G : ℝ) +
      Section7.supportEnergy G0 eta10 / (Nat.card G : ℝ) +
        (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) / (Nat.card Smax : ℝ) +
          (((Nat.card (ambientDerivedSubgroup Tmax) : ℝ) - (v : ℝ) ^ 2) /
            (Nat.card Tmax : ℝ)) := by
  -- TeX `(13.10.2)`: decompose the total norm of `η₁₀`, use `(13.7)` on
  -- `H#`, and use the swapped/T-side instance of `(13.8)` on `Q#`.
  have hfields :=
    section13_theorem_13_10_etaTotalNormSourceFields_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT eta10
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH heta10 h10 hD hG0
  have h7 := theorem_13_7 Smax Tmax W W1 W2 P Q U V C D H
    Sfam Tfam τS τT ω η μ ν μsum νsum δ δ' σ p q u v c d
    hsource hnotation hH
  have h7eta : squareSumLowerBound (Section7.puncturedSubgroupSet H) eta10
      (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) := by
    simpa [heta10] using h7
  exact section13_theorem_13_10_etaTotalNormInequality_from_pieces
    Smax Tmax H Q G0 eta10 v hfields.1 h7eta hfields.2

private theorem section13_theorem_13_10_HConjugateClosure_cardinality_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    (Nat.card
        (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ) : ℝ) =
      (Nat.card G : ℝ) *
        ((Nat.card (Section7.puncturedSubgroupSet H) : ℝ) / (Nat.card Smax : ℝ)) := by
  exact section13_conjugatesOfSetBySet_card_real_eq
    (X := Section7.puncturedSubgroupSet H) (N := Smax)
    (section13_one_not_mem_puncturedSubgroupSet H)
    (section13_theorem_13_10_Hsharp_tiNormalizer_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT
      p q u v c d hsource hH hG0)

private theorem section13_theorem_13_10_QConjugateClosure_cardinality_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hD : D = ⊥)
    (hH : H = P ⊔ C)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    (Nat.card
        (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ) : ℝ) =
      (Nat.card G : ℝ) *
        ((Nat.card (Section7.puncturedSubgroupSet Q) : ℝ) / (Nat.card Tmax : ℝ)) := by
  exact section13_conjugatesOfSetBySet_card_real_eq
    (X := Section7.puncturedSubgroupSet Q) (N := Tmax)
    (section13_one_not_mem_puncturedSubgroupSet Q)
    (section13_theorem_13_10_Qsharp_tiNormalizer_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT
      p q u v c d hsource hD hH hG0)

private theorem section13_theorem_13_10_disjointCardinalitySourceData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hD : D = ⊥)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hH : H = P ⊔ C)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    theorem_13_10_disjointCardinalitySourceData Smax Tmax H Q G0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact section13_theorem_13_10_totalCardinality_from_G0Data_and_disjoint
      H Q G0 hG0
      (section13_theorem_13_10_disjointConjugateClosures_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        p q u v c d hsource hD h10 hH)
  · exact section13_theorem_13_10_HConjugateClosure_cardinality_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT
      p q u v c d hsource hH hG0
  · exact section13_theorem_13_10_QConjugateClosure_cardinality_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT
      p q u v c d hsource hD hH hG0

private theorem section13_theorem_13_10_scaledDisjointCardinality_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hD : D = ⊥)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hH : H = P ⊔ C)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    (Nat.card G : ℝ) =
      1 + (Nat.card G0 : ℝ) +
        (Nat.card G : ℝ) *
          ((Nat.card (Section7.puncturedSubgroupSet H) : ℝ) /
            (Nat.card Smax : ℝ)) +
        (Nat.card G : ℝ) *
          ((Nat.card (Section7.puncturedSubgroupSet Q) : ℝ) /
            (Nat.card Tmax : ℝ)) := by
  exact section13_theorem_13_10_scaledDisjointCardinality_from_sourceData
    Smax Tmax H Q G0
    (section13_theorem_13_10_disjointCardinalitySourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT
      p q u v c d hsource hD h10 hH hG0)

private theorem section13_theorem_13_10_disjointCardinalityIdentity_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hD : D = ⊥)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hH : H = P ⊔ C)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    1 = 1 / (Nat.card G : ℝ) + (Nat.card G0 : ℝ) / (Nat.card G : ℝ) +
      (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) / (Nat.card Smax : ℝ) +
        (Nat.card (Section7.puncturedSubgroupSet Q) : ℝ) / (Nat.card Tmax : ℝ) := by
  -- TeX `(13.10.3)`: `{1}`, `G₀`, `(H#)^G`, and `(Q#)^G` are a disjoint
  -- partition of `G`, with the TI normalizers giving the two quotient terms.
  have hGpos : 0 < (Nat.card G : ℝ) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card G)
  exact section13_theorem_13_10_disjointCardinalityIdentity_from_scaled
    (Nat.card G : ℝ)
    (Nat.card G0 : ℝ)
    ((Nat.card (Section7.puncturedSubgroupSet H) : ℝ) / (Nat.card Smax : ℝ))
    ((Nat.card (Section7.puncturedSubgroupSet Q) : ℝ) / (Nat.card Tmax : ℝ))
    hGpos
    (section13_theorem_13_10_scaledDisjointCardinality_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT
      p q u v c d hsource hD h10 hH hG0)

private theorem section13_theorem_13_10_totalNormDecompositionData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (G0 : Set G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ eta10 : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hlam_mem : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (heta10 : eta10 = η 1 0)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hD : D = ⊥)
    (hG0 : theorem_13_9_G0Data H Q G0) :
    theorem_13_10_totalNormDecompositionData
      (Nat.card G : ℝ)
      (Section7.supportEnergy G0 lamτ)
      (Section7.supportEnergy G0 eta10)
      (Nat.card G0 : ℝ)
      ((Nat.card (Section7.puncturedSubgroupSet H) : ℝ) / (Nat.card Smax : ℝ))
      (Complex.normSq (lam 1) / (Nat.card Smax : ℝ))
      (((Nat.card (ambientDerivedSubgroup Tmax) : ℝ) - (v : ℝ) ^ 2) /
        (Nat.card Tmax : ℝ))
      ((Nat.card (Section7.puncturedSubgroupSet Q) : ℝ) / (Nat.card Tmax : ℝ)) := by
  rcases h6hyp with ⟨hH, hlam_irred, hlam_deg, hlam_linear, hlamτ⟩
  exact ⟨
    section13_theorem_13_10_lambdaTotalNormInequality_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τ1 τT lam lamτ
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hcoh hnotation
      hlam_mem ⟨hH, hlam_irred, hlam_deg, hlam_linear, hlamτ⟩ hG0,
    section13_theorem_13_10_etaTotalNormInequality_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT eta10
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH heta10 h10 hD hG0,
    section13_theorem_13_10_disjointCardinalityIdentity_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τT
      p q u v c d hsource hD h10 hH hG0⟩

private theorem section13_theorem_13_10_sourceEstimateRawFields_of_hypothesis
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u) :
    ∃ (H : Subgroup G) (G0 : Set G)
      (lam : Section1.ClassFunction Smax) (lamτ eta10 : Section1.ClassFunction G),
      Complex.normSq (lam 1) = ((u * q : ℕ) : ℝ) * ((u * q : ℕ) : ℝ) ∧
        theorem_13_10_sourceEstimateRawFields
          (Nat.card G : ℝ)
          (Section7.supportEnergy G0 lamτ)
          (Section7.supportEnergy G0 eta10)
          (Nat.card G0 : ℝ)
          ((Nat.card (Section7.puncturedSubgroupSet H) : ℝ) / (Nat.card Smax : ℝ))
          (Complex.normSq (lam 1) / (Nat.card Smax : ℝ))
          (((Nat.card (ambientDerivedSubgroup Tmax) : ℝ) - (v : ℝ) ^ 2) /
            (Nat.card Tmax : ℝ))
          ((Nat.card (Section7.puncturedSubgroupSet Q) : ℝ) / (Nat.card Tmax : ℝ)) := by
  -- This is the remaining source-level content of TeX `(13.10.1)`,
  -- `(13.10.2)`, and `(13.10.3)`: total-norm decompositions over the
  -- relevant support pieces and the disjoint-union cardinal identity.
  classical
  have hsourceOrig := hsource
  have h10Orig := h10
  rcases h10 with ⟨lam, hlam_mem, hlam_irred, hlam_deg, hlam_linear⟩
  rcases hsource with
    ⟨_hcaseB, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      hnotationData, _hChoice, _hMin⟩
  rcases hnotationData with
    ⟨ω, η, μ, ν, μsum, νsum, δ, δ', σ, hnotation⟩
  rcases ((theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsourceOrig).1
      ω η μ ν μsum νsum δ δ' σ hnotation).2 with
    ⟨τ1, hcoh, houtput⟩
  let H : Subgroup G := P ⊔ C
  let G0 : Set G :=
    section16NonidentityElements (Set.univ : Set G) \
      (section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ ∪
        section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet Q) Set.univ)
  let lamτ : Section1.ClassFunction G := τ1 lam
  let eta10 : Section1.ClassFunction G := η 1 0
  have hlam_normSq :
      Complex.normSq (lam 1) = ((u * q : ℕ) : ℝ) * ((u * q : ℕ) : ℝ) :=
    section13_normSq_one_eq_of_degree_nat_mul hlam_deg
  have h9hyp : theorem_13_9_hypothesis Smax H P C Q G0 Sfam τ1 lam lamτ p q u := by
    refine ⟨?_, hlam_mem, ?_⟩
    · dsimp [theorem_13_9_G0Data, G0]
    · dsimp [theorem_13_6_hypothesis, H, lamτ]
      exact ⟨rfl, hlam_irred, hlam_deg, by simpa using hlam_linear, rfl⟩
  have h9concl := theorem_13_9 Smax Tmax W W1 W2 P Q U V C D H G0
    Sfam Tfam τS τ1 τT lam lamτ ω η μ ν μsum νsum δ δ' σ p q u v c d
    hsourceOrig hnotation hcoh houtput h9hyp
  have hGpos : 0 < (Nat.card G : ℝ) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card G)
  have hD_bot : D = ⊥ := by
    have h4 := theorem_13_4 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsourceOrig h10Orig
    exact h4.1
  have hsource123 :=
    section13_theorem_13_10_totalNormDecompositionData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H G0 Sfam Tfam τS τ1 τT
      lam lamτ eta10 ω η μ ν μsum νsum δ δ' σ p q u v c d
      hsourceOrig hcoh hnotation hlam_mem h9hyp.2.2 rfl h10Orig hD_bot h9hyp.1
  refine ⟨H, G0, lam, lamτ, eta10, hlam_normSq, ?_⟩
  exact section13_theorem_13_10_sourceEstimateRawFields_from_totalNormData
    hGpos hsource123 h9concl.2

private theorem section13_theorem_13_10_cardinalFormulaEstimateData_of_hypothesis
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u) :
    theorem_13_10_cardinalFormulaEstimateData p q u c := by
  -- This private package is exactly the formal content of TeX `(13.10.1)`,
  -- `(13.10.2)`, `(13.10.3)`, `(13.9)(b)`, and the cardinal substitutions
  -- following the symmetric `(13.4)` case-B conclusion.
  rcases section13_theorem_13_10_rawSourcePositivity_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource with
    ⟨hp_pos, hq1, hc_pos⟩
  have hq_pos : 0 < q := by omega
  rcases section13_uv_pos_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource with
    ⟨hu_pos, hv_pos⟩
  have hv_formula :
      (v : ℝ) = ((q : ℝ) ^ p - 1) / ((q - 1 : ℕ) : ℝ) :=
    section13_theorem_13_10_v_real_formula_of_hypothesis
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource h10
  have hV_card : Nat.card V = v :=
    section13_theorem_13_10_v_card_formula_of_hypothesis
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource h10
  have hQ_card : Nat.card Q = q ^ p :=
    section13_theorem_13_10_q_card_formula_of_hypothesis
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource h10
  have hQsharp_card : Nat.card (Section7.puncturedSubgroupSet Q) = q ^ p - 1 :=
    section13_theorem_13_10_qSharp_card_formula_of_hypothesis
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource h10
  have hP_card : Nat.card P = p ^ q :=
    section13_theorem_13_10_p_card_formula_of_hypothesis
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  have hS_card : Nat.card Smax = (p ^ q) * (u * c) * q :=
    section13_smax_card_formula_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource hP_card
  have hT_card : Nat.card Tmax = p * (q ^ p) * v :=
    section13_tmax_card_formula_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource hQ_card hV_card
  have hTderiv_card : Nat.card (ambientDerivedSubgroup Tmax) = (q ^ p) * v :=
    section13_tderiv_card_formula_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource hQ_card hV_card
  rcases section13_theorem_13_10_sourceEstimateRawFields_of_hypothesis
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource h10 with
    ⟨H, G0, lam, lamτ, eta10, hlam_normSq, hraw⟩
  have hLratio :
      Complex.normSq (lam 1) / (Nat.card Smax : ℝ) =
        ((u : ℝ) * (q : ℝ)) / ((c : ℝ) * (p : ℝ) ^ q) := by
    rw [hlam_normSq]
    exact section13_lratio_of_card_formula (sCard := Nat.card Smax)
      hp_pos hq_pos hu_pos hc_pos hS_card
  have hTterm :
      (((Nat.card (ambientDerivedSubgroup Tmax) : ℝ) - (v : ℝ) ^ 2) /
          (Nat.card Tmax : ℝ)) =
        1 / (p : ℝ) - 1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ)) +
          1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p)) := by
    calc
      (((Nat.card (ambientDerivedSubgroup Tmax) : ℝ) - (v : ℝ) ^ 2) /
          (Nat.card Tmax : ℝ)) =
          1 / (p : ℝ) - (v : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p)) := by
            exact section13_tSourceTerm_of_card_formula
              (tCard := Nat.card Tmax)
              (tDerivCard := Nat.card (ambientDerivedSubgroup Tmax))
              hp_pos hq_pos hv_pos hT_card hTderiv_card
      _ = 1 / (p : ℝ) - 1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ)) +
          1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p)) := by
            exact section13_tTerm_substitution_of_v hp_pos hq1 hv_formula
  have hQterm :
      ((Nat.card (Section7.puncturedSubgroupSet Q) : ℝ) / (Nat.card Tmax : ℝ)) =
        ((q - 1 : ℕ) : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p)) := by
    calc
      ((Nat.card (Section7.puncturedSubgroupSet Q) : ℝ) / (Nat.card Tmax : ℝ)) =
          (((q ^ p - 1 : ℕ) : ℝ) / (Nat.card Tmax : ℝ)) := by
            rw [hQsharp_card]
      _ = (((q : ℝ) ^ p - 1) / ((p : ℝ) * ((q : ℝ) ^ p) * (v : ℝ))) := by
            exact section13_qSharpTerm_of_tCard_formula
              (p := p) (q := q) (v := v) (tCard := Nat.card Tmax) hq_pos hT_card
      _ = ((q - 1 : ℕ) : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p)) := by
            exact section13_qTerm_substitution_of_v hp_pos hq1 hv_formula
  exact section13_theorem_13_10_cardinalFormulaEstimateData_from_rawFields
    hraw hLratio hTterm hQterm

private theorem section13_theorem_13_10_cardinalFormulaInequality_of_hypothesis
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u) :
    ((u : ℝ) * (q : ℝ)) / ((c : ℝ) * (p : ℝ) ^ q) >
      (1 / (p : ℝ) - 1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ)) +
        1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p))) -
          ((q - 1 : ℕ) : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p)) := by
  exact section13_theorem_13_10_cardinalFormulaInequality_from_estimateData
    (section13_theorem_13_10_cardinalFormulaEstimateData_of_hypothesis
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource h10)

private theorem section13_theorem_13_10_rawSourceInequality_of_hypothesis
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u) :
    ((u : ℝ) * (q : ℝ)) / ((c : ℝ) * (p : ℝ) ^ q) >
      1 / (p : ℝ) - 1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ)) -
        ((q - 1 : ℕ) : ℝ) / ((p : ℝ) * ((q : ℝ) ^ p)) +
          1 / ((p : ℝ) * ((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p)) := by
  exact section13_theorem_13_10_rawSourceInequality_from_cardinalFormula
    (section13_theorem_13_10_cardinalFormulaInequality_of_hypothesis
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource h10)

private theorem section13_theorem_13_10_rawSourceEstimate_of_hypothesis
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u) :
    theorem_13_10_rawSourceEstimate p q u c := by
  rcases section13_theorem_13_10_rawSourcePositivity_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource with
    ⟨hp, hq, hc⟩
  exact ⟨hp, hq, hc,
    section13_theorem_13_10_rawSourceInequality_of_hypothesis
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource h10⟩

private theorem section13_theorem_13_10_sourceEstimate_of_hypothesis
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) (m : ℝ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hm : m = 1 - 1 / ((q - 1 : ℕ) : ℝ) -
      ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) +
        1 / (((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p))) :
    theorem_13_10_sourceEstimate p q u c m := by
  exact section13_theorem_13_10_sourceEstimate_from_raw hm
    (section13_theorem_13_10_rawSourceEstimate_of_hypothesis
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource h10)

/-- Proof placeholder for `theorem_13_10_statement`. -/
public theorem theorem_13_10
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (m : ℝ)
    : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      theorem_13_10_hypothesis Smax P C Sfam p q u →
      m = 1 - 1 / ((q - 1 : ℕ) : ℝ) - ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) +
        1 / (((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p)) →
      (u : ℝ) / (c : ℝ) > (m * (p : ℝ) ^ (q - 1)) / (q : ℝ) := by
  intro hsource h10 hm
  exact section13_theorem_13_10_from_sourceEstimate
    (section13_theorem_13_10_sourceEstimate_of_hypothesis
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d m hsource h10 hm)
end CFSG.Section13
