module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_2_Field

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.7)
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

/-! ## (14.7) -/


public theorem section14_theorem_14_7_conj_normalizes_U
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        characteristicSubgroupIn U H →
          ∃ y : G, y ∈ Q ∧ W2.conjBy y ≤ Subgroup.normalizer (U : Set G) := by
  intro hctx h143 hchar
  rcases section14_theorem_14_5_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 with
    ⟨y, hyQ, hsemi⟩
  exact ⟨y, hyQ,
    le_sup_right.trans
      (section14_semidirect_right_le_normalizer_of_characteristic hsemi hchar)⟩

public theorem section14_theorem_14_7_actor_dvd_group_card_sub_one
    {A E : Type*} [Group A] [Finite A] [Group E] [Finite E]
    [MulDistribMulAction A E]
    (hfree : ∀ a : A, a ≠ 1 → ∀ e : E, a • e = e → e = 1) :
    Nat.card A ∣ Nat.card E - 1 := by
  classical
  let α := {e : E // e ≠ 1}
  letI : MulAction A α :=
    { smul := fun a e => ⟨a • (e : E), by
        intro h
        apply e.2
        have h' := congrArg (fun x : E => a⁻¹ • x) h
        simpa using h'⟩
      one_smul := by
        intro e
        apply Subtype.ext
        change (1 : A) • (e : E) = (e : E)
        simp
      mul_smul := by
        intro a b e
        apply Subtype.ext
        change (a * b) • (e : E) = a • (b • (e : E))
        rw [mul_smul] }
  have hstab : ∀ e : α, MulAction.stabilizer A e = ⊥ := by
    intro e
    rw [eq_bot_iff]
    intro a ha
    have hae : a • e = e := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha_not_bot
    have ha_ne : a ≠ 1 := by
      intro ha1
      apply ha_not_bot
      simp [ha1]
    have hfix : a • (e : E) = (e : E) := congrArg Subtype.val hae
    exact e.2 (hfree a ha_ne (e : E) hfix)
  have hcard_equiv := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hcardα : Nat.card α = Nat.card E - 1 := by
    letI : Fintype E := Fintype.ofFinite E
    letI : Fintype α := Fintype.ofFinite α
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {e : E // e ≠ 1} = Fintype.card E - 1
    simp
  rw [hcardα, Nat.card_prod] at hcard_equiv
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A α)), by
    rw [mul_comm]
    exact hcard_equiv⟩

public theorem section14_theorem_14_7_fixedPointFree_u_divisibility_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        characteristicSubgroupIn U H →
          p ∣ u - 1 := by
  intro hctx h143 hchar
  rcases section14_theorem_14_5_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 with
    ⟨y, _hyQ, hsemi⟩
  have hfrobLH : Section7.frobeniusWithKernel L H :=
    (section14_theorem_14_5_pf13_17_inputs hctx h143).2.1
  have hUH : U ≤ H := hchar.1
  have hW2y_card : Nat.card (W2.conjBy y) = p := by
    rcases hctx.1 with
      ⟨_hcase, _hSTypeP, _hTTypeP, hp_card, _hq_card, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    calc
      Nat.card (W2.conjBy y) = Nat.card W2 := section11_card_conjBy (G := G) W2 y
      _ = p := hp_card.symm
  have hW2y_le_L : W2.conjBy y ≤ L :=
    (le_sup_right : W2.conjBy y ≤ W1 ⊔ W2.conjBy y).trans hsemi.right_le
  have hW2y_not_H : ∀ a : W2.conjBy y, a ≠ 1 → (a : G) ∉ H := by
    intro a ha hH
    have ha_inf : (a : G) ∈ H ⊓ (W1 ⊔ W2.conjBy y) :=
      ⟨hH, (le_sup_right : W2.conjBy y ≤ W1 ⊔ W2.conjBy y) a.property⟩
    have ha_bot : (a : G) ∈ (⊥ : Subgroup G) := by
      simpa [hsemi.inf_eq_bot] using ha_inf
    exact ha (Subtype.ext (by simpa using ha_bot))
  have hW2y_norm_U : W2.conjBy y ≤ Subgroup.normalizer (U : Set G) :=
    le_sup_right.trans
      (section14_semidirect_right_le_normalizer_of_characteristic hsemi hchar)
  rcases section14_frobeniusWithKernel_invariant_subgroup_fixedPointFree_action
      (hfrob := hfrobLH) (A := W2.conjBy y) (Ω := U)
      hW2y_le_L hW2y_not_H hUH hW2y_norm_U with
    ⟨hUAction, hUfree⟩
  letI : MulDistribMulAction (W2.conjBy y) U := hUAction
  have hdivCard : Nat.card (W2.conjBy y) ∣ Nat.card U - 1 :=
    section14_theorem_14_7_actor_dvd_group_card_sub_one hUfree
  have hc_one : c = 1 :=
    Section13.theorem_13_12 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1
  have hUcard_eq : Nat.card U = u := by
    rcases hctx.1 with
      ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, hUcard,
        _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    rw [hUcard, hc_one, Nat.mul_one]
  rw [hW2y_card, hUcard_eq] at hdivCard
  exact hdivCard

public theorem section14_theorem_14_7_geom_quotient_mod_p_eq_one
    {p q : ℕ}
    (hp : Nat.Prime p)
    (hqpos : 0 < q) :
    ((p ^ q - 1) / (p - 1)) % p = 1 := by
  rw [← Nat.geomSum_eq hp.two_le q]
  induction q with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          simp [Nat.mod_eq_of_lt hp.one_lt]
      | succ n =>
          rw [Finset.sum_range_succ]
          have hprev : (∑ i ∈ Finset.range (n + 1), p ^ i) % p = 1 :=
            ih (by omega)
          have hpowmod : p ^ (n + 1) % p = 0 := by
            rw [Nat.mod_eq_zero_of_dvd]
            exact dvd_pow_self p (by omega : n + 1 ≠ 0)
          rw [Nat.add_mod, hprev, hpowmod]
          exact Nat.mod_eq_of_lt hp.one_lt

public theorem section14_theorem_14_7_mod_eq_one_of_dvd_sub_one
    {p n : ℕ}
    (hp : 1 < p)
    (hn : 0 < n)
    (hdiv : p ∣ n - 1) :
    n % p = 1 := by
  have h1n : 1 ≡ n [MOD p] :=
    (Nat.modEq_iff_dvd' (by omega : 1 ≤ n)).mpr hdiv
  have hn1 : n ≡ 1 [MOD p] := h1n.symm
  rw [Nat.ModEq] at hn1
  simpa [Nat.mod_eq_of_lt hp] using hn1

public theorem section14_theorem_14_7_mod_eq_one_branch_contradiction
    {p q u : ℕ}
    (hp : Nat.Prime p)
    (h2q : 2 < q)
    (hqp : q < p)
    (hupos : 0 < u)
    (hqu : q * u = (p ^ q - 1) / (p - 1))
    (hpdiv : p ∣ u - 1) :
    False := by
  have hu_mod : u % p = 1 :=
    section14_theorem_14_7_mod_eq_one_of_dvd_sub_one hp.one_lt hupos hpdiv
  have hgeom_mod : ((p ^ q - 1) / (p - 1)) % p = 1 :=
    section14_theorem_14_7_geom_quotient_mod_p_eq_one hp (by omega)
  have hqu_mod : (q * u) % p = 1 := by
    rw [hqu]
    exact hgeom_mod
  have huModEq : u ≡ 1 [MOD p] := by
    rw [Nat.ModEq]
    simpa [Nat.mod_eq_of_lt hp.one_lt] using hu_mod
  have hq_mul_mod : (q * 1) % p = 1 := by
    have hmul : q * u ≡ q * 1 [MOD p] :=
      (Nat.ModEq.refl q).mul huModEq
    rw [Nat.ModEq] at hmul
    rw [← hmul]
    exact hqu_mod
  have hq_eq_one : q = 1 := by
    simpa [Nat.mul_one, Nat.mod_eq_of_lt hqp] using hq_mul_mod
  omega

public theorem section14_theorem_14_7_product_formula_of_mod_eq_one
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcase :
      Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (hqp : q < p)
    (h2q : 2 < q)
    (hmod : p % q = 1) :
    q * u = (p ^ q - 1) / (p - 1) := by
  rcases hcase with
    ⟨_h92, _hH0, _hquot, hpPrime, hqPrime, _ho, _hcard, _hcent, _hcyc,
      _hirr, _hfield, _hcop, _hdiv, _hprimeField⟩
  have hpOdd : Odd p := hpPrime.odd_of_ne_two (by omega)
  have hqOdd : Odd q := hqPrime.odd_of_ne_two (by omega)
  have hgeom_dvd : q ∣ (p ^ q - 1) / (p - 1) :=
    (Section13.theorem_13_14 p q 1 hpPrime hqPrime hpOdd hqOdd).2.1 hmod
  have hforms := Section13.theorem_13_15 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsrc
    ⟨_h92, _hH0, _hquot, hpPrime, hqPrime, _ho, _hcard, _hcent, _hcyc,
      _hirr, _hfield, _hcop, _hdiv, _hprimeField⟩
  have hu : u = (p ^ q - 1) / (q * (p - 1)) := hforms.2 hmod
  have hdivdiv :
      (p ^ q - 1) / (q * (p - 1)) = ((p ^ q - 1) / (p - 1)) / q := by
    rw [Nat.mul_comm q (p - 1), ← Nat.div_div_eq_div_mul]
  rw [hu, hdivdiv]
  exact Nat.mul_div_cancel' hgeom_dvd

public theorem section14_theorem_14_7_odd_W1_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Odd (Nat.card W1) := by
  rcases hctx.1 with
    ⟨hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, hNotation, _hChoice, _hMin⟩
  rcases hcase with
    ⟨hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType,
      _hTType, _hCover⟩
  rcases hNotation with
    ⟨_ω, _η, _μ, _ν, _μsum, _νsum, _δ, _δ', _σ, hNotationFor⟩
  rcases hNotationFor with
    ⟨hω, _hσ, _hη, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hω with ⟨h31, _hqpos, _hppos, _ωFin, _hωNotation, _hωNat⟩
  change Section3.isCyclicTIHypothesis W1 W2 W at h31
  rcases h31 with
    ⟨_hW1le, _hW2le, _hprod31, _hcyc31, hWOdd, _hW1card, _hW2card, _hTI⟩
  exact Odd.of_dvd_nat hWOdd (Subgroup.card_dvd_of_le hprod.1)

public theorem section14_theorem_14_7_two_lt_q_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    2 < q := by
  rcases section14_context_primes_of_sourceData hctx with ⟨_hpPrime, hqPrime⟩
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp_card, hq_card, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  have hqOdd : Odd q := by
    rw [hq_card]
    exact section14_theorem_14_7_odd_W1_of_sourceData hctx
  have hq_ne_two : q ≠ 2 := by
    intro hq2
    rw [hq2] at hqOdd
    rcases hqOdd with ⟨k, hk⟩
    omega
  exact lt_of_le_of_ne hqPrime.two_le (Ne.symm hq_ne_two)

public theorem section14_theorem_14_7_positive_u_formula_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        characteristicSubgroupIn U H →
          u = (p ^ q - 1) / (p - 1) := by
  intro hctx h143 hchar
  have hcase :
      Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u :=
    section14_theorem_14_6_source_data_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  have hforms := Section13.theorem_13_15 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hctx.1 hcase
  by_cases hmod : p % q = 1
  · rcases section14_context_primes_of_sourceData hctx with ⟨hp, _hq⟩
    have h2q : 2 < q := section14_theorem_14_7_two_lt_q_of_sourceData hctx
    have hqu : q * u = (p ^ q - 1) / (p - 1) :=
      section14_theorem_14_7_product_formula_of_mod_eq_one hctx.1 hcase hctx.2 h2q hmod
    have hpdiv : p ∣ u - 1 :=
      section14_theorem_14_7_fixedPointFree_u_divisibility_source_bridge
        Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 hchar
    have hupos : 0 < u := by
      rcases hctx.1 with
        ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, hUcard,
          _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
      have hc_one : c = 1 :=
        Section13.theorem_13_12 Smax Tmax W W1 W2 P Q U V C D
          Sfam Tfam τS τT p q u v c d hctx.1
      have hUcard_eq : Nat.card U = u := by
        rw [hUcard, hc_one, Nat.mul_one]
      rw [← hUcard_eq]
      exact Nat.card_pos
    exact False.elim
      (section14_theorem_14_7_mod_eq_one_branch_contradiction
        hp h2q hctx.2 hupos hqu hpdiv)
  · exact hforms.1 hmod

public theorem section14_theorem_14_7_source_field_and_positive_u_formula_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        characteristicSubgroupIn U H →
          theorem_14_2_a_fieldIsoData P U W2 p q ∧
            (Section13.theorem_13_10_hypothesis Smax P C Sfam p q u →
              u = (p ^ q - 1) / (p - 1)) := by
  intro hctx h143 hchar
  have hcase :
      Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u :=
    section14_theorem_14_6_source_data_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  have hu : u = (p ^ q - 1) / (p - 1) :=
    section14_theorem_14_7_positive_u_formula_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 hchar
  have hCbot : C = ⊥ :=
    section14_C_eq_bot_of_pf13_12_source hctx.1
  exact ⟨section14_theorem_14_2_fieldIso_of_case_b_source_bridge hcase hCbot hu,
    fun _h10 => hu⟩

public theorem section14_theorem_14_7_source_field_and_positive_U_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        characteristicSubgroupIn U H →
          theorem_14_2_a_fieldIsoData P U W2 p q ∧
            (Section13.theorem_13_10_hypothesis Smax P C Sfam p q u →
              Nat.card U = (p ^ q - 1) / (p - 1) ∧
                Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) := by
  intro hctx h143 hchar
  rcases section14_theorem_14_7_source_field_and_positive_u_formula_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 hchar with
    ⟨hfield, hu_of_h10⟩
  have hcase97 : Section13.case_9_7_b_for_section13 Smax C p q u :=
    section14_theorem_14_6_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  have hc : c = 1 :=
    Section13.theorem_13_12 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1
  refine ⟨hfield, ?_⟩
  intro h10
  have hu : u = (p ^ q - 1) / (p - 1) := hu_of_h10 h10
  have hUcard : Nat.card U = (p ^ q - 1) / (p - 1) :=
    section14_U_card_of_sourceData_of_u_eq_and_c_eq_one hctx.1 hu hc
  have hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) := by
    simpa [hu] using hcase97.2.2.2.1
  exact ⟨hUcard, hcop⟩

public theorem section14_theorem_14_7_source_hard_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        characteristicSubgroupIn U H →
          theorem_14_2_a_fieldIsoData P U W2 p q ∧
            Nat.card U = (p ^ q - 1) / (p - 1) ∧
            Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) := by
  intro hctx h143 hchar
  rcases section14_theorem_14_7_source_field_and_positive_U_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 hchar with
    ⟨hfield, hpos⟩
  by_cases h10 : Section13.theorem_13_10_hypothesis Smax P C Sfam p q u
  · rcases hpos h10 with ⟨hUcard, hcop⟩
    exact ⟨hfield, hUcard, hcop⟩
  · rcases section14_theorem_14_2_U_card_coprime_of_not_theorem_13_10
      hctx.1 h10 with
      ⟨hUcard, hcop⟩
    exact ⟨hfield, hUcard, hcop⟩

public theorem section14_theorem_14_7_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d : ℕ) :
      hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        characteristicSubgroupIn U H →
          theorem_14_2_a_data P U W2 p q ∧
            theorem_14_2_b_data Q W1 W2 U q := by
  intro hctx h143 hchar
  have hconjNorm :
      ∃ y : G, y ∈ Q ∧ W2.conjBy y ≤ Subgroup.normalizer (U : Set G) :=
    section14_theorem_14_7_conj_normalizes_U
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 hchar
  rcases Section13.theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1 with
    ⟨_hSmaxMF, _htypeS, _htypeII, hUcomm, _hUfrob, hPelem, hPcard, _hu,
      _hSfamCoh, _hTI, _hTauS⟩
  rcases section14_context_primes_of_sourceData hctx with ⟨hp, hq⟩
  rcases section14_theorem_14_7_source_hard_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 hchar with
    ⟨hfield, hUcard, hcop⟩
  have hW2le : W2 ≤ P :=
    section14_theorem_14_2_a_W2_le_P_of_sourceData hctx.1
  have hW2card : Nat.card W2 = p :=
    section14_theorem_14_2_a_cardW2_of_sourceData hctx.1
  have ha : theorem_14_2_a_data P U W2 p q :=
    ⟨hfield, hp, hq, hPelem, hUcomm, hPcard, hUcard, hW2le, hW2card, hcop⟩
  exact ⟨ha,
    section14_theorem_14_2_b_Q_elementary_of_sourceData hctx.1,
    section14_theorem_14_2_b_W2_le_normalizer_Q_of_sourceData hctx.1,
    hconjNorm⟩


end CFSG.Section14
