module

public import CFSG.RankThree.PartTwo.Sec6.HeringB3G2
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
public import CFSG.RankThree.PartTwo.Sec8.Hering418FD4
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofEvenDesc

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.KFacts
open CFSG.PGLModel (projImage)

open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof (d4ShortSL2)


section Certs


theorem perfSubnormalBot_of_pgl {X : Type} [Group X] {C : Subgroup X} {f : ℕ} {π : Bool}
    {F : Type} [Field F] (hPi : Sec4.PiField π 2 f F) (hpar : cond π (Even f) (Odd f))
    (Φ : ↥C ≃* ↥(projImage (Sec4.glPi π 3 (2 ^ f) F))) : PerfSubnormalBot C := by
  haveI := hPi.finite
  by_cases hq2 : 2 < 2 ^ f
  · obtain ⟨Q, hQC, hQcomm, hQs, -, ⟨ι⟩⟩ := Sec8.Hering418.exists_core_of_pgl hPi hq2 Φ
    have hmod : Sec4.ModThree π (2 ^ f) := by
      cases π
      · exact two_pow_mod_three_of_odd hpar
      · exact two_pow_mod_three_of_even hpar
    have hcardP := Sec13.card_projImage_slPi_mul_three hPi hmod
    have h9 : 9 ∣ (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) *
        cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1) := by
      generalize 2 ^ f = q at hmod ⊢
      cases π
      · have hq' : q % 3 = 2 := hmod
        have h2 : q ^ 2 % 3 = 1 := by simp [Nat.pow_mod, hq']
        have h3 : q ^ 3 % 3 = 2 := by simp [Nat.pow_mod, hq']
        obtain ⟨a, ha⟩ : 3 ∣ q ^ 2 - 1 := by omega
        obtain ⟨b, hb⟩ : 3 ∣ q ^ 3 + 1 := by omega
        show 9 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)
        rw [ha, hb]
        exact ⟨q ^ 3 * a * b, by ring⟩
      · have hq' : q % 3 = 1 := hmod
        have h2 : q ^ 2 % 3 = 1 := by simp [Nat.pow_mod, hq']
        have h3 : q ^ 3 % 3 = 1 := by simp [Nat.pow_mod, hq']
        obtain ⟨a, ha⟩ : 3 ∣ q ^ 2 - 1 := by omega
        obtain ⟨b, hb⟩ : 3 ∣ q ^ 3 - 1 := by omega
        show 9 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)
        rw [ha, hb]
        exact ⟨q ^ 3 * a * b, by ring⟩
    have h3 : 3 ∣ Nat.card ↥Q := by
      rw [Nat.card_congr ι.toEquiv]
      generalize Nat.card ↥(projImage (Sec4.slPi π 3 (2 ^ f) F)) = N at hcardP
      generalize (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) *
        cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1) = M at hcardP h9
      omega
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : Finite ↥Q := Finite.of_equiv _ ι.symm.toEquiv
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hx1 : x ≠ 1 := fun h => by simp [h] at hx
    refine perfSubnormalBot_of_commutators_le_grp hQC (fun x hx y hy => ?_)
      (perfSubnormalBotGrp_of_isSimpleGroup hQs ⟨x, hx1, hx3⟩)
    exact hQcomm (by rw [← commutatorElement_def]; exact Subgroup.commutator_mem_commutator hx hy)
  · have hf1 : f = 1 := by
      by_contra hne
      have hf2 : 2 ≤ f := by
        rcases hPi.one_le.eq_or_lt with h | h
        · exact absurd h.symm hne
        · omega
      exact hq2 (calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2)
    have h2 : 2 ^ f = 2 := by rw [hf1]; norm_num
    cases π with
    | true => exact absurd hpar (by rw [hf1]; decide)
    | false =>
      haveI : Group.IsSolvable ↥(projImage (Sec4.glPi false 3 (2 ^ f) F)) :=
        Sec13.isSolvable_projImage_glPi_two hPi h2
      exact perfSubnormalBot_of_isSolvable
        (Group.isSolvable_of_isSolvable_injective (f := Φ.toMonoidHom) Φ.injective)

section D4

variable {K : Type} [Field K] [Finite K] {f : ℕ} {σ : K ≃+* K}

theorem d4_ringChar_two (hK : Nat.card K = (2 ^ f) ^ 3) : ringChar K = 2 :=
  ringChar_eq_of_card_pow Nat.prime_two (f := f * 3) (by rw [hK, pow_mul])

theorem d4_sigma_pow_three (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    σ ^ 3 = 1 := by
  ext c
  rw [pow_three, RingAut.mul_apply, RingAut.mul_apply]
  exact ringEquiv_cube_apply_eq hK hσ c

theorem d4_four_le_card (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) : 4 ≤ Nat.card K := by
  rw [hK]
  have h2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  calc 4 ≤ 2 ^ 3 := by norm_num
    _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left h2 3

theorem exists_order_three_d4 (hσ3 : σ ^ 3 = 1) (hK3 : ¬ 3 ∣ Nat.card K) :
    ∃ x ∈ d4ShortSL2 K σ.toRingHom, x ≠ 1 ∧ x ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := KS11Lie4Proof.card_d4ShortSL2 (K := K) hσ3
  have h3 : 3 ∣ Nat.card (d4ShortSL2 K σ.toRingHom) := by
    rw [hcard]
    exact Dvd.dvd.mul_left (three_dvd_sq_sub_one hK3) _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  refine ⟨(x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom), x.2, ?_, ?_⟩
  · intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega
  · exact congrArg Subtype.val hx3

theorem perfSubnormalBot_centralizer_d4 (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hz3 : z ^ 3 = 1) :
    PerfSubnormalBot (Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom))) := by
  have hK2 := d4_ringChar_two hK
  have hσ3 : σ ^ 3 = 1 := d4_sigma_pow_three hK hσ
  have hq3 : ¬ 3 ∣ 2 ^ f := not_three_dvd_two_pow f
  have hK3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact fun h => hq3 (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  have hK4 := d4_four_le_card hf hK
  have hS3 := exists_order_three_d4 hσ3 hK3
  by_cases hz1 : z = 1
  · subst hz1
    have hC : Subgroup.centralizer ({1} : Set (graphFixedRootGroup TwistTag.D4 K
        σ.toRingHom)) = ⊤ := by
      ext y
      refine ⟨fun _ => Subgroup.mem_top y, fun _ => ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_one y).trans (one_mul y).symm
    rw [hC]
    have hperf := commutator_graphFixedRootGroup_triality_char_two hK2 σ
      (ringEquiv_cube_apply_eq hK hσ) hK4
    have hs : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      (isSimpleGroup_graphFixedRootGroup_of_perfect TwistTag.D4 K σ hperf).1
    obtain ⟨x, -, hx1, hx3⟩ := hS3
    exact perfSubnormalBot_of_isSimpleGroup Subgroup.topEquiv.isSimpleGroup
      ⟨x, Subgroup.mem_top x, hx1, hx3⟩
  · obtain ⟨g, hg⟩ := KS11Lie6Proof.d4ThreeConj_holds K (2 ^ f) σ hK hσ hq3 z hz3 hz1
    refine perfSubnormalBot_centralizer_of_conj z g ?_
    have hw3 : (g * z * g⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hz3]
      group
    have hw1 : g * z * g⁻¹ ≠ 1 := fun h => hz1 (by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group)
    rcases hg with hS | hM
    · rcases KS11Lie6Proof.d4ThreeACent_holds K (2 ^ f) σ hK hσ hq3 _ hS hw3 hw1 with
        hsol | ⟨N, hNC, hcomm, hNq, x, hxN, -, hx1, hx3⟩
      · exact perfSubnormalBot_of_isSolvable hsol
      · exact perfSubnormalBot_of_commutators_le_quasisimple hNC hcomm hNq ⟨x, hxN, hx1, hx3⟩
    · obtain ⟨hcomm, -⟩ := KS11Lie6Proof.d4ThreeBCent_holds K (2 ^ f) σ hK hσ hq3 _ hM hw3 hw1
      have hSq := KS11Lie4Proof.isQuasisimple_d4ShortSL2 hσ3 hK4
      have hSC : d4ShortSL2 K σ.toRingHom ≤ Subgroup.centralizer
          ({g * z * g⁻¹} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
        intro s hs
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hM) s hs
      exact perfSubnormalBot_of_commutators_le_quasisimple hSC hcomm hSq hS3

noncomputable def autFix_conj_equiv {X : Type*} [Group X] (γ α : MulAut X) :
    Sec4.autFix (γ * α * γ⁻¹) ≃* Sec4.autFix α :=
  (MulEquiv.subgroupCongr (congrArg Sec4.autFix
    (show γ * α * γ⁻¹ = MulAut.congr γ α from (MulEquiv.ext fun _ => rfl)))).trans
    (Sec4.autFixCongrEquiv γ α)

theorem b3Fix_d4_of_outer (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hβ : β ^ 3 = 1)
    (hout : ¬ IsInnerAut β) {C : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hC : ∀ z, z ∈ C ↔ β z = z) : B3Fix C := by
  have hCeq : C = Sec4.autFix β := Subgroup.ext fun z => by rw [hC z]; rfl
  subst hCeq
  have hK2 := d4_ringChar_two hK
  rcases Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hf hK hσ hβ hout with
    ⟨γ, hγ⟩ | ⟨⟨e₂⟩⟩
  ·
    obtain ⟨ψ⟩ := nonempty_fixedPoints_fieldActor_mulEquiv_g2 σ hK2
    obtain ⟨e1⟩ : Nonempty (Sec4.autFix β ≃* Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) := by
      rcases hγ with rfl | rfl
      · exact ⟨autFix_conj_equiv γ _⟩
      · exact ⟨(autFix_conj_equiv γ _).trans
          (MulEquiv.subgroupCongr (Sec8.Item8KFacts2Proof.autFix_inv _))⟩
    have e2 : Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ) ≃*
        adjointGroup .G2 (fixSubfield σ) :=
      (MulEquiv.subgroupCongr (by ext; rfl)).trans ψ
    set Φ := e1.trans e2 with hΦ
    have hcard := card_fixSubfield_of_cube hf hK hσ
    haveI : CharP K 2 := ringChar.of_eq hK2
    haveI : CharP (fixSubfield σ) 2 :=
      RingHom.charP (fixSubfield σ).subtype (fixSubfield σ).subtype_injective 2
    have hk₀3 : ringChar (fixSubfield σ) ≠ 3 := by rw [ringChar.eq _ 2]; norm_num
    by_cases hf2 : 2 ≤ f
    · have h4 : 4 ≤ Nat.card (fixSubfield σ) := by
        rw [hcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      have hs : IsSimpleGroup (adjointGroup .G2 (fixSubfield σ)) :=
        CFSG.QuasithinUnique.Id2519.isSimpleGroup_adjointGroup_g2 (by omega)
      obtain ⟨x, hx1, hx3⟩ := exists_order_three_adjointG2 (K := fixSubfield σ) hk₀3
      exact b3Fix_of_perfSubnormalBot (perfSubnormalBot_of_grp
        (perfSubnormalBotGrp_of_mulEquiv Φ (perfSubnormalBotGrp_of_isSimpleGroup hs
          ⟨x, hx1, hx3⟩)))
    · have hf1 : f = 1 := by omega
      subst hf1
      have h2 : Nat.card (fixSubfield σ) = 2 := by rw [hcard]; norm_num
      refine b3Fix_of_card_dvd (M := 12096) ?_ fun a ha => not_suzukiOrder_dvd_12096 ha
      rw [Nat.card_congr Φ.toEquiv,
        CFSG.ComponentClassification.ExcSelector.card_adjointGroup_G2_two h2]
  ·
    rcases Nat.even_or_odd f with hfe | hfo
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := Sec8.kF82D4SecondCentY0Even_holds f hfe hf K σ hK hσ
      have hPi : Sec4.PiField true 2 f F := ⟨Nat.prime_two, hf, hF⟩
      exact b3Fix_of_perfSubnormalBot (perfSubnormalBot_of_pgl hPi hfe (e₂.trans e₃))
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := Sec8.kF82D4SecondCentY0_holds f hfo K σ hK hσ
      have hPi : Sec4.PiField false 2 f F := ⟨Nat.prime_two, hf, hF⟩
      exact b3Fix_of_perfSubnormalBot (perfSubnormalBot_of_pgl hPi hfo (e₂.trans e₃))

theorem threePrimeB3_graphFixed_triality (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ThreePrimeB3 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  refine threePrimeB3_of_b3Fix fun β hβ C hC => ?_
  by_cases hin : IsInnerAut β
  · obtain ⟨z, rfl⟩ := hin
    have hz3 := pow_three_eq_one_of_conj_pow_three
      (CFSG.TauCetiBridge.Twisted.center_graphFixedRootGroup_eq_bot σ.toRingHom) hβ
    rw [fixed_conj_eq_centralizer hC]
    exact b3Fix_of_perfSubnormalBot (perfSubnormalBot_centralizer_d4 hf hK hσ z hz3)
  · exact b3Fix_d4_of_outer hf hK hσ hβ hin hC

end D4

theorem threePrimeB3_of_chevalleyTriality {X : Type} [Group X] {f : ℕ}
    (h : ChevalleyExceptionalModel X .trialityD4 2 f) : ThreePrimeB3 X := by
  have hf : 1 ≤ f := h.1.2.1
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := Sec4.exists_mulEquiv_graphFixedRootGroup_D4 h
  exact threePrimeB3_of_mulEquiv e (threePrimeB3_graphFixed_triality hf hK hσ)

end Certs

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
