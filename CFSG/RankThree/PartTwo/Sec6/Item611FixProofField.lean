module

public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofTools
public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofG2
public import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofKField
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofFieldD
import CFSG.RankThree.PartTwo.Sec6.Item611Res3Proof
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusOrders
import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
public import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofKStar
public import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofSK

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

open CFSG.GorensteinWalter (PSL2)

open Res611Res4 Res611Res7
open scoped commutatorElement

section Certs

theorem item611FieldL2KField_holdsFix (h45 : Sec4.Item4_5)
    (h41 : Sec4.Item4_1LargePrime) (h413 : Sec4.Item4_13_forwardFix) :
    Item611FieldL2KField := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ he hcE d hd hdc hdF K hK
    hCAK hLK hcK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, m, hm, ⟨φ⟩, -⟩ := he
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.1.1
  have hdE : d ∈ E := hd.1
  have hdA : d ∈ A := hE.2 hdE
  have hd1 : d ≠ 1 := fun h => hdc (h ▸ Subgroup.one_mem _)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hKd : K ∈ thetaComponentsAt 3 d := lZeroStarAt_subset A d hK
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hL
  set P := Sec11.sec11K L d with hP
  obtain ⟨F', _, _, hF'card, hF'neg, ⟨eP⟩⟩ := exists_sec11K_quotient_psl2 hm φ hdF hd3
  have hPdvd : Nat.card (PSL2 F') ∣ Nat.card (K ⧸ aschbacherSolvableCore 3 K) := by
    rw [← Nat.card_congr eP.toEquiv]
    exact (card_quotient_dvd_card_map hLK).trans (Subgroup.card_subgroup_dvd_card _)
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe hdA hd1 K hKd
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hAK hcA
  rcases Res611Fix.cases413 h45 h41 h413 hst hA hrank hdA hd1 hK hCAK with
    ⟨-, -, n, hn, ⟨φK⟩, -⟩ | ⟨hAK', N, hNn, hNdef, hiso⟩ | ⟨hdec, hdK, hiso⟩ | hcase
  ·
    refine ⟨n, hn, ⟨φK⟩, ?_⟩
    set F := GaloisField 3 (3 * n) with hF
    set ψK := φK.trans (Sec4.projSLEquivPSL F) with hψK
    have hZK : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
      CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv ψK
        (CFSG.GorensteinWalter.psl2_center_eq_bot F)
    set γ := Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩) with hγ
    have hγ3 : γ ^ 3 = 1 := by
      have h1 : (⟨c, hcN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hc3)
      rw [hγ, ← map_pow, ← map_pow, h1, map_one, map_one]
    have hγP : ∀ p : K, (p : G) ∈ P →
        γ (p : K ⧸ aschbacherSolvableCore 3 K) = (p : K ⧸ aschbacherSolvableCore 3 K) := by
      intro p hp
      rw [hγ, Sec4.thetaQuotMulAut_mk]
      congr 1
      apply Subtype.ext
      rw [show ((Sec4.compAction K ⟨c, hcN⟩ p : K) : G) = c * (p : G) * c⁻¹ from rfl]
      have hpL : (p : G) ∈ L := Sec11.sec11K_le L d hp
      have hpc := Subgroup.mem_centralizer_singleton_iff.mp
        (le_centralizer_of_mem_thetaComponentsAt hLc hpL)
      rw [← hpc, mul_inv_cancel_right]
    have hout : Sec4.InducesOuterTheta c K := by
      refine ⟨hcN, fun hinn => ?_⟩
      obtain ⟨u, hu⟩ := hinn
      have hu' : MulAut.conj u = γ := hu
      have hu1 : u ≠ 1 := by
        rintro rfl
        apply hcK
        refine (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct hcN).mpr ?_
        rw [map_one] at hu'
        exact hu'.symm
      have hu3 : u ^ 3 = 1 := by
        have h1 : MulAut.conj (u ^ 3) = 1 := by rw [map_pow, hu', hγ3]
        have h2 := Sec12.mem_center_of_conj_eq_one h1
        rwa [hZK, Subgroup.mem_bot] at h2
      have hcu : ∀ p : K, (p : G) ∈ P → ψK (p : K ⧸ aschbacherSolvableCore 3 K) ∈
          Subgroup.centralizer ({ψK u} : Set (PSL2 F)) := by
        intro p hp
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        congr 1
        have h1 := hγP p hp
        rw [← hu', MulAut.conj_apply] at h1
        calc (p : K ⧸ aschbacherSolvableCore 3 K) * u =
            (u * (p : K ⧸ aschbacherSolvableCore 3 K) * u⁻¹) * u := by rw [h1]
          _ = u * (p : K ⧸ aschbacherSolvableCore 3 K) := by group
      have hψu1 : ψK u ≠ 1 := fun h => hu1 (ψK.injective (by rw [h, map_one]))
      have hψu3 : (ψK u) ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
      have h4 : 4 ≤ Nat.card F' := by
        rw [hF'card]
        calc 4 ≤ 3 ^ 2 := by norm_num
          _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm.le
      apply not_forall_commute_of_isQuasisimple (KFacts.isQuasisimple_psl2_of_four_le_card h4)
      intro x y
      obtain ⟨x', rfl⟩ := eP.surjective x
      obtain ⟨y', rfl⟩ := eP.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      obtain ⟨x0, rfl⟩ := QuotientGroup.mk_surjective x'
      obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective y'
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      set ι := Subgroup.inclusion hLK with hι
      have hcomm : ψK ((ι x0 : K) : K ⧸ aschbacherSolvableCore 3 K) *
          ψK ((ι y0 : K) : K ⧸ aschbacherSolvableCore 3 K) =
          ψK ((ι y0 : K) : K ⧸ aschbacherSolvableCore 3 K) *
            ψK ((ι x0 : K) : K ⧸ aschbacherSolvableCore 3 K) :=
        commute_of_mem_centralizer_psl2 (by omega) hψu1 hψu3 (hcu (ι x0) x0.2) (hcu (ι y0) y0.2)
      rw [← map_mul, ← map_mul] at hcomm
      have hcomm' := ψK.injective hcomm
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm'
      have h5 : (((x0 * y0)⁻¹ * (y0 * x0) : P) : G) ∈
          inSubgroup (aschbacherSolvableCore 3) K ⊓ P := by
        exact ⟨⟨_, hcomm', rfl⟩, ((x0 * y0)⁻¹ * (y0 * x0) : P).2⟩
      obtain ⟨z, hz, hzeq⟩ := theta_inf_le_theta hLK h5
      rwa [show z = (x0 * y0)⁻¹ * (y0 * x0) from Subtype.ext hzeq] at hz
    exact KFacts.InducesStdKind.psl2 F
      ⟨ψK, KFacts.inducesKind_field_of_pow_three K hc3 hout ψK⟩
  ·
    exfalso
    have hc3' : IsPGroup 3 (Subgroup.zpowers d) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1, pow_one])
    have hNcard : Nat.card N = 3 := by
      rw [hNdef, Res611Res4.card_map_mk_of_isPGroup hc3' (Subgroup.zpowers_le.mpr (hAK' hdA)),
        Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
    have hcardK : Nat.card (K ⧸ aschbacherSolvableCore 3 K) =
        Nat.card ((K ⧸ aschbacherSolvableCore 3 K) ⧸ N) * 3 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rwa [hNcard] at h1
    rcases hiso with hU | hMc
    · obtain ⟨e⟩ := hU
      rw [hcardK, Nat.card_congr e.toEquiv, BThreeCensus.card_projSU_four_three] at hPdvd
      exact not_card_psl2_dvd hm hF'card hF'neg (by norm_num) hPdvd
    · obtain ⟨e⟩ := hMc
      rw [hcardK, Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL] at hPdvd
      exact not_card_psl2_dvd hm hF'card hF'neg (by norm_num) hPdvd
  ·
    exfalso
    rcases hiso with hG | hMc | hL4 | hU4
    ·
      have hθodd := Res611Res3.odd_card_theta_of_config h45 hst hA hrank hcA hc1 hLc
      obtain ⟨hdN, hQ, -⟩ := Res611Res7.fieldCent_facts hm φ hdF hd3
      have hTd : T ≤ L ⊓ Subgroup.centralizer ({d} : Set G) := le_inf hTL fun t ht =>
        Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hd.2 t ht)
      obtain ⟨hET, hTab, hT4⟩ := mem_fourGroups_iff.mp hT.1
      have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4]; norm_num)
      have hTK : T ≤ K := (le_sec11K_of_isPGroup_two hθodd hdN hd3 hQ.1 hTd hT2).trans hLK
      have hTθK : T ⊓ inSubgroup (aschbacherSolvableCore 3) K = ⊥ := by
        have h1 := Res611Fix.inf_thetaQuotCentralizer_eq_bot h45 h41 h413 hst hA hrank hdA hd1
          hK hCAK hTab
        exact le_bot_iff.mp ((inf_le_inf_left T (theta_le_thetaQuotCentralizer K)).trans h1.le)
      have hK0 : K ∈ lZero E := by
        refine ⟨mem_thetaComponentFamily_iff.mpr ⟨d, hdE, hd1, hKd⟩, T,
          (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨hTK, hT2, hET⟩, fun h => ?_⟩
        rw [← hT.2] at h
        have h1 : T ≤ T ⊓ inSubgroup (aschbacherSolvableCore 3) K := le_inf le_rfl h
        rw [hTθK] at h1
        have h2 := Subgroup.card_le_of_le h1
        rw [Subgroup.card_bot, hT4] at h2
        omega
      exact item611NotG2T_holds G hst A hA hrank d hdA hd1 K hK hCAK E hE hK0 T hT hTK hTθK hdec
        hdK hG
    · obtain ⟨e⟩ := hMc
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL] at hPdvd
      exact not_card_psl2_dvd hm hF'card hF'neg (by norm_num) hPdvd
    · obtain ⟨e⟩ := hL4
      have h := Sec11.KSListsProof.card_projSL_four_mul (GaloisField 3 1)
      rw [GaloisField.card 3 1 (by norm_num)] at h
      norm_num at h
      have h' : Nat.card (projSL 4 (GaloisField 3 1)) = 6065280 := by omega
      rw [Nat.card_congr e.toEquiv, h'] at hPdvd
      exact not_card_psl2_dvd hm hF'card hF'neg (by norm_num) hPdvd
    · obtain ⟨e⟩ := hU4
      rw [Nat.card_congr e.toEquiv, BThreeCensus.card_projSU_four_three] at hPdvd
      exact not_card_psl2_dvd hm hF'card hF'neg (by norm_num) hPdvd
  ·
    exfalso
    have hθodd := Res611Res3.odd_card_theta_of_config h45 hst hA hrank hcA hc1 hLc
    obtain ⟨hdN, hQ, -⟩ := Res611Res7.fieldCent_facts hm φ hdF hd3
    have hTd : T ≤ L ⊓ Subgroup.centralizer ({d} : Set G) := le_inf hTL fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hd.2 t ht)
    obtain ⟨hET, hTab, hT4⟩ := mem_fourGroups_iff.mp hT.1
    have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4]; norm_num)
    have hTK : T ≤ K := (le_sec11K_of_isPGroup_two hθodd hdN hd3 hQ.1 hTd hT2).trans hLK
    have hTθK : T ⊓ inSubgroup (aschbacherSolvableCore 3) K = ⊥ := by
      have h1 := Res611Fix.inf_thetaQuotCentralizer_eq_bot h45 h41 h413 hst hA hrank hdA hd1
        hK hCAK hTab
      exact le_bot_iff.mp ((inf_le_inf_left T (theta_le_thetaQuotCentralizer K)).trans h1.le)
    have hK0 : K ∈ lZero E := by
      refine ⟨mem_thetaComponentFamily_iff.mpr ⟨d, hdE, hd1, hKd⟩, T,
        (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨hTK, hT2, hET⟩, fun h => ?_⟩
      rw [← hT.2] at h
      have h1 : T ≤ T ⊓ inSubgroup (aschbacherSolvableCore 3) K := le_inf le_rfl h
      rw [hTθK] at h1
      have h2 := Subgroup.card_le_of_le h1
      rw [Subgroup.card_bot, hT4] at h2
      omega
    exact item611NotG2CoverT_holds G hst A hA hrank d hdA hd1 K hK hCAK E hE hK0 T hT hTK hTθK
      hcase

end Certs

section CertsS

theorem item611FieldL2S_holdsFix (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (h41 : Sec4.Item4_1LargePrime) (h413 : Sec4.Item4_13_forwardFix) : Item611FieldL2S := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ he hcE d hd hdc S hS hS1
    hSc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdF := item611FieldL2DField_holds h45 G hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT
    hTL hTθ he hcE d hd hdc
  obtain ⟨K, hKd, hLK⟩ := item611FieldL2KExists_holds h48 G hst A hA hrank c hcA hc1 L hL hCA E
    hE hLE T hT hTL hTθ he hcE d hd hdc hdF
  obtain ⟨hSK, hSKθ, hcK⟩ := item611FieldL2SK_holds h45 G hst A hA hrank c hcA hc1 L hL hCA E hE
    hLE T hT hTL hTθ he hcE d hd hdc hdF S hS hS1 hSc K hKd hLK
  obtain ⟨hCAK, hK⟩ := item611FieldL2KStar_holds h45 h49 G hst A hA hrank c hcA hc1 L hL hCA E hE
    hLE T hT hTL hTθ he hcE d hd hdc hdF S hS hS1 hSc K hKd hLK hSK hSKθ hcK
  obtain ⟨n, hn, ⟨φK⟩, -⟩ := item611FieldL2KField_holdsFix h45 h41 h413 G hst A hA hrank c hcA hc1 L
    hL hCA E hE hLE T hT hTL hTθ he hcE d hd hdc hdF K hK hCAK hLK hcK
  obtain ⟨-, -, m, hm, ⟨φ⟩, -⟩ := he
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.1.1
  have hdE : d ∈ E := hd.1
  have hdA : d ∈ A := hE.2 hdE
  have hd1 : d ≠ 1 := fun h => hdc (h ▸ Subgroup.one_mem _)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hL
  have hθodd := Res611Res3.odd_card_theta_of_config h45 hst hA hrank hcA hc1 hLc
  obtain ⟨hdN, hQ, -⟩ := Res611Res7.fieldCent_facts hm φ hdF hd3
  have hTd : T ≤ L ⊓ Subgroup.centralizer ({d} : Set G) := le_inf hTL fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hd.2 t ht)
  obtain ⟨hET, hTab, hT4⟩ := mem_fourGroups_iff.mp hT.1
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4]; norm_num)
  have hTK : T ≤ K := (le_sec11K_of_isPGroup_two hθodd hdN hd3 hQ.1 hTd hT2).trans hLK
  have hTθK : T ⊓ inSubgroup (aschbacherSolvableCore 3) K = ⊥ := by
    have h1 := Res611Fix.inf_thetaQuotCentralizer_eq_bot h45 h41 h413 hst hA hrank hdA hd1 hK
      hCAK hTab
    exact le_bot_iff.mp ((inf_le_inf_left T (theta_le_thetaQuotCentralizer K)).trans h1.le)
  set F := GaloisField 3 (3 * n) with hF
  set ψK := φK.trans (Sec4.projSLEquivPSL F) with hψK
  set θK := aschbacherSolvableCore 3 K with hθK
  set f : T →* PSL2 F := ψK.toMonoidHom.comp
    ((QuotientGroup.mk' θK).comp (Subgroup.inclusion hTK)) with hf
  have hfapp : ∀ t : T, f t = ψK (((Subgroup.inclusion hTK t : K)) : K ⧸ θK) := fun t => rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro t ht
    rw [hfapp, map_eq_one_iff _ ψK.injective, QuotientGroup.eq_one_iff] at ht
    have h1 : (t : G) ∈ T ⊓ inSubgroup (aschbacherSolvableCore 3) K := ⟨t.2, ⟨_, ht, rfl⟩⟩
    rw [hTθK, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  set V := f.range with hV
  have hVe : CFSG.Assembly.IsElemAbelian 2 V := by
    rw [hV, MonoidHom.range_eq_map]
    refine CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 2 f ⊤ ?_
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x _ => Subtype.ext ?_⟩
    · exact congrArg Subtype.val (hTab.1.is_comm.comm (a : T) (b : T))
    · exact hTab.2 x x.2
  have hV4 : Nat.card V = 4 := by
    rw [hV, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hfinj, Subgroup.card_top,
      hT4]
  have hFodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨3, 3 * n, Nat.prime_three, by decide, by omega, GaloisField.card 3 (3 * n) (by omega)⟩
  have hfix : ∀ g (hg : g ∈ Subgroup.normalizer (K : Set G)),
      g ∈ Subgroup.centralizer (T : Set G) →
        ∀ v ∈ V, MulAut.congr ψK (thetaAct K ⟨g, hg⟩) v = v := by
    rintro g hg hgT _ ⟨t, rfl⟩
    rw [hfapp]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
    rw [thetaAct_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe]
    have h1 := Subgroup.mem_centralizer_iff.mp hgT (t : G) t.2
    change g * (t : G) * g⁻¹ = (t : G)
    rw [← h1, mul_inv_cancel_right]
  have hLcC : L ≤ Subgroup.centralizer ({c} : Set G) := le_centralizer_of_mem_thetaComponentsAt hLc
  have hcT : c ∈ Subgroup.centralizer (T : Set G) := Subgroup.mem_centralizer_iff.mpr fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLcC (hTL ht))
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe hdA hd1 K hKd
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hAK hcA
  rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two] at hS
  obtain ⟨hSle, -, -⟩ := hS
  have hcomm : ∀ s ∈ S, ∀ hs : s ∈ Subgroup.normalizer (K : Set G),
      thetaAct K ⟨s, hs⟩ * thetaAct K ⟨c, hcN⟩ = thetaAct K ⟨c, hcN⟩ * thetaAct K ⟨s, hs⟩ := by
    intro s hsS hs
    have hsT : s ∈ Subgroup.centralizer (T : Set G) := (hSle hsS).2
    have h1 := commute_of_fix_kleinFour hFodd hVe hV4 (hfix s hs hsT) (hfix c hcN hcT)
    rw [← map_mul (MulAut.congr ψK), ← map_mul (MulAut.congr ψK)] at h1
    exact (MulAut.congr ψK).injective h1
  apply hSKθ
  rw [Subgroup.commutator_comm, commutator_le_theta_iff hSK, ← hSc, Subgroup.commutator_le]
  intro s hsS y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hs := hSK hsS
  have hck : c ^ k ∈ Subgroup.normalizer (K : Set G) := zpow_mem hcN k
  have hmem : ⁅s, c ^ k⁆ ∈ Subgroup.normalizer (K : Set G) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hs hck) (inv_mem hs)) (inv_mem hck)
  refine (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct hmem).mpr ?_
  have he1 : (⟨⁅s, c ^ k⁆, hmem⟩ : Subgroup.normalizer (K : Set G)) =
      ⁅(⟨s, hs⟩ : Subgroup.normalizer (K : Set G)), ⟨c, hcN⟩ ^ k⁆ := by
    apply Subtype.ext
    simp [commutatorElement_def]
  change thetaAct K ⟨⁅s, c ^ k⁆, hmem⟩ = 1
  rw [he1, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, map_zpow]
  have hc' : Commute (thetaAct K ⟨s, hs⟩) (thetaAct K ⟨c, hcN⟩ ^ k) :=
    (Commute.zpow_right (hcomm s hsS hs) k)
  rw [hc'.eq]
  group

theorem item611FieldL2Max_holdsFix (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h49 : Sec4.Item4_9) (h41 : Sec4.Item4_1LargePrime) (h413 : Sec4.Item4_13_forwardFix) :
    Item611FieldL2Max :=
  item611FieldL2Max_of_S (item611FieldL2S_holdsFix h45 h48 h49 h41 h413)

theorem item611FieldL2T_holdsFix (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (h41 : Sec4.Item4_1LargePrime) (h413 : Sec4.Item4_13_forwardFix) : Item611FieldL2T :=
  item611FieldL2T_of (item611FieldL2S_holdsFix h45 h48 h49 h41 h413)

end CertsS

end CFSG.RankThree.PartTwo.Sec6
