module

public import CFSG.Quasithin.Background.B69Iso
public import CFSG.Quasithin.Vol2.Ch9Sec3FFBList
public import CFSG.Quasithin.Vol2.Ch9Sec3FFDB51
public import CFSG.Quasithin.Vol2.Ch9Sec3FFDMod
public import CFSG.RankThree.PartOne.S11b.Sec109SylowTransport

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Vol2.Ch10.SecB.C11AmS
open scoped IsMulCommutative

section Num

theorem sl2_ne_60480 (n : ℕ) : (2 ^ n) * ((2 ^ n) ^ 2 - 1) ≠ 60480 := by
  intro h
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> norm_num at h
  · have hq : 64 ≤ 2 ^ n := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 64 * (64 ^ 2 - 1) ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
      Nat.mul_le_mul hq (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    omega

theorem sp4_ne_60480 (n : ℕ) :
    (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) ≠ 60480 := by
  intro h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num at h
  · have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 4 ^ (2 ^ 2) * (((4 ^ 2 - 1)) * (4 ^ 4 - 1)) ≤
        (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq _)
        (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1))
    omega

theorem g2_ne_60480 (n : ℕ) :
    (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) ≠ 60480 := by
  intro h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num at h
  · have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 4 ^ 6 * ((4 ^ 6 - 1) * (4 ^ 2 - 1)) ≤
        (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq 6)
        (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 6) 1)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
    omega

end Num

section Part2

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}

theorem part2_direct_of_card [Finite V] (h2 : B51Part2 L) (hN : Nat.card ↥L = 60480) :
    IsIntDirect (commV L) (fixV L) ⊤ := by
  by_contra hnd
  have hl := (h2.2 hnd).2
  rcases hl with ⟨n, F, _, _, hF, π, hπ⟩ | ⟨n, F, _, _, hF, π, hπ⟩ | ⟨n, F, _, _, hF, π, hπ⟩ |
    h | h | ⟨F, _, _, hF, π, hπ⟩ | ⟨F, _, _, hF, π, hπ⟩
  · have hc := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_two1527d, hF, hN] at hc
    exact sl2_ne_60480 n hc.symm
  · have hc := card_eq_of_nat_realizes1527d hπ
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF, hN, hI,
      Finset.prod_pair (by norm_num)] at hc
    exact sp4_ne_60480 n hc.symm
  · have := FFC.charP_two_of_card_pow hF
    have hcard : Nat.card ↥L = Nat.card ↥(CFSG.Open.quasithinG2 F) :=
      (Nat.card_congr (Equiv.ofBijective π
        ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
    rw [card_quasithinG2_1527d hF, hF, hN] at hcard
    exact g2_ne_60480 n hcard.symm
  · exact not_alternatingNatural1527d (n := 6) (by norm_num) (by rw [hN]; decide) h
  · obtain ⟨π, hπ⟩ := h
    have hinj := FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
    have hc : Nat.card ↥(alternatingGroup (Fin 8)) = Nat.card ↥L :=
      Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)
    rw [card_alternatingGroup1527d 8 (by norm_num), hN] at hc
    exact absurd hc (by decide)
  · have hG2 := card_quasithinG2_1527d hF
    rw [hF] at hG2
    have hfin : Finite ↥(CFSG.Open.quasithinG2 F) :=
      Nat.finite_of_card_ne_zero (by rw [hG2]; norm_num)
    have h1 : Nat.card ↥L ∣
        Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ :=
      Subgroup.card_dvd_of_surjective hπ.1
    have h2 : Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ ∣
        Nat.card ↥(CFSG.Open.quasithinG2 F) := by
      refine Subgroup.card_dvd_of_le ?_
      rw [Subgroup.commutator_le]
      intro a ha b hb
      exact (CFSG.Open.quasithinG2 F).mul_mem
        ((CFSG.Open.quasithinG2 F).mul_mem ((CFSG.Open.quasithinG2 F).mul_mem ha hb)
          ((CFSG.Open.quasithinG2 F).inv_mem ha)) ((CFSG.Open.quasithinG2 F).inv_mem hb)
    have h3 := h1.trans h2
    rw [hG2, hN] at h3
    norm_num at h3
  · have hc := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_three1527d, hF, hN] at hc
    exact absurd hc (by norm_num)

end Part2

section Factor

theorem not_noOrderFour_sl3_charTwo {F : Type} [Field F] [CharP F 2] :
    ¬ L246C127.NoOrderFour (Matrix.SpecialLinearGroup (Fin 3) F) := by
  intro h
  apply L246C127.not_noOrderFour_sl3
  set f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F with hf
  have hfi : Function.Injective f := f.injective
  set φ := Matrix.SpecialLinearGroup.map (n := Fin 3) f with hφ
  have hφi : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    ext i j
    have := congrArg
      (fun g : Matrix.SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) i j) hab
    exact hfi this
  intro g hg
  apply hφi
  rw [map_pow, map_one]
  exact h (φ g) (by rw [← map_pow, hg, map_one])

theorem notB56Factor_of_card {V : Type} [CommGroup V] {K : Subgroup (MulAut V)}
    (hcardK : Nat.card ↥K = 60480) (hK4 : ¬ L246C127.NoOrderFour ↥K) :
    InternalSec.NotB56Factor K := by
  intro X hKX _ hX
  have hX4 : ¬ L246C127.NoOrderFour ↥X := fun h => hK4
    ((FFD.noOrderFour_subgroup h (K.subgroupOf X)).of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hKX).symm)
  have hfinK : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [hcardK]; norm_num)
  rcases hX with (⟨n, F, _, _, -, hF, he⟩ | he | ⟨m, F, _, _, -, hmo, hF, he⟩) | he | he |
      ⟨n, F, _, _, hF, π, hπ⟩
  · obtain ⟨e⟩ := he
    have := Fintype.ofFinite F
    have : CharP F 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
    exact hX4 (FFD.noOrderFour_of_surjective e.symm.toMonoidHom e.symm.surjective)
  · obtain ⟨e⟩ := he
    have hdvd : 60480 ∣ Nat.card ↥X := hcardK ▸ Subgroup.card_dvd_of_le hKX
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      at hdvd
    exact absurd hdvd (by decide)
  · obtain ⟨e⟩ := he
    have hdvd : 60480 ∣ Nat.card ↥X := hcardK ▸ Subgroup.card_dvd_of_le hKX
    have h5 : 5 ∣ Nat.card ↥X := (by norm_num : 5 ∣ 60480).trans hdvd
    rw [Nat.card_congr e.toEquiv] at h5
    exact FFD.not_five_dvd_card_sl3 hmo hF h5
  · obtain ⟨e⟩ := he
    have hdvd : 60480 ∣ Nat.card ↥X := hcardK ▸ Subgroup.card_dvd_of_le hKX
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at hdvd
    exact absurd hdvd (by decide)
  · obtain ⟨e⟩ := he
    have hdvd : 60480 ∣ Nat.card ↥X := hcardK ▸ Subgroup.card_dvd_of_le hKX
    rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three,
      Nat.card_zmod] at hdvd
    exact absurd hdvd (by decide)
  · have := Fintype.ofFinite F
    have : CharP F 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
    exact hX4 (FFD.noOrderFour_of_surjective π hπ)

theorem card_center_sl3_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) = 3 := by
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (i := (0 : Fin 3)) (R := F)
  rw [Nat.card_congr e.toEquiv, Fintype.card_fin]
  have hU : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have htop : rootsOfUnity 3 F = ⊤ := by
    ext u
    simp only [Subgroup.mem_top, iff_true, mem_rootsOfUnity]
    rw [← hU]
    exact pow_card_eq_one'
  rw [htop, Subgroup.card_top, hU]

end Factor

section SL34

variable {G : Type} [Group G] [Finite G]

theorem isIntDirect_of_sl34 (h51 : AsB51) (h56 : AsB56) {Y T KY U : Subgroup G}
    [IsMulCommutative ↥U] (hSQ : SQTKGroup ↥Y) (hT : IsSylowTwoOf T Y) (hKYc : KY ∈ cComp Y)
    (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) (hred : IsTwoReducedIn Y U)
    (hJ : ¬ ⁅KY, thompsonJ T⁆ ≤ Subgroup.centralizer (U : Set G))
    (hqKY : CFSG.IsQuasisimple (O2Q KY)) (hqA : CFSG.IsQuasisimple ↥(autOn KY U))
    (hlist : B56QuasisimpleList ↥(autOn KY U)) (h60 : 60 ∣ Nat.card ↥(autOn KY U))
    (hSL : IsSL3 4 (O2Q KY)) :
    IsIntDirect (commV (autOn KY U)) (fixV (autOn KY U)) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVe : IsElemAbelian 2 U := hred.2.2.1
  have hYU : Y ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  have hKYY : KY ≤ Y := le_of_mem_cComp hKYc
  have hKYN : KY ≤ Subgroup.normalizer (U : Set G) := hKYY.trans hYU
  have hO2 : pCoreOf 2 (autOn Y U) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hle : autOn KY U ≤ autOn Y U := InternalSec.autOn_le_autOn_of_le hKYY
  have hn : ((autOn KY U).subgroupOf (autOn Y U)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hle).mpr fun k a hk ha => ?_
    exact InternalSec.autOn_normal_of (U := U) hYKY a ha k hk
  have hO2KY : pCoreOf 2 (autOn KY U) = ⊥ := by
    have h := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _ hle hn
    rw [hO2] at h
    exact le_bot_iff.1 h
  set π : O2Q KY →* ↥(autOn KY U) := QuotientGroup.lift (CFSG.pCore 2 ↥KY)
    (InternalSec.autOnHom hKYN) (InternalSec.pCore_le_ker_autOnHom hKYN hO2KY) with hπdef
  have hπs : Function.Surjective π :=
    QuotientGroup.lift_surjective_of_surjective _ _ (InternalSec.autOnHom_surjective hKYN) _
  have hπne : π.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := InternalSec.exists_noncomm_of_isQuasisimple hqA
    obtain ⟨x, rfl⟩ := hπs a
    obtain ⟨y, rfl⟩ := hπs b
    have hx : x ∈ π.ker := by rw [htop]; exact Subgroup.mem_top x
    have hy : y ∈ π.ker := by rw [htop]; exact Subgroup.mem_top y
    rw [MonoidHom.mem_ker] at hx hy
    rw [hx, hy] at hab
    exact hab rfl
  have hπZ : π.ker ≤ Subgroup.center (O2Q KY) :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hqKY inferInstance).resolve_left hπne
  obtain ⟨F, _, _, hF, ⟨e3⟩⟩ := hSL
  have : CharP F 2 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  set e : O2Q KY ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    e3.trans (specialLinearGroupEquivStatedSL 3 F).symm with he
  have hcardSL : Nat.card (O2Q KY) = 60480 := by
    rw [Nat.card_congr e3.toEquiv, card_statedSL_three1527d, hF]
    norm_num
  have hZ : Nat.card (Subgroup.center (O2Q KY)) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact card_center_sl3_four hF
  have hk3 : Nat.card π.ker ∣ 3 := by
    have := Subgroup.card_dvd_of_le hπZ
    rwa [hZ] at this
  have hπcard := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  rw [hcardSL, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv] at hπcard
  have hπi : π.ker = ⊥ := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hkZ : π.ker = Subgroup.center (O2Q KY) :=
        Subgroup.eq_of_le_of_card_ge hπZ (by rw [h3, hZ])
      set eP : ↥(autOn KY U) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
        (QuotientGroup.quotientKerEquivOfSurjective π hπs).symm.trans
          ((QuotientGroup.quotientMulEquivOfEq hkZ).trans
            ((QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
              (projectiveSpecialLinearGroupEquivStatedProj 3 F))) with heP
      have hc : Nat.card ↥(autOn KY U) = 2 ^ 6 * 315 := by
        rw [h3] at hπcard
        omega
      rcases FFB.b56_of_chk hlist hqA h60 hc (by decide) (P := fun c => c == 315)
          (by decide) (by decide) with ⟨h, -⟩ | ⟨-, -, ⟨e4⟩⟩
      · omega
      · exact B69.not_equiv_sl_four_psl_three (K := ZMod 2) (F := F) (by simp) hF
          (e4.trans ((specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm.trans
            ((CFSG.RankThree.PartOne.Sec109.projectiveSLEquivSL_two (by simp) (by norm_num)).trans
              (B69.statedProjEquivProjectiveSL 4 (ZMod 2)).symm))) eP
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hπi
  set eA : O2Q KY ≃* ↥(autOn KY U) := MulEquiv.ofBijective π ⟨hπinj, hπs⟩ with heA
  have hcard : Nat.card ↥(autOn KY U) = 60480 := by
    rw [← Nat.card_congr eA.toEquiv, hcardSL]
  have h4 : ¬ L246C127.NoOrderFour ↥(autOn KY U) := fun h =>
    not_noOrderFour_sl3_charTwo (F := F) (h.of_mulEquiv (e.symm.trans eA))
  have hker : IsPGroup 2 ↥(KY ⊓ Subgroup.centralizer (U : Set G)) := by
    intro x
    have hx1 : (⟨(x : G), x.2.1⟩ : ↥KY) ∈ (InternalSec.autOnHom hKYN).ker :=
      (InternalSec.mem_ker_autOnHom hKYN _).2 x.2.2
    have hx2 : (QuotientGroup.mk ⟨(x : G), x.2.1⟩ : O2Q KY) ∈ π.ker := by
      rw [MonoidHom.mem_ker, hπdef, QuotientGroup.lift_mk]
      exact hx1
    rw [hπi, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hx2
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥KY)) ⟨_, hx2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (⟨(x : G), x.2.1⟩ : ↥KY) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val h1
    simpa using h2
  have hSA : SQTKGroup ↥(autOn KY U) :=
    InternalSec.sqtkGroup_autOn hKYN (K8.sqtkGroup_of_le hSQ hKYY) hker
  obtain ⟨A, -, hA, hLA⟩ := FFD.exists_offender_of_commutator hVe hred hT hKYY hYKY hqA le_rfl hJ
  have hV2 : ∀ w ∈ U, w ^ 2 = 1 := fun w hw => by simpa [pow_two] using hVe.2 w hw
  obtain ⟨hB, -⟩ := InternalSec.b51Hyp_ffJ_autOn_of_b56_of_notFactor h56 hV2 hYU hKYY hYKY
    hSQ hO2 hqA hSA hA hLA (notB56Factor_of_card hcard h4)
  have hV2' : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hVe.2 v v.2)
  obtain ⟨-, hP2, -⟩ := h51 ↥U hV2' _ _ hB
  exact part2_direct_of_card hP2 hcard

end SL34

section Direct

variable {G : Type} [Group G]

theorem false_of_isIntDirect {KY K U U₀ : Subgroup G} {v : G} [IsMulCommutative ↥U]
    (hKYN : KY ≤ Subgroup.normalizer (U : Set G)) (hKKY : K ≤ KY)
    (hdir : IsIntDirect (commV (autOn KY U)) (fixV (autOn KY U)) ⊤) (hU₀ : U₀ ≤ U)
    (hU₀K : U₀ ≤ ⁅U₀, K⁆) (hv : v ∈ U₀) (hv1 : v ≠ 1)
    (hKYv : KY ≤ Subgroup.centralizer ({v} : Set G)) : False := by
  have hvU : v ∈ U := hU₀ hv
  have h1 : (⟨v, hvU⟩ : ↥U) ∈ commV (autOn KY U) := by
    rw [commV_autOn_eq1527d hKYN, Subgroup.mem_subgroupOf]
    exact Subgroup.commutator_mono hU₀ hKKY (hU₀K hv)
  have h2 : (⟨v, hvU⟩ : ↥U) ∈ fixV (autOn KY U) := by
    rw [FFD.fixV_autOn_eq hKYN, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hKYv hk) v rfl).symm
  have h3 : (⟨v, hvU⟩ : ↥U) ∈ commV (autOn KY U) ⊓ fixV (autOn KY U) := ⟨h1, h2⟩
  rw [hdir.2, Subgroup.mem_bot] at h3
  exact hv1 (congrArg Subtype.val h3)

end Direct

end CFSG.Quasithin.H13.Ch9.KGFF
