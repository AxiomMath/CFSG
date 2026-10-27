module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProofQL
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec16.Item163ProofY4
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

section Tools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_isL3TwoPow_of_a7 {L : Subgroup G}
    (h7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))) :
    ¬ IsL3TwoPow L := by
  rintro ⟨n, -, hn⟩
  obtain ⟨φ⟩ := h7
  have h2 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 := by
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact not_isoLThreePi_of_card_eq_2520 h2 2 n hn

theorem cover_of_isL3TwoPow {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h1514 : Item1514 A (lB A) c L) (hMeets : Step163Meets) (h32 : IsL3TwoPow L)
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hLY : L ≤ Y) :
    Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∧ omegaA A = {Subgroup.zpowers c} ∧
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) := by
  rcases h1514 Y hY (hMeets G A c L h Y hY hLY) with ⟨hcov, -, hΩ, hprod, -⟩ | ⟨h7, -⟩ |
    ⟨-, -, -, -, hno, -⟩
  · exact ⟨hcov, hΩ, hprod⟩
  · exact absurd h32 (not_isL3TwoPow_of_a7 h7)
  · exact absurd hLY (hno Y hY)

theorem isEmpty_m12_of_le {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h1514 : Item1514 A (lB A) c L) (hMeets : Step163Meets) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (hLY : L ≤ Y) :
    IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) := by
  rcases h1514 Y hY (hMeets G A c L h Y hY hLY) with ⟨-, -, -, -, h12⟩ | ⟨⟨φ⟩, -⟩ |
    ⟨-, -, -, -, hno, -⟩
  · exact h12
  · exact ⟨fun ψ => KFacts.KS14.isEmpty_mulEquiv_M12_alternating.2.1.false (ψ.symm.trans φ)⟩
  · exact absurd hLY (hno Y hY)

theorem hasInvEven_of_not_odd {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hθ : ¬ Odd (Nat.card (aschbacherSolvableCore 3 ↥L))) : HasInvEven A L := by
  obtain ⟨-, hchar, h3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  have hcard : Nat.card (θ.map L.subtype) = Nat.card θ :=
    Subgroup.card_map_of_injective L.subtype_injective
  refine ⟨θ.map L.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · have := hchar
    exact h.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic θ)
  · rwa [hcard]
  · rw [hcard]
    exact even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hθ)

theorem exists_scriptQPi_two_of_hasInvEven {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h142 : Concl142 A (lB A)) (hK : HasInvEven A L) :
    ∃ Q ∈ scriptQPi A (lB A) L (piOf 2), Q ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  obtain ⟨K, hKL, hAK, hK3, hK2⟩ := hK
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  obtain ⟨R, hRK, hR2, hAR, hRcard⟩ :=
    Sec17.HeadProof.exists_invariant_sylow hA3 hK3 hAK Nat.prime_two
  have hR1 : R ≠ ⊥ := by
    intro h0
    have hpos : 0 < (Nat.card K).factorization 2 :=
      Nat.prime_two.factorization_pos_of_dvd Nat.card_pos.ne' hK2
    rw [h0, Subgroup.card_bot] at hRcard
    have : 2 ≤ 2 ^ (Nat.card K).factorization 2 :=
      Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hpos) 2
    omega
  have hRL : R ≤ L := hRK.trans hKL
  have hR3 : ¬ 3 ∣ Nat.card R := fun h3 => hK3 (h3.trans (Subgroup.card_dvd_of_le hRK))
  have hRH : R ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3) :=
    ⟨hRL.trans (hD.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)),
      (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩
  exact ⟨R, ⟨⟨mem_scriptQ_of_concl142 h142 h.zpowers_mem_omegaA hRH, hRL⟩,
    (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR2⟩, hR1⟩

theorem pCoreOf_sup_ne_bot_of_le {L Y R : Subgroup G} (hLY : L ≤ Y) (hR : R ≠ ⊥)
    (hRO : R ≤ CFSG.Open.pCoreOf 2 (Y ⊔ R)) : CFSG.Open.pCoreOf 2 (R ⊔ L) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 (Y ⊔ R) with hO
  have hIle : R ⊔ L ≤ Y ⊔ R := sup_le le_sup_right (hLY.trans le_sup_left)
  have hN : R ⊔ L ≤ Subgroup.normalizer ((O ⊓ (R ⊔ L) : Subgroup G) : Set G) :=
    (le_inf (hIle.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hp : IsPGroup 2 ↥(O ⊓ (R ⊔ L)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (Y ⊔ R)).to_le inf_le_left
  have hle : O ⊓ (R ⊔ L) ≤ CFSG.Open.pCoreOf 2 (R ⊔ L) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hN hp
  intro h0
  apply hR
  rw [eq_bot_iff, ← h0]
  exact (le_inf hRO le_sup_left).trans hle

theorem pCoreOf_delta_mem_scriptQPi {A : Subgroup G} (h142 : Concl142 A (lB A))
    (h143 : Concl143 A (lB A)) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) ∈
      scriptQPi A (lB A) ⊤ (piOf 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := delta A (lB A) (Subgroup.centralizer ({a} : Set G)) with hD
  set R := CFSG.Open.pCoreOf 2 D with hR
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) D
  have hRD : R ≤ D := CFSG.LieType.BorelTits.pCoreOf_le 2 D
  have hDC : D ≤ Subgroup.centralizer ({a} : Set G) := delta_le _
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hAD.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D)
  have hR3 : ¬ 3 ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hRQ : R ∈ scriptQ A (lB A) := by
    by_cases hΩ : Subgroup.zpowers a ∈ omegaA A
    · exact mem_scriptQ_of_concl142 h142 hΩ ⟨(hRD.trans hDC).trans
        (centralizer_singleton_le_normalizer_zpowers a),
        (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩
    · obtain ⟨Q', hQ', hRQ'⟩ := exists_le_mem_maxInvariantPiSubgroups
        (⟨hRD, (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩ :
          R ∈ invariantPiSubgroups D A (piCompl 3))
      exact mem_scriptQ_of_le (h143 a ha ha1 hΩ Q' hQ').1 hRQ' hAR
  exact ⟨⟨hRQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR2⟩

theorem xA_le_normalizer_pCoreOf_delta {A : Subgroup G} {a : G} (ha : a ∈ A) :
    xA A ≤ Subgroup.normalizer
      (CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) : Set G) := by
  intro x hx
  have hxC : x ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hx
  have hxN : x ∈ Subgroup.normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ hxC
  have hxa : x ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha) hxC
  have hCa : (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj x).toMonoidHom =
      Subgroup.centralizer ({a} : Set G) :=
    Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hxa)
  have hD : x ∈ Subgroup.normalizer
      ((delta A (lB A) (Subgroup.centralizer ({a} : Set G)) : Subgroup G) : Set G) :=
    mem_normalizer_of_map_conj_eq (by rw [Sec17.HeadProof.map_conj_delta hxN, hCa])
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hD

theorem xA_le_normalizer_of_goodR163 {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    (h1411 : Item1411_1 A (lB A)) {R : Subgroup G} (hRgood : GoodR163 A L R)
    (hΔ : ∀ Y ∈ scriptY0Star A (lB A), R ≤ Subgroup.normalizer (Y : Set G) →
      delta A (lB A) (Subgroup.normalizer (CFSG.Open.pCoreOf 2 (R ⊔ L) : Set G)) ≤
        Subgroup.normalizer (Y : Set G)) :
    ∀ Y ∈ scriptY0Star A (lB A), xA A ≤ Subgroup.normalizer (Y : Set G) := by
  have hXP := xA_le_delta_normalizer h hRgood.2.1
  intro Y hY
  obtain ⟨S₀, hS₀, hS₀Y⟩ := exists_qStar_le_normalizer h153 hobs hY
  obtain ⟨w, hw, hRw⟩ := exists_conj_le_normalizer h1411 hS₀ hS₀Y hRgood.1
  have hYw := map_conj_mem_scriptY0Star hw hY
  have h1 : xA A ≤ Subgroup.normalizer
      ((Y.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G) :=
    hXP.trans (hΔ _ hYw hRw)
  have h2 : (xA A).map (MulAut.conj w).toMonoidHom ≤
      (Subgroup.normalizer (Y : Set G)).map (MulAut.conj w).toMonoidHom := by
    rw [map_conj_xA hw, Subgroup.map_equiv_normalizer_eq]
    exact h1
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj w).injective).mp h2

theorem exists_scriptQPiStar_inf {A L Y Q : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hLY : L ≤ Y)
    (hQ : Q ∈ scriptQPi A (lB A) L (piOf 2)) :
    ∃ S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2),
      S ⊓ L ∈ scriptQPiStar A (lB A) L (piOf 2) ∧ Q ≤ S ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hQT, hT⟩ :=
    Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) L (piOf 2))) hQ
  have hTN : T ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2) :=
    ⟨⟨hT.prop.1.1, hT.prop.1.2.trans (hLY.trans Subgroup.le_normalizer)⟩, hT.prop.2⟩
  obtain ⟨S, hTS, hS⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2))) hTN
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hSL : S ⊓ L ∈ scriptQPi A (lB A) L (piOf 2) := by
    refine ⟨⟨mem_scriptQ_of_le hS.prop.1.1 inf_le_left ?_, inf_le_right⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hS2.to_le inf_le_left)⟩
    exact (le_inf hS.prop.1.1.1.2.2 hAL).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hTSL : T ≤ S ⊓ L := le_inf hTS hT.prop.1.2
  have hSLT : S ⊓ L = T := le_antisymm (hT.2 hSL hTSL) hTSL
  refine ⟨S, hS, ?_, hQT.trans hTSL⟩
  rw [hSLT]
  exact hT

end Tools

section Y4

variable {G : Type} [Group G] [Finite G]

theorem eq_oPrimeResidualOf_of_isSimpleGroup {L : Subgroup G} (hLp : Group.IsPerfect ↥L)
    (hsimp : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) (h3 : 3 ∣ Nat.card L) :
    L = oPrimeResidualOf 3 L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθ := solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set N := oPrimeResidual 3 ↥L with hNdef
  have hNn : N.Normal := oPrimeResidual_normal 3 ↥L
  have hmapn : (N.map (QuotientGroup.mk' θ)).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective θ)
  have hsup : N ⊔ θ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' θ)) with
      hbot | htop
    · exfalso
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
      have hx3 : x ^ 3 = 1 := by rw [← hx, pow_orderOf_eq_one]
      have hxN : x ∈ N := Subgroup.subset_closure ⟨1, by rw [pow_one]; exact hx3⟩
      have hxθ : x ∈ θ := by
        have hmem : QuotientGroup.mk' θ x ∈ N.map (QuotientGroup.mk' θ) :=
          Subgroup.mem_map_of_mem _ hxN
        rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
        exact hmem
      rw [eq_one_of_mem_aschbacherSolvableCore hxθ hx3, orderOf_one] at hx
      omega
    · have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' θ) N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp θ.subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hx : x ∈ N ⊔ θ := hsup ▸ Subgroup.mem_top x
    rw [Subgroup.mem_sup_of_normal_left] at hx
    obtain ⟨n, hn, t, ht, rfl⟩ := hx
    refine ⟨⟨t, ht⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  have : Group.IsSolvable θ := hθ.1
  have hsolv : Group.IsSolvable (↥L ⧸ N) := Group.isSolvable_of_surjective hsurj
  have hperf : Group.IsPerfect (↥L ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hNtop : N = ⊤ := by
    by_contra hne
    have : Nontrivial (↥L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    exact Group.IsPerfect.not_isSolvable (↥L ⧸ N) hsolv
  rw [oPrimeResidualOf, ← hNdef, hNtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem eq_oPrimeResidualOf_of_sec15R
    {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L) : L = oPrimeResidualOf 3 L := by
  have hLc : L ∈ thetaComponentsAt 3 c := h.toSec13Data.mem_thetaComponentsAt
  have hz := Sec15.center_eq_bot_of_types hLc
    (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  have hsimp : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    have e : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ⧸
        Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃*
          ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    exact (MulEquiv.isSimpleGroup_congr e).mp hq.2.1
  exact eq_oPrimeResidualOf_of_isSimpleGroup (Sec6.isPerfect_of_mem_thetaComponentsAt hLc) hsimp
    (three_dvd_card_of_mem_lA h h.zpowers_mem_omegaA h.mem_lA)

theorem eq_delta_of_cover {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h142 : Concl142 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY4 A (lB A)) (hLY : L ≤ Y)
    (hcov : Y ≤ L ⊔ CFSG.Open.pCoreOf 2 Y) : L = delta A (lB A) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  set D := delta A (lB A) L with hDdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hY.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hLH : L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hD.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hmem : ∀ R : Subgroup G, R ≤ L → ¬ 3 ∣ Nat.card R →
      A ≤ Subgroup.normalizer (R : Set G) → R ≤ D := fun R hRL hR3 hAR =>
    le_delta (mem_scriptQ_of_concl142 h142 h.zpowers_mem_omegaA ⟨hRL.trans hLH,
      (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩) hRL
  have hDL : D ≤ L := delta_le L
  have hQ : ∀ Q ∈ collectionIn (scriptQ A (lB A)) Y, Q ≤ D ⊔ O := by
    rintro Q ⟨hQ, hQY⟩
    have hQO : IsPiSubgroup (piCompl 3) (Q ⊔ O) := isPiSubgroup_piCompl_sup hQ.1.2.1
      ((isPiSubgroup_piCompl_iff Nat.prime_three O).mpr hO3) (hQY.trans hYO)
    have hR : (Q ⊔ O) ⊓ L ≤ D := hmem _ inf_le_right
      (fun h3 => (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hQO
        (h3.trans (Subgroup.card_dvd_of_le inf_le_left)))
      ((le_inf (le_normalizer_sup hQ.1.2.2 hAO) hD.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
    intro q hq
    have hqY : q ∈ ((L ⊔ O : Subgroup G) : Set G) := hcov (hQY hq)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L O (hLY.trans hYO)] at hqY
    obtain ⟨l, hl, o, ho, rfl⟩ := hqY
    have hlR : l ∈ (Q ⊔ O) ⊓ L := by
      refine Subgroup.mem_inf.mpr ⟨?_, hl⟩
      have hlo : l = (l * o) * o⁻¹ := by group
      rw [hlo]
      exact mul_mem (Subgroup.mem_sup_left hq) (inv_mem (Subgroup.mem_sup_right ho))
    exact mul_mem (Subgroup.mem_sup_left (hR hlR)) (Subgroup.mem_sup_right ho)
  have hYle : Y ≤ D ⊔ O :=
    hY.2.2.1.le.trans (show delta A (lB A) Y ≤ D ⊔ O from sSup_le hQ)
  have hLO : L ⊓ O ≤ D := hmem _ inf_le_left
    (fun h3 => hO3 (h3.trans (Subgroup.card_dvd_of_le inf_le_right)))
    ((le_inf hD.le_normalizer hAO).trans Subgroup.inf_normalizer_le_normalizer_inf)
  refine le_antisymm (fun l hl => ?_) hDL
  have hl' : l ∈ ((D ⊔ O : Subgroup G) : Set G) := hYle (hLY hl)
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D O (hDL.trans (hLY.trans hYO))] at hl'
  obtain ⟨d, hd, o, ho, rfl⟩ := hl'
  have hoL : o ∈ L := by
    have := mul_mem (inv_mem (hDL hd)) hl
    rwa [inv_mul_cancel_left] at this
  exact mul_mem hd (hLO ⟨hoL, ho⟩)

theorem mem_scriptY4_of_cover
    {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h142 : Concl142 A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY4 A (lB A)) (hLY : L ≤ Y) (hcov : Y ≤ L ⊔ CFSG.Open.pCoreOf 2 Y) :
    L ∈ scriptY4 A (lB A) :=
  ⟨⟨fun hL => hY.1.1 (top_le_iff.mp (hL ▸ hLY)), h.toSec13Data.le_normalizer⟩,
    eq_oPrimeResidualOf_of_sec15R h, eq_delta_of_cover h h142 hY hLY hcov,
    isQuasisimple_of_cover hY hLY hcov (three_dvd_card_of_mem_lA h h.zpowers_mem_omegaA h.mem_lA)⟩

theorem mem_scriptY4_of_le
    {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h142 : Concl142 A (lB A)) (h1514 : Item1514 A (lB A) c L)
    (hMeets : Step163Meets) (hA7 : Step163L4A7) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (hLY : L ≤ Y) : L ∈ scriptY4 A (lB A) := by
  by_cases hcov : Y ≤ L ⊔ CFSG.Open.pCoreOf 2 Y
  · exact mem_scriptY4_of_cover h h142 hY.prop.1 hLY hcov
  · rcases h1514 Y hY (hMeets G A c L h Y hY hLY) with ⟨hc, -⟩ | ⟨h7, -⟩ |
      ⟨-, -, -, -, hno, -⟩
    · exfalso
      apply hcov
      rw [inf_eq_right.mpr hLY] at hc
      exact hc.le
    · exact hA7 G A c L h h7 Y hY hLY hcov
    · exact absurd hLY (hno Y hY)

theorem delta_normalizer_le_of_mem_scriptY4 {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h155 : Item155 A (lB A)) (hL4 : L ∈ scriptY4 A (lB A))
    (hO : CFSG.Open.pCoreOf 2 L ≠ ⊥) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hLY : L ≤ Y) :
    delta A (lB A) (Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G)) ≤
      Subgroup.normalizer (Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL3 : oPrimeResidualOf 3 L = L := hL4.2.1.symm
  have hOL : CFSG.Open.pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hY3 : L ∈ scriptY3 A (lB A) := ⟨⟨hL4.1, hO⟩, hL4.2.2.1⟩
  have hX4 : oPrimeResidualOf 3 L ∈ scriptY4 A (lB A) := by
    rw [hL3]
    exact hL4
  have hLeq : L = oPrimeResidualOf 3 L ⊔ CFSG.Open.pCoreOf 2 L := by
    rw [hL3]
    exact (sup_eq_left.mpr hOL).symm
  have hΓ : Y ∈ gam155 A (lB A) L (oPrimeResidualOf 3 L) := by
    refine ⟨hY, ?_, hLY.trans Subgroup.le_normalizer⟩
    rw [hL3]
    exact hLY
  have hΩ : omg155 A (oPrimeResidualOf 3 L) := by
    rw [hL3]
    exact Or.inr ⟨c, L, h.zpowers_mem_omegaA, h.mem_lA, by rw [inf_idem, sup_eq_left.mpr hOL]⟩
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hO2 hO
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hAL : A ⊔ L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    sup_le (h.toSec13Data.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ L : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hle (hAL hx)⟩
  exact (delta_mono hle).trans ((h155 L hY3 hX4 hLeq).2 Y hΓ (Or.inl hΩ) M hMm)

omit [Finite G] in
theorem mem_of_pow_three_of_mem_sup {L Q : Subgroup G}
    (hQL : Q ≤ Subgroup.normalizer (L : Set G)) (hQ2 : IsPGroup 2 Q) {x : G}
    (hx : x ∈ L ⊔ Q) {k : ℕ} (hxk : x ^ 3 ^ k = 1) : x ∈ L := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left L Q hQL] at hx
  obtain ⟨l, hl, q, hq, rfl⟩ := hx
  have key : ∀ m : ℕ, (l * q) ^ m * (q ^ m)⁻¹ ∈ L := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (l * q) ^ (m + 1) * (q ^ (m + 1))⁻¹ =
          ((l * q) ^ m * (q ^ m)⁻¹) * (q ^ m * l * (q ^ m)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      exact mul_mem ih ((Subgroup.mem_normalizer_iff.mp (hQL (pow_mem hq m)) l).mp hl)
  have hqL : q ^ 3 ^ k ∈ L := by
    have h1 := key (3 ^ k)
    rw [hxk, one_mul] at h1
    exact inv_mem_iff.mp h1
  obtain ⟨j, hj⟩ := hQ2 ⟨q, hq⟩
  have hqj : q ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcop : Nat.Coprime (3 ^ k) (orderOf q) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hqj)
      (Nat.Coprime.pow k j (by norm_num))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hqL' : q ∈ L := by
    rw [← hm]
    exact pow_mem hqL m
  exact mul_mem hl hqL'

theorem delta_normalizer_le_of_centralizer {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h155 : Item155 A (lB A))
    (hQ142 : ∀ Q ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3), Q ∈ scriptQ A (lB A))
    (hL4 : L ∈ scriptY4 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hLY : L ≤ Y) {R : Subgroup G} (hR : GoodR163 A L R)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hne : CFSG.Open.pCoreOf 2 L ≠ ⊥ ∨
      CFSG.Open.pCoreOf 2 (R ⊔ L) ⊓ Subgroup.centralizer ({c} : Set G) ≠ ⊥) :
    delta A (lB A) (Subgroup.normalizer (CFSG.Open.pCoreOf 2 (R ⊔ L) : Set G)) ≤
      Subgroup.normalizer (Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set P := CFSG.Open.pCoreOf 2 (R ⊔ L) with hPdef
  set Q := P ⊓ Subgroup.centralizer ({c} : Set G) with hQdef
  set Y' := L ⊔ Q with hY'def
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (R ⊔ L)
  have hPne : P ≠ ⊥ := hR.2.2
  have hLP : L ≤ Subgroup.normalizer (P : Set G) :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (R ⊔ L))
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    (le_normalizer_sup hR.1.1.1.1.2.2 hD.le_normalizer).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (R ⊔ L))
  have hQ2 : IsPGroup 2 Q := hP2.to_le inf_le_left
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := hD.le_centralizer
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute ha hD.mem_A)
  have hCN : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) :=
    (le_inf hLP (hLc.trans hCN)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    (le_inf hAP (hAc.trans hCN)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hQL : Q ≤ Subgroup.normalizer (L : Set G) :=
    (inf_le_right.trans (centralizer_singleton_le_normalizer_zpowers c)).trans
      (normalizer_zpowers_le_normalizer_L h
        (three_dvd_card_of_mem_lA h h.zpowers_mem_omegaA h.mem_lA))
  have hQ3 : ¬ 3 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hQQ : Q ∈ scriptQ A (lB A) := hQ142 Q ⟨inf_le_right.trans
    (centralizer_singleton_le_normalizer_zpowers c),
    (isPiSubgroup_piCompl_iff Nat.prime_three Q).mpr hQ3, hAQ⟩
  have hY'c : Y' ≤ Subgroup.centralizer ({c} : Set G) := sup_le hLc inf_le_right
  have hY'L : Y' ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hQL
  have hY'Q : Y' ≤ Subgroup.normalizer (Q : Set G) := sup_le hLQ Subgroup.le_normalizer
  have hQO : Q ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hY'Q hQ2
  have hOLO : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
      (hY'L.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L)
  have hO2 : CFSG.Open.pCoreOf 2 Y' ≠ ⊥ := by
    rcases hne with h1 | h1
    · exact fun h0 => h1 (le_bot_iff.mp (h0 ▸ hOLO))
    · exact fun h0 => h1 (le_bot_iff.mp (h0 ▸ hQO))
  have hY'Δ : Y' = delta A (lB A) Y' :=
    le_antisymm (sup_le (hL4.2.2.1.le.trans (delta_mono le_sup_left)) (le_delta hQQ le_sup_right))
      (delta_le _)
  have hY'top : Y' ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hD.ne_one (top_le_iff.mp (htop ▸ hY'c))
  have hY'3 : Y' ∈ scriptY3 A (lB A) :=
    ⟨⟨⟨hY'top, le_normalizer_sup hD.le_normalizer hAQ⟩, hO2⟩, hY'Δ⟩
  have hres : oPrimeResidualOf 3 Y' = L :=
    ((oPrimeResidualOf_eq_of_le le_sup_left fun x hx k hk =>
      mem_of_pow_three_of_mem_sup hQL hQ2 hx hk).symm.trans hL4.2.1.symm)
  have hX4 : oPrimeResidualOf 3 Y' ∈ scriptY4 A (lB A) := by
    rw [hres]
    exact hL4
  have hY'eq : Y' = oPrimeResidualOf 3 Y' ⊔ CFSG.Open.pCoreOf 2 Y' := by
    rw [hres]
    exact le_antisymm (sup_le le_sup_left (hQO.trans le_sup_right))
      (sup_le le_sup_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y'))
  have hY'Y : Y' ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le (hLY.trans Subgroup.le_normalizer)
      (inf_le_left.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 (R ⊔ L)).trans
        (sup_le hRY (hLY.trans Subgroup.le_normalizer))))
  have hΓ : Y ∈ gam155 A (lB A) Y' (oPrimeResidualOf 3 Y') :=
    ⟨hY, by rw [hres]; exact hLY, hY'Y⟩
  have hΩ : omg155 A (oPrimeResidualOf 3 Y') := by
    rw [hres]
    exact Or.inr ⟨c, L, h.zpowers_mem_omegaA, h.mem_lA, by
      rw [inf_idem, sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)]⟩
  have hloc : IsPLocal 2 (Subgroup.normalizer (P : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hP2 hPne
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hAY' : A ⊔ Y' ≤ Subgroup.normalizer (P : Set G) :=
    sup_le hAP (sup_le hLP (inf_le_left.trans Subgroup.le_normalizer))
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y' : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hle (hAY' hx)⟩
  exact (delta_mono hle).trans ((h155 Y' hY'3 hX4 hY'eq).2 Y hΓ (Or.inl hΩ) M hMm)

omit [Finite G] in
theorem isQuasisimple_of_le_sup {L X N : Subgroup G} (hLX : L ≤ X) (hX : X ≤ L ⊔ N)
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) (hNO : N ≤ CFSG.Open.pCoreOf 2 X)
    (hO : CFSG.Open.pCoreOf 2 L = ⊥) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 2 ↥X with hOdef
  set f : ↥L →* ↥X ⧸ O := (QuotientGroup.mk' O).comp (Subgroup.inclusion hLX) with hf
  have hOL : CFSG.pCore 2 ↥L = ⊥ := by
    exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp hO
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O q
    have hy : (y : G) ∈ ((L ⊔ N : Subgroup G) : Set G) := hX y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L N hLN] at hy
    obtain ⟨l, hl, n, hn, hln⟩ := hy
    obtain ⟨n', hn', hnn'⟩ := Subgroup.mem_map.mp (hNO hn)
    have hn'O : n' ∈ O := by rwa [hOdef]
    have hy' : y = Subgroup.inclusion hLX ⟨l, hl⟩ * n' := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, ← hln]
      exact congrArg (l * ·) hnn'.symm
    have h1 : QuotientGroup.mk' O n' = 1 := (QuotientGroup.eq_one_iff n').mpr hn'O
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hy', hf, MonoidHom.comp_apply, map_mul, h1, mul_one]
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hOL]
    have hp : IsPGroup 2 f.ker := by
      intro x
      have hx : Subgroup.inclusion hLX (x : ↥L) ∈ O := by
        have hx1 : QuotientGroup.mk' O (Subgroup.inclusion hLX (x : ↥L)) = 1 :=
          MonoidHom.mem_ker.mp x.2
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥X) ⟨_, hx⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg (fun z : ↥O => ((z : ↥X) : G)) hn
      simpa using this
    exact le_sSup (show f.ker ∈ {N : Subgroup ↥L | N.Normal ∧ IsPGroup 2 N} from
      ⟨inferInstance, hp⟩)
  have e : ↥L ≃* ↥X ⧸ O := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have e' : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hOL).trans QuotientGroup.quotientBot
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e'.trans e) hq

theorem exists_deltaY_of_mem_scriptQ {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (hL4 : L ∈ scriptY4 A (lB A)) (hO : CFSG.Open.pCoreOf 2 L = ⊥)
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hLY : L ≤ Y) {R : Subgroup G}
    (hR : GoodR163 A L R) (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hPQ : CFSG.Open.pCoreOf 2 (R ⊔ L) ∈ scriptQ A (lB A)) :
    ∃ Y' ∈ scriptY3 A (lB A), oPrimeResidualOf 3 Y' ∈ scriptY4 A (lB A) ∧
      Y' = oPrimeResidualOf 3 Y' ⊔ CFSG.Open.pCoreOf 2 Y' ∧
      Y ∈ gam155 A (lB A) Y' (oPrimeResidualOf 3 Y') ∧
      (omg155 A (oPrimeResidualOf 3 Y') ∨
        Y = oPrimeResidualOf 3 Y' ⊔ CFSG.Open.pCoreOf 2 Y) ∧
      ∃ M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y' : Subgroup G) : Set G),
        Subgroup.normalizer (CFSG.Open.pCoreOf 2 (R ⊔ L) : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set P := CFSG.Open.pCoreOf 2 (R ⊔ L) with hPdef
  set Y' := L ⊔ P with hY'def
  set X' := oPrimeResidualOf 3 Y' with hX'def
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (R ⊔ L)
  have hPne : P ≠ ⊥ := hR.2.2
  have hLP : L ≤ Subgroup.normalizer (P : Set G) :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (R ⊔ L))
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    (le_normalizer_sup hR.1.1.1.1.2.2 hD.le_normalizer).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (R ⊔ L))
  have hPY : P ≤ Subgroup.normalizer (Y : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (R ⊔ L)).trans
      (sup_le hRY (hLY.trans Subgroup.le_normalizer))
  have hY'P : Y' ≤ Subgroup.normalizer (P : Set G) := sup_le hLP Subgroup.le_normalizer
  have hPO : P ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hY'P hP2
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) := le_normalizer_sup hD.le_normalizer hAP
  have hY'top : Y' ≠ ⊤ := fun htop =>
    normalizer_ne_top_of_isPGroup h.toTheoremFourHyp.isSimpleGroup h.toTheoremFourHyp.nonabelian
      hPne hP2 (top_le_iff.mp (htop ▸ hY'P))
  have hY'Δ : Y' = delta A (lB A) Y' :=
    le_antisymm (sup_le (hL4.2.2.1.le.trans (delta_mono le_sup_left)) (le_delta hPQ le_sup_right))
      (delta_le _)
  have hO2 : CFSG.Open.pCoreOf 2 Y' ≠ ⊥ := fun h0 => hPne (le_bot_iff.mp (h0 ▸ hPO))
  have hY'3 : Y' ∈ scriptY3 A (lB A) := ⟨⟨⟨hY'top, hAY'⟩, hO2⟩, hY'Δ⟩
  have hLX' : L ≤ X' := hL4.2.1.le.trans (oPrimeResidualOf_mono 3 le_sup_left)
  have hX'Y' : X' ≤ Y' := oPrimeResidualOf_le_self 3 Y'
  have hX'Y : X' ≤ Y := by
    rw [hX'def, oPrimeResidualOf_eq_closure, Subgroup.closure_le]
    rintro x ⟨hx, k, hk⟩
    have hPN : P ≤ Subgroup.normalizer ((Y ⊓ Y' : Subgroup G) : Set G) :=
      (le_inf hPY (le_sup_right.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hx' : x ∈ (Y ⊓ Y') ⊔ P :=
      (sup_le ((le_inf hLY le_sup_left).trans le_sup_left) le_sup_right : Y' ≤ (Y ⊓ Y') ⊔ P) hx
    exact (Subgroup.mem_inf.mp (mem_of_pow_three_of_mem_sup hPN hP2 hx' hk)).1
  have hX'eq : X' ≤ L ⊔ (X' ⊓ P) := by
    intro x hx
    have hx' : x ∈ ((L ⊔ P : Subgroup G) : Set G) := hX'Y' hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L P hLP] at hx'
    obtain ⟨l, hl, p, hp, rfl⟩ := hx'
    have hpX : p ∈ X' := by
      have := mul_mem (inv_mem (hLX' hl)) hx
      rwa [inv_mul_cancel_left] at this
    exact mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right ⟨hpX, hp⟩)
  have hAX' : A ≤ Subgroup.normalizer (X' : Set G) := le_normalizer_oPrimeResidualOf hAY'
  have hX'PQ : X' ⊓ P ∈ scriptQ A (lB A) := mem_scriptQ_of_le hPQ inf_le_right
    ((le_inf hAX' hAP).trans Subgroup.inf_normalizer_le_normalizer_inf)
  have hX'Δ : X' = delta A (lB A) X' :=
    le_antisymm (hX'eq.trans (sup_le (hL4.2.2.1.le.trans (delta_mono hLX'))
      (le_delta hX'PQ inf_le_left))) (delta_le _)
  have hX'X' : X' = oPrimeResidualOf 3 X' :=
    (oPrimeResidualOf_eq_of_le hX'Y' fun x hx k hk => by
      rw [hX'def, oPrimeResidualOf_eq_closure]
      exact Subgroup.subset_closure ⟨hx, k, hk⟩).symm
  have hLXP : L ≤ Subgroup.normalizer ((X' ⊓ P : Subgroup G) : Set G) :=
    (le_inf (hLX'.trans Subgroup.le_normalizer) hLP).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hXPO : X' ⊓ P ≤ CFSG.Open.pCoreOf 2 X' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      ((le_inf Subgroup.le_normalizer (hX'Y'.trans hY'P)).trans
        Subgroup.inf_normalizer_le_normalizer_inf) (hP2.to_le inf_le_right)
  have hX'4 : X' ∈ scriptY4 A (lB A) :=
    ⟨⟨fun htop => hY'top (top_le_iff.mp (htop ▸ hX'Y')), hAX'⟩, hX'X', hX'Δ,
      isQuasisimple_of_le_sup hLX' hX'eq hLXP hXPO hO hL4.2.2.2⟩
  have hY'eq : Y' = X' ⊔ CFSG.Open.pCoreOf 2 Y' :=
    le_antisymm (sup_le (hLX'.trans le_sup_left) (hPO.trans le_sup_right))
      (sup_le hX'Y' (CFSG.LieType.BorelTits.pCoreOf_le 2 Y'))
  have hΓ : Y ∈ gam155 A (lB A) Y' X' :=
    ⟨hY, hX'Y, sup_le (hLY.trans Subgroup.le_normalizer) hPY⟩
  have hΩ : omg155 A X' := Or.inr ⟨c, L, h.zpowers_mem_omegaA, h.mem_lA, by
    rw [inf_eq_left.mpr hLX', hO, sup_bot_eq]⟩
  have hloc : IsPLocal 2 (Subgroup.normalizer (P : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hP2 hPne
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hAY'P : A ⊔ Y' ≤ Subgroup.normalizer (P : Set G) := sup_le hAP hY'P
  exact ⟨Y', hY'3, hX'4, hY'eq, hΓ, Or.inl hΩ, M, ⟨hM, fun x hx => hle (hAY'P hx)⟩, hle⟩

end Y4

section QL

theorem step163QLNE_of
    (h142 : Concl142R) (h1514 : Item1514R) (hMeets : Step163Meets) (hK : KS163QLInv) :
    Step163QLNE := by
  intro G _ _ A c L h hL _ h32 hne
  obtain ⟨Y, hY⟩ := hne
  by_cases hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  · exact exists_scriptQPi_two_of_j2 h hJ
  refine exists_scriptQPi_two_of_hasInvEven h (h142 G A c L h) ?_
  by_cases hθ : Odd (Nat.card (aschbacherSolvableCore 3 ↥L))
  · exact hK G A c L h h32 (not_nonempty_iff.mp hJ)
      (isEmpty_m12_of_le h (h1514 G A c L h) hMeets hY (hL Y hY)) hθ
  · exact hasInvEven_of_not_odd h hθ

end QL

section V

theorem step163VNE_of (hQL : Step163QLNE) (hVR : Step163VR) : Step163VNE := by
  intro G _ _ A c L h hL hO h32 hne
  obtain ⟨Q, hQ, hQ1⟩ := hQL G A c L h hL hO h32 hne
  obtain ⟨Y, hY⟩ := hne
  obtain ⟨S, hS, hSL, hQS⟩ := exists_scriptQPiStar_inf h.le_normalizer (hL Y hY) hQ
  exact hVR G A c L h hL hO h32 Y hY S hS hSL (ne_bot_of_le_ne_bot hQ1 hQS)

end V

section Delta

theorem step163Delta_of
    (h155 : Item155R) (h142 : Concl142R) (h1514 : Item1514R)
    (hMeets : Step163Meets) (hA7 : Step163L4A7) (hY : Step163DeltaY) : Step163Delta := by
  intro G _ _ A c L h hL Y hYs R hR hRY
  by_cases hne : CFSG.Open.pCoreOf 2 L ≠ ⊥ ∨
      CFSG.Open.pCoreOf 2 (R ⊔ L) ⊓ Subgroup.centralizer ({c} : Set G) ≠ ⊥
  · exact delta_normalizer_le_of_centralizer h (h155 G A c L h)
      (fun Q hQ => mem_scriptQ_of_concl142 (h142 G A c L h) h.zpowers_mem_omegaA hQ)
      (mem_scriptY4_of_le h (h142 G A c L h) (h1514 G A c L h) hMeets hA7 hYs (hL Y hYs)) hYs
      (hL Y hYs) hR hRY hne
  · push Not at hne
    obtain ⟨Y', hY'3, hX'4, hY'eq, hΓ, hΩ, M, hM, hPM⟩ :=
      hY G A c L h hL hne.1 Y hYs R hR hRY hne.2
    exact (delta_mono hPM).trans ((h155 G A c L h Y' hY'3 hX'4 hY'eq).2 Y hΓ hΩ M hM)

theorem step163DeltaY_of_Q
    (h142 : Concl142R) (h1514 : Item1514R)
    (hMeets : Step163Meets) (hA7 : Step163L4A7) (hQ : Step163DeltaQ) : Step163DeltaY :=
  fun G _ _ A c L h hL hO Y hY R hR hRY hfpf => exists_deltaY_of_mem_scriptQ h
    (mem_scriptY4_of_le h (h142 G A c L h) (h1514 G A c L h) hMeets hA7 hY (hL Y hY)) hO hY
    (hL Y hY) hR hRY (hQ G A c L h hL hO Y hY R hR hRY hfpf)

end Delta

section Q2

theorem step163XTransTwoPow_of (hloc : Claim1411LocalR) (h1514 : Item1514R)
    (hMeets : Step163Meets) (hX : Step163XTransH) : Step163XTransTwoPow := by
  intro G _ _ A c L h hL hO h32 hne
  obtain ⟨Y, hY⟩ := hne
  obtain ⟨-, hΩ, -⟩ := cover_of_isL3TwoPow h (h1514 G A c L h) hMeets h32 hY (hL Y hY)
  exact rank3II_14_11_2_of h.toSec14Std (hloc G A c L h)
    (hX G A c L h hL hO h32 ⟨Y, hY⟩ hΩ)

theorem step163Q2TwoPow_of (hTwo : Step163TwoPowNE) (hΔ : Step163Delta) (h153 : Item153MainR)
    (hobs : Claim153ObsR) (h1411 : Item1411_1R) (hX : Step163XTransTwoPow) :
    Step163Q2TwoPow := by
  intro G _ _ A c L h hL hO h32 Y₁ hY₁ Y₂ hY₂ _
  obtain ⟨R, hR⟩ := hTwo G A c L h hL hO h32 ⟨Y₁, hY₁⟩
  have hXY := xA_le_normalizer_of_goodR163 h (h153 G A c L h) (hobs G A c L h)
    (h1411 G A c L h) hR (fun Y hY hRY => hΔ G A c L h hL Y hY R hR hRY)
  obtain ⟨S₁, hS₁, hS₁Y⟩ := exists_qStar_le_normalizer (h153 G A c L h) (hobs G A c L h) hY₁
  obtain ⟨S₂, hS₂, hS₂Y⟩ := exists_qStar_le_normalizer (h153 G A c L h) (hobs G A c L h) hY₂
  obtain ⟨x, hx, hS₁x⟩ := hX G A c L h hL hO h32 ⟨Y₁, hY₁⟩ S₂ hS₂ S₁ hS₁
  have hxY : x ∈ Subgroup.normalizer (Y₂ : Set G) := hXY Y₂ hY₂ (Subgroup.mem_inf.mp hx).1
  have hS₁Y₂ : S₁ ≤ Subgroup.normalizer (Y₂ : Set G) := by
    have hmap := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hS₂Y
    rwa [Subgroup.map_equiv_normalizer_eq, Late.map_conj_eq_of_mem_normalizer hxY, ← hS₁x]
      at hmap
  have hR1 : R ≠ ⊥ := by
    rintro rfl
    exact hR.2.2 (by rw [bot_sup_eq]; exact hO)
  have hS1 : S₁ ≠ ⊥ := by
    intro h0
    rw [h0] at hS₁
    exact hR1 (le_bot_iff.mp (hS₁.2 hR.1 bot_le))
  exact ⟨S₁, ⟨⟨hS₁.prop.1.1, le_inf hS₁Y hS₁Y₂⟩, hS₁.prop.2⟩, hS1⟩

end Q2

section Main

variable {G : Type} [Group G] [Finite G]

theorem rank3II_16_3_of_NE {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h1514 : ∀ (c' : G) (L' : Subgroup G), Sec15R G A c' L' → Item1514 A (lB A) c' L')
    (h162 : Item162 A (lB A)) (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A))
    (h1411 : Item1411_1 A (lB A)) (h142 : Concl142 A (lB A)) (hU35 : Step163U35)
    (hPt : Step163Pt) (hYa : Step163Ya) (hMeets : Step163Meets) (hA7 : Step163A7)
    (hA10 : Step163A10) (hQL : Step163QLNE) (hQ2 : Step163Q2TwoPow) (hΔ : Step163Delta)
    (hTwo : Step163TwoPowNE) (hV : Step163VNE) : Item163 A (lB A) c L := by
  have h45 := rank3II_16_3_four_five_of h h1514 h162 hU35 hPt hYa hMeets hA7 hA10
  have hL : ∀ Y ∈ scriptY0Star A (lB A), L ≤ Y := fun Y hY => (h45 Y hY).1
  have hΔ' := hΔ G A c L h hL
  suffices hcore : (scriptY0Star A (lB A)).Nonempty → Item163 A (lB A) c L from
    fun Y hY => hcore ⟨Y, hY⟩ Y hY
  intro hne
  by_cases hO : CFSG.Open.pCoreOf 2 L = ⊥
  · by_cases h32 : IsL3TwoPow L
    · obtain ⟨R, hR⟩ := hTwo G A c L h hL hO h32 hne
      exact item163_of_core h h162 h153 hobs h1411 h45 (hQ2 G A c L h hL hO h32) hR
        (fun Y hY hRY => hΔ' Y hY R hR hRY)
    · obtain ⟨R, hR⟩ := hV G A c L h hL hO h32 hne
      exact item163_of_core h h162 h153 hobs h1411 h45
        (fun Y₁ hY₁ Y₂ hY₂ _ => qTwoNe_of_scriptQPi (hQL G A c L h hL hO h32 hne)
          (hL Y₁ hY₁) (hL Y₂ hY₂))
        hR (fun Y hY hRY => hΔ' Y hY R hR hRY)
  · have hQ := pCoreOf_mem_scriptQPi h fun Q hQ =>
      mem_scriptQ_of_concl142 h142 h.zpowers_mem_omegaA hQ
    exact item163_of_core h h162 h153 hobs h1411 h45
      (fun Y₁ hY₁ Y₂ hY₂ _ => qTwoNe_of_scriptQPi ⟨_, hQ, hO⟩ (hL Y₁ hY₁) (hL Y₂ hY₂))
      (goodR163_bot hO) (fun Y hY hRY => hΔ' Y hY ⊥ (goodR163_bot hO) hRY)

end Main

theorem item163R_of_NE (h1514 : Item1514R) (h162 : Item162R) (h153 : Item153MainR)
    (hobs : Claim153ObsR) (h1411 : Item1411_1R) (h142 : Concl142R) (hU35 : Step163U35)
    (hPt : Step163Pt) (hYa : Step163Ya) (hMeets : Step163Meets) (hA7 : Step163A7)
    (hA10 : Step163A10) (hQL : Step163QLNE) (hQ2 : Step163Q2TwoPow) (hΔ : Step163Delta)
    (hTwo : Step163TwoPowNE) (hV : Step163VNE) : Item163R :=
  fun G _ _ A c L hR => rank3II_16_3_of_NE hR (fun c' L' hR' => h1514 G A c' L' hR')
    (h162 G A c L hR) (h153 G A c L hR) (hobs G A c L hR) (h1411 G A c L hR) (h142 G A c L hR)
    hU35 hPt hYa hMeets hA7 hA10 hQL hQ2 hΔ hTwo hV

end CFSG.RankThree.PartTwo.Sec16
