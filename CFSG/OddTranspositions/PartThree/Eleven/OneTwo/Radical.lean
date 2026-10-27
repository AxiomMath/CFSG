module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.Hyp
public import CFSG.GH74.Generic.BProg.B2.L2Cover
public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
public import CFSG.GroupTheory.CentralExtensionPerfectPreimage
public import CFSG.OddTranspositions.PartThree.Eleven.GroupLemmas
public import TauCeti.GroupTheory.DerivedCentralQuotient

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open scoped commutatorElement

section Radical

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenTwoHyp

variable {hC : HypothesisC D}

private theorem commutator_facts (h : ElevenTwoHyp hC) :
    CFSG.IsQuasisimple (commutator (Halpha D hC.alpha)) ∧
      Subgroup.center (commutator (Halpha D hC.alpha)) =
        (CFSG.solvableRadical (Halpha D hC.alpha)).subgroupOf (commutator (Halpha D hC.alpha)) ∧
      Nonempty (commutator (Halpha D hC.alpha) ⧸
        Subgroup.center (commutator (Halpha D hC.alpha)) ≃* PSL225) := by
  classical
  let H := Halpha D hC.alpha
  let K : Subgroup H := CFSG.solvableRadical H
  let π : H →* (H ⧸ K) := QuotientGroup.mk' K
  let J : Subgroup H := commutator H
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hπker : π.ker = K := QuotientGroup.ker_mk' K
  have hKcenter : K = Subgroup.center H := h.center
  have hKleJ : K ≤ J := by
    simpa only [K, J, H] using radical_le_commutator h
  have hmap : (commutator H).map π = commutator (H ⧸ K) := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπsurj]
    rfl
  let ψ : ↥J →* ↥(commutator (H ⧸ K)) :=
    { toFun := fun x =>
        ⟨π (x : H), by
          rw [← hmap]
          exact Subgroup.mem_map_of_mem π x.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        simp }
  have hψsurj : Function.Surjective ψ := by
    intro y
    have hy : (y : H ⧸ K) ∈ (commutator H).map π := by
      rw [hmap]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hψker : ψ.ker = K.subgroupOf J := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      have hx1 : ψ x = 1 := MonoidHom.mem_ker.mp hx
      have h1 : (x : H) ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val hx1
      rwa [hπker] at h1
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      have hx1 : ψ x = 1 := by
        apply Subtype.ext
        show π (x : H) = 1
        exact (QuotientGroup.eq_one_iff (x := (x : H))).mpr hx
      exact MonoidHom.mem_ker.mpr hx1
  let e₁ : ↥J ⧸ ψ.ker ≃* ↥(commutator (H ⧸ K)) :=
    QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj
  let e₂ : ↥J ⧸ K.subgroupOf J ≃* ↥(commutator (H ⧸ K)) :=
    (QuotientGroup.quotientMulEquivOfEq hψker).symm.trans e₁
  let e₃ : ↥J ⧸ K.subgroupOf J ≃* PSL225 :=
    e₂.trans h.facts.derived.some
  haveI : Fintype K25 := Fintype.ofFinite K25
  have hcardK25 : Fintype.card K25 = 25 := by
    rw [Fintype.card_eq_nat_card]
    exact CFSG.OddTranspositions.QZ.card_K25
  have hPSLcomm : commutator PSL225 = ⊤ :=
    (CFSG.LieType.Steinberg.CentralExt.SL2Closed.psl_two_hopfMultiplier
      (k := K25) (by rw [hcardK25]; norm_num) (by rw [hcardK25]; norm_num)).1
  haveI hPSLperf : Group.IsPerfect PSL225 := Group.isPerfect_def.mpr hPSLcomm
  haveI hPSLsimple : IsSimpleGroup PSL225 := CFSG.OddTranspositions.QZ.PSL225_isSimple
  have hPSLnab : ∃ a b : PSL225, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative PSL225 (IsMulCommutative.of_comm h)
  have hPSLcenter : Subgroup.center PSL225 = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
      (Group.IsPerfect.not_isMulCommutative PSL225)
  have hKleCenter : K ≤ Subgroup.center H := by rw [hKcenter]
  have hMleCenter : K.subgroupOf J ≤ Subgroup.center ↥J := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    show (w : H) * (z : H) = (z : H) * (w : H)
    have hzK : (z : H) ∈ K := by rwa [Subgroup.mem_subgroupOf] at hz
    exact Subgroup.mem_center_iff.mp (hKleCenter hzK) (w : H)
  have hcenterLe : Subgroup.center ↥J ≤ K.subgroupOf J := by
    intro z hz
    have hzψ : ψ z ∈ Subgroup.center ↥(commutator (H ⧸ K)) :=
      Subgroup.map_center_le_center hψsurj (Subgroup.mem_map_of_mem ψ hz)
    have hzPSL : h.facts.derived.some (ψ z) ∈ Subgroup.center PSL225 :=
      Subgroup.map_center_le_center h.facts.derived.some.surjective
        (Subgroup.mem_map_of_mem h.facts.derived.some.toMonoidHom hzψ)
    have hz1 : h.facts.derived.some (ψ z) = 1 := by
      have hbot : h.facts.derived.some (ψ z) ∈ (⊥ : Subgroup PSL225) := by
        rwa [hPSLcenter] at hzPSL
      exact Subgroup.mem_bot.mp hbot
    have hψz : ψ z = 1 := h.facts.derived.some.injective (by simpa using hz1)
    have hzker : z ∈ ψ.ker := MonoidHom.mem_ker.mpr hψz
    rwa [hψker] at hzker
  have hcenter : Subgroup.center ↥J = K.subgroupOf J := le_antisymm hcenterLe hMleCenter
  have hLperf : Group.IsPerfect ↥(commutator (H ⧸ K)) :=
    Group.IsPerfect.ofSurjective (f := h.facts.derived.some.symm.toMonoidHom)
      h.facts.derived.some.symm.surjective
  have hL : ⁅commutator (H ⧸ K), commutator (H ⧸ K)⁆ = commutator (H ⧸ K) :=
    Subgroup.isPerfect_iff.mp hLperf
  have hcyc : IsCyclic ((H ⧸ K) ⧸ commutator (H ⧸ K)) := by
    have hcard : Nat.card ((H ⧸ K) ⧸ commutator (H ⧸ K)) = 2 := by
      rw [← Subgroup.index_eq_card]
      exact h.facts.index_two
    exact isCyclic_of_prime_card (p := 2) hcard
  have hcomap : (commutator (H ⧸ K)).comap π = commutator H := by
    rw [← hmap]
    exact Subgroup.comap_map_eq_self (by rw [hπker]; exact hKleJ)
  have hJperf : Group.IsPerfect ↥(commutator H) := by
    have hc : π.ker ≤ Subgroup.center H := by rw [hπker, hKcenter]
    have hk : π.ker ≤ commutator H := by rw [hπker]; exact hKleJ
    have hp := CFSG.GroupTheory.isPerfect_comap_of_isCyclic_quotient π hπsurj hc hk hL
    rwa [hcomap] at hp
  have hE : (↥J ⧸ Subgroup.center ↥J) ≃* PSL225 :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans e₃
  have hsimple : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hE.isSimpleGroup
  have hQnab : ∃ a b : ↥J ⧸ Subgroup.center ↥J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hPSLnab
    refine ⟨hE.symm a, hE.symm b, ?_⟩
    intro h
    exact hab (by simpa using congrArg hE h)
  have hq : CFSG.IsQuasisimple ↥J :=
    ⟨hJperf, hsimple, hQnab⟩
  exact ⟨hq, hcenter, ⟨hE⟩⟩

theorem card_radical_dvd_two (h : ElevenTwoHyp hC) :
    Nat.card (CFSG.solvableRadical (Halpha D hC.alpha)) ∣ 2 := by
  classical
  obtain ⟨hq, hcenter, ⟨e⟩⟩ := commutator_facts h
  haveI : Fintype K25 := Fintype.ofFinite K25
  have hcardK25 : Fintype.card K25 = 25 := by
    rw [Fintype.card_eq_nat_card]
    exact CFSG.OddTranspositions.QZ.card_K25
  have hcardHop : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier PSL225) = 2 := by
    obtain ⟨-, ⟨eH⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.SL2Closed.psl_two_hopfMultiplier
        (k := K25) (by rw [hcardK25]; norm_num) (by rw [hcardK25]; norm_num)
    have h1 := Nat.card_congr
      ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess PSL225).symm.trans eH).toEquiv
    rw [h1, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, hcardK25]
    norm_num
  have hdvd : Nat.card (Subgroup.center (commutator (Halpha D hC.alpha))) ∣ 2 := by
    have h := CFSG.GH74.Generic.BProg.B2.L2Cover.card_center_dvd_card_hopfMultiplier_qs
      hq e
    rwa [hcardHop] at h
  have hcardM : Nat.card (CFSG.solvableRadical (Halpha D hC.alpha)) =
      Nat.card (Subgroup.center (commutator (Halpha D hC.alpha))) := by
    rw [hcenter]
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (radical_le_commutator h)).toEquiv).symm
  rwa [hcardM]

theorem radical_eq_bot (h : ElevenTwoHyp hC) :
    CFSG.solvableRadical (Halpha D hC.alpha) = ⊥ := by
  classical
  let H0 : Subgroup G := Halpha D hC.alpha
  let M : Subgroup H0 := CFSG.solvableRadical H0
  let J : Subgroup H0 := commutator H0
  let π : H0 →* H0 ⧸ M := QuotientGroup.mk' M
  rcases (Nat.dvd_prime Nat.prime_two).mp (card_radical_dvd_two h) with hcard1 | hcard2
  · exact Subgroup.eq_bot_of_card_eq _ hcard1
  · exfalso
    obtain ⟨hq, hcen, ⟨e⟩⟩ := commutator_facts h
    have hMJ : M ≤ J := h.radical_le_commutator
    have hcard_center : Nat.card (Subgroup.center J) = 2 := by
      rw [hcen]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMJ).toEquiv]
      exact hcard2
    have h2pg : IsPGroup 2 ↥(Subgroup.center J) :=
      IsPGroup.of_card (n := 1) (by rw [hcard_center, pow_one])
    have hodd25 : Odd (Nat.card K25) := by rw [card_K25]; norm_num
    have h5_25 : 5 ≤ Nat.card K25 := by rw [card_K25]; norm_num
    have e' : J ⧸ Subgroup.center J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K25 := e
    rcases CFSG.GH74.Generic.BProg.B2.L2Cover.l2_cover_two_group hq h2pg
        (F := K25) hodd25 h5_25 e' with hbot | ⟨-, ⟨φ⟩⟩
    · have h2eq1 : Nat.card (⊥ : Subgroup J) = 2 := by rw [← hbot]; exact hcard_center
      rw [Subgroup.card_bot] at h2eq1
      exact absurd h2eq1 (by norm_num)
    ·
      let T : Sylow 2 (H0 ⧸ M) := default
      obtain ⟨r, hr⟩ := h.facts.frame T
      have hr0Θ : r 0 ∈ imageClass hC := by
        have hmem : r 0 ∈ Set.range r := Set.mem_range_self 0
        rw [← hr.inter_eq] at hmem
        exact hmem.2
      have hr1Θ : r 1 ∈ imageClass hC := by
        have hmem : r 1 ∈ Set.range r := Set.mem_range_self 1
        rw [← hr.inter_eq] at hmem
        exact hmem.2
      rw [imageClass] at hr0Θ hr1Θ
      obtain ⟨a, ha, haeq⟩ := hr0Θ
      obtain ⟨b, hb, hbeq⟩ := hr1Θ
      have haeq' : π a = r 0 := haeq
      have hbeq' : π b = r 1 := hbeq
      have hr01 : r 0 ≠ r 1 := fun h01 => absurd (hr.injective h01) (by decide)
      have haord : orderOf a = 2 := (DstarH_isOddTransp hC).1 a ha
      have hbord : orderOf b = 2 := (DstarH_isOddTransp hC).1 b hb
      have ha2 : a * a = 1 := by
        have h := pow_orderOf_eq_one a
        rw [haord, pow_two] at h
        exact h
      have hb2 : b * b = 1 := by
        have h := pow_orderOf_eq_one b
        rw [hbord, pow_two] at h
        exact h
      have hr0sq : r 0 * r 0 = 1 := by rw [← haeq', ← map_mul, ha2, map_one]
      have hr1sq : r 1 * r 1 = 1 := by rw [← hbeq', ← map_mul, hb2, map_one]
      have hπab : π (a * b) = r 0 * r 1 := by rw [map_mul, haeq', hbeq']
      have hab2 : (a * b) * (a * b) = 1 := by
        rcases (DstarH_isOddTransp hC).2 a ha b hb with hdvd | hodd
        · have h2 : (a * b) ^ 2 = 1 :=
            (orderOf_dvd_iff_pow_eq_one (x := a * b) (n := 2)).mp hdvd
          simpa [pow_two] using h2
        · exfalso
          have hπodd : Odd (orderOf (π (a * b))) :=
            hodd.of_dvd_nat (orderOf_map_dvd π (a * b))
          rw [hπab] at hπodd
          have hcsq : (r 0 * r 1) * (r 0 * r 1) = 1 := by
            have hcomm : Commute (r 0) (r 1) := hr.commute 0 1
            calc (r 0 * r 1) * (r 0 * r 1)
                = r 0 * (r 1 * r 0) * r 1 := by group
              _ = r 0 * (r 0 * r 1) * r 1 := by rw [← hcomm.eq]
              _ = (r 0 * r 0) * (r 1 * r 1) := by group
              _ = 1 := by rw [hr0sq, hr1sq, mul_one]
          have hr01one : r 0 * r 1 = 1 := by
            have hdvd2 : orderOf (r 0 * r 1) ∣ 2 :=
              (orderOf_dvd_iff_pow_eq_one (x := r 0 * r 1) (n := 2)).mpr
                (by simpa [pow_two] using hcsq)
            rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
            · exact orderOf_eq_one_iff.mp h1
            · rw [h2] at hπodd
              exact absurd hπodd (by decide)
          exact hr01 (by
            rw [eq_inv_of_mul_eq_one_left hr01one, inv_eq_of_mul_eq_one_left hr1sq])
      obtain ⟨g, hg⟩ := DstarH_transitive hC ha hb
      have hab_comm : a * b = ⁅g⁻¹, b⁆ := by
        have ha_eq : a = g⁻¹ * b * g := by rw [← hg]; group
        rw [ha_eq, commutatorElement_def, inv_eq_of_mul_eq_one_left hb2]
        group
      have habJ : a * b ∈ J := by
        rw [hab_comm]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g⁻¹) (Subgroup.mem_top b)
      let x : J := ⟨a * b, habJ⟩
      have hx2 : x * x = 1 := Subtype.ext (by
        change (a * b) * (a * b) = (1 : H0)
        exact hab2)
      have hφxsq : φ x * φ x = 1 := by rw [← map_mul, hx2, map_one]
      have hφxcen : φ x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K25) := by
        rw [CFSG.ClassicalInvolution.mem_center_sl2_iff]
        by_cases h1 : φ x = 1
        · exact Or.inl h1
        · refine Or.inr ?_
          have hdvd : orderOf (φ x) ∣ 2 :=
            (orderOf_dvd_iff_pow_eq_one (x := φ x) (n := 2)).mpr
              (by simpa [pow_two] using hφxsq)
          have hord2 : orderOf (φ x) = 2 := by
            rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
            · exact absurd (orderOf_eq_one_iff.mp h) h1
            · exact h
          exact (CFSG.ClassicalInvolution.sl2_orderOf_eq_two_iff hodd25 (φ x)).mp hord2
      have hxcen : x ∈ Subgroup.center J := by
        have hmem : φ x ∈ Subgroup.map (φ : J →* Matrix.SpecialLinearGroup (Fin 2) K25)
            (Subgroup.center J) := by
          rw [Subgroup.map_center_eq φ]
          exact hφxcen
        obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_map).mp hmem
        have : y = x := φ.injective hyx
        rwa [this] at hy
      have hxM : (a * b : H0) ∈ M := by
        have hxsub : x ∈ M.subgroupOf J := by rw [← hcen]; exact hxcen
        exact (Subgroup.mem_subgroupOf).mp hxsub
      have hπ1 : π (a * b) = 1 := (QuotientGroup.eq_one_iff (a * b)).mpr hxM
      have hr01one : r 0 * r 1 = 1 := by rw [← hπab]; exact hπ1
      exact hr01 (by
        rw [eq_inv_of_mul_eq_one_left hr01one, inv_eq_of_mul_eq_one_left hr1sq])

theorem factsH (h : ElevenTwoHyp hC) : O4MinusFacts (Halpha D hC.alpha) (DstarH hC) := by
  have hM : CFSG.solvableRadical (Halpha D hC.alpha) = ⊥ := radical_eq_bot h
  let e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      Halpha D hC.alpha :=
    (QuotientGroup.quotientMulEquivOfEq hM).trans QuotientGroup.quotientBot
  have hval : ∀ x : Halpha D hC.alpha,
      e (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x) = x := by
    intro x
    change ((QuotientGroup.quotientMulEquivOfEq hM).trans QuotientGroup.quotientBot)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x) = x
    rw [QuotientGroup.mk'_apply, MulEquiv.trans_apply,
      QuotientGroup.quotientMulEquivOfEq_mk]
    rw [← QuotientGroup.quotientBot_symm_apply x]
    exact QuotientGroup.quotientBot.apply_symm_apply x
  have he : e '' imageClass hC = DstarH hC := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp only [imageClass, Set.mem_image] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      rw [hval x]
      exact hx
    · intro hy
      refine ⟨QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) y, ?_, ?_⟩
      · simp only [imageClass, Set.mem_image]
        exact ⟨y, hy, rfl⟩
      · exact hval y
  exact O4MinusFacts.of_mulEquiv e he h.facts

end ElevenTwoHyp

end Radical

end CFSG.OddTranspositions.PartThree
