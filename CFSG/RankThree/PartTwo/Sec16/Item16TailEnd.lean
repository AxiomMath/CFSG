module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec3.TwoGroupPrimeFiveAction
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof169

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec16
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (H : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hy z hz
    have hz' : g⁻¹ * z * g ∈ H := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) z).mp hz
      simpa using this
    have hc := hy _ hz'
    calc z * (g * y * g⁻¹) = g * ((g⁻¹ * z * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by rw [hc]
      _ = g * y * g⁻¹ * z := by group
  · intro hy z hz
    have hz' : g * z * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hg z).mp hz
    have hc := hy _ hz'
    have h2 : g * (z * y) * g⁻¹ = g * (y * z) * g⁻¹ := by
      calc g * (z * y) * g⁻¹ = (g * z * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * z * g⁻¹) := hc
        _ = g * (y * z) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

omit [Finite G] in
theorem subgroupOf_le_normalizer_subgroupOf {H K N : Subgroup G}
    (h : H ≤ Subgroup.normalizer (K : Set G)) :
    H.subgroupOf N ≤ Subgroup.normalizer ((K.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hxH : (x : G) ∈ H := Subgroup.mem_subgroupOf.mp hx
  simpa [Subgroup.mem_subgroupOf] using Subgroup.mem_normalizer_iff.mp (h hxH) y

theorem false_of_commutator_action
    (hloc : ∀ r : ℕ, r.Prime → 3 < r → CFSG.Assembly.RankThreeEven.localRank r G < 3)
    {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp5 : p ≠ 5) (hq : q.Prime) (hq3 : 3 < q)
    {X U Q : Subgroup G} (hXp : Nat.card X = p) (hU2 : IsPGroup 2 U) (hUX : ⁅U, X⁆ = U)
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hQ : IsPGroup q Q)
    (hUQ : U ≤ Subgroup.normalizer (Q : Set G)) (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hUC : ¬ U ≤ Subgroup.centralizer (Q : Set G)) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  set K := U ⊓ Subgroup.centralizer (Q : Set G) with hK
  set N := Subgroup.normalizer (K : Set G) with hN
  have hKU : K ≤ U := inf_le_left
  have hK2 : IsPGroup 2 K := hU2.to_le hKU
  have hCN : ∀ {Y : Subgroup G}, Y ≤ Subgroup.normalizer (U : Set G) →
      Y ≤ Subgroup.normalizer (Q : Set G) → Y ≤ N := fun h1 h2 =>
    le_normalizer_inf h1 (h2.trans (normalizer_le_normalizer_centralizer Q))
  have hUN : U ≤ N := hCN Subgroup.le_normalizer hUQ
  have hXN : X ≤ N := hCN hXU hXQ
  have hQN : Q ≤ N :=
    (Subgroup.le_centralizer_iff.mp (inf_le_right : K ≤ _)).trans
      (Subgroup.centralizer_le_normalizer _)
  set K' : Subgroup ↥N := K.subgroupOf N with hK'
  set π := QuotientGroup.mk' K' with hπ
  set U' := (U.subgroupOf N).map π with hU'
  set X' := (X.subgroupOf N).map π with hX'
  set P' := (Q.subgroupOf N).map π with hP'
  have hcop2 : ∀ {r : ℕ}, r.Prime → r ≠ 2 → Nat.Coprime r (Nat.card K) := by
    intro r hr hr2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK2
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  have hPp : IsPGroup q P' := (hQ.comap_subtype (K := N)).map π
  have hUp : IsPGroup 2 U' := (hU2.comap_subtype (K := N)).map π
  have hXK : X ⊓ K = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (by rw [hXp]; exact hcop2 hp (by omega))).eq_bot
  have hinj : Function.Injective (π.comp (X.subgroupOf N).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxK : ((x : ↥N) : G) ∈ K := by
      have : (x : ↥N) ∈ K' := (QuotientGroup.eq_one_iff _).mp hx
      exact Subgroup.mem_subgroupOf.mp this
    have hxX : ((x : ↥N) : G) ∈ X := Subgroup.mem_subgroupOf.mp x.2
    have h1 : ((x : ↥N) : G) ∈ X ⊓ K := ⟨hxX, hxK⟩
    rw [hXK, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hXcard : Nat.card X' = p := by
    have hX'eq : X' = (π.comp (X.subgroupOf N).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hX'eq, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv, hXp]
  have hcomm : ⁅U.subgroupOf N, X.subgroupOf N⁆ = U.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUN,
      Subgroup.map_subgroupOf_eq_of_le hXN]
    exact hUX
  have hUX' : ⁅U', X'⁆ = U' := by
    rw [hU', hX', ← Subgroup.map_commutator, hcomm]
  have hU'1 : U' ≠ ⊥ := by
    intro hbot
    apply hUC
    rw [hU', Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    intro u hu
    have hmem : (⟨u, hUN hu⟩ : ↥N) ∈ K' := hbot (Subgroup.mem_subgroupOf.mpr hu)
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2
  have hUP' : U' ≤ Subgroup.normalizer (P' : Set _) :=
    (Subgroup.map_mono (subgroupOf_le_normalizer_subgroupOf hUQ)).trans
      (Subgroup.le_normalizer_map π)
  have hXP' : X' ≤ Subgroup.normalizer (P' : Set _) :=
    (Subgroup.map_mono (subgroupOf_le_normalizer_subgroupOf hXQ)).trans
      (Subgroup.le_normalizer_map π)
  have hQU : Q ⊓ U = ⊥ := (Subgroup.disjoint_of_coprime_natCard (by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU2
    rw [hk, hm]
    exact Nat.Coprime.pow k m ((Nat.coprime_primes hq Nat.prime_two).mpr (by omega)))).eq_bot
  have hfaith : U' ⊓ Subgroup.centralizer (P' : Set _) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨u, hu, rfl⟩, hc⟩
    rw [Subgroup.mem_bot]
    have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have huC : (u : G) ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzN : z ∈ N := hQN hz
      have h1 := Subgroup.mem_centralizer_iff.mp hc (π ⟨z, hzN⟩)
        ⟨⟨z, hzN⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
      have h2 : (⟨z, hzN⟩ * u : ↥N)⁻¹ * (u * ⟨z, hzN⟩) ∈ K' := by
        rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
        exact h1
      have h3 : ((⟨z, hzN⟩ * u : ↥N)⁻¹ * (u * ⟨z, hzN⟩) : ↥N).1 ∈ K :=
        Subgroup.mem_subgroupOf.mp h2
      have hval : ((⟨z, hzN⟩ * u : ↥N)⁻¹ * (u * ⟨z, hzN⟩) : ↥N).1 =
          (u : G)⁻¹ * z⁻¹ * (u : G) * z := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
        group
      rw [hval] at h3
      have h4 : (u : G)⁻¹ * z⁻¹ * (u : G) * z ∈ Q := by
        have h5 : (u : G)⁻¹ * z⁻¹ * (u : G) ∈ Q := by
          have := (Subgroup.mem_normalizer_iff.mp (hUQ (inv_mem huU)) z⁻¹).mp (inv_mem hz)
          simpa using this
        exact mul_mem h5 hz
      have h6 : (u : G)⁻¹ * z⁻¹ * (u : G) * z ∈ Q ⊓ U := ⟨h4, hKU h3⟩
      rw [hQU, Subgroup.mem_bot] at h6
      have h7 : (u : G) * z = z * (u : G) := by
        calc (u : G) * z = z * (u : G) * ((u : G)⁻¹ * z⁻¹ * (u : G) * z) := by group
          _ = z * (u : G) := by rw [h6, mul_one]
      exact h7.symm
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ⟨huU, huC⟩)
  have hfix : ∀ u ∈ U', u ≠ 1 →
      CFSG.Assembly.pRank q (P' ⊓ Subgroup.centralizer ({u} : Set _)) ≤ 2 := by
    intro ū hū hū1
    have hT2 : IsPGroup 2 (Subgroup.zpowers ū) := hUp.to_le (Subgroup.zpowers_le.mpr hū)
    have hT1 : Subgroup.zpowers ū ≠ ⊥ := by
      intro hbot
      apply hū1
      have : ū ∈ Subgroup.zpowers ū := Subgroup.mem_zpowers ū
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have hloc2 : CFSG.Open.IsTwoLocal
        (Subgroup.normalizer (Subgroup.zpowers ū : Set (↥N ⧸ K'))) := ⟨_, hT1, hT2, rfl⟩
    have hle : P' ⊓ Subgroup.centralizer ({ū} : Set _) ≤
        Subgroup.normalizer (Subgroup.zpowers ū : Set (↥N ⧸ K')) :=
      inf_le_right.trans (centralizer_singleton_le_normalizer_zpowers ū)
    have h1 := CFSG.RankThreeEvenClassification.Helpers.pRank_mono q hq hle
    have h2 : CFSG.Open.pRank q (Subgroup.normalizer (Subgroup.zpowers ū : Set (↥N ⧸ K'))) ≤
        CFSG.Assembly.RankThreeEven.localRank q (↥N ⧸ K') :=
      le_csSup (CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_bddAbove q hq _)
        ⟨_, hloc2, rfl⟩
    have hK'q : ¬ q ∣ Nat.card K' := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer :
        K ≤ N)).toEquiv]
      exact (Nat.Prime.coprime_iff_not_dvd hq).mp (hcop2 hq (by omega))
    have h3 := CFSG.RankThree.Classical2.localRank_quotient_le hq (by omega) K' hK'q
    have h4 := localRank_subgroup_le hq N
    have h5 := hloc q hq hq3
    change CFSG.Open.pRank q _ ≤ 2
    omega
  exact hp5 (Sec3.rank3II_3_6 hq (by omega) hp hp3 hPp hUp hXcard hUX' hU'1 hUP' hXP' hfaith
    hfix)

theorem pCore_two_thetaCen_eq_bot {d : G}
    (hO2 : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) = ⊥) :
    CFSG.pCore 2 ↥(thetaCen ({d} : Set G)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Θ := thetaCen ({d} : Set G) with hΘ
  set T := (CFSG.pCore 2 ↥Θ).map Θ.subtype with hT
  have hTΘ : T ≤ Θ := Subgroup.map_subtype_le _
  have hΘC : Θ ≤ Subgroup.centralizer ({d} : Set G) := Subgroup.map_subtype_le _
  have hCT : Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (T : Set G) :=
    (centralizer_le_normalizer_thetaCen _).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hT2 : IsPGroup 2 T := (CFSG.pCore_isPGroup (p := 2) (G := ↥Θ)).map _
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hTΘ.trans hΘC) hCT hT2
  rw [hO2, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ Θ.subtype_injective] at hle
  exact hle

theorem exists_prime_not_le_centralizer_pCore {Θ U : Subgroup G} (hs : Group.IsSolvable ↥Θ)
    (h3 : ¬ 3 ∣ Nat.card Θ) (hO2 : CFSG.pCore 2 ↥Θ = ⊥) (hUΘ : U ≤ Θ) (hU2 : IsPGroup 2 U)
    (hU1 : U ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧
      ¬ U ≤ Subgroup.centralizer (((CFSG.pCore r ↥Θ).map Θ.subtype : Subgroup G) : Set G) := by
  by_contra hall
  push Not at hall
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U₀ := U.subgroupOf Θ with hU₀
  have hU₀2 : IsPGroup 2 U₀ := hU2.comap_subtype
  have hcent : ∀ r : (Nat.card ↥Θ).primeFactors.attach,
      U₀ ≤ Subgroup.centralizer (CFSG.pCore r.1.1 ↥Θ : Set ↥Θ) := by
    rintro ⟨⟨r, hr⟩, -⟩
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    by_cases hr2 : r = 2
    · subst hr2
      rw [hO2]
      intro u _
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hz
      rw [hz, one_mul, mul_one]
    have hr3 : r ≠ 3 := fun h => h3 (h ▸ Nat.dvd_of_mem_primeFactors hr)
    have hr3' : 3 < r := by
      have := hrp.two_le
      omega
    have h := hall r hrp hr3'
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have := Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_subgroupOf.mp hu)) (z : G)
      ⟨z, hz, rfl⟩
    exact Subtype.ext this
  have hF := CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores hcent
  have hFF := hF.trans (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs)
  have hle := CFSG.ABGLocalTools.le_pCore_of_isPGroup_of_le_fitting hU₀2 hFF
  rw [hO2] at hle
  apply hU1
  rw [eq_bot_iff]
  intro u hu
  have hmem : (⟨u, hUΘ hu⟩ : ↥Θ) ∈ (⊥ : Subgroup ↥Θ) := hle (Subgroup.mem_subgroupOf.mpr hu)
  rw [Subgroup.mem_bot] at hmem ⊢
  exact congrArg Subtype.val hmem

end CFSG.RankThree.PartTwo.Sec16.Proof169

