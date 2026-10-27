module

public import CFSG.RankThree.PartTwo.Sec16.ResGapProofFiveSix
public import CFSG.RankThree.PartTwo.Sec16.Item16TailEnd
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient

public section

namespace CFSG.RankThree.PartTwo.Sec16.ResGapFive

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec16
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_commutator_action_c
    (hloc : ∀ r : ℕ, r.Prime → 3 < r → CFSG.Assembly.RankThreeEven.localRank r G < 3)
    {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) {X U Q : Subgroup G} (hXp : Nat.card X = 5)
    (hU2 : IsPGroup 2 U) (hUX : ⁅U, X⁆ = U) (hXU : X ≤ Subgroup.normalizer (U : Set G))
    (hQ : IsPGroup q Q) (hUQ : U ≤ Subgroup.normalizer (Q : Set G))
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) (hUC : ¬ U ≤ Subgroup.centralizer (Q : Set G))
    {c : G} (hc3 : c ^ 3 = 1) (hcU : c ∈ Subgroup.normalizer (U : Set G))
    (hcQ : c ∈ Subgroup.normalizer (Q : Set G)) (hcX : ∀ y ∈ X, y * c = c * y)
    (hcfix : ∀ u ∈ U, c * u * c⁻¹ = u → ∀ y ∈ X, y * u * y⁻¹ = u) : False := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  set K := U ⊓ Subgroup.centralizer (Q : Set G) with hK
  set N := Subgroup.normalizer (K : Set G) with hN
  have hKU : K ≤ U := inf_le_left
  have hK2 : IsPGroup 2 K := hU2.to_le hKU
  have hCN : ∀ {Y : Subgroup G}, Y ≤ Subgroup.normalizer (U : Set G) →
      Y ≤ Subgroup.normalizer (Q : Set G) → Y ≤ N := fun h1 h2 =>
    Proof169.le_normalizer_inf h1 (h2.trans (Proof169.normalizer_le_normalizer_centralizer Q))
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
    (Subgroup.disjoint_of_coprime_natCard (by
      rw [hXp]
      exact hcop2 (by norm_num) (by norm_num))).eq_bot
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
  have hXcard : Nat.card X' = 5 := by
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
    (Subgroup.map_mono (Proof169.subgroupOf_le_normalizer_subgroupOf hUQ)).trans
      (Subgroup.le_normalizer_map π)
  have hXP' : X' ≤ Subgroup.normalizer (P' : Set _) :=
    (Subgroup.map_mono (Proof169.subgroupOf_le_normalizer_subgroupOf hXQ)).trans
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
  have hcN : c ∈ N := hCN (Subgroup.zpowers_le.mpr hcU) (Subgroup.zpowers_le.mpr hcQ)
    (Subgroup.mem_zpowers c)
  set c' := π ⟨c, hcN⟩ with hc'
  have hc3' : c' ^ 3 = 1 := by
    rw [hc', ← map_pow]
    have : (⟨c, hcN⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simp [hc3])
    rw [this, map_one]
  have hcU' : c' ∈ Subgroup.normalizer (U' : Set (↥N ⧸ K')) := by
    refine Subgroup.le_normalizer_map π ⟨⟨c, hcN⟩, ?_, rfl⟩
    exact Proof169.subgroupOf_le_normalizer_subgroupOf (Subgroup.zpowers_le.mpr hcU)
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers c))
  have hcX' : ∀ y ∈ X', y * c' = c' * y := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hc', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcX y (Subgroup.mem_subgroupOf.mp hy))
  have hcfix' : ∀ u ∈ U', c' * u * c'⁻¹ = u → ∀ y ∈ X', y * u * y⁻¹ = u := by
    rintro _ ⟨u, hu, rfl⟩ hfixu _ ⟨y, hy, rfl⟩
    have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have hyX : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
    have h1 : (u : G)⁻¹ * (c * u * c⁻¹) ∈ K := by
      have h2 : π (⟨c, hcN⟩ * u * (⟨c, hcN⟩ : ↥N)⁻¹) = π u := by
        rw [map_mul, map_mul, map_inv]
        exact hfixu
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf] at h2
      have h3 := inv_mem h2
      have e : (((⟨c, hcN⟩ * u * (⟨c, hcN⟩ : ↥N)⁻¹ : ↥N)⁻¹ * u : ↥N) : G)⁻¹ =
          (u : G)⁻¹ * (c * u * c⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rwa [e] at h3
    obtain ⟨n, hnK, hfixn⟩ := exists_fixed_of_conj_mem hc3 hK2 hcN h1
    have hun : (u : G) * n ∈ U := mul_mem huU (hKU hnK)
    have hy' := hcfix _ hun hfixn y hyX
    rw [← map_mul, ← map_inv, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hyn : (y : G) * n * (y : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hXN hyX) n).mp hnK
    have e : (((y * u * y⁻¹ : ↥N)⁻¹ * u : ↥N) : G) = ((y : G) * n * (y : G)⁻¹) * n⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc ((y : G) * u * (y : G)⁻¹)⁻¹ * u
          = ((y : G) * ((u : G) * n) * (y : G)⁻¹ * ((y : G) * n⁻¹ * (y : G)⁻¹))⁻¹ * u := by
            group
        _ = ((u : G) * n * ((y : G) * n⁻¹ * (y : G)⁻¹))⁻¹ * u := by rw [hy']
        _ = (y : G) * n * (y : G)⁻¹ * n⁻¹ := by group
    rw [e]
    exact mul_mem hyn (inv_mem hnK)
  exact false_of_c_action hq hq3 hPp hUp hXcard hUX' hU'1 hUP' hXP' hfaith hfix hc3'
    hcU' hcX' hcfix'


end CFSG.RankThree.PartTwo.Sec16.ResGapFive
