module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_18_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# lemma_12_18_b
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 12.18(b). -/
public theorem CFSG.lemma_12_18_b
    {M P Q : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M)
    (hq : q ∈ section10PPrimeSet p)
    (hQle : Q ≤ M) (hQne : Q ≠ ⊥) (hQq : IsPGroup q.val Q)
    (hPinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : subgroupCentralizerIn Q P = ⊥)
    (hnotUnique : section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M})
    (hQSylow : section12SylowSubgroupIn q Q M) :
    section10AlphaPrimes M = section10BetaPrimes M ∧
      section10Malpha M ≠ ⊥ ∧ q ∉ section10AlphaPrimes M ∧
        subgroupCentralizerIn (section10Malpha M) P ≠ ⊥ ∧
          subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) = ⊥ := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  have : Fact p.val.Prime := ⟨p.property⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hP_M, _hPcard⟩
  rcases hQSylow with ⟨SQ, hSQmap⟩
  have hSQmap' : (SQ : Subgroup M).map M.subtype = Q := by
    simpa [section10AmbientSylowSubgroup] using hSQmap
  have hQproper : Q ≠ ⊤ := by
    intro hQtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      rw [← hQtop]
      exact hQle
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hnormQproper : Subgroup.normalizer (Q : Set G) ≠ ⊤ :=
    section12_normalizer_ne_top_of_ne_bot_ne_top (G := G) hQne hQproper
  have hq_dvd_Q : q.val ∣ Nat.card Q := by
    rcases hQq.card_eq_or_dvd with hcard | hdiv
    · exact False.elim (hQne ((Subgroup.card_eq_one (H := Q)).1 hcard))
    · exact hdiv
  have hqM : q ∈ subgroupPrimeSet M :=
    hq_dvd_Q.trans (Subgroup.card_dvd_of_le hQle)
  have hQsub_eq_SQ : Q.subgroupOf M = (SQ : Subgroup M) := by
    ext x
    constructor
    · intro hx
      change ((x : M) : G) ∈ Q at hx
      have hxmap : ((x : M) : G) ∈ (SQ : Subgroup M).map M.subtype := by
        simpa [hSQmap'] using hx
      rcases Subgroup.mem_map.mp hxmap with ⟨y, hySQ, hyx⟩
      have hy_eq : y = x := Subtype.ext hyx
      simpa [hy_eq] using hySQ
    · intro hx
      change ((x : M) : G) ∈ Q
      rw [← hSQmap']
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hQleD : Q ≤ ambientDerivedSubgroup M := by
    have hq_ne_p : q ≠ p := by
      intro hqp
      subst q
      have hPp : IsPGroup p.val P :=
        section12_primeOrderSubgroupsIn_isPGroup (G := G) hP
      have hQ_dvd : p.val ∣ Nat.card Q := by
        rcases hQq.card_eq_or_dvd with hcard | hdiv
        · exact False.elim (hQne ((Subgroup.card_eq_one (H := Q)).1 hcard))
        · exact hdiv
      let : Subgroup.Normalizes P Q := ⟨hPinv⟩
      have hone_fixed : (1 : Q) ∈ MulAction.fixedPoints P Q := by
        simp [MulAction.mem_fixedPoints]
      rcases hPp.exists_fixed_point_of_prime_dvd_card_of_fixed_point
          (α := Q) hQ_dvd hone_fixed with
        ⟨x, hxfix, h1x⟩
      have hfixed_eq :
          fixedPointSubgroup (↥P) (↥Q) =
            (subgroupCentralizerIn Q P).subgroupOf Q := by
        simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Q P hPinv
      have hxfix_sub : x ∈ fixedPointSubgroup (↥P) (↥Q) := by
        simpa [fixedPointSubgroup] using hxfix
      have hxCsub : x ∈ (subgroupCentralizerIn Q P).subgroupOf Q := by
        simpa [hfixed_eq] using hxfix_sub
      have hxC : (x : G) ∈ subgroupCentralizerIn Q P := by
        simpa [Subgroup.mem_subgroupOf] using hxCsub
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hCQ] using hxC
      have hx_one : x = 1 := by
        apply Subtype.ext
        simpa using hxbot
      exact h1x hx_one.symm
    have hPp : IsPGroup p.val P :=
      section12_primeOrderSubgroupsIn_isPGroup (G := G) hP
    have hPπ : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) P :=
      section8_isPiSubgroup_singleton_of_isPGroup hPp
    have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q :=
      section8_isPiSubgroup_singleton_of_isPGroup hQq
    have hdis_pq : Disjoint ({p} : Set Nat.Primes) ({q} : Set Nat.Primes) := by
      rw [Set.disjoint_left]
      intro r hrp hrq
      have hrp_eq : r = p := by simpa using hrp
      have hrq_eq : r = q := by simpa using hrq
      exact hq_ne_p (hrq_eq.symm.trans hrp_eq)
    have hcop : Nat.Coprime (Nat.card P) (Nat.card Q) :=
      section12_coprime_card_of_isPiSubgroup_disjoint_primes_current
        (G := G) hPπ hQπ hdis_pq
    let : Subgroup.Normalizes P Q := ⟨hPinv⟩
    have hfixed_eq :
        fixedPointSubgroup (↥P) (↥Q) =
          (subgroupCentralizerIn Q P).subgroupOf Q := by
      simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Q P hPinv
    have hfix_bot : fixedPointSubgroup (↥P) (↥Q) = ⊥ := by
      rw [hfixed_eq]
      simpa using congrArg (fun S : Subgroup G => S.subgroupOf Q) hCQ
    have hQnil : Group.IsNilpotent Q :=
      IsPGroup.isNilpotent (p := q.val) (G := Q) hQq
    let : Group.IsNilpotent Q := hQnil
    have hsolvQ : Group.IsSolvable Q := inferInstance
    have hsup :
        fixedPointSubgroup (↥P) (↥Q) ⊔
            commutatorAction (A := ↥P) (G := ↥Q) = ⊤ :=
      proposition_1_6_a (G := ↥Q) (A := ↥P) hsolvQ hcop
    have hcomm_top : commutatorAction (A := ↥P) (G := ↥Q) = ⊤ := by
      rw [hfix_bot, bot_sup_eq] at hsup
      exact hsup
    have hcomm_map :
        (commutatorAction (A := ↥P) (G := ↥Q)).map Q.subtype = ⁅Q, P⁆ := by
      simpa using commutatorAction_subgroup_conj_map_eq_commutator Q P hPinv
    have htop_map : (⊤ : Subgroup Q).map Q.subtype = Q := by
      ext x
      constructor
      · rintro ⟨y, _hy, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, by simp, rfl⟩
    have hcomm_eq : ⁅Q, P⁆ = Q := by
      calc
        ⁅Q, P⁆ = (commutatorAction (A := ↥P) (G := ↥Q)).map Q.subtype := by
          exact hcomm_map.symm
        _ = (⊤ : Subgroup Q).map Q.subtype := by rw [hcomm_top]
        _ = Q := htop_map
    have hcomm_le_D : ⁅Q, P⁆ ≤ ambientDerivedSubgroup M := by
      have hcomm_le : ⁅Q, P⁆ ≤ ⁅M, M⁆ :=
        Subgroup.commutator_mono hQle hP_M
      rw [ambientDerivedSubgroup, derivedSubgroup, derivedSeries_one]
      change ⁅Q, P⁆ ≤ (_root_.commutator M).map M.subtype
      rw [Subgroup.map_subtype_commutator]
      exact hcomm_le
    rw [← hcomm_eq]
    exact hcomm_le_D
  have hnormalizer_unique_contradiction
      {D : Subgroup G} (hDunique : D ∈ section9UniqueSubgroups G)
      (hDleM : D ≤ M) (hDleNorm : D ≤ Subgroup.normalizer (Q : Set G)) :
      False := by
    have hnorm_le_M : Subgroup.normalizer (Q : Set G) ≤ M :=
      section12_le_unique_maximal_of_le
        (G := G) (Y := D) (X := Subgroup.normalizer (Q : Set G)) (M := M)
        hDleNorm hnormQproper
        (section12_unique_overgroups_eq_of_contains_maximal_local
          (G := G) (H := D) (M := M) hDunique hM hDleM)
    have hnorm_unique :
        Subgroup.normalizer (Q : Set G) ∈ section9UniqueSubgroups G :=
      section9_unique_of_le hDleNorm hnormQproper hDunique
    have hsingle :
        section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) = {M} :=
      section12_unique_overgroups_eq_of_contains_maximal_local
        (G := G) (H := Subgroup.normalizer (Q : Set G)) (M := M)
        hnorm_unique hM hnorm_le_M
    exact hnotUnique hsingle
  have hqα : q ∉ section10AlphaPrimes M := by
    intro hqα
    have hQrank_three : 3 ≤ groupRank Q := by
      have hprimeRankM : 3 ≤ primeRank q.val M := Nat.succ_le_of_lt hqα.2
      have hSQrank : 3 ≤ groupRank (SQ : Subgroup M) :=
        hprimeRankM.trans (section10_primeRank_le_groupRank_sylow (G := M) SQ)
      let eSQ : (SQ : Subgroup M) ≃* Q :=
        (Subgroup.equivMapOfInjective
          (f := M.subtype) (SQ : Subgroup M) M.subtype_injective).trans
            (MulEquiv.subgroupCongr hSQmap')
      exact hSQrank.trans (groupRank_le_of_equiv eSQ.symm)
    have hQunique : Q ∈ section9UniqueSubgroups G :=
      theorem_9_6 (G := G) (K := Q) hQproper (by omega)
        (Or.inl hQrank_three)
    exact hnormalizer_unique_contradiction
      (D := Q) hQunique hQle Subgroup.le_normalizer
  have hqβ : q ∉ section10BetaPrimes M := by
    intro hqβ
    exact hqα hqβ.1
  have hαβ : section10AlphaPrimes M = section10BetaPrimes M := by
    ext r
    constructor
    · intro hrα
      by_contra hrβ
      have hrq : r ≠ q := by
        intro hrq
        subst r
        exact hqα hrα
      have hCunique : subgroupCentralizerIn M Q ∈ section9UniqueSubgroups G :=
        corollary_10_9_a_2
          (G := G) (M := M) (X := Q) (p := r) (q := q)
          hM hrα.1 hqM hrβ hqβ hrq hQle hQq (Or.inl hQleD) hrα
      let D : Subgroup G := subgroupCentralizerIn M Q
      have hDleM : D ≤ M := inf_le_left
      have hDleNorm : D ≤ Subgroup.normalizer (Q : Set G) :=
        (inf_le_right : D ≤ Subgroup.centralizer (Q : Set G)).trans
          (centralizer_le_normalizer Q)
      exact False.elim <|
        hnormalizer_unique_contradiction
          (D := D) hCunique hDleM hDleNorm
    · intro hrβ
      exact hrβ.1
  have hMα : section10Malpha M ≠ ⊥ := by
    intro hMalpha_bot
    have hMalphaSubgroup_bot : section10MalphaSubgroup M = ⊥ := by
      apply Subgroup.map_injective M.subtype_injective
      simpa [section10Malpha] using hMalpha_bot
    let K : Subgroup M := section10MalphaSubgroup M
    let D : Subgroup M := derivedSubgroup M
    rcases (theorem_10_2_d (G := G) hM).2 with ⟨hKD, hKnormalD, hquot_nil⟩
    let KsubD : Subgroup D := K.subgroupOf D
    have : KsubD.Normal := by
      simpa [KsubD, K, D] using hKnormalD
    have hKsubD_bot : KsubD = ⊥ := by
      ext x
      constructor
      · intro hx
        have hxK : (x : M) ∈ K := Subgroup.mem_subgroupOf.mp hx
        have hxbot : (x : M) ∈ (⊥ : Subgroup M) := by
          simpa [K, hMalphaSubgroup_bot] using hxK
        have hx_eq : x = 1 := by
          apply Subtype.ext
          simpa using hxbot
        simp [hx_eq]
      · intro hx
        have hx_eq : x = 1 := by
          simpa using hx
        rw [hx_eq]
        exact KsubD.one_mem
    have hDnil : Group.IsNilpotent D := by
      let e : D ⧸ KsubD ≃* D :=
        (QuotientGroup.quotientMulEquivOfEq hKsubD_bot).trans QuotientGroup.quotientBot
      have hquot_nil' : Group.IsNilpotent (D ⧸ KsubD) := by
        simpa [D, K, KsubD] using hquot_nil
      let : Group.IsNilpotent (D ⧸ KsubD) := hquot_nil'
      exact Group.nilpotent_of_mulEquiv (G := D ⧸ KsubD) (G' := D) e
    have hSQleD : (SQ : Subgroup M) ≤ D := by
      intro x hx
      have hxQ : ((x : M) : G) ∈ Q := by
        rw [← hSQmap']
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      have hxDg : ((x : M) : G) ∈ ambientDerivedSubgroup M := hQleD hxQ
      rw [ambientDerivedSubgroup, Subgroup.mem_map] at hxDg
      rcases hxDg with ⟨y, hyD, hyx⟩
      have hyxM : y = x := Subtype.ext hyx
      simpa [D, hyxM] using hyD
    let SD : Sylow q.val D := SQ.subtype hSQleD
    have hSDmap : (SD : Subgroup D).map D.subtype = (SQ : Subgroup M) := by
      calc
        (SD : Subgroup D).map D.subtype =
            ((SQ : Subgroup M).subgroupOf D).map D.subtype := by
              simp [SD, Sylow.coe_subtype]
        _ = (SQ : Subgroup M) ⊓ D := by
              exact Subgroup.subgroupOf_map_subtype (SQ : Subgroup M) D
        _ = (SQ : Subgroup M) := inf_eq_left.mpr hSQleD
    have hSDnormal : (SD : Subgroup D).Normal := by
      let : Group.IsNilpotent D := hDnil
      exact Group.IsNilpotent.sylow_normal (p := q.val) inferInstance SD
    have hSDchar : (SD : Subgroup D).Characteristic :=
      Sylow.characteristic_of_normal SD hSDnormal
    have hSQchar : (SQ : Subgroup M).Characteristic := by
      have : D.Characteristic := by infer_instance
      have hmap_char : ((SD : Subgroup D).map D.subtype).Characteristic := by
        let : (SD : Subgroup D).Characteristic := hSDchar
        simpa [D] using
          characteristic_map_subtype_of_characteristic (G := M) D (SD : Subgroup D)
      simpa [hSDmap] using hmap_char
    have hQsub_char : (Q.subgroupOf M).Characteristic := by
      simpa [hQsub_eq_SQ] using hSQchar
    have hQsub_normal : (Q.subgroupOf M).Normal := by
      let : (Q.subgroupOf M).Characteristic := hQsub_char
      infer_instance
    have hM_le_norm : M ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := Q) (K := M) hQle).mp hQsub_normal
    have hnorm_eq_M : Subgroup.normalizer (Q : Set G) = M :=
      (hM.le_iff_eq hnormQproper).mp hM_le_norm
    have hsingle :
        section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) = {M} := by
      ext N
      constructor
      · intro hN
        have hMN : M ≤ N := by
          simpa [hnorm_eq_M] using hN.2
        have hNM : N = M := (hM.le_iff_eq hN.1.1).mp hMN
        simp [hNM]
      · intro hN
        have hNM : N = M := by simpa using hN
        subst N
        exact ⟨hM, by rw [hnorm_eq_M]⟩
    exact hnotUnique hsingle
  rcases
    lemma_12_18_a
      (G := G) (M := M) (P := P) (Q := Q) (p := p) (q := q)
      hM hp hP hq hQle hQne hQq hPinv hCQ hnotUnique hMα hqα with
    ⟨hCPαne, hCPQαbot⟩
  exact ⟨hαβ, hMα, hqα, hCPαne, hCPQαbot⟩

end Section12
