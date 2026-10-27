module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.corollary_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_17
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_b

namespace CFSG
end CFSG
open CFSG

/-! # Theorem 5.5(a) from BG Section 5 -/

open scoped commutatorElement

private theorem CFSG.theorem_5_5_a_coe_smul_of_isInvariant
    {A G : Type*} [Group A] [Group G] [MulDistribMulAction A G]
    {H : Subgroup G} [IsInvariant A G H] (a : A) (x : H) :
    ((a • x : H) : G) = a • (x : G) :=
  rfl

private theorem CFSG.pCore_quotient_pCore_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    pCore p (G ⧸ pCore p G) = ⊥ := by
  let q : G →* G ⧸ pCore p G := QuotientGroup.mk' (pCore p G)
  have hmap :
      (pCore p G).map q = pCore p (G ⧸ pCore p G) := by
    exact pCore_map_mk'_eq_of_normal_isPGroup (G := G) (p := p) (pCore p G)
      (pCore_isPGroup (G := G) (p := p))
  calc
    pCore p (G ⧸ pCore p G) = (pCore p G).map q := hmap.symm
    _ = ⊥ := by
      change (pCore p G).map (QuotientGroup.mk' (pCore p G)) = ⊥
      exact QuotientGroup.map_mk'_self (N := pCore p G)

private theorem CFSG.coprime_card_quotient_pCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcomm : IsMulCommutative (G ⧸ pCore p G)) :
    Nat.Coprime p (Nat.card (G ⧸ pCore p G)) := by
  let : IsMulCommutative (G ⧸ pCore p G) := hcomm
  have hpcore_bot : pCore p (G ⧸ pCore p G) = ⊥ :=
    pCore_quotient_pCore_eq_bot (G := G) (p := p)
  by_contra hcop
  have hpdvd : p ∣ Nat.card (G ⧸ pCore p G) := by
    by_contra hpdvd'
    exact hcop ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 hpdvd')
  let P : Sylow p (G ⧸ pCore p G) := default
  have hP_card_dvd : p ∣ Nat.card (P : Subgroup (G ⧸ pCore p G)) := by
    simpa using P.dvd_card_of_dvd_card hpdvd
  have hP_ne_bot : (P : Subgroup (G ⧸ pCore p G)) ≠ ⊥ := by
    intro hPbot
    have hP_card_one : Nat.card (P : Subgroup (G ⧸ pCore p G)) = 1 := by
      rw [hPbot]
      exact Subgroup.card_bot
    exact (Fact.out : Nat.Prime p).not_dvd_one (by simpa [hP_card_one] using hP_card_dvd)
  have hP_le_pcore : (P : Subgroup (G ⧸ pCore p G)) ≤ pCore p (G ⧸ pCore p G) := by
    exact le_sSup
      ⟨Subgroup.normal_of_isMulCommutative (H := (P : Subgroup (G ⧸ pCore p G))),
        P.isPGroup'⟩
  have hP_bot : (P : Subgroup (G ⧸ pCore p G)) = ⊥ := by
    exact le_bot_iff.mp (by simpa [hpcore_bot] using hP_le_pcore)
  exact hP_ne_bot hP_bot

private theorem CFSG.theorem_5_5_a_of_derivedSubgroup_isPGroup
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (hder_p : IsPGroup p (derivedSubgroup A)) :
    IsMulCommutative (A ⧸ pCore p A) ∧ Nat.Coprime p (Nat.card (A ⧸ pCore p A)) := by
  have hder_le_pcore : derivedSubgroup A ≤ pCore p A :=
    le_sSup ⟨(inferInstance : (derivedSubgroup A).Normal), hder_p⟩
  have hquot_comm : IsMulCommutative (A ⧸ pCore p A) := by
    apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    change derivedSeries A 1 ≤ pCore p A at hder_le_pcore
    rw [derivedSeries_one] at hder_le_pcore
    exact hder_le_pcore
  exact ⟨hquot_comm, coprime_card_quotient_pCore (G := A) (p := p) hquot_comm⟩

private theorem CFSG.natCard_eq_prime_of_isPGroup_nontrivial_le_prime
    {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    (hQp : IsPGroup p Q) [Nontrivial Q] (hle : Nat.card Q ≤ p) :
    Nat.card Q = p := by
  rcases hQp.exists_card_eq with ⟨k, hk⟩
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    have hcard_one : Nat.card Q = 1 := by simpa [hk0] using hk
    exact (Nat.ne_of_gt Finite.one_lt_card) hcard_one
  have hk_le_one : k ≤ 1 := by
    rw [hk] at hle
    have hpow : p ^ k ≤ p ^ 1 := by simpa using hle
    exact (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hpow
  have hk_one : k = 1 := by omega
  simpa [hk_one] using hk

public theorem CFSG.zpowers_eq_top_of_prime_card_of_ne_one_local
    {A : Type*} [Group A] [Finite A]
    (hAprime : Nat.Prime (Nat.card A)) {a : A} (ha : a ≠ 1) :
    Subgroup.zpowers a = ⊤ := by
  have hcard_dvd : Nat.card (Subgroup.zpowers a) ∣ Nat.card A :=
    Subgroup.card_subgroup_dvd_card (Subgroup.zpowers a)
  have hcard_ne_one : Nat.card (Subgroup.zpowers a) ≠ 1 := by
    intro hcard
    have hbot : Subgroup.zpowers a = ⊥ :=
      (Subgroup.eq_bot_iff_card (H := Subgroup.zpowers a)).2 hcard
    have ha_bot : a ∈ (⊥ : Subgroup A) := by
      simpa [hbot] using (Subgroup.mem_zpowers a)
    exact ha (by simpa using ha_bot)
  have hcard_eq : Nat.card (Subgroup.zpowers a) = Nat.card A :=
    (hAprime.eq_one_or_self_of_dvd (Nat.card (Subgroup.zpowers a)) hcard_dvd).resolve_left
      hcard_ne_one
  exact (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers a)).1 hcard_eq

private theorem CFSG.theorem_5_5_a_low_rank
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R) (hrank : groupRank R ≤ 2)
    {A : Subgroup (MulAut R)} [Group.IsSolvable A] (hoddA : Odd (Nat.card A)) :
    IsMulCommutative (A ⧸ pCore p A) ∧ Nat.Coprime p (Nat.card (A ⧸ pCore p A)) := by
  let : Fact (IsPGroup p R) := ⟨hpR⟩
  have hder_p : IsPGroup p (derivedSubgroup A) :=
    theorem_4_17 (R := R) (A := A) (p := p) hpodd (hsolvA := inferInstance) hrank hoddA
  exact theorem_5_5_a_of_derivedSubgroup_isPGroup (A := A) (p := p) hder_p

private theorem CFSG.derivedSubgroup_isPGroup_of_fixingSubgroup_and_quotient
    {R : Type*} [Group R] [Finite R]
    {A : Subgroup (MulAut R)} {H : Subgroup R}
    {p : ℕ} [Fact p.Prime]
    [hfix_normal : (fixingSubgroupOf (derivedSubgroup A) R (H : Set R)).Normal]
    (hfix_p : IsPGroup p
      (fixingSubgroupOf (derivedSubgroup A) R (H : Set R)))
    (hquot_p : IsPGroup p
      ((derivedSubgroup A) ⧸ fixingSubgroupOf (derivedSubgroup A) R (H : Set R))) :
    IsPGroup p (derivedSubgroup A) := by
  let K : Subgroup (derivedSubgroup A) := fixingSubgroupOf (derivedSubgroup A) R (H : Set R)
  obtain ⟨m, hm⟩ := hquot_p.exists_card_eq
  obtain ⟨n, hn⟩ := hfix_p.exists_card_eq
  refine (IsPGroup.iff_card (p := p) (G := derivedSubgroup A)).2 ?_
  refine ⟨m + n, ?_⟩
  calc
    Nat.card (derivedSubgroup A)
        = Nat.card ((derivedSubgroup A) ⧸ K) * Nat.card K := by
            exact Subgroup.card_eq_card_quotient_mul_card_subgroup (s := K) (α := derivedSubgroup A)
    _ = p ^ m * p ^ n := by rw [hm, hn]
    _ = p ^ (m + n) := by rw [← Nat.pow_add]

private theorem CFSG.fixingSubgroupOf_normal_of_characteristic
    {B R : Type*} [Group B] [Group R] [MulDistribMulAction B R]
    {H : Subgroup R} (hHchar : H.Characteristic) :
    (fixingSubgroupOf B R (H : Set R)).Normal := by
  refine ⟨?_⟩
  intro n hn g
  rw [mem_fixingSubgroup_iff] at hn ⊢
  intro x hx
  have hx_pre : g⁻¹ • x ∈ H := by
    let φ : MulAut R := MulDistribMulAction.toMulAut B R g⁻¹
    have hxmap : φ x ∈ H :=
      (Subgroup.characteristic_iff_map_le.mp hHchar φ)
        (Subgroup.mem_map_of_mem φ.toMonoidHom hx)
    simpa [φ] using hxmap
  have hnfix : n • (g⁻¹ • x) = g⁻¹ • x := hn (g⁻¹ • x) hx_pre
  calc
    (g * n * g⁻¹) • x = g • (n • (g⁻¹ • x)) := by simp [mul_smul, mul_assoc]
    _ = g • (g⁻¹ • x) := by rw [hnfix]
    _ = x := by simp

private theorem CFSG.fixingSubgroupOf_subtype_univ_eq
    {B R : Type*} [Group B] [Group R] [MulDistribMulAction B R]
    {H : Subgroup R} [IsInvariant B R H] :
    fixingSubgroupOf B H (Set.univ : Set H) =
      fixingSubgroupOf B R (H : Set R) := by
  ext b
  rw [mem_fixingSubgroup_iff, mem_fixingSubgroup_iff]
  constructor
  · intro hb x hx
    exact congrArg Subtype.val (hb ⟨x, hx⟩ (by trivial))
  · intro hb x _
    apply Subtype.ext
    exact hb x.1 x.2

private theorem CFSG.theorem_5_5_a_high_rank_choose_R₀
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R)
    (hR : 3 ≤ groupRank R) :
    ∃ R₀ : Subgroup R, Nat.card R₀ = p ∧
      groupRank (Subgroup.centralizer (R₀ : Set R)) ≤ 2 := by
  exact (corollary_5_4 (p := p) hpodd (R := R) hnarrow.1 hR).mp hnarrow

public theorem CFSG.groupRank_at_least_three_of_generatorRank_subgroup
    {q : ℕ} (hq : Nat.Prime q)
    {G : Type*} [Group G] [Finite G] {A K : Subgroup G}
    (hAK : A ≤ K) (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A)
    (hAgen : 3 ≤ generatorRank A) :
    3 ≤ groupRank K := by
  let A' : Subgroup K := A.subgroupOf K
  have hA'p : IsPGroup q A' := by
    exact hAp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK).symm
  have hA'comm : IsMulCommutative A' := by
    let : IsMulCommutative A := hAcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := K)
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK)
  have hqrankK : 3 ≤ primeRank q K := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card K, ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
      exact hnB.trans <| (generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
    · exact ⟨A', hA'p, hA'comm, by simpa [hgen_eq] using hAgen⟩
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card K, ?_⟩
    intro n hn
    rcases hn with ⟨r, _hr, hnr⟩
    exact hnr.trans (primeRank_le_natCard (p := r) K)
  · exact ⟨q, hq, hqrankK⟩

private theorem CFSG.generatorRank_le_groupRank_of_subgroup
    {q : ℕ} (hq : Nat.Prime q)
    {G : Type*} [Group G] [Finite G] {A K : Subgroup G}
    (hAK : A ≤ K) (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A) :
    generatorRank A ≤ groupRank K := by
  let A' : Subgroup K := A.subgroupOf K
  have hA'p : IsPGroup q A' := by
    exact hAp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK).symm
  have hA'comm : IsMulCommutative A' := by
    let : IsMulCommutative A := hAcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := K)
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK)
  have hqrankK : generatorRank A ≤ primeRank q K := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card K, ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
      exact hnB.trans <| (generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
    · exact ⟨A', hA'p, hA'comm, by simp [hgen_eq]⟩
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card K, ?_⟩
    intro n hn
    rcases hn with ⟨r, _hr, hnr⟩
    exact hnr.trans (primeRank_le_natCard (p := r) K)
  · exact ⟨q, hq, hqrankK⟩

private theorem CFSG.primeRank_le_primeRank_of_subgroup
    {q : ℕ}
    {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hHK : H ≤ K) :
    primeRank q H ≤ primeRank q K := by
  classical
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := H), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨A, hAp, hAcomm, hnA⟩
    let A' : Subgroup K := (A.map H.subtype).subgroupOf K
    have hAmap_le_K : A.map H.subtype ≤ K := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨a, haA, rfl⟩
      exact hHK a.2
    have hA'p : IsPGroup q A' := by
      have hAmap_p : IsPGroup q (A.map H.subtype) := by
        exact IsPGroup.map (p := q) (H := A) hAp H.subtype
      exact hAmap_p.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := A.map H.subtype) (K := K) hAmap_le_K).symm
    have hA'comm : IsMulCommutative A' := by
      have hAmap_comm : IsMulCommutative (A.map H.subtype) := by
        let : IsMulCommutative A := hAcomm
        simpa using (Subgroup.map_isMulCommutative (f := H.subtype) (H := A))
      let : IsMulCommutative (A.map H.subtype) := hAmap_comm
      exact Subgroup.subgroupOf_isMulCommutative (H := A.map H.subtype) (K := K)
    have hgen_eq_map : generatorRank (A.map H.subtype) = generatorRank A := by
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      let e : A ≃* (A.map H.subtype) :=
        Subgroup.equivMapOfInjective (f := H.subtype) A H.subtype_injective
      exact (Group.rank_congr e).symm
    have hgen_eq : generatorRank A' = generatorRank A := by
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      let e : A' ≃* (A.map H.subtype) :=
        Subgroup.subgroupOfEquivOfLe (H := A.map H.subtype) (K := K) hAmap_le_K
      calc
        Group.rank A' = Group.rank (A.map H.subtype) := Group.rank_congr e
        _ = Group.rank A := by simpa [generatorRank_eq_group_rank] using hgen_eq_map
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card K, ?_⟩
      intro m hm
      rcases hm with ⟨B, _hBp, _hBcomm, hmB⟩
      exact hmB.trans <| (generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
    · exact ⟨A', hA'p, hA'comm, by simpa [hgen_eq] using hnA⟩

public theorem CFSG.groupRank_le_groupRank_of_subgroup
    {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hHK : H ≤ K) :
    groupRank H ≤ groupRank K := by
  classical
  rw [groupRank]
  refine csSup_le ?_ ?_
  · refine ⟨0, 2, by decide, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨q, hq, hnq⟩
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card K, ?_⟩
      intro m hm
      rcases hm with ⟨r, _hr, hmr⟩
      exact hmr.trans (primeRank_le_natCard (p := r) K)
    · exact ⟨q, hq, hnq.trans (primeRank_le_primeRank_of_subgroup (q := q) (H := H) (K := K) hHK)⟩

private theorem CFSG.subgroupCentralizerIn_le_subgroupCentralizerIn_of_le
    {G : Type*} [Group G] {H K R : Subgroup G}
    (hHK : H ≤ K) :
    subgroupCentralizerIn H R ≤ subgroupCentralizerIn K R := by
  intro x hx
  exact ⟨hHK hx.1, hx.2⟩

public theorem CFSG.pCore_centralizer_rank_le_two_of_fitting_centralizer_rank_le_two
    {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {E : Subgroup G} (_hE_le : E ≤ fittingSubgroup G)
    (hcent_rank : groupRank (subgroupCentralizerIn (fittingSubgroup G) E) ≤ 2) :
    groupRank (subgroupCentralizerIn (pCore q G) E) ≤ 2 := by
  have hpCore_le_fit : pCore q G ≤ fittingSubgroup G := pCore_le_fitting G q
  have hcent_le :
      subgroupCentralizerIn (pCore q G) E ≤ subgroupCentralizerIn (fittingSubgroup G) E :=
    subgroupCentralizerIn_le_subgroupCentralizerIn_of_le hpCore_le_fit
  exact (groupRank_le_groupRank_of_subgroup hcent_le).trans hcent_rank

private theorem CFSG.primeRank_le_groupRank_sylow
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] (S : Sylow p G) :
    primeRank p G ≤ groupRank (S : Subgroup G) := by
  classical
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := p) (G := G), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨A, hAp, hAcomm, hnA⟩
    obtain ⟨Q, hAQ⟩ := IsPGroup.exists_le_sylow (p := p) hAp
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
    let Aconj : Subgroup G := A.map (MulAut.conj g).toMonoidHom
    have hAconj_le_S : Aconj ≤ (S : Subgroup G) := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨a, haA, rfl⟩
      have haQ : a ∈ (Q : Subgroup G) := hAQ haA
      have hmem : (MulAut.conj g) a ∈ ((g • Q : Sylow p G) : Subgroup G) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) (Q : Subgroup G) haQ
      simpa [hg] using hmem
    have hAconj_p : IsPGroup p Aconj := by
      exact hAp.of_equiv
        (Subgroup.equivMapOfInjective (f := (MulAut.conj g).toMonoidHom) A
          (EquivLike.injective (MulAut.conj g)))
    have hAconj_comm : IsMulCommutative Aconj := by
      let : IsMulCommutative A := hAcomm
      simpa [Aconj] using
        (Subgroup.map_isMulCommutative (f := (MulAut.conj g).toMonoidHom) (H := A))
    have hgen_eq : generatorRank A = generatorRank Aconj := by
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      exact Group.rank_congr
        (Subgroup.equivMapOfInjective (f := (MulAut.conj g).toMonoidHom) A
          (EquivLike.injective (MulAut.conj g)))
    exact hnA.trans <| by
      rw [hgen_eq]
      exact generatorRank_le_groupRank_of_subgroup
        (q := p) (G := G) Fact.out hAconj_le_S hAconj_p hAconj_comm

public theorem CFSG.primeRank_le_two_of_sylow_groupRank_le_two
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] {S : Sylow p G}
    (hSrank : groupRank (S : Subgroup G) ≤ 2) :
    primeRank p G ≤ 2 :=
  (primeRank_le_groupRank_sylow (p := p) (G := G) S).trans hSrank

public theorem CFSG.primeRank_fitting_le_groupRank_pCore
    {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime] :
    primeRank q (fittingSubgroup G) ≤ groupRank (pCore q G) := by
  classical
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := fittingSubgroup G), inferInstance,
      Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨A, hAp, hAcomm, hnA⟩
    let Amap : Subgroup G := A.map (fittingSubgroup G).subtype
    have hAmap_p : IsPGroup q Amap := by
      exact hAp.of_equiv
        (Subgroup.equivMapOfInjective (f := (fittingSubgroup G).subtype) A
          (fittingSubgroup G).subtype_injective)
    have hAmap_comm : IsMulCommutative Amap := by
      let : IsMulCommutative A := hAcomm
      simpa [Amap] using
        (Subgroup.map_isMulCommutative (f := (fittingSubgroup G).subtype) (H := A))
    have hgen_eq : generatorRank A = generatorRank Amap := by
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      exact Group.rank_congr
        (Subgroup.equivMapOfInjective (f := (fittingSubgroup G).subtype) A
          (fittingSubgroup G).subtype_injective)
    obtain ⟨S, hAS⟩ := IsPGroup.exists_le_sylow (p := q) hAp
    have hAmap_le_Smap : Amap ≤ S.map (fittingSubgroup G).subtype := by
      exact Subgroup.map_mono hAS
    have hSmap_le_pCore : S.map (fittingSubgroup G).subtype ≤ pCore q G := by
      have hS_normal : (S : Subgroup (fittingSubgroup G)).Normal := by
        exact Group.IsNilpotent.sylow_normal (G := ↥(fittingSubgroup G)) (h := inferInstance) q S
      have : S.Characteristic := Sylow.characteristic_of_normal S hS_normal
      have hSmap_normal : (S.map (fittingSubgroup G).subtype).Normal := by
        infer_instance
      have hSmap_p : IsPGroup q (S.map (fittingSubgroup G).subtype) := by
        exact IsPGroup.map (p := q) (H := (S : Subgroup (fittingSubgroup G))) S.isPGroup'
          (fittingSubgroup G).subtype
      exact le_sSup ⟨hSmap_normal, hSmap_p⟩
    have hAmap_rank : generatorRank Amap ≤ groupRank (pCore q G) := by
      exact
        generatorRank_le_groupRank_of_subgroup
          (q := q) (G := G) Fact.out (hAmap_le_Smap.trans hSmap_le_pCore) hAmap_p hAmap_comm
    exact hnA.trans <| by simpa [hgen_eq] using hAmap_rank

public theorem CFSG.sylow_map_le_pCore_local
    {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (hN : N.Normal) (hnil : Group.IsNilpotent ↥N)
    {p : ℕ} [Fact p.Prime] (P : Sylow p ↥N) :
    P.map N.subtype ≤ pCore p G := by
  have hP_normal_sub : (P : Subgroup ↥N).Normal :=
    Group.IsNilpotent.sylow_normal hnil p P
  have hP_char : P.Characteristic :=
    Sylow.characteristic_of_normal P hP_normal_sub
  let _ : (P.map N.subtype).Normal := by infer_instance
  have hP_p : IsPGroup p (P.map N.subtype) := P.isPGroup'.map N.subtype
  exact le_sSup ⟨inferInstance, hP_p⟩

public theorem CFSG.elementaryAbelian_le_pCore_of_le_fitting
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {E : Subgroup G} [IsElementaryAbelian p E] (hE_le : E ≤ fittingSubgroup G) :
    E ≤ pCore p G := by
  classical
  have hEsub_elem : IsElementaryAbelian p (E.subgroupOf (fittingSubgroup G)) :=
    IsElementaryAbelian.subgroupOf (p := p) hE_le
  let _ : IsElementaryAbelian p (E.subgroupOf (fittingSubgroup G)) := hEsub_elem
  have hEsub_p : IsPGroup p (E.subgroupOf (fittingSubgroup G)) :=
    IsElementaryAbelian.isPGroup p (E.subgroupOf (fittingSubgroup G))
  obtain ⟨S, hEsub_le_S⟩ := IsPGroup.exists_le_sylow (p := p) hEsub_p
  have hSmap_le_pCore : S.map (fittingSubgroup G).subtype ≤ pCore p G := by
    exact sylow_map_le_pCore_local
      (G := G) (N := fittingSubgroup G) inferInstance inferInstance S
  have hEsub_map_le_Smap :
      (E.subgroupOf (fittingSubgroup G)).map (fittingSubgroup G).subtype ≤
        S.map (fittingSubgroup G).subtype := by
    exact Subgroup.map_mono hEsub_le_S
  have hEsub_map_eq :
      (E.subgroupOf (fittingSubgroup G)).map (fittingSubgroup G).subtype = E := by
    exact
      Subgroup.map_subgroupOf_eq_of_le
        (G := G) (H := E) (K := fittingSubgroup G) hE_le
  rw [← hEsub_map_eq]
  exact hEsub_map_le_Smap.trans hSmap_le_pCore

public theorem CFSG.pCore_commute_of_ne_local
    {G : Type*} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) :
    ∀ x ∈ pCore p G, ∀ y ∈ pCore q G, x * y = y * x := by
  intro x hx y hy
  have hdisj : Disjoint (pCore p G) (pCore q G) :=
    IsPGroup.disjoint_of_ne p q hpq (pCore p G) (pCore q G)
      (pCore_isPGroup (p := p) (G := G)) (pCore_isPGroup (p := q) (G := G))
  have hmem_comm : ⁅x, y⁆ ∈ ⁅pCore p G, pCore q G⁆ :=
    Subgroup.commutator_mem_commutator hx hy
  have hle : ⁅pCore p G, pCore q G⁆ ≤ pCore p G ⊓ pCore q G :=
    Subgroup.commutator_le_inf (H₁ := pCore p G) (H₂ := pCore q G)
  have hmem_inf : ⁅x, y⁆ ∈ pCore p G ⊓ pCore q G := hle hmem_comm
  have hinf_eq : (pCore p G ⊓ pCore q G : Subgroup G) = ⊥ := hdisj.eq_bot
  rw [hinf_eq] at hmem_inf
  have hcomm : ⁅x, y⁆ = (1 : G) := by simpa using hmem_inf
  rwa [commutatorElement_eq_one_iff_mul_comm] at hcomm

private theorem CFSG.actsTrivially_of_isPGroup_on_cyclic_prime_order_local
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G] [MulDistribMulAction A G]
    {p : ℕ} (hp : Nat.Prime p) (hA : IsPGroup p A) (hG_cyclic : IsCyclic G)
    (hG_card : Nat.card G = p) :
    ActsTrivially (A := A) (G := G) := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic G := hG_cyclic
  let φ : A →* MulAut G := MulDistribMulAction.toMulAut A G
  have hA_top : IsPGroup p (⊤ : Subgroup A) := by
    simpa using hA.to_subgroup (⊤ : Subgroup A)
  have hφrange_p : IsPGroup p φ.range := by
    rw [MonoidHom.range_eq_map]
    exact IsPGroup.map (p := p) (H := (⊤ : Subgroup A)) hA_top φ
  have hmulAut_card : Nat.card (MulAut G) = p - 1 := by
    rw [IsCyclic.card_mulAut, hG_card, Nat.totient_prime hp]
  have hp_not_dvd_mulAut : ¬ p ∣ Nat.card (MulAut G) := by
    intro hp_dvd
    have hdiv_one : p ∣ 1 := by
      have hdiv_sub : p ∣ p - (p - 1) := Nat.dvd_sub (dvd_refl p) (hmulAut_card ▸ hp_dvd)
      have hsub : p - (p - 1) = 1 := by
        have hp_eq : p = (p - 1) + 1 := by
          simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hp.pos).symm
        rw [hp_eq]
        exact Nat.add_sub_cancel_left (p - 1) 1
      rw [hsub] at hdiv_sub
      exact hdiv_sub
    exact hp.not_dvd_one hdiv_one
  have hp_not_dvd_range : ¬ p ∣ Nat.card φ.range := by
    intro hp_dvd
    exact hp_not_dvd_mulAut (hp_dvd.trans (Subgroup.card_subgroup_dvd_card φ.range))
  have hφrange_card_one : Nat.card φ.range = 1 :=
    (hφrange_p.card_eq_or_dvd).resolve_right hp_not_dvd_range
  have hφrange_bot : φ.range = ⊥ := (Subgroup.card_eq_one (H := φ.range)).1 hφrange_card_one
  intro a g
  have ha_range : φ a ∈ φ.range := ⟨a, rfl⟩
  have ha_bot : φ a ∈ (⊥ : Subgroup (MulAut G)) := by simpa [hφrange_bot] using ha_range
  have hφa : φ a = 1 := Subgroup.mem_bot.mp ha_bot
  simpa [φ, MulDistribMulAction.toMulAut_apply] using congrArg (fun f : MulAut G => f g) hφa

private theorem CFSG.derivedSubgroup_actsTrivially_on_cyclic_prime_order
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G] [MulDistribMulAction A G]
    {p : ℕ} [Fact p.Prime] (hG_cyclic : IsCyclic G) (hG_card : Nat.card G = p) :
    ActsTrivially (A := derivedSubgroup A) (G := G) := by
  classical
  let _ := hG_card
  let φ : A →* MulAut G := MulDistribMulAction.toMulAut A G
  let eAut : MulAut G ≃* (ZMod (Nat.card G))ˣ := IsCyclic.mulAutMulEquiv (G := G)
  let : CommGroup (MulAut G) := MonoidHom.commGroupOfInjective eAut.toMonoidHom eAut.injective
  intro a g
  have ha_comm : (a : A) ∈ _root_.commutator A := by
    change (a : A) ∈ derivedSubgroup A
    exact a.2
  have ha_ker : (a : A) ∈ φ.ker := (Abelianization.commutator_subset_ker φ) ha_comm
  have ha_one : φ (a : A) = 1 := by
    simpa [MonoidHom.mem_ker] using ha_ker
  change (a : A) • g = g
  simpa [φ, MulDistribMulAction.toMulAut_apply] using
    congrArg (fun f : MulAut G => f g) ha_one

private theorem CFSG.pow_pred_actsTrivially_on_cyclic_prime_order
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G] [MulDistribMulAction A G]
    {p : ℕ} [Fact p.Prime] (hG_cyclic : IsCyclic G) (hG_card : Nat.card G = p)
    (a : A) :
    ActsTrivially (A := Subgroup.zpowers (a ^ (p - 1))) (G := G) := by
  classical
  let : IsCyclic G := hG_cyclic
  let φ : A →* MulAut G := MulDistribMulAction.toMulAut A G
  have hmulAut_card : Nat.card (MulAut G) = p - 1 := by
    rw [IsCyclic.card_mulAut, hG_card, Nat.totient_prime (Fact.out : Nat.Prime p)]
  have hφpow : φ (a ^ (p - 1)) = 1 := by
    rw [map_pow, ← hmulAut_card]
    exact pow_card_eq_one' (G := MulAut G) (x := φ a)
  intro b g
  have hb_mem : (b : A) ∈ Subgroup.zpowers (a ^ (p - 1)) := b.2
  exact smul_eq_self_of_mem_zpowers (G := A) (α := G) hb_mem (a := g) (by
      simpa [φ, MulDistribMulAction.toMulAut_apply] using
        congrArg (fun f : MulAut G => f g) hφpow)

private theorem CFSG.actsTriviallyOn_subgroup_of_smul_div_mem_and_coprime_order
    {G A : Type*} [Group G] [Finite G] [Group A] [MulDistribMulAction A G]
    (H K : Subgroup G) (a : A)
    (hcop : Nat.Coprime (orderOf a) (Nat.card H))
    (htriv_factor : ∀ g : G, g ∈ K → (a • g) * g⁻¹ ∈ H)
    (htriv_H : ∀ g : G, g ∈ H → a • g = g) :
    ∀ g : G, g ∈ K → a • g = g := by
  intro g hgK
  set x := (a • g) * g⁻¹ with hx_def
  have hxH : x ∈ H := htriv_factor g hgK
  have hx_pow_mem : ∀ n : ℕ, x ^ n ∈ H := fun n => pow_mem hxH n
  have hax_pow : ∀ n : ℕ, a • (x ^ n) = x ^ n := fun n => htriv_H (x ^ n) (hx_pow_mem n)
  have hformula : ∀ n : ℕ, a ^ n • g = x ^ n * g := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        calc
          a ^ (n + 1) • g = a • (a ^ n • g) := by rw [pow_succ', smul_smul]
          _ = a • (x ^ n * g) := by rw [ih]
          _ = (a • (x ^ n)) * (a • g) := by rw [MulDistribMulAction.smul_mul]
          _ = x ^ n * (a • g) := by rw [hax_pow n]
          _ = x ^ n * ((a • g) * 1) := by simp
          _ = x ^ n * ((a • g) * (g⁻¹ * g)) := by group
          _ = x ^ n * (((a • g) * g⁻¹) * g) := by group
          _ = x ^ n * (x * g) := by rw [hx_def]
          _ = (x ^ n * x) * g := by rw [← mul_assoc]
          _ = x ^ (n + 1) * g := by rw [← pow_succ x n]
  have hx_pow_order : x ^ orderOf a = 1 := by
    have ha_order : a ^ orderOf a = 1 := pow_orderOf_eq_one a
    have hsmul : a ^ orderOf a • g = g := by rw [ha_order, one_smul]
    have hform := hformula (orderOf a)
    rw [hsmul] at hform
    have := congrArg (fun t : G => t * g⁻¹) hform
    simp [mul_assoc] at this
    exact this.symm
  have h_order_x_dvd_a : orderOf x ∣ orderOf a :=
    orderOf_dvd_of_pow_eq_one hx_pow_order
  have h_order_x_dvd_H : orderOf x ∣ Nat.card H :=
    Subgroup.orderOf_dvd_natCard H hxH
  have h_order_x_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h_order_x_dvd_a h_order_x_dvd_H
  have hx_one : x = 1 := orderOf_eq_one_iff.mp h_order_x_one
  calc
    a • g = x * g := by rw [hx_def]; group
    _ = 1 * g := by rw [hx_one]
    _ = g := by simp

private theorem CFSG.pow_pred_acts_trivially_of_prime_quotient_chain
    {p : ℕ} [Fact p.Prime]
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (hGp : IsPGroup p G)
    (Gi : ℕ → Subgroup G)
    (hzero : Gi 0 = ⊤)
    (hbot : ∃ n, Gi n = ⊥)
    (_hdesc : ∀ n, Gi (n + 1) ≤ Gi n)
    (hnormal : ∀ n, (Gi n).Normal)
    (hinv : ∀ n, IsInvariant A G (Gi n))
    (hquot_card : ∀ n, Gi n ≠ ⊥ →
      Nat.card ((Gi n) ⧸ (Gi (n + 1)).subgroupOf (Gi n)) = p)
    (a : A) (hcop : Nat.Coprime p (orderOf a)) :
    ∀ g : G, (a ^ (p - 1)) • g = g := by
  classical
  let b : A := a ^ (p - 1)
  have hfactor :
      ∀ i (g : G), g ∈ Gi i → (b • g) * g⁻¹ ∈ Gi (i + 1) := by
    intro i g hg
    by_cases hGi_bot : Gi i = ⊥
    · have hg_one : g = 1 := by
        simpa [hGi_bot] using hg
      rw [hg_one]
      change (b • (1 : G)) * (1 : G)⁻¹ ∈ Gi (i + 1)
      simp [smul_one]
    · let K : Subgroup G := Gi i
      let N : Subgroup K := (Gi (i + 1)).subgroupOf K
      have : K.Normal := hnormal i
      have : (Gi (i + 1)).Normal := hnormal (i + 1)
      have : N.Normal := Subgroup.Normal.subgroupOf (hnormal (i + 1)) K
      let : IsInvariant A G K := hinv i
      let : MulDistribMulAction A K := inferInstance
      have hNinv : IsInvariant A K N := by
        constructor
        intro c x
        constructor
        · intro hx
          have hxG : (x : G) ∈ Gi (i + 1) := hx
          have hsmul : c • (x : G) ∈ Gi (i + 1) :=
            (hinv (i + 1)).invariant c (x : G) |>.mp hxG
          simpa [N, Subgroup.mem_subgroupOf, theorem_5_5_a_coe_smul_of_isInvariant] using
            hsmul
        · intro hx
          have hsmulG : c • (x : G) ∈ Gi (i + 1) := by
            simpa [N, Subgroup.mem_subgroupOf, theorem_5_5_a_coe_smul_of_isInvariant] using
              hx
          have hxG : (x : G) ∈ Gi (i + 1) :=
            (hinv (i + 1)).invariant c (x : G) |>.mpr hsmulG
          simpa [N, Subgroup.mem_subgroupOf, theorem_5_5_a_coe_smul_of_isInvariant] using hxG
      let : IsInvariant A K N := hNinv
      let : MulAction.QuotientAction A N :=
        quotientAction_of_isInvariant (A := A) N hNinv
      let : MulDistribMulAction A (K ⧸ N) :=
        quotientMulDistribMulAction (A := A) (G := K) N hNinv
      have hQcard : Nat.card (K ⧸ N) = p := by
        simpa [K, N] using hquot_card i hGi_bot
      have hQcyc : IsCyclic (K ⧸ N) := isCyclic_of_prime_card hQcard
      have htriv :
          ActsTrivially (A := Subgroup.zpowers b) (G := K ⧸ N) :=
        pow_pred_actsTrivially_on_cyclic_prime_order
          (A := A) (G := K ⧸ N) (p := p) hQcyc hQcard a
      let gK : K := ⟨g, hg⟩
      let bgen : Subgroup.zpowers b := ⟨b, Subgroup.mem_zpowers b⟩
      have hfix : bgen • ((gK : K) : K ⧸ N) = ((gK : K) : K ⧸ N) :=
        htriv bgen _
      have hmk_eq : QuotientGroup.mk' N (b • gK) = QuotientGroup.mk' N gK := by
        simpa [bgen, b] using hfix
      have hdiv_mem : (b • gK) / gK ∈ N :=
        (QuotientGroup.eq_iff_div_mem (N := N) (x := b • gK) (y := gK)).1 hmk_eq
      simpa [K, N, gK, b, Subgroup.mem_subgroupOf, div_eq_mul_inv,
        theorem_5_5_a_coe_smul_of_isInvariant] using hdiv_mem
  have hcop_b_p : Nat.Coprime (orderOf b) p := by
    have hb_dvd : orderOf b ∣ orderOf a := orderOf_pow_dvd (x := a) (p - 1)
    exact Nat.Coprime.of_dvd_left hb_dvd hcop.symm
  obtain ⟨m, hm⟩ := hbot
  have htriv_chain :
      ∀ k, k ≤ m → ∀ g : G, g ∈ Gi k → b • g = g := by
    have hbase : ∀ g : G, g ∈ Gi m → b • g = g := by
      intro g hg
      have hg_one : g = 1 := by
        simpa [hm] using hg
      rw [hg_one]
      simp [smul_one]
    have hstep :
        ∀ k, k < m →
          (∀ g : G, g ∈ Gi (k + 1) → b • g = g) →
          ∀ g : G, g ∈ Gi k → b • g = g := by
      intro k hk ih
      have hcop_lower : Nat.Coprime (orderOf b) (Nat.card (Gi (k + 1))) := by
        obtain ⟨n, hn⟩ := (hGp.to_subgroup (Gi (k + 1))).exists_card_eq
        rw [hn]
        exact hcop_b_p.pow_right n
      exact
        actsTriviallyOn_subgroup_of_smul_div_mem_and_coprime_order
          (A := A) (H := Gi (k + 1)) (K := Gi k) b hcop_lower
          (hfactor k) ih
    intro k hk
    exact Nat.decreasingInduction hstep hbase hk
  intro g
  have hg : g ∈ Gi 0 := by
    rw [hzero]
    trivial
  simpa [b] using htriv_chain 0 (Nat.zero_le m) g hg

private theorem CFSG.subgroupCentralizerIn_le_omega1_centralizer_of_exponent
    {p : ℕ} [Fact p.Prime]
    {R : Type*} [Group R] {H R₀ : Subgroup R}
    (hHexp : Monoid.exponent (↥H) = p) :
    subgroupCentralizerIn H R₀ ≤
      (omega₁ (G := Subgroup.centralizer (R₀ : Set R)) (p := p)).map
        (Subgroup.centralizer (R₀ : Set R)).subtype := by
  intro x hx
  let C : Subgroup R := Subgroup.centralizer (R₀ : Set R)
  have hxH : x ∈ H := hx.1
  have hxC : x ∈ C := hx.2
  let xH : H := ⟨x, hxH⟩
  let xC : C := ⟨x, hxC⟩
  have hxH_pow : xH ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (by rw [hHexp]) xH
  have hxC_pow : xC ^ p = 1 := by
    apply Subtype.ext
    simpa [xH, xC] using congrArg Subtype.val hxH_pow
  have hxomega : xC ∈ omega₁ (G := C) (p := p) := by
    rw [omega₁, omega]
    refine Subgroup.subset_closure ?_
    simpa [pow_one] using hxC_pow
  exact Subgroup.mem_map_of_mem C.subtype hxomega

private theorem CFSG.ne_bot_of_exponent_eq_prime
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hHexp : Monoid.exponent (↥H) = p) :
    H ≠ ⊥ := by
  intro hH_bot
  have : Subsingleton ↥H := by
    rw [hH_bot]
    infer_instance
  have hexp_one : Monoid.exponent (↥H) = 1 := Monoid.exp_eq_one_of_subsingleton
  exact (show Nat.Prime p from Fact.out).ne_one <| hHexp.symm.trans hexp_one

private theorem CFSG.subgroupCentralizerIn_ne_bot_of_normal_exponent
    {p : ℕ} [Fact p.Prime]
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R)
    {H R₀ : Subgroup R} [H.Normal]
    (hHexp : Monoid.exponent (↥H) = p) :
    subgroupCentralizerIn H R₀ ≠ ⊥ := by
  have hH_ne_bot : H ≠ ⊥ := ne_bot_of_exponent_eq_prime (p := p) H hHexp
  let : Fact (IsPGroup p R) := ⟨hpR⟩
  let : Nontrivial ↥H := H.nontrivial_iff_ne_bot.mpr hH_ne_bot
  obtain ⟨x, hx_ne, hxZ⟩ :=
    exists_nontrivial_center_mem_normal (G := R) (p := p) (N := H)
  intro hCH_bot
  have hxCH : (x : R) ∈ subgroupCentralizerIn H R₀ := by
    refine ⟨x.2, ?_⟩
    exact (Subgroup.center_le_centralizer (R₀ : Set R)) hxZ
  have hxbot : (x : R) ∈ (⊥ : Subgroup R) := by simpa [hCH_bot] using hxCH
  exact hx_ne <| Subtype.ext <| by simpa using hxbot

private theorem CFSG.normal_prime_order_subgroup_le_center_of_isPGroup
    {p : ℕ} [Fact p.Prime]
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R)
    {S : Subgroup R} [S.Normal] (hScard : Nat.card S = p) :
    S ≤ Subgroup.center R := by
  classical
  let : IsCyclic S := isCyclic_of_prime_card hScard
  let : Finite (ConjAct R) := Finite.of_equiv R ConjAct.toConjAct.toEquiv
  have hConjP : IsPGroup p (ConjAct R) := hpR.of_equiv ConjAct.toConjAct
  have htriv : ActsTrivially (A := ConjAct R) (G := S) :=
    actsTrivially_of_isPGroup_on_cyclic_prime_order_local
      (A := ConjAct R) (G := S) (Fact.out : Nat.Prime p) hConjP inferInstance hScard
  intro s hs
  rw [Subgroup.mem_center_iff]
  intro r
  have hfix : ConjAct.toConjAct r • (⟨s, hs⟩ : S) = ⟨s, hs⟩ :=
    htriv (ConjAct.toConjAct r) ⟨s, hs⟩
  have hconj : r * s * r⁻¹ = s := by
    have hfix_val := congrArg Subtype.val hfix
    change ConjAct.toConjAct r • (s : R) = s at hfix_val
    simpa [ConjAct.toConjAct_smul] using hfix_val
  have hmul : r * s = s * r := by
    simpa [mul_assoc] using congrArg (fun x => x * r) hconj
  simpa [eq_comm] using hmul

private theorem CFSG.theorem_5_5_a_high_rank_R₀_not_le_H
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R)
    (hR : 3 ≤ groupRank R)
    {H R₀ : Subgroup R} [H.Normal]
    (hHcomm : ⁅H, ⊤⁆ ≤ centerIn (G := R) H)
    (hHexp : Monoid.exponent (↥H) = p)
    (hR₀card : Nat.card R₀ = p)
    (hR₀rank : groupRank (Subgroup.centralizer (R₀ : Set R)) ≤ 2) :
    ¬ R₀ ≤ H := by
  classical
  let : Fact (IsPGroup p R) := ⟨hnarrow.1⟩
  intro hR₀_le_H
  let ZH : Subgroup R := centerIn (G := R) H
  have hZH_eq : ZH = (Subgroup.center H).map H.subtype := by
    simpa [ZH] using centerIn_eq_map_center_local (G := R) H
  have hZH_norm : ZH.Normal := by
    rw [hZH_eq]
    let : (Subgroup.center H).Characteristic := Subgroup.centerCharacteristic
    exact ConjAct.normal_of_characteristic_of_normal
  let U : Subgroup R := R₀ ⊔ ZH
  have hR₀_elem : IsElementaryAbelian p R₀ := by
    let : IsCyclic R₀ := isCyclic_of_prime_card hR₀card
    exact isElementaryAbelian_of_prime_card_isCyclic (p := p) (G := R₀) hR₀card
  let : IsElementaryAbelian p R₀ := hR₀_elem
  have hZH_elem : IsElementaryAbelian p ZH := by
    refine
      { toIsMulCommutative := by
          rw [hZH_eq]
          exact Subgroup.map_isMulCommutative (f := H.subtype) (H := Subgroup.center H)
        exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro z
    apply Subtype.ext
    have hzH : (z : R) ∈ H := by
      simpa [ZH] using z.2.1
    let zH : H := ⟨z, hzH⟩
    have hzH_pow : zH ^ p = 1 := by
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (by rw [hHexp]) zH
    simpa [zH] using congrArg Subtype.val hzH_pow
  let : IsElementaryAbelian p ZH := hZH_elem
  have hZH_le_centR₀ : ZH ≤ Subgroup.centralizer (R₀ : Set R) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp hz.2) _ (hR₀_le_H hr)
  have hU_elem : IsElementaryAbelian p U :=
    isElementaryAbelian_sup_of_le_centralizer' (p := p) (E := R₀) (C := ZH) hZH_le_centR₀
  let : IsElementaryAbelian p U := hU_elem
  have hU_le_H : U ≤ H := sup_le hR₀_le_H inf_le_left
  have hU_le_centR₀ : U ≤ Subgroup.centralizer (R₀ : Set R) := by
    refine sup_le ?_ hZH_le_centR₀
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact setLike_mul_comm (s := R₀) hs hr
  have hU_norm : U.Normal := by
    refine ⟨fun u hu x => ?_⟩
    have huH : u ∈ H := hU_le_H hu
    have hux : ⁅u, x⁆ ∈ centerIn (G := R) H := by
      exact hHcomm <| Subgroup.commutator_mem_commutator huH (by simp)
    have hxcomm : ⁅x, u⁆ ∈ centerIn (G := R) H := by
      have hux_inv : ⁅u, x⁆⁻¹ ∈ centerIn (G := R) H :=
        (centerIn (G := R) H).inv_mem hux
      simpa [commutatorElement_inv] using hux_inv
    have hxcommZH : ⁅x, u⁆ ∈ ZH := by
      simpa [ZH] using hxcomm
    have hxcommU : ⁅x, u⁆ ∈ U := Subgroup.mem_sup_right hxcommZH
    simpa [commutatorElement_def, mul_assoc] using U.mul_mem hxcommU hu
  have hU_nontrivial : U ≠ ⊥ := by
    intro hU_bot
    have hR₀_bot : R₀ = ⊥ := by
      exact eq_bot_iff.mpr (fun x hx => by
        have hxU : x ∈ U := Subgroup.mem_sup_left hx
        simpa [hU_bot] using hxU)
    have hp_ne_one : p ≠ 1 := (Fact.out : Nat.Prime p).ne_one
    exact hp_ne_one <| by simpa [hR₀_bot] using hR₀card.symm
  by_cases hUcyc : IsCyclic U
  · let : IsCyclic U := hUcyc
    have : U.Normal := hU_norm
    have hU_eq_R₀ : U = R₀ := by
      let : CommGroup U := IsCyclic.commGroup
      let R₀U : Subgroup U := R₀.subgroupOf U
      have hR₀U_card : Nat.card R₀U = p := by
        rw [natCard_subgroupOf_eq R₀ U le_sup_left, hR₀card]
      have hR₀U_pow : ∀ x : R₀U, (x : U) ^ p = 1 := by
        intro x
        apply Subtype.ext
        let x₀ : R₀ := ⟨(x : U), Subgroup.mem_subgroupOf.mp x.property⟩
        have horder_dvd : orderOf ((x₀ : R₀) : R) ∣ Nat.card R₀ := by
          simpa using (Subgroup.orderOf_dvd_natCard R₀ x₀.2)
        have hxpow : (((x₀ : R₀) : R) ^ p) = 1 := by
          rw [hR₀card] at horder_dvd
          exact orderOf_dvd_iff_pow_eq_one.mp horder_dvd
        simpa [x₀] using hxpow
      have hR₀U_eq_ker :
          R₀U = (powMonoidHom (α := U) p).ker :=
        cyclic_prime_kernel_unique (p := p) (G := U) R₀U hR₀U_card hR₀U_pow
      have hU_le_R₀ : U ≤ R₀ := by
        intro u hu
        have hupow : (⟨u, hu⟩ : U) ^ p = 1 := by
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p p U) ⟨u, hu⟩
        have huKer : (⟨u, hu⟩ : U) ∈ (powMonoidHom (α := U) p).ker := by
          simpa using hupow
        have huR₀U : (⟨u, hu⟩ : U) ∈ R₀U := by
          simpa [hR₀U_eq_ker] using huKer
        exact Subgroup.mem_subgroupOf.mp huR₀U
      exact le_antisymm hU_le_R₀ le_sup_left
    have hcent_eq_top : Subgroup.centralizer (R₀ : Set R) = ⊤ := by
      apply (Subgroup.centralizer_eq_top_iff_subset).2
      have hU_le_center : U ≤ Subgroup.center R :=
        normal_prime_order_subgroup_le_center_of_isPGroup
          (p := p) (R := R) hnarrow.1 (S := U) (by
            rw [hU_eq_R₀, hR₀card])
      intro x hx
      exact hU_le_center (by simpa [hU_eq_R₀] using hx)
    have hRank_le_two : groupRank R ≤ 2 := by
      have htop : groupRank (⊤ : Subgroup R) ≤ 2 := by
        rw [← hcent_eq_top]
        exact hR₀rank
      simpa [groupRank_top_subgroup_eq R] using htop
    exact (by decide : ¬ 3 ≤ (2 : ℕ)) (le_trans hR hRank_le_two)
  · have hU_ncyc : ¬ IsCyclic U := hUcyc
    have : U.Normal := hU_norm
    have hU_rank_two : U ∈ elementaryAbelianSubgroupsOfRank p 2 R := by
      have hUp : IsPGroup p U := hnarrow.1.to_subgroup U
      rcases hUp.exists_card_eq with ⟨k, hk⟩
      have hk_ne_zero : k ≠ 0 := by
        intro hk0
        exact hU_nontrivial ((Subgroup.card_eq_one (H := U)).1 (by simpa [hk0] using hk))
      have hk_ne_one : k ≠ 1 := by
        intro hk1
        exact hU_ncyc (isCyclic_of_prime_card (by simpa [hk1] using hk))
      have hk_le_two : k ≤ 2 := by
        by_contra hk_not_le
        have hk_ge_three : 3 ≤ k := by omega
        let : Fact (IsPGroup p U) := ⟨hUp⟩
        obtain ⟨B, _hBnorm, hB_le_top, hBcard⟩ :=
          lemma_1_22 (G := U) p (⊤ : Subgroup U) inferInstance k (by simp [hk]) 3 hk_ge_three
        let Bmap : Subgroup R := B.map U.subtype
        have hBmap_le_cent : Bmap ≤ Subgroup.centralizer (R₀ : Set R) := by
          exact (Subgroup.map_subtype_le B).trans hU_le_centR₀
        have hBmap_card : Nat.card Bmap = p ^ 3 := by
          calc
            Nat.card Bmap = Nat.card B := by
              symm
              exact Nat.card_congr
                (Subgroup.equivMapOfInjective (f := U.subtype) B U.subtype_injective).toEquiv
            _ = p ^ 3 := hBcard
        have hU_top_elem : IsElementaryAbelian p (⊤ : Subgroup U) :=
          isElementaryAbelian_top (p := p) (G := U)
        have hBmap_elem : IsElementaryAbelian p Bmap := by
          let : IsElementaryAbelian p (⊤ : Subgroup U) := hU_top_elem
          have hB_elem : IsElementaryAbelian p B := by
            exact isElementaryAbelian_of_le (p := p) hB_le_top
          let : IsElementaryAbelian p B := hB_elem
          simpa [Bmap] using IsElementaryAbelian.map_subtype (p := p) (K := U) (H := B)
        let Bcent : Subgroup (Subgroup.centralizer (R₀ : Set R)) := Bmap.subgroupOf (Subgroup.centralizer (R₀ : Set R))
        have hBcent_card : Nat.card Bcent = p ^ 3 := by
          rw [natCard_subgroupOf_eq Bmap (Subgroup.centralizer (R₀ : Set R)) hBmap_le_cent,
            hBmap_card]
        have hBcent_elem : IsElementaryAbelian p Bcent := by
          let : IsElementaryAbelian p Bmap := hBmap_elem
          exact IsElementaryAbelian.subgroupOf (p := p) hBmap_le_cent
        let : IsElementaryAbelian p Bcent := hBcent_elem
        have hcent_rank_ge : 3 ≤ groupRank (Subgroup.centralizer (R₀ : Set R)) :=
          groupRank_at_least_three_of_elementaryAbelian_subgroup_card_p3'
            (p := p) (G := Subgroup.centralizer (R₀ : Set R)) (B := Bcent) hBcent_card
        exact (by decide : ¬ 3 ≤ (2 : ℕ)) (le_trans hcent_rank_ge hR₀rank)
      have hk_two : k = 2 := by omega
      exact ⟨by simpa [hk_two] using hk, hU_elem⟩
    obtain ⟨A, hA, hUA⟩ :=
      lemma_5_1_b (p := p) hpodd (R := R) hnarrow.1 hR (E := U) hU_rank_two
    have hArank : 3 ≤ generatorRank A :=
      scnSubgroup_generatorRank_at_least_three (p := p) hpodd (R := R) hnarrow.1 hA
    have hAcomm : IsMulCommutative A :=
      (scnSubgroup_normal_commutative (p := p) (R := R) hnarrow.1 hA).2
    rcases hA with ⟨_hAnorm, hAcent_eq, _hAgroupRank⟩
    have hA_le_centR₀ : A ≤ Subgroup.centralizer (R₀ : Set R) := by
      rw [← hAcent_eq]
      exact
        (Subgroup.centralizer_le (show (U : Set R) ⊆ (A : Set R) from hUA)).trans
          (Subgroup.centralizer_le
            (show (R₀ : Set R) ⊆ (U : Set R) from fun x hx => Subgroup.mem_sup_left hx))
    have hcent_rank_ge : 3 ≤ groupRank (Subgroup.centralizer (R₀ : Set R)) :=
      groupRank_at_least_three_of_generatorRank_subgroup
        (q := p) Fact.out hA_le_centR₀ (hnarrow.1.to_subgroup A)
        hAcomm hArank
    exact (by decide : ¬ 3 ≤ (2 : ℕ)) (le_trans hcent_rank_ge hR₀rank)

private theorem CFSG.theorem_5_5_a_high_rank_fixed_centralizer_order_p_of_not_le
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R)
    (hR : 3 ≤ groupRank R)
    {H R₀ : Subgroup R} [H.Normal]
    (hR₀card : Nat.card R₀ = p)
    (hR₀rank : groupRank (Subgroup.centralizer (R₀ : Set R)) ≤ 2)
    (hHexp : Monoid.exponent (↥H) = p)
    (hR₀_not_le_H : ¬ R₀ ≤ H) :
    Nat.card (subgroupCentralizerIn H R₀) = p := by
  classical
  let : Fact (IsPGroup p R) := ⟨hnarrow.1⟩
  let C : Subgroup R := Subgroup.centralizer (R₀ : Set R)
  let T : Subgroup R := subgroupCentralizerIn (CΩ₁Z₂ p R) R₀
  obtain ⟨hTcyc, _hR₀_der, hR₀T_bot, hcent⟩ :=
    theorem_5_3_d (p := p) hpodd (R := R) hnarrow hR
      (S := R₀) hR₀card hR₀rank
  have hR₀_le_C : R₀ ≤ C := by
    dsimp [C]
    rw [hcent]
    exact le_sup_left
  have hT_le_C : T ≤ C := by
    intro x hx
    exact hx.2
  have hdisj : Disjoint R₀ T := by
    rw [Subgroup.disjoint_def]
    intro x hxR₀ hxT
    have hxCΩ : x ∈ CΩ₁Z₂ p R := hxT.1
    have hxmeet : x ∈ R₀ ⊓ CΩ₁Z₂ p R := ⟨hxR₀, hxCΩ⟩
    have hxbot : x ∈ (⊥ : Subgroup R) := by
      simpa [hR₀T_bot] using hxmeet
    exact Subgroup.mem_bot.mp hxbot
  have hCncyc : ¬ IsCyclic C := by
    simpa [C, T] using
      narrow_witness_centralizer_not_cyclic
        (p := p) (R := R) hnarrow.1 hR hR₀card hTcyc hdisj hcent
  have hindex : ∃ S : Subgroup C, IsCyclic S ∧ Nat.card (C ⧸ S) = p := by
    let Tsub : Subgroup C := T.subgroupOf C
    refine ⟨Tsub, ?_, ?_⟩
    · let e : Tsub ≃* T :=
        Subgroup.subgroupOfEquivOfLe (H := T) (K := C) hT_le_C
      exact e.isCyclic.2 hTcyc
    · have hR₀sub_normal : (R₀.subgroupOf C).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hR₀_le_C]
        simpa [C] using (centralizer_le_normalizer (R := R₀))
      let : (R₀.subgroupOf C).Normal := hR₀sub_normal
      have hsupC : R₀.subgroupOf C ⊔ T.subgroupOf C = ⊤ := by
        rw [← Subgroup.subgroupOf_sup (A := R₀) (A' := T) (B := C) hR₀_le_C hT_le_C]
        simp [C, T, hcent]
      have hdisjC : Disjoint (R₀.subgroupOf C) (T.subgroupOf C) := by
        rw [Subgroup.disjoint_def]
        intro x hx0 hxT
        apply Subtype.ext
        exact Subgroup.disjoint_def.mp hdisj hx0 hxT
      have hcomp : (R₀.subgroupOf C).IsComplement' (T.subgroupOf C) :=
        isComplement'_of_disjoint_sup_eq_top_of_normal
          (R₀.subgroupOf C) (T.subgroupOf C) hdisjC hsupC
      have hcard_R₀sub : Nat.card (R₀.subgroupOf C) = p := by
        rw [natCard_subgroupOf_eq R₀ C hR₀_le_C, hR₀card]
      rw [← Subgroup.index_eq_card, hcomp.index_eq_card, hcard_R₀sub]
  let E : Subgroup R := (omega₁ (G := C) (p := p)).map C.subtype
  let : Fact (IsPGroup p C) := ⟨hnarrow.1.to_subgroup C⟩
  have hEcard : Nat.card E = p ^ 2 := by
    obtain ⟨hΩcard, _hΩelem⟩ := lemma_4_5_b (R := C) (p := p) hpodd hCncyc hindex
    calc
      Nat.card E = Nat.card (omega₁ (G := C) (p := p)) := by
        simpa [E] using
          (Nat.card_congr
            (Subgroup.equivMapOfInjective (f := C.subtype) (omega₁ (G := C) (p := p))
              C.subtype_injective).toEquiv).symm
      _ = p ^ 2 := hΩcard
  have hR₀_le_E : R₀ ≤ E := by
    intro x hxR₀
    have hxC : x ∈ C := hR₀_le_C hxR₀
    let x₀ : R₀ := ⟨x, hxR₀⟩
    have horder_dvd : orderOf ((x₀ : R₀) : R) ∣ Nat.card R₀ := by
      simpa using (Subgroup.orderOf_dvd_natCard R₀ x₀.2)
    have hxpowR : (((x₀ : R₀) : R) ^ p) = 1 := by
      rw [hR₀card] at horder_dvd
      exact orderOf_dvd_iff_pow_eq_one.mp horder_dvd
    have hxpowC : (⟨x, hxC⟩ : C) ^ p = 1 := by
      apply Subtype.ext
      simpa [x₀] using hxpowR
    have hxΩ : (⟨x, hxC⟩ : C) ∈ omega₁ (G := C) (p := p) := by
      rw [omega₁, omega]
      refine Subgroup.subset_closure ?_
      simpa [pow_one] using hxpowC
    simpa [E] using Subgroup.mem_map_of_mem C.subtype hxΩ
  have hCH_le_E :
      subgroupCentralizerIn H R₀ ≤ E := by
    simpa [E, C] using
      subgroupCentralizerIn_le_omega1_centralizer_of_exponent
        (p := p) (R := R) (H := H) (R₀ := R₀) hHexp
  have hCH_ne_bot : subgroupCentralizerIn H R₀ ≠ ⊥ :=
    subgroupCentralizerIn_ne_bot_of_normal_exponent
      (p := p) (R := R) hnarrow.1 (H := H) (R₀ := R₀) hHexp
  have hCHp : IsPGroup p (subgroupCentralizerIn H R₀) :=
    hnarrow.1.to_subgroup (subgroupCentralizerIn H R₀)
  rcases hCHp.exists_card_eq with ⟨k, hk⟩
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    apply hCH_ne_bot
    apply (Subgroup.card_eq_one (H := subgroupCentralizerIn H R₀)).1
    simpa [hk0] using hk
  have hk_le_two : k ≤ 2 := by
    have hcard_le : Nat.card (subgroupCentralizerIn H R₀) ≤ Nat.card E :=
      Subgroup.card_le_of_le hCH_le_E
    rw [hk, hEcard] at hcard_le
    exact (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hcard_le
  have hk_ne_two : k ≠ 2 := by
    intro hk2
    have hCHcard : Nat.card (subgroupCentralizerIn H R₀) = p ^ 2 := by
      simpa [hk2] using hk
    have hCH_eq_E : subgroupCentralizerIn H R₀ = E :=
      Subgroup.eq_of_le_of_card_ge hCH_le_E (by rw [hCHcard, hEcard])
    have hR₀_le_H : R₀ ≤ H := by
      intro x hxR₀
      have hxE : x ∈ E := hR₀_le_E hxR₀
      have hxCH : x ∈ subgroupCentralizerIn H R₀ := by
        simpa [hCH_eq_E] using hxE
      exact hxCH.1
    exact hR₀_not_le_H hR₀_le_H
  have hk_one : k = 1 := by omega
  simpa [hk_one] using hk

private theorem CFSG.exponent_eq_prime_of_nontrivial_subgroup_of_exponent_prime
    {p : ℕ} [Fact p.Prime]
    {R : Type*} [Group R] {H K : Subgroup R}
    (hHexp : Monoid.exponent (↥H) = p) (hK_le_H : K ≤ H) (hK_ne_bot : K ≠ ⊥) :
    Monoid.exponent (↥K) = p := by
  have hK_dvd : Monoid.exponent (↥K) ∣ p := by
    refine (Monoid.exponent_dvd_iff_forall_pow_eq_one).2 ?_
    intro x
    let xH : H := ⟨x, hK_le_H x.2⟩
    have hxHpow : xH ^ p = 1 := by
      exact (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (show Monoid.exponent (↥H) ∣ p by simp [hHexp])) xH
    apply Subtype.ext
    simpa [xH] using congrArg Subtype.val hxHpow
  have hK_ne_one : Monoid.exponent (↥K) ≠ 1 := by
    intro hKexp_one
    have hK_one : ∀ x : K, x = 1 := by
      intro x
      have hxpow : x ^ Monoid.exponent (↥K) = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (dvd_refl (Monoid.exponent (↥K))) x
      simpa [hKexp_one] using hxpow
    apply hK_ne_bot
    have : Subsingleton K := ⟨fun x y => by simp [hK_one x, hK_one y]⟩
    exact Subgroup.eq_bot_of_subsingleton (H := K)
  exact (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd (Monoid.exponent (↥K)) hK_dvd |>.resolve_left hK_ne_one

private theorem CFSG.theorem_5_5_a_high_rank_fixed_centralizer_order_p_of_characteristic
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R)
    (hR : 3 ≤ groupRank R)
    {H R₀ K : Subgroup R} [H.Normal] [K.Normal]
    (hR₀card : Nat.card R₀ = p)
    (hR₀rank : groupRank (Subgroup.centralizer (R₀ : Set R)) ≤ 2)
    (hHexp : Monoid.exponent (↥H) = p)
    (hR₀_not_le_H : ¬ R₀ ≤ H)
    (_hK_char : K.Characteristic) (hK_le_H : K ≤ H) (hK_ne_bot : K ≠ ⊥) :
    Nat.card (subgroupCentralizerIn K R₀) = p := by
  have hKexp : Monoid.exponent (↥K) = p :=
    exponent_eq_prime_of_nontrivial_subgroup_of_exponent_prime
      (p := p) (H := H) (K := K) hHexp hK_le_H hK_ne_bot
  exact
    theorem_5_5_a_high_rank_fixed_centralizer_order_p_of_not_le
      (p := p) hpodd (R := R) hnarrow hR (H := K) (R₀ := R₀)
      hR₀card hR₀rank hKexp <| by
        intro hR₀_le_K
        exact hR₀_not_le_H (hR₀_le_K.trans hK_le_H)

private theorem CFSG.elementCentralizerIn_eq_subgroupCentralizerIn_of_zpowers_eq_top
    {R : Type*} [Group R] (K R₀ : Subgroup R) (v : R₀)
    (hvgen : Subgroup.zpowers v = ⊤) :
    elementCentralizerIn K (v : R) = subgroupCentralizerIn K R₀ := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    change x ∈ Subgroup.centralizer (R₀ : Set R)
    rw [Subgroup.mem_centralizer_iff]
    intro r hrR₀
    have hrmem : (⟨r, hrR₀⟩ : R₀) ∈ Subgroup.zpowers v := by
      simp [hvgen]
    rcases Subgroup.mem_zpowers_iff.mp hrmem with ⟨m, hm⟩
    have hv_comm : (v : R) * x = x * (v : R) := by
      exact (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
    have hcomm : Commute (v : R) x := by
      exact commutatorElement_eq_one_iff_commute.mp
        ((commutatorElement_eq_one_iff_mul_comm.mpr hv_comm))
    have hr_comm : ((v : R) ^ m) * x = x * ((v : R) ^ m) := by
      exact (Commute.zpow_left hcomm m).eq
    have hrv : r = (v : R) ^ m := by
      simpa using congrArg Subtype.val hm.symm
    simpa [hrv] using hr_comm
  · intro hx
    refine ⟨hx.1, ?_⟩
    change x ∈ Subgroup.centralizer ({(v : R)} : Set R)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hx.2) (v : R) v.2).symm

private lemma CFSG.commutatorElement_mul_left_of_commutator_le_centerIn
    {R : Type*} [Group R] {H : Subgroup R}
    (hHcomm : ⁅H, (⊤ : Subgroup R)⁆ ≤ centerIn (G := R) H)
    {x y z : R} (hx : x ∈ H) (hy : y ∈ H) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hyz_cent : ⁅y, z⁆ ∈ centerIn (G := R) H :=
    hHcomm <| Subgroup.commutator_mem_commutator hy (by simp)
  have hleft :
      x * ⁅y, z⁆ * x⁻¹ = ⁅y, z⁆ := by
    calc
      x * ⁅y, z⁆ * x⁻¹ = (⁅y, z⁆ * x) * x⁻¹ := by
        rw [(Subgroup.mem_centralizer_iff.mp hyz_cent.2) x hx]
      _ = ⁅y, z⁆ := by simp [mul_assoc]
  have hEq : ⁅x * y, z⁆ * ⁅z, x⁆ = ⁅y, z⁆ := by
    calc
      ⁅x * y, z⁆ * ⁅z, x⁆ = x * ⁅y, z⁆ * x⁻¹ := by
        simp [commutatorElement_def, mul_assoc]
      _ = ⁅y, z⁆ := hleft
  have hxz_cent : ⁅x, z⁆ ∈ centerIn (G := R) H :=
    hHcomm <| Subgroup.commutator_mem_commutator hx (by simp)
  have hyz_comm : ⁅y, z⁆ * ⁅x, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ :=
    ((Subgroup.mem_centralizer_iff.mp hxz_cent.2) ⁅y, z⁆ hyz_cent.1)
  have hzx_one : ⁅z, x⁆ * ⁅x, z⁆ = 1 := by
    simpa [commutatorElement_inv] using (mul_inv_cancel (⁅z, x⁆))
  calc
    ⁅x * y, z⁆ = ⁅x * y, z⁆ * 1 := by simp
    _ = ⁅x * y, z⁆ * (⁅z, x⁆ * ⁅x, z⁆) := by rw [hzx_one]
    _ = (⁅x * y, z⁆ * ⁅z, x⁆) * ⁅x, z⁆ := by simp [mul_assoc]
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by rw [hEq]
    _ = ⁅x, z⁆ * ⁅y, z⁆ := hyz_comm

private theorem CFSG.theorem_5_5_a_commutator_quotient_card_le_centralizer
    {R : Type*} [Group R] [Finite R] {H K R₀ : Subgroup R} [K.Normal]
    [(((⁅K, (⊤ : Subgroup R)⁆).subgroupOf H).subgroupOf (K.subgroupOf H)).Normal]
    (hK_le_H : K ≤ H)
    (hHcomm : ⁅H, (⊤ : Subgroup R)⁆ ≤ centerIn (G := R) H)
    (v : R₀) (hvgen : Subgroup.zpowers v = ⊤) :
    Nat.card ((K.subgroupOf H) ⧸
        ((⁅K, (⊤ : Subgroup R)⁆).subgroupOf H).subgroupOf (K.subgroupOf H)) ≤
      Nat.card (subgroupCentralizerIn K R₀) := by
  classical
  let N : Subgroup R := ⁅K, (⊤ : Subgroup R)⁆
  have hN_le_K : N ≤ K := by
    simpa [N] using Subgroup.commutator_le_left
      (H₁ := K) (H₂ := (⊤ : Subgroup R))
  have hN_le_H : N ≤ H := hN_le_K.trans hK_le_H
  let KH : Subgroup H := K.subgroupOf H
  let NH : Subgroup H := N.subgroupOf H
  let Nsub : Subgroup KH := NH.subgroupOf KH
  let C : Subgroup R := elementCentralizerIn K (v : R)
  have hC_le_K : C ≤ K := inf_le_left
  have hC_le_H : C ≤ H := hC_le_K.trans hK_le_H
  let CH : Subgroup H := C.subgroupOf H
  have hCH_le_KH : CH ≤ KH := by
    intro x hx
    change (x : R) ∈ K
    exact hC_le_K hx
  let Csub : Subgroup KH := CH.subgroupOf KH
  let φ : KH →* Nsub :=
    { toFun := fun x => by
        let xr : R := ((x : KH) : H)
        have hxK : xr ∈ K := x.2
        have hxN : ⁅xr, (v : R)⁆ ∈ N :=
          Subgroup.commutator_mem_commutator hxK (by simp)
        have hxH : ⁅xr, (v : R)⁆ ∈ H := hN_le_H hxN
        have hxKH : (⟨⁅xr, (v : R)⁆, hxH⟩ : H) ∈ KH := hN_le_K hxN
        refine ⟨⟨⟨⁅xr, (v : R)⁆, hxH⟩, hxKH⟩, ?_⟩
        change ⁅xr, (v : R)⁆ ∈ N
        exact hxN
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        change ⁅(((x * y : KH) : H) : R), (v : R)⁆ =
          ⁅(((x : KH) : H) : R), (v : R)⁆ * ⁅(((y : KH) : H) : R), (v : R)⁆
        simpa using
          commutatorElement_mul_left_of_commutator_le_centerIn
            (H := H) hHcomm (x := (((x : KH) : H) : R))
            (y := (((y : KH) : H) : R)) (z := (v : R))
            (hK_le_H x.2) (hK_le_H y.2) }
  have hφker : φ.ker = Csub := by
    ext x
    constructor
    · intro hx
      have hxcomm : ⁅(((x : KH) : H) : R), (v : R)⁆ = 1 := by
        have h :=
          congrArg (fun y : Nsub => (((y : KH) : H) : R))
            (show φ x = 1 from hx)
        simpa [φ] using h
      change (((x : KH) : H) : R) ∈ C
      refine ⟨x.2, ?_⟩
      change (((x : KH) : H) : R) ∈ Subgroup.centralizer ({(v : R)} : Set R)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commutatorElement_eq_one_iff_mul_comm.mp hxcomm
    · intro hx
      have hxcomm : ⁅(((x : KH) : H) : R), (v : R)⁆ = 1 := by
        change (((x : KH) : H) : R) ∈ C at hx
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hx.2)
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      simpa [φ] using hxcomm
  have : Csub.Normal := by
    rw [← hφker]
    infer_instance
  have hquot_C_eq : Nat.card (KH ⧸ Csub) = Nat.card φ.range :=
    by simpa [hφker] using Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hKC_le_N : Nat.card (KH ⧸ Csub) ≤ Nat.card Nsub := by
    rw [hquot_C_eq]
    exact Subgroup.card_le_card_group (H := φ.range)
  have hcard_K_C :
      Nat.card KH = Nat.card (KH ⧸ Csub) * Nat.card Csub :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (s := Csub) (α := KH)
  have hcard_K_N :
      Nat.card KH = Nat.card (KH ⧸ Nsub) * Nat.card Nsub :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (s := Nsub) (α := KH)
  have hmul_le :
      Nat.card (KH ⧸ Nsub) * Nat.card Nsub ≤ Nat.card Csub * Nat.card Nsub := by
    calc
      Nat.card (KH ⧸ Nsub) * Nat.card Nsub = Nat.card KH := hcard_K_N.symm
      _ = Nat.card (KH ⧸ Csub) * Nat.card Csub := hcard_K_C
      _ ≤ Nat.card Nsub * Nat.card Csub := Nat.mul_le_mul_right (Nat.card Csub) hKC_le_N
      _ = Nat.card Csub * Nat.card Nsub := Nat.mul_comm _ _
  have hquot_le_Csub :
      Nat.card (KH ⧸ Nsub) ≤ Nat.card Csub :=
    Nat.le_of_mul_le_mul_right hmul_le (Nat.card_pos (α := Nsub))
  have hCsub_card : Nat.card Csub = Nat.card (subgroupCentralizerIn K R₀) := by
    calc
      Nat.card Csub = Nat.card CH := natCard_subgroupOf_eq CH KH hCH_le_KH
      _ = Nat.card C := natCard_subgroupOf_eq C H hC_le_H
      _ = Nat.card (subgroupCentralizerIn K R₀) := by
        change Nat.card (elementCentralizerIn K (v : R)) =
          Nat.card (subgroupCentralizerIn K R₀)
        rw [elementCentralizerIn_eq_subgroupCentralizerIn_of_zpowers_eq_top K R₀ v hvgen]
  simpa [KH, NH, Nsub, N, Csub, CH, C, hCsub_card] using hquot_le_Csub

private def CFSG.theorem_5_5_a_commutatorChain
    {R : Type*} [Group R] (H : Subgroup R) : ℕ → Subgroup R :=
  fun n => Nat.rec (motive := fun _ => Subgroup R) H (fun _ K => ⁅K, ⊤⁆) n

private theorem CFSG.theorem_5_5_a_commutatorChain_zero
    {R : Type*} [Group R] (H : Subgroup R) :
    theorem_5_5_a_commutatorChain H 0 = H := by
  rfl

private theorem CFSG.theorem_5_5_a_commutatorChain_succ
    {R : Type*} [Group R] (H : Subgroup R) (n : ℕ) :
    theorem_5_5_a_commutatorChain H (n + 1) =
      ⁅theorem_5_5_a_commutatorChain H n, ⊤⁆ := by
  rfl

private theorem CFSG.theorem_5_5_a_commutatorChain_characteristic
    {R : Type*} [Group R] {H : Subgroup R} (hHchar : H.Characteristic) :
    ∀ n, (theorem_5_5_a_commutatorChain H n).Characteristic := by
  intro n
  induction n with
  | zero =>
      simpa [theorem_5_5_a_commutatorChain_zero] using hHchar
  | succ n ih =>
      rw [theorem_5_5_a_commutatorChain_succ]
      let : (theorem_5_5_a_commutatorChain H n).Characteristic := ih
      infer_instance

private theorem CFSG.theorem_5_5_a_commutatorChain_descends
    {R : Type*} [Group R] {H : Subgroup R} (hHchar : H.Characteristic) :
    ∀ n,
      theorem_5_5_a_commutatorChain H (n + 1) ≤
        theorem_5_5_a_commutatorChain H n := by
  intro n
  have hchar := theorem_5_5_a_commutatorChain_characteristic (R := R) hHchar n
  let : (theorem_5_5_a_commutatorChain H n).Characteristic := hchar
  rw [theorem_5_5_a_commutatorChain_succ]
  exact Subgroup.commutator_le_left
    (H₁ := theorem_5_5_a_commutatorChain H n) (H₂ := (⊤ : Subgroup R))

private theorem CFSG.theorem_5_5_a_commutatorChain_le_lowerCentralSeries
    {R : Type*} [Group R] {H : Subgroup R} :
    ∀ n,
      theorem_5_5_a_commutatorChain H n ≤
        (⊤ : Subgroup R).lowerCentralSeries n := by
  intro n
  induction n with
  | zero =>
      simp [theorem_5_5_a_commutatorChain_zero, Subgroup.lowerCentralSeries_zero]
  | succ n ih =>
      have hmono :
          ⁅theorem_5_5_a_commutatorChain H n, (⊤ : Subgroup R)⁆ ≤
            ⁅(⊤ : Subgroup R).lowerCentralSeries n, (⊤ : Subgroup R)⁆ :=
        Subgroup.commutator_mono ih le_rfl
      simpa [theorem_5_5_a_commutatorChain_succ, Subgroup.lowerCentralSeries_succ,
        Subgroup.commutator_def] using hmono

private theorem CFSG.theorem_5_5_a_commutatorChain_eventually_bot
    {R : Type*} [Group R] [Group.IsNilpotent R] (H : Subgroup R) :
    ∃ n, theorem_5_5_a_commutatorChain H n = ⊥ := by
  obtain ⟨n, hn⟩ :=
    (Subgroup.nilpotent_iff_lowerCentralSeries (G := R)).1
      (show Group.IsNilpotent R from inferInstance)
  refine ⟨n, ?_⟩
  have hle :
      theorem_5_5_a_commutatorChain H n ≤ (⊥ : Subgroup R) := by
    simpa [hn] using
      theorem_5_5_a_commutatorChain_le_lowerCentralSeries (R := R) (H := H) n
  exact le_bot_iff.mp hle


private theorem CFSG.stabilizesNormalSeries_of_prime_quotient_chain
    {p : ℕ} [Fact p.Prime]
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (Gi : ℕ → Subgroup G)
    (hzero : Gi 0 = ⊤)
    (hbot : ∃ n, Gi n = ⊥)
    (hdesc : ∀ n, Gi (n + 1) ≤ Gi n)
    (hnormal : ∀ n, (Gi n).Normal)
    (hinv : ∀ n, IsInvariant A G (Gi n))
    (hquot_card : ∀ n, Gi n ≠ ⊥ →
      Nat.card ((Gi n) ⧸ (Gi (n + 1)).subgroupOf (Gi n)) = p) :
    ∃ (ι : Type) (Gi' : ι → Subgroup G) (next : ι → ι),
      StabilizesNormalSeries (G := G) (A := derivedSubgroup A) Gi' next := by
  classical
  refine ⟨ℕ, Gi, Nat.succ, ?_⟩
  obtain ⟨n, hn⟩ := hbot
  refine ⟨⟨0, n, hzero, hn, ⟨n, by
    simpa using Nat.succ_iterate 0 n⟩⟩, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [Nat.succ_eq_add_one] using hdesc i
  · exact hnormal
  · intro i
    let : IsInvariant A G (Gi i) := hinv i
    constructor
    intro a g
    exact IsInvariant.invariant (A := A) (G := G) (H := Gi i) (a : A) g
  · intro i a g hg
    by_cases hGi_bot : Gi i = ⊥
    · have hg_one : g = 1 := by
        simpa [hGi_bot] using hg
      have hgoal : a • g * g⁻¹ = 1 := by
        rw [hg_one]
        change ((a : A) • (1 : G)) * (1 : G)⁻¹ = 1
        simp [smul_one]
      rw [hgoal]
      rw [Nat.succ_eq_add_one]
      exact (Gi (i + 1)).one_mem
    · let K : Subgroup G := Gi i
      let N : Subgroup K := (Gi (i + 1)).subgroupOf K
      have : K.Normal := hnormal i
      have : (Gi (i + 1)).Normal := hnormal (i + 1)
      have : N.Normal := Subgroup.Normal.subgroupOf (hnormal (i + 1)) K
      let : IsInvariant A G K := hinv i
      let : MulDistribMulAction A K := inferInstance
      have hNinv : IsInvariant A K N := by
        constructor
        intro b x
        constructor
        · intro hx
          have hxG : (x : G) ∈ Gi (i + 1) := hx
          have hsmul : b • (x : G) ∈ Gi (i + 1) :=
            (hinv (i + 1)).invariant b (x : G) |>.mp hxG
          simpa [N, Subgroup.mem_subgroupOf, theorem_5_5_a_coe_smul_of_isInvariant] using
            hsmul
        · intro hx
          have hsmulG : b • (x : G) ∈ Gi (i + 1) := by
            simpa [N, Subgroup.mem_subgroupOf, theorem_5_5_a_coe_smul_of_isInvariant] using
              hx
          have hxG : (x : G) ∈ Gi (i + 1) :=
            (hinv (i + 1)).invariant b (x : G) |>.mpr hsmulG
          simpa [N, Subgroup.mem_subgroupOf, theorem_5_5_a_coe_smul_of_isInvariant] using hxG
      let : IsInvariant A K N := hNinv
      let : MulDistribMulAction A (K ⧸ N) :=
        quotientMulDistribMulAction (A := A) (G := K) N hNinv
      have hQcard : Nat.card (K ⧸ N) = p := by
        simpa [K, N] using hquot_card i hGi_bot
      have hQcyc : IsCyclic (K ⧸ N) := isCyclic_of_prime_card hQcard
      have htriv : ActsTrivially (A := derivedSubgroup A) (G := K ⧸ N) :=
        derivedSubgroup_actsTrivially_on_cyclic_prime_order
          (A := A) (G := K ⧸ N) hQcyc hQcard
      let gK : K := ⟨g, hg⟩
      have hfix : a • ((gK : K) : K ⧸ N) = ((gK : K) : K ⧸ N) := htriv a _
      have hmk_eq : QuotientGroup.mk' N (a • gK) = QuotientGroup.mk' N gK := by
        rw [MulAction.subgroup_smul_def]
        rw [MulAction.subgroup_smul_def] at hfix
        exact (MulAction.Quotient.smul_coe (H := N) (a : A) gK).symm.trans hfix
      have hdiv_mem : (a • gK) / gK ∈ N :=
        (QuotientGroup.eq_iff_div_mem (N := N) (x := a • gK) (y := gK)).1 hmk_eq
      change ((a : A) • g) * g⁻¹ ∈ Gi (i + 1)
      rw [MulAction.subgroup_smul_def] at hdiv_mem
      simpa [K, N, gK, Subgroup.mem_subgroupOf, div_eq_mul_inv,
        theorem_5_5_a_coe_smul_of_isInvariant] using hdiv_mem

private theorem CFSG.theorem_5_5_a_high_rank_series_from_H_core
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R)
    (hR : 3 ≤ groupRank R)
    {A : Subgroup (MulAut R)} [Group.IsSolvable A] (hoddA : Odd (Nat.card A))
    {H : Subgroup R}
    (hHchar : H.Characteristic)
    (hHcomm : ⁅H, ⊤⁆ ≤ centerIn (G := R) H)
    (hHnil : NilpotencyClassLe 2 (↥H))
    (hHexp : Monoid.exponent (↥H) = p)
    [hfix_normal : (fixingSubgroupOf (derivedSubgroup A) R (H : Set R)).Normal] :
    IsPGroup p
      ((derivedSubgroup A) ⧸ fixingSubgroupOf (derivedSubgroup A) R (H : Set R)) := by
  classical
  let : Fact (IsPGroup p R) := ⟨hnarrow.1⟩
  have hRnil : Group.IsNilpotent R := (Fact.out : IsPGroup p R).isNilpotent
  let : Group.IsNilpotent R := hRnil
  have : Group.IsSolvable R := inferInstance
  let : H.Characteristic := hHchar
  let : H.Normal := by infer_instance
  let : IsInvariant A R H :=
    isInvariant_of_characteristic (A := A) (G := R) H
  let : MulDistribMulAction A H := inferInstance
  let : IsInvariant (derivedSubgroup A) R H :=
    isInvariant_of_characteristic (A := derivedSubgroup A) (G := R) H
  let : MulDistribMulAction (derivedSubgroup A) H := inferInstance
  have hker_eq :
      fixingSubgroupOf (derivedSubgroup A) H (Set.univ : Set H) =
        fixingSubgroupOf (derivedSubgroup A) R (H : Set R) :=
    fixingSubgroupOf_subtype_univ_eq (B := derivedSubgroup A) (R := R) (H := H)
  let π : Set Nat.Primes := {⟨p, Fact.out⟩}
  have hHsolv : Group.IsSolvable ↥H := by infer_instance
  have hHpgroup : IsPGroup p H := (Fact.out : IsPGroup p R).to_subgroup H
  have hHpi : IsPiGroup π H := by
    rw [IsPiGroup_iff π H]
    intro q hqdvd
    rcases hHpgroup.exists_card_eq with ⟨n, hn⟩
    have hqdvd_pow : q.1 ∣ p ^ n := by
      simpa [hn] using hqdvd
    have hq_eq : q.1 = p := Nat.prime_eq_prime_of_dvd_pow q.2 Fact.out hqdvd_pow
    have hq_eq' : q = ⟨p, Fact.out⟩ := by
      apply Subtype.ext
      simpa using hq_eq
    dsimp [π]
    exact Set.mem_singleton_iff.mpr hq_eq'
  have hker_normal' : (fixingSubgroupOf (derivedSubgroup A) H (Set.univ : Set H)).Normal := by
    rw [hker_eq]
    infer_instance
  let _ := hpodd
  let _ := hR
  let _ := hoddA
  let _ := hHnil
  have hstab :
      ∃ (ι : Type) (Gi : ι → Subgroup H) (next : ι → ι),
        StabilizesNormalSeries (G := H) (A := derivedSubgroup A) Gi next := by
    obtain ⟨R₀, hR₀card, hR₀rank⟩ :=
      theorem_5_5_a_high_rank_choose_R₀
        (p := p) hpodd (R := R) hnarrow hR
    have hR₀_not_le_H : ¬ R₀ ≤ H :=
      theorem_5_5_a_high_rank_R₀_not_le_H
        (p := p) hpodd (R := R) hnarrow hR (H := H) (R₀ := R₀)
        hHcomm hHexp hR₀card hR₀rank
    let GiR : ℕ → Subgroup R := theorem_5_5_a_commutatorChain H
    let GiH : ℕ → Subgroup H := fun n => (GiR n).subgroupOf H
    have hGiR_le_H : ∀ n, GiR n ≤ H := by
      intro n
      induction n with
      | zero =>
          intro x hx
          simpa [GiR, theorem_5_5_a_commutatorChain_zero] using hx
      | succ n ih =>
          have hstep : GiR (n + 1) ≤ GiR n := by
            simpa [GiR, Nat.succ_eq_add_one] using
              theorem_5_5_a_commutatorChain_descends (R := R) hHchar n
          exact hstep.trans ih
    have hfixed_cent :
        ∀ n, GiR n ≠ ⊥ → Nat.card (subgroupCentralizerIn (GiR n) R₀) = p := by
      intro n hGi_ne_bot
      have hGi_char :
          (GiR n).Characteristic := by
        simpa [GiR] using
          theorem_5_5_a_commutatorChain_characteristic (R := R) hHchar n
      let : (GiR n).Characteristic := hGi_char
      let : (GiR n).Normal := by infer_instance
      exact
        theorem_5_5_a_high_rank_fixed_centralizer_order_p_of_characteristic
          (p := p) hpodd (R := R) hnarrow hR (H := H) (R₀ := R₀) (K := GiR n)
          hR₀card hR₀rank hHexp hR₀_not_le_H hGi_char
          (hGiR_le_H n) hGi_ne_bot
    have hzero : GiH 0 = ⊤ := by
      ext x
      simp [GiH, GiR, theorem_5_5_a_commutatorChain_zero]
    have hbot : ∃ n, GiH n = ⊥ := by
      obtain ⟨n, hn⟩ := theorem_5_5_a_commutatorChain_eventually_bot (R := R) H
      refine ⟨n, ?_⟩
      ext x
      simp [GiH, GiR, hn]
    have hdesc : ∀ n, GiH (n + 1) ≤ GiH n := by
      intro n x hx
      have hstepR : GiR (n + 1) ≤ GiR n := by
        simpa [GiH, GiR, Nat.succ_eq_add_one] using
          theorem_5_5_a_commutatorChain_descends (R := R) hHchar n
      change (x : R) ∈ GiR n
      exact hstepR hx
    have hnormal : ∀ n, (GiH n).Normal := by
      intro n
      have hGi_char :
          (GiR n).Characteristic := by
        simpa [GiR] using
          theorem_5_5_a_commutatorChain_characteristic (R := R) hHchar n
      let : (GiR n).Characteristic := hGi_char
      have hGi_norm : (GiR n).Normal := by infer_instance
      simpa [GiH] using Subgroup.Normal.subgroupOf hGi_norm H
    have hinv : ∀ n, IsInvariant A H (GiH n) := by
      intro n
      have hGi_char :
          (GiR n).Characteristic := by
        simpa [GiR] using
          theorem_5_5_a_commutatorChain_characteristic (R := R) hHchar n
      let : (GiR n).Characteristic := hGi_char
      have hGi_inv_R : IsInvariant A R (GiR n) :=
        isInvariant_of_characteristic (A := A) (G := R) (GiR n)
      constructor
      intro a x
      constructor
      · intro hx
        change a • (x : R) ∈ GiR n
        exact (hGi_inv_R.invariant a (x : R)).1 hx
      · intro hx
        change (x : R) ∈ GiR n
        have hx' : a • (x : R) ∈ GiR n := hx
        exact (hGi_inv_R.invariant a (x : R)).2 hx'
    have hquot_card :
        ∀ n, GiH n ≠ ⊥ →
          Nat.card ((GiH n) ⧸ (GiH (n + 1)).subgroupOf (GiH n)) = p := by
      intro n hGiH_ne_bot
      have hGiR_ne_bot : GiR n ≠ ⊥ := by
        intro hGiR_bot
        apply hGiH_ne_bot
        ext x
        simp [GiH, hGiR_bot]
      have hR₀_ne_bot : R₀ ≠ ⊥ := by
        intro hR₀_bot
        exact (Fact.out : Nat.Prime p).ne_one (by simpa [hR₀_bot] using hR₀card.symm)
      let : Nontrivial R₀ := R₀.nontrivial_iff_ne_bot.mpr hR₀_ne_bot
      obtain ⟨v, hv_ne_one⟩ := exists_ne (1 : R₀)
      have hvgen : Subgroup.zpowers v = ⊤ := by
        exact zpowers_eq_top_of_prime_card_of_ne_one_local
          (A := R₀) (by simpa [hR₀card] using (Fact.out : Nat.Prime p)) hv_ne_one
      have hGi_char : (GiR n).Characteristic := by
        simpa [GiR] using
          theorem_5_5_a_commutatorChain_characteristic (R := R) hHchar n
      let : (GiR n).Characteristic := hGi_char
      have : (GiR n).Normal := by infer_instance
      have :
          (((⁅GiR n, (⊤ : Subgroup R)⁆).subgroupOf H).subgroupOf
            ((GiR n).subgroupOf H)).Normal := by
        have hNnorm :
            ((GiH (n + 1)).subgroupOf (GiH n)).Normal :=
          Subgroup.Normal.subgroupOf (hnormal (n + 1)) (GiH n)
        simpa [GiH, GiR, theorem_5_5_a_commutatorChain_succ] using hNnorm
      have hquot_le_p :
          Nat.card ((GiH n) ⧸ (GiH (n + 1)).subgroupOf (GiH n)) ≤ p := by
        have hbound :=
          theorem_5_5_a_commutator_quotient_card_le_centralizer
            (H := H) (K := GiR n) (R₀ := R₀)
            (hK_le_H := hGiR_le_H n) (hHcomm := hHcomm) v hvgen
        have hcent : Nat.card (subgroupCentralizerIn (GiR n) R₀) = p :=
          hfixed_cent n hGiR_ne_bot
        simpa [GiH, GiR, theorem_5_5_a_commutatorChain_succ, hcent] using hbound
      have hNsub_ne_top :
          (GiH (n + 1)).subgroupOf (GiH n) ≠ ⊤ := by
        intro htop
        have hstep_eq_H : GiH (n + 1) = GiH n := by
          apply le_antisymm (hdesc n)
          exact (Subgroup.subgroupOf_eq_top).1 htop
        have hstep_eq_R : GiR (n + 1) = GiR n := by
          apply le_antisymm
          · simpa [GiR, Nat.succ_eq_add_one] using
              theorem_5_5_a_commutatorChain_descends (R := R) hHchar n
          · intro x hx
            have hxH : (⟨x, hGiR_le_H n hx⟩ : H) ∈ GiH n := by
              change x ∈ GiR n
              exact hx
            have hxH' : (⟨x, hGiR_le_H n hx⟩ : H) ∈ GiH (n + 1) := by
              simpa [hstep_eq_H] using hxH
            change x ∈ GiR (n + 1)
            exact hxH'
        have hconstR : ∀ k, GiR (n + k) = GiR n := by
          intro k
          induction k with
          | zero =>
              simp
          | succ k ih =>
              calc
                GiR (n + (k + 1)) = GiR ((n + k) + 1) := by rw [Nat.add_assoc]
                _ = ⁅GiR (n + k), (⊤ : Subgroup R)⁆ := by
                  simpa [GiR] using
                    theorem_5_5_a_commutatorChain_succ (R := R) H (n + k)
                _ = ⁅GiR n, (⊤ : Subgroup R)⁆ := by rw [ih]
                _ = GiR (n + 1) := by
                  simpa [GiR] using
                    (theorem_5_5_a_commutatorChain_succ (R := R) H n).symm
                _ = GiR n := hstep_eq_R
        obtain ⟨m, hm⟩ := hbot
        by_cases hmn : m ≤ n
        · have hdesc_from_m : ∀ d, GiH (m + d) ≤ GiH m := by
            intro d
            induction d with
            | zero =>
                simp
            | succ d ih =>
                calc
                  GiH (m + (d + 1)) = GiH ((m + d) + 1) := by rw [Nat.add_assoc]
                  _ ≤ GiH (m + d) := hdesc (m + d)
                  _ ≤ GiH m := ih
          obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmn
          have hle_bot : GiH n ≤ ⊥ := by
            rw [hd]
            exact (hdesc_from_m d).trans (by simp [hm])
          exact hGiH_ne_bot (le_bot_iff.mp hle_bot)
        · have hnm : n ≤ m := Nat.le_of_not_ge hmn
          obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hnm
          have hGiH_eq : GiH m = GiH n := by
            rw [hd]
            ext x
            change (x : R) ∈ GiR (n + d) ↔ (x : R) ∈ GiR n
            rw [hconstR d]
          exact hGiH_ne_bot (by simpa [hGiH_eq] using hm)
      have : ((GiH (n + 1)).subgroupOf (GiH n)).Normal :=
        Subgroup.Normal.subgroupOf (hnormal (n + 1)) (GiH n)
      have hQ_nontrivial :
          Nontrivial ((GiH n) ⧸ (GiH (n + 1)).subgroupOf (GiH n)) :=
        (QuotientGroup.nontrivial_iff
          (G := GiH n) (N := (GiH (n + 1)).subgroupOf (GiH n))).2 hNsub_ne_top
      let : Nontrivial ((GiH n) ⧸ (GiH (n + 1)).subgroupOf (GiH n)) := hQ_nontrivial
      have hQp : IsPGroup p ((GiH n) ⧸ (GiH (n + 1)).subgroupOf (GiH n)) :=
        (hHpgroup.to_subgroup (GiH n)).to_quotient ((GiH (n + 1)).subgroupOf (GiH n))
      exact natCard_eq_prime_of_isPGroup_nontrivial_le_prime (p := p) hQp hquot_le_p
    exact
      stabilizesNormalSeries_of_prime_quotient_chain
        (p := p) (G := H) (A := A) GiH hzero hbot hdesc hnormal hinv hquot_card
  have hquot_pi :
      IsPiGroup π
        ((derivedSubgroup A) ⧸ fixingSubgroupOf (derivedSubgroup A) H (Set.univ : Set H)) :=
    lemma_1_9 (G := H) (A := derivedSubgroup A) π hHsolv hHpi hstab hker_normal'
  have hquot_p : IsPGroup p
      ((derivedSubgroup A) ⧸ fixingSubgroupOf (derivedSubgroup A) H (Set.univ : Set H)) := by
    let Q := ((derivedSubgroup A) ⧸ fixingSubgroupOf (derivedSubgroup A) H (Set.univ : Set H))
    refine (IsPGroup.iff_card (p := p) (G := Q)).2 ?_
    have hQ_pos : 0 < Nat.card Q := Nat.card_pos (α := Q)
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hQ_pos.ne' ?_⟩
    intro q hqprime hqdvd
    let q' : Nat.Primes := ⟨q, hqprime⟩
    have hq_mem : q' ∈ π := (IsPiGroup_iff π Q).1 hquot_pi q' hqdvd
    have hq_eq' : q' = ⟨p, Fact.out⟩ := by
      exact Set.mem_singleton_iff.mp (by simpa [π] using hq_mem)
    simpa using congrArg Subtype.val hq_eq'
  let Q' := ((derivedSubgroup A) ⧸ fixingSubgroupOf (derivedSubgroup A) R (H : Set R))
  refine (IsPGroup.iff_card (p := p) (G := Q')).2 ?_
  obtain ⟨n, hn⟩ := hquot_p.exists_card_eq
  refine ⟨n, ?_⟩
  have hcard_eq :
      Nat.card Q' =
        Nat.card ((derivedSubgroup A) ⧸ fixingSubgroupOf (derivedSubgroup A) H (Set.univ : Set H)) := by
    exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker_eq).symm.toEquiv
  rw [hcard_eq, hn]

public theorem CFSG.theorem_5_5_b_high_rank_pow_pred_fixes_H_core
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R)
    (hR : 3 ≤ groupRank R)
    {A : Subgroup (MulAut R)} [Group.IsSolvable A] (hoddA : Odd (Nat.card A))
    {H : Subgroup R}
    (hHchar : H.Characteristic)
    (hHcomm : ⁅H, ⊤⁆ ≤ centerIn (G := R) H)
    (hHnil : NilpotencyClassLe 2 (↥H))
    (hHexp : Monoid.exponent (↥H) = p)
    (a : A) (hcop : Nat.Coprime p (orderOf a)) :
    ∀ x : R, x ∈ H → ((a ^ (p - 1) : A) : MulAut R) x = x := by
  classical
  let : Fact (IsPGroup p R) := ⟨hnarrow.1⟩
  have hRnil : Group.IsNilpotent R := (Fact.out : IsPGroup p R).isNilpotent
  let : Group.IsNilpotent R := hRnil
  let : H.Characteristic := hHchar
  let : H.Normal := by infer_instance
  let : IsInvariant A R H :=
    isInvariant_of_characteristic (A := A) (G := R) H
  let : MulDistribMulAction A H := inferInstance
  have hHpgroup : IsPGroup p H := (Fact.out : IsPGroup p R).to_subgroup H
  let _ := hoddA
  let _ := hHnil
  obtain ⟨R₀, hR₀card, hR₀rank⟩ :=
    theorem_5_5_a_high_rank_choose_R₀
      (p := p) hpodd (R := R) hnarrow hR
  have hR₀_not_le_H : ¬ R₀ ≤ H :=
    theorem_5_5_a_high_rank_R₀_not_le_H
      (p := p) hpodd (R := R) hnarrow hR (H := H) (R₀ := R₀)
      hHcomm hHexp hR₀card hR₀rank
  let GiR : ℕ → Subgroup R := theorem_5_5_a_commutatorChain H
  let GiH : ℕ → Subgroup H := fun n => (GiR n).subgroupOf H
  have hGiR_le_H : ∀ n, GiR n ≤ H := by
    intro n
    induction n with
    | zero =>
        intro x hx
        simpa [GiR, theorem_5_5_a_commutatorChain_zero] using hx
    | succ n ih =>
        have hstep : GiR (n + 1) ≤ GiR n := by
          simpa [GiR, Nat.succ_eq_add_one] using
            theorem_5_5_a_commutatorChain_descends (R := R) hHchar n
        exact hstep.trans ih
  have hfixed_cent :
      ∀ n, GiR n ≠ ⊥ → Nat.card (subgroupCentralizerIn (GiR n) R₀) = p := by
    intro n hGi_ne_bot
    have hGi_char :
        (GiR n).Characteristic := by
      simpa [GiR] using
        theorem_5_5_a_commutatorChain_characteristic (R := R) hHchar n
    let : (GiR n).Characteristic := hGi_char
    let : (GiR n).Normal := by infer_instance
    exact
      theorem_5_5_a_high_rank_fixed_centralizer_order_p_of_characteristic
        (p := p) hpodd (R := R) hnarrow hR (H := H) (R₀ := R₀) (K := GiR n)
        hR₀card hR₀rank hHexp hR₀_not_le_H hGi_char
        (hGiR_le_H n) hGi_ne_bot
  have hzero : GiH 0 = ⊤ := by
    ext x
    simp [GiH, GiR, theorem_5_5_a_commutatorChain_zero]
  have hbot : ∃ n, GiH n = ⊥ := by
    obtain ⟨n, hn⟩ := theorem_5_5_a_commutatorChain_eventually_bot (R := R) H
    refine ⟨n, ?_⟩
    ext x
    simp [GiH, GiR, hn]
  have hdesc : ∀ n, GiH (n + 1) ≤ GiH n := by
    intro n x hx
    have hstepR : GiR (n + 1) ≤ GiR n := by
      simpa [GiH, GiR, Nat.succ_eq_add_one] using
        theorem_5_5_a_commutatorChain_descends (R := R) hHchar n
    change (x : R) ∈ GiR n
    exact hstepR hx
  have hnormal : ∀ n, (GiH n).Normal := by
    intro n
    have hGi_char :
        (GiR n).Characteristic := by
      simpa [GiR] using
        theorem_5_5_a_commutatorChain_characteristic (R := R) hHchar n
    let : (GiR n).Characteristic := hGi_char
    have hGi_norm : (GiR n).Normal := by infer_instance
    simpa [GiH] using Subgroup.Normal.subgroupOf hGi_norm H
  have hinv : ∀ n, IsInvariant A H (GiH n) := by
    intro n
    have hGi_char :
        (GiR n).Characteristic := by
      simpa [GiR] using
        theorem_5_5_a_commutatorChain_characteristic (R := R) hHchar n
    let : (GiR n).Characteristic := hGi_char
    have hGi_inv_R : IsInvariant A R (GiR n) :=
      isInvariant_of_characteristic (A := A) (G := R) (GiR n)
    constructor
    intro b x
    constructor
    · intro hx
      change b • (x : R) ∈ GiR n
      exact (hGi_inv_R.invariant b (x : R)).1 hx
    · intro hx
      change (x : R) ∈ GiR n
      have hx' : b • (x : R) ∈ GiR n := hx
      exact (hGi_inv_R.invariant b (x : R)).2 hx'
  have hquot_card :
      ∀ n, GiH n ≠ ⊥ →
        Nat.card ((GiH n) ⧸ (GiH (n + 1)).subgroupOf (GiH n)) = p := by
    intro n hGiH_ne_bot
    have hGiR_ne_bot : GiR n ≠ ⊥ := by
      intro hGiR_bot
      apply hGiH_ne_bot
      ext x
      simp [GiH, hGiR_bot]
    have hR₀_ne_bot : R₀ ≠ ⊥ := by
      intro hR₀_bot
      exact (Fact.out : Nat.Prime p).ne_one (by simpa [hR₀_bot] using hR₀card.symm)
    let : Nontrivial R₀ := R₀.nontrivial_iff_ne_bot.mpr hR₀_ne_bot
    obtain ⟨v, hv_ne_one⟩ := exists_ne (1 : R₀)
    have hvgen : Subgroup.zpowers v = ⊤ := by
      exact zpowers_eq_top_of_prime_card_of_ne_one_local
        (A := R₀) (by simpa [hR₀card] using (Fact.out : Nat.Prime p)) hv_ne_one
    have hGi_char : (GiR n).Characteristic := by
      simpa [GiR] using
        theorem_5_5_a_commutatorChain_characteristic (R := R) hHchar n
    let : (GiR n).Characteristic := hGi_char
    have : (GiR n).Normal := by infer_instance
    have :
        (((⁅GiR n, (⊤ : Subgroup R)⁆).subgroupOf H).subgroupOf
          ((GiR n).subgroupOf H)).Normal := by
      have hNnorm :
          ((GiH (n + 1)).subgroupOf (GiH n)).Normal :=
        Subgroup.Normal.subgroupOf (hnormal (n + 1)) (GiH n)
      simpa [GiH, GiR, theorem_5_5_a_commutatorChain_succ] using hNnorm
    have hquot_le_p :
        Nat.card ((GiH n) ⧸ (GiH (n + 1)).subgroupOf (GiH n)) ≤ p := by
      have hbound :=
        theorem_5_5_a_commutator_quotient_card_le_centralizer
          (H := H) (K := GiR n) (R₀ := R₀)
          (hK_le_H := hGiR_le_H n) (hHcomm := hHcomm) v hvgen
      have hcent : Nat.card (subgroupCentralizerIn (GiR n) R₀) = p :=
        hfixed_cent n hGiR_ne_bot
      simpa [GiH, GiR, theorem_5_5_a_commutatorChain_succ, hcent] using hbound
    have hNsub_ne_top :
        (GiH (n + 1)).subgroupOf (GiH n) ≠ ⊤ := by
      intro htop
      have hstep_eq_H : GiH (n + 1) = GiH n := by
        apply le_antisymm (hdesc n)
        exact (Subgroup.subgroupOf_eq_top).1 htop
      have hstep_eq_R : GiR (n + 1) = GiR n := by
        apply le_antisymm
        · simpa [GiR, Nat.succ_eq_add_one] using
            theorem_5_5_a_commutatorChain_descends (R := R) hHchar n
        · intro x hx
          have hxH : (⟨x, hGiR_le_H n hx⟩ : H) ∈ GiH n := by
            change x ∈ GiR n
            exact hx
          have hxH' : (⟨x, hGiR_le_H n hx⟩ : H) ∈ GiH (n + 1) := by
            simpa [hstep_eq_H] using hxH
          change x ∈ GiR (n + 1)
          exact hxH'
      have hconstR : ∀ k, GiR (n + k) = GiR n := by
        intro k
        induction k with
        | zero =>
            simp
        | succ k ih =>
            calc
              GiR (n + (k + 1)) = GiR ((n + k) + 1) := by rw [Nat.add_assoc]
              _ = ⁅GiR (n + k), (⊤ : Subgroup R)⁆ := by
                simpa [GiR] using
                  theorem_5_5_a_commutatorChain_succ (R := R) H (n + k)
              _ = ⁅GiR n, (⊤ : Subgroup R)⁆ := by rw [ih]
              _ = GiR (n + 1) := by
                simpa [GiR] using
                  (theorem_5_5_a_commutatorChain_succ (R := R) H n).symm
              _ = GiR n := hstep_eq_R
      obtain ⟨m, hm⟩ := hbot
      by_cases hmn : m ≤ n
      · have hdesc_from_m : ∀ d, GiH (m + d) ≤ GiH m := by
          intro d
          induction d with
          | zero =>
              simp
          | succ d ih =>
              calc
                GiH (m + (d + 1)) = GiH ((m + d) + 1) := by rw [Nat.add_assoc]
                _ ≤ GiH (m + d) := hdesc (m + d)
                _ ≤ GiH m := ih
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmn
        have hle_bot : GiH n ≤ ⊥ := by
          rw [hd]
          have hm_le : GiH m ≤ ⊥ := by rw [hm]
          exact (hdesc_from_m d).trans hm_le
        exact hGiH_ne_bot (le_bot_iff.mp hle_bot)
      · have hnm : n ≤ m := Nat.le_of_not_ge hmn
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hnm
        have hGiH_eq : GiH m = GiH n := by
          rw [hd]
          ext x
          change (x : R) ∈ GiR (n + d) ↔ (x : R) ∈ GiR n
          rw [hconstR d]
        exact hGiH_ne_bot (by simpa [hGiH_eq] using hm)
    have : ((GiH (n + 1)).subgroupOf (GiH n)).Normal :=
      Subgroup.Normal.subgroupOf (hnormal (n + 1)) (GiH n)
    have hQ_nontrivial :
        Nontrivial ((GiH n) ⧸ (GiH (n + 1)).subgroupOf (GiH n)) :=
      (QuotientGroup.nontrivial_iff
        (G := GiH n) (N := (GiH (n + 1)).subgroupOf (GiH n))).2 hNsub_ne_top
    let : Nontrivial ((GiH n) ⧸ (GiH (n + 1)).subgroupOf (GiH n)) := hQ_nontrivial
    have hQp : IsPGroup p ((GiH n) ⧸ (GiH (n + 1)).subgroupOf (GiH n)) :=
      (hHpgroup.to_subgroup (GiH n)).to_quotient ((GiH (n + 1)).subgroupOf (GiH n))
    exact natCard_eq_prime_of_isPGroup_nontrivial_le_prime (p := p) hQp hquot_le_p
  exact
    fun x hx => by
      have hfix :=
        pow_pred_acts_trivially_of_prime_quotient_chain
          (p := p) (G := H) (A := A) hHpgroup GiH hzero hbot hdesc hnormal hinv hquot_card a hcop
          ⟨x, hx⟩
      exact congrArg Subtype.val hfix

public theorem CFSG.theorem_5_5_a_high_rank_series_bridge
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R) (hR : 3 ≤ groupRank R)
    {A : Subgroup (MulAut R)} [Group.IsSolvable A] (hoddA : Odd (Nat.card A)) :
    IsPGroup p (derivedSubgroup A) := by
  classical
  let : Fact (IsPGroup p R) := ⟨hnarrow.1⟩
  have hR_nontrivial : Nontrivial R := by
    refine not_subsingleton_iff_nontrivial.mp ?_
    intro hsub
    let : Subsingleton R := hsub
    have hcyc : IsCyclic R := inferInstance
    have hRank_le_one : groupRank R ≤ 1 := groupRank_le_one_of_isCyclic R
    exact (by decide : ¬ 3 ≤ (1 : ℕ)) (le_trans hR hRank_le_one)
  let : Nontrivial R := hR_nontrivial
  obtain ⟨H, hHchar, hHcomm, hHnil, hHexp, hAfix_p⟩ :=
    theorem_1_13 (G := R) (p := p) hpodd
  have : (fixingSubgroupOf (derivedSubgroup A) R (H : Set R)).Normal :=
    fixingSubgroupOf_normal_of_characteristic
      (B := derivedSubgroup A) (R := R) hHchar
  have hfix_p : IsPGroup p
      (fixingSubgroupOf (derivedSubgroup A) R (H : Set R)) := by
    let Afix : Subgroup (MulAut R) :=
      fixingSubgroup (M := MulAut R) (α := R) (H : Set R)
    let K : Subgroup (derivedSubgroup A) :=
      fixingSubgroupOf (derivedSubgroup A) R (H : Set R)
    let φ : K →* Afix := {
      toFun := fun a => by
        refine ⟨((((a : K) : derivedSubgroup A) : A) : MulAut R), ?_⟩
        rw [mem_fixingSubgroup_iff]
        intro x hx
        have ha :=
          (mem_fixingSubgroup_iff
            (M := derivedSubgroup A) (s := (H : Set R))).1 a.2 x hx
        rw [MulAction.subgroup_smul_def, MulAction.subgroup_smul_def] at ha
        simpa [MulAction.subgroup_smul_def, MulAut.smul_def] using ha
      map_one' := by
        ext x
        rfl
      map_mul' := by
        intro a b
        ext x
        rfl }
    have hφinj : Function.Injective φ := by
      intro a b hab
      have hφval :
          ((((a : K) : derivedSubgroup A) : A) : MulAut R) =
            ((((b : K) : derivedSubgroup A) : A) : MulAut R) := by
        have h := congrArg Subtype.val hab
        dsimp [φ] at h
        exact h
      exact Subtype.ext (Subtype.ext (Subtype.ext hφval))
    exact hAfix_p.of_injective φ hφinj
  have hquot_p : IsPGroup p
      ((derivedSubgroup A) ⧸ fixingSubgroupOf (derivedSubgroup A) R (H : Set R)) :=
    theorem_5_5_a_high_rank_series_from_H_core
      (p := p) hpodd (R := R) hnarrow hR (A := A) hoddA
      hHchar hHcomm hHnil hHexp
  exact
    derivedSubgroup_isPGroup_of_fixingSubgroup_and_quotient
      (R := R) (A := A) (H := H) hfix_p hquot_p

private theorem CFSG.theorem_5_5_a_high_rank
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R) (hR : 3 ≤ groupRank R)
    {A : Subgroup (MulAut R)} [Group.IsSolvable A] (hoddA : Odd (Nat.card A)) :
    IsMulCommutative (A ⧸ pCore p A) ∧ Nat.Coprime p (Nat.card (A ⧸ pCore p A)) := by
  have hder_p : IsPGroup p (derivedSubgroup A) :=
    theorem_5_5_a_high_rank_series_bridge
      (p := p) hpodd (R := R) hnarrow hR (A := A) hoddA
  exact theorem_5_5_a_of_derivedSubgroup_isPGroup (A := A) (p := p) hder_p

public theorem CFSG.theorem_5_5_a
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R)
    {A : Subgroup (MulAut R)} [Group.IsSolvable A] (hoddA : Odd (Nat.card A)) :
    IsMulCommutative (A ⧸ pCore p A) ∧ Nat.Coprime p (Nat.card (A ⧸ pCore p A)) := by
  classical
  have hpR : IsPGroup p R := hnarrow.1
  by_cases hrank : groupRank R ≤ 2
  · exact theorem_5_5_a_low_rank (p := p) hpodd (R := R) hpR hrank (A := A) hoddA
  · have hR : 3 ≤ groupRank R := by omega
    exact theorem_5_5_a_high_rank (p := p) hpodd (R := R) hnarrow hR (A := A) hoddA
