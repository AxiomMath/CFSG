module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.gorenstein_5_4_15
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_20_a

namespace CFSG
end CFSG
open CFSG

/-! # Theorem 4.20(c) from BG Section 4 -/

universe u

section Main

open scoped FixedPoints


public theorem CFSG.theorem_4_20_rank_hyp_of_normal_subgroup
    {G : Type*} [Group G] [Finite G] (K : Subgroup G) [K.Normal]
    (hrank : groupRank G ≤ 2 ∨ groupRank (fittingSubgroup G) ≤ 2) :
    groupRank K ≤ 2 ∨ groupRank (fittingSubgroup K) ≤ 2 := by
  classical
  rcases hrank with hG | hF
  · exact Or.inl ((groupRank_le_of_subgroup (R := G) K).trans hG)
  · right
    let FK : Subgroup K := fittingSubgroup K
    let FKG : Subgroup G := FK.map K.subtype
    have hFKG_le_FG : FKG ≤ fittingSubgroup G := by
      simpa [FK, FKG, fittingSubgroupOf] using
        fittingSubgroupOf_le_fittingSubgroup (G := G) K (inferInstance : K.Normal)
    let FKGsub : Subgroup (fittingSubgroup G) := FKG.subgroupOf (fittingSubgroup G)
    let eMap : FK ≃* FKG := Subgroup.equivMapOfInjective FK K.subtype K.subtype_injective
    let eSub : FKGsub ≃* FKG :=
      Subgroup.subgroupOfEquivOfLe (G := G) (H := FKG) (K := fittingSubgroup G) hFKG_le_FG
    have hFK_rank_le :
        groupRank FK ≤ groupRank FKGsub := by
      exact groupRank_le_of_equiv (R := FKGsub) (S := FK) (eSub.trans eMap.symm)
    exact hFK_rank_le.trans ((groupRank_le_of_subgroup (R := fittingSubgroup G) FKGsub).trans hF)

private noncomputable def CFSG.topQuotientSubgroupOfEquivQuotient
    {G : Type*} [Group G] (K : Subgroup G) [K.Normal] :
    ((⊤ : Subgroup G) ⧸ K.subgroupOf (⊤ : Subgroup G)) ≃* G ⧸ K := by
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have htop_map : (⊤ : Subgroup G).map q = ⊤ := by
    exact Subgroup.map_top_of_surjective (f := q) (QuotientGroup.mk'_surjective K)
  exact (quotientSubgroupRangeEquiv (⊤ : Subgroup G) K).trans
    ((MulEquiv.subgroupCongr htop_map).trans Subgroup.topEquiv)

public theorem CFSG.inf_eq_bot_of_pSubgroup_and_pPrime_card
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H K : Subgroup G} (hHp : IsPGroup p H) (hKcop : Nat.Coprime p (Nat.card K)) :
    H ⊓ K = ⊥ := by
  have hHKsub_p : IsPGroup p ↥((H ⊓ K).subgroupOf H) :=
    IsPGroup.to_subgroup (H := (H ⊓ K).subgroupOf H) hHp
  have hHKp : IsPGroup p ↥(H ⊓ K) := by
    exact hHKsub_p.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := H ⊓ K) (K := H) inf_le_left)
  have hHKcard_dvd : Nat.card ↥(H ⊓ K) ∣ Nat.card K := by
    have hsub_dvd : Nat.card ↥((H ⊓ K).subgroupOf K) ∣ Nat.card K :=
      Subgroup.card_subgroup_dvd_card ((H ⊓ K).subgroupOf K)
    have hcard_eq : Nat.card ↥((H ⊓ K).subgroupOf K) = Nat.card ↥(H ⊓ K) := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := H ⊓ K) (K := K) inf_le_right).toEquiv
    rwa [hcard_eq] at hsub_dvd
  have hHKcop : Nat.Coprime p (Nat.card ↥(H ⊓ K)) :=
    Nat.Coprime.of_dvd_right hHKcard_dvd hKcop
  have hcard_one : Nat.card ↥(H ⊓ K) = 1 := by
    rcases hHKp.card_eq_or_dvd with h1 | hpdiv
    · exact h1
    · exfalso
      exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hHKcop) hpdiv
  exact Subgroup.card_eq_one.mp hcard_one

private theorem CFSG.sylow_map_quotient_pPrimeCore_eq_top_of_hasNormalPComplement
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcomp : HasNormalPComplement p G) (S : Sylow p G) :
    (S : Subgroup G).map (QuotientGroup.mk' (pPrimeCore p G)) = ⊤ := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let Q := G ⧸ M
  have hQp : IsPGroup p Q :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := p) (H := G) hcomp
  let Tmap : Sylow p Q := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective M)
  have htop_p : IsPGroup p (⊤ : Subgroup Q) := by
    simpa using hQp.to_subgroup (⊤ : Subgroup Q)
  let Ttop : Sylow p Q :=
    IsPGroup.toSylow (G := Q) (p := p) htop_p (by
      simpa using (Fact.out : Nat.Prime p).not_dvd_one)
  have hTtop_normal : (Ttop : Subgroup Q).Normal := by
    have hTtop_eq : (Ttop : Subgroup Q) = ⊤ := by
      dsimp [Ttop]
    rw [hTtop_eq]
    infer_instance
  have : Unique (Sylow p Q) := Sylow.unique_of_normal Ttop hTtop_normal
  have hSylow_eq : Tmap = Ttop := Subsingleton.elim _ _
  change (Tmap : Subgroup Q) = ⊤
  simpa [Tmap, Ttop, IsPGroup.toSylow_coe, q, M, Q] using
    congrArg (fun P : Sylow p Q => (P : Subgroup Q)) hSylow_eq

private noncomputable def CFSG.quotientPPrimeCoreEquivSylowOfHasNormalPComplement
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcomp : HasNormalPComplement p G) (S : Sylow p G) :
    (G ⧸ pPrimeCore p G) ≃* ↥(S : Subgroup G) := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  have hSmap_top : (S : Subgroup G).map q = ⊤ := by
    simpa [q, M] using
      sylow_map_quotient_pPrimeCore_eq_top_of_hasNormalPComplement
        (G := G) (p := p) hcomp S
  let qS : ↥(S : Subgroup G) →* (S : Subgroup G).map q := q.subgroupMap (S : Subgroup G)
  have hqS_surj : Function.Surjective qS := MonoidHom.subgroupMap_surjective q (S : Subgroup G)
  have hqS_range_top : qS.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    exact hqS_surj
  have hM_cop : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  have hS_inf_M : (S : Subgroup G) ⊓ M = ⊥ :=
    inf_eq_bot_of_pSubgroup_and_pPrime_card (G := G) (p := p) S.isPGroup' hM_cop
  have hqS_ker : qS.ker = ⊥ := by
    have hker : qS.ker = M.subgroupOf (S : Subgroup G) := by
      simpa [qS, q, M, QuotientGroup.ker_mk'] using
        (Subgroup.ker_subgroupMap (f := q) (H := (S : Subgroup G)))
    rw [hker, Subgroup.subgroupOf_eq_bot, disjoint_iff]
    simpa [inf_comm] using hS_inf_M
  let eKer : ↥(S : Subgroup G) ⧸ qS.ker ≃* ↥(S : Subgroup G) :=
    (QuotientGroup.quotientMulEquivOfEq hqS_ker).trans QuotientGroup.quotientBot
  let eImage : ↥(S : Subgroup G) ⧸ qS.ker ≃* (S : Subgroup G).map q :=
    (QuotientGroup.quotientKerEquivRange qS).trans
      ((MulEquiv.subgroupCongr hqS_range_top).trans Subgroup.topEquiv)
  let eToQuot : ↥(S : Subgroup G) ≃* G ⧸ M :=
    eKer.symm.trans (eImage.trans ((MulEquiv.subgroupCongr hSmap_top).trans Subgroup.topEquiv))
  exact eToQuot.symm


@[expose] public def CFSG.HasOrderedCharacteristicSylowSeriesWithPrimeDivisors
    (G : Type*) [Group G] [Finite G] : Prop :=
  ∃ (n : ℕ) (series : Fin (n + 1) → Subgroup G) (primes : Fin n → ℕ),
    series 0 = ⊤ ∧ series (Fin.last n) = ⊥ ∧
    (∀ i, (series i).Characteristic) ∧
    StrictMono primes ∧
    (∀ i : Fin n,
      series i.succ ≤ series i.castSucc ∧
        ∃ (_ : Fact (primes i).Prime) (P : Sylow (primes i) G)
          (_ : ((series i.succ).subgroupOf (series i.castSucc)).Normal),
          Nonempty
            ((series i.castSucc ⧸ (series i.succ).subgroupOf (series i.castSucc)) ≃*
              ↥(P : Subgroup G))) ∧
    (∀ i : Fin n, primes i ∣ Nat.card G)

private theorem CFSG.hasOrderedCharacteristicSylowSeriesWithPrimeDivisors_of_subsingleton
    {G : Type*} [Group G] [Finite G] [Subsingleton G] :
    HasOrderedCharacteristicSylowSeriesWithPrimeDivisors G := by
  classical
  refine ⟨0, (fun _ : Fin 1 => (⊤ : Subgroup G)), (fun i : Fin 0 => Fin.elim0 i),
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · intro _hx
      have hx : x = 1 := Subsingleton.elim x 1
      simp [hx]
    · intro hx
      simp
  · intro i
    exact inferInstance
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

private theorem CFSG.hasOrderedCharacteristicSylowSeriesWithPrimeDivisors_of_isPGroup
    {G : Type*} [Group G] [Finite G] [Nontrivial G] {p : ℕ} [Fact p.Prime]
    (hGp : IsPGroup p G) :
    HasOrderedCharacteristicSylowSeriesWithPrimeDivisors G := by
  classical
  let series : Fin 2 → Subgroup G := Fin.cases (⊤ : Subgroup G) (fun _ : Fin 1 => ⊥)
  let primes : Fin 1 → ℕ := fun _ => p
  have hp_dvd : p ∣ Nat.card G := by
    rcases hGp.card_eq_or_dvd with hcard_one | hp_dvd
    · exact False.elim ((Nat.ne_of_gt (Finite.one_lt_card (α := G))) hcard_one)
    · exact hp_dvd
  refine ⟨1, series, primes, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro i
    fin_cases i
    · change (⊤ : Subgroup G).Characteristic
      infer_instance
    · change (⊥ : Subgroup G).Characteristic
      infer_instance
  · intro i j hij
    fin_cases i
    fin_cases j
    simp at hij
  · intro i
    fin_cases i
    refine ⟨?_, ?_⟩
    · simp [series]
    · have htop_p : IsPGroup p (⊤ : Subgroup G) := hGp.to_subgroup (⊤ : Subgroup G)
      let S : Sylow p G :=
        IsPGroup.toSylow (G := G) (p := p) htop_p (by
          simpa using (Fact.out : Nat.Prime p).not_dvd_one)
      have hS_top : (S : Subgroup G) = ⊤ := by
        simp [S, IsPGroup.toSylow_coe]
      have hnorm_bot : ((⊥ : Subgroup G).subgroupOf (⊤ : Subgroup G)).Normal := by
        rw [Subgroup.bot_subgroupOf]
        infer_instance
      refine ⟨inferInstance, S, ?_, ⟨?_⟩⟩
      · change ((⊥ : Subgroup G).subgroupOf (⊤ : Subgroup G)).Normal
        exact hnorm_bot
      let eTopQuot :
          ((⊤ : Subgroup G) ⧸ (⊥ : Subgroup G).subgroupOf (⊤ : Subgroup G)) ≃*
            G ⧸ (⊥ : Subgroup G) :=
        topQuotientSubgroupOfEquivQuotient (G := G) (⊥ : Subgroup G)
      change ((⊤ : Subgroup G) ⧸ (⊥ : Subgroup G).subgroupOf (⊤ : Subgroup G)) ≃*
        ↥(S : Subgroup G)
      exact eTopQuot.trans
        (QuotientGroup.quotientBot.trans
          (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hS_top.symm)))
  · intro i
    fin_cases i
    exact hp_dvd

private theorem CFSG.quotient_map_subtype_factor_equiv
    {G : Type*} [Group G] (K : Subgroup G) {L M : Subgroup K} (hLM : L ≤ M)
    [hN : (L.subgroupOf M).Normal] :
    ∃ (_ : ((L.map K.subtype).subgroupOf (M.map K.subtype)).Normal),
      Nonempty
        ((M.map K.subtype ⧸ (L.map K.subtype).subgroupOf (M.map K.subtype)) ≃*
          (M ⧸ L.subgroupOf M)) := by
  classical
  let Mmap : Subgroup G := M.map K.subtype
  let Lmap : Subgroup G := L.map K.subtype
  let eM : M ≃* Mmap := Subgroup.equivMapOfInjective M K.subtype K.subtype_injective
  have hmap_eq : (L.subgroupOf M).map eM.toMonoidHom = Lmap.subgroupOf Mmap := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨l, hl, rfl⟩
      change (eM l : G) ∈ Lmap
      exact Subgroup.mem_map_of_mem K.subtype (by simpa [Subgroup.mem_subgroupOf] using hl)
    · intro hx
      rcases x with ⟨x, _hxMmap⟩
      change x ∈ Lmap at hx
      rcases Subgroup.mem_map.mp hx with ⟨l, hlL, rfl⟩
      refine ⟨⟨l, hLM hlL⟩, ?_, ?_⟩
      · simpa [Subgroup.mem_subgroupOf] using hlL
      · rfl
  have : (Lmap.subgroupOf Mmap).Normal := by
    rw [← hmap_eq]
    exact Subgroup.Normal.map hN eM.toMonoidHom eM.surjective
  refine ⟨by simpa [Lmap, Mmap], ⟨?_⟩⟩
  exact (QuotientGroup.congr (L.subgroupOf M) (Lmap.subgroupOf Mmap) eM hmap_eq).symm

private theorem CFSG.sylow_equiv_of_normal_quotient_pgroup_ne
    {G : Type*} [Group G] [Finite G] (K : Subgroup G) [K.Normal]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hquotp : IsPGroup p (G ⧸ K)) (hqp : q ≠ p) (P : Sylow q K) :
    ∃ Q : Sylow q G, Nonempty (↥(P : Subgroup K) ≃* ↥(Q : Subgroup G)) := by
  classical
  obtain ⟨Q, hQcomap⟩ := P.exists_comap_subtype_eq
  let π : G →* G ⧸ K := QuotientGroup.mk' K
  let Qmap : Subgroup (G ⧸ K) := (Q : Subgroup G).map π
  have hQmap_q : IsPGroup q Qmap := by
    simpa [Qmap] using IsPGroup.map (p := q) (H := (Q : Subgroup G)) Q.isPGroup' π
  have hQmap_p : IsPGroup p Qmap := hquotp.to_subgroup Qmap
  have hQmap_bot : Qmap = ⊥ := by
    have hcard_one : Nat.card Qmap = 1 := by
      rcases hQmap_q.card_eq_or_dvd with h1 | hqdiv
      · exact h1
      · exfalso
        obtain ⟨n, hn⟩ := hQmap_p.exists_card_eq
        have hq_dvd_pow : q ∣ p ^ n := by simpa [hn] using hqdiv
        have hq_eq_p : q = p :=
          Nat.prime_eq_prime_of_dvd_pow (Fact.out : Nat.Prime q) (Fact.out : Nat.Prime p)
            hq_dvd_pow
        exact hqp hq_eq_p
    exact Subgroup.eq_bot_of_card_eq (H := Qmap) hcard_one
  have hQ_le_K : (Q : Subgroup G) ≤ K := by
    have hleker : (Q : Subgroup G) ≤ π.ker :=
      (Subgroup.map_eq_bot_iff (H := (Q : Subgroup G)) (f := π)).1 hQmap_bot
    simpa [π, QuotientGroup.ker_mk'] using hleker
  let Qsub : Sylow q K := Q.subtype hQ_le_K
  have hQsub_eq : Qsub = P := by
    apply Sylow.ext
    simpa [Qsub, Sylow.coe_subtype] using hQcomap
  have hQsub_coe : (Qsub : Subgroup K) = (Q : Subgroup G).subgroupOf K := by
    exact Sylow.coe_subtype (P := Q) hQ_le_K
  let eQsub : ↥(Qsub : Subgroup K) ≃* ↥((Q : Subgroup G).subgroupOf K) :=
    MulEquiv.subgroupCongr hQsub_coe
  let eQbase : ↥((Q : Subgroup G).subgroupOf K) ≃* ↥(Q : Subgroup G) :=
    Subgroup.subgroupOfEquivOfLe (G := G) (H := (Q : Subgroup G)) (K := K) hQ_le_K
  let eQ : ↥(Qsub : Subgroup K) ≃* ↥(Q : Subgroup G) := eQsub.trans eQbase
  let eP : ↥(P : Subgroup K) ≃* ↥(Qsub : Subgroup K) :=
    MulEquiv.subgroupCongr (by
      simpa using congrArg (fun S : Sylow q K => (S : Subgroup K)) hQsub_eq.symm)
  exact ⟨Q, ⟨eP.trans eQ⟩⟩

private theorem CFSG.sylow_map_subtype_of_normal_quotient_pgroup_ne
    {G : Type*} [Group G] [Finite G] (K : Subgroup G) [K.Normal]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hquotp : IsPGroup p (G ⧸ K)) (hqp : q ≠ p) (P : Sylow q K) :
    ∃ Q : Sylow q G, (Q : Subgroup G) = (P : Subgroup K).map K.subtype := by
  classical
  obtain ⟨Q, hQcomap⟩ := P.exists_comap_subtype_eq
  let π : G →* G ⧸ K := QuotientGroup.mk' K
  let Qmap : Subgroup (G ⧸ K) := (Q : Subgroup G).map π
  have hQmap_q : IsPGroup q Qmap := by
    simpa [Qmap] using IsPGroup.map (p := q) (H := (Q : Subgroup G)) Q.isPGroup' π
  have hQmap_p : IsPGroup p Qmap := hquotp.to_subgroup Qmap
  have hQmap_bot : Qmap = ⊥ := by
    have hcard_one : Nat.card Qmap = 1 := by
      rcases hQmap_q.card_eq_or_dvd with h1 | hqdiv
      · exact h1
      · exfalso
        obtain ⟨n, hn⟩ := hQmap_p.exists_card_eq
        have hq_dvd_pow : q ∣ p ^ n := by simpa [hn] using hqdiv
        have hq_eq_p : q = p :=
          Nat.prime_eq_prime_of_dvd_pow (Fact.out : Nat.Prime q) (Fact.out : Nat.Prime p)
            hq_dvd_pow
        exact hqp hq_eq_p
    exact Subgroup.eq_bot_of_card_eq (H := Qmap) hcard_one
  have hQ_le_K : (Q : Subgroup G) ≤ K := by
    have hleker : (Q : Subgroup G) ≤ π.ker :=
      (Subgroup.map_eq_bot_iff (H := (Q : Subgroup G)) (f := π)).1 hQmap_bot
    simpa [π, QuotientGroup.ker_mk'] using hleker
  let Qsub : Sylow q K := Q.subtype hQ_le_K
  have hQsub_eq : Qsub = P := by
    apply Sylow.ext
    simpa [Qsub, Sylow.coe_subtype] using hQcomap
  refine ⟨Q, ?_⟩
  ext x
  constructor
  · intro hxQ
    have hxQsub : (⟨x, hQ_le_K hxQ⟩ : K) ∈ (Qsub : Subgroup K) := by
      change x ∈ (Q : Subgroup G)
      exact hxQ
    have hxP : (⟨x, hQ_le_K hxQ⟩ : K) ∈ (P : Subgroup K) := by
      simpa [hQsub_eq] using hxQsub
    exact ⟨⟨x, hQ_le_K hxQ⟩, hxP, rfl⟩
  · intro hxPmap
    rcases Subgroup.mem_map.mp hxPmap with ⟨xK, hxP, rfl⟩
    have hxQsub : xK ∈ (Qsub : Subgroup K) := by
      simpa [hQsub_eq] using hxP
    change (xK : G) ∈ (Q : Subgroup G)
    exact hxQsub

private theorem CFSG.minFac_natCard_isSmallestPrimeDivisor
    (G : Type*) [Group G] [Finite G] [Nontrivial G] :
    IsSmallestPrimeDivisor (Nat.minFac (Nat.card G)) (Nat.card G) := by
  have hcard_ne_one : Nat.card G ≠ 1 := Nat.ne_of_gt (Finite.one_lt_card (α := G))
  refine ⟨Nat.minFac_prime hcard_ne_one, Nat.minFac_dvd (Nat.card G), ?_⟩
  intro q hq hq_dvd
  exact Nat.minFac_le_of_dvd hq.two_le hq_dvd

private theorem CFSG.hasNormalPComplement_minFac_of_groupRank_le_two
    {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (hG : groupRank G ≤ 2) :
    HasNormalPComplement (Nat.minFac (Nat.card G)) G := by
  classical
  let p := Nat.minFac (Nat.card G)
  have hp_small : IsSmallestPrimeDivisor p (Nat.card G) :=
    minFac_natCard_isSmallestPrimeDivisor G
  have : Fact p.Prime := ⟨hp_small.1⟩
  have hp_mem : p ∣ Nat.card G := hp_small.2.1
  have hprank : primeRank p G ≤ 2 :=
    (primeRank_le_groupRank (R := G) hp_small.1).trans hG
  exact theorem_4_18_b (G := G) (p := p) hsolv hodd hp_mem hprank (Or.inr hp_small)

private theorem CFSG.isPGroup_quotient_pPrimeCore_of_commutative
    {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hcomm : IsMulCommutative Q) :
    IsPGroup p (Q ⧸ pPrimeCore p Q) := by
  classical
  let M : Subgroup Q := pPrimeCore p Q
  let Qbar := Q ⧸ M
  have hcore_bot : pPrimeCore p Qbar = ⊥ := by
    simpa [Qbar, M] using pPrimeCore_quotient_pPrimeCore_eq_bot (G := Q) (p := p)
  have : IsMulCommutative Q := hcomm
  let : CommGroup Q := IsMulCommutative.instCommGroup
  have : CommGroup Qbar := by infer_instance
  have hnil : Group.IsNilpotent (⊤ : Subgroup Qbar) := by infer_instance
  have htop : IsPGroup p (⊤ : Subgroup Qbar) :=
    isPGroup_of_nilpotent_normal (G := Qbar) (p := p) (⊤ : Subgroup Qbar)
      inferInstance hnil hcore_bot
  exact htop.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup Qbar) ≃* Qbar)

private theorem CFSG.pSubgroup_le_ker_of_le_comap_pPrimeCore
    {G Q : Type*} [Group G] [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (q : G →* Q) {P : Subgroup G} (hPp : IsPGroup p P)
    (hP_le : P ≤ (pPrimeCore p Q).comap q) :
    P ≤ q.ker := by
  classical
  have hPmap_p : IsPGroup p (P.map q) :=
    IsPGroup.map (p := p) (H := P) hPp q
  have hPmap_le_core : P.map q ≤ pPrimeCore p Q := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact hP_le hx
  have hPmap_inf :
      (P.map q) ⊓ pPrimeCore p Q = ⊥ :=
    inf_eq_bot_of_pSubgroup_and_pPrime_card (G := Q) (p := p)
      hPmap_p (pPrimeCore_coprime_card (G := Q) (p := p))
  have hPmap_bot : P.map q = ⊥ := by
    have hinf : (P.map q) ⊓ pPrimeCore p Q = P.map q := inf_eq_left.mpr hPmap_le_core
    rw [← hinf, hPmap_inf]
  intro x hx
  have hxmap : q x ∈ P.map q := Subgroup.mem_map_of_mem q hx
  have hxbot : q x ∈ (⊥ : Subgroup Q) := by
    simpa [hPmap_bot] using hxmap
  simpa [MonoidHom.mem_ker] using hxbot

private theorem CFSG.primeRank_le_of_pSubgroups_map_le
    {R : Type*} [Group R] [Finite R] (H K : Subgroup R) (q : ℕ)
    (hmap : ∀ A : Subgroup H, IsPGroup q A → (A.map H.subtype) ≤ K) :
    primeRank q H ≤ primeRank q K := by
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup H, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card H, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact le_trans hnA <|
      le_trans (generatorRank_le_card (G := A)) (Subgroup.card_le_card_group A)
  by_cases hT : T.Nonempty
  · have hsSup_mem : sSup T ∈ T := Nat.sSup_mem hT hTbdd
    rcases hsSup_mem with ⟨A, hAq, hAcomm, hsSup_le⟩
    let A' : Subgroup R := A.map H.subtype
    have hA'_le_K : A' ≤ K := hmap A hAq
    let B : Subgroup K := A'.subgroupOf K
    let eMap : A ≃* A' := Subgroup.equivMapOfInjective A H.subtype H.subtype_injective
    let eSub : B ≃* A' := Subgroup.subgroupOfEquivOfLe (G := R) (H := A') (K := K) hA'_le_K
    let eAB : A ≃* B := eMap.trans eSub.symm
    have hBq : IsPGroup q B := hAq.of_equiv eAB
    have hBcomm : IsMulCommutative B := by
      let : IsMulCommutative A := hAcomm
      have : IsMulCommutative A' := by infer_instance
      refine ⟨⟨fun x y => ?_⟩⟩
      apply eSub.injective
      simpa only [map_mul] using
        (IsMulCommutative.is_comm.comm (eSub x) (eSub y))
    have hgen_le : generatorRank A ≤ generatorRank B :=
      generatorRank_le_of_equiv (G := B) (H := A) eAB.symm
    have hmem : generatorRank A ∈
        {n : ℕ | ∃ B : Subgroup K, IsPGroup q B ∧ IsMulCommutative B ∧ n ≤ generatorRank B} :=
      ⟨B, hBq, hBcomm, hgen_le⟩
    have hprimeRank : generatorRank A ≤ primeRank q K := by
      simpa [primeRank] using le_csSup
        (show BddAbove {n : ℕ | ∃ B : Subgroup K, IsPGroup q B ∧ IsMulCommutative B ∧
            n ≤ generatorRank B} from
          ⟨Nat.card K, by
            intro n hn
            rcases hn with ⟨B, _hBq, _hBcomm, hnB⟩
            exact le_trans hnB (le_trans (generatorRank_le_card (G := B))
              (Subgroup.card_le_card_group B))⟩)
        hmem
    rw [primeRank]
    exact le_trans hsSup_le hprimeRank
  · have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have hSet :
        {n : ℕ | ∃ A : Subgroup H, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A} = ∅ := by
      simpa [T] using hTempty
    rw [primeRank, hSet]
    simp

private theorem CFSG.primeRank_comap_pPrimeCore_le_ker
    {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (q : G →* Q) :
    primeRank p ((pPrimeCore p Q).comap q) ≤ primeRank p q.ker := by
  classical
  let H : Subgroup G := (pPrimeCore p Q).comap q
  refine primeRank_le_of_pSubgroups_map_le (H := H) (K := q.ker) p ?_
  intro A hAq
  have hAmap_p : IsPGroup p (A.map H.subtype) :=
    IsPGroup.map (p := p) (H := A) hAq H.subtype
  have hAmap_le_H : A.map H.subtype ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    exact a.property
  exact pSubgroup_le_ker_of_le_comap_pPrimeCore (G := G) (Q := Q) (p := p)
    q hAmap_p (by simpa [H] using hAmap_le_H)

private theorem CFSG.isPGroup_quotient_comap_pPrimeCore_of_commutative
    {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (q : G →* Q) (hq : Function.Surjective q) (hcomm : IsMulCommutative Q) :
    IsPGroup p (G ⧸ (pPrimeCore p Q).comap q) := by
  classical
  let K : Subgroup Q := pPrimeCore p Q
  let ψ : G →* Q ⧸ K := (QuotientGroup.mk' K).comp q
  have hker : ψ.ker = K.comap q := by
    ext x
    change (QuotientGroup.mk' K) (q x) = 1 ↔ q x ∈ K
    simp [K]
  have hψsurj : Function.Surjective ψ := by
    intro y
    refine QuotientGroup.induction_on y ?_
    intro z
    rcases hq z with ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hψrange : ψ.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    exact hψsurj
  let eKer : G ⧸ K.comap q ≃* G ⧸ ψ.ker :=
    QuotientGroup.quotientMulEquivOfEq hker.symm
  let eRange : G ⧸ ψ.ker ≃* ψ.range := QuotientGroup.quotientKerEquivRange ψ
  let eTop : ψ.range ≃* Q ⧸ K :=
    (MulEquiv.subgroupCongr hψrange).trans Subgroup.topEquiv
  let e : G ⧸ K.comap q ≃* Q ⧸ K := eKer.trans (eRange.trans eTop)
  have hQp : IsPGroup p (Q ⧸ K) := by
    simpa [K] using isPGroup_quotient_pPrimeCore_of_commutative (Q := Q) (p := p) hcomm
  exact hQp.of_equiv e.symm

private theorem CFSG.theorem_4_20_intermediate_characteristic
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    ((pPrimeCore p (G ⧸ fittingSubgroup G)).comap
        (QuotientGroup.mk' (fittingSubgroup G))).Characteristic := by
  exact Subgroup.Characteristic.comap_quotient_mk
    (H := fittingSubgroup G) (K := pPrimeCore p (G ⧸ fittingSubgroup G))
    (pPrimeCore_characteristic (p := p) (G := G ⧸ fittingSubgroup G))

private theorem CFSG.theorem_4_20_intermediate_quotient_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcomm : IsMulCommutative (G ⧸ fittingSubgroup G)) :
    IsPGroup p
      (G ⧸ (pPrimeCore p (G ⧸ fittingSubgroup G)).comap
        (QuotientGroup.mk' (fittingSubgroup G))) := by
  simpa using
    isPGroup_quotient_comap_pPrimeCore_of_commutative
      (G := G) (Q := G ⧸ fittingSubgroup G) (p := p)
      (QuotientGroup.mk' (fittingSubgroup G))
      (QuotientGroup.mk'_surjective (fittingSubgroup G)) hcomm

private theorem CFSG.theorem_4_20_intermediate_primeRank_le_two
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hF : groupRank (fittingSubgroup G) ≤ 2) :
    primeRank p
      ((pPrimeCore p (G ⧸ fittingSubgroup G)).comap
        (QuotientGroup.mk' (fittingSubgroup G))) ≤ 2 := by
  let F : Subgroup G := fittingSubgroup G
  let q : G →* G ⧸ F := QuotientGroup.mk' F
  have hle_ker :
      primeRank p ((pPrimeCore p (G ⧸ F)).comap q) ≤ primeRank p q.ker :=
    primeRank_comap_pPrimeCore_le_ker (G := G) (Q := G ⧸ F) (p := p) q
  have hker_le_two : primeRank p q.ker ≤ 2 := by
    have hF_le_two : primeRank p F ≤ 2 :=
      (primeRank_le_groupRank (R := F) (q := p) Fact.out).trans hF
    have hker_eq : q.ker = F := by
      simp [q]
    rw [hker_eq]
    exact hF_le_two
  exact hle_ker.trans hker_le_two

private theorem CFSG.isPGroup_quotient_map_subtype_of_extension
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) [H.Normal] (K : Subgroup H) [K.Characteristic]
    (hHKp : IsPGroup p (H ⧸ K)) (hGHp : IsPGroup p (G ⧸ H)) :
    IsPGroup p (G ⧸ K.map H.subtype) := by
  classical
  let N : Subgroup G := K.map H.subtype
  have hN_le_H : N ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨k, _hk, rfl⟩
    exact k.property
  have : N.Normal := by
    dsimp [N]
    infer_instance
  let qN : G →* G ⧸ N := QuotientGroup.mk' N
  let Hbar : Subgroup (G ⧸ N) := H.map qN
  have : Hbar.Normal := by
    exact Subgroup.Normal.map (inferInstance : H.Normal) qN (QuotientGroup.mk'_surjective N)
  have hHbar_p : IsPGroup p Hbar := by
    let eHN : H ⧸ N.subgroupOf H ≃* H ⧸ K :=
      QuotientGroup.quotientMulEquivOfEq (by
        simpa [N] using (subgroupOf_map_subtype_eq (K := H) K))
    let eRange : H ⧸ N.subgroupOf H ≃* Hbar := quotientSubgroupRangeEquiv H N
    exact hHKp.of_equiv (eHN.symm.trans eRange)
  have hquot_p : IsPGroup p ((G ⧸ N) ⧸ Hbar) := by
    let e : (G ⧸ N) ⧸ Hbar ≃* G ⧸ H :=
      QuotientGroup.quotientQuotientEquivQuotient (N := N) (M := H) hN_le_H
    exact hGHp.of_equiv e.symm
  obtain ⟨a, ha⟩ := hquot_p.exists_card_eq
  obtain ⟨b, hb⟩ := hHbar_p.exists_card_eq
  have hcard :
      Nat.card (G ⧸ N) = Nat.card ((G ⧸ N) ⧸ Hbar) * Nat.card Hbar := by
    simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := Hbar))
  refine IsPGroup.of_card (p := p) (G := G ⧸ N) (n := a + b) ?_
  rw [hcard, ha, hb, Nat.pow_add]

private theorem CFSG.hasNormalPComplement_of_characteristic_subgroup_and_pgroup_quotient
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) [H.Normal] (hGHp : IsPGroup p (G ⧸ H))
    (hHcomp : HasNormalPComplement p H) :
    HasNormalPComplement p G := by
  classical
  let K : Subgroup H := pPrimeCore p H
  let N : Subgroup G := K.map H.subtype
  have : K.Characteristic := pPrimeCore_characteristic (p := p) (G := H)
  have hNnorm : N.Normal := by
    dsimp [N, K]
    infer_instance
  have hNcop : Nat.Coprime p (Nat.card N) := by
    have hcard : Nat.card N = Nat.card K := by
      simpa [N] using
        (Subgroup.card_map_of_injective (K := K) (f := H.subtype) H.subtype_injective)
    rw [hcard]
    exact pPrimeCore_coprime_card (G := H) (p := p)
  have hHKp : IsPGroup p (H ⧸ K) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := p) (H := H) hHcomp
  have hGNp : IsPGroup p (G ⧸ N) :=
    isPGroup_quotient_map_subtype_of_extension (G := G) (p := p)
      H K hHKp hGHp
  exact ⟨N, hNnorm, hNcop, hGNp⟩

private theorem CFSG.hasNormalPComplement_minFac_of_fitting_rank_le_two
    {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (hF : groupRank (fittingSubgroup G) ≤ 2) :
    HasNormalPComplement (Nat.minFac (Nat.card G)) G := by
  classical
  let p := Nat.minFac (Nat.card G)
  have hp_small : IsSmallestPrimeDivisor p (Nat.card G) :=
    minFac_natCard_isSmallestPrimeDivisor G
  have : Fact p.Prime := ⟨hp_small.1⟩
  let F : Subgroup G := fittingSubgroup G
  let q : G →* G ⧸ F := QuotientGroup.mk' F
  let H : Subgroup G := (pPrimeCore p (G ⧸ F)).comap q
  have hHchar : H.Characteristic := by
    simpa [H, q, F] using theorem_4_20_intermediate_characteristic (G := G) (p := p)
  have : H.Normal := by
    let : H.Characteristic := hHchar
    infer_instance
  have hder_nil : Group.IsNilpotent (derivedSubgroup G) :=
    theorem_4_20_a (G := G) hsolv hodd (Or.inr hF)
  have hD_le_F : derivedSubgroup G ≤ F := by
    exact le_sSup ⟨inferInstance, hder_nil⟩
  have hQcomm : IsMulCommutative (G ⧸ F) := by
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := F)).2 hD_le_F
  have hGHp : IsPGroup p (G ⧸ H) := by
    simpa [H, q, F] using
      theorem_4_20_intermediate_quotient_isPGroup (G := G) (p := p) hQcomm
  by_cases hpH : p ∣ Nat.card H
  · have : Group.IsSolvable G := hsolv
    have hHsolv : Group.IsSolvable H := by infer_instance
    have hHodd : Odd (Nat.card H) :=
      hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card H)
    have hHrank : primeRank p H ≤ 2 := by
      simpa [H, q, F] using
        theorem_4_20_intermediate_primeRank_le_two (G := G) (p := p) hF
    have hp_small_H : IsSmallestPrimeDivisor p (Nat.card H) := by
      refine ⟨hp_small.1, hpH, ?_⟩
      intro r hr hrdvdH
      exact hp_small.2.2 r hr (hrdvdH.trans (Subgroup.card_subgroup_dvd_card H))
    have hHcomp : HasNormalPComplement p H :=
      theorem_4_18_b (G := H) (p := p) hHsolv hHodd hpH hHrank (Or.inr hp_small_H)
    exact hasNormalPComplement_of_characteristic_subgroup_and_pgroup_quotient
      (G := G) (p := p) H hGHp hHcomp
  · have hHcop : Nat.Coprime p (Nat.card H) :=
      (hp_small.1.coprime_iff_not_dvd).2 hpH
    exact ⟨H, inferInstance, hHcop, hGHp⟩

public theorem CFSG.hasNormalPComplement_minFac_of_rank_hyp
    {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (hrank : groupRank G ≤ 2 ∨ groupRank (fittingSubgroup G) ≤ 2) :
    HasNormalPComplement (Nat.minFac (Nat.card G)) G := by
  rcases hrank with hG | hF
  · exact hasNormalPComplement_minFac_of_groupRank_le_two (G := G) hsolv hodd hG
  · exact hasNormalPComplement_minFac_of_fitting_rank_le_two (G := G) hsolv hodd hF

private theorem CFSG.isHallSubgroup_top_of_smallestPrime_ge
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp_small : IsSmallestPrimeDivisor p (Nat.card G)) :
    IsHallSubgroup ({q : Nat.Primes | p ≤ q.val}) (⊤ : Subgroup G) := by
  refine isHallSubgroup_of (G := G) ({q : Nat.Primes | p ≤ q.val}) (⊤ : Subgroup G)
    (hcard := ?_) (hindex := ?_)
  · intro q hq_dvd
    exact hp_small.2.2 q.val q.property (by simpa using hq_dvd)
  · intro q _hq_mem hq_idx
    have hq_one : q.val ∣ 1 := by simpa using hq_idx
    exact q.property.not_dvd_one hq_one

private theorem CFSG.isHallSubgroup_pPrimeCore_of_smallestPrime_gt
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp_small : IsSmallestPrimeDivisor p (Nat.card G))
    (hcomp : HasNormalPComplement p G) :
    IsHallSubgroup ({q : Nat.Primes | p < q.val}) (pPrimeCore p G) := by
  classical
  let K : Subgroup G := pPrimeCore p G
  refine isHallSubgroup_of (G := G) ({q : Nat.Primes | p < q.val}) K
    (hcard := ?_) (hindex := ?_)
  · intro q hq_dvd
    have hq_dvd_G : q.val ∣ Nat.card G :=
      hq_dvd.trans (Subgroup.card_subgroup_dvd_card K)
    have hp_le_q : p ≤ q.val := hp_small.2.2 q.val q.property hq_dvd_G
    have hp_ne_q : p ≠ q.val := by
      intro hpq
      have hp_dvd_K : p ∣ Nat.card K := by simpa [hpq] using hq_dvd
      exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd).1
        (by simpa [K] using pPrimeCore_coprime_card (G := G) (p := p)) hp_dvd_K
    exact lt_of_le_of_ne hp_le_q hp_ne_q
  · intro q hq_mem hq_idx
    have hquot_p : IsPGroup p (G ⧸ K) := by
      simpa [K] using
        isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := p) (H := G) hcomp
    obtain ⟨n, hn⟩ := hquot_p.exists_card_eq
    have hq_quot : q.val ∣ Nat.card (G ⧸ K) := by
      simpa [K, Subgroup.index_eq_card] using hq_idx
    have hq_pow : q.val ∣ p ^ n := by simpa [hn] using hq_quot
    have hq_eq_p : q.val = p :=
      Nat.prime_eq_prime_of_dvd_pow q.property (Fact.out : Nat.Prime p) hq_pow
    exact (ne_of_gt hq_mem) hq_eq_p

private theorem CFSG.isHallSubgroup_map_subtype_of_isHallSubgroup_of_subset
    {G : Type*} [Group G] [Finite G] {π ρ : Set Nat.Primes}
    {K : Subgroup G} {H : Subgroup K}
    (hK : IsHallSubgroup ρ K) (hH : IsHallSubgroup π H) (hπρ : π ⊆ ρ) :
    IsHallSubgroup π (H.map K.subtype) := by
  refine isHallSubgroup_of (G := G) π (H.map K.subtype)
    (hcard := ?_) (hindex := ?_)
  · intro q hq_dvd
    have hcard_map : Nat.card (H.map K.subtype) = Nat.card H := by
      simpa using
        (Subgroup.card_map_of_injective (K := H) (f := K.subtype) K.subtype_injective)
    have hq_dvd_H : q.val ∣ Nat.card H := by
      rw [hcard_map] at hq_dvd
      exact hq_dvd
    exact hH.p_in_pi_of_p_dvd_card q hq_dvd_H
  · intro q hq_mem hq_idx
    have hidx_map :
        (H.map K.subtype).index = H.index * K.index :=
      Subgroup.index_map_subtype (K := H)
    have hq_mul : q.val ∣ H.index * K.index := by simpa [hidx_map] using hq_idx
    rcases q.property.dvd_mul.mp hq_mul with hq_Hidx | hq_Kidx
    · exact (hH.p_in_pi_of_p_dvd_index q hq_Hidx) hq_mem
    · exact (hK.p_in_pi_of_p_dvd_index q hq_Kidx) (hπρ hq_mem)

public theorem CFSG.theorem_4_20_c_characteristic_hall_ge_gt
    {G : Type u} [Group G] [Finite G]
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (hrank : groupRank G ≤ 2 ∨ groupRank (fittingSubgroup G) ≤ 2)
    {p : Nat.Primes} (hpG : p.val ∣ Nat.card G) :
    ∃ L K : Subgroup G,
      L.Characteristic ∧ K.Characteristic ∧
        IsHallSubgroup ({q : Nat.Primes | p.val ≤ q.val}) L ∧
          IsHallSubgroup ({q : Nat.Primes | p.val < q.val}) K ∧ K ≤ L := by
  classical
  let P : ℕ → Prop := fun m =>
    ∀ (H : Type u) [Group H] [Finite H], Nat.card H = m →
      Group.IsSolvable H → Odd (Nat.card H) →
      (groupRank H ≤ 2 ∨ groupRank (fittingSubgroup H) ≤ 2) →
      ∀ {p : Nat.Primes}, p.val ∣ Nat.card H →
        ∃ L K : Subgroup H,
          L.Characteristic ∧ K.Characteristic ∧
            IsHallSubgroup ({q : Nat.Primes | p.val ≤ q.val}) L ∧
              IsHallSubgroup ({q : Nat.Primes | p.val < q.val}) K ∧ K ≤ L
  have hP : ∀ m, (∀ k < m, P k) → P m := by
    intro m ih H _ _ hcard hHsolv hHodd hHrank p hpH
    have hHnot_subsingleton : ¬ Subsingleton H := by
      intro hsub
      let : Subsingleton H := hsub
      have hcard_one : Nat.card H = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
      exact p.property.not_dvd_one (by simpa [hcard_one] using hpH)
    have : Nontrivial H := not_subsingleton_iff_nontrivial.mp hHnot_subsingleton
    let r := Nat.minFac (Nat.card H)
    have hr_small : IsSmallestPrimeDivisor r (Nat.card H) :=
      minFac_natCard_isSmallestPrimeDivisor H
    have : Fact r.Prime := ⟨hr_small.1⟩
    have hcomp : HasNormalPComplement r H := by
      simpa [r] using hasNormalPComplement_minFac_of_rank_hyp
        (G := H) hHsolv hHodd hHrank
    by_cases hpr : p.val = r
    · refine ⟨⊤, pPrimeCore r H, inferInstance, ?_, ?_, ?_, le_top⟩
      · simpa [hpr] using pPrimeCore_characteristic (p := r) (G := H)
      · simpa [hpr] using isHallSubgroup_top_of_smallestPrime_ge (G := H) hr_small
      · simpa [hpr] using
          isHallSubgroup_pPrimeCore_of_smallestPrime_gt (G := H) hr_small hcomp
    · have hr_le_p : r ≤ p.val := hr_small.2.2 p.val p.property hpH
      have hr_lt_p : r < p.val := lt_of_le_of_ne hr_le_p (by
        intro hrp
        exact hpr hrp.symm)
      let K₀ : Subgroup H := pPrimeCore r H
      have hK₀_char : K₀.Characteristic := by
        simpa [K₀] using pPrimeCore_characteristic (p := r) (G := H)
      have : K₀.Characteristic := hK₀_char
      have : K₀.Normal := by infer_instance
      have hquot_r : IsPGroup r (H ⧸ K₀) := by
        simpa [K₀] using
          isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := r) (H := H) hcomp
      obtain ⟨a, ha⟩ := hquot_r.exists_card_eq
      have hpK₀ : p.val ∣ Nat.card K₀ := by
        have hcard_mul :
            Nat.card H = Nat.card (H ⧸ K₀) * Nat.card K₀ := by
          simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := H) (s := K₀))
        have hp_prod : p.val ∣ Nat.card (H ⧸ K₀) * Nat.card K₀ := by
          simpa [hcard_mul] using hpH
        rcases p.property.dvd_mul.mp hp_prod with hp_quot | hp_K₀
        · have hp_pow : p.val ∣ r ^ a := by simpa [ha] using hp_quot
          have hp_eq_r : p.val = r :=
            Nat.prime_eq_prime_of_dvd_pow p.property (Fact.out : Nat.Prime r) hp_pow
          exact False.elim (hpr hp_eq_r)
        · exact hp_K₀
      have hr_not_dvd_K₀ : ¬ r ∣ Nat.card K₀ :=
        ((Fact.out : Nat.Prime r).coprime_iff_not_dvd).1
          (by simpa [K₀] using pPrimeCore_coprime_card (G := H) (p := r))
      have hK₀_ne_top : K₀ ≠ ⊤ := by
        intro htop
        have hcardK₀ : Nat.card K₀ = Nat.card H := by
          simp [htop]
        exact hr_not_dvd_K₀ (by simpa [hcardK₀] using hr_small.2.1)
      have hK₀ltH : Nat.card K₀ < Nat.card H := by
        have hle : Nat.card K₀ ≤ Nat.card H := Subgroup.card_le_card_group (H := K₀)
        have hne : Nat.card K₀ ≠ Nat.card H := by
          intro hEq
          exact hK₀_ne_top ((Subgroup.card_eq_iff_eq_top (H := K₀)).1 hEq)
        exact lt_of_le_of_ne hle hne
      have hK₀lt : Nat.card K₀ < m := by
        simpa [hcard] using hK₀ltH
      have hK₀solv : Group.IsSolvable K₀ := by
        let : Group.IsSolvable H := hHsolv
        infer_instance
      have hK₀odd : Odd (Nat.card K₀) :=
        hHodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K₀)
      have hK₀rank :
          groupRank K₀ ≤ 2 ∨ groupRank (fittingSubgroup K₀) ≤ 2 :=
        theorem_4_20_rank_hyp_of_normal_subgroup (G := H) K₀ hHrank
      obtain ⟨L₀, K₁, hL₀char, hK₁char, hL₀hall, hK₁hall, hK₁leL₀⟩ :=
        ih (Nat.card K₀) hK₀lt K₀ rfl hK₀solv hK₀odd hK₀rank hpK₀
      let L : Subgroup H := L₀.map K₀.subtype
      let K : Subgroup H := K₁.map K₀.subtype
      have hK₀hall : IsHallSubgroup ({q : Nat.Primes | r < q.val}) K₀ :=
        isHallSubgroup_pPrimeCore_of_smallestPrime_gt (G := H) hr_small hcomp
      have hge_subset : ({q : Nat.Primes | p.val ≤ q.val} : Set Nat.Primes) ⊆
          ({q : Nat.Primes | r < q.val} : Set Nat.Primes) := by
        intro q hq
        exact lt_of_lt_of_le hr_lt_p hq
      have hgt_subset : ({q : Nat.Primes | p.val < q.val} : Set Nat.Primes) ⊆
          ({q : Nat.Primes | r < q.val} : Set Nat.Primes) := by
        intro q hq
        exact lt_trans hr_lt_p hq
      have hLhall : IsHallSubgroup ({q : Nat.Primes | p.val ≤ q.val}) L :=
        isHallSubgroup_map_subtype_of_isHallSubgroup_of_subset
          (G := H) hK₀hall hL₀hall hge_subset
      have hKhall : IsHallSubgroup ({q : Nat.Primes | p.val < q.val}) K :=
        isHallSubgroup_map_subtype_of_isHallSubgroup_of_subset
          (G := H) hK₀hall hK₁hall hgt_subset
      have hLchar : L.Characteristic := by
        let : L₀.Characteristic := hL₀char
        simpa [L] using characteristic_map_subtype_of_characteristic (G := H) K₀ L₀
      have hKchar : K.Characteristic := by
        let : K₁.Characteristic := hK₁char
        simpa [K] using characteristic_map_subtype_of_characteristic (G := H) K₀ K₁
      refine ⟨L, K, hLchar, hKchar, hLhall, hKhall, ?_⟩
      exact Subgroup.map_mono hK₁leL₀
  have hmain : P (Nat.card G) := Nat.strong_induction_on (Nat.card G) hP
  exact hmain G rfl hsolv hodd hrank hpG

public theorem CFSG.theorem_4_20_c_with_prime_divisors
    {G : Type u} [Group G] [Finite G]
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (hrank : groupRank G ≤ 2 ∨ groupRank (fittingSubgroup G) ≤ 2) :
    HasOrderedCharacteristicSylowSeriesWithPrimeDivisors G := by
  classical
  let P : ℕ → Prop := fun m =>
    ∀ (H : Type u) [Group H] [Finite H], Nat.card H = m →
      Group.IsSolvable H → Odd (Nat.card H) →
      (groupRank H ≤ 2 ∨ groupRank (fittingSubgroup H) ≤ 2) →
      HasOrderedCharacteristicSylowSeriesWithPrimeDivisors H
  have hP : ∀ m, (∀ k < m, P k) → P m := by
    intro m ih H _ _ hcard hHsolv hHodd hHrank
    by_cases hHsub : Subsingleton H
    · let : Subsingleton H := hHsub
      exact hasOrderedCharacteristicSylowSeriesWithPrimeDivisors_of_subsingleton (G := H)
    · have : Nontrivial H := not_subsingleton_iff_nontrivial.mp hHsub
      let p := Nat.minFac (Nat.card H)
      have hp_small : IsSmallestPrimeDivisor p (Nat.card H) :=
        minFac_natCard_isSmallestPrimeDivisor H
      have : Fact p.Prime := ⟨hp_small.1⟩
      have hcomp : HasNormalPComplement p H := by
        simpa [p] using hasNormalPComplement_minFac_of_rank_hyp
          (G := H) hHsolv hHodd hHrank
      let K : Subgroup H := pPrimeCore p H
      have hKchar : K.Characteristic := by
        simpa [K] using pPrimeCore_characteristic (p := p) (G := H)
      let : K.Characteristic := hKchar
      have : K.Normal := by infer_instance
      have hquotp : IsPGroup p (H ⧸ K) := by
        simpa [K] using
          isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := p) (H := H) hcomp
      by_cases hKsub : Subsingleton K
      · let : Subsingleton K := hKsub
        have hK_bot : K = ⊥ := by
          apply eq_bot_iff.2
          intro x hx
          have hx_one : (⟨x, hx⟩ : K) = 1 := Subsingleton.elim _ _
          simpa using congrArg Subtype.val hx_one
        have hHp : IsPGroup p H := by
          have hquot_bot : IsPGroup p (H ⧸ (⊥ : Subgroup H)) := by
            exact hquotp.of_equiv (QuotientGroup.quotientMulEquivOfEq hK_bot)
          exact hquot_bot.of_equiv QuotientGroup.quotientBot
        exact hasOrderedCharacteristicSylowSeriesWithPrimeDivisors_of_isPGroup (G := H) hHp
      · have : Nontrivial K := not_subsingleton_iff_nontrivial.mp hKsub
        have hp_not_dvd_K : ¬ p ∣ Nat.card K :=
          (hp_small.1.coprime_iff_not_dvd).1
            (by simpa [K] using pPrimeCore_coprime_card (G := H) (p := p))
        have hK_ne_top : K ≠ ⊤ := by
          intro htop
          have hcardK : Nat.card K = Nat.card H := by
            simp [htop]
          have hp_dvd_K : p ∣ Nat.card K := by
            simpa [hcardK] using hp_small.2.1
          exact hp_not_dvd_K hp_dvd_K
        have hKltH : Nat.card K < Nat.card H := by
          have hle : Nat.card K ≤ Nat.card H := Subgroup.card_le_card_group (H := K)
          have hne : Nat.card K ≠ Nat.card H := by
            intro hEq
            exact hK_ne_top ((Subgroup.card_eq_iff_eq_top (H := K)).1 hEq)
          exact lt_of_le_of_ne hle hne
        have hKlt : Nat.card K < m := by
          simpa [hcard] using hKltH
        have hKsolv : Group.IsSolvable K := by
          let : Group.IsSolvable H := hHsolv
          infer_instance
        have hKodd : Odd (Nat.card K) :=
          hHodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)
        have hKrank :
            groupRank K ≤ 2 ∨ groupRank (fittingSubgroup K) ≤ 2 :=
          theorem_4_20_rank_hyp_of_normal_subgroup (G := H) K hHrank
        obtain ⟨n, seriesK, primesK, htopK, hbotK, hcharK, hmonoK, hstepK, hdivK⟩ :=
          ih (Nat.card K) hKlt K rfl hKsolv hKodd hKrank
        have hp_lt_primeK : ∀ j : Fin n, p < primesK j := by
          intro j
          rcases (hstepK j).2 with ⟨hqFact, _P, _hnorm, _hequiv⟩
          have hqprime : Nat.Prime (primesK j) := hqFact.out
          have hq_dvd_H : primesK j ∣ Nat.card H :=
            (hdivK j).trans (Subgroup.card_subgroup_dvd_card K)
          have hp_le_q : p ≤ primesK j := hp_small.2.2 (primesK j) hqprime hq_dvd_H
          have hp_ne_q : p ≠ primesK j := by
            intro hpq
            exact hp_not_dvd_K (by
              rw [hpq]
              exact hdivK j)
          exact lt_of_le_of_ne hp_le_q hp_ne_q
        let series : Fin ((n + 1) + 1) → Subgroup H :=
          Fin.cases (⊤ : Subgroup H) (fun j : Fin (n + 1) => (seriesK j).map K.subtype)
        let primes : Fin (n + 1) → ℕ := Fin.cases p primesK
        refine ⟨n + 1, series, primes, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · change (seriesK (Fin.last n)).map K.subtype = ⊥
          simp [hbotK]
        · intro i
          cases i using Fin.cases with
          | zero =>
              change (⊤ : Subgroup H).Characteristic
              infer_instance
          | succ j =>
              change ((seriesK j).map K.subtype).Characteristic
              let : (seriesK j).Characteristic := hcharK j
              exact characteristic_map_subtype_of_characteristic (G := H) K (seriesK j)
        · intro i j hij
          cases i using Fin.cases with
          | zero =>
              cases j using Fin.cases with
              | zero =>
                  exact False.elim ((lt_irrefl (0 : Fin (n + 1))) hij)
              | succ j =>
                  simpa [primes] using hp_lt_primeK j
          | succ i =>
              cases j using Fin.cases with
              | zero =>
                  have hval : (i.succ : Fin (n + 1)).val < (0 : Fin (n + 1)).val := hij
                  exact False.elim (Nat.not_lt_zero _ hval)
              | succ j =>
                  apply hmonoK
                  simpa using hij
        · intro i
          cases i using Fin.cases with
          | zero =>
              refine ⟨?_, ?_⟩
              · simp [series]
              · let S : Sylow p H := Classical.choice (Sylow.nonempty (p := p) (G := H))
                have hnormKtop : (K.subgroupOf (⊤ : Subgroup H)).Normal := by
                  infer_instance
                have htop_map : (⊤ : Subgroup K).map K.subtype = K := by
                  simpa [MonoidHom.range_eq_map] using (K.range_subtype : K.subtype.range = K)
                have hfirst :
                    series (1 : Fin ((n + 1) + 1)) = K := by
                  change (seriesK 0).map K.subtype = K
                  rw [htopK]
                  exact htop_map
                have hden :
                    (series (1 : Fin ((n + 1) + 1))).subgroupOf (⊤ : Subgroup H) =
                      K.subgroupOf (⊤ : Subgroup H) := by
                  rw [hfirst]
                have hsource_norm :
                    ((series (1 : Fin ((n + 1) + 1))).subgroupOf
                      (⊤ : Subgroup H)).Normal := by
                  rw [hden]
                  exact hnormKtop
                refine ⟨(by simpa [primes] using (inferInstance : Fact p.Prime)), S,
                  hsource_norm, ⟨?_⟩⟩
                · let : ((series (1 : Fin ((n + 1) + 1))).subgroupOf
                    (⊤ : Subgroup H)).Normal := hsource_norm
                  let : (K.subgroupOf (⊤ : Subgroup H)).Normal := hnormKtop
                  let eAdjust :
                      ((⊤ : Subgroup H) ⧸
                          (series (1 : Fin ((n + 1) + 1))).subgroupOf
                            (⊤ : Subgroup H)) ≃*
                        ((⊤ : Subgroup H) ⧸ K.subgroupOf (⊤ : Subgroup H)) :=
                    QuotientGroup.quotientMulEquivOfEq hden
                  let eTopQuot :
                    ((⊤ : Subgroup H) ⧸ K.subgroupOf (⊤ : Subgroup H)) ≃* H ⧸ K :=
                    topQuotientSubgroupOfEquivQuotient (G := H) K
                  change ((⊤ : Subgroup H) ⧸
                      (series (1 : Fin ((n + 1) + 1))).subgroupOf (⊤ : Subgroup H)) ≃*
                    ↥(S : Subgroup H)
                  exact eAdjust.trans <| eTopQuot.trans
                    (quotientPPrimeCoreEquivSylowOfHasNormalPComplement
                      (G := H) (p := p) hcomp S)
          | succ j =>
              rcases hstepK j with ⟨hleK, hfactorK⟩
              refine ⟨?_, ?_⟩
              · change (seriesK j.succ).map K.subtype ≤ (seriesK j.castSucc).map K.subtype
                exact Subgroup.map_mono hleK
              · rcases hfactorK with ⟨hqFact, Pj, hnormK, ⟨eKquot⟩⟩
                let : Fact (primesK j).Prime := hqFact
                let : ((seriesK j.succ).subgroupOf (seriesK j.castSucc)).Normal := hnormK
                obtain ⟨hnormG, ⟨eGquot⟩⟩ :=
                  quotient_map_subtype_factor_equiv (K := K)
                    (L := seriesK j.succ) (M := seriesK j.castSucc) hleK
                have hq_ne_p : primesK j ≠ p := ne_of_gt (hp_lt_primeK j)
                obtain ⟨Qj, ⟨eSylow⟩⟩ :=
                  sylow_equiv_of_normal_quotient_pgroup_ne (G := H) K hquotp hq_ne_p Pj
                refine ⟨hqFact, Qj, ?_, ⟨?_⟩⟩
                · change (((seriesK j.succ).map K.subtype).subgroupOf
                    ((seriesK j.castSucc).map K.subtype)).Normal
                  exact hnormG
                · change (((seriesK j.castSucc).map K.subtype) ⧸
                      ((seriesK j.succ).map K.subtype).subgroupOf
                        ((seriesK j.castSucc).map K.subtype)) ≃*
                    ↥(Qj : Subgroup H)
                  exact eGquot.trans (eKquot.trans eSylow)
        · intro i
          cases i using Fin.cases with
          | zero =>
              simpa [primes] using hp_small.2.1
          | succ j =>
              simpa [primes] using
                ((hdivK j).trans (Subgroup.card_subgroup_dvd_card K))
  have hmain : P (Nat.card G) := Nat.strong_induction_on (Nat.card G) hP
  exact hmain G rfl hsolv hodd hrank

public theorem CFSG.theorem_4_20_c {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (hrank : groupRank G ≤ 2 ∨ groupRank (fittingSubgroup G) ≤ 2) :
    HasOrderedCharacteristicSylowSeries G := by
  rcases theorem_4_20_c_with_prime_divisors (G := G) hsolv hodd hrank with
    ⟨n, series, primes, htop, hbot, hchar, hmono, hstep, _hdiv⟩
  exact ⟨n, series, primes, htop, hbot, hchar, hmono, hstep⟩


public theorem CFSG.theorem_4_20_largest_prime_normal_sylow
    {G : Type u} [Group G] [Finite G]
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (hrank : groupRank G ≤ 2 ∨ groupRank (fittingSubgroup G) ≤ 2)
    {p : ℕ} [Fact p.Prime] (hp_largest : IsLargestPrimeDivisor p (Nat.card G)) :
    ∃ S : Sylow p G, (S : Subgroup G).Normal := by
  classical
  let P : ℕ → Prop := fun m =>
    ∀ (H : Type u) [Group H] [Finite H], Nat.card H = m →
      Group.IsSolvable H → Odd (Nat.card H) →
      (groupRank H ≤ 2 ∨ groupRank (fittingSubgroup H) ≤ 2) →
      ∀ {p : ℕ} [Fact p.Prime], IsLargestPrimeDivisor p (Nat.card H) →
        ∃ S : Sylow p H, (S : Subgroup H).Normal
  have hP : ∀ m, (∀ k < m, P k) → P m := by
    intro m ih H _ _ hcard hHsolv hHodd hHrank p hpFact hp_largest_H
    have hHcard_ne_one : Nat.card H ≠ 1 := by
      intro hcard_one
      exact hp_largest_H.1.not_dvd_one (by simpa [hcard_one] using hp_largest_H.2.1)
    have hHcard_gt : 1 < Nat.card H := by
      have hpos : 0 < Nat.card H := Nat.card_pos
      omega
    have : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp hHcard_gt
    let r := Nat.minFac (Nat.card H)
    have hr_small : IsSmallestPrimeDivisor r (Nat.card H) :=
      minFac_natCard_isSmallestPrimeDivisor H
    have : Fact r.Prime := ⟨hr_small.1⟩
    have hcomp : HasNormalPComplement r H := by
      simpa [r] using hasNormalPComplement_minFac_of_rank_hyp
        (G := H) hHsolv hHodd hHrank
    let K : Subgroup H := pPrimeCore r H
    have hKchar : K.Characteristic := by
      simpa [K] using pPrimeCore_characteristic (p := r) (G := H)
    let : K.Characteristic := hKchar
    have : K.Normal := by infer_instance
    have hquotr : IsPGroup r (H ⧸ K) := by
      simpa [K] using
        isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := r) (H := H) hcomp
    by_cases hKsub : Subsingleton K
    · let : Subsingleton K := hKsub
      have hK_bot : K = ⊥ := by
        apply eq_bot_iff.2
        intro x hx
        have hx_one : (⟨x, hx⟩ : K) = 1 := Subsingleton.elim _ _
        simpa using congrArg Subtype.val hx_one
      have hHr : IsPGroup r H := by
        have hquot_bot : IsPGroup r (H ⧸ (⊥ : Subgroup H)) := by
          exact hquotr.of_equiv (QuotientGroup.quotientMulEquivOfEq hK_bot)
        exact hquot_bot.of_equiv QuotientGroup.quotientBot
      obtain ⟨n, hn⟩ := hHr.exists_card_eq
      have hp_dvd_pow : p ∣ r ^ n := by
        simpa [hn] using hp_largest_H.2.1
      have hp_eq_r : p = r :=
        Nat.prime_eq_prime_of_dvd_pow hpFact.out (Fact.out : Nat.Prime r) hp_dvd_pow
      subst p
      have htop_r : IsPGroup r (⊤ : Subgroup H) := hHr.to_subgroup (⊤ : Subgroup H)
      let S : Sylow r H := IsPGroup.toSylow (G := H) (p := r) htop_r (by
        simpa using (Fact.out : Nat.Prime r).not_dvd_one)
      refine ⟨S, ?_⟩
      have hS_top : (S : Subgroup H) = ⊤ := by
        simp [S, IsPGroup.toSylow_coe]
      rw [hS_top]
      infer_instance
    · have : Nontrivial K := not_subsingleton_iff_nontrivial.mp hKsub
      have hKcard_ne_one : Nat.card K ≠ 1 := by
        exact Nat.ne_of_gt (Finite.one_lt_card (α := K))
      have hp_ne_r : p ≠ r := by
        intro hp_eq_r
        obtain ⟨s, hsprime, hsdvdK⟩ := Nat.exists_prime_and_dvd hKcard_ne_one
        have hsdvdH : s ∣ Nat.card H :=
          hsdvdK.trans (Subgroup.card_subgroup_dvd_card K)
        have hr_le_s : r ≤ s := hr_small.2.2 s hsprime hsdvdH
        have hs_le_r : s ≤ r := by
          simpa [hp_eq_r] using hp_largest_H.2.2 s hsprime hsdvdH
        have hs_eq_r : s = r := le_antisymm hs_le_r hr_le_s
        have hKcop : Nat.Coprime r (Nat.card K) := by
          simpa [K] using pPrimeCore_coprime_card (G := H) (p := r)
        exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime r)).1 hKcop)
          (by simpa [hs_eq_r] using hsdvdK)
      have hp_not_dvd_quot : ¬ p ∣ Nat.card (H ⧸ K) := by
        intro hpquot
        obtain ⟨n, hn⟩ := hquotr.exists_card_eq
        have hp_dvd_pow : p ∣ r ^ n := by simpa [hn] using hpquot
        have hp_eq_r : p = r :=
          Nat.prime_eq_prime_of_dvd_pow hpFact.out (Fact.out : Nat.Prime r) hp_dvd_pow
        exact hp_ne_r hp_eq_r
      have hp_dvd_K : p ∣ Nat.card K := by
        have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := H) (s := K)
        have hp_prod : p ∣ Nat.card (H ⧸ K) * Nat.card K := by
          simpa [hmul] using hp_largest_H.2.1
        rcases hpFact.out.dvd_or_dvd hp_prod with hpquot | hpK
        · exact False.elim (hp_not_dvd_quot hpquot)
        · exact hpK
      have hp_largest_K : IsLargestPrimeDivisor p (Nat.card K) := by
        refine ⟨hpFact.out, hp_dvd_K, ?_⟩
        intro q hqprime hqdvdK
        exact hp_largest_H.2.2 q hqprime
          (hqdvdK.trans (Subgroup.card_subgroup_dvd_card K))
      have hK_ne_top : K ≠ ⊤ := by
        intro htop
        have hcardK : Nat.card K = Nat.card H := by
          simp [htop]
        have hr_dvd_K : r ∣ Nat.card K := by
          simpa [hcardK] using hr_small.2.1
        have hKcop : Nat.Coprime r (Nat.card K) := by
          simpa [K] using pPrimeCore_coprime_card (G := H) (p := r)
        exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime r)).1 hKcop)
          hr_dvd_K
      have hKltH : Nat.card K < Nat.card H := by
        have hle : Nat.card K ≤ Nat.card H := Subgroup.card_le_card_group (H := K)
        have hne : Nat.card K ≠ Nat.card H := by
          intro hEq
          exact hK_ne_top ((Subgroup.card_eq_iff_eq_top (H := K)).1 hEq)
        exact lt_of_le_of_ne hle hne
      have hKlt : Nat.card K < m := by
        simpa [hcard] using hKltH
      have hKsolv : Group.IsSolvable K := by
        let : Group.IsSolvable H := hHsolv
        infer_instance
      have hKodd : Odd (Nat.card K) :=
        hHodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)
      have hKrank :
          groupRank K ≤ 2 ∨ groupRank (fittingSubgroup K) ≤ 2 :=
        theorem_4_20_rank_hyp_of_normal_subgroup (G := H) K hHrank
      obtain ⟨P, hPnorm⟩ :=
        ih (Nat.card K) hKlt K rfl hKsolv hKodd hKrank hp_largest_K
      obtain ⟨S, hS_eq⟩ :=
        sylow_map_subtype_of_normal_quotient_pgroup_ne (G := H) K hquotr hp_ne_r P
      refine ⟨S, ?_⟩
      rw [hS_eq]
      have hPchar : (P : Subgroup K).Characteristic :=
        Sylow.characteristic_of_normal P hPnorm
      let : (P : Subgroup K).Characteristic := hPchar
      have hPmap_char :
          ((P : Subgroup K).map K.subtype : Subgroup H).Characteristic :=
        characteristic_map_subtype_of_characteristic (G := H) K (P : Subgroup K)
      let : ((P : Subgroup K).map K.subtype : Subgroup H).Characteristic := hPmap_char
      infer_instance
  have hmain : P (Nat.card G) := Nat.strong_induction_on (Nat.card G) hP
  exact hmain G rfl hsolv hodd hrank hp_largest

end Main
