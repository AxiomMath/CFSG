module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront78Nar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)

section Abstract

variable {W : Type*} [Group W] [Finite W]

theorem uc22s21rq_exists_conj_le_of_not_dvd_index {p : ℕ} [Fact p.Prime] {H : Subgroup W}
    (hH : ¬ p ∣ H.index) {E : Subgroup W} (hE : IsPGroup p E) :
    ∃ w : W, ∀ x ∈ E, w⁻¹ * x * w ∈ H := by
  classical
  obtain ⟨S₀⟩ : Nonempty (Sylow p H) := inferInstance
  have hSp : IsPGroup p ((S₀ : Subgroup H).map H.subtype) := S₀.isPGroup'.map H.subtype
  have hSH : (S₀ : Subgroup H).map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hSidx : ¬ p ∣ ((S₀ : Subgroup H).map H.subtype).index := by
    rw [← Subgroup.relIndex_mul_index hSH]
    have h1 : ((S₀ : Subgroup H).map H.subtype).relIndex H = (S₀ : Subgroup H).index := by
      unfold Subgroup.relIndex
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [h1]
    exact fun h => ((Nat.Prime.dvd_mul Fact.out).1 h).elim S₀.not_dvd_index hH
  let SW : Sylow p W := hSp.toSylow hSidx
  obtain ⟨S', hES'⟩ := hE.exists_le_sylow
  have : MulAction.IsPretransitive W (Sylow p W) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W SW S'
  refine ⟨g, fun x hx => ?_⟩
  have hx' : x ∈ (S' : Subgroup W) := hES' hx
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx'
  obtain ⟨s, hs, hsx⟩ := hx'
  have hsx' : g * s * g⁻¹ = x := by simpa [MulAut.smul_def, MulAut.conj_apply] using hsx
  have hsH : s ∈ H := hSH (by simpa [SW] using hs)
  have : g⁻¹ * x * g = s := by rw [← hsx']; group
  rw [this]
  exact hsH

theorem uc22s21rq_index_normalizer_dvd {q : ℕ} [Fact q.Prime] (Δ : Subgroup W) [Δ.Normal]
    (P : Sylow q Δ) :
    (normalizer (((P : Subgroup Δ).map Δ.subtype : Subgroup W) : Set W)).index ∣
      Nat.card Δ := by
  have h1 := Sylow.normalizer_sup_eq_top P
  have h2 := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal Δ
    (normalizer (((P : Subgroup Δ).map Δ.subtype : Subgroup W) : Set W))
  rw [sup_comm, h1, Subgroup.relIndex_top_right] at h2
  rw [h2]
  exact Subgroup.relIndex_dvd_card _ _

theorem uc22s21rq_pRank_le_normalizer {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (Δ : Subgroup W)
    [Δ.Normal] (hp : ¬ p ∣ Nat.card Δ) (P : Sylow q Δ) :
    Open.pRank p (⊤ : Subgroup W) ≤
      Open.pRank p (normalizer (((P : Subgroup Δ).map Δ.subtype : Subgroup W) : Set W)) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup W)
  have hidx : ¬ p ∣ (normalizer (((P : Subgroup Δ).map Δ.subtype : Subgroup W) : Set W)).index :=
    fun h => hp (h.trans (uc22s21rq_index_normalizer_dvd Δ P))
  obtain ⟨w, hw⟩ := uc22s21rq_exists_conj_le_of_not_dvd_index hidx hE.isPGroup
  have hle : E.map (MulAut.conj w⁻¹).toMonoidHom ≤
      normalizer (((P : Subgroup Δ).map Δ.subtype : Subgroup W) : Set W) := by
    rintro _ ⟨y, hy, rfl⟩
    have := hw y hy
    simpa [MulAut.conj_apply] using this
  refine CFSG.SectionRank.le_pRank hp1 hle (CFSG.SectionRank.isElemAbelian_map hE _) ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj w⁻¹).injective, hcard]

end Abstract

section Lift

variable {W V : Type*} [Group W] [Group V] [Finite W]

theorem uc22s21rq_map_sylow_comap (π : W →* V) (hπ : Function.Surjective π) {q : ℕ}
    [Fact q.Prime] {R : Subgroup V} (hR : IsPGroup q R) (S : Sylow q (R.comap π)) :
    ((S : Subgroup (R.comap π)).map (R.comap π).subtype).map π = R := by
  classical
  let f : (R.comap π) →* R := (π.comp (R.comap π).subtype).codRestrict R (fun x => x.2)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hπ (y : V)
    exact ⟨⟨x, by change π x ∈ R; rw [hx]; exact y.2⟩, Subtype.ext hx⟩
  have htop : (S.mapSurjective hf : Subgroup R) = ⊤ :=
    ((S.mapSurjective hf).3 (Q := ⊤) (hR.of_equiv Subgroup.topEquiv.symm) le_top).symm
  ext y
  constructor
  · rintro ⟨x, ⟨s, hs, rfl⟩, rfl⟩
    exact s.2
  · intro hy
    have hmem : (⟨y, hy⟩ : R) ∈ (S.mapSurjective hf : Subgroup R) := htop ▸ Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hmem
    obtain ⟨s, hs, hsy⟩ := hmem
    exact ⟨s, ⟨s, hs, rfl⟩, congrArg Subtype.val hsy⟩

theorem uc22s21rq_disjoint_ker (π : W →* V) (hker : IsPGroup 2 π.ker) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) {R : Subgroup V} (S : Sylow q (R.comap π)) :
    Disjoint ((S : Subgroup (R.comap π)).map (R.comap π).subtype) π.ker :=
  IsPGroup.disjoint_of_ne q 2 hq2 _ _ (S.isPGroup'.map _) hker

theorem uc22s21rq_not_dvd_card_comap (π : W →* V) (hker : IsPGroup 2 π.ker) {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hp2 : p ≠ 2) (hpq : p ≠ q) {R : Subgroup V}
    (hR : IsPGroup q R) : ¬ p ∣ Nat.card (R.comap π) := by
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hy : orderOf (x : W) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have hcopq : ∀ k : ℕ, Nat.Coprime p (q ^ k) := fun k =>
    Nat.Coprime.pow_right k ((Nat.coprime_primes Fact.out Fact.out).2 hpq)
  have hcop2 : ∀ k : ℕ, Nat.Coprime p (2 ^ k) := fun k =>
    Nat.Coprime.pow_right k ((Nat.coprime_primes Fact.out Nat.prime_two).2 hp2)
  have hpow : (x : W) ^ p = 1 := by rw [← hy]; exact pow_orderOf_eq_one _
  have hπx : π x = 1 := by
    obtain ⟨k, hk⟩ := hR ⟨π x, x.2⟩
    have hk' : (π x) ^ q ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf (π x) ∣ p := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hpow, map_one])
    have h2 : orderOf (π x) ∣ q ^ k := orderOf_dvd_of_pow_eq_one hk'
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hcopq k) h1 h2)
  obtain ⟨j, hj⟩ := hker ⟨(x : W), hπx⟩
  have hj' : (x : W) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have h3 : p ∣ 2 ^ j := hy ▸ orderOf_dvd_of_pow_eq_one hj'
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes (hcop2 j) dvd_rfl h3)

end Lift

section Transport

variable {G : Type} [Group G] [Finite G]

theorem uc22s21rq_exists_sylow (M : Subgroup G) {q : ℕ} [Fact q.Prime] {R : Subgroup (Bar2 M)}
    {Q : Subgroup G} (hQ : IsSylowOf q Q (barPreimage M R)) :
    Q ≤ M ∧ ∃ S : Sylow q ↥(R.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))),
      (S : Subgroup _).map (R.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).subtype =
        Q.subgroupOf M := by
  have hQM : Q ≤ M := hQ.le.trans (Subgroup.map_subtype_le _)
  refine ⟨hQM, ?_⟩
  have h1 : (Q.subgroupOf M).map M.subtype = Q := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hQM]
  have hQ' : IsSylowOf q (Q.subgroupOf M) (R.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := q) M, h1]
    exact hQ
  exact hQ'

theorem uc22s21rq_barImage_sylow (M : Subgroup G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {R : Subgroup (Bar2 M)} (hR : IsPGroup q R) {Q : Subgroup G}
    (hQ : IsSylowOf q Q (barPreimage M R)) :
    Q ≤ M ∧ barImage M Q = R ∧
      Disjoint (Q.subgroupOf M) (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker := by
  haveI := Fact.mk hq
  obtain ⟨hQM, S, hS⟩ := uc22s21rq_exists_sylow M hQ
  have hπs : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) :=
    QuotientGroup.mk'_surjective _
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  refine ⟨hQM, ?_, ?_⟩
  · have h1 := uc22s21rq_map_sylow_comap _ hπs hR S
    rw [hS] at h1
    exact h1
  · have := uc22s21rq_disjoint_ker _ hker hq2 S
    rw [hS] at this
    exact this

theorem uc22s21rq_pRank_le (M : Subgroup G) {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hpq : p ≠ q) {R : Subgroup (Bar2 M)} [R.Normal] (hR : IsPGroup q R)
    {Q : Subgroup G} (hQ : IsSylowOf q Q (barPreimage M R)) :
    Open.pRank p M ≤ Open.pRank p (M ⊓ normalizer (Q : Set G)) := by
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  obtain ⟨hQM, S, hS⟩ := uc22s21rq_exists_sylow M hQ
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  haveI : (R.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).Normal :=
    Subgroup.Normal.comap inferInstance _
  have h1 := uc22s21rq_pRank_le_normalizer (p := p) _
    (uc22s21rq_not_dvd_card_comap _ hker hp2 hpq hR) S
  rw [hS] at h1
  have h2 : Open.pRank p M = Open.pRank p (⊤ : Subgroup ↥M) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup M
  have h3 := CFSG.SectionRank.pRank_le_map hp.one_lt M.subtype M.subtype_injective
    (normalizer ((Q.subgroupOf M : Subgroup ↥M) : Set ↥M))
  have h4 : (normalizer ((Q.subgroupOf M : Subgroup ↥M) : Set ↥M)).map M.subtype ≤
      M ⊓ normalizer (Q : Set G) := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n.2, ?_⟩
    have hn' : n ∈ normalizer ((Q.subgroupOf M : Subgroup ↥M) : Set ↥M) := hn
    rw [Subgroup.mem_normalizer_iff] at hn'
    show (n : G) ∈ normalizer (Q : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact (hn' ⟨h, hQM hh⟩).1 hh
    · intro hh
      have hhM : h ∈ M := by
        have := M.mul_mem (M.mul_mem (M.inv_mem n.2) (hQM hh)) n.2
        simpa [mul_assoc] using this
      exact (hn' ⟨h, hhM⟩).2 hh
  exact h2 ▸ h1.trans (h3.trans (CFSG.SectionRank.pRank_mono hp.one_lt h4))

theorem uc22s21rq_gamma_le (D : Data G) (hr77 : F07.R77E4 D) (hσ1 : D.sig ⊆ D.sig1) {p q : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig) (hq : q.Prime) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hqσ : q ∉ D.sig) (hsp : IsStronglyPEmbedded p D.M) (hrk : 3 < Open.pRank p D.M)
    {X : Subgroup (Bar2 D.M)} [X.Normal] (hXq : IsPGroup q X) (hXnc : ¬ IsCyclic X)
    (hXexp : ∀ x ∈ X, x ^ q = 1) (hXcl : ⁅⁅X, X⁆, X⁆ = ⊥) {Q : Subgroup G}
    (hQ : IsSylowOf q Q (barPreimage D.M X)) : rankThreeGamma 1 q Q ≤ D.M := by
  haveI := Fact.mk hq
  obtain ⟨hQM, hXQ, hdisj⟩ := uc22s21rq_barImage_sylow D.M hq hq2 hXq hQ
  have hrank : 3 < Open.pRank p (D.M ⊓ normalizer (Q : Set G)) :=
    lt_of_lt_of_le hrk (uc22s21rq_pRank_le D.M hp hp2 hq hpq hXq hQ)
  have hmem : ∀ x : Q, QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (Subgroup.inclusion hQM x) ∈ X :=
    fun x => by
      rw [← hXQ]
      exact ⟨Subgroup.inclusion hQM x, x.2, rfl⟩
  refine hr77 hσ1 p hpσ hp2 hsp q hq hq2 hqσ Q hQM hQ.isPGroup ?_ ?_ ?_ hrank
  · intro hc
    refine hXnc (isCyclic_of_surjective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).comp (Subgroup.inclusion hQM) |>.codRestrict X hmem)
      ?_)
    intro y
    have hy : (y : Bar2 D.M) ∈ barImage D.M Q := by rw [hXQ]; exact y.2
    obtain ⟨z, hz, hzy⟩ := hy
    exact ⟨⟨(z : G), hz⟩, Subtype.ext hzy⟩
  · intro x hx
    have hx1 : (⟨x, hQM hx⟩ : ↥D.M) ∈ Q.subgroupOf D.M := hx
    have hy : (⟨x, hQM hx⟩ : ↥D.M) ^ q ∈ Q.subgroupOf D.M := (Q.subgroupOf D.M).pow_mem hx1 q
    have hker : (⟨x, hQM hx⟩ : ↥D.M) ^ q ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hXexp _ (hXQ ▸ ⟨_, hx1, rfl⟩)
    have := Subgroup.disjoint_def.1 hdisj hy hker
    simpa using congrArg Subtype.val this
  · have hQ' : (Q.subgroupOf D.M).map D.M.subtype = Q := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hQM]
    have hle : ∀ A B : Subgroup ↥D.M, A ≤ Q.subgroupOf D.M → B ≤ Q.subgroupOf D.M →
        ⁅A, B⁆ ≤ Q.subgroupOf D.M := by
      intro A B hA hB
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact (Q.subgroupOf D.M).mul_mem ((Q.subgroupOf D.M).mul_mem
        ((Q.subgroupOf D.M).mul_mem (hA ha) (hB hb)) ((Q.subgroupOf D.M).inv_mem (hA ha)))
        ((Q.subgroupOf D.M).inv_mem (hB hb))
    have h1 : ⁅Q.subgroupOf D.M, Q.subgroupOf D.M⁆ ≤ Q.subgroupOf D.M := hle _ _ le_rfl le_rfl
    have h2 : ⁅⁅Q.subgroupOf D.M, Q.subgroupOf D.M⁆, Q.subgroupOf D.M⁆ ≤ Q.subgroupOf D.M :=
      hle _ _ h1 le_rfl
    have h3 : ⁅⁅Q.subgroupOf D.M, Q.subgroupOf D.M⁆, Q.subgroupOf D.M⁆ = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      have hmap : (⁅⁅Q.subgroupOf D.M, Q.subgroupOf D.M⁆, Q.subgroupOf D.M⁆).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) = ⊥ := by
        rw [Subgroup.map_commutator, Subgroup.map_commutator]
        change ⁅⁅barImage D.M Q, barImage D.M Q⁆, barImage D.M Q⁆ = ⊥
        rw [hXQ]
        exact hXcl
      exact Subgroup.mem_bot.2 (Subgroup.disjoint_def.1 hdisj (h2 hc)
        ((Subgroup.map_eq_bot_iff _).1 hmap hc))
    rw [← hQ', ← Subgroup.map_commutator, ← Subgroup.map_commutator, h3, Subgroup.map_bot]

end Transport

end CFSG.LocalAnalysis.UniquenessCase.UC22
