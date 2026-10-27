module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKStarDefs
public import CFSG.LocalAnalysis.StandardType.GGSummandStructBasic
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeInner

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Abstract


theorem ggOTwoFrame_pCore_inf_eq_bot {G : Type} [Group G] [Finite G] {G₀ G₁ M : Subgroup G} {b : G}
    (hG₀G₁ : G₀ ≤ G₁) (hG₁M : G₁ ≤ M) (hMN : M ≤ Subgroup.normalizer (G₀ : Set G))
    (hodd : Odd (G₀.relIndex G₁))
    (hO2 : pCoreOf 2 (G₀ ⊓ Subgroup.centralizer {b}) = ⊥) :
    pCoreOf 2 (M ⊓ Subgroup.centralizer {b}) ⊓ G₁ = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ bot_le
  rw [← hO2]
  refine le_pCoreOf_of_normalized 2 ?_ ?_ ?_
  · intro x hx
    refine ⟨?_, ?_⟩
    · have hxR : x ∈ pCoreOf 2 (M ⊓ Subgroup.centralizer {b}) := hx.1
      have hxG1 : x ∈ G₁ := hx.2
      obtain ⟨k, hk⟩ := (isPGroup_pCoreOf' 2 (M ⊓ Subgroup.centralizer {b})).exists_orderOf_dvd_pow
        ⟨x, hxR⟩
      let N : Subgroup G₁ := G₀.subgroupOf G₁
      have hG1norm : G₁ ≤ Subgroup.normalizer (G₀ : Set G) := hG₁M.trans hMN
      have hNnormal : N.Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hG₀G₁).mpr hG1norm
      haveI := hNnormal
      let xB : G₁ := ⟨x, hxG1⟩
      have hord : orderOf xB = orderOf (⟨x, hxR⟩ :
          ↥(pCoreOf 2 (M ⊓ Subgroup.centralizer {b}))) := by
        rw [← Subgroup.orderOf_coe xB,
          ← Subgroup.orderOf_coe (⟨x, hxR⟩ : ↥(pCoreOf 2 (M ⊓ Subgroup.centralizer {b})))]
      have hxdvd1 : orderOf xB ∣ 2 ^ k := by rw [hord]; exact hk
      let xq : G₁ ⧸ N := QuotientGroup.mk' N xB
      have hcard : Nat.card (G₁ ⧸ N) = G₀.relIndex G₁ := rfl
      have hxdvd2 : orderOf xq ∣ G₀.relIndex G₁ := by
        rw [← hcard]
        exact orderOf_dvd_natCard xq
      have hcop : Nat.Coprime (2 ^ k) (G₀.relIndex G₁) :=
        (Nat.coprime_two_left.mpr hodd).pow_left k
      have hxdvd3 : orderOf xq ∣ 2 ^ k := by
        rw [orderOf_dvd_iff_pow_eq_one]
        show (QuotientGroup.mk' N xB) ^ (2 ^ k) = 1
        rw [← map_pow, (orderOf_dvd_iff_pow_eq_one).mp hxdvd1, map_one]
      have hxq1 : orderOf xq = 1 := Nat.eq_one_of_dvd_coprimes hcop hxdvd3 hxdvd2
      have hxqeq1 : xq = 1 := orderOf_eq_one_iff.mp hxq1
      have hker : xB ∈ (QuotientGroup.mk' N).ker := MonoidHom.mem_ker.mpr hxqeq1
      rw [QuotientGroup.ker_mk'] at hker
      exact Subgroup.mem_subgroupOf.mp hker
    · exact (pCoreOf_le' 2 (M ⊓ Subgroup.centralizer {b}) hx.1).2
  · exact (isPGroup_pCoreOf' 2 (M ⊓ Subgroup.centralizer {b})).to_le inf_le_left
  · intro h hh q hq
    refine ⟨?_, ?_⟩
    · exact conj_mem_pCoreOf' 2 ⟨hG₁M (hG₀G₁ hh.1), hh.2⟩ hq.1
    · exact G₁.mul_mem (G₁.mul_mem (hG₀G₁ hh.1) hq.2) (G₁.inv_mem (hG₀G₁ hh.1))

theorem ggOTwoFrame_pCore_le_centralizer {G : Type} [Group G] [Finite G] {G₁ M : Subgroup G} {b : G}
    (hG₁M : G₁ ≤ M) (hN : ∀ m ∈ M, ∀ c ∈ G₁, m * c * m⁻¹ ∈ G₁)
    (h : pCoreOf 2 (M ⊓ Subgroup.centralizer {b}) ⊓ G₁ = ⊥) :
    pCoreOf 2 (M ⊓ Subgroup.centralizer {b}) ≤
      Subgroup.centralizer ((G₁ ⊓ Subgroup.centralizer {b} : Subgroup G) : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have hwR : r * c * r⁻¹ * c⁻¹ ∈ pCoreOf 2 (M ⊓ Subgroup.centralizer {b}) := by
    have hcMC : c ∈ M ⊓ Subgroup.centralizer {b} := ⟨hG₁M hc.1, hc.2⟩
    have h1 : c * r⁻¹ * c⁻¹ ∈ pCoreOf 2 (M ⊓ Subgroup.centralizer {b}) :=
      conj_mem_pCoreOf' 2 hcMC (Subgroup.inv_mem _ hr)
    convert (Subgroup.mul_mem _ hr h1) using 1
    group
  have hwG1 : r * c * r⁻¹ * c⁻¹ ∈ G₁ := by
    have hrM : r ∈ M := (pCoreOf_le' 2 (M ⊓ Subgroup.centralizer {b}) hr).1
    exact G₁.mul_mem (hN r hrM c hc.1) (G₁.inv_mem hc.1)
  have hw1 : r * c * r⁻¹ * c⁻¹ = 1 := by
    have hmem := Subgroup.mem_inf.mpr ⟨hwR, hwG1⟩
    rwa [h, Subgroup.mem_bot] at hmem
  have h2 : (r * c * r⁻¹ * c⁻¹) * (c * r) = r * c := by group
  rw [hw1, one_mul] at h2
  exact h2

theorem ggExistsInvolution_of_isPGroup_ne_bot {G : Type} [Group G] [Finite G] {R : Subgroup G}
    (h2 : IsPGroup 2 R) (hR : R ≠ ⊥) :
    ∃ r ∈ R, orderOf r = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp h2
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hR (Subgroup.eq_bot_of_card_eq R hn)
  have hdvd : 2 ∣ Nat.card R := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 hdvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

end Abstract

section GOne


@[expose] def ggG1 {G : Type} [Group G]
    {t : StatedLieTag} {n f : ℕ} (ψ : (ggU t n f).K →* G) : Subgroup G where
  carrier := {c | c ∈ Subgroup.normalizer (ψ.range : Set G) ∧ GGPsiInnerDiag (ggU t n f).D ψ c}
  mul_mem' := by
    rintro c c' ⟨hc, hdiag⟩ ⟨hc', hdiag'⟩
    refine ⟨Subgroup.mul_mem (Subgroup.normalizer (ψ.range : Set G)) hc hc', ?_⟩
    obtain ⟨g, hg, hgroot⟩ := hdiag
    obtain ⟨g', hg', hg'root⟩ := hdiag'
    have hc'inv : c'⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) :=
      (Subgroup.normalizer (ψ.range : Set G)).inv_mem hc'
    have hconj : c'⁻¹ * g * c' ∈ ψ.range := by
      have h := (Subgroup.mem_normalizer_iff.mp hc'inv g).mp hg
      rwa [inv_inv] at h
    refine ⟨(c'⁻¹ * g * c') * g', ψ.range.mul_mem hconj hg', fun γ hγ => ?_⟩
    obtain ⟨h, hh, hhroot⟩ := hgroot γ hγ
    obtain ⟨h', hh', hh'root⟩ := hg'root γ hγ
    refine ⟨h' * h, Subgroup.mul_mem (ggTorus (ggU t n f).D) hh' hh, fun z hz => ?_⟩
    have hz' : h * z * h⁻¹ ∈ ((ggU t n f).D).rootGroup γ := by
      have hmem : h ∈ Subgroup.normalizer (((ggU t n f).D).rootGroup γ :
          Set (ggU t n f).K) := by
        have hh' := hh
        simp only [ggTorus, Subgroup.mem_iInf] at hh'
        exact hh' γ hγ
      exact (Subgroup.mem_normalizer_iff.mp hmem z).mp hz
    have e1 : c * c' * ((c'⁻¹ * g * c') * g') = (c * g) * (c' * g') := by group
    have e2 : (c * c' * ((c'⁻¹ * g * c') * g'))⁻¹ = (c' * g')⁻¹ * (c * g)⁻¹ := by group
    rw [e2, e1]
    rw [show (c' * g')⁻¹ * (c * g)⁻¹ * ψ z * ((c * g) * (c' * g')) =
        (c' * g')⁻¹ * ((c * g)⁻¹ * ψ z * (c * g)) * (c' * g') from by group]
    rw [hhroot z hz, hh'root (h * z * h⁻¹) hz']
    congr 1
    group
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    refine ⟨1, ψ.range.one_mem, fun γ hγ => ⟨1, Subgroup.one_mem _, fun z hz => ?_⟩⟩
    simp
  inv_mem' := by
    rintro c ⟨hc, hdiag⟩
    refine ⟨(Subgroup.normalizer (ψ.range : Set G)).inv_mem hc, ?_⟩
    obtain ⟨g, hg, hgroot⟩ := hdiag
    have hc' : c * g⁻¹ * c⁻¹ ∈ ψ.range :=
      (Subgroup.mem_normalizer_iff.mp hc g⁻¹).mp (ψ.range.inv_mem hg)
    refine ⟨c * g⁻¹ * c⁻¹, hc', fun γ hγ => ?_⟩
    obtain ⟨h, hh, hhroot⟩ := hgroot γ hγ
    refine ⟨h⁻¹, Subgroup.inv_mem _ hh, fun z hz => ?_⟩
    have hmem : h ∈ Subgroup.normalizer (((ggU t n f).D).rootGroup γ :
        Set (ggU t n f).K) := by
      have hh' := hh
      simp only [ggTorus, Subgroup.mem_iInf] at hh'
      exact hh' γ hγ
    have hw : h⁻¹ * z * h ∈ ((ggU t n f).D).rootGroup γ := by
      have hnorm : h⁻¹ ∈ Subgroup.normalizer (((ggU t n f).D).rootGroup γ :
          Set (ggU t n f).K) := (Subgroup.normalizer _).inv_mem hmem
      have h := (Subgroup.mem_normalizer_iff.mp hnorm z).mp hz
      rwa [inv_inv] at h
    have key4 : (c * g)⁻¹ * ψ (h⁻¹ * z * h) * (c * g) = ψ z := by
      rw [hhroot (h⁻¹ * z * h) hw]
      congr 1
      group
    have key5 : (c * g) * ψ z * (c * g)⁻¹ = ψ (h⁻¹ * z * h) := by
      have hg1 : (c * g) * ((c * g)⁻¹ * ψ (h⁻¹ * z * h) * (c * g)) * (c * g)⁻¹ =
          ψ (h⁻¹ * z * h) := by group
      rwa [key4] at hg1
    have hL : c⁻¹ * (c * g⁻¹ * c⁻¹) = (c * g)⁻¹ := by group
    rw [hL, inv_inv h, inv_inv (c * g)]
    exact key5

theorem ggG1_le_ggM {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hr : ψ.range = ggG0 p B x L D J) : ggG1 ψ ≤ ggM p B x L D J := by
  intro c hc
  change c ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G)
  rw [← hr]
  exact hc.1

theorem ggG0_le_ggG1 {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hr : ψ.range = ggG0 p B x L D J) : ggG0 p B x L D J ≤ ggG1 ψ := by
  intro c hc
  refine ⟨?_, ?_⟩
  · rw [hr]
    exact Subgroup.le_normalizer hc
  · have hc' : c ∈ ψ.range := by rw [hr]; exact hc
    refine ⟨c⁻¹, ψ.range.inv_mem hc', fun γ hγ => ⟨1, Subgroup.one_mem _, fun z hz => ?_⟩⟩
    simp

theorem ggBs_le_ggG1 {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) :
    Bs ≤ ggG1 ψ := by
  intro b hb
  refine ⟨?_, hctx.2.2.2.2.2.2.1.2 b hb⟩
  rw [hctx.range_eq]
  exact hctx.bstar_le_normalizer hb

theorem ggG1_le_ggG0_of_diagInner {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (h : GGPsiDiagInnerAt t)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) : ggG1 ψ ≤ ggG0 p B x L D J := by
  intro c hc
  obtain ⟨hcnorm, hcdiag⟩ := hc
  have hcnorm' : c ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
    rw [hctx.range_eq] at hcnorm
    exact hcnorm
  obtain ⟨g, hg, hcg⟩ := h G n f ψ (ggG0 p B x L D J)
    ⟨hctx.2.2.2.1, ⟨hctx.range_eq, hctx.2.2.2.2.1.2⟩, hctx.perfect, hctx.lieModel⟩
    c hcnorm' hcdiag
  have hcg1 : c * g = 1 := by
    have hmem := hcg
    rw [s1.1, Subgroup.mem_bot] at hmem
    exact hmem
  have hceq : c = g⁻¹ := by
    calc c = c * g * g⁻¹ := by group
      _ = 1 * g⁻¹ := by rw [hcg1]
      _ = g⁻¹ := by rw [one_mul]
  rw [hceq]
  exact (ggG0 p B x L D J).inv_mem hg

theorem ggR_inf_ggG1_eq_bot {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hr : ψ.range = ggG0 p B x L D J)
    (hodd : Odd ((ggG0 p B x L D J).relIndex (ggG1 ψ))) {b : G}
    (hO2 : pCoreOf 2 (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) = ⊥) :
    pCoreOf 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) ⊓ ggG1 ψ = ⊥ := by
  exact ggOTwoFrame_pCore_inf_eq_bot (G₀ := ggG0 p B x L D J) (G₁ := ggG1 ψ)
    (M := ggM p B x L D J) (b := b) (ggG0_le_ggG1 hr) (ggG1_le_ggM hr) le_rfl hodd hO2

theorem ggR_le_centralizer_ggG1 {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hr : ψ.range = ggG0 p B x L D J)
    (hN : ∀ m ∈ ggM p B x L D J, ∀ c ∈ ggG1 ψ, m * c * m⁻¹ ∈ ggG1 ψ) {b : G}
    (h : pCoreOf 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) ⊓ ggG1 ψ = ⊥) :
    pCoreOf 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) ≤
      Subgroup.centralizer ((ggG1 ψ ⊓ Subgroup.centralizer {b} : Subgroup G) : Set G) := by
  exact ggOTwoFrame_pCore_le_centralizer (G₁ := ggG1 ψ) (M := ggM p B x L D J) (b := b)
    (ggG1_le_ggM hr) hN h

theorem ggR_inf_ggG0_eq_bot_of_diagInner {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (h : GGPsiDiagInnerAt t)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) {b : G}
    (hO2 : pCoreOf 2 (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) = ⊥) :
    pCoreOf 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) ⊓ ggG0 p B x L D J = ⊥ ∧
      pCoreOf 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) ≤
        Subgroup.centralizer
          ((ggG0 p B x L D J ⊓ Subgroup.centralizer {b} : Subgroup G) : Set G) := by
  have hg1 : ggG1 ψ = ggG0 p B x L D J :=
    le_antisymm (ggG1_le_ggG0_of_diagInner h hctx s1) (ggG0_le_ggG1 hctx.range_eq)
  have hodd : Odd ((ggG0 p B x L D J).relIndex (ggG1 ψ)) := by
    rw [hg1, Subgroup.relIndex_self]
    exact ⟨0, by norm_num⟩
  have h1 : pCoreOf 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) ⊓ ggG1 ψ = ⊥ :=
    ggR_inf_ggG1_eq_bot hctx.range_eq hodd hO2
  have hnorm : ∀ m ∈ ggM p B x L D J, ∀ c ∈ ggG0 p B x L D J,
      m * c * m⁻¹ ∈ ggG0 p B x L D J := by
    intro m hm c hc
    exact (Subgroup.mem_normalizer_iff.mp hm c).mp hc
  have hN : ∀ m ∈ ggM p B x L D J, ∀ c ∈ ggG1 ψ, m * c * m⁻¹ ∈ ggG1 ψ := by
    intro m hm c hc
    rw [hg1] at hc ⊢
    exact hnorm m hm c hc
  constructor
  · rw [← hg1]
    exact h1
  · have h2 := ggR_le_centralizer_ggG1 hctx.range_eq hN h1
    rw [hg1] at h2
    exact h2

end GOne

section Assembly

@[expose] def GGOTwoStarAt
    (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), b ∈ Bs → b ≠ 1 →
        IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
        ∀ m ∈ ggM p B x L D J,
          D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} →
          pCoreOf 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) = ⊥ ∨
            GGOTwoXi (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) b

theorem ggOTwoCentralizerInputStar_of_at
    (h : ∀ t, GGOTwoStarAt t) : GGOTwoCentralizerInputStar :=
  fun G _ _ p B Bs x L D J t n f ψ => h t G p B Bs x L D J n f ψ

@[expose] def GGOuterInvAt
    (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), b ∈ Bs → b ≠ 1 →
        IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
        ∀ m ∈ ggM p B x L D J,
          D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} →
          ∀ r ∈ pCoreOf 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}), orderOf r = 2 →
            GGOTwoXi (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) b

theorem ggOTwoStarAt_of_outerInv
    {t : StatedLieTag} (h : GGOuterInvAt t) : GGOTwoStarAt t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 b L₁ hb hb1 hL₁ m hm hEC
  by_cases hR : pCoreOf 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) = ⊥
  · exact Or.inl hR
  · obtain ⟨r, hr, hr2⟩ := ggExistsInvolution_of_isPGroup_ne_bot
      (isPGroup_pCoreOf' 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b})) hR
    exact Or.inr (h G p B Bs x L D J n f ψ hctx s1 b L₁ hb hb1 hL₁ m hm hEC r hr hr2)

theorem ggOuterInvAt_of_small
    {t : StatedLieTag}
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGOuterInvAt t := by
  intro G _ _ p B Bs x L D J n f ψ hctx
  have hrank : (ggU t n f).D.rank = 0 := lieUniversal_rank_eq_zero t n 2 f Nat.prime_two ht
  have h2 := hctx.2.2.2.1.2
  rw [hrank] at h2
  exact absurd h2 (by norm_num)

theorem ggOuterInvAt_POmegaOdd
    : GGOuterInvAt .POmegaOdd := by
  intro G _ _ p B Bs x L D J n f ψ hctx
  exact (hctx.2.2.2.1.1.2.2.2 rfl).elim

@[expose] def GGOuterInvRest
    : Prop :=
  GGOuterInvAt .PSL ∧ GGOuterInvAt .PSU ∧ GGOuterInvAt .PSp ∧ GGOuterInvAt .POmegaPlus ∧
    GGOuterInvAt .POmegaMinus ∧ GGOuterInvAt .F4 ∧ GGOuterInvAt .E6 ∧ GGOuterInvAt .E7 ∧
    GGOuterInvAt .E8 ∧ GGOuterInvAt .twistedE6

theorem ggOTwoCentralizerInputStar_of_rest
    (h : GGOuterInvRest) : GGOTwoCentralizerInputStar := by
  obtain ⟨hL, hU, hSp, hP, hM, hF4, hE6, hE7, hE8, h2E6⟩ := h
  refine ggOTwoCentralizerInputStar_of_at fun t => ggOTwoStarAt_of_outerInv ?_
  cases t with
  | PSL => exact hL
  | PSU => exact hU
  | PSp => exact hSp
  | POmegaOdd => exact ggOuterInvAt_POmegaOdd
  | POmegaPlus => exact hP
  | POmegaMinus => exact hM
  | G2 => exact ggOuterInvAt_of_small (Or.inl rfl)
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact h2E6
  | trialityD4 => exact ggOuterInvAt_of_small (Or.inr (Or.inl rfl))
  | twistedB2 => exact ggOuterInvAt_of_small (Or.inr (Or.inr (Or.inl rfl)))
  | twistedG2 => exact ggOuterInvAt_of_small (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | twistedF4 => exact ggOuterInvAt_of_small (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | Tits => exact ggOuterInvAt_of_small (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

end Assembly

end CFSG.StandardType
