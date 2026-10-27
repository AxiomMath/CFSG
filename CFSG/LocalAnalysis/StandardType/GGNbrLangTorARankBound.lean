module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankKG
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegKG
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Rank

variable {G : Type} [Group G] [Finite G]

theorem ggNbr_mem_zpowers_of_centralizes {p : ℕ} {B : Subgroup G} {x : G} {D J : Subgroup G}
    {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K) {b : G} (hb : b ∈ B)
    (hcent : ∀ k ∈ K, b * k * b⁻¹ = k) : b ∈ Subgroup.zpowers y := by
  obtain ⟨-, -, -, -, -, hker⟩ := hK.1
  have hc : b ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    calc k * b = b * k * b⁻¹ * b := by rw [hcent k hk]
      _ = b * k := by group
  refine (hker b).1 ⟨hb, Subgroup.centralizer_le_normalizer _ hc, ?_⟩
  refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
  have h2 : g₂ ∈ Subgroup.centralizer (K : Set G) := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₂
    exact Subgroup.zpow_mem _ hc n
  rw [commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 h2 g₁ hg₁)]
  exact Subgroup.one_mem _

theorem ggNbr_pow_le_card_A₀ {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) {B₀ : Subgroup G} (hB₀ : B₀ ≤ Bs)
    (hcard : Nat.card B₀ * p = Nat.card Bs)
    (hmem : ∀ (b : G) (hb : b ∈ Bs), b ∈ B₀ ↔ ggLAut K θ ⟨b, hN hb⟩ ∈ I) :
    p ^ (LargeEvenTwoLocalRank p G - 2) ≤
      Nat.card {α : MulAut ↥K // α ∈ (ggBsAut hN).range ∧ kgInducedAut θ α ∈ I} := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hβ : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
  obtain ⟨hBmax, hyB, -, -, -, -⟩ := hK.1
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hBmax.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hy : y ^ p = 1 := hBmax.1.2 y hyB
  haveI : Finite (MulAut ↥K) := inferInstanceAs (Finite (↥K ≃* ↥K))
  have hHBs : B₀ ⊓ B ≤ Bs := inf_le_left.trans hB₀
  let ρ : ↥(B₀ ⊓ B) →* MulAut ↥K := (ggBsAut hN).comp (Subgroup.inclusion hHBs)
  have hker : Nat.card ρ.ker ≤ p := by
    have hzp : Nat.card (Subgroup.zpowers y) ≤ p := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hy)
    have hmemy : ∀ h : ρ.ker, ((h.1 : ↥(B₀ ⊓ B)) : G) ∈ Subgroup.zpowers y := by
      intro h
      refine ggNbr_mem_zpowers_of_centralizes hK h.1.2.2 fun k hk => ?_
      have h1 : ρ h.1 = 1 := h.2
      exact congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : G)) h1
    refine le_trans (Nat.card_le_card_of_injective
      (fun h : ρ.ker => (⟨((h.1 : ↥(B₀ ⊓ B)) : G), hmemy h⟩ : Subgroup.zpowers y)) ?_) hzp
    intro a b hab
    have h' := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h')
  have h1 : B₀.relIndex B * Nat.card (B₀ ⊓ B : Subgroup G) = Nat.card B :=
    Subgroup.relIndex_mul_card B₀ B
  have h2 : B₀.relIndex Bs * Nat.card (B₀ ⊓ Bs : Subgroup G) = Nat.card Bs :=
    Subgroup.relIndex_mul_card B₀ Bs
  rw [inf_eq_left.2 hB₀] at h2
  have hB₀pos : 0 < Nat.card B₀ := Nat.card_pos
  have hrel : B₀.relIndex Bs = p := by
    apply Nat.eq_of_mul_eq_mul_left hB₀pos
    calc Nat.card B₀ * B₀.relIndex Bs = B₀.relIndex Bs * Nat.card B₀ := mul_comm _ _
      _ = Nat.card Bs := h2
      _ = Nat.card B₀ * p := hcard.symm
  have hrelB : B₀.relIndex B ≤ p := by
    have := Subgroup.relIndex_le_of_le_right (H := B₀) hBBs (by rw [hrel]; exact hp.ne_zero)
    rwa [hrel] at this
  have hHcard : p ^ (LargeEvenTwoLocalRank p G - 1) ≤ Nat.card ↥(B₀ ⊓ B) := by
    have h3 : p ^ LargeEvenTwoLocalRank p G ≤ p * Nat.card ↥(B₀ ⊓ B) := by
      rw [← hBcard, ← h1]
      exact Nat.mul_le_mul_right _ hrelB
    have h4 : p ^ LargeEvenTwoLocalRank p G = p * p ^ (LargeEvenTwoLocalRank p G - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h4] at h3
    exact Nat.le_of_mul_le_mul_left h3 hp.pos
  have hrange : p ^ (LargeEvenTwoLocalRank p G - 2) ≤ Nat.card ρ.range := by
    have h5 := TableB.card_range_mul_card_ker ρ
    have h6 : p ^ (LargeEvenTwoLocalRank p G - 1) ≤ Nat.card ρ.range * p := by
      calc p ^ (LargeEvenTwoLocalRank p G - 1) ≤ Nat.card ↥(B₀ ⊓ B) := hHcard
        _ = Nat.card ρ.range * Nat.card ρ.ker := h5.symm
        _ ≤ Nat.card ρ.range * p := Nat.mul_le_mul_left _ hker
    have h7 : p ^ (LargeEvenTwoLocalRank p G - 1) = p ^ (LargeEvenTwoLocalRank p G - 2) * p := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h7] at h6
    exact Nat.le_of_mul_le_mul_right h6 hp.pos
  have hA : ∀ α : ρ.range, (α : MulAut ↥K) ∈ (ggBsAut hN).range ∧
      kgInducedAut θ (α : MulAut ↥K) ∈ I := by
    rintro ⟨_, ⟨⟨b, hb⟩, rfl⟩⟩
    exact ⟨⟨⟨b, hHBs hb⟩, rfl⟩, (hmem b (hHBs hb)).1 hb.1⟩
  exact hrange.trans (Nat.card_le_card_of_injective
    (fun α : ρ.range => (⟨(α : MulAut ↥K), hA α⟩ :
      {α : MulAut ↥K // α ∈ (ggBsAut hN).range ∧ kgInducedAut θ α ∈ I}))
    fun a b hab => by
      have h' := congrArg Subtype.val hab
      exact Subtype.ext h')

theorem ggNbr_sq_le_card_A₀ {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) {B₀ : Subgroup G} (hB₀ : B₀ ≤ Bs)
    (hcard : Nat.card B₀ * p = Nat.card Bs)
    (hmem : ∀ (b : G) (hb : b ∈ Bs), b ∈ B₀ ↔ ggLAut K θ ⟨b, hN hb⟩ ∈ I) :
    p ^ 2 ≤ Nat.card {α : MulAut ↥K // α ∈ (ggBsAut hN).range ∧ kgInducedAut θ α ∈ I} := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hβ : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
  exact (Nat.pow_le_pow_right hp.pos (by omega)).trans
    (ggNbr_pow_le_card_A₀ hcfg hK hN θ hB₀ hcard hmem)

theorem ggNbr_pow_le_card_A₀_of_torusLift {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hK : GGNbr p B x D J y K) (hK₁ : commutator ↥K = ⊤)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) (hlift : GGTorusLift p r R) {B₀ : Subgroup G}
    (hB₀ : B₀ ≤ Bs) (hcard : Nat.card B₀ * p = Nat.card Bs)
    (hmem : ∀ (b : G) (hb : b ∈ Bs), b ∈ B₀ ↔ ggLAut K θ ⟨b, hN hb⟩ ∈ I) :
    p ^ (r - 1) ≤ Nat.card {α : MulAut ↥K // α ∈ (ggBsAut hN).range ∧ kgInducedAut θ α ∈ I} := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hBmax, hyB, hy1, hLy, -, -⟩ := hK.1
  have hy : y ^ p = 1 := hBmax.1.2 y hyB
  have hr : r + 1 ≤ LargeEvenTwoLocalRank p G :=
    succ_le_twoLocalRank_of_torusLift hp hLy hy hy1 hK₁ θ hlift
  exact (Nat.pow_le_pow_right hp.pos (by omega)).trans
    (ggNbr_pow_le_card_A₀ hcfg hK hN θ hB₀ hcard hmem)

theorem ggNbr_pow_div_le_card_A₀ {p d : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hK₁ : commutator ↥K = ⊤) (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (hlift : ∃ r, d / p + 3 ≤ r ∧ GGTorusLift p r R) {B₀ : Subgroup G} (hB₀ : B₀ ≤ Bs)
    (hcard : Nat.card B₀ * p = Nat.card Bs)
    (hmem : ∀ (b : G) (hb : b ∈ Bs), b ∈ B₀ ↔ ggLAut K θ ⟨b, hN hb⟩ ∈ I) :
    p ^ (d / p + 2) ≤
      Nat.card {α : MulAut ↥K // α ∈ (ggBsAut hN).range ∧ kgInducedAut θ α ∈ I} := by
  obtain ⟨r, hr, hlift⟩ := hlift
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  exact (Nat.pow_le_pow_right hp.pos (by omega)).trans
    (ggNbr_pow_le_card_A₀_of_torusLift hcfg hK hK₁ hN θ hlift hB₀ hcard hmem)

end Rank

theorem largeEvenLabelAll_torusLift_typeA {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (htag : lab.tag = .A) (hl : 4 ≤ lab.rank) (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (lab.rank + 1 - 2) R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hpn ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TypeA.ggTorusLift_sub_two hp hpK (by omega) (TypeA.slHasSections_of_five_le (by omega)))⟩

theorem largeEvenLabelAll_torusLift_splitTypeARank
    {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGNbrLangTypeARankLabel p lab) (hs : GGTypeASplitPrime p lab) :
    LargeEvenLabelAll lab fun R _ _ _ => ∃ r, (lab.rank + 1) / p + 3 ≤ r ∧ GGTorusLift p r R := by
  have hlt := ggNbrLangTypeARankLabel_lt hp hp2 h
  have hdvd : p ∣ lab.rank + 1 := h.1.2
  have hdiv : 1 ≤ (lab.rank + 1) / p :=
    Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos _) hdvd) hp.pos
  rcases hs with ⟨htag, hpq⟩ | ⟨htag, hpq⟩
  · have hlt' := hlt.2 htag
    have hl : 4 ≤ lab.rank := by omega
    exact (largeEvenLabelAll_torusLift_typeA hp htag hl hpq).mono fun R _ I F hlift =>
      ⟨lab.rank + 1 - 2, by omega, hlift⟩
  · have hlt' := hlt.1
    refine (largeEvenLabelAll_torusLift_twA hlab htag hp hpq).mono fun R _ I F hlift =>
      ⟨ggUnitaryTorusRank p (lab.rank + 1), ?_, hlift⟩
    simp only [ggUnitaryTorusRank, hdvd, ↓reduceIte]
    omega

end CFSG.StandardType
