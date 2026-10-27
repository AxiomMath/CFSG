module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerCore
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeALabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGTorusNoLine (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ W : Set L',
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        ((∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
          ∀ a₀ ∈ A, a₀ ≠ 1 →
            ∃ n ∈ W, MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀)

theorem ggTorusNoLine_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (h : GGTorusNoLine p r R' I') : GGTorusNoLine p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_ hr h3 hsc
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, hI φ hφ, fun l => ?_⟩
    simp [MulAut.congr_apply, hφa l]

theorem ggTorusNoLine_mono {p r r' : ℕ} (hr : r ≤ r') {R : Type} [Group R]
    {I : Set (MulAut R)} (hp : 0 < p) (h : GGTorusNoLine p r R I) : GGTorusNoLine p r' R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr' h3 hsc
  exact h L' ψ hψ hker hperf A hA hAI ((Nat.pow_le_pow_right hp hr).trans hr') h3 hsc

theorem ggNbrExists_move_of_irred {p : ℕ} (hp : p.Prime) {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (h3 : p ^ 3 ≤ Nat.card A) {W : Set L'}
    (hW2 : ∀ A' : Subgroup (MulAut L'), A' ≤ A →
      (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') → A' = ⊥ ∨ A' = A)
    {a₀ : MulAut L'} (ha₀ : a₀ ∈ A) (ha₁ : a₀ ≠ 1) :
    ∃ n ∈ W, MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀ := by
  by_contra hcon
  push Not at hcon
  have hz : Subgroup.zpowers a₀ ≤ A := Subgroup.zpowers_le.mpr ha₀
  have hinv : ∀ n ∈ W, ∀ a ∈ Subgroup.zpowers a₀,
      MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ Subgroup.zpowers a₀ := by
    intro n hn a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hcon n hn) k
  rcases hW2 (Subgroup.zpowers a₀) hz hinv with hbot | htop
  · exact ha₁ (by simpa using hbot)
  · have hcard : Nat.card A = orderOf a₀ := by rw [← htop, Nat.card_zpowers]
    have hdvd : orderOf a₀ ∣ p := orderOf_dvd_of_pow_eq_one (hA.2 a₀ ha₀)
    have hle : orderOf a₀ ≤ p := Nat.le_of_dvd hp.pos hdvd
    have hlt : p < p ^ 3 := by
      have := Nat.pow_lt_pow_right hp.one_lt (by norm_num : 1 < 3)
      simpa using this
    omega

theorem ggTorusNoLine_of_ggTorusIrred {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (h : GGTorusIrred p r R I) : GGTorusNoLine p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 _
  obtain ⟨W, hW1, hW2, -, -⟩ := h L' ψ hψ hker hperf A hA hAI hr h3
  exact ⟨W, hW1, fun _ a₀ ha₀ ha₁ => ggNbrExists_move_of_irred hp hA h3 hW2 ha₀ ha₁⟩

section Config

variable {G : Type} [Group G] [Finite G]

theorem not_mem_centralizer_of_nbr {p : ℕ} {B : Subgroup G} {x : G} {D J : Subgroup G} {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K) : x ∉ Subgroup.centralizer (K : Set G) := by
  intro h
  apply hnb.2.2.2
  have h3 : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) := (Subgroup.zpowers_le).mpr h
  have h4 : (⁅Subgroup.zpowers x, K⁆ : Subgroup G) = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr h3
  rw [Subgroup.commutator_comm, h4]
  exact bot_le

theorem pow_three_le_card_range_ggGamma_bstar {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    p ^ 3 ≤ Nat.card (ggGamma K hN).range := by
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSHat p B y K := hnb.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hN
  have hcA := card_range_ggGamma_mul_of_sHat hp hS hBN
  have hle : Nat.card (ggGamma K hBN).range ≤ Nat.card (ggGamma K hN).range := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  refine le_trans ?_ hle
  have h4 := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
  rw [← hcA, pow_succ] at h4
  exact Nat.le_of_mul_le_mul_right h4 hp.pos

theorem pow_le_card_range_ggGamma_bstar_of_torusLift {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hlift : GGTorusLift p r R) : p ^ r ≤ Nat.card (ggGamma K hN).range := by
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSHat p B y K := hnb.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hN
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hS.2.2.2.1
  have hcA := card_range_ggGamma_mul_of_sHat hp hS hBN
  have hle : Nat.card (ggGamma K hBN).range ≤ Nat.card (ggGamma K hN).range := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  have h1 := succ_le_twoLocalRank_of_torusLift hp hKy (hS.1.1.2 y hS.2.1) hS.2.2.1 hK θ hlift
  have h2 : p ^ (r + 1) ≤ Nat.card (ggGamma K hBN).range * p := by
    rw [hcA, hS.1.2.1]
    exact Nat.pow_le_pow_right hp.pos h1
  rw [pow_succ] at h2
  exact (Nat.le_of_mul_le_mul_right h2 hp.pos).trans hle

theorem ggNbrInnerWeyl_of_ggTorusNoLine {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma K hN).range) (hT : GGTorusNoLine p r R I) :
    ∃ w ∈ K, (∀ b ∈ Bs, w * b * w⁻¹ ∈ Subgroup.centralizer (Bs : Set G)) ∧
      w * x * w⁻¹ ∉ Subgroup.zpowers x := by
  classical
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma K hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : K, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta K θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom K hN θ b l⟩
  have h3 : p ^ 3 ≤ Nat.card γ.range := pow_three_le_card_range_ggGamma_bstar hcfg hnb hN
  obtain ⟨W, hW1, hW2⟩ := hT K (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
    hK γ.range hA hAI hr h3 (ggTorusSelfCent_ggGamma hN hSC)
  have hWB : ∀ n ∈ W, ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
    intro n hn b hb
    obtain ⟨htp, htA⟩ := hW1 n hn (γ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    have htG : ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) = n * b * (n : G)⁻¹ * b⁻¹ := by
      push_cast
      rw [hγ, ggGamma_coe]
      group
    have htC : ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      have h1 := congrArg Subtype.val (htA (γ ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩)
      rw [hγ, ggGamma_coe] at h1
      calc b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G)
          = b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) * b'⁻¹ * b' := by group
        _ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) * b' := by rw [h1]
    have htp' : ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) ^ p = 1 := by
      have := congrArg Subtype.val htp
      simpa using this
    have htB := hSC _ htC htp'
    have e : (n : G) * b * (n : G)⁻¹ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) * b := by
      rw [htG]
      group
    rw [e]
    exact Bs.mul_mem htB hb
  have hWA : ∀ n ∈ W, ∀ a ∈ γ.range, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ γ.range := by
    rintro n hn _ ⟨b, rfl⟩
    exact ⟨⟨(n : G) * b * (n : G)⁻¹, hWB n hn b b.2⟩,
      (ggGamma_conj K hN n b (hWB n hn b b.2)).symm ▸ rfl⟩
  have hxγ : γ ⟨x, hxBs⟩ ≠ 1 := by
    intro h1
    rw [hγ, ggGamma_eq_one_iff] at h1
    exact not_mem_centralizer_of_nbr hnb h1
  obtain ⟨n, hn, hmv⟩ := hW2 hWA (γ ⟨x, hxBs⟩) ⟨⟨x, hxBs⟩, rfl⟩ hxγ
  refine ⟨(n : G), n.2, fun b hb => ?_, fun hmem => hmv ?_⟩
  · exact Subgroup.mem_centralizer_iff.mpr fun c hc =>
      IsElemAbelian.comm hBs hc (hWB n hn b hb)
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have e : (⟨(n : G) * x * (n : G)⁻¹, hWB n hn x hxBs⟩ : Bs) = (⟨x, hxBs⟩ : Bs) ^ k := by
      apply Subtype.ext
      simpa using hk.symm
    rw [← ggGamma_conj K hN n ⟨x, hxBs⟩ (hWB n hn x hxBs), e, map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k

end Config

@[expose] def GGNbrWeylInnerKLevel (p : ℕ) : LargeEvenRawCont :=
  fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    (∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I) ∧
      ∃ r, (GGTorusLift p r R ∨ r = 0) ∧ GGTorusNoLine p r R I

theorem ggNbrInnerWeylOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      S p lab → LargeEvenLabelAll lab (GGNbrWeylInnerKLevel p)) :
    GGNbrInnerWeylOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN hxK P hP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hK, lab, hlab, hraw⟩ := hP
  by_cases hSl : S p lab
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ (h p lab hp hp2 hlab hSl _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hPθ⟩, hQ⟩
    refine ⟨hs, hna, θ, hPθ, fun _ _ => ?_⟩
    obtain ⟨hpow, r, hlift, hT⟩ := hQ hs hna
    have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I := by
      intro b hb
      apply hpow
      have e : (⟨b, hN hb⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hcfg.2.1.2.1.2 b hb)
      rw [← map_pow, e, map_one]
    have hr : p ^ r ≤ Nat.card (ggGamma K hN).range := by
      rcases hlift with hl | rfl
      · exact pow_le_card_range_ggGamma_bstar_of_torusLift hcfg hnb hK θ hN hl
      · rw [pow_zero]
        exact Nat.card_pos
    exact ggNbrInnerWeyl_of_ggTorusNoLine hcfg hnb hK θ hN hBsI hr hT
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ⟩
    exact ⟨hs, hna, θ, hPθ, fun hS => absurd hS hSl⟩

theorem largeEvenLabelAll_weylInnerKLevel_of_noLine {p : ℕ} {lab : LargeEvenLabel}
    (hPow : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I)
    (hT : LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNoLine p r R I) :
    LargeEvenLabelAll lab (GGNbrWeylInnerKLevel p) := fun Q hQ =>
  largeEvenRawDatum_mono (fun _ _ _ _ ⟨hq, h1, r, hl, hT'⟩ =>
    ⟨hq, fun hs hna => ⟨h1 hs hna, r, Or.inl hl, hT'⟩⟩) (largeEvenLabelAll_and hPow hT Q hQ)

end CFSG.StandardType

end
