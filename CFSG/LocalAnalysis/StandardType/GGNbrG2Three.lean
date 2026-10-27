module

public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldComp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggNbrInnerWeyl_of_ggTorusNoLineFieldCompOff (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {I F : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsIF : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ Subgroup.closure (I ∪ F))
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hxI : ggLAut K θ ⟨x, hxK⟩ ∈ I)
    (hr : p ^ (r + 1) ≤ Nat.card (ggGamma K hN).range)
    {N : ℕ} (hT : GGTorusNoLineFieldCompOff p r R I F N)
    (hcard : Nat.card (ggFix (K.normalizerMonoidHom ⟨x, hxK⟩)) ≠ N) :
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
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ Subgroup.closure (I ∪ F),
      ∀ l : K, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta K θ hN b, hBsIF b b.2, fun l => ggBeta_ggQuotHom K hN θ b l⟩
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
    ⟨ggBeta K θ hN ⟨x, hxBs⟩, hxI, fun l => ggBeta_ggQuotHom K hN θ ⟨x, hxBs⟩ l⟩
    (ggFixCompCyclic_ggGamma_x hL hcfg
      (hPJ _ _ _ _ _ _ _ hcfg.1 hcfg.2.2) hnb hN hxBs) hcard
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

theorem ggNbrInnerWeylOn_g2Three (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hA : GGNbrG2NotA2Line) (h : GGNbrKGFieldG2Three) :
    GGNbrInnerWeylOn fun p lab => p = 3 ∧ lab.tag = .G2 ∧ 6 ∣ lab.n := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN hxK P hP
  by_cases hp3 : p = 3
  · subst hp3
    have hPA := hA G B Bs x L D J hcfg y K hnb hN hxK P hP
    obtain ⟨hK, lab, hlab, hraw⟩ := hG G 3 B Bs x L D J hcfg y K hnb hN _ hPA
    by_cases hSl : lab.tag = .G2 ∧ 6 ∣ lab.n
    · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ (h lab hlab hSl.1 hSl.2 _ hraw)⟩
      rintro R _ I F ⟨⟨hs, hna, θ, ⟨hPθ, hAθ⟩, hgr⟩, hQ⟩
      refine ⟨hs, hna, θ, hPθ, fun _ hxI => ?_⟩
      obtain ⟨hTc, hTf⟩ := hQ hs hna
      have hcard := hAθ hSl.1 hSl.2 hxI
      have h3 : 3 ^ 3 ≤ Nat.card (ggGamma K hN).range :=
        pow_three_le_card_range_ggGamma_bstar hcfg hnb hN
      have hBsIF : ∀ (b : G) (hb : b ∈ Bs),
          ggLAut K θ ⟨b, hN hb⟩ ∈ Subgroup.closure (I ∪ F) := by
        intro b hb
        obtain ⟨u, hu, f, hf, e⟩ := hgr b hb
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl hu))
          (Subgroup.closure_mono Set.subset_union_right hf)
      by_cases hall : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I
      · exact ggNbrInnerWeyl_of_ggTorusNoLineComp hL hPJ hcfg hnb hK θ hN hall
          ((Nat.pow_le_pow_right (by norm_num) (by norm_num)).trans h3) hTc
      · exact ggNbrInnerWeyl_of_ggTorusNoLineFieldCompOff hL hPJ hcfg hnb hK θ hN hBsIF hxK hxI
          h3 hTf hcard
    · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
      rintro R _ I F ⟨hs, hna, θ, ⟨hPθ, -⟩, -⟩
      exact ⟨hs, hna, θ, hPθ, fun hS => absurd ⟨hS.2.1, hS.2.2⟩ hSl⟩
  · obtain ⟨hK, lab, hlab, hraw⟩ := hP
    refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ⟩
    exact ⟨hs, hna, θ, hPθ, fun hS => absurd hS.1 hp3⟩

theorem ggNbrInnerWeylOn_of_g2Three_split {S : ℕ → LargeEvenLabel → Prop}
    (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) (hG : GGNbrGraphInput)
    (hA : GGNbrG2NotA2Line) (h : GGNbrKGFieldG2Three)
    (hS : GGNbrInnerWeylOn fun p lab => S p lab ∧ ¬ (p = 3 ∧ lab.tag = .G2 ∧ 6 ∣ lab.n)) :
    GGNbrInnerWeylOn S :=
  (hS.or (ggNbrInnerWeylOn_g2Three hL hPJ hG hA h)).mono fun p lab hS' => by
    by_cases hr : p = 3 ∧ lab.tag = .G2 ∧ 6 ∣ lab.n
    · exact Or.inr hr
    · exact Or.inl ⟨hS', hr⟩

end CFSG.StandardType

end
