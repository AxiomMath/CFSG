module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTriD4ThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylResidualTriD4
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylComp
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section Config

variable {G : Type} [Group G] [Finite G]

theorem isComponentOf_comap_ggFix_ggGamma_x_of_dvd (hL : GGLBalanceInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hpJ : p ∣ Nat.card J)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hxBs : x ∈ Bs) :
    J ≤ K ∧ IsComponentOf (J.comap K.subtype) (ggFix (ggGamma K hN ⟨x, hxBs⟩)) := by
  obtain ⟨hI, -, hDJ⟩ := hcfg
  obtain ⟨-, -, -, -, -, -, hS, -⟩ := id hI
  have hJK : J ≤ K := le_of_ggNbr hL hI hDJ hpJ hnb
  have hJZ : IsComponentOf J
      (Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hnb.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hnb.1.2.2.2.1
  have hfix : (ggFix (ggGamma K hN ⟨x, hxBs⟩)).map K.subtype =
      K ⊓ Subgroup.centralizer ({x} : Set G) := map_ggFix_ggGamma K hN ⟨x, hxBs⟩
  have hJle : J ≤ K ⊓ Subgroup.centralizer ({x} : Set G) := le_inf hJK (hJZ.1.trans inf_le_right)
  have hKxZ : K ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
    inf_le_inf_right _ hKy
  exact ⟨hJK, (isComponentOf_comap_of_injective K.subtype K.subtype_injective
    (by rw [hfix]; exact hJZ.of_le_of_le hJle hKxZ)).1⟩

theorem isComponentOf_comap_ggFix_ggGamma_x (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hxBs : x ∈ Bs) :
    J ≤ K ∧ IsComponentOf (J.comap K.subtype) (ggFix (ggGamma K hN ⟨x, hxBs⟩)) := by
  exact isComponentOf_comap_ggFix_ggGamma_x_of_dvd hL hcfg
    (hPJ G p B x L D J hcfg.1 hcfg.2.2) hnb hN hxBs

theorem mem_zpowers_ggGamma_x_of_fixes_J {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hxBs : x ∈ Bs)
    (hJK : J ≤ K) (hcard : Nat.card (ggGamma K hN).range ≤ p ^ 3) {f : MulAut K}
    (hf : f ∈ (ggGamma K hN).range) (hfJ : ∀ l ∈ J.comap K.subtype, f l = l) :
    f ∈ Subgroup.zpowers (ggGamma K hN ⟨x, hxBs⟩) := by
  classical
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSHat p B y K := hnb.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hN
  have hyB : y ∈ B := hS.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hS.2.2.2.1
  have hcA := card_range_ggGamma_mul_of_sHat hp hS hBN
  have h3 : p ^ 3 ≤ Nat.card (ggGamma K hBN).range := by
    have h4 := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
    rw [← hcA, pow_succ] at h4
    exact Nat.le_of_mul_le_mul_right h4 hp.pos
  have hle : (ggGamma K hBN).range ≤ (ggGamma K hN).range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  have heq : (ggGamma K hBN).range = (ggGamma K hN).range :=
    Subgroup.eq_of_le_of_card_ge hle (hcard.trans h3)
  obtain ⟨b, rfl⟩ : f ∈ (ggGamma K hBN).range := by
    rw [heq]
    exact hf
  have hbJ : (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : (b : G) * l * (b : G)⁻¹ = l := by
      have h2 := congrArg Subtype.val (hfJ ⟨l, hJK hl⟩ hl)
      rw [ggGamma_coe] at h2
      exact h2
    calc l * (b : G) = (b : G) * l * (b : G)⁻¹ * (b : G) := by rw [h1]
      _ = (b : G) * l := by group
  have hbD : (b : G) ∈ D := by
    have hDeq : D = B ⊓ Subgroup.centralizer (J : Set G) := hcfg.2.2.1.2.2.2.2.2.2
    rw [hDeq]
    exact ⟨b.2, hbJ⟩
  have hyC : y ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hKy hl)
  have hγy : ggGamma K hN ⟨y, hBBs hyB⟩ = 1 :=
    (ggGamma_eq_one_iff K hN ⟨y, hBBs hyB⟩).mpr hyC
  have hDM : D ≤ ((Subgroup.zpowers (ggGamma K hN ⟨x, hxBs⟩)).comap (ggGamma K hN)).map
      Bs.subtype := by
    rw [hnb.2.1, Subgroup.closure_le]
    rintro g (hg | hg)
    · rw [hg]
      exact ⟨⟨x, hxBs⟩, Subgroup.mem_zpowers _, rfl⟩
    · rw [Set.mem_singleton_iff.mp hg]
      refine ⟨⟨y, hBBs hyB⟩, ?_, rfl⟩
      show ggGamma K hN ⟨y, hBBs hyB⟩ ∈ Subgroup.zpowers (ggGamma K hN ⟨x, hxBs⟩)
      rw [hγy]
      exact one_mem _
  obtain ⟨b', hb', hb'b⟩ := hDM hbD
  have hbb' : b' = ⟨(b : G), hBBs b.2⟩ := Subtype.ext hb'b
  rw [hbb'] at hb'
  exact hb'

theorem ggNbrInnerWeyl_of_ggTriD4LineKnown (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {I F : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsIF : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ Subgroup.closure (I ∪ F))
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hxI : ggLAut K θ ⟨x, hxK⟩ ∈ I)
    (hT : GGTriD4LineKnown p R I F) :
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
  obtain ⟨hcard, hmain⟩ := hT K (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
    hK γ.range hA hAI
  have h3 : p ^ 3 ≤ Nat.card γ.range := pow_three_le_card_range_ggGamma_bstar hcfg hnb hN
  have hxγ : γ ⟨x, hxBs⟩ ≠ 1 := by
    intro h1
    rw [hγ, ggGamma_eq_one_iff] at h1
    exact not_mem_centralizer_of_nbr hnb h1
  rcases hmain h3 (ggTorusSelfCent_ggGamma hN hSC) (γ ⟨x, hxBs⟩) ⟨⟨x, hxBs⟩, rfl⟩ hxγ
      ⟨ggBeta K θ hN ⟨x, hxBs⟩, hxI, fun l => ggBeta_ggQuotHom K hN θ ⟨x, hxBs⟩ l⟩
      (ggFixCompCyclic_ggGamma_x hL hcfg
      (hPJ _ _ _ _ _ _ _ hcfg.1 hcfg.2.2) hnb hN hxBs) with
    ⟨n, hn1, hn2⟩ | ⟨f, hfA, hfx, hfJ⟩
  ·
    have hWB : ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
      intro b hb
      obtain ⟨htp, htA⟩ := hn1 (γ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
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
    refine ⟨(n : G), n.2, fun b hb => ?_, fun hmem => hn2 ?_⟩
    · exact Subgroup.mem_centralizer_iff.mpr fun c hc =>
        IsElemAbelian.comm hBs hc (hWB b hb)
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have e : (⟨(n : G) * x * (n : G)⁻¹, hWB x hxBs⟩ : Bs) = (⟨x, hxBs⟩ : Bs) ^ k := by
        apply Subtype.ext
        simpa using hk.symm
      rw [← ggGamma_conj K hN n ⟨x, hxBs⟩ (hWB x hxBs), e, map_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  ·
    obtain ⟨hJK, hJ1⟩ := isComponentOf_comap_ggFix_ggGamma_x hL hPJ hcfg hnb hN hxBs
    exact absurd (mem_zpowers_ggGamma_x_of_fixes_J hcfg hnb hN hxBs hJK hcard hfA (hfJ _ hJ1))
      hfx

end Config

theorem ggNbrInnerWeylOn_triD4Residual_of_known (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hG : GGNbrGraphInput) (hKG : GGNbrKGFieldTriD4ThreeLine) :
    GGNbrInnerWeylOn fun p lab => GGNbrWeylResidualOpenLabel p lab ∧ lab.tag = .triD4 := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN hxK P hP
  obtain ⟨hK, lab, hlab, hraw⟩ := hG G p B Bs x L D J hcfg y K hnb hN P hP
  by_cases hSl : GGNbrWeylResidualOpenLabel p lab ∧ lab.tag = .triD4
  · obtain ⟨⟨hres, hns⟩, htag⟩ := hSl
    have hfam : p = 3 ∧ 2 ≤ lab.n := by
      rcases hres.2 with ⟨ht, -⟩ | ⟨-, hp3, hn2⟩
      · rw [htag] at ht
        cases ht
      · exact ⟨hp3, hn2⟩
    obtain ⟨hp3, hn2⟩ := hfam
    have h3 : 3 ∣ 2 ^ lab.n - 1 := by
      by_contra h
      exact hns ⟨htag, hp3, hn2, h⟩
    subst hp3
    refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ (hKG lab hlab htag hn2 h3 _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hPθ, hgr⟩, hQ⟩
    refine ⟨hs, hna, θ, hPθ, fun _ hxI => ?_⟩
    have hBsIF : ∀ (b : G) (hb : b ∈ Bs),
        ggLAut K θ ⟨b, hN hb⟩ ∈ Subgroup.closure (I ∪ F) := by
      intro b hb
      obtain ⟨u, hu, f, hf, e⟩ := hgr b hb
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl hu))
        (Subgroup.closure_mono Set.subset_union_right hf)
    exact ggNbrInnerWeyl_of_ggTriD4LineKnown hL hPJ hcfg hnb hK θ hN hBsIF hxK hxI (hQ hs hna)
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ, -⟩
    exact ⟨hs, hna, θ, hPθ, fun hS => absurd hS hSl⟩

end CFSG.StandardType

end
