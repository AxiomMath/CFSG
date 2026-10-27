module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTwE6Prop87
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Holds
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc3
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcReduction
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB

variable {G : Type} [Group G] [Finite G]

private theorem sd_mem_zpowers_ggGamma_x_of_fixes_J {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hxBs : x ∈ Bs)
    (hJK : J ≤ K) (hBeq : B = Bs) {f : MulAut K}
    (hf : f ∈ (ggGamma K hN).range) (hfJ : ∀ l ∈ J.comap K.subtype, f l = l) :
    f ∈ Subgroup.zpowers (ggGamma K hN ⟨x, hxBs⟩) := by
  classical
  subst hBeq
  have hS : LargeEvenSHat p B y K := hnb.1
  have hyB : y ∈ B := hS.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hS.2.2.2.1
  obtain ⟨b, rfl⟩ : f ∈ (ggGamma K hN).range := hf
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
  have hγy : ggGamma K hN ⟨y, hyB⟩ = 1 :=
    (ggGamma_eq_one_iff K hN ⟨y, hyB⟩).mpr hyC
  have hDM : D ≤ ((Subgroup.zpowers (ggGamma K hN ⟨x, hxBs⟩)).comap (ggGamma K hN)).map
      B.subtype := by
    rw [hnb.2.1, Subgroup.closure_le]
    rintro g (hg | hg)
    · rw [hg]
      exact ⟨⟨x, hxBs⟩, Subgroup.mem_zpowers _, rfl⟩
    · rw [Set.mem_singleton_iff.mp hg]
      refine ⟨⟨y, hyB⟩, ?_, rfl⟩
      show ggGamma K hN ⟨y, hyB⟩ ∈ Subgroup.zpowers (ggGamma K hN ⟨x, hxBs⟩)
      rw [hγy]
      exact one_mem _
  obtain ⟨b', hb', hb'b⟩ := hDM hbD
  have hbb' : b' = ⟨(b : G), b.2⟩ := Subtype.ext hb'b
  rw [hbb'] at hb'
  exact hb'

theorem ggTwE6SCFourSetting_of_caseII (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hsc : GGTorusSelfCent 3 (ggGamma K hN).range)
    (hBeq : B = Bs) (h4 : Nat.card (ggGamma K hN).range = 3 ^ 4)
    {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∃ _ : J ≤ K, GGTwE6SCFourSetting I (ggQuotHom θ) (ggGamma K hN).range
      (ggGamma K hN ⟨x, hcfg.tableB_facts.2.2.1⟩) (J.subgroupOf K) := by
  classical
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a :=
    fun a ha b hb => CFSG.Open.IsElemAbelian.comm hBs ha hb
  have hIH : GGThmIHyp 3 B x L := hcfg.1
  unfold GGThmIHyp at hIH
  obtain ⟨-, -, -, -, -, -, hS, hst⟩ := hIH
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := le_normalizer_of_stdSub hS hst hcfg.2.2.1
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) := by
    rw [← hBeq]
    exact hBJ
  obtain ⟨hJK, hJ1⟩ := isComponentOf_comap_ggFix_ggGamma_x hL hPJ hcfg hnb hN hxBs
  have hBp : ∀ b : Bs, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (CFSG.Open.IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian 3 (ggGamma K hN).range := isElemAbelian_range hBc hBp (ggGamma K hN)
  refine ⟨hJK, ?_⟩
  unfold GGTwE6SCFourSetting
  refine ⟨hA, ?_, h4, hsc, ⟨⟨x, hxBs⟩, rfl⟩, ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta K θ hN b, ggBeta_mem K θ hN h3 b, fun l => ggBeta_ggQuotHom K hN θ b l⟩
  ·
    intro h1
    rw [ggGamma_eq_one_iff] at h1
    exact not_mem_centralizer_of_nbr hnb h1
  ·
    exact hJ1
  ·
    intro a ha l hl
    obtain ⟨b, rfl⟩ := ha
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    rw [ggGamma_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hBsJ b.2) (l : G)).mp hl
  ·
    rintro a ⟨b, rfl⟩ hfix
    exact sd_mem_zpowers_ggGamma_x_of_fixes_J hcfg hnb hN hxBs hJK hBeq
      (f := ggGamma K hN b) ⟨b, rfl⟩ hfix

end CFSG.StandardType

end
