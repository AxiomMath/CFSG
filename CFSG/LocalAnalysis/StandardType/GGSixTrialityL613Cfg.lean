module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613CfgSplit
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KG
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneNine
public import CFSG.LocalAnalysis.StandardType.GGHypSixD4BstarRankInner
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KGConj
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.StandardType.Triality
  Multiplicative CFSG.StandardType.D4Rank CFSG.StandardType.OrthD4 CFSG.StandardType.L613KG

namespace L613Cfg

section Sub

variable {G : Type} [Group G]

theorem isSubnormal_inf_right {A B : Subgroup G} (h : CFSG.Assembly.IsSubnormal A B)
    (X : Subgroup G) : CFSG.Assembly.IsSubnormal (A ⊓ X) (B ⊓ X) :=
  h.inf X

theorem isComponentOf_comap {Γ : Type} [Group Γ] {ι : Γ →* G} (hinj : Function.Injective ι)
    {J H : Subgroup G} (hJH : J ≤ H) (hsub : CFSG.Assembly.IsSubnormal J H)
    (hq : CFSG.Assembly.IsQuasisimple J) (hJι : J ≤ ι.range) :
    CFSG.Assembly.IsComponentOf (J.comap ι) (H.comap ι) := by
  refine ⟨Subgroup.comap_mono hJH,
    CFSG.LocalAnalysis.ComponentInitial.assembly_isSubnormal_comap ι hsub, ?_⟩
  rw [CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (comapEquiv hinj hJι).symm hq

end Sub

end L613Cfg

section Main

open L613Cfg

theorem ggSixTrialityDClassThreeInput_of_omegaFour (hOF : GGOmegaFourFactorInput) :
    GGSixTrialityDClassThreeInput := by
  intro G _ _ B Bs x L D J f ψ hctx hC y hy hyo htri
  have h3f : 3 ∣ 2 ^ f - 1 := htri.2.2.2.1
  have hpres := hctx.presents
  have hf1 : 1 ≤ f := hpres.1.1.2.1
  have hKc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK3 : 3 ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hKc]; exact h3f
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι, hinj, hrange, hιψ⟩ := exists_om8_embedding hpres
  have hcfg : GGConfig 3 B Bs x L D J := hctx.config
  have hBι : Bs ≤ ι.range := fun b hb => by
    rw [hrange]
    exact D4Bstar.mem_ggG0_of_psiInnerDiag hcfg hpres hctx.bstar_le_normalizer hb
      (hctx.2.2.2.2.2.2.1.2 b hb)
  obtain ⟨-, hBs, -, -, h81⟩ := hcfg.tableB_facts
  obtain ⟨ι₁, hinj₁, hrange₁, hfr, hdim⟩ :=
    exists_frame8 hBs hctx.bstar.2.2.2 h81 ι hinj hBι
  have hBBs : B ≤ Bs := hctx.bstar.1
  have hcardBs : Nat.card Bs = 3 ^ 4 := by
    rw [← hrange₁, NoOffUO.card_range_eq hinj₁]
  have hBeq : B = Bs := by
    refine Subgroup.eq_of_le_of_card_ge hBBs ?_
    have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hctx.sstar.1.2.1
    have h4 : 4 ≤ LargeEvenTwoLocalRank 3 G := hctx.beta.2.2.2
    rw [hcardBs, hBc]
    exact Nat.pow_le_pow_right (by norm_num) h4
  have hDBs : D ≤ Bs := hctx.d_le_bstar
  let Dbar : AddSubgroup (Fin 4 → ZMod 3) :=
    { carrier := {s | ι (ι₁ (ofAdd s)) ∈ D}
      add_mem' := fun {s t} hs ht => by
        change ι (ι₁ (ofAdd (s + t))) ∈ D
        rw [ofAdd_add, map_mul, map_mul]
        exact D.mul_mem hs ht
      zero_mem' := by
        change ι (ι₁ (ofAdd 0)) ∈ D
        rw [ofAdd_zero, map_one, map_one]
        exact D.one_mem
      neg_mem' := fun {s} hs => by
        change ι (ι₁ (ofAdd (-s))) ∈ D
        rw [ofAdd_neg, map_inv, map_inv]
        exact D.inv_mem hs }
  have hmemD : ∀ s, s ∈ Dbar ↔ ι (ι₁ (ofAdd s)) ∈ D := fun s => Iff.rfl
  have hDsurj : ∀ d ∈ D, ∃ s ∈ Dbar, ι (ι₁ (ofAdd s)) = d := by
    intro d hd
    obtain ⟨s, hs⟩ : d ∈ (ι.comp ι₁).range := by rw [hrange₁]; exact hDBs hd
    refine ⟨toAdd s, ?_, ?_⟩
    · rw [hmemD, ofAdd_toAdd]
      change (ι.comp ι₁) s ∈ D
      rw [hs]
      exact hd
    · rw [ofAdd_toAdd]
      exact hs
  have hcardD : Nat.card Dbar = 9 := by
    rw [← show Nat.card D = 9 by rw [hctx.card_d]; norm_num]
    refine Nat.card_eq_of_bijective (fun s => ⟨ι (ι₁ (ofAdd s.1)), s.2⟩) ⟨fun s t hst => ?_,
      fun d => ?_⟩
    · have h := congrArg Subtype.val hst
      exact Subtype.ext (ofAdd.injective (hinj₁ h))
    · obtain ⟨s, hs, hsd⟩ := hDsurj d.1 d.2
      exact ⟨⟨s, hs⟩, Subtype.ext hsd⟩
  have hcent : (Subgroup.centralizer (D : Set G)).comap ι =
      Subgroup.centralizer ((fun s => ι₁ (ofAdd s)) '' (Dbar : Set (Fin 4 → ZMod 3))) := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · rintro hg _ ⟨s, hs, rfl⟩
      apply hinj
      rw [map_mul, map_mul]
      exact hg _ hs
    · intro hg d hd
      obtain ⟨s, hs, rfl⟩ := hDsurj d hd
      rw [← map_mul, ← map_mul, hg _ ⟨s, hs, rfl⟩]
  have hstd := hctx.stdSub.1
  have hxD : x ∈ D := hstd.2.2.2.1
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hstd.2.2.2.2.2.1
  have hLcomp : IsComponentOf L (Subgroup.centralizer {x}) := hctx.sstar.2.2.2.1
  have hCDx : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer {x} :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxD)
  have hLsub : IsSubnormal (L ⊓ Subgroup.centralizer (D : Set G))
      (Subgroup.centralizer (D : Set G)) := by
    have h := isSubnormal_inf_right hLcomp.2.1 (Subgroup.centralizer (D : Set G))
    rwa [inf_eq_right.mpr hCDx] at h
  have hJsub : IsSubnormal J (Subgroup.centralizer (D : Set G)) :=
    CFSG.LocalAnalysis.ComponentInitial.assembly_isSubnormal_trans hJcomp.2.1 hLsub
  have hLG₀ : L ≤ ggG0 3 B x L D J := le_sup_left
  have hJι : J ≤ ι.range := by
    rw [hrange]
    exact hJcomp.1.trans (inf_le_left.trans hLG₀)
  have hJbar : IsComponentOf (J.comap ι)
      (Subgroup.centralizer ((fun s => ι₁ (ofAdd s)) '' (Dbar : Set (Fin 4 → ZMod 3)))) := by
    rw [← hcent]
    exact isComponentOf_comap hinj (hJcomp.1.trans inf_le_right) hJsub hJcomp.2.2 hJι
  have hCJ : ∀ s, ι₁ (ofAdd s) ∈ Subgroup.centralizer ((J.comap ι : Subgroup _) : Set _) →
      s ∈ Dbar := by
    intro s hs
    rw [hmemD, hstd.2.2.2.2.2.2]
    refine ⟨?_, ?_⟩
    · rw [hBeq, ← hrange₁]
      exact ⟨ofAdd s, rfl⟩
    · show ι (ι₁ (ofAdd s)) ∈ Subgroup.centralizer (J : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      obtain ⟨j', rfl⟩ := hJι hj
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hs) j' hj]
  obtain ⟨t, htD, ht3⟩ := exists_supp_three hOF hK3 hfr hdim hcardD hJbar hCJ
  have hd2 : omFixDim (ι₁ (ofAdd t)) = 2 := by
    have := hdim t
    rw [ht3] at this
    omega
  refine ⟨ι (ι₁ (ofAdd t)), htD, fun h1 => ?_, modelEquiv8.symm (ι₁ (ofAdd t)), ?_, ?_⟩
  · have h1' : ι₁ (ofAdd t) = 1 := hinj (by rw [h1, map_one])
    rw [h1', omFixDim_one] at hd2
    exact absurd hd2 (by norm_num)
  · rw [← hιψ, ← modelEquiv8_apply, MulEquiv.apply_symm_apply]
  · rw [← modelEquiv8_apply, MulEquiv.apply_symm_apply]
    exact hd2

end Main

end CFSG.StandardType
