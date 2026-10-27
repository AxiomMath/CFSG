module

public import CFSG.Quasithin.EmptyFaithful.SBd18Fin
public import CFSG.Quasithin.EmptyFaithful.SBd18Pk
public import CFSG.Quasithin.EmptyFaithful.SBd18OutProof
public import CFSG.Quasithin.EmptyFaithful.SBd17Main
public import CFSG.Quasithin.EmptyFaithful.SBd16Main
public import CFSG.Quasithin.EmptyFaithful.SBd15Step
public import CFSG.Quasithin.EmptyFaithful.SzN15Final
public import CFSG.Quasithin.EmptyFaithful.R3cRankOne
public import CFSG.Quasithin.EmptyFaithful.S153D25
public import CFSG.Quasithin.EmptyFaithful.S153D45
public import CFSG.Quasithin.EmptyFaithful.S153D59
public import CFSG.Quasithin.EmptyFaithful.SzN10A5
public import CFSG.Quasithin.EmptyFaithful.SzN11ZL
public import CFSG.Quasithin.EmptyFaithful.SzN12Hat
public import CFSG.Quasithin.EmptyFaithful.SzN9A5Short

public section

namespace CFSG.Quasithin.SBd18

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def Input15338FusionF : Prop :=
  A318Facts → ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    SBd14.RestHyp T Mc M V₁ V₂ Yp I L t → I = Subgroup.normalizer (V₁ : Set G) →
    (∀ v ∈ V₁, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ I) →
    (∀ (g x : G), x ∈ V₁ → x ≠ 1 → g⁻¹ * x * g ∈ V₁ → g ∈ Subgroup.normalizer (V₁ : Set G)) →
    I ⊓ Subgroup.centralizer (L : Set G) = V₁ → L.relIndex I = 12 → I = L ⊔ Yp ⊔ Sgp153 T V₁ →
    ∀ (X : Subgroup G) (τ f : G), X ≤ Yp → IsPGroup 3 ↥X → ¬ 3 ∣ X.relIndex Yp →
      Sgp153 T V₁ ⊓ L ⊓ Subgroup.centralizer (X : Set G) = ⊥ →
      τ ∈ Sgp153 T V₁ → f ∈ Sgp153 T V₁ → τ ∈ Subgroup.normalizer (X : Set G) →
      f ∈ Subgroup.normalizer (X : Set G) → τ * τ = 1 → f * f = 1 → τ * f = f * τ → τ ≠ 1 → f ≠ 1 →
      τ ≠ f →
      (∀ s ∈ Sgp153 T V₁ ⊓ Subgroup.normalizer (X : Set G), s = 1 ∨ s = τ ∨ s = f ∨ s = τ * f) →
      (∀ x ∈ X, f * x * f⁻¹ = x⁻¹) → (∀ v ∈ V₁, (τ * f) * v = v * (τ * f)) →
      (∃ v ∈ V₁, τ * v ≠ v * τ) → τ * f ∉ L →
      Subgroup.centralizer (V₁ : Set G) = L ⊔ Subgroup.zpowers (τ * f) →
      (∃ t₀ ∈ T ⊓ Subgroup.normalizer (X : Set G),
        t₀ * τ * t₀⁻¹ = τ * f ∧ t₀ * (τ * f) * t₀⁻¹ = τ) →
      (∀ g : G, g⁻¹ * τ * g ∉ V₁) →
      (∀ z : G, z ≠ 1 → z * z = 1 → (∀ g ∈ T, g * z = z * g) → ∀ g : G, g⁻¹ * τ * g ≠ z) →
      (∃ Lτ Lf : Subgroup G, SBd14.CoreProps L V₁ I Lτ τ ∧ SBd14.CoreProps L V₁ I Lf f ∧
        ((Nat.card (↥Lτ ⧸ Subgroup.center ↥Lτ) = 168 ∧
            Nat.card (↥Lf ⧸ Subgroup.center ↥Lf) = 60) ∨
          (Nat.card (↥Lτ ⧸ Subgroup.center ↥Lτ) = 60 ∧
            Nat.card (↥Lf ⧸ Subgroup.center ↥Lf) = 168))) →
      ∀ g : G, g⁻¹ * τ * g ≠ f

end CFSG.Quasithin.SBd18

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.false_of_residues_f (h312 : A312ForSQTK) (h318 : A318Facts)
    (kC : SBd16.Input15338CentV) (kF : SBd18.Input15338FusionF)
    (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113)
    (hI : I = Subgroup.normalizer (V₁ : Set G)) : False := by
  classical
  have hK1 := kC h312 G T Mc M V₁ V₂ Yp I L t r hI
  have hTI := r.V₁_TI h113 hI hK1
  have hOut : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 →
      SBd18.OutFacts K := fun K _ _ _ hK => SBd18.outFacts hK
  obtain ⟨X, τ, f, hXY, hX3, hXidx, hreg, hτS, hfS, hτN, hfN, hττ, hff, hτf, hτ1, hf1, hτf',
    hcl, hinv, hcent, hmove, ⟨t₀, ht₀N, ht₀τ, ht₀f⟩, g, hg⟩ := r.exists_fusion_package_t0 h113
  have hσ1 : τ * f ≠ 1 := by
    intro h
    apply hτf'
    calc τ = f⁻¹ := eq_inv_of_mul_eq_one_left h
      _ = f := inv_eq_of_mul_eq_one_right hff
  have hσL : τ * f ∉ L :=
    r.not_mem_L_of_regular hXY hX3 hreg (Subgroup.mul_mem _ hτS hfS) (Subgroup.mul_mem _ hτN hfN) hσ1
  have hcl' : Subgroup.centralizer (V₁ : Set G) = L ⊔ Subgroup.zpowers (τ * f) :=
    r.centralizer_V₁_eq h113 hK1 hτS hττ hmove (Subgroup.mul_mem _ hτS hfS) hcent hσL
  have hNV := r.not_conj_V₁_of_swap h113 hOut hI hK1 hTI hτS hfS hττ hff hτf hcent hmove hσL hcl'
    ht₀τ
  have hNz : ∀ z : G, z ≠ 1 → z * z = 1 → (∀ g ∈ T, g * z = z * g) → ∀ g : G, g⁻¹ * τ * g ≠ z :=
    fun z hz1 hz2 hzT => r.not_conj_z h113 hOut hK1 hτS hfS hττ hff hτf hcent hmove hσL hzT hz1 hz2
  have hcore := r.exists_core_pair h113 hOut hτS hfS hττ hff hτf hcent hmove hσL
  have hnf := kF h318 G T Mc M V₁ V₂ Yp I L t r hI hK1 hTI (r.centralizer_I_L h113)
    (r.relIndex_L_I h113) (r.I_eq_sup h113) X τ f hXY hX3 hXidx hreg hτS hfS hτN hfN hττ hff hτf hτ1
    hf1 hτf' hcl hinv hcent hmove hσL hcl' ⟨t₀, ht₀N, ht₀τ, ht₀f⟩ hNV hNz hcore
  have hno := r.noFusion_of_notconj_f h113 hOut hI hK1 hTI hτS hfS hττ hff hτf hcent hmove hσL hcl'
    ht₀τ hnf g
  exact hg.elim hno.1 hno.2

end CFSG.Quasithin.SBd14

namespace CFSG.Quasithin.SBd18

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_restHyp_f (F : SBd15.Frontier15338) (h312 : A312ForSQTK) (h318 : A318Facts)
    (kC : SBd16.Input15338CentV) (kF : Input15338FusionF) :
    ∀ (n : ℕ) (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
      Nat.card G - Nat.card ↥I = n → SBd14.RestHyp T Mc M V₁ V₂ Yp I L t → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T Mc M V₁ V₂ Yp I L t hn r
    have hV : V₁ = centerOf L := r.V₁_eq_center F.h113
    have hII₁ : I ≤ Subgroup.normalizer (V₁ : Set G) := SBd14.le_normalizer_of_eq_center r.hNL hV
    by_cases hI : Subgroup.normalizer (V₁ : Set G) ≤ I
    · exact r.false_of_residues_f h312 h318 kC kF F.h113 (le_antisymm hII₁ hI)
    · obtain ⟨W₁, W₂, L₁, r₁⟩ := SBd15.exists_next F r
      have hlt : Nat.card ↥I < Nat.card ↥(Subgroup.normalizer (V₁ : Set G)) := by
        by_contra hge
        exact hI (Subgroup.eq_of_le_of_card_ge hII₁ (not_lt.mp hge)).ge
      have hle : Nat.card ↥(Subgroup.normalizer (V₁ : Set G)) ≤ Nat.card G :=
        Subgroup.card_le_card_group _
      exact ih (Nat.card G - Nat.card ↥(Subgroup.normalizer (V₁ : Set G))) (by omega)
        T Mc M W₁ W₂ Yp _ L₁ t rfl r₁

theorem input15338RestV_of_residues_f (F : SBd15.Frontier15338) (h312 : A312ForSQTK)
    (h318 : A318Facts) (kC : SBd16.Input15338CentV) (kF : Input15338FusionF) :
    SBd14.Input15338RestV := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hL0 hn2 hYL hy hY hNL hYY hB hBM hQV h1 h2 h3 h4 _hV
  exact false_of_restHyp_f F h312 h318 kC kF _ T Mc M V₁ V₂ Yp I L t rfl
    ⟨c, hL0, hn2, hYL, hy, hY, hNL, hYY, hB, hBM, hQV, h1, h2, h3, h4⟩

theorem input15338Rest_of_residues_f (F : SBd15.Frontier15338) (h312 : A312ForSQTK)
    (h318 : A318Facts) (kC : SBd16.Input15338CentV) (kF : Input15338FusionF) :
    SBd9.Input15338Rest :=
  SBd14.input15338Rest_of_restV F.h113 (input15338RestV_of_residues_f F h312 h318 kC kF)

theorem input15338_of_residues_f (F : SBd15.Frontier15338) (hrank : Lemma122Rank)
    (h312 : A312ForSQTK) (h318 : A318Facts) (kC : SBd16.Input15338CentV) (kF : Input15338FusionF) :
    Input15338 :=
  SBd9.input15338_of_rest F.h113 F.hA37 F.hA38 hrank F.kR
    (input15338Rest_of_residues_f F h312 h318 kC kF)

theorem stage15344_of_named_stageB_inputs_final18
    (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hcover : AsA36NoOddCover)
    (h15 : Input15315Two) (h16 : Input15316One)
    (kR : Input21Rank) (kP : Input21ProperRank)
    (k17L : ThreeRankBlocks) (k17B : SolvOvergroupsThreePrime) (k17T : ThetaEqComponent)
    (k19C : Lin2QuotIsLin2OrA5) (k19F : A5FixedPoints) (k19O : A5OddCommuting)
    (k20N : SL3Sp4NotA38Type) (hB51 : AsB51) (hA21 : AsA21SQTKSection)
    (k20B : SolvOvergroupsInBorel) (k20C : RankTwoMaxParabolics)
    (k21N : A7NotA38Type) (k21T : HatA6ProperThreePart) (k21E : ExcA7NoS3Section)
    (k21O : OrdA7ConfigNoNine) (k21S : HatA6SwapLocal)
    (h23 : Input15323) (h24 : Input15324M)
    (h26 : Input15326Two) (h27 : Input15327) (h28 : Input15328)
    (h30 : Input15330) (h31 : Input15331) (h32 : Input15332) (hc : Input15325Count)
    (h33 : Input15333) (h34 : Input15334) (h36 : Input15336One)
    (h37 : Input15337) (kC : SBd16.Input15338CentV) (kF : Input15338FusionF) (h39 : Input15339)
    (h40 : Input15340)
    (hcl : Input15335Close) (hr : Input15343Reduce) (he : Input15343Elim)
    (hA39 : A39ForSQTK) (hrank : Lemma122Rank) (h312 : A312ForSQTK) (h318 : A318Facts) :
    Stage15344 :=
  have h5 : Input15311FiveII := S153D.input15311FiveII_of_stages h11 h113
  have h13 : Stage15313 :=
    stage15313_of_named_stageB_inputs7M3 h11 h113 hC27 hA37 hA38 hcover h15 h16 h36 kR kP k17L k17B
      k17T
      (lin2Setup_of_noStar hA37 hA38 (lin2SetupNoStar_of_inner hA37 hA38 k17L (lin2YInner_holds hA37 hA38)))
      (lin2RLSylow_holds hA37 hA38) (lin2ZLInYL_holds hA37 hA38) k19C
      (a5Setup_of_noStar hA37 hA38 (a5SetupNoStar_of_short hA37 hA38 a5IsShort_holds)) k19F k19O k20N
      (SzN15.noGraphAutOnFFModule3_of_b51 hB51 hA21 hcover)
      k20B k20C k21N k21T k21E k21O (hatA6VleU_holds h113) k21S h23 h24
  have h25 : Stage15325 :=
    stage15325_of_blocks h113 h13
      (stage15325One_of_inputs h11 h113 hA37 hA38 h5 h26 h27 h28 h30 h31 h32 hc)
  have h8 : Input15311Eight := S153D.input15311Eight_of_stages h113
  have h38 : Input15338 :=
    input15338_of_residues_f ⟨h11, h113, h25, h34, h36, h37, hA37, hA38, hA39, rankOneFamilies153_holds,
      rankTwoFamilies153_holds⟩ hrank h312 h318 kC kF
  stage15344_of_blocks h25
    (stageComponentCase_of_blocks h113
      (stageComponentTwo_of_inputs h11 h113 h25 h8 h33 h34 h36 h37 h38 h39 h40 hcl)
      (stageComponentOne_of_inputs h11 h113 h25 h8 h5 h33 h34
        (S153D.input15343Open_of_notA4 h113 (S153D.input15343NotA4_proved h113)) hr he))

end CFSG.Quasithin.SBd18
