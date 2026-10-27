module

public import CFSG.Quasithin.Vol2.Ch3xD15Proved
public import CFSG.Quasithin.Background.SimsD1TwelveGen
public import CFSG.Quasithin.Background.SimsD1FourGen
public import CFSG.Quasithin.Background.SimsD1FourGeneral
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.Quasithin.Background.MS09.D1Transport

public section

namespace CFSG.ASVolI.ChD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

structure HypD11 (G₁ G₂ T V M₂ : Subgroup G) : Prop where
  finite₁ : Finite G₁
  finite₂ : Finite G₂
  sylow₁ : IsSylowTwoOf T G₁
  sylow₂ : IsSylowTwoOf T G₂
  reduced : IsTwoReducedIn G₁ V
  nontrivial : V ≠ ⊥
  unique_max : IsUniqueMaxOver G₂ T M₂
  centralizer : pCoreOf 2 G₁ = T ⊓ Subgroup.centralizer (V : Set G)
  no_normal : ∀ N : Subgroup G, N ≤ pCoreOf 2 G₁ → (N.subgroupOf (G₁ ⊔ G₂)).Normal → N = ⊥

@[expose] noncomputable def qSub (H V : Subgroup G) (hH : Finite H) (hVH : V ≤ H)
    (hE : IsElemAbelian 2 V) : WithTop ℚ :=
  haveI : Finite V := haveI := hH; Finite.of_injective (Subgroup.inclusion hVH)
    (Subgroup.inclusion_injective hVH)
  @qOf ↥V (commGroupOfElemAbelian hE) this (autOn H V)

@[expose] noncomputable def mRel (N L : Subgroup G) : ℕ := padicValNat 2 (L.relIndex N)

@[expose] def secFix (A N L : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ N ∧ x ∈ Subgroup.normalizer (L : Set G) ∧ ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ L}
  one_mem' := ⟨N.one_mem, Subgroup.one_mem _, fun a _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxN, hxL, hx⟩ ⟨hyN, hyL, hy⟩
    refine ⟨N.mul_mem hxN hyN, Subgroup.mul_mem _ hxL hyL, fun a ha => ?_⟩
    have h1 := hx a ha
    have h2 := (Subgroup.mem_normalizer_iff.mp hxL _).mp (hy a ha)
    have : a * (x * y) * a⁻¹ * (x * y)⁻¹ =
        (a * x * a⁻¹ * x⁻¹) * (x * (a * y * a⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [this]
    exact L.mul_mem h1 h2
  inv_mem' := by
    rintro x ⟨hxN, hxL, hx⟩
    refine ⟨N.inv_mem hxN, Subgroup.inv_mem _ hxL, fun a ha => ?_⟩
    have h1 := L.inv_mem (hx a ha)
    have h2 := (Subgroup.mem_normalizer_iff''.mp hxL _).mp h1
    have : a * x⁻¹ * a⁻¹ * (x⁻¹)⁻¹ = x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x := by group
    rw [this]
    exact h2

@[expose] def conjBy (X : Subgroup G) (g : G) : Subgroup G := X.map (MulAut.conj g⁻¹).toMonoidHom

@[expose] def NontrivQuadOn (A U : Subgroup G) : Prop :=
  ⁅⁅U, A⁆, A⁆ = ⊥ ∧ ⁅U, A⁆ ≠ ⊥

@[expose] def IsMinNontrivMod (R R₂ A : Subgroup G) : Prop :=
  IsMaxElemAbelian R A ∧ ¬ A ≤ R₂ ∧
    ∀ A' : Subgroup G, IsMaxElemAbelian R A' → ¬ A' ≤ R₂ → A' ⊔ R₂ ≤ A ⊔ R₂ → A' ⊔ R₂ = A ⊔ R₂

@[expose] def IsProdA3Blocks (H X : Subgroup G) : Prop :=
  ∃ S : Finset (Subgroup G), (∀ L ∈ S, IsBlock2 H L ∧ IsAltType L 3) ∧ X = ⨆ L ∈ S, L

end CFSG.ASVolI.ChD

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChD

@[expose] def D_1_2 : Prop :=
  ∀ (G : Type) [Group G] (G₁ G₂ T V M₂ : Subgroup G) (h : HypD11 G₁ G₂ T V M₂),
    (1 : WithTop ℚ) < qSub G₁ V h.finite₁ h.reduced.1 h.reduced.2.2.1 →
    (V ≤ pCoreOf 2 G₂ → IsElemAbelian 2 (conjClosure V G₂)) ∧
    (thompsonJ T = thompsonJ (pCoreOf 2 G₁) ∧
      thompsonJ (pCoreOf 2 G₁) = thompsonJ (pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂)) ∧
    (¬ G₂ ≤ Subgroup.normalizer (T : Set G) ∧ ¬ thompsonJ (pCoreOf 2 G₁) ≤ pCoreOf 2 G₂) ∧
    IsMinParabolicOf G₂ G₂ ∧
    (∀ (W : Subgroup G) (hWG : W ≤ G₂) (hWE : IsElemAbelian 2 W),
      G₂ ≤ Subgroup.normalizer (W : Set G) → W ≤ pCoreOf 2 G₂ →
      pCoreOf 2 G₂ ≤ Subgroup.centralizer (W : Set G) →
      G₂ ⊓ Subgroup.centralizer (W : Set G) ≤ M₂ →
      IsTwoReducedIn G₂ W ∧ (1 : WithTop ℚ) ≤ qSub G₂ W h.finite₂ hWG hWE)

@[expose] def D_1_2_five_general : Prop :=
  ∀ (G : Type) [Group G] (G₁ G₂ T V M₂ : Subgroup G) (h : HypD11 G₁ G₂ T V M₂),
    (1 : WithTop ℚ) < qSub G₁ V h.finite₁ h.reduced.1 h.reduced.2.2.1 →
    ∀ (W : Subgroup G) (hWG : W ≤ G₂) (hWE : IsElemAbelian 2 W),
      G₂ ≤ Subgroup.normalizer (W : Set G) → W ≤ pCoreOf 2 G₂ →
      pCoreOf 2 G₂ ≤ Subgroup.centralizer (W : Set G) →
      G₂ ⊓ Subgroup.centralizer (W : Set G) ≤ M₂ →
      (1 : WithTop ℚ) ≤ qSub G₂ W h.finite₂ hWG hWE

theorem as_D_1_2_five_general : D_1_2_five_general := by
  intro G _ G₁ G₂ T V M₂ h hq W hWG hWE hG₂W hWR hRC hCM
  haveI := h.finite₁
  haveI := h.finite₂
  exact CFSG.Quasithin.MS09.d12_five_general
    ⟨h.sylow₁, h.sylow₂, h.reduced, h.nontrivial, h.unique_max, h.centralizer, h.no_normal⟩ hq
    W hWG hWE hG₂W hWR hRC hCM

section as_D_1_2

theorem as_D_1_2
    : D_1_2 := by
  intro G _ G₁ G₂ T V M₂ h hq
  haveI := h.finite₁
  haveI := h.finite₂
  obtain ⟨c1, c2, c3, c4, c5⟩ := CFSG.Quasithin.SimsD1.TwelveGen.d12_general
    CFSG.Quasithin.b69One_proved
    ⟨h.sylow₁, h.sylow₂, h.reduced, h.nontrivial, h.unique_max, h.centralizer, h.no_normal⟩ hq
  exact ⟨c1, c2, c3, c4, fun W hWG hWE hG₂W hWR hRC hCM =>
    ⟨(c5 W hWG hWE hG₂W hWR hRC hCM).1,
      as_D_1_2_five_general G G₁ G₂ T V M₂ h hq W hWG hWE hG₂W hWR hRC hCM⟩⟩

end as_D_1_2

@[expose] def D_1_3 : Prop :=
  ∀ (G : Type) [Group G] (G₁ G₂ T V M₂ : Subgroup G) (h : HypD11 G₁ G₂ T V M₂),
    (1 : WithTop ℚ) < qSub G₁ V h.finite₁ h.reduced.1 h.reduced.2.2.1 →
    V ≤ pCoreOf 2 G₂ →
    ∀ c : ℕ, 2 ≤ c → IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c →
      IsElemAbelian 2 (conjClosure V G₂) ∧
      pCoreOf 2 G₂ ⊓ Subgroup.centralizer (conjClosure V G₂ : Set G) =
        twoPrimeResidual (G₂ ⊓ Subgroup.centralizer (conjClosure V G₂ : Set G)) ∧
      qSub G₁ V h.finite₁ h.reduced.1 h.reduced.2.2.1 ≤ 2 ∧
      ((∀ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A ↔ IsMaxElemAbelian T A) ∧
        (∃ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A ∧ NontrivQuadOn A (conjClosure V G₂)) ∧
        (∀ A : Subgroup G, IsMinNontrivMod (pCoreOf 2 G₁) (pCoreOf 2 G₂) A →
          ∃ A' : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A' ∧
            A' ⊔ pCoreOf 2 G₂ = A ⊔ pCoreOf 2 G₂ ∧ A' ≤ A ⊔ conjClosure V G₂ ∧
            NontrivQuadOn A' (conjClosure V G₂))) ∧
      (qSub G₁ V h.finite₁ h.reduced.1 h.reduced.2.2.1 = 2 →
        c = 2 ∧
        ∀ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A → NontrivQuadOn A (conjClosure V G₂) →
          2 * mRel A (A ⊓ pCoreOf 2 G₂) =
            mRel (conjClosure V G₂) (conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G)) ∧
          mRel (conjClosure V G₂) (conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G)) =
            2 * mRel (A ⊓ pCoreOf 2 G₂)
              (A ⊓ pCoreOf 2 G₂ ⊓ Subgroup.centralizer (conjClosure V G₂ : Set G)) ∧
          (∀ g ∈ G₂, ⁅conjBy V g, A ⊓ pCoreOf 2 G₂⁆ ≠ ⊥ →
            2 * mRel (A ⊓ pCoreOf 2 G₂)
                (A ⊓ pCoreOf 2 G₂ ⊓ Subgroup.centralizer (conjBy V g : Set G)) =
              mRel (conjBy V g)
                (conjBy V g ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G))) ∧
          (∀ L N : Subgroup G, IsChiefStep G₂ (conjClosure V G₂) L N → ¬ IsCentralStep G₂ L N →
            mRel A (A ⊓ pCoreOf 2 G₂) = mRel N (secFix A N L)) ∧
          conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G) =
            conjClosure V G₂ ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G))

@[expose] def D_1_3_one_three_general : Prop :=
  ∀ (G : Type) [Group G] (G₁ G₂ T V M₂ : Subgroup G) (h : HypD11 G₁ G₂ T V M₂),
    (1 : WithTop ℚ) < qSub G₁ V h.finite₁ h.reduced.1 h.reduced.2.2.1 →
    V ≤ pCoreOf 2 G₂ →
    ∀ c : ℕ, 2 ≤ c → IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c →
      qSub G₁ V h.finite₁ h.reduced.1 h.reduced.2.2.1 ≤ 2 ∧
      (qSub G₁ V h.finite₁ h.reduced.1 h.reduced.2.2.1 = 2 →
        c = 2 ∧
        ∀ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 G₁) A → NontrivQuadOn A (conjClosure V G₂) →
          2 * mRel A (A ⊓ pCoreOf 2 G₂) =
            mRel (conjClosure V G₂) (conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G)) ∧
          mRel (conjClosure V G₂) (conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G)) =
            2 * mRel (A ⊓ pCoreOf 2 G₂)
              (A ⊓ pCoreOf 2 G₂ ⊓ Subgroup.centralizer (conjClosure V G₂ : Set G)) ∧
          (∀ g ∈ G₂, ⁅conjBy V g, A ⊓ pCoreOf 2 G₂⁆ ≠ ⊥ →
            2 * mRel (A ⊓ pCoreOf 2 G₂)
                (A ⊓ pCoreOf 2 G₂ ⊓ Subgroup.centralizer (conjBy V g : Set G)) =
              mRel (conjBy V g)
                (conjBy V g ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G))) ∧
          (∀ L N : Subgroup G, IsChiefStep G₂ (conjClosure V G₂) L N → ¬ IsCentralStep G₂ L N →
            mRel A (A ⊓ pCoreOf 2 G₂) = mRel N (secFix A N L)) ∧
          conjClosure V G₂ ⊓ Subgroup.centralizer (A : Set G) =
            conjClosure V G₂ ⊓ Subgroup.centralizer ((A ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G))

theorem as_D_1_3_one_three_general : D_1_3_one_three_general := by
  intro G _ G₁ G₂ T V M₂ h hq hVR₂ c hc hser
  haveI := h.finite₁
  haveI := h.finite₂
  exact CFSG.Quasithin.MS09.d13_one_three_general
    ⟨h.sylow₁, h.sylow₂, h.reduced, h.nontrivial, h.unique_max, h.centralizer, h.no_normal⟩
    hq hVR₂ c hc hser

theorem as_D_1_3 : D_1_3 := by
  intro G _ G₁ G₂ T V M₂ h hq hVR₂ c hc hser
  haveI := h.finite₁
  haveI := h.finite₂
  obtain ⟨e1, e2, -, e4, -⟩ := CFSG.Quasithin.SimsD1.ThreeGen.d13_general
    CFSG.Quasithin.MS09.d125NonsolvableSQTK_holds
    ⟨h.sylow₁, h.sylow₂, h.reduced, h.nontrivial, h.unique_max, h.centralizer, h.no_normal⟩
    hq hVR₂ c hc hser
  obtain ⟨g1, g3⟩ := as_D_1_3_one_three_general G G₁ G₂ T V M₂ h hq hVR₂ c hc hser
  exact ⟨e1, e2, g1, e4, g3⟩

@[expose] def D_1_4 : Prop :=
  ∀ (G : Type) [Group G] (G₁ G₂ T V M₂ : Subgroup G) (h : HypD11 G₁ G₂ T V M₂),
    V ≤ pCoreOf 2 G₂ →
    IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1 →
    IsDualFFInt G₁ V h.reduced.2.2.1 ∨
    (((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).subgroupOf G₂).Normal ∧
      IsElemAbelian 2 (conjClosure V G₂) ∧
      ⁅conjClosure V G₂, twoResidual G₂⁆ ≤ centerOf (pCoreOf 2 G₂) ∧
      twoResidual G₂ = ⁅twoResidual G₂, thompsonJ (pCoreOf 2 G₁)⁆ ∧
      (¬ IsFFInt G₁ V h.reduced.2.2.1 → thompsonJ T = thompsonJ (pCoreOf 2 G₁)) ∧
      (∃ (I : Subgroup G) (hI : IsTwoReducedIn G₂ I),
        I ≤ conjClosure V G₂ ∧ IsFFInt G₂ I hI.2.2.1) ∧
      (Group.IsSolvable G₂ → CharTwo G₂ →
        IsProdA3Blocks G₂ (twoResidual G₂) ∧
          IsSylowTwoOf (pCoreOf 2 G₁) (twoResidual G₂ ⊔ pCoreOf 2 G₁)))

section as_D_1_4

theorem as_D_1_4 : D_1_4 := by
  intro G _ G₁ G₂ T V M₂ h hVR₂ hchief
  haveI := h.finite₁
  haveI := h.finite₂
  have h' : D11Hyp G₁ G₂ T V M₂ :=
    ⟨h.sylow₁, h.sylow₂, h.reduced, h.nontrivial, h.unique_max, h.centralizer, h.no_normal⟩
  by_cases hdual : IsDualFFInt G₁ V h.reduced.2.2.1
  · exact Or.inl hdual
  rcases CFSG.Quasithin.SimsD1.FourGen.d14_general h' hVR₂ hchief with
    h1 | ⟨hn, hea, hcom, hres, hJ, hI, hsyl⟩
  · exact absurd h1 hdual
  exact Or.inr ⟨hn, hea, hcom, hres, hJ, hI, fun hsolv hchar =>
    ⟨CFSG.Quasithin.SimsD1.FourGeneral.prodA3Blocks_general_of_factorization
      CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved h' hVR₂ hchief
      hdual hsolv hchar, hsyl hsolv hchar⟩⟩

end as_D_1_4

@[expose] def D_1_5 : Prop :=
  ∀ (G : Type) [Group G] (G₁ G₂ T V M₂ : Subgroup G) (h : HypD11 G₁ G₂ T V M₂),
    ¬ V ≤ pCoreOf 2 G₂ ∨
    (qSub G₁ V h.finite₁ h.reduced.1 h.reduced.2.2.1 ≤ 1 ∧ IsFFInt G₁ V h.reduced.2.2.1) ∨
    IsDualFFInt G₁ V h.reduced.2.2.1 ∨
    (qSub G₁ V h.finite₁ h.reduced.1 h.reduced.2.2.1 ≤ 2 ∧
      (∀ x ∈ conjClosure V G₂, ∀ y ∈ conjClosure V G₂, x * y = y * x) ∧
      ∃ c : ℕ, 2 ≤ c ∧ IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c) ∨
    (((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).subgroupOf G₂).Normal ∧
      IsElemAbelian 2 (conjClosure V G₂) ∧
      IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1 ∧
      ⁅conjClosure V G₂, twoResidual G₂⁆ ≤ centerOf (pCoreOf 2 G₂) ∧
      twoResidual G₂ = ⁅twoResidual G₂, thompsonJ (pCoreOf 2 G₁)⁆ ∧
      thompsonJ (pCoreOf 2 G₁) = thompsonJ T)

@[expose] def D_1_5_general : Prop :=
  ∀ (G : Type) [Group G] (G₁ G₂ T V M₂ : Subgroup G) (h : HypD11 G₁ G₂ T V M₂),
    ¬ V ≤ pCoreOf 2 G₂ ∨
    (qSub G₁ V h.finite₁ h.reduced.1 h.reduced.2.2.1 ≤ 1 ∧ IsFFInt G₁ V h.reduced.2.2.1) ∨
    IsDualFFInt G₁ V h.reduced.2.2.1 ∨
    (qSub G₁ V h.finite₁ h.reduced.1 h.reduced.2.2.1 ≤ 2 ∧
      (∀ x ∈ conjClosure V G₂, ∀ y ∈ conjClosure V G₂, x * y = y * x) ∧
      ∃ c : ℕ, 2 ≤ c ∧ IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c) ∨
    (((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).subgroupOf G₂).Normal ∧
      IsElemAbelian 2 (conjClosure V G₂) ∧
      IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1 ∧
      ⁅conjClosure V G₂, twoResidual G₂⁆ ≤ centerOf (pCoreOf 2 G₂) ∧
      twoResidual G₂ = ⁅twoResidual G₂, thompsonJ (pCoreOf 2 G₁)⁆ ∧
      thompsonJ (pCoreOf 2 G₁) = thompsonJ T)

theorem as_D_1_5_general : D_1_5_general := by
  intro G _ G₁ G₂ T V M₂ h
  haveI := h.finite₁
  haveI := h.finite₂
  exact CFSG.Quasithin.MS09.d15_general
    ⟨h.sylow₁, h.sylow₂, h.reduced, h.nontrivial, h.unique_max, h.centralizer, h.no_normal⟩

theorem as_D_1_5 : D_1_5 := as_D_1_5_general

end CFSG.ASVolI
