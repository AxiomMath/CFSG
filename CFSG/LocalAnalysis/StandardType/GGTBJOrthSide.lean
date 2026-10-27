module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmTorusAut
public import CFSG.LocalAnalysis.StandardType.GGTBJFrameCorank
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeDSupported
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeDTwisted
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBSupported
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBTwisted

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG CFSG.Assembly SpCoord
open CFSG.RankThree.Classical2 (orthDerived)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs X J : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {R : Type} [Group R]
  {eR : R ≃* ↥(orthDerived Q)} {r : ℕ} {E : Subgroup (V ≃ₗ[K] V)} {Δ : TBJOmData Q p E r}
  {hE : E ≤ orthDerived Q}

theorem hcountA_of_hcountBs (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (σ : (Fin r → Multiplicative (ZMod p)) →* ↥X)
    (ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma X hBsN).range)
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f))
    (Θ : ((Fin r → Multiplicative (ZMod p)) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* ↥Bs)
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = ((σ w : ↥X) : G) * c)
    (hmem : ∀ f, ((σ f : ↥X) : G) ∈ Bs) (hJX : J ≤ X)
    (hcountBs : p ^ 2 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ Nat.card ↥Bs) :
    p ^ 2 * Nat.card ↥((ggGamma X hBsN).range ⊓
        ⨅ j : ↥(J.subgroupOf X), MulAction.stabilizer (MulAut ↥X) (j : ↥X)) ≤
      Nat.card ↥(ggGamma X hBsN).range := by
  classical
  obtain ⟨hB, hC⟩ := FrameBs.card_centralizer_frame Θ σ hΘ hmem hJX
  have hcardA : Nat.card ↥(ggGamma X hBsN).range = p ^ r := by
    rw [← Nat.card_congr ΘA.toEquiv]
    exact FrameBs.card_zmodFrame p r
  have hst := card_stabilizer_frame_eq_card_centralizer ΘA hΘA (J.subgroupOf X)
  have hset : Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J.subgroupOf X, σ f * j = j * σ f} =
      Nat.card {f : Fin r → Multiplicative (ZMod p) //
        ∀ j ∈ J, ((σ f : ↥X) : G) * j = j * ((σ f : ↥X) : G)} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
    constructor
    · intro h j hj
      have := h ⟨j, hJX hj⟩ (Subgroup.mem_subgroupOf.mpr hj)
      simpa using congrArg Subtype.val this
    · intro h j hj
      exact Subtype.ext (by simpa using h j.1 (Subgroup.mem_subgroupOf.mp hj))
  rw [hst, hset, hcardA]
  have hpos : 0 < Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := Nat.card_pos
  rw [hC, hB] at hcountBs
  nlinarith

theorem ggTBJOrth_nf_sideDatum_with_fixed_centralizer (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {ψ₀ : ↥X →* R} (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center ↥X)
    (hZ : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {σ : (Fin r → Multiplicative (ZMod p)) →* ↥X}
    {ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma X hBsN).range}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f))
    (hWeyl : ∀ n : ↥X, MulAut.conj n ∈ Subgroup.normalizer
      ((ggGamma X hBsN).range : Set (MulAut ↥X)) → GGTorusWeylElt p (ggGamma X hBsN).range n)
    (hnf : ∀ v : V, (∀ a ∈ E, a v = v) → v = 0) (hr : 4 ≤ r)
    {y : MulAut ↥X} (hy : y ∈ (ggGamma X hBsN).range) (hy1 : y ≠ 1) (hJX : J ≤ X)
    (hJ : CFSG.Open.IsComponentOf (J.subgroupOf X)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcountA : p ^ 2 * Nat.card ↥((ggGamma X hBsN).range ⊓
        ⨅ j : ↥(J.subgroupOf X), MulAction.stabilizer (MulAut ↥X) (j : ↥X)) ≤
      Nat.card ↥(ggGamma X hBsN).range)
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    (GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J) ∧
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  classical
  obtain ⟨hmem, -⟩ := FrameBs.sectionFrame_model hBs hSC hBsN σ ΘA hΘA
  obtain ⟨Θ, hΘ, hAut⟩ :=
    FrameBs.ggAutomizer_eq_map_liftBs_sectionFrameAut hBs hSC hBsN hZ σ ΘA hΘA
  obtain ⟨S, hfix, hshape⟩ := ggTBJ_om_torus_aut_nf hp2 hQ hT hψsurj hker hZ hψσ hΘA hnf
    hy hy1 hJ hcountA
  have hXaut : ggAutomizer X Bs = (TypeDDatum.evenSignedAut r p).map (TypeBDatum.liftBs Θ) := by
    rw [hAut X le_rfl, FrameBs.sectionFrameAut_subtype_comp σ le_rfl, Subgroup.subgroupOf_self,
      sectionFrameAut_top_nf hp2 hQ hT hψsurj hker hZ hψσ hnf]
  have hJaut := hAut J hJX
  rw [FrameBs.sectionFrameAut_subtype_comp σ hJX] at hJaut
  have hcentral : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    refine FrameBs.mem_centralizer_of_automizer_fixed Θ σ hΘ hJX
      (by rw [FrameBs.sectionFrameAut_subtype_comp σ hJX]; exact hJaut) ?_
    intro f hf j hj
    have h1 := hfix f (by
      intro τ hτ
      exact hf τ (by rw [FrameBs.sectionFrameAut_subtype_comp σ hJX]; exact hτ)) ⟨j, hJX hj⟩
      (Subgroup.mem_subgroupOf.mpr hj)
    simpa using congrArg Subtype.val h1
  refine ⟨?_, hcentral⟩
  rcases hshape with ⟨hS3, hSu, hSJ⟩ | ⟨s, hs, hS2, hSJ⟩
  ·
    have hSJ' : ggAutomizer J Bs = (TypeDDatum.evenSignedSupportedAut r p S).map
        (TypeBDatum.liftBs Θ) := by rw [hJaut, hSJ]
    have hc3 : r - S.card ≤ 3 :=
      FrameBs.corank_le_three_of_supported hΘ hmem
        (fun f hf => FrameBs.evenSignedSupportedAut_fix hf) hSJ' hcentral hCJ
    have hSlt : S.card < r := by
      have := Finset.card_lt_card (lt_of_le_of_ne (Finset.subset_univ S) hSu)
      simpa using this
    have hres := TypeDDatum.ggTBJTypeD_sideDatum_evenSupported hp2 hr hBs Θ hXaut hS3
      (by omega) hc3 hSJ'
    by_cases h1 : r - S.card = 1
    · exact Or.inl (hres.1 h1)
    · exact Or.inr (hres.2 (by omega))
  ·
    have hSJ' : ggAutomizer J Bs = (TypeBDatum.twistedPermAut r p S s hs).map
        (TypeBDatum.liftBs Θ) := by rw [hJaut, hSJ]
    have hc3 : r - S.card + 1 ≤ 3 :=
      FrameBs.corank_le_three_of_twisted hΘ hmem hs (by omega)
        (fun f m hf => FrameBs.twistedPermAut_fix hs hf) hSJ' hcentral hCJ
    have hSle : S.card ≤ r := by simpa using Finset.card_le_univ S
    have hres := TypeDDatum.ggTBJTypeD_sideDatum_twistedPerm hp2 hr hBs Θ hXaut hS2
      (by omega) hs hSJ'
    by_cases h1 : r + 1 - S.card = 1
    · exact Or.inl (hres.1 h1)
    · exact Or.inr (hres.2 (by omega))

theorem ggTBJOrth_nf_sideDatum (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {ψ₀ : ↥X →* R} (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center ↥X)
    (hZ : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {σ : (Fin r → Multiplicative (ZMod p)) →* ↥X}
    {ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma X hBsN).range}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f))
    (hWeyl : ∀ n : ↥X, MulAut.conj n ∈ Subgroup.normalizer
      ((ggGamma X hBsN).range : Set (MulAut ↥X)) → GGTorusWeylElt p (ggGamma X hBsN).range n)
    (hnf : ∀ v : V, (∀ a ∈ E, a v = v) → v = 0) (hr : 4 ≤ r)
    {y : MulAut ↥X} (hy : y ∈ (ggGamma X hBsN).range) (hy1 : y ≠ 1) (hJX : J ≤ X)
    (hJ : CFSG.Open.IsComponentOf (J.subgroupOf X)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcountA : p ^ 2 * Nat.card ↥((ggGamma X hBsN).range ⊓
        ⨅ j : ↥(J.subgroupOf X), MulAction.stabilizer (MulAut ↥X) (j : ↥X)) ≤
      Nat.card ↥(ggGamma X hBsN).range)
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  exact (ggTBJOrth_nf_sideDatum_with_fixed_centralizer hp2 hBs hSC hBsN hQ hT hψsurj hker hZ hψσ hΘA
    hWeyl hnf hr hy hy1 hJX hJ hcountA hCJ).1


theorem ggTBJOrth_fixed_sideDatum_with_fixed_centralizer (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {ψ₀ : ↥X →* R} (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center ↥X)
    (hZ : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {σ : (Fin r → Multiplicative (ZMod p)) →* ↥X}
    {ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma X hBsN).range}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f))
    (hWeyl : ∀ n : ↥X, MulAut.conj n ∈ Subgroup.normalizer
      ((ggGamma X hBsN).range : Set (MulAut ↥X)) → GGTorusWeylElt p (ggGamma X hBsN).range n)
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ E, a v = v) (hr : 2 ≤ r)
    {y : MulAut ↥X} (hy : y ∈ (ggGamma X hBsN).range) (hy1 : y ≠ 1) (hJX : J ≤ X)
    (hJ : CFSG.Open.IsComponentOf (J.subgroupOf X)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcountA : p ^ 2 * Nat.card ↥((ggGamma X hBsN).range ⊓
        ⨅ j : ↥(J.subgroupOf X), MulAction.stabilizer (MulAut ↥X) (j : ↥X)) ≤
      Nat.card ↥(ggGamma X hBsN).range)
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    (GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J) ∧
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  classical
  obtain ⟨hmem, -⟩ := FrameBs.sectionFrame_model hBs hSC hBsN σ ΘA hΘA
  obtain ⟨Θ, hΘ, hAut⟩ :=
    FrameBs.ggAutomizer_eq_map_liftBs_sectionFrameAut hBs hSC hBsN hZ σ ΘA hΘA
  obtain ⟨S, hfix, hshape⟩ := ggTBJ_om_torus_aut_fixed hp2 hQ hT hψsurj hker hZ hψσ hΘA hW
    hy hy1 hJ hcountA
  have hXaut : ggAutomizer X Bs = (TypeBDatum.signedAut r p).map (TypeBDatum.liftBs Θ) := by
    rw [hAut X le_rfl, FrameBs.sectionFrameAut_subtype_comp σ le_rfl, Subgroup.subgroupOf_self,
      sectionFrameAut_top_fixed hp2 hQ hT hψsurj hker hZ hψσ hW]
  have hJaut := hAut J hJX
  rw [FrameBs.sectionFrameAut_subtype_comp σ hJX] at hJaut
  have hcentral : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    refine FrameBs.mem_centralizer_of_automizer_fixed Θ σ hΘ hJX
      (by rw [FrameBs.sectionFrameAut_subtype_comp σ hJX]; exact hJaut) ?_
    intro f hf j hj
    have h1 := hfix f (by
      intro τ hτ
      exact hf τ (by rw [FrameBs.sectionFrameAut_subtype_comp σ hJX]; exact hτ)) ⟨j, hJX hj⟩
      (Subgroup.mem_subgroupOf.mpr hj)
    simpa using congrArg Subtype.val h1
  refine ⟨?_, hcentral⟩
  rcases hshape with ⟨hS1, hSu, hSJ⟩ | ⟨s, hs, hS2, hSJ⟩
  ·
    have hSJ' : ggAutomizer J Bs = (TypeBDatum.signedSupportedAut r p S).map
        (TypeBDatum.liftBs Θ) := by rw [hJaut, hSJ]
    have hc3 : r - S.card ≤ 3 :=
      FrameBs.corank_le_three_of_supported hΘ hmem
        (fun f hf => FrameBs.signedSupportedAut_fix hf) hSJ' hcentral hCJ
    have hSlt : S.card < r := by
      have := Finset.card_lt_card (lt_of_le_of_ne (Finset.subset_univ S) hSu)
      simpa using this
    have hres := TypeBDatum.ggTBJTypeB_sideDatum_signedSupported hp2 hr hBs Θ hXaut hS1
      (by omega) hc3 hSJ'
    by_cases h1 : r - S.card = 1
    · exact Or.inl (hres.1 h1)
    · exact Or.inr (hres.2 (by omega))
  ·
    have hSJ' : ggAutomizer J Bs = (TypeBDatum.twistedPermAut r p S s hs).map
        (TypeBDatum.liftBs Θ) := by rw [hJaut, hSJ]
    have hc3 : r - S.card + 1 ≤ 3 :=
      FrameBs.corank_le_three_of_twisted hΘ hmem hs (by omega)
        (fun f m hf => FrameBs.twistedPermAut_fix hs hf) hSJ' hcentral hCJ
    have hSle : S.card ≤ r := by simpa using Finset.card_le_univ S
    have hres := TypeBDatum.ggTBJTypeB_sideDatum_twistedPerm hp2 hr hBs Θ hXaut hS2
      (by omega) hs hSJ'
    by_cases h1 : r + 1 - S.card = 1
    · exact Or.inl (hres.1 h1)
    · exact Or.inr (hres.2 (by omega))

theorem ggTBJOrth_fixed_sideDatum (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {ψ₀ : ↥X →* R} (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center ↥X)
    (hZ : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {σ : (Fin r → Multiplicative (ZMod p)) →* ↥X}
    {ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma X hBsN).range}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f))
    (hWeyl : ∀ n : ↥X, MulAut.conj n ∈ Subgroup.normalizer
      ((ggGamma X hBsN).range : Set (MulAut ↥X)) → GGTorusWeylElt p (ggGamma X hBsN).range n)
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ E, a v = v) (hr : 2 ≤ r)
    {y : MulAut ↥X} (hy : y ∈ (ggGamma X hBsN).range) (hy1 : y ≠ 1) (hJX : J ≤ X)
    (hJ : CFSG.Open.IsComponentOf (J.subgroupOf X)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcountA : p ^ 2 * Nat.card ↥((ggGamma X hBsN).range ⊓
        ⨅ j : ↥(J.subgroupOf X), MulAction.stabilizer (MulAut ↥X) (j : ↥X)) ≤
      Nat.card ↥(ggGamma X hBsN).range)
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  exact (ggTBJOrth_fixed_sideDatum_with_fixed_centralizer hp2 hBs hSC hBsN hQ hT hψsurj hker hZ hψσ hΘA
    hWeyl hW hr hy hy1 hJX hJ hcountA hCJ).1


theorem ggTBJ_sq_mul_card_inf_centralizer_le {p : ℕ} {B : Subgroup G} {x : G}
    {L D : Subgroup G} (hcfg : GGConfig p B Bs x L D J) :
    p ^ 2 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ Nat.card ↥Bs := by
  obtain ⟨hp, -, -, -, -⟩ := GGConfig.tableB_facts hcfg
  have hB_le_Bs : B ≤ Bs := hcfg.2.1.1
  have hcardD : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hDBJ : D = B ⊓ Subgroup.centralizer (J : Set G) := hcfg.2.2.1.2.2.2.2.2.2
  have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.2.1.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
  have hp4B : p ^ 4 ≤ Nat.card B := by
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4
      _ = Nat.card B := hBc.symm
  refine FrameBs.sq_mul_card_le_of_inf hB_le_Bs inf_le_left hp4B ?_
  rw [← inf_assoc, inf_of_le_left hB_le_Bs, ← hDBJ]
  exact hcardD

theorem ggTBJOrth_nf_sideDatum_of_countBs (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {ψ₀ : ↥X →* R} (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center ↥X)
    (hZ : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {σ : (Fin r → Multiplicative (ZMod p)) →* ↥X}
    {ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma X hBsN).range}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f))
    (hWeyl : ∀ n : ↥X, MulAut.conj n ∈ Subgroup.normalizer
      ((ggGamma X hBsN).range : Set (MulAut ↥X)) → GGTorusWeylElt p (ggGamma X hBsN).range n)
    (hnf : ∀ v : V, (∀ a ∈ E, a v = v) → v = 0) (hr : 4 ≤ r)
    {y : MulAut ↥X} (hy : y ∈ (ggGamma X hBsN).range) (hy1 : y ≠ 1) (hJX : J ≤ X)
    (hJ : CFSG.Open.IsComponentOf (J.subgroupOf X)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcountBs : p ^ 2 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ Nat.card ↥Bs)
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  obtain ⟨hmem, -⟩ := FrameBs.sectionFrame_model hBs hSC hBsN σ ΘA hΘA
  obtain ⟨Θ, hΘ, -⟩ :=
    FrameBs.ggAutomizer_eq_map_liftBs_sectionFrameAut hBs hSC hBsN hZ σ ΘA hΘA
  exact ggTBJOrth_nf_sideDatum hp2 hBs hSC hBsN hQ hT hψsurj hker hZ hψσ hΘA hWeyl hnf hr hy
    hy1 hJX hJ (hcountA_of_hcountBs hBsN σ ΘA hΘA Θ hΘ hmem hJX hcountBs) hCJ

theorem ggTBJOrth_fixed_sideDatum_of_countBs (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {ψ₀ : ↥X →* R} (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center ↥X)
    (hZ : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    {σ : (Fin r → Multiplicative (ZMod p)) →* ↥X}
    {ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma X hBsN).range}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f))
    (hWeyl : ∀ n : ↥X, MulAut.conj n ∈ Subgroup.normalizer
      ((ggGamma X hBsN).range : Set (MulAut ↥X)) → GGTorusWeylElt p (ggGamma X hBsN).range n)
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ E, a v = v) (hr : 2 ≤ r)
    {y : MulAut ↥X} (hy : y ∈ (ggGamma X hBsN).range) (hy1 : y ≠ 1) (hJX : J ≤ X)
    (hJ : CFSG.Open.IsComponentOf (J.subgroupOf X)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcountBs : p ^ 2 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ Nat.card ↥Bs)
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  obtain ⟨hmem, -⟩ := FrameBs.sectionFrame_model hBs hSC hBsN σ ΘA hΘA
  obtain ⟨Θ, hΘ, -⟩ :=
    FrameBs.ggAutomizer_eq_map_liftBs_sectionFrameAut hBs hSC hBsN hZ σ ΘA hΘA
  exact ggTBJOrth_fixed_sideDatum hp2 hBs hSC hBsN hQ hT hψsurj hker hZ hψσ hΘA hWeyl hW hr hy
    hy1 hJX hJ (hcountA_of_hcountBs hBsN σ ΘA hΘA Θ hΘ hmem hJX hcountBs) hCJ

end OrthTorus

end CFSG.StandardType

end
