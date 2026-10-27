module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6ThreeDvd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three2
public import CFSG.HardMathSupport.Lang.SeitzPlane.Phi3D4LayerData
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Excl
public import CFSG.RankThree.PartOne.KE6.Phi6Frame
public import CFSG.RankThree.PartOne.KE6.Phi6Torsion
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

namespace CFSG.StandardType.E6TwoSeven

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE6.NonsplitLayers
open CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
open CFSG.HardMathSupport.Lang.SeitzPlane
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_injective adjEmb_mem
  adjEmb_frobenius sigma_embedding_data subtorusImage mem_subtorusImage_iff twistedTorusOf
  twistedFixedPoints mem_twistedFixedPoints subtorusSigma subtorusSigma_le_twistedTorusOf)
open CFSG.Assembly (IsComponentOf)
open scoped Matrix MatrixGroups Pointwise

private theorem ltqLay_A2_kernelLayer_type
    {Ω : Type} [Field Ω] {Fr : Ω →+* Ω} {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ twistedTorus (phi3N Ω) Fr)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) :
    ∃ KL : KernelLayer (phi3N Ω) (Units.map (entrywiseHom Fr)) (torusRootKernel x) K Unit,
      ∀ i, Nonempty (↥(KL.P i) ≃* SL(3, K)) ∨ ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
        Nonempty (↥(KL.P i) ≃* ↥(d4ThetaFixed Ω Fr e)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨w, hw⟩ := hA2
  obtain ⟨hQ, hfin, hq, hcomm, h₀, hsl⟩ := phi3_A2_layer_data hf hK hFr hx hw
  obtain ⟨KL, hKL⟩ := exists_kernelLayer_single_P (fun α hα => hα.1) hQ hfin hq hcomm
    ⟨e6Index 0, h₀, hsl⟩
  obtain ⟨-, -, -, -, -, -, hne, -⟩ :=
    phi3_A2_layer_equiv (Ω := Ω) (Fr := Fr) hf hK hFr (fun α hα => hα.1)
      (torusRootKernel_smul_stable hFr hx) hw
  refine ⟨KL, fun i => Or.inl ?_⟩
  rw [hKL i]
  exact hne

private theorem ltqLay_A2A2_kernelLayer_type
    {Ω : Type} [Field Ω] {Fr : Ω →+* Ω} {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ twistedTorus (phi3N Ω) Fr)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) :
    ∃ KL : KernelLayer (phi3N Ω) (Units.map (entrywiseHom Fr)) (torusRootKernel x) K (Fin 2),
      ∀ i, Nonempty (↥(KL.P i) ≃* SL(3, K)) ∨ ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
        Nonempty (↥(KL.P i) ≃* ↥(d4ThetaFixed Ω Fr e)) := by
  classical
  obtain ⟨w, S₁, S₂, KL, -, hw₁, hw₂, hS₁roots, hvS₁, hS₂roots, hvS₂, hKL, -⟩ :=
    phi3_A2A2_kernelLayer_dvd_P hf hK hFr hx hA2A2
      (p := Nat.card K ^ 2 + Nat.card K + 1) dvd_rfl
  obtain ⟨hne₁, hne₂, -, -⟩ :=
    phi3_A2A2_layer_equivs (Ω := Ω) (Fr := Fr) hf hK hFr hS₁roots hvS₁ hw₁ hS₂roots hvS₂ hw₂
      (p := Nat.card K ^ 2 + Nat.card K + 1) dvd_rfl
  refine ⟨KL, fun i => Or.inl ?_⟩
  rw [hKL]
  fin_cases i
  · exact hne₁
  · exact hne₂

private theorem ltqLay_D4_kernelLayer_type
    {Ω : Type} [Field Ω] {Fr : Ω →+* Ω} {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ twistedTorus (phi3N Ω) Fr)
    (hD4 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 d4Support) :
    ∃ KL : KernelLayer (phi3N Ω) (Units.map (entrywiseHom Fr)) (torusRootKernel x) K Unit,
      ∀ i, Nonempty (↥(KL.P i) ≃* SL(3, K)) ∨ ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
        Nonempty (↥(KL.P i) ≃* ↥(d4ThetaFixed Ω Fr e)) := by
  obtain ⟨w, hw⟩ := hD4
  obtain ⟨hQ, hfin, hq, hcomm, hh0, hee⟩ :=
    phi3_D4_layer_data' (Ω := Ω) (Fr := Fr) hf hK hFr hx hw
  obtain ⟨h₀, hsl⟩ := hh0
  obtain ⟨e, g, he, hconj, hne⟩ := hee
  obtain ⟨KL, hKL⟩ := exists_kernelLayer_single_P (fun α hα => hα.1) hQ hfin hq hcomm
    ⟨d4Idx 2, h₀, hsl⟩
  refine ⟨KL, fun i => Or.inr ⟨e, he, ?_⟩⟩
  rw [hKL i]
  exact hne

theorem e6Phi3_perx_type
    (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL .E6 L} (hg0C : g0 ∈ adjointGroup .E6 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * phi3N L)
    (hperf : ∀ P : Subgroup (ModGL .E6 L), Finite P → P ≤ adjointGroup .E6 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .E6 K L).range)
    {x : adjointGroup .E6 K} (hx : orderOf x = p) (c : adjointGroup .E6 K)
    (hh : g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0 ∈
      twistedTorus (phi3N L) (iterateFrobenius L ℓ f)) :
    ∃ (ι' : Type) (KL : KernelLayer (phi3N L)
        (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
        (torusRootKernel (g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0)) K ι')
      (ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)) →* ModGL .E6 L),
      Function.Injective ψ ∧
      (∀ y, ψ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L
        (torusRootKernel (g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0))) ∧
      (∀ y, phi3N L * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ y) * (phi3N L)⁻¹ =
        ψ y) ∧
      (∀ i, KL.P i ≤ ψ.range) ∧
      (∀ i, Nonempty (↥(KL.P i) ≃* SL(3, K)) ∨ ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
        Nonempty (↥(KL.P i) ≃* ↥(d4ThetaFixed L (iterateFrobenius L ℓ f) e))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr c
  have hℓ : ℓ.Prime := Fact.out
  have hq0 : ((ℓ ^ f : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  have hpq' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    rw [hK] at hpq
    exact hpq
  obtain ⟨hpL, ⟨ζ, hζ⟩, hr⟩ := phi3_prime_setup hq0 hp hpq'
  have hp7 : 7 ≤ p := (e6Three_data hp hp3 hpq').2.2.2.2.1
  have hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E6) := not_dvd_card_weyl_E6 hp (by omega)
  set ι : adjointGroup .E6 K →* ModGL .E6 L := adjEmb .E6 K L with hιdef
  set h : ModGL .E6 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hh).1
  have hb' : rootDiagUnit .E6 b = g0⁻¹ * ι (c * x * c⁻¹) * g0 := hb.symm
  have hordh : orderOf h = p := by
    have e1 : orderOf h = orderOf (ι (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (ι (c * x * c⁻¹))
      rw [hhdef]
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (ι (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective ι adjEmb_injective _
    have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
      simpa [MulAut.conj_apply] using this
    rw [e1, e2, e3, hx]
  have hhp : h ^ p = 1 := hordh ▸ pow_orderOf_eq_one h
  have hh1 : h ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hordh
    exact hp.one_lt.ne hordh
  have htri : torusRootKernel h = ∅ ∨
      (∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel h = parabolicRoots Tag.E6 support13) ∨
      (∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel h = parabolicRoots Tag.E6 supportA2A2) ∨
      (∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel h = parabolicRoots Tag.E6 d4Support) := by
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨z, -, hzc, hzker, hz0⟩ := exists_column_of_phi3Torus hFr hζ hh hhp
    rw [hzker]
    exact phi3_kernel_types (by omega) z (hz0 hh1) _ hzc
  have hnC : phi3N L ∈ adjointGroup .E6 L := canonicalRep_mem_adjointGroup _ L _
  have hrootneg : ∀ α ∈ torusRootKernel h, -α ∈ torusRootKernel h := fun α hα => by
    rw [hb, torusRootKernel_rootDiagUnit] at hα ⊢
    exact ⟨CFSG.LieType.Chevalley.IsRoot.neg hα.1, by rw [CFSG.RankThree.Classical2.rootChar_neg', hα.2, inv_one]⟩
  have finish : ∀ {ι' : Type} (KL : KernelLayer (phi3N L) (Units.map (entrywiseHom Fr))
      (torusRootKernel h) K ι'), (∀ i, Nonempty (↥(KL.P i) ≃* SL(3, K)) ∨ ∃ e : ℕ,
        (e = 1 ∨ e = 2) ∧ Nonempty (↥(KL.P i) ≃* ↥(d4ThetaFixed L Fr e))) →
      ∃ (ι'' : Type) (KL' : KernelLayer (phi3N L)
        (Units.map (entrywiseHom Fr)) (torusRootKernel h) K ι'')
      (ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)) →* ModGL .E6 L),
      Function.Injective ψ ∧
      (∀ y, ψ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L (torusRootKernel h)) ∧
      (∀ y, phi3N L * Units.map (entrywiseHom Fr) (ψ y) * (phi3N L)⁻¹ = ψ y) ∧
      (∀ i, KL'.P i ≤ ψ.range) ∧
      (∀ i, Nonempty (↥(KL'.P i) ≃* SL(3, K)) ∨ ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
        Nonempty (↥(KL'.P i) ≃* ↥(d4ThetaFixed L Fr e))) := by
    intro ι' KL hKL
    have hcS : c * x * c⁻¹ ∈ subtorusImage ι g0
        (subtorusSigma (phi3N L) (Units.map (entrywiseHom Fr)) (torusRootKernel h)) := by
      rw [mem_subtorusImage_iff]
      refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have hle := rootSpan_le_centralizer (K := L) b (S := torusRootKernel h) (by
        rw [← torusRootKernel_rootDiagUnit, hb])
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
      rw [hb'] at h1
      exact h1
    have hkerZ : ∀ a : Fin Tag.E6.rank → Lˣ,
        rootDiagUnit .E6 a = g0⁻¹ * ι (c * x * c⁻¹) * g0 → rootCharKernel a ⊆ torusRootKernel h :=
      fun a ha => by
        have : a = b := rootDiagUnit_injective (ha.trans hb'.symm)
        rw [this, ← torusRootKernel_rootDiagUnit, hb]
    obtain ⟨ψ, hψinj, -, hψHQ, hψR, -, hPψ, -⟩ := sigma_embedding_data ι adjEmb_injective
      adjEmb_mem (Units.map (entrywiseHom Fr)) (adjEmb_frobenius Fr hFrK) (phi3N L) g0 hg0C hg0
      hperf hp hordW (fun α hα => hα.1) hrootneg KL.P KL.fin KL.quasi KL.le_span KL.le_fixed
      (fun i => (KL.le_span i).trans (rootSpan_le_adjointGroup L _)) KL.norm
      (fun y hy hyR hc => by
        obtain ⟨hyH, hyC⟩ := KL.cent y hy hc
        exact Subgroup.mem_inf.2 ⟨mem_twistedTorus.2 ⟨hyH, mem_twistedFixedPoints.1 hyR⟩, hyC⟩)
      hx c hcS hkerZ
    exact ⟨ι', KL, ψ, hψinj, hψHQ, hψR, hPψ, hKL⟩
  rcases htri with hreg | hA2 | hA2A2 | hD4
  · have KL : KernelLayer (phi3N L) (Units.map (entrywiseHom Fr)) (torusRootKernel h) K Empty := by
      rw [hreg]
      exact KernelLayer.empty
    exact finish KL (fun e => e.elim)
  · obtain ⟨KL, hKL⟩ := ltqLay_A2_kernelLayer_type (Ω := L) (Fr := Fr) hf hK hFr hh hA2
    exact finish KL hKL
  · obtain ⟨KL, hKL⟩ := ltqLay_A2A2_kernelLayer_type (Ω := L) (Fr := Fr) hf hK hFr hh hA2A2
    exact finish KL hKL
  · obtain ⟨KL, hKL⟩ := ltqLay_D4_kernelLayer_type (Ω := L) (Fr := Fr) hf hK hFr hh hD4
    exact finish KL hKL

theorem e6Phi3_component_type
    (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∀ x : adjointGroup .E6 K, orderOf x = p →
      ∀ X : Subgroup (adjointGroup .E6 K),
        IsComponentOf X (Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))) →
          Nonempty (↥X ≃* SL(3, K)) ∨ ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
            Nonempty (↥X ≃* ↥(d4ThetaFixed L (iterateFrobenius L ℓ f) e)) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := e6_three_frame K hf hK hp hp3 hpq L
  intro x hx X hX
  have hpg : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := hconj _ hpg
  have hh := hc x (Subgroup.mem_zpowers x)
  obtain ⟨ι', KL, ψ, hψinj, hψT, hψθ, hPψ, hPd⟩ :=
    e6Phi3_perx_type K hf hK hp hp3 hpq L hg0C hg0 hperf hx c hh
  have hX' : CFSG.IsComponent (X.subgroupOf
      (Subgroup.centralizer ({x} : Set (adjointGroup .E6 K)))) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hX.1).1 hX
  obtain ⟨i, hi⟩ := CFSG.StandardType.E6Nonsplit.exists_eq_comap_of_isComponent ψ hψinj KL.P hPψ
    KL.quasi
    (fun i d u hu => KL.norm i (ψ d) (hψT d) (mem_twistedFixedPoints.2 (hψθ d)) u hu)
    (Z := (torusGroup .E6 L : Set (ModGL .E6 L)))
    (fun a ha b hb => phi3_torusGroup_comm a ha b hb)
    (fun d hd => (KL.cent (ψ d) (hψT d) hd).1) hX'
  have hmap : ((KL.P i).comap ψ).map ψ = KL.P i := by
    rw [Subgroup.map_comap_eq, inf_of_le_right (hPψ i)]
  let e : ↥X ≃* ↥(KL.P i) :=
    ((Subgroup.subgroupOfEquivOfLe hX.1).symm).trans
      ((MulEquiv.subgroupCongr hi).trans
        ((Subgroup.equivMapOfInjective ((KL.P i).comap ψ) ψ hψinj).trans
          (MulEquiv.subgroupCongr hmap)))
  rcases hPd i with hne | ⟨e₀, he₀, hne⟩
  · exact Or.inl ⟨e.trans hne.some⟩
  · exact Or.inr ⟨e₀, he₀, ⟨e.trans hne.some⟩⟩

end CFSG.StandardType.E6TwoSeven

end
