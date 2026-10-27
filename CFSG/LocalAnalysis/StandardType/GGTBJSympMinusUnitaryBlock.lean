module

public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusUnitaryVec
public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusUnitaryPoly
public import CFSG.LocalAnalysis.StandardType.GGTBJSpBlockAux
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.S11d.LieCentralizerGL
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicBlocks
public import CFSG.Goldschmidt.Steps.G37Basic
public import CFSG.ClassicalInvolution.Q3.Q3TLTLayer
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Assembly
public import CFSG.Goldschmidt.Steps.G37Transport
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.Bender1970.S3.Basic
public import CFSG.Walter.Bender1970.S3.OStar
public import CFSG.Walter.PSL2Facts

public section

namespace CFSG.StandardType.SympMinus

open Subgroup Polynomial Module Matrix CFSG CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
  CFSG.StandardType.SpJoin CFSG.StandardType.TorC
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (StatedSp)
open scoped commutatorElement

theorem smu_exists_card_eq_two_pow (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  haveI := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  refine ⟨n, n.pos, ?_⟩
  first
    | exact hn
    | rw [Nat.card_eq_fintype_card]; exact hn

theorem smu_commutator_quasisimple {r : ℕ} {K : Type} [Field K] {ℓ f p : ℕ}
    (_hq2 : 2 ≤ ℓ ^ f) {x : StatedSp r K} {h : primaryFactors (spEnd x)}
    (hself : reciprocalPolynomial (h : K[X]) = h) (hdeg : (h : K[X]).natDegree = 2)
    (hS : SpSelfDualBlock ℓ f p x h)
    (hm : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X]))
    (hqm : (primaryMultiplicity (spEnd x) (h : K[X]) = 2 → 4 ≤ ℓ ^ f) ∧
      (primaryMultiplicity (spEnd x) (h : K[X]) = 3 → 3 ≤ ℓ ^ f)) :
    ⁅orbitFactor (spForm r K) (spLin r K x) (h : K[X]),
        orbitFactor (spForm r K) (spLin r K x) (h : K[X])⁆ =
      specialBlock (spForm r K) (spLin r K x) (h : K[X]) ∧
    CFSG.IsQuasisimple (specialBlock (spForm r K) (spLin r K x) (h : K[X])) := by
  obtain ⟨d, hnd, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, hφ⟩ := hS.exists_half
  have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
    rw [hself, Set.pair_eq_singleton]
  have hd : d = 1 := by omega
  subst hd
  let ψ : orbitFactor (spForm r K) (spLin r K x) (h : K[X]) ≃* sesqUnitaryGroup Hf :=
    (spOrbitEquiv x hO).trans φ
  have hψ : ∀ (g : orbitFactor (spForm r K) (spLin r K x) (h : K[X]))
      (v : Fin r ⊕ Fin r → K) (hv : v ∈ primaryComponent (spEnd x) (h : K[X])),
      blockApply (ψ g : blockGL (spEnd x) (h : K[X])) v hv =
        ((g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) : Module.End K _) v := by
    intro g v hv
    rw [MulEquiv.trans_apply]
    have := hφ (spOrbitEquiv x hO g) v hv
    rw [this, spEnd_orbitEquiv]
  let ι : sesqUnitaryGroup Hf →* blockGL (spEnd x) (h : K[X]) :=
    (sesqUnitaryGroup Hf).subtype
  have hspec := specialBlock_eq_kerImage (B := spForm r K) ψ ι hψ
  let D : sesqUnitaryGroup Hf →* (AdjoinRoot (h : K[X]))ˣ :=
    (blockGLDet (spEnd x) (h : K[X])).comp ι
  have hker : D.ker = (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
    ext δ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
    constructor
    · intro h
      refine ⟨δ.2, ?_⟩
      have := congrArg Units.val h
      simpa [D, ι, blockGLDet] using this
    · rintro ⟨-, h⟩
      apply Units.ext
      simpa [D, ι, blockGLDet] using h
  have hquasi : CFSG.IsQuasisimple D.ker := by
    rw [hker]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm
      (isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf hHfl hm
        ⟨fun h2 => by simpa [Nat.mul_one] using hqm.1 h2,
          fun h3 => by simpa [Nat.mul_one] using hqm.2 h3⟩)
  obtain ⟨e⟩ := nonempty_kerImage_mulEquiv (orbitFactor (spForm r K) (spLin r K x) (h : K[X])) ψ D
  refine ⟨?_, ?_⟩
  · rw [hspec]
    exact (kerImage_eq_commutator _ ψ _ hquasi.1).symm
  · rw [hspec]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hquasi

theorem smu_isSolvable_specialBlock {r : ℕ} {K : Type} [Field K] {ℓ f p : ℕ}
    {x : StatedSp r K} {h : primaryFactors (spEnd x)}
    (hself : reciprocalPolynomial (h : K[X]) = h) (hdeg : (h : K[X]).natDegree = 2)
    (hS : SpSelfDualBlock ℓ f p x h) (hℓf : ℓ ^ f = 2)
    (hm1 : 1 ≤ primaryMultiplicity (spEnd x) (h : K[X]))
    (hm3 : primaryMultiplicity (spEnd x) (h : K[X]) ≤ 3) :
    Group.IsSolvable (specialBlock (spForm r K) (spLin r K x) (h : K[X])) := by
  obtain ⟨d, hnd, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, hφ⟩ := hS.exists_half
  have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
    rw [hself, Set.pair_eq_singleton]
  have hd : d = 1 := by omega
  subst hd
  rw [Nat.mul_one] at hE
  have hf1 : 1 ≤ f := hE.one_le
  have hℓ : ℓ = 2 := by
    have h1 : ℓ ∣ 2 := by
      have h2 : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
      rwa [hℓf] at h2
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd h (by have := hE.prime.two_le; omega)
    · exact h
  subst hℓ
  have hf : f = 1 := by
    rcases Nat.lt_or_ge f 2 with h | h
    · omega
    · exfalso
      have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h
      rw [hℓf] at h4
      omega
  subst hf
  let ψ : orbitFactor (spForm r K) (spLin r K x) (h : K[X]) ≃* sesqUnitaryGroup Hf :=
    (spOrbitEquiv x hO).trans φ
  have hψ : ∀ (g : orbitFactor (spForm r K) (spLin r K x) (h : K[X]))
      (v : Fin r ⊕ Fin r → K) (hv : v ∈ primaryComponent (spEnd x) (h : K[X])),
      blockApply (ψ g : blockGL (spEnd x) (h : K[X])) v hv =
        ((g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) : Module.End K _) v := by
    intro g v hv
    rw [MulEquiv.trans_apply]
    have := hφ (spOrbitEquiv x hO g) v hv
    rw [this, spEnd_orbitEquiv]
  let ι : sesqUnitaryGroup Hf →* blockGL (spEnd x) (h : K[X]) :=
    (sesqUnitaryGroup Hf).subtype
  have hspec := specialBlock_eq_kerImage (B := spForm r K) ψ ι hψ
  let D : sesqUnitaryGroup Hf →* (AdjoinRoot (h : K[X]))ˣ :=
    (blockGLDet (spEnd x) (h : K[X])).comp ι
  have hker : D.ker = (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
    ext δ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
    constructor
    · intro h
      refine ⟨δ.2, ?_⟩
      have := congrArg Units.val h
      simpa [D, ι, blockGLDet] using this
    · rintro ⟨-, h⟩
      apply Units.ext
      simpa [D, ι, blockGLDet] using h
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hHf hHfl
  have hSU : Group.IsSolvable ↥(sesqSpecialUnitaryGroup Hf) := by
    obtain ⟨e1⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE e
      (G := 1) (fun i j => by rw [he i j, Matrix.one_apply])
    haveI : Group.IsSolvable ↥(gramSU hE (1 : Matrix (Fin (Module.finrank (AdjoinRoot (h : K[X]))
        (primaryComponent (spEnd x) (h : K[X])))) (Fin (Module.finrank (AdjoinRoot (h : K[X]))
          (primaryComponent (spEnd x) (h : K[X])))) (AdjoinRoot (h : K[X])))) := by
      rw [← unitarySU_eq_gramSU hE]
      exact CFSG.StandardType.WitSU.isSolvable_unitarySU_two_one hE hm1 hm3
    exact Group.isSolvable_of_isSolvable_injective (f := e1.toMonoidHom) e1.injective
  haveI : Group.IsSolvable ↥(sesqSpecialUnitaryGroup Hf) := hSU
  have hkerSolv : Group.IsSolvable D.ker := by
    rw [hker]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).injective
  haveI : Group.IsSolvable D.ker := hkerSolv
  obtain ⟨e2⟩ := nonempty_kerImage_mulEquiv (orbitFactor (spForm r K) (spLin r K x) (h : K[X])) ψ D
  have hImgSolv : Group.IsSolvable
      ↥(kerImage (orbitFactor (spForm r K) (spLin r K x) (h : K[X])) ψ D) :=
    Group.isSolvable_of_surjective (f := e2.symm.toMonoidHom) e2.symm.surjective
  rw [hspec]
  exact hImgSolv

theorem smu_commutator_le_specialBlock {r : ℕ} {K : Type} [Field K] {x : StatedSp r K}
    (h : K[X]) :
    ⁅orbitFactor (spForm r K) (spLin r K x) h,
      orbitFactor (spForm r K) (spLin r K x) h⁆ ≤
      specialBlock (spForm r K) (spLin r K x) h := by
  refine Subgroup.commutator_le.mpr fun g hg g' hg' => ?_
  have hmem : ⁅g, g'⁆ ∈ orbitFactor (spForm r K) (spLin r K x) h :=
    commutator_self_le _ (Subgroup.commutator_mem_commutator hg hg')
  refine (mem_specialBlock (B := spForm r K) (x := spLin r K x)).mpr
    ⟨hmem, orbitFactor_le_gl_centralizer hmem, ?_⟩
  have h1 : (⟨⁅g, g'⁆, orbitFactor_le_gl_centralizer hmem⟩ : gl_centralizer (spLin r K x)) =
      ⁅(⟨g, orbitFactor_le_gl_centralizer hg⟩ : gl_centralizer (spLin r K x)),
        (⟨g', orbitFactor_le_gl_centralizer hg'⟩ : gl_centralizer (spLin r K x))⁆ := rfl
  rw [h1, map_commutatorElement, commutatorElement_def,
    mul_comm (blockDetHom (spLin r K x) h _), mul_inv_cancel_right, mul_inv_cancel]

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p m : ℕ}
  {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K}

theorem smuQuad_mem_primaryFactors (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (hζ : Function.Injective ζ) (f₀ : Fin m → Multiplicative (ZMod p))
    {c : Multiplicative (ZMod p)} (hc : c ≠ 1) {S : Finset (Fin m)}
    (hS : ∀ i, i ∈ S ↔ f₀ i = c ∨ f₀ i = c⁻¹) (hSne : S.Nonempty) :
    smuQuad ((ζ c : Matrix (Fin 2) (Fin 2) K).trace) ∈
      primaryFactors (spEnd (spPlaneTorus m ζ f₀)) := by
  classical
  have hirr := irreducible_smuQuad hp hp2 hpq hζ hc
  refine mem_primaryFactors.mpr ⟨hirr, smuQuad_monic _, ?_⟩
  by_contra hndvd
  obtain ⟨u, w, huw⟩ := (Irreducible.coprime_iff_not_dvd hirr).mpr hndvd
  obtain ⟨i, hi⟩ := hSne
  have hesupp : SmuSuppIn S (Pi.single (Sum.inl i) (1 : K) : Fin m ⊕ Fin m → K) :=
    smu_suppIn_single (by simpa using hi)
  have h0e := aeval_smuQuad_suppIn (ζ := ζ) hS hesupp
  have hone : aeval (spEnd (spPlaneTorus m ζ f₀))
      (u * smuQuad ((ζ c : Matrix (Fin 2) (Fin 2) K).trace) +
        w * minpoly K (spEnd (spPlaneTorus m ζ f₀))) = 1 := by
    rw [huw]; simp
  have h1 := congrArg (fun T => T (Pi.single (Sum.inl i) (1 : K) : Fin m ⊕ Fin m → K)) hone
  simp only [map_add, map_mul, minpoly.aeval, LinearMap.add_apply, Module.End.mul_apply, h0e,
    map_zero, mul_zero, zero_add, Module.End.one_apply] at h1
  have h2 := congrFun h1 (Sum.inl i)
  simp at h2

theorem suppOff_of_mem_primaryComponent (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (hζ : Function.Injective ζ) (f₀ : Fin m → Multiplicative (ZMod p))
    {c : Multiplicative (ZMod p)} (hc : c ≠ 1) {S : Finset (Fin m)}
    (hS : ∀ i, i ∈ S ↔ f₀ i = c ∨ f₀ i = c⁻¹) (hSne : S.Nonempty)
    {b : K[X]} (hb : b ∈ primaryFactors (spEnd (spPlaneTorus m ζ f₀)))
    (hbne : b ≠ smuQuad ((ζ c : Matrix (Fin 2) (Fin 2) K).trace)) {v : Fin m ⊕ Fin m → K}
    (hv : v ∈ primaryComponent (spEnd (spPlaneTorus m ζ f₀)) b) : SmuSuppOff S v := by
  classical
  have hmem := smuQuad_mem_primaryFactors hp hp2 hpq hζ f₀ hc hS hSne
  obtain ⟨u, w, huw⟩ := isCoprime_of_mem_primaryFactors hb hmem hbne
  have hv0 : aeval (spEnd (spPlaneTorus m ζ f₀)) b v = 0 := mem_primaryComponent.mp hv
  have hub : aeval (spEnd (spPlaneTorus m ζ f₀)) (u * b) v = 0 := by
    rw [map_mul, Module.End.mul_apply, hv0, map_zero]
  have h1 : aeval (spEnd (spPlaneTorus m ζ f₀))
      (u * b + w * smuQuad ((ζ c : Matrix (Fin 2) (Fin 2) K).trace)) v = v := by
    rw [huw]; simp
  rw [map_add, LinearMap.add_apply, hub, zero_add, mul_comm, map_mul, Module.End.mul_apply] at h1
  rw [← h1]
  exact aeval_smuQuad_suppOff (ζ := ζ) hS _

theorem smu_mem_spSupported_of_fix (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (hζ : Function.Injective ζ) (f₀ : Fin m → Multiplicative (ZMod p))
    {c : Multiplicative (ZMod p)} (hc : c ≠ 1) {S : Finset (Fin m)}
    (hS : ∀ i, i ∈ S ↔ f₀ i = c ∨ f₀ i = c⁻¹) (hSne : S.Nonempty)
    {y : StatedSp m K} (hyc : y * spPlaneTorus m ζ f₀ = spPlaneTorus m ζ f₀ * y)
    (hyfix : ∀ v : Fin m ⊕ Fin m → K, SmuSuppOff S v →
      ((y : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = v) :
    y ∈ spSupported (spPlaneTorus m ζ f₀)
      {smuQuad ((ζ c : Matrix (Fin 2) (Fin 2) K).trace)} := by
  rw [mem_spSupported]
  refine ⟨hyc, fun k hk hkO v hv => ?_⟩
  have hkne : k ≠ smuQuad ((ζ c : Matrix (Fin 2) (Fin 2) K).trace) := fun h => hkO (by simp [h])
  have := suppOff_of_mem_primaryComponent hp hp2 hpq hζ f₀ hc hS hSne hk hkne hv
  rw [spEnd_apply]
  exact hyfix v this

theorem smu_two_le_primaryMultiplicity (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (hζ : Function.Injective ζ) (f₀ : Fin m → Multiplicative (ZMod p))
    {c : Multiplicative (ZMod p)} (hc : c ≠ 1) {S : Finset (Fin m)}
    (hS : ∀ i, i ∈ S ↔ f₀ i = c ∨ f₀ i = c⁻¹) (hS2 : 2 ≤ S.card) :
    2 ≤ primaryMultiplicity (spEnd (spPlaneTorus m ζ f₀))
      (smuQuad ((ζ c : Matrix (Fin 2) (Fin 2) K).trace)) := by
  classical
  have hirr := irreducible_smuQuad hp hp2 hpq hζ hc
  haveI : Fact (Irreducible (smuQuad ((ζ c : Matrix (Fin 2) (Fin 2) K).trace))) := ⟨hirr⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hS2
  let idx : Fin 4 → Fin m ⊕ Fin m := ![Sum.inl a, Sum.inr a, Sum.inl b, Sum.inr b]
  have hidx : Function.Injective idx := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [idx]
  have hmemV : ∀ i, (Pi.single (idx i) (1 : K) : Fin m ⊕ Fin m → K) ∈
      primaryComponent (spEnd (spPlaneTorus m ζ f₀))
        (smuQuad ((ζ c : Matrix (Fin 2) (Fin 2) K).trace)) := by
    intro i
    rw [mem_primaryComponent]
    refine aeval_smuQuad_suppIn (ζ := ζ) hS (smu_suppIn_single ?_)
    fin_cases i <;> simp [idx, ha, hb]
  let fam : Fin 4 → primaryComponent (spEnd (spPlaneTorus m ζ f₀))
      (smuQuad ((ζ c : Matrix (Fin 2) (Fin 2) K).trace)) := fun i => ⟨_, hmemV i⟩
  have hli : LinearIndependent K fam := by
    refine LinearIndependent.of_comp (Submodule.subtype _) ?_
    have := (Pi.basisFun K (Fin m ⊕ Fin m)).linearIndependent.comp idx hidx
    simpa [Function.comp_def, fam, Pi.basisFun_apply] using this
  have h4 : 4 ≤ Module.finrank K (primaryComponent (spEnd (spPlaneTorus m ζ f₀))
      (smuQuad ((ζ c : Matrix (Fin 2) (Fin 2) K).trace))) := by
    simpa using hli.fintype_card_le_finrank
  have hfin := finrank_primaryComponent (spEnd (spPlaneTorus m ζ f₀))
    (smuQuad ((ζ c : Matrix (Fin 2) (Fin 2) K).trace))
  rw [smuQuad_natDegree] at hfin
  change 2 ≤ Module.finrank (AdjoinRoot (smuQuad ((ζ c : Matrix (Fin 2) (Fin 2) K).trace)))
    (primaryComponent (spEnd (spPlaneTorus m ζ f₀))
      (smuQuad ((ζ c : Matrix (Fin 2) (Fin 2) K).trace)))
  omega

end Torus

theorem mem_component_of_involution {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K ∨ Nat.card K = 2) {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1)
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    (f₀ : Fin m → Multiplicative (ZMod p)) {c : Multiplicative (ZMod p)} (hc : c ≠ 1)
    {J₀ : Subgroup (StatedSp m K)}
    (hJ : CFSG.Assembly.IsComponentOf J₀
      (Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K))))
    {S : Finset (Fin m)} (hS : ∀ i, i ∈ S ↔ f₀ i = c ∨ f₀ i = c⁻¹)
    (hsupp : ∀ j ∈ J₀, SmuOffFix S
      (((j : StatedSp m K) : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K))
    (hS2 : 2 ≤ S.card) {n : StatedSp m K} (hn2 : n * n = 1)
    (hnc : n * spPlaneTorus m ζ f₀ = spPlaneTorus m ζ f₀ * n)
    (hnfix : ∀ v : Fin m ⊕ Fin m → K, SmuSuppOff S v →
      ((n : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = v) :
    n ∈ J₀ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨f, hf1, hK⟩ := smu_exists_card_eq_two_pow K
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i₀, hi₀⟩ := hSne
  have hr : 1 ≤ m := Nat.succ_le_of_lt (Fin.pos i₀)
  set g : StatedSp m K := spPlaneTorus m ζ f₀ with hgdef
  have hpow : ∀ y : Multiplicative (ZMod p), y ^ p = 1 := fun y => by
    obtain ⟨z, rfl⟩ : ∃ z : ZMod p, Multiplicative.ofAdd z = y := ⟨Multiplicative.toAdd y, rfl⟩
    rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]
  have hAp : g ^ p = 1 := by
    rw [hgdef, ← map_pow]
    have : f₀ ^ p = 1 := funext fun i => hpow (f₀ i)
    rw [this, map_one]
  have hA1 : g ≠ 1 := by
    intro h
    have h1 : f₀ = 1 := spPlaneTorus_injective hζ m (h.trans (map_one _).symm)
    have h2 : f₀ i₀ = 1 := by rw [h1]; rfl
    rcases (hS i₀).mp hi₀ with h3 | h3
    · exact hc (h3.symm.trans h2)
    · exact hc (inv_eq_one.mp (h3.symm.trans h2))
  have hAo : orderOf g = p := orderOf_eq_prime hAp hA1
  have hker : (proj m K).ker = ⊥ := by
    rw [SymplecticHigher.ker_proj, ← Subgroup.card_eq_one, card_spScalars_eq_gcd K hr]
    have hK2 : 2 ∣ Nat.card K := hK ▸ dvd_pow_self 2 (by omega)
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have h2' : ¬ 2 ∣ Nat.card K - 1 := by omega
    exact Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2')
  have hinj : Function.Injective (proj m K) := (MonoidHom.ker_eq_bot_iff _).mp hker
  have hxo : orderOf (proj m K g) = p := by
    rw [orderOf_injective (proj m K) hinj g, hAo]
  obtain ⟨-, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf1 hK hp
    hp2 hp2 hr (proj m K g) hxo
  have blocks := hblocks g rfl hAo
  set t : K := ((ζ c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace with ht
  have hirr : Irreducible (smuQuad t) := irreducible_smuQuad hp hp2 hpq hζ hc
  have hmem : smuQuad t ∈ primaryFactors (spEnd g) :=
    smuQuad_mem_primaryFactors hp hp2 hpq hζ f₀ hc hS ⟨i₀, hi₀⟩
  let h₀ : primaryFactors (spEnd g) := ⟨smuQuad t, hmem⟩
  have hself : reciprocalPolynomial (h₀ : K[X]) = h₀ := reciprocalPolynomial_smuQuad t
  have hdeg : (h₀ : K[X]).natDegree = 2 := smuQuad_natDegree t
  have hSelf : SpSelfDualBlock 2 f p g h₀ := blocks.selfDual h₀ (smuQuad_ne_X_sub_one t) hself
  have hm2 : 2 ≤ primaryMultiplicity (spEnd g) (smuQuad t) :=
    smu_two_le_primaryMultiplicity hp hp2 hpq hζ f₀ hc hS hS2
  set Sb := specialBlock (spForm m K) (spLin m K g) (smuQuad t) with hSb
  have hSb_le : Sb ≤ sesqUnitaryGroup (spForm m K) :=
    specialBlock_le_unitaryCentralizer.trans (fun y hy => hy.1)
  set Bq : Subgroup (StatedSp m K) := Sb.comap (spLin m K) with hBq
  have hO : orbitFactor (spForm m K) (spLin m K g) (smuQuad t) =
      supportedUnitary (spForm m K) (spLin m K g) {smuQuad t} := by
    rw [orbitFactor_spForm, reciprocalPolynomial_smuQuad, Set.pair_eq_singleton]
  have h1 : J₀.map (spLin m K) ≤
      ⁅orbitFactor (spForm m K) (spLin m K g) (smuQuad t),
        orbitFactor (spForm m K) (spLin m K g) (smuQuad t)⁆ := by
    have hperf : ⁅J₀, J₀⁆ = J₀ := Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hJ.2.2.1)
    have hOle : J₀.map (spLin m K) ≤ orbitFactor (spForm m K) (spLin m K g) (smuQuad t) := by
      rintro _ ⟨j, hj, rfl⟩
      have hjc : j * g = g * j := Subgroup.mem_centralizer_singleton_iff.mp (hJ.1 hj)
      have hsup : j ∈ spSupported g {smuQuad t} :=
        smu_mem_spSupported_of_fix hp hp2 hpq hζ f₀ hc hS ⟨i₀, hi₀⟩ hjc
          (fun v hv => (hsupp j hj).mulVec_eq hv)
      rw [hO, ← map_spSupported]
      exact ⟨j, hsup, rfl⟩
    calc J₀.map (spLin m K) = ⁅J₀, J₀⁆.map (spLin m K) := by rw [hperf]
      _ = ⁅J₀.map (spLin m K), J₀.map (spLin m K)⁆ := Subgroup.map_commutator _ _ _
      _ ≤ _ := Subgroup.commutator_mono hOle hOle
  have hpair : ⁅orbitFactor (spForm m K) (spLin m K g) (smuQuad t),
        orbitFactor (spForm m K) (spLin m K g) (smuQuad t)⁆ = Sb ∧
      CFSG.IsQuasisimple Sb := by
    rcases hq with hK4 | hK2
    · obtain ⟨hcomm, hquasi⟩ :=
        smu_commutator_quasisimple (by rw [← hK]; omega) hself hdeg hSelf hm2
          ⟨fun _ => by rw [← hK]; exact hK4, fun _ => by rw [← hK]; omega⟩
      exact ⟨hcomm, hquasi⟩
    · have h2f : 2 ^ f = 2 := by rw [← hK, hK2]
      have hm4 : 4 ≤ primaryMultiplicity (spEnd g) (smuQuad t) := by
        by_contra hlt
        have hm1 : 1 ≤ primaryMultiplicity (spEnd g) (smuQuad t) := by omega
        have hm3 : primaryMultiplicity (spEnd g) (smuQuad t) ≤ 3 := by omega
        haveI : Group.IsSolvable Sb :=
          smu_isSolvable_specialBlock (ℓ := 2) (f := f) (p := p) hself hdeg hSelf h2f hm1 hm3
        have hcl : ⁅orbitFactor (spForm m K) (spLin m K g) (smuQuad t),
            orbitFactor (spForm m K) (spLin m K g) (smuQuad t)⁆ ≤ Sb :=
          smu_commutator_le_specialBlock (x := g) (smuQuad t)
        have hmap_le : J₀.map (spLin m K) ≤ Sb := h1.trans hcl
        haveI : Group.IsSolvable ↥(J₀.map (spLin m K)) :=
          Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hmap_le)
            (by intro a b hab; exact Subtype.ext (by simpa using congrArg Subtype.val hab))
        haveI : Group.IsSolvable ↥J₀ :=
          Group.isSolvable_of_isSolvable_injective
            (f := (Subgroup.equivMapOfInjective J₀ (spLin m K) spLin_injective).toMonoidHom)
            (Subgroup.equivMapOfInjective J₀ (spLin m K) spLin_injective).injective
        haveI : Nontrivial (J₀ ⧸ Subgroup.center ↥J₀) := hJ.2.2.2.toNontrivial
        haveI : Nontrivial ↥J₀ := (QuotientGroup.mk'_surjective (Subgroup.center ↥J₀)).nontrivial
        exact absurd hJ.2.2.1
          (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥J₀))
      obtain ⟨hcomm, hquasi⟩ :=
        smu_commutator_quasisimple (by rw [← hK]; omega) hself hdeg hSelf hm2
          ⟨fun h2 => False.elim (absurd (h2 ▸ hm4) (by norm_num)),
            fun h3 => False.elim (absurd (h3 ▸ hm4) (by norm_num))⟩
      exact ⟨hcomm, hquasi⟩
  have hBqq : CFSG.IsQuasisimple ↥Bq :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (comapSpLinEquiv Sb hSb_le).symm
      hpair.2
  have hBC : Bq ≤ Subgroup.centralizer ({g} : Set (StatedSp m K)) := by
    intro y hy
    refine Subgroup.mem_centralizer_singleton_iff.mpr (spLin_injective ?_)
    have hu : spLin m K y ∈ unitaryCentralizer (spForm m K) (spLin m K g) :=
      specialBlock_le_unitaryCentralizer (show spLin m K y ∈ Sb from hy)
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hu.2
  have hJle : J₀ ≤ Bq := by
    rw [hpair.1] at h1
    exact Subgroup.map_le_iff_le_comap.mp h1
  have hJBq : CFSG.Assembly.IsComponentOf J₀ Bq := hJ.of_le_of_le hJle hBC
  have hBqBq : CFSG.Assembly.IsComponentOf Bq Bq :=
    ⟨le_rfl, CFSG.Assembly.IsSubnormal.refl _,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hBqq⟩
  have hGW1 := CFSG.ClassicalInvolution.Q3.isComponentOf_of_open
    ((CFSG.Assembly.isComponentOf_iff_open).mp hJBq)
  have hGW2 := CFSG.ClassicalInvolution.Q3.isComponentOf_of_open
    ((CFSG.Assembly.isComponentOf_iff_open).mp hBqBq)
  have hJeq : J₀ = Bq := CFSG.Goldschmidt.G37.eq_of_isComponentOf_of_le hGW1 hGW2 hJle
  rw [hJeq]
  have hnsup : n ∈ spSupported g {smuQuad t} :=
    smu_mem_spSupported_of_fix hp hp2 hpq hζ f₀ hc hS ⟨i₀, hi₀⟩ hnc hnfix
  have hnO : spLin m K n ∈ orbitFactor (spForm m K) (spLin m K g) (smuQuad t) := by
    rw [hO, ← map_spSupported]
    exact ⟨n, hnsup, rfl⟩
  have hng := orbitFactor_le_gl_centralizer hnO
  refine mem_specialBlock.mpr ⟨hnO, hng, ?_⟩
  have hsq1 : (⟨spLin m K n, hng⟩ : gl_centralizer (spLin m K g)) * ⟨spLin m K n, hng⟩ = 1 := by
    apply Subtype.ext
    change spLin m K n * spLin m K n = 1
    rw [← map_mul, hn2, map_one]
  have hdet := congrArg (blockDetHom (spLin m K g) (smuQuad t)) hsq1
  rw [map_mul, map_one] at hdet
  haveI : Fact (Irreducible (smuQuad t)) := ⟨hirr⟩
  haveI : CharP (AdjoinRoot (smuQuad t)) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (smuQuad t))).injective 2
  exact ggTBJSpB_eq_one_of_mul_self hdet

end CFSG.StandardType.SympMinus

end
