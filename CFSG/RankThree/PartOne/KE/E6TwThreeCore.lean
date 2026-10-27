module

public import CFSG.RankThree.PartOne.KE.E6TwThreeFrame
public import CFSG.RankThree.PartOne.KE.E6TwThreeAbstract
public import CFSG.RankThree.PartOne.KE.E6TwFourData
public import CFSG.RankThree.Classical2.TwistedE6Phi3OddKernels
public import CFSG.LieType.Chevalley.E6GraphLeviIntersections
public import CFSG.LieType.SteinbergBRMulEquivCores

public noncomputable section

namespace CFSG.RankThree.PartOne.KETw3

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.E6
open CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne.KE (diagE6 twE6Emb twE6Emb_injective twE6Emb_mem)
open scoped Matrix MatrixGroups Pointwise commutatorElement

section OuterForm

variable {K : Type} [Field K] [Finite K]

theorem exists_adjoint_of_outer_form (σ : K ≃+* K)
    (hcoeΔ : ∀ u (g : twistedE6RootGroup K σ),
      ((compatDiagAutHom TwistTag.E6 K σ.toRingHom u g : twistedE6RootGroup K σ) :
        ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) * g *
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹)
    (hPσ : ∀ g : twistedE6RootGroup K σ,
      ((fieldActor σ σ g : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹)
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] (g' : twistedE6RootGroup K σ) (u : _) :
    ∃ a : ModGL Tag.E6 Ω, a ∈ adjointGroup Tag.E6 Ω ∧ ∀ y' : twistedE6RootGroup K σ,
      twE6Emb K σ Ω ((MulAut.conj g' * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
        fieldActor σ σ : MulAut (twistedE6RootGroup K σ)) y') =
          a * diagE6 Ω * twE6Emb K σ Ω y' * (diagE6 Ω)⁻¹ * a⁻¹ := by
  classical
  obtain ⟨D, hD⟩ : ∃ D, rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) = D :=
    ⟨_, rfl⟩
  have hgC : (g' : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag K :=
    ((graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom).trans inf_le_left) g'.2
  have hDΩ : baseChangeGL (algebraMap K Ω) D ∈ adjointGroup TwistTag.E6.tag Ω := by
    rw [← hD, baseChangeGL_rootDiagUnit]
    exact (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag Ω _).1
  have ha : baseChangeGL (algebraMap K Ω) ((g' : ModGL TwistTag.E6.tag K) * D) ∈
      adjointGroup TwistTag.E6.tag Ω := by
    rw [map_mul]
    exact mul_mem (baseChangeGL_mem_adjointGroup _ hgC) hDΩ
  refine ⟨(baseChangeGL (algebraMap K Ω) ((g' : ModGL TwistTag.E6.tag K) * D) :
    ModGL Tag.E6 Ω), ha, fun y' => ?_⟩
  have hηcoe : (((MulAut.conj g' * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
        fieldActor σ σ : MulAut (twistedE6RootGroup K σ)) y' : twistedE6RootGroup K σ) :
          ModGL TwistTag.E6.tag K) =
        ((g' : ModGL TwistTag.E6.tag K) * D) * diagramMap TwistTag.E6 K * y' *
          (diagramMap TwistTag.E6 K)⁻¹ * ((g' : ModGL TwistTag.E6.tag K) * D)⁻¹ := by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, hcoeΔ, hPσ, hD]
    group
  show baseChangeGL (algebraMap K Ω) (((MulAut.conj g' * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ σ : MulAut (twistedE6RootGroup K σ)) y' : twistedE6RootGroup K σ) :
        ModGL TwistTag.E6.tag K) =
      baseChangeGL (algebraMap K Ω) ((g' : ModGL TwistTag.E6.tag K) * D) *
        diagramMap TwistTag.E6 Ω * baseChangeGL (algebraMap K Ω) (y' : ModGL TwistTag.E6.tag K) *
          (diagramMap TwistTag.E6 Ω)⁻¹ *
            (baseChangeGL (algebraMap K Ω) ((g' : ModGL TwistTag.E6.tag K) * D))⁻¹
  rw [hηcoe]
  simp only [map_mul, map_inv, baseChangeGL_diagramMap]

end OuterForm

section Main

theorem twPhi3_core_odd {ℓ f : ℕ} (hℓ : ℓ.Prime) (K : Type) [Field K] [Finite K] (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1)
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    {x : twistedE6RootGroup K σ} (hxp : orderOf x = p)
    (hy : g⁻¹ * twE6Emb K σ Ω x * g ∈ phi3Torus Ω Fr)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel (g⁻¹ * twE6Emb K σ Ω x * g) =
        parabolicRoots Tag.E6 supportA2A2)
    {B : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hB : (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range ≤ B) :
    Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer
      ({(MulAut.conj x : MulAut (twistedE6RootGroup K σ))} :
        Set (MulAut (twistedE6RootGroup K σ)))))) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hC : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    KE.conj_injective_of_center_eq_bot hC
  let ιg : twistedE6RootGroup K σ →* ModGL Tag.E6 Ω :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (twE6Emb K σ Ω)
  have hιg : Function.Injective ιg := (MulAut.conj g⁻¹).injective.comp twE6Emb_injective
  have hιgx : ∀ d, ιg d = g⁻¹ * twE6Emb K σ Ω d * g := fun d => by
    simp [ιg]
  have hrange : ιg.range = phi3CStar K σ.toRingHom Ω g := by
    ext z
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨twE6Emb K σ Ω d, ⟨(d : ModGL TwistTag.E6.tag K), d.2, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨d', hd', rfl⟩, rfl⟩
      exact ⟨⟨d', hd'⟩, rfl⟩
  set y : ModGL Tag.E6 Ω := g⁻¹ * twE6Emb K σ Ω x * g with hydef
  have hyC : y ∈ phi3CStar K σ.toRingHom Ω g := hrange ▸ ⟨x, (hιgx x).symm ▸ rfl⟩
  have hyT : y ∈ phi3TStar K σ.toRingHom Ω Fr g := ⟨hy, hyC⟩
  have hyp : orderOf y = p := by
    rw [← hxp, ← orderOf_injective ιg hιg x, hιgx]
  obtain ⟨-, hcent, -⟩ := twisted_E6_cyclotomic_three_full_torus_centralizers_and_odd_inner_solvable_kernels
    (σ := σ.toRingHom) hℓ hf hK (fun c => hσ c) hFr hp hp3 hpq hg hgn
  obtain ⟨-, -, -, hA2A2c, hsolvD⟩ := hcent y hyT hyp
  obtain ⟨-, -, -, -, -, hqs, -, hres, -, -⟩ := hA2A2c hA2A2
  set D : Subgroup (ModGL Tag.E6 Ω) := phi3CStar K σ.toRingHom Ω g ⊓ Subgroup.centralizer {y}
    with hD
  have hDeq : ιg.range ⊓ Subgroup.centralizer ({ιg x} : Set (ModGL Tag.E6 Ω)) = D := by
    rw [hrange, hD, hιgx x]
  set Dx := Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)) with hDx
  obtain ⟨eD, heD⟩ : ∃ e : Dx ≃* ↥D,
      ∀ d, ((e d : ↥D) : ModGL Tag.E6 Ω) = ιg (d : twistedE6RootGroup K σ) :=
    ⟨(centralizerEquivOfInjective ιg hιg x).trans (MulEquiv.subgroupCongr hDeq), fun d => rfl⟩
  have hsolv : OddSolvNormal Dx :=
    oddSolvNormal_of_mulEquiv eD hsolvD
  set P' : Subgroup (twistedE6RootGroup K σ) :=
    (CFSG.perfectResidual Dx).map Dx.subtype with hP'def
  have hP'map : P'.map ιg = ⁅rootSpan Tag.E6 Ω (torusRootKernel y) ⊓ phi3FixedGroup Ω Fr,
      rootSpan Tag.E6 Ω (torusRootKernel y) ⊓ phi3FixedGroup Ω Fr⁆ := by
    rw [hP'def, Subgroup.map_map]
    have hcomp : ιg.comp Dx.subtype = D.subtype.comp eD.toMonoidHom :=
      MonoidHom.ext fun d => (heD d).symm
    rw [hcomp, ← Subgroup.map_map, CFSG.LieType.SteinbergBR.perfectResidual_map_equiv eD, hres]
  have hP'q : CFSG.IsQuasisimple P' := by
    have e : ↥P' ≃* ↥(⁅rootSpan Tag.E6 Ω (torusRootKernel y) ⊓ phi3FixedGroup Ω Fr,
        rootSpan Tag.E6 Ω (torusRootKernel y) ⊓ phi3FixedGroup Ω Fr⁆) :=
      (Subgroup.equivMapOfInjective P' ιg hιg).trans (MulEquiv.subgroupCongr hP'map)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqs
  refine core_odd_of_involutions_inner hp hC hB hsolv ?_
  intro η hη hη2
  obtain ⟨-, -, -, -, -, hcoeΔ, -, -, ⟨Θ, hΘ, -, -, -, -, hinvol⟩, hPσ, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  rcases hinvol η hη2 with hin | ⟨-, g', u, hηeq⟩
  · exact hin
  · exfalso
    obtain ⟨a, haA, hae⟩ := exists_adjoint_of_outer_form σ hcoeΔ hPσ Ω g' u
    rw [← hηeq] at hae
    obtain ⟨hηx, hηP⟩ := core_fixes_perfectResidual hp hC hB hP'q hη
    set P : ModGL Tag.E6 Ω := diagE6 Ω with hPdef
    set G₃ : ModGL Tag.E6 Ω := g⁻¹ * a * (P * g * P⁻¹) with hG₃def
    have hG₃adj : G₃ ∈ adjointGroup Tag.E6 Ω :=
      mul_mem (mul_mem (inv_mem hg) haA) (E6GraphLevi.diagramMap_conj_mem_adjointGroup' hg)
    have hfix : (G₃ * P) * y * (G₃ * P)⁻¹ = y := by
      have h1 := hae x
      rw [hηx] at h1
      calc (G₃ * P) * y * (G₃ * P)⁻¹
          = g⁻¹ * (a * P * twE6Emb K σ Ω x * P⁻¹ * a⁻¹) * g := by rw [hG₃def, hydef]; group
        _ = g⁻¹ * twE6Emb K σ Ω x * g := by rw [← h1]
    refine phi3_graph_contra (σ := σ.toRingHom) hℓ hf hK (fun c => hσ c) hFr hp hp3 hpq hy hyp hA2A2
      hG₃adj hfix (fun u' hu' => ?_)
    rw [← hP'map] at hu'
    obtain ⟨d, hd, rfl⟩ := hu'
    have h2 := hae d
    rw [hηP d hd] at h2
    calc (G₃ * P) * ιg d * (G₃ * P)⁻¹
        = g⁻¹ * (a * P * twE6Emb K σ Ω d * P⁻¹ * a⁻¹) * g := by rw [hG₃def, hιgx d]; group
      _ = ιg d := by rw [← h2, hιgx d]

end Main

end CFSG.RankThree.PartOne.KETw3
