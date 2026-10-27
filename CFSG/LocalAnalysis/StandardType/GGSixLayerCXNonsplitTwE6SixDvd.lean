module

public import CFSG.RankThree.PartOne.KE6.Tw6Solvable
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6SixDvdLayers
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Gen
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951

public noncomputable section

namespace CFSG.StandardType.TwE6Nonsplit

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Lang.SeitzPlane CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.RankThree.PartOne.KE (twistedTorusOf mem_twistedTorusOf twistedFixedPoints
  mem_twistedFixedPoints subtorusImage mem_subtorusImage_iff subtorusSigma
  subtorusSigma_le_twistedTorusOf adjEmb sigma_embedding_data twE6Emb twE6Emb_injective
  twE6Emb_mem twE6Emb_fixed card_fixSubfield_twisted)
open CFSG.RankThree.PartOne.KE6 (KernelLayer phi3_kernel_types tw6_frame tw6N tw6Theta tw6ThetaConj tw6_prime_setup
  exists_column_of_tw6Torus e6Six_data not_dvd_card_weyl_E6 tw6_torusRootKernel_smul_stable
  phi3_torusGroup_comm)
open CFSG.RankThree.Classical2 (twistE6)
open CFSG.RankThree.Lattice (e6T3W toMat lget)
open CFSG.Assembly (IsComponentOf)
open scoped Matrix MatrixGroups Pointwise


theorem tw6_perx_dvd {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL Tag.E6 L} (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : twistE6 L (iterateFrobenius L ℓ f) g0 = g0 * tw6N L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 L (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range)
    {x : twistedE6RootGroup K σ} (hx : orderOf x = p) (c : twistedE6RootGroup K σ)
    (hh : g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L ℓ f))) :
    ∃ (ι' : Type) (KL : KernelLayer (tw6N L) (twistE6 L (iterateFrobenius L ℓ f))
        (torusRootKernel (g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0)) (fixSubfield σ) ι')
      (ψ : Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)) →* ModGL Tag.E6 L),
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * twE6Emb K σ L (c * (y : twistedE6RootGroup K σ) * c⁻¹) * g0) ∧
      (∀ y, ψ y ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L
        (torusRootKernel (g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0))) ∧
      (∀ y, tw6N L * twistE6 L (iterateFrobenius L ℓ f) (ψ y) * (tw6N L)⁻¹ = ψ y) ∧
      (∀ i, KL.P i ≤ ψ.range) ∧ (∀ i, p ∣ Nat.card ↥(KL.P i)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq0 : ((ℓ ^ f : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by have := hℓ.pos; omega)]
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by
      change algebraMap K L (σ c) = Fr (algebraMap K L c)
      rw [hσ, hFr, map_pow]
  have : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
  have : IsAlgClosure (fixSubfield σ) L := IsAlgClosure.ofAlgebraic (fixSubfield σ) K L
  have : Finite (fixSubfield σ) := inferInstance
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_twisted hℓ hf hK σ hσ
  have hpqN : p ∣ Nat.card (fixSubfield σ) ^ 2 - Nat.card (fixSubfield σ) + 1 := by
    rw [hkc]
    exact nat_dvd_phiSix_of_int (Nat.one_le_pow _ _ hℓ.pos) hpq
  have hCharP : CharP L ℓ := inferInstance
  have : CharP L ℓ := hCharP
  obtain ⟨hpL, ⟨ζ, hζ⟩, hr⟩ := tw6_prime_setup hq0 hp hpq
  have hp7 : 7 ≤ p := (e6Six_data hp hp3 hpq).2.2.2.2.1
  have hq3 : 3 ≤ ℓ ^ f := by
    by_contra hlt
    have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
    have h2 : ℓ ^ f = 2 := by omega
    rw [h2] at hpq
    norm_num at hpq
    have := Int.le_of_dvd (by norm_num) hpq
    omega
  have hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E6) := not_dvd_card_weyl_E6 hp (by omega)
  set ι : twistedE6RootGroup K σ →* ModGL Tag.E6 L := twE6Emb K σ L with hιdef
  set h : ModGL Tag.E6 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hh).1
  have hb' : rootDiagUnit .E6 b = g0⁻¹ * ι (c * x * c⁻¹) * g0 := hb.symm
  have hordh : orderOf h = p := by
    have e1 : orderOf h = orderOf (ι (c * x * c⁻¹)) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
        (ι (c * x * c⁻¹))
      rw [hhdef]
      simpa [MulAut.conj_apply] using this
    have e2 : orderOf (ι (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
      orderOf_injective ι twE6Emb_injective _
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
    obtain ⟨z, -, hzc, hzker, hz0⟩ := exists_column_of_tw6Torus hFr hζ hh hhp
    rw [hzker]
    exact phi3_kernel_types (by omega) z (hz0 hh1) _ hzc
  have hrootneg : ∀ α ∈ torusRootKernel h, -α ∈ torusRootKernel h := fun α hα => by
    rw [hb, torusRootKernel_rootDiagUnit] at hα ⊢
    exact ⟨CFSG.LieType.Chevalley.IsRoot.neg hα.1,
      by rw [CFSG.RankThree.Classical2.rootChar_neg', hα.2, inv_one]⟩
  have finish : ∀ {ι' : Type} (KL : KernelLayer (tw6N L) (twistE6 L Fr)
      (torusRootKernel h) (fixSubfield σ) ι'), (∀ i, p ∣ Nat.card ↥(KL.P i)) →
      ∃ (ι'' : Type) (KL' : KernelLayer (tw6N L)
        (twistE6 L Fr) (torusRootKernel h) (fixSubfield σ) ι'')
      (ψ : Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)) →* ModGL Tag.E6 L),
      Function.Injective ψ ∧ (∀ y, ψ y = g0⁻¹ * ι (c * (y : twistedE6RootGroup K σ) * c⁻¹) * g0) ∧
      (∀ y, ψ y ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (torusRootKernel h)) ∧
      (∀ y, tw6N L * twistE6 L Fr (ψ y) * (tw6N L)⁻¹ = ψ y) ∧
      (∀ i, KL'.P i ≤ ψ.range) ∧ (∀ i, p ∣ Nat.card ↥(KL'.P i)) := by
    intro ι' KL hKL
    have hcS : c * x * c⁻¹ ∈ subtorusImage ι g0
        (subtorusSigma (tw6N L) (twistE6 L Fr) (torusRootKernel h)) := by
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
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, -, hPψ, -⟩ := sigma_embedding_data ι twE6Emb_injective
      twE6Emb_mem (twistE6 L Fr) (twE6Emb_fixed Fr hcomm) (tw6N L) g0 hg0C hg0
      hperf hp hordW (fun α hα => hα.1) hrootneg KL.P KL.fin KL.quasi KL.le_span KL.le_fixed
      (fun i => (KL.le_span i).trans (rootSpan_le_adjointGroup L _)) KL.norm
      (fun y hy hyR hc => by
        obtain ⟨hyH, hyC⟩ := KL.cent y hy hc
        exact Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hyH, hyR⟩, hyC⟩)
      hx c hcS hkerZ
    exact ⟨ι', KL, ψ, hψinj, hψ, hψHQ, hψR, hPψ, hKL⟩
  rcases htri with hreg | hA2 | hA2A2 | hD4
  · have KL : KernelLayer (tw6N L) (twistE6 L Fr) (torusRootKernel h) (fixSubfield σ) Empty := by
      rw [hreg]
      exact KernelLayer.empty
    exact finish KL (fun e => e.elim)
  · obtain ⟨KL, hKL⟩ := tw6_A2_kernelLayer_dvd hf hkc hq3 hFr hh hA2 hpqN
    exact finish KL hKL
  · obtain ⟨KL, hKL⟩ := tw6_A2A2_kernelLayer_dvd hf hkc hq3 hFr hh hA2A2 hpqN
    exact finish KL hKL
  · obtain ⟨KL, hKL⟩ := tw6_D4_kernelLayer_dvd hf hkc hFr hh hD4 hpqN
    exact finish KL hKL


theorem tw6_six_components_dvd {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∀ x : twistedE6RootGroup K σ, orderOf x = p →
      ∀ X : Subgroup (twistedE6RootGroup K σ),
        IsComponentOf X (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))) →
          p ∣ Nat.card X := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := tw6_frame K hf hK σ hσ hp hp3 hpq L
  intro x hx X hX
  have hpg : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := hconj _ hpg
  have hh := hc x (Subgroup.mem_zpowers x)
  obtain ⟨ι', KL, ψ, hψinj, -, hψT, hψθ, hPψ, hPd⟩ :=
    tw6_perx_dvd K hf hK σ hσ hp hp3 hpq L hg0C hg0 hperf hx c hh
  exact CFSG.StandardType.E6Nonsplit.dvd_card_of_isComponentOf_of_layers ψ hψinj KL.P hPψ
    KL.quasi
    (fun i d u hu => KL.norm i (ψ d) (hψT d) (mem_twistedFixedPoints.2 (hψθ d)) u hu)
    (Z := (torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)))
    (fun a ha b hb => phi3_torusGroup_comm a ha b hb)
    (fun d hd => (KL.cent (ψ d) (hψT d) hd).1) hPd hX

theorem dvd_card_of_isComponentOf_twE6_of_phiSix {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 6).eval ((2 ^ f : ℕ) : ℤ))
    {a : twistedE6RootGroup K σ} (ha : orderOf a = p)
    {X : Subgroup (twistedE6RootGroup K σ)}
    (hX : IsComponentOf X (Subgroup.centralizer ({a} : Set (twistedE6RootGroup K σ)))) :
    p ∣ Nat.card X := by
  have hpq : (p : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 2 - ((2 ^ f : ℕ) : ℤ) + 1 := by
    simpa [CFSG.RankThree.Chevalley.exhaustionPhi] using hpf
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  exact tw6_six_components_dvd (ℓ := 2) (K := K) (f := f) (L := AlgebraicClosure K)
    (σ := σ) hf hK hσ hp hp3 hpq a ha X hX

end CFSG.StandardType.TwE6Nonsplit
