module

public import CFSG.RankThree.PartOne.KE6.Tw6A2A2Case
public import CFSG.RankThree.PartOne.KE6.Tw6D4Case
public import CFSG.RankThree.PartOne.KE6.Tw6Frame
public import CFSG.RankThree.PartOne.KE6.Tw6Torsion
public import CFSG.RankThree.PartOne.KE6.Phi3Solvable

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KE (adjEmb sigma_embedding_data subtorusImage mem_subtorusImage_iff
  twistedTorusOf mem_twistedTorusOf twistedFixedPoints mem_twistedFixedPoints subtorusSigma
  subtorusSigma_le_twistedTorusOf twE6Emb twE6Emb_injective twE6Emb_mem twE6Emb_fixed
  card_fixSubfield_twisted)
open scoped Matrix Pointwise

section Case

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem tw6_A2_kernelLayer {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hq3 : 3 ≤ ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {x : ModGL Tag.E6 Ω} (hx : x ∈ twistedTorusOf (tw6N Ω) (twistE6 Ω Fr))
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) :
    Nonempty (KernelLayer (tw6N Ω) (twistE6 Ω Fr) (torusRootKernel x) K Unit) := by
  obtain ⟨w, hw⟩ := hA2
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨hQ, hfin, hq, hcomm, h₀, hsl⟩ := tw6_A2_layer_gen hf hK hq3 hFr (fun α hα => hα.1)
    (tw6_torusRootKernel_smul_stable hFr hx) hw
  exact ⟨KernelLayer.single (fun α hα => hα.1) hQ hfin hq hcomm ⟨e6Index 0, h₀, hsl⟩⟩

end Case

theorem tw6_perx {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K] [CharP K ℓ]
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
      (∀ i, KL.P i ≤ ψ.range) ∧
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))), V.Normal →
        Group.IsSolvable V → ∀ v ∈ V,
          ψ v ∈ subtorusSigma (tw6N L) (twistE6 L (iterateFrobenius L ℓ f))
            (torusRootKernel (g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0)) := by
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
      (torusRootKernel h) (fixSubfield σ) ι'), ∃ (ι'' : Type) (KL' : KernelLayer (tw6N L)
        (twistE6 L Fr) (torusRootKernel h) (fixSubfield σ) ι'')
      (ψ : Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)) →* ModGL Tag.E6 L),
      Function.Injective ψ ∧ (∀ y, ψ y = g0⁻¹ * ι (c * (y : twistedE6RootGroup K σ) * c⁻¹) * g0) ∧
      (∀ y, ψ y ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (torusRootKernel h)) ∧
      (∀ y, tw6N L * twistE6 L Fr (ψ y) * (tw6N L)⁻¹ = ψ y) ∧
      (∀ i, KL'.P i ≤ ψ.range) ∧
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))), V.Normal →
        Group.IsSolvable V → ∀ v ∈ V,
          ψ v ∈ subtorusSigma (tw6N L) (twistE6 L Fr) (torusRootKernel h) := by
    intro ι' KL
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
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, -, hPψ, hψV⟩ := sigma_embedding_data ι twE6Emb_injective
      twE6Emb_mem (twistE6 L Fr) (twE6Emb_fixed Fr hcomm) (tw6N L) g0 hg0C hg0
      hperf hp hordW (fun α hα => hα.1) hrootneg KL.P KL.fin KL.quasi KL.le_span KL.le_fixed
      (fun i => (KL.le_span i).trans (rootSpan_le_adjointGroup L _)) KL.norm
      (fun y hy hyR hc => by
        obtain ⟨hyH, hyC⟩ := KL.cent y hy hc
        exact Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hyH, hyR⟩, hyC⟩)
      hx c hcS hkerZ
    exact ⟨ι', KL, ψ, hψinj, hψ, hψHQ, hψR, hPψ, hψV⟩
  rcases htri with hreg | hA2 | hA2A2 | hD4
  · have KL : KernelLayer (tw6N L) (twistE6 L Fr) (torusRootKernel h) (fixSubfield σ) Empty := by
      rw [hreg]
      exact KernelLayer.empty
    exact finish KL
  · obtain ⟨KL⟩ := tw6_A2_kernelLayer hf hkc hq3 hFr hh hA2
    exact finish KL
  · obtain ⟨KL⟩ := tw6_A2A2_kernelLayer hf hkc hq3 hFr hh hA2A2
    exact finish KL
  · obtain ⟨KL⟩ := tw6_D4_kernelLayer hf hkc hFr hh hD4
    exact finish KL

theorem e6_tw_six_solvable {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∀ x : twistedE6RootGroup K σ, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))), V.Normal →
        Group.IsSolvable V → Odd (Nat.card V) ∧ ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq0 : ((ℓ ^ f : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by have := hℓ.pos; omega)]
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := tw6_frame K hf hK σ hσ hp hp3 hpq L
  intro x hx V hVn hVs
  have hpg : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := hconj _ hpg
  have hh := hc x (Subgroup.mem_zpowers x)
  obtain ⟨ι', KL, ψ, hψinj, -, -, -, -, hψV⟩ := tw6_perx K hf hK σ hσ hp hp3 hpq L hg0C hg0 hperf
    hx c hh
  obtain ⟨hTcard, hTodd⟩ := natCard_tw6Torus (Ω := L) (Fr := Fr) hFr hq0
  let φ : V →* ModGL Tag.E6 L := ψ.comp V.subtype
  have hφinj : Function.Injective φ := hψinj.comp V.subtype_injective
  have hφT : ∀ v : V, φ v ∈ twistedTorusOf (tw6N L) (twistE6 L Fr) := fun v =>
    subtorusSigma_le_twistedTorusOf _ _ _ (hψV V hVn hVs v v.2)
  let φ' : V →* twistedTorusOf (tw6N L) (twistE6 L Fr) := φ.codRestrict _ hφT
  have hφ'inj : Function.Injective φ' := fun a a' haa => hφinj (congrArg Subtype.val haa)
  refine ⟨Odd.of_dvd_nat hTodd (Subgroup.card_dvd_of_injective φ' hφ'inj), fun v hv w hw => ?_⟩
  have hcomm := phi3_torusGroup_comm _ (mem_twistedTorusOf.1 (hφT ⟨v, hv⟩)).1 _
    (mem_twistedTorusOf.1 (hφT ⟨w, hw⟩)).1
  have h2 : φ (⟨v, hv⟩ * ⟨w, hw⟩) = φ (⟨w, hw⟩ * ⟨v, hv⟩) := by
    rw [map_mul, map_mul]
    exact hcomm
  have h3 := hφinj h2
  exact congrArg Subtype.val h3

theorem e6_tw_six_toral {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∀ x : twistedE6RootGroup K σ, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))), V.Normal →
        Group.IsSolvable V →
        (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  intro x hx V hVn hVs
  obtain ⟨hodd, hcomm⟩ := e6_tw_six_solvable K hf hK σ hσ hp hp3 hpq L x hx V hVn hVs
  refine ⟨hcomm, ?_⟩
  have hsub : Subsingleton {v : V // v ^ 2 = 1} := ⟨fun a b => by
    have h1 : ∀ v : V, v ^ 2 = 1 → v = 1 := fun v hv => by
      have hd1 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one hv
      have hd2 : orderOf v ∣ Nat.card V := orderOf_dvd_natCard v
      have hcop : Nat.Coprime 2 (Nat.card V) := Nat.coprime_two_left.2 hodd
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
      exact orderOf_eq_one_iff.1 this
    exact Subtype.ext ((h1 a a.2).trans (h1 b b.2).symm)⟩
  have : Nat.card {v : V // v ^ 2 = 1} ≤ 1 := by
    have : Finite {v : V // v ^ 2 = 1} := inferInstance
    exact Finite.card_le_one_iff_subsingleton.2 hsub
  omega

end CFSG.RankThree.PartOne.KE6
