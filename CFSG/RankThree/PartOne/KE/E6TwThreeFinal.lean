module

public import CFSG.RankThree.PartOne.KE.E6TwThreeCore
public import CFSG.RankThree.PartOne.KE.NativeCyclicTwisted

public noncomputable section

namespace CFSG.RankThree.PartOne.KETw3

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.E6
open CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne.KE (diagE6 twE6Emb twE6Emb_injective twE6Emb_mem
  twistedE6_outer_commutator_odd localCoreTrivialOn_noninner_twistedE6
  component_odd_conclusion_of_native OddEndpoint cycloVal planeLocalCoreOdd_of_odd_kernels_abstract)
open scoped Matrix MatrixGroups Pointwise commutatorElement

theorem oddSolvNormal_centralizer_conj {C : Type*} [Group C] (c₀ x : C)
    (h : OddSolvNormal (Subgroup.centralizer ({c₀ * x * c₀⁻¹} : Set C))) :
    OddSolvNormal (Subgroup.centralizer ({x} : Set C)) := by
  have hf : Function.Injective (MulAut.conj c₀ : MulAut C).toMonoidHom := (MulAut.conj c₀).injective
  have hrange : (MulAut.conj c₀ : MulAut C).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top_of_surjective _ (MulAut.conj c₀).surjective
  have hx : (MulAut.conj c₀ : MulAut C).toMonoidHom x = c₀ * x * c₀⁻¹ := by
    simp [MulAut.conj_apply]
  have hDeq : (MulAut.conj c₀ : MulAut C).toMonoidHom.range ⊓ Subgroup.centralizer
      ({(MulAut.conj c₀ : MulAut C).toMonoidHom x} : Set C) =
        Subgroup.centralizer ({c₀ * x * c₀⁻¹} : Set C) := by
    rw [hrange, hx, top_inf_eq]
  exact oddSolvNormal_of_mulEquiv
    ((centralizerEquivOfInjective _ hf x).trans (MulEquiv.subgroupCongr hDeq)) h

section Frame

theorem range_conj_twE6Emb {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (σ : K ≃+* K) (g : ModGL Tag.E6 Ω) :
    ((MulAut.conj g⁻¹).toMonoidHom.comp (twE6Emb K σ Ω)).range =
      phi3CStar K σ.toRingHom Ω g := by
  ext z
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨twE6Emb K σ Ω d, ⟨(d : ModGL TwistTag.E6.tag K), d.2, rfl⟩, rfl⟩
  · rintro ⟨u, ⟨d', hd', rfl⟩, rfl⟩
    exact ⟨⟨d', hd'⟩, rfl⟩

theorem exists_conj_into_TStar {ℓ f : ℕ} {K : Type} [Field K] {σ : K ≃+* K} {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {Fr : Ω →+* Ω} {g : ModGL Tag.E6 Ω} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    (E : Subgroup (twistedE6RootGroup K σ)) (hE : IsPGroup p E) :
    ∃ c₀ : twistedE6RootGroup K σ, ∀ e ∈ E,
      g⁻¹ * twE6Emb K σ Ω (c₀ * e * c₀⁻¹) * g ∈ phi3TStar K σ.toRingHom Ω Fr g := by
  classical
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hconj, -, -⟩, -, -⟩ :=
    twisted_E6_cyclotomic_three_full_torus_centralizers_and_odd_inner_solvable_kernels
      (σ := σ.toRingHom) hℓ hf hK (fun c => hσ c) hFr hp hp3 hpq hg hgn
  have hC0 : (twE6Emb K σ Ω).range = phi3C K σ.toRingHom Ω := by
    change ((baseChangeGL (algebraMap K Ω)).comp (twistedE6RootGroup K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  obtain ⟨c, hcmem, hc⟩ := hconj (E.map (twE6Emb K σ Ω)) (fun z hz => by
      obtain ⟨e, he, rfl⟩ := hz
      rw [← hC0]
      exact ⟨e, rfl⟩) (hE.map _)
  rw [← hC0] at hcmem
  obtain ⟨c₀, rfl⟩ := hcmem
  refine ⟨c₀, fun e he => ?_⟩
  obtain ⟨t, ht, hte⟩ := hc ⟨twE6Emb K σ Ω e, ⟨e, he, rfl⟩, rfl⟩
  have h1 : g * t * g⁻¹ = twE6Emb K σ Ω (c₀ * e * c₀⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    exact hte
  rw [← h1]
  have : g⁻¹ * (g * t * g⁻¹) * g = t := by group
  rw [this]
  exact ht

end Frame

section Odd

theorem twPhi3_oddSolvNormal {ℓ f : ℕ} (hℓ : ℓ.Prime) (K : Type) [Field K] [Finite K] (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1)
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    {x : twistedE6RootGroup K σ} (hxp : orderOf x = p)
    (hy : g⁻¹ * twE6Emb K σ Ω x * g ∈ phi3Torus Ω Fr) :
    OddSolvNormal (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let ιg : twistedE6RootGroup K σ →* ModGL Tag.E6 Ω :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (twE6Emb K σ Ω)
  have hιg : Function.Injective ιg := (MulAut.conj g⁻¹).injective.comp twE6Emb_injective
  have hιgx : ∀ d, ιg d = g⁻¹ * twE6Emb K σ Ω d * g := fun d => by simp [ιg]
  have hrange : ιg.range = phi3CStar K σ.toRingHom Ω g := range_conj_twE6Emb σ g
  set y : ModGL Tag.E6 Ω := g⁻¹ * twE6Emb K σ Ω x * g with hydef
  have hyC : y ∈ phi3CStar K σ.toRingHom Ω g := hrange ▸ ⟨x, (hιgx x).symm ▸ rfl⟩
  have hyT : y ∈ phi3TStar K σ.toRingHom Ω Fr g := ⟨hy, hyC⟩
  have hyp : orderOf y = p := by
    rw [← hxp, ← orderOf_injective ιg hιg x, hιgx]
  obtain ⟨-, hcent, -⟩ := twisted_E6_cyclotomic_three_full_torus_centralizers_and_odd_inner_solvable_kernels
    (σ := σ.toRingHom) hℓ hf hK (fun c => hσ c) hFr hp hp3 hpq hg hgn
  obtain ⟨-, -, -, -, hsolvD⟩ := hcent y hyT hyp
  set D : Subgroup (ModGL Tag.E6 Ω) := phi3CStar K σ.toRingHom Ω g ⊓ Subgroup.centralizer {y}
    with hD
  have hDeq : ιg.range ⊓ Subgroup.centralizer ({ιg x} : Set (ModGL Tag.E6 Ω)) = D := by
    rw [hrange, hD, hιgx x]
  exact oddSolvNormal_of_mulEquiv
    ((centralizerEquivOfInjective ιg hιg x).trans (MulEquiv.subgroupCongr hDeq)) hsolvD

end Odd

section Actor

theorem card_core_conj_eq {C : Type*} [Group C] [Finite C] {p : ℕ} (hp : p.Prime)
    {B : Subgroup (MulAut C)} (hB : (MulAut.conj : C →* MulAut C).range ≤ B) (c₀ e : C) :
    Nat.card ↥(inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer
      ({(MulAut.conj (c₀ * e * c₀⁻¹) : MulAut C)} : Set (MulAut C)))) =
    Nat.card ↥(inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer
      ({(MulAut.conj e : MulAut C)} : Set (MulAut C)))) := by
  have hc : (MulAut.conj c₀ : MulAut C) ∈ B := hB ⟨c₀, rfl⟩
  set φ : MulAut C ≃* MulAut C := MulAut.conj (MulAut.conj c₀ : MulAut C) with hφ
  have hBφ : B.map φ.toMonoidHom = B := by
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      exact mul_mem (mul_mem hc hb) (inv_mem hc)
    · intro b hb
      refine ⟨(MulAut.conj c₀)⁻¹ * b * MulAut.conj c₀, mul_mem (mul_mem (inv_mem hc) hb) hc, ?_⟩
      simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hφe : φ (MulAut.conj e) = MulAut.conj (c₀ * e * c₀⁻¹) := by
    simp [hφ, MulAut.conj_apply]
  have h := map_inSubgroup_theta_centralizer_mulEquiv hp φ B (MulAut.conj e)
  rw [hBφ, hφe] at h
  rw [← h, Subgroup.card_map_of_injective φ.injective]

theorem twPhi3_actor {ℓ f : ℕ} (hℓ : ℓ.Prime) (K : Type) [Field K] [Finite K] (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1)
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    {B : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hB : (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range ≤ B)
    (A : Subgroup (MulAut (twistedE6RootGroup K σ))) (hA : IsElementaryAbelian p A)
    (hcard : Nat.card A = p ^ 2)
    (hAin : A ≤ (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range) :
    ∃ a ∈ A, a ≠ 1 ∧ Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (twistedE6RootGroup K σ)))))) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hC : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hIntinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    KE.conj_injective_of_center_eq_bot hC
  set A₀ : Subgroup (twistedE6RootGroup K σ) :=
    A.comap (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : twistedE6RootGroup K σ →*
      MulAut (twistedE6RootGroup K σ)) = A := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hAin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hIntinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  obtain ⟨c₀, hc₀⟩ := exists_conj_into_TStar hℓ hf hK hσ hFr hp hp3 hpq hg hgn A₀ hpg
  let f' : twistedE6RootGroup K σ →* ModGL Tag.E6 Ω := (MulAut.conj g⁻¹).toMonoidHom.comp
    ((twE6Emb K σ Ω).comp (MulAut.conj c₀).toMonoidHom)
  have hf'inj : Function.Injective f' :=
    (MulAut.conj g⁻¹).injective.comp (twE6Emb_injective.comp (MulAut.conj c₀).injective)
  have hf'app : ∀ e, f' e = g⁻¹ * twE6Emb K σ Ω (c₀ * e * c₀⁻¹) * g := fun e => by
    simp [f']
  have hĒle : A₀.map f' ≤ phi3TStar K σ.toRingHom Ω Fr g := by
    rintro _ ⟨e, he, rfl⟩
    rw [hf'app]
    exact hc₀ e he
  have hĒcard : Nat.card (A₀.map f') = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hf'inj]
    exact hA₀card
  have hpow : ∀ e ∈ A₀, e ^ p = 1 := fun e he => by
    have h1 : (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) (e ^ p) =
        1 := by
      rw [map_pow]
      exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) _ he
    exact hIntinj (h1.trans (map_one _).symm)
  have hĒexp : ∀ u ∈ A₀.map f', u ^ p = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hpow e he, map_one]
  obtain ⟨-, -, hplanes⟩ := twisted_E6_cyclotomic_three_full_torus_centralizers_and_odd_inner_solvable_kernels
    (σ := σ.toRingHom) hℓ hf hK (fun c => hσ c) hFr hp hp3 hpq hg hgn
  obtain ⟨-, L, hL, -, -, hmeet⟩ := hplanes
  obtain ⟨u, huĒ, huL, hu1⟩ := hmeet (A₀.map f') hĒle hĒexp hĒcard 0
  obtain ⟨e, he, rfl⟩ := huĒ
  have hA2A2 := (hL 0).2.2 (f' e) huL hu1
  have he1 : e ≠ 1 := fun h => hu1 (by rw [h, map_one])
  have hx'1 : c₀ * e * c₀⁻¹ ≠ 1 := fun h => he1 (by simpa using h)
  have hx'p : orderOf (c₀ * e * c₀⁻¹) = p := by
    refine orderOf_eq_prime ?_ hx'1
    have h1 : (c₀ * e * c₀⁻¹) ^ p = c₀ * e ^ p * c₀⁻¹ := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← map_pow]
    rw [h1, hpow e he]
    group
  have hyT := hĒle ⟨e, he, rfl⟩
  have hy : g⁻¹ * twE6Emb K σ Ω (c₀ * e * c₀⁻¹) * g ∈ phi3Torus Ω Fr := by
    rw [← hf'app]
    exact hyT.1
  have hA2A2' : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel (g⁻¹ * twE6Emb K σ Ω (c₀ * e * c₀⁻¹) * g) =
        parabolicRoots Tag.E6 supportA2A2 := by
    rw [← hf'app]
    exact hA2A2
  have hodd := twPhi3_core_odd hℓ K hf hK σ hσ hp hp3 hpq Ω Fr hFr hg hgn hx'p hy hA2A2' hB
  refine ⟨MulAut.conj e, ?_, fun h1 => he1 (hIntinj (by rw [h1, map_one])), ?_⟩
  · rw [← hA₀map]
    exact ⟨e, he, rfl⟩
  · rw [← card_core_conj_eq hp hB c₀ e]
    exact hodd

end Actor

section Final

theorem planeLocalCoreOdd_twE6_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (K : Type) [Field K] [Finite K]
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) :
    PlaneLocalCoreOdd p (twistedE6RootGroup K σ) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let Ω := AlgebraicClosure K
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.E6.tag K) := CFSG.LieType.Chevalley.finite_modGL
  have hout := twistedE6_outer_commutator_odd hℓ hf hK σ hσ
  have hcore := localCoreTrivialOn_noninner_twistedE6 hℓ hf hK σ hσ hp hp3
  have hFr : ∀ c, (iterateFrobenius Ω ℓ f) c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g, hg, hgn⟩ := exists_inv_mul_twistE6_eq hf hFr
    (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) Ω phi3V)
  have hsolv : ∀ x : twistedE6RootGroup K σ, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))), V.Normal →
        Group.IsSolvable V → Odd (Nat.card V) := by
    intro x hxp
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨c₀, hc₀⟩ := exists_conj_into_TStar hℓ hf hK hσ hFr hp hp3 hpq hg hgn
      (Subgroup.zpowers x) (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxp, pow_one]))
    have h := hc₀ x (Subgroup.mem_zpowers x)
    have hxc : orderOf (c₀ * x * c₀⁻¹) = p := by
      have := orderOf_injective (MulAut.conj c₀).toMonoidHom (MulAut.conj c₀).injective x
      simpa [MulAut.conj_apply, hxp] using this
    exact oddSolvNormal_centralizer_conj c₀ x
      (twPhi3_oddSolvNormal hℓ K hf hK σ hσ hp hp3 hpq Ω _ hFr hg hgn hxc h.1)
  exact planeLocalCoreOdd_of_odd_kernels_abstract hp
    (exceptional_fixed_center_trivial TwistTag.E6 K σ) hsolv hout hcore
    (fun B hB A _ hA hcard hAin => twPhi3_actor hℓ K hf hK σ hσ hp hp3 hpq Ω _ hFr hg hgn hB A hA
      hcard hAin)

theorem oddEndpoint_twE6_phi3 :
    OddEndpoint .twistedE6 fun p ℓ f => (p : ℤ) ∣ cycloVal 3 ℓ f := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  have hm' : TwistedChevalleyModel (L ⧸ Subgroup.center L) .E6 (ℓ ^ f) := hmod.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hℓ hf hm'
  have hK2 : Nat.card K = (ℓ ^ f) ^ 2 := hK
  have hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1 := by
    have h : (p : ℤ) ∣ (((ℓ ^ f) ^ 2 + ℓ ^ f + 1 : ℕ) : ℤ) := by
      simpa [cycloVal, exhaustionPhi] using hc
    exact_mod_cast h
  exact (component_odd_conclusion_of_native hp (by omega) hE hEc ht ht1 hL hEL hSL e.symm
    (planeLocalCoreOdd_twE6_three hℓ K hf hK2 σ hσ hp hp3 hpq)).1

end Final

end CFSG.RankThree.PartOne.KETw3
