module

public import CFSG.RankThree.PartOne.KE6.Phi6Core
public import CFSG.RankThree.PartOne.KE.NativeCyclicEndpoint
public import CFSG.RankThree.PartOne.KE.NativeCyclicLocalCore
public import CFSG.RankThree.PartOne.KE.OrdinaryEOuter

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2 CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_injective adjEmb_mem
  OddEndpoint cycloVal planeLocalCoreOdd_of_odd_kernels_abstract oddEndpoint_E6_of_native
  ordinary_E_outer_derived_subgroup_odd localCoreTrivialOn_noninner_E conj_injective_of_center_eq_bot)
open scoped Matrix MatrixGroups Pointwise commutatorElement

theorem card_core_conj_eq' {C : Type*} [Group C] [Finite C] {p : ℕ} (hp : p.Prime)
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

theorem phi6_actor (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {B : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hB : (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range ≤ B)
    (A : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hA : IsElementaryAbelian p A)
    (hcard : Nat.card A = p ^ 2)
    (hAin : A ≤ (MulAut.conj : adjointGroup Tag.E6 K →*
      MulAut (adjointGroup Tag.E6 K)).range) :
    ∃ a ∈ A, a ≠ 1 ∧ Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (adjointGroup Tag.E6 K)))))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq0 : ((ℓ ^ f : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  have hpq' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    rw [hK] at hpq
    exact hpq
  obtain ⟨hpL, ⟨ζ, hζ⟩, hr⟩ := phi6_prime_setup hq0 hp hpq'
  have hC : Subgroup.center (adjointGroup Tag.E6 K) = ⊥ := center_adjointGroup_eq_bot
  have hIntinj : Function.Injective
      (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)) :=
    conj_injective_of_center_eq_bot hC
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := e6_six_frame K hf hK hp hp3 hpq L
  set A₀ : Subgroup (adjointGroup Tag.E6 K) :=
    A.comap (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : adjointGroup Tag.E6 K →*
      MulAut (adjointGroup Tag.E6 K)) = A := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hAin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hIntinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  let f' : adjointGroup Tag.E6 K →* ModGL Tag.E6 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb Tag.E6 K L).comp (MulAut.conj c).toMonoidHom)
  have hf'inj : Function.Injective f' :=
    (MulAut.conj g0⁻¹).injective.comp (adjEmb_injective.comp (MulAut.conj c).injective)
  have hf'app : ∀ e, f' e = g0⁻¹ * adjEmb Tag.E6 K L (c * e * c⁻¹) * g0 := fun e => by
    simp [f']
  have hpow : ∀ e ∈ A₀, e ^ p = 1 := fun e he => by
    have h1 : (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)) (e ^ p) =
        1 := by
      rw [map_pow]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) _ he
    exact hIntinj (h1.trans (map_one _).symm)
  have hĒle : A₀.map f' ≤ phi6TorusTorsion L Fr p := by
    rintro _ ⟨e, he, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hf'app]
      exact hc e he
    · rw [← map_pow, hpow e he, map_one]
  have hĒcard : Nat.card (A₀.map f') = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hf'inj]
    exact hA₀card
  have hTcard : Nat.card (phi6TorusTorsion L Fr p) = p ^ 2 :=
    natCard_phi6TorusTorsion hFr hq0 hp hpq'
  have : Finite (phi6TorusTorsion L Fr p) :=
    Nat.finite_of_card_ne_zero (by rw [hTcard]; exact (pow_pos hp.pos 2).ne')
  have hĒeq : A₀.map f' = phi6TorusTorsion L Fr p :=
    Subgroup.eq_of_le_of_card_ge hĒle (by rw [hTcard, hĒcard])
  obtain ⟨t, htT, ht1, hwt⟩ := exists_twoA2_mem_phi6TorusTorsion (L := L) hp3 hFr hζ hr
  have htT0 : t ∈ twistedTorus (phi6N L) Fr := (mem_phi6TorusTorsion.1 htT).1
  have htA : t ∈ A₀.map f' := by
    rw [hĒeq]
    exact htT
  obtain ⟨e, he, het⟩ := htA
  have he1 : e ≠ 1 := fun h => ht1 (by rw [← het, h, map_one])
  have hxp : orderOf (c * e * c⁻¹) = p := by
    have hord : orderOf e = p := orderOf_eq_prime (hpow e he) he1
    have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective e
    simpa [MulAut.conj_apply, hord] using this
  have hh : g0⁻¹ * adjEmb Tag.E6 K L (c * e * c⁻¹) * g0 ∈ twistedTorus (phi6N L) Fr := by
    rw [← hf'app, het]
    exact htT0
  have hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel (g0⁻¹ * adjEmb Tag.E6 K L (c * e * c⁻¹) * g0) =
        parabolicRoots Tag.E6 supportA2A2 := by
    rw [← hf'app, het]
    exact hwt
  have hodd := e6_six_core_odd K hf hK hp hp3 hpq L hg0C hg0 hperf hxp hh hA2A2 hB
  refine ⟨MulAut.conj e, ?_, fun h1 => he1 (hIntinj (by rw [h1, map_one])), ?_⟩
  · rw [← hA₀map]
    exact ⟨e, he, rfl⟩
  · rw [← card_core_conj_eq' hp hB c e]
    exact hodd

theorem planeLocalCoreOdd_E6_six (K : Type) [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 6).eval (Nat.card K : ℤ)) :
    PlaneLocalCoreOdd p (adjointGroup Tag.E6 K) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hout := (ordinary_E_outer_derived_subgroup_odd .E6 (Or.inl rfl) K).1
  have hcore := localCoreTrivialOn_noninner_E .E6 (Or.inl rfl) K hp hp3
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1 := by
    simpa [exhaustionPhi] using hpf
  exact planeLocalCoreOdd_of_odd_kernels_abstract hp center_adjointGroup_eq_bot
    (e6_six_solvable K hf hK hp hp3 hpq L) hout hcore
    (fun B hB A _ hA hcard hAin => phi6_actor K hf hK hp hp3 hpq L hB A hA hcard hAin)

theorem oddEndpoint_E6_phi6 :
    OddEndpoint .E6 fun p ℓ f => (p : ℤ) ∣ cycloVal 6 ℓ f := by
  refine oddEndpoint_E6_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact planeLocalCoreOdd_E6_six K hℓ hf hK hp hp3 (by simpa [cycloVal, hK] using hc)

end CFSG.RankThree.PartOne.KE6
