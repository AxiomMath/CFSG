module

public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case

public noncomputable section

namespace CFSG.RankThree.PartOne.KETw3

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.E6
open CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise commutatorElement

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem phi3_A2A2_transport' [IsAlgClosed Ω] {q p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hFr : ∀ c, Fr c = c ^ q) {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (hr : (-(q : ZMod p)) ^ 2 - -(q : ZMod p) + 1 = 0) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ phi3TorusTorsion Ω Fr p) (hx1 : x ≠ 1)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) :
    ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2 ∧
      (rootSpan Tag.E6 Ω (torusRootKernel x)).map
          (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
        subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56 ∧
      ∃ π π' : Equiv.Perm (Fin 3),
        (∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
          phi3ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
            pinnedX Tag.E6 Ω (chainRoot chain56 (π j) (π i)) (e * Fr c)) ∧
        (∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
          phi3ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
            pinnedX Tag.E6 Ω (chainRoot chain13 (π' j) (π' i)) (e * Fr c)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨⟨a, b⟩, hab⟩ := (mem_phi3TorusTorsion_iff hFr hζ hr x).1 hx
  have hab0 : (a, b) ≠ 0 := fun h => hx1 (by
    rw [← hab, h, ofAdd_zero, map_one])
  have hker0 : torusRootKernel x = rootKernel (eisensteinColumn (-(q : ZMod p)) a b) := by
    rw [← hab]
    exact torusRootKernel_phi3TorsionHom hζ _ a b
  obtain ⟨w₀, hw₀⟩ := hA2A2
  rw [hker0] at hw₀
  have hne : (rootKernel (eisensteinColumn (-(q : ZMod p)) a b)).Nonempty := by
    have h1 : (parabolicRoots Tag.E6 supportA2A2).Nonempty := by
      rw [parabolicRoots_supportA2A2]
      exact ⟨_, Or.inl (chainRoot13_mem_parabolicRoots (show (0 : Fin 3) ≠ 1 by decide))⟩
    rw [← hw₀] at h1
    exact Set.image_nonempty.1 h1
  have hcard := ncard_rootKernel_of_image hw₀
  rw [ncard_parabolicRoots_supportA2A2] at hcard
  obtain ⟨-, -, -, -, h8⟩ := E6_Coxeter_square_eight_Eisenstein_root_kernel_lines
  obtain ⟨-, -, -, hline, -, hA2A2', hA2'⟩ := h8 p hp3 _ hr
  obtain ⟨k, hk⟩ := (hline a b hab0).1 hne
  have hk4 : k.val < 4 := by
    by_contra h
    obtain ⟨w', hw', -⟩ := hA2' k (by omega)
    have := (hw' a b hab0 hk).2
    omega
  obtain ⟨w, hw, -, -, ⟨π, hπ⟩, ⟨π', hπ'⟩⟩ := hA2A2' k hk4
  have hwker := (hw a b hab0 hk).1
  refine ⟨w, by rw [hker0]; exact hwker, ?_, π, π', fun i j hij => ?_, fun i j hij => ?_⟩
  · rw [hker0, (canonical_weyl_root_transport Tag.E6 Ω).1 w _ fun α hα => hα.1, hwker,
      rootSpan_supportA2A2]
  · have hβ : IsRoot Tag.E6 (chainRoot chain13 i j) := (chainRoot13_mem_parabolicRoots hij).1
    obtain ⟨e, he, hθ⟩ := exists_conj_phi3Theta_pinnedX (Fr := Fr) w hβ
    have hπij : (w * e6CoxeterSq * w⁻¹) • chainRoot chain13 i j =
        chainRoot chain56 (π i) (π j) := hπ i j
    refine ⟨e, he, fun c => ?_⟩
    rw [phi3ThetaConj_apply, hθ, hπij, ← chainRoot_swap]
  · have hβ : IsRoot Tag.E6 (chainRoot chain56 i j) := isRoot_chainRoot56 hij
    obtain ⟨e, he, hθ⟩ := exists_conj_phi3Theta_pinnedX (Fr := Fr) w hβ
    have hπij : (w * e6CoxeterSq * w⁻¹) • chainRoot chain56 i j =
        chainRoot chain13 (π' i) (π' j) := hπ' i j
    refine ⟨e, he, fun c => ?_⟩
    rw [phi3ThetaConj_apply, hθ, hπij, ← chainRoot_swap]

section Layer

variable {K : Type} [Field K] {σ : K →+* K} [Algebra K Ω]

theorem phi3_A2A2_layer [IsAlgClosure K Ω] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ phi3Torus Ω Fr) (hxp : orderOf x = p)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) :
    ∃ (w : WeylGroup Tag.E6) (k₂ : Subfield Ω) (h₁ h₂ : SL(3, Ω)),
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2 ∧
      (∀ c, c ∈ k₂ ↔ c ^ (ℓ ^ f) ^ 2 = c) ∧
      ∀ A : SL(3, k₂), (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ *
        twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
          h₂ * invTransposeMapSL Fr 3 (Matrix.SpecialLinearGroup.map k₂.subtype A) * h₂⁻¹) *
          canonicalRep (coxeterSystem Tag.E6) Ω w ∈
        ⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
          rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆ := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  obtain ⟨hpΩ, ⟨ζ, hζ⟩, hr⟩ := phi3_prime_setup (Ω := Ω) hf hp hpq
  have hxT0 : x ∈ phi3Torus Ω Fr := hx
  have hxp' : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have hxT : x ∈ phi3TorusTorsion Ω Fr p := ⟨hxT0, hxp'⟩
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  obtain ⟨w, hwx, hQ₁₂, π, π', h12, h21⟩ := phi3_A2A2_transport' hp3 hFr hζ hr hxT hx1 hA2A2
  obtain ⟨θ, hθ, a, b, hab⟩ := exists_exchanged_layer hFrs (phi3ThetaConj Ω Fr w)
    (phi3ThetaConj_injective w) π π' h12 h21
  set k₀ := RingHom.eqLocusField σ (RingHom.id K)
  have : Module.Finite k₀ K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic k₀ K := Algebra.IsAlgebraic.of_finite k₀ K
  have : IsAlgClosure k₀ Ω := IsAlgClosure.ofAlgebraic k₀ K Ω
  have hk₀card : Nat.card k₀ = ℓ ^ f := natCard_eqLocusField hℓ hf hK hσ
  set k₂ : Subfield Ω := RingHom.eqLocusField (Fr.comp Fr) (RingHom.id Ω)
  have hk₂ : ∀ c, c ∈ k₂ ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [RingHom.mem_eqLocusField, RingHom.comp_apply, hFr, hFr, RingHom.id_apply, ← pow_mul, sq]
  have hτ : ∀ X : SL(3, Ω), ((invTransposeMapSL Fr 3 X : SL(3, Ω)) :
      Matrix (Fin 3) (Fin 3) Ω) = (((X : Matrix (Fin 3) (Fin 3) Ω).map (· ^ (ℓ ^ f)))⁻¹)ᵀ :=
    fun X => by
      rw [coe_invTransposeMapSL]
      congr 3
      exact funext hFr
  obtain ⟨h₁, h₂, ψ, hψ, -, -, -, -, -, -, -, -, -, -, hder9⟩ :=
    negative_exchanged_SL3_central_product_fixed_layer hk₀card k₂ hk₂ (invTransposeMapSL Fr 3) hτ
      twoA2MulSup twoA2MulSup_surjective twoA2MulSup_eq_one_iff θ a b hab
  set Y := rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr with hYdef
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hYF : Y.map (MulAut.conj n).toMonoidHom =
      (fixSubgroup θ).map (subsystemGroup Tag.E6 Ω support13 ⊔
        subsystemGroup Tag.E6 Ω support56).subtype :=
    map_conj_inf_phi3FixedGroup hQ₁₂ θ hθ
  let F : ↥(subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56) →*
      ModGL Tag.E6 Ω := (MulAut.conj n).symm.toMonoidHom.comp (Subgroup.subtype _)
  have hFapp : ∀ y, F y = n⁻¹ * (y : ModGL Tag.E6 Ω) * n := fun y => by
    simp [F, MulAut.conj_symm_apply]
  have hYf : (fixSubgroup θ).map F = Y := by
    have hid : (MulAut.conj n).symm.toMonoidHom.comp (MulAut.conj n).toMonoidHom =
        MonoidHom.id _ := MonoidHom.ext fun y => by simp
    rw [show F = (MulAut.conj n).symm.toMonoidHom.comp (Subgroup.subtype _) from rfl,
      ← Subgroup.map_map, ← hYF, Subgroup.map_map, hid, Subgroup.map_id]
  set ψ' : SL(3, k₂) →* ModGL Tag.E6 Ω := F.comp ψ with hψ'def
  have hrange : ψ'.range = ⁅Y, Y⁆ := by
    rw [← hYf, ← Subgroup.map_commutator, hder9, MonoidHom.range_comp]
  refine ⟨w, k₂, h₁, h₂, hwx, hk₂, fun A => ?_⟩
  have hmem : ψ' A ∈ ⁅Y, Y⁆ := hrange ▸ ⟨A, rfl⟩
  have hψA : (ψ A : ModGL Tag.E6 Ω) = twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A *
      h₁⁻¹, h₂ * invTransposeMapSL Fr 3 (Matrix.SpecialLinearGroup.map k₂.subtype A) * h₂⁻¹) := by
    rw [hψ A]
    rfl
  have hψ'A : ψ' A = n⁻¹ * (ψ A : ModGL Tag.E6 Ω) * n := hFapp (ψ A)
  rw [← hψA, ← hψ'A]
  exact hmem

end Layer

end CFSG.RankThree.PartOne.KETw3
