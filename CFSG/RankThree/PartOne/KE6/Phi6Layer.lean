module

public import CFSG.RankThree.PartOne.KE6.Phi6A2A2Case

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus twistedFixedPoints
  mem_twistedFixedPoints)
open Matrix
open scoped Matrix MatrixGroups Pointwise commutatorElement

variable {Ω : Type} [Field Ω]

section Transport

variable {Fr : Ω →+* Ω}

theorem phi6_A2A2_transport' [IsAlgClosed Ω] {q p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hFr : ∀ c, Fr c = c ^ q) {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (hr : ((q : ℕ) : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ phi6TorusTorsion Ω Fr p) (hx1 : x ≠ 1)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) :
    ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2 ∧
      (rootSpan Tag.E6 Ω (torusRootKernel x)).map
          (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
        subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56 ∧
      ∃ π π' : Equiv.Perm (Fin 3),
        (∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
          phi6ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
            pinnedX Tag.E6 Ω (chainRoot chain56 (π i) (π j)) (e * Fr c)) ∧
        (∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
          phi6ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain56 i j) c) =
            pinnedX Tag.E6 Ω (chainRoot chain13 (π' i) (π' j)) (e * Fr c)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨⟨a, b⟩, hab⟩ := (mem_phi6TorusTorsion_iff hFr hζ hr x).1 hx
  have hab0 : (a, b) ≠ 0 := fun h => hx1 (by
    rw [← hab, h, ofAdd_zero, map_one])
  have hker0 : torusRootKernel x = rootKernel (eisensteinColumn (q : ZMod p) a b) := by
    rw [← hab]
    exact torusRootKernel_phi3TorsionHom hζ _ a b
  obtain ⟨w₀, hw₀⟩ := hA2A2
  rw [hker0] at hw₀
  have hne : (rootKernel (eisensteinColumn (q : ZMod p) a b)).Nonempty := by
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
    obtain ⟨e, he, hθ⟩ := exists_conj_phi6Theta_pinnedX (Fr := Fr) w hβ
    have hπij : (w * e6CoxeterSq * w⁻¹) • chainRoot chain13 i j =
        chainRoot chain56 (π i) (π j) := hπ i j
    exact ⟨e, he, fun c => by rw [hθ, hπij]⟩
  · have hβ : IsRoot Tag.E6 (chainRoot chain56 i j) := isRoot_chainRoot56 hij
    obtain ⟨e, he, hθ⟩ := exists_conj_phi6Theta_pinnedX (Fr := Fr) w hβ
    have hπij : (w * e6CoxeterSq * w⁻¹) • chainRoot chain56 i j =
        chainRoot chain13 (π' i) (π' j) := hπ' i j
    exact ⟨e, he, fun c => by rw [hθ, hπij]⟩


end Transport

section LayerSection

variable {Fr : Ω →+* Ω}

theorem phi6_A2A2_layer {K : Type} [Field K] [Finite K] [Algebra K Ω] [IsAlgClosure K Ω]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ twistedTorus (phi6N Ω) Fr) (hxp : orderOf x = p)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) :
    ∃ (w : WeylGroup Tag.E6) (k₂ : Subfield Ω) (h₁ h₂ : SL(3, Ω)),
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2 ∧
      (∀ c, c ∈ k₂ ↔ c ^ (ℓ ^ f) ^ 2 = c) ∧
      ∀ A : SL(3, k₂), (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ *
        twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
          h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
            h₂⁻¹) * canonicalRep (coxeterSystem Tag.E6) Ω w ∈
        phi6P Ω Fr (torusRootKernel x) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : ((ℓ ^ f : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  obtain ⟨hpΩ, ⟨ζ, hζ⟩, hr⟩ := phi6_prime_setup hq0 hp hpq
  have hxp' : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have hxT : x ∈ phi6TorusTorsion Ω Fr p := ⟨hx, hxp'⟩
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  obtain ⟨w, hwx, hQ₁₂, π, π', h12, h21⟩ := phi6_A2A2_transport' hp3 hFr hζ hr hxT hx1 hA2A2
  obtain ⟨θ, hθ, a, b, hab⟩ := exists_exchanged_layer_pos hFrs (phi6ThetaConj Ω Fr w)
    (phi6ThetaConj_injective w) π π' h12 h21
  obtain ⟨k₂, hk₂, h₁, h₂, ψ, hψ, hψfix, -, hqs9, -, -, -, hcardcenter9, hfin9, hindex9, hder9⟩ := CFSG.RankThree.Classical.SteinbergBY.exchanged_sl3_central_product_frobenius_full_fixed_layer hℓ hf hK Fr
    hFr twoA2MulSup twoA2MulSup_surjective (fun xy => twoA2MulSup_eq_one_iff xy.1 xy.2) θ a b hab
  set Y := phi6Qθ Ω Fr (torusRootKernel x) with hYdef
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hYF : Y.map (MulAut.conj n).toMonoidHom =
      (fixSubgroup θ).map (subsystemGroup Tag.E6 Ω support13 ⊔
        subsystemGroup Tag.E6 Ω support56).subtype :=
    map_conj_phi6Qθ hQ₁₂ θ hθ
  let F : ↥(subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56) →*
      ModGL Tag.E6 Ω := (MulAut.conj n).symm.toMonoidHom.comp (Subgroup.subtype _)
  have hF : Function.Injective F := (MulAut.conj n).symm.injective.comp Subtype.val_injective
  have hFapp : ∀ y, F y = n⁻¹ * (y : ModGL Tag.E6 Ω) * n := fun y => by
    simp [F, MulAut.conj_symm_apply]
  have hYf : (fixSubgroup θ).map F = Y := by
    have hid : (MulAut.conj n).symm.toMonoidHom.comp (MulAut.conj n).toMonoidHom =
        MonoidHom.id _ := MonoidHom.ext fun y => by simp
    rw [show F = (MulAut.conj n).symm.toMonoidHom.comp (Subgroup.subtype _) from rfl,
      ← Subgroup.map_map, ← hYF, Subgroup.map_map, hid, Subgroup.map_id]
  set ψ' : SL(3, k₂) →* ModGL Tag.E6 Ω := F.comp ψ with hψ'def
  have hder' : ⁅fixSubgroup θ, fixSubgroup θ⁆ = ψ.range := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hψfix, ← hder9, commutator_def,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hrange : ψ'.range = ⁅Y, Y⁆ := by
    rw [← hYf, ← Subgroup.map_commutator, hder', MonoidHom.range_comp]
  refine ⟨w, k₂, h₁, h₂, hwx, hk₂, fun A => ?_⟩
  have hmem : ψ' A ∈ ⁅Y, Y⁆ := hrange ▸ ⟨A, rfl⟩
  have hψA : (ψ A : ModGL Tag.E6 Ω) = twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A *
      h₁⁻¹, h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
        h₂⁻¹) := by
    rw [hψ A]
    rfl
  have hψ'A : ψ' A = n⁻¹ * (ψ A : ModGL Tag.E6 Ω) * n := hFapp (ψ A)
  rw [← hψA, ← hψ'A]
  exact hmem

end LayerSection

end CFSG.RankThree.PartOne.KE6
