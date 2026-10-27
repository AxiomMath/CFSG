module

public import CFSG.Quasithin.Background.SmithB42Sp4Excl

public section

namespace CFSG.Quasithin.B42Sp4

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

section Singleton

variable {F : Type} [Field F] [CharP F 2] [Fintype F] (k : Type) [Field k] [Algebra F k]

theorem tensorRepS_singleton_mulVec (j : ℕ) (g : antiSp F)
    (y : ((↥({j} : Finset ℕ)) → Fin 4) → k) (a : Fin 4) :
    (tensorRepS k {j} g).mulVec y (fun _ => a) =
      ∑ c : Fin 4, natRepS k j g a c * y (fun _ => c) := by
  have hU : Unique (↥({j} : Finset ℕ)) :=
    ⟨⟨⟨j, Finset.mem_singleton_self j⟩⟩, fun x => Subtype.ext (Finset.mem_singleton.mp x.2)⟩
  rw [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (Equiv.funUnique ↥({j} : Finset ℕ) (Fin 4)).symm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : (Equiv.funUnique ↥({j} : Finset ℕ) (Fin 4)).symm c = fun _ => c := rfl
  rw [this, tensorRepS_apply, Fintype.prod_unique]
  rw [Finset.mem_singleton.mp (default : ↥({j} : Finset ℕ)).2]

end Singleton

section Ident

variable {F : Type} [Field F] [CharP F 2] [Fintype F]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem dvd_of_shiftSet_singleton {f d i : ℕ} (hi : i < 2 * f)
    (h : shiftSet f (2 * d) {i} = {i}) : f ∣ d := by
  have h1 : (i + 2 * d) % (2 * f) = i := by
    have : (i + 2 * d) % (2 * f) ∈ shiftSet f (2 * d) {i} :=
      Finset.mem_image_of_mem _ (Finset.mem_singleton_self i)
    rw [h] at this
    exact Finset.mem_singleton.mp this
  have h2 : i + 2 * d ≡ i + 0 [MOD 2 * f] := by
    rw [add_zero]
    unfold Nat.ModEq
    rw [h1, Nat.mod_eq_of_lt hi]
  have h3 : 2 * d ≡ 0 [MOD 2 * f] := Nat.ModEq.add_left_cancel' i h2
  have h4 : 2 * f ∣ 2 * d := (Nat.modEq_zero_iff_dvd).mp h3
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4

theorem exists_ringHom_of_dvd {F D : Type} [Field F] [Field D] [Finite F] [Finite D] [CharP F 2]
    [CharP D 2] {f d : ℕ} (hF : Nat.card F = 2 ^ f) (hD : Nat.card D = 2 ^ d) (hfd : f ∣ d) :
    Nonempty (F →+* D) := by
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  let _ : Algebra (ZMod 2) D := ZMod.algebra D 2
  have : Fintype F := Fintype.ofFinite F
  have : Fintype D := Fintype.ofFinite D
  have hfF : Module.finrank (ZMod 2) F = f := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [ZMod.card, Fintype.card_eq_nat_card, hF] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have hfD : Module.finrank (ZMod 2) D = d := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [ZMod.card, Fintype.card_eq_nat_card, hD] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  obtain ⟨ι⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2) (K := F) (L := D)
    (by rw [hfF, hfD]; exact hfd)
  exact ⟨ι.toRingHom⟩

theorem exists_natural_of_four {f : ℕ} (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) [Fact (repOf π).IsIrreducible]
    (hnt : ∃ g, repOf π g ≠ 1) (hdim : Module.finrank (EndRing (repOf π)) M = 4) :
    ∃ (i : ℕ) (φ : M ≃+ (Fin 4 → F)), ∀ g w,
      φ (π g w) = (glMat (((minorAut F ^ i) g : antiSp F) : GL (Fin 4) F)).mulVec (φ w) := by
  classical
  set ρ := repOf π with hρ
  obtain ⟨d, hd1, hDcard, hdesc⟩ := sp4_descent hF hf hnt
  have hfinD : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) M := Module.Finite.of_finite
  have hchar : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  obtain ⟨E, _, _, _, ιF, ιD, S, hSne, hS, -, hshift, hdimW⟩ :=
    hdesc (Module.finBasis (EndRing ρ) M)
  have hS1 : S.card = 1 := by
    rw [hdim] at hdimW
    have h := (Nat.pow_right_injective (le_refl 2) (by
      rw [show (2 : ℕ) ^ (2 * S.card) = 4 ^ S.card by rw [pow_mul]; norm_num]
      rw [← hdimW]; norm_num : 2 ^ (2 * S.card) = 2 ^ 2))
    omega
  obtain ⟨i₀, rfl⟩ := Finset.card_eq_one.mp hS1
  have hi₀ : i₀ < 2 * f := Finset.mem_range.mp (hS (Finset.mem_singleton_self i₀))
  have hfd : f ∣ d := dvd_of_shiftSet_singleton hi₀ hshift
  have hFcard : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨ιF'⟩ := exists_ringHom_of_dvd hFcard hDcard hfd
  let _ : Algebra F (EndRing ρ) := ιF'.toAlgebra
  let b : Module.Basis (Fin 4) (EndRing ρ) M := Module.finBasisOfFinrankEq (EndRing ρ) M hdim
  obtain ⟨S', -, -, ⟨Φ⟩, hdim'⟩ := exists_label hF hf hnt b ιF' (RingHom.id (EndRing ρ))
  have hS'1 : S'.card = 1 := by
    have h := (Nat.pow_right_injective (le_refl 2) (by
      rw [show (2 : ℕ) ^ (2 * S'.card) = 4 ^ S'.card by rw [pow_mul]; norm_num]
      rw [← hdim']; norm_num : 2 ^ (2 * S'.card) = 2 ^ 2))
    omega
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hS'1
  let θ : M ≃+ (Fin 4 → EndRing ρ) :=
    (b.equivFun.toAddEquiv.trans Φ.symm.toLinearEquiv.toAddEquiv).trans
      (LinearEquiv.funCongrLeft (EndRing ρ) (EndRing ρ)
        (Equiv.funUnique ↥({i} : Finset ℕ) (Fin 4)).symm).toAddEquiv
  have hθ : ∀ w a, θ w a = Φ.symm (b.equivFun w) (fun _ => a) := fun w a => rfl
  have hcoord : ∀ (g : antiSp F) (w : M), b.equivFun (ρ g w) =
      matRepE b (RingHom.id (EndRing ρ)) g (b.equivFun w) := by
    intro g w
    rw [matRepE_apply]
    have := LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
    rw [repD_apply] at this
    simpa [CFSG.QuasithinUnique.Setup.SL2Modules.matRep] using this.symm
  have hact : ∀ (g : antiSp F) (w : M) (a : Fin 4),
      θ (π g w) a = ∑ c : Fin 4, ιF' (glMat (((minorAut F ^ i) g : antiSp F) :
        GL (Fin 4) F) a c) * θ w c := by
    intro g w a
    have h1 : θ (π g w) a = θ (ρ g w) a := rfl
    rw [h1, hθ, hcoord, equiv_apply Φ.symm g, CFSG.QuasithinUnique.Setup.X7.matRep_apply,
      tensorRepS_singleton_mulVec]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [natRepS_apply, Matrix.map_apply, hθ]
    rfl
  have hsurj : Function.Surjective ιF' := by
    obtain ⟨-, hirr⟩ :=
      (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp Fact.out
    let U₀ : AddSubgroup M :=
      { carrier := {w | ∀ a, θ w a ∈ ιF'.range}
        add_mem' := fun {x y} hx hy a => by
          rw [map_add, Pi.add_apply]
          exact ιF'.range.add_mem (hx a) (hy a)
        zero_mem' := fun a => by
          rw [map_zero, Pi.zero_apply]
          exact ιF'.range.zero_mem
        neg_mem' := fun {x} hx a => by
          rw [map_neg, Pi.neg_apply]
          exact ιF'.range.neg_mem (hx a) }
    let U : Submodule (ZMod 2) M := AddSubgroup.toZModSubmodule 2 U₀
    have hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U := by
      intro g u hu a
      have h1 : θ (ρ g u) a = θ (π g u) a := rfl
      rw [h1, hact]
      refine ιF'.range.sum_mem fun c _ => ιF'.range.mul_mem ⟨_, rfl⟩ (hu c)
    have hne : θ.symm (Pi.single 0 1) ∈ U := by
      intro a
      rw [AddEquiv.apply_symm_apply]
      by_cases ha : a = 0
      · subst ha
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [ha]⟩
    rcases hirr U hU with h | h
    · exfalso
      have h1 : θ.symm (Pi.single 0 1) = 0 := by
        have := hne
        rw [h] at this
        exact (Submodule.mem_bot _).mp this
      have h2 := congrArg (fun w => θ w 0) h1
      simp at h2
    · intro x
      have hx : θ.symm (Pi.single 0 x) ∈ U := by rw [h]; exact Submodule.mem_top
      have := hx 0
      rw [AddEquiv.apply_symm_apply] at this
      simpa using this
  let κ : EndRing ρ ≃+* F := (RingEquiv.ofBijective ιF' ⟨ιF'.injective, hsurj⟩).symm
  have hκ' : ∀ y : EndRing ρ, ιF' (κ y) = y := fun y =>
    (RingEquiv.ofBijective ιF' ⟨ιF'.injective, hsurj⟩).apply_symm_apply y
  let φ : M ≃+ (Fin 4 → F) := θ.trans (AddEquiv.piCongrRight fun _ : Fin 4 => κ.toAddEquiv)
  have hφ : ∀ w c, ιF' (φ w c) = θ w c := fun w c => hκ' (θ w c)
  refine ⟨i, φ, fun g w => ?_⟩
  funext a
  apply ιF'.injective
  have hsum : ∀ t : Fin 4 → F, ιF' (∑ c, t c) = ∑ c, ιF' (t c) := fun t =>
    map_sum ιF' t Finset.univ
  rw [hφ, hact, Matrix.mulVec, dotProduct, hsum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, hφ]

theorem exists_natural_of_offender {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card F = 2 ^ f) (π : antiSp F →* (M ≃ₗ[ZMod 2] M)) (hπ : Function.Injective π)
    (hnt : Nontrivial M)
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)
    (hAe : CFSG.IsElementaryAbelian 2 A) (hA1 : A ≠ ⊥)
    (hoff : Nat.card M ≤ Nat.card A * Nat.card {m : M // ∀ a ∈ A, a m = m}) :
    ∃ (i : ℕ) (φ : M ≃+ (Fin 4 → F)), ∀ g w,
      φ (π g w) = (glMat (((minorAut F ^ i) g : antiSp F) : GL (Fin 4) F)).mulVec (φ w) := by
  have hKf : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : Fact (repOf π).IsIrreducible :=
    ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff (repOf π)).mpr ⟨hnt, hirr⟩⟩
  have hπ'inj : Function.Injective (repOf π) := fun g g' hg =>
    hπ (LinearEquiv.toLinearMap_injective hg)
  have hπ'nt : ∃ g, repOf π g ≠ 1 :=
    ⟨invX F, fun h1 => invX_ne_one (hπ'inj (h1.trans (map_one (repOf π)).symm))⟩
  by_cases hdim : Module.finrank (EndRing (repOf π)) M = 4
  · exact exists_natural_of_four hKf (by omega) π hπ'nt hdim
  · exact absurd hoff (not_le.mpr
      (card_mul_card_fixed_lt_of_ne_four hf hK π hπ hdim A hnorm hAe hA1))

end Ident

end CFSG.Quasithin.B42Sp4
