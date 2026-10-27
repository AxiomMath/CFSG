module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL1Lin
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL1AlgU
public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4U

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec4.E27

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec21.Item219LieProof
open CFSG.RankThree.Classical2 (unitarySet)
open scoped Matrix MatrixGroups Pointwise commutatorElement

section Unitary


variable {X : Type} [Field X] [Finite X]

set_option maxHeartbeats 400000 in
theorem layerUnitaryModel_of_model {n : ℕ} (hn1 : 1 ≤ n) (hq2 : 2 < 2 ^ n) (hq1 : 2 ^ n % 3 = 2)
    (σ : X ≃+* X) (hK : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (Ω : Type) [Field Ω] [Algebra X Ω] [IsAlgClosure X Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (g : ModGL TwistTag.D4.tag Ω) (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω)
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω (-1)) (a : Fin TwistTag.D4.tag.rank → Ωˣ)
    (ha : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr (-1))
    (hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = 3) (v : WeylGroup Tag.D4)
    (hv : (fun α => v • α) '' d4A2Sigma = survivingRoots a)
    (x : C0 σ)
    (hx : threeSixEmb X Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹) :
    LayerUnitaryModel σ n x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hℓ3 : (2 : ℕ) ≠ 3 := by decide
  have hε : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have hq0 : 2 ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed X
  have : CharP Ω 2 := charP_of_card_cube (K := X) Nat.prime_two hn1 hK
  have hFrs : Function.Surjective Fr := fun c => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hq0)
    exact ⟨z, by rw [hFr, hz]⟩
  have hstab := threeSix_stab hFr hε ha hv
  have hD := (threeSix_unitary_model Nat.prime_two hℓ3 hn1 hq2 X hK σ hσ Ω Fr hFr g hgG hFg a ha
    hord v hv x hx).1
  obtain ⟨s, hs, hΦfix, hact⟩ := layer_embedding_of_model Nat.prime_two hℓ3 hn1 σ hK hσ Ω Fr hFr
    g hgG hFg a hord v hv x hx hε hFrs hstab hD
  obtain ⟨hcl, h₀⟩ := setup_k₀ (Ω := Ω) Nat.prime_two hn1 hK hσ
  haveI := hcl
  set k₀ := RingHom.eqLocusField σ.toRingHom (RingHom.id X) with hk₀
  obtain ⟨π, b, hb⟩ := threeSix_phi_unitary Fr hFrs v hstab
  obtain ⟨-, ⟨H₀, hH₀⟩, -⟩ :=
    CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_unitary (k := k₀)
      Nat.prime_two hn1 h₀ π (threeSixPhi Ω Fr hFrs (Or.inr rfl) v hstab) b
      (fun i j hij t => by rw [hb i j hij t, hFr])
  set H : GL (Fin 3) Ω := Matrix.SpecialLinearGroup.toGL H₀ with hH
  have hGLinj : Function.Injective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 3) Ω →* GL (Fin 3) Ω) :=
    fun A B h => Subtype.ext (congrArg Units.val h)
  let s' : layerSub σ x →* GL (Fin 3) Ω :=
    (MulAut.conj H⁻¹).toMonoidHom.comp (Matrix.SpecialLinearGroup.toGL.comp s)
  have hs'apply : ∀ d, s' d = H⁻¹ * Matrix.SpecialLinearGroup.toGL (s d) * H := by
    intro d
    show H⁻¹ * Matrix.SpecialLinearGroup.toGL (s d) * (H⁻¹)⁻¹ = _
    rw [inv_inv]
  have hs' : Function.Injective s' := by
    intro d d' h
    apply hs
    apply hGLinj
    have h1 := congrArg (fun Y : GL (Fin 3) Ω => H * Y * H⁻¹) (show s' d = s' d' from h)
    simp only [hs'apply] at h1
    simpa [mul_assoc] using h1
  have hrange' : ∀ Y : GL (Fin 3) Ω, Y ∈ s'.range ↔ Y ∈ unitarySet (2 ^ n) 3 := by
    intro Y
    constructor
    · rintro ⟨d, rfl⟩
      obtain ⟨Y', hY', hXY⟩ := (hH₀ (s d)).1 ((hΦfix (s d)).1 ⟨d, rfl⟩)
      rw [hs'apply, hXY]
      have : H⁻¹ * (H * Y' * H⁻¹) * H = Y' := by group
      rw [this]
      exact hY'
    · intro hY
      have hdet : ((H * Y * H⁻¹ : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω).det = 1 := by
        rw [Units.val_mul, Units.val_mul]
        have : ((H : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
            ((Matrix.SpecialLinearGroup.toGL H₀ : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) := rfl
        rw [Matrix.det_units_conj]
        exact hY.2.1
      set X' : Matrix.SpecialLinearGroup (Fin 3) Ω :=
        ⟨((H * Y * H⁻¹ : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω), hdet⟩ with hX'
      have hX'GL : Matrix.SpecialLinearGroup.toGL X' = H * Y * H⁻¹ := Units.ext rfl
      have hmem : X' ∈ CFSG.RankThree.Classical2.fixSubgroup
          (threeSixPhi Ω Fr hFrs (Or.inr rfl) v hstab) :=
        (hH₀ X').2 ⟨Y, hY, hX'GL⟩
      obtain ⟨d, hd⟩ := (hΦfix X').2 hmem
      refine ⟨d, ?_⟩
      rw [hs'apply, hd, hX'GL]
      group
  have hact' : ∀ y ∈ cenX σ x, ∃ N : GL (Fin 3) Ω, ∀ d d' : layerSub σ x,
      (d' : C0 σ) = y * d * y⁻¹ → s' d' = N * s' d * N⁻¹ := by
    intro y hy
    obtain ⟨N, hN⟩ := hact y hy
    refine ⟨H⁻¹ * N * H, fun d d' hdd' => ?_⟩
    have h1 := hN d d' hdd'
    rw [hs'apply, hs'apply, h1]
    group
  obtain ⟨F, hF, hFd, e, he⟩ := unitary_layer_model_of_interface (ℓ := 2) (f := n) (Ω := Ω)
    (layerSub σ x) (cenX σ x) (fun g hg d hd => layerSub_conj_mem σ x hg hd) hn1 hℓ3 hq1 s' hs'
    hrange' hact'
  exact ⟨F, hF, hFd, e, he⟩

end Unitary

end CFSG.RankThree.PartTwo.Sec4.E27
