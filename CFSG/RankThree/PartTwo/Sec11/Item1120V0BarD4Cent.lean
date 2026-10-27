module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofCentS

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar

open Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KGD
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof Subgroup
open CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof
open scoped MatrixGroups

section Cent


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ℓ f : ℕ} [hℓ : Fact ℓ.Prime]

theorem isSimpleGroup_graphFixedRootGroup_d4 (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hℓp : ℓ.Prime := Fact.out
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓp (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  obtain ⟨-, -, -, hsimple, -⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group ℓ f hℓp hf K hK L 1
      (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)
      (iterateFrobenius L ℓ f) (fun c => iterateFrobenius_def ℓ f c)
  exact hsimple

theorem nonempty_mulEquiv_centralizer_d4ShortSL2 (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), CharP F ℓ ∧ Nat.card F = ℓ ^ f ∧
      Nonempty (SpecialLinearGroup (Fin 2) F ≃*
        ↥(centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
          Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
            Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))) := by
  have hℓp : ℓ.Prime := Fact.out
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓp (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hcomm : ∀ c, algebraMap K L (σ c) = Fr (algebraMap K L c) := fun c => by
    rw [hσ, hFr, map_pow]
  have hfixθ := twistHom_thetaConj σ Fr (RingHom.ext hcomm)
  set k := RingHom.eqLocusField Fr (RingHom.id L) with hk
  have hkcard : Nat.card k = ℓ ^ f := natCard_eqLocusField_frob hℓp hf hFr
  have hkfin : Finite k :=
    Nat.finite_of_card_ne_zero (by rw [hkcard]; exact pow_ne_zero _ hℓp.ne_zero)
  have hkchar : CharP k ℓ := (k.subtype.charP_iff_charP ℓ).mpr inferInstance
  refine ⟨k, inferInstance, hkfin, hkchar, hkcard, ?_⟩
  have hmem : ∀ A : SpecialLinearGroup (Fin 2) k,
      thetaHom L (Matrix.SpecialLinearGroup.map k.subtype A) ∈ (triEmb K σ L).range := by
    intro A
    rw [triEmb_range hℓp hf hK hσ Fr hFr]
    refine Subgroup.mem_inf.2 ⟨thetaHom_mem_adjointGroup _, ?_⟩
    change twistHom TwistTag.D4 L Fr (thetaHom L _) = MonoidHom.id _ (thetaHom L _)
    rw [twistHom_thetaHom Fr hfixθ, map_frob_map_subtype]
    rfl
  set θk : SpecialLinearGroup (Fin 2) k →* ModGL TwistTag.D4.tag L :=
    (thetaHom L).comp (Matrix.SpecialLinearGroup.map k.subtype) with hθk
  have hθkinj : Function.Injective θk :=
    (thetaHom_injective (L := L)).comp (sl2Map_injective k.subtype)
  set Φ : SpecialLinearGroup (Fin 2) k →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    ((MonoidHom.ofInjective (triEmb_injective (K := K) (σ := σ) (L := L))).symm.toMonoidHom).comp
      (θk.codRestrict (triEmb K σ L).range hmem) with hΦ
  have hΦe : ∀ A, triEmb K σ L (Φ A) = θk A := by
    intro A
    have := (MonoidHom.ofInjective (triEmb_injective (K := K) (σ := σ) (L := L))).apply_symm_apply
      (θk.codRestrict (triEmb K σ L).range hmem A)
    exact congrArg Subtype.val this
  have hΦinj : Function.Injective Φ := fun A B h =>
    hθkinj (by rw [← hΦe, ← hΦe, h])
  have hΦS : ∀ A, Φ A ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := fun A =>
    mem_centralizer_of_triEmb_mem (L := L) (by rw [hΦe]; exact thetaHom_mem_thetaPair _)
  have hΦsurj : ∀ x ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), ∃ A, Φ A = x := by
    intro x hx
    obtain ⟨Z, hZ⟩ := exists_thetaHom_of_mem_centralizer hf hℓ3 hK hσ L hFr hx
    have hFZ : Matrix.SpecialLinearGroup.map Fr Z = Z := thetaHom_injective (by
      rw [← twistHom_thetaHom Fr hfixθ, hZ]
      exact triEmb_fixed Fr (RingHom.ext hcomm) x)
    obtain ⟨Zk, hZk⟩ := exists_sl2_eqLocus Fr Z hFZ
    refine ⟨Zk, triEmb_injective (L := L) ?_⟩
    rw [hΦe, hθk, MonoidHom.comp_apply, hZk, hZ]
  refine ⟨MulEquiv.ofBijective (Φ.codRestrict _ hΦS) ⟨fun A B h => hΦinj (congrArg Subtype.val h),
    fun x => ?_⟩⟩
  obtain ⟨A, hA⟩ := hΦsurj x.1 x.2
  exact ⟨A, Subtype.ext hA⟩

end Cent

end CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar

end
