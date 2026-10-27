module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofOmegaD4
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofD4Tools
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofArith
import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofG2Two
import CFSG.RankThree.PartTwo.Sec21.LangTwisted3ProofD4Even

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projSL)


namespace Item8KFacts3D4

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem nonempty_autFix_mulEquiv_g2 (hK2 : ringChar K = 2)
    {γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hγ : Sec4.IsStdGraphFieldConj σ γ) :
    Nonempty (Sec4.autFix γ ≃* adjointGroup Tag.G2 (fixSubfield σ)) := by
  obtain ⟨φ⟩ := KFacts.nonempty_fixedPoints_fieldActor_mulEquiv_g2 σ hK2
  set σ₀ := fieldActor (t := TwistTag.D4) σ σ
  have hfix : Sec4.autFix σ₀ = σ₀.toMonoidHom.eqLocus (MonoidHom.id _) := by
    ext x
    rfl
  have hfixinv : Sec4.autFix σ₀⁻¹ = Sec4.autFix σ₀ := by
    ext x
    rw [Sec4.mem_autFix, Sec4.mem_autFix, MulAut.inv_apply, MulEquiv.symm_apply_eq, eq_comm]
  have hcongr : ∀ (β ρ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      β * ρ * β⁻¹ = MulAut.congr β ρ := by
    intro β ρ
    ext x
    rfl
  obtain ⟨β, hβ | hβ⟩ := hγ
  · rw [hβ, hcongr]
    exact ⟨((Sec4.autFixCongrEquiv β σ₀).trans (MulEquiv.subgroupCongr hfix)).trans φ⟩
  · rw [hβ, hcongr]
    exact ⟨(((Sec4.autFixCongrEquiv β σ₀⁻¹).trans (MulEquiv.subgroupCongr hfixinv)).trans
      (MulEquiv.subgroupCongr hfix)).trans φ⟩

theorem not_injective_projSL_autFix {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 3)
    (hG2 : ∀ g : adjointGroup Tag.G2 (fixSubfield σ), orderOf g ≠ 2 ^ (3 * m) + 1)
    (hN : ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), α ^ 3 = 1 →
      ¬ IsInnerAut α → ¬ Sec4.IsStdGraphFieldConj σ α →
        ¬ (2 ^ m) ^ 3 * (((2 ^ m) ^ 3) ^ 2 - 1) ∣ Nat.card (Sec4.autFix α))
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hα3 : α ^ 3 = 1)
    (hαin : ¬ IsInnerAut α) (f : projSL 2 (GaloisField 2 (3 * m)) →* Sec4.autFix α)
    (hf : Function.Injective f) : False := by
  by_cases hstd : Sec4.IsStdGraphFieldConj σ α
  · obtain ⟨e⟩ := nonempty_autFix_mulEquiv_g2 (Item8KFactsProof.ringChar_eq_two_of_card hK) hstd
    obtain ⟨y, hy⟩ := Item86ResProof.exists_orderOf_projSL_two_eq (3 * m) (by omega)
    apply hG2 (e (f y))
    rw [MulEquiv.orderOf_eq, orderOf_injective f hf, hy]
  · apply hN α hα3 hαin hstd
    have h := Subgroup.card_dvd_of_injective f hf
    have e3 : (2 : ℕ) ^ (3 * m) = (2 ^ m) ^ 3 := by rw [← pow_mul, mul_comm]
    rwa [Item87Proof.card_projSL_two_three hm, e3] at h

theorem exists_involution_of_trialityD4 {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 3)
    (hG2 : ∀ g : adjointGroup Tag.G2 (fixSubfield σ), orderOf g ≠ 2 ^ (3 * m) + 1)
    (hN : ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), α ^ 3 = 1 →
      ¬ IsInnerAut α → ¬ Sec4.IsStdGraphFieldConj σ α →
        ¬ (2 ^ m) ^ 3 * (((2 ^ m) ^ 3) ^ 2 - 1) ∣ Nat.card (Sec4.autFix α))
    {τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    {w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hτ3 : τ ^ 3 = 1) (hτin : ¬ IsInnerAut τ) (hτw : τ w = w)
    (φ : perfectResidual
        (Subgroup.centralizer ({w} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ≃*
      projSL 2 (GaloisField 2 (3 * m))) :
    ∃ v : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      v ≠ 1 ∧ v ^ 2 = 1 ∧ τ v = v ∧ v * w = w * v := by
  set Cw := Subgroup.centralizer ({w} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    with hCwdef
  set Kb := inSubgroup perfectResidual Cw with hKbdef
  have hCw : Cw.map τ.toMonoidHom = Cw := by
    rw [hCwdef, PartTwo.map_centralizer_singleton τ w, hτw]
  have hKb : Kb.map τ.toMonoidHom = Kb := by
    rw [hKbdef, PartTwo.map_inSubgroup_perfectResidual τ Cw, hCw]
  have hKbCw : Kb ≤ Cw := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  set ψ₀ : Kb ≃* projSL 2 (GaloisField 2 (3 * m)) :=
    (Item812Res8.inSubgroupPerfectResidualEquiv Cw).trans φ
  rcases exists_fixed_involution_or_eq_conj hτ3 hKb (ψ₀.trans (Sec4.projSLEquivPSL _)) with
    ⟨v, hvK, hv1, hv2, hτv⟩ | ⟨k, hkK, hk3, hτk, hact⟩
  · exact ⟨v, hv1, hv2, hτv, Subgroup.mem_centralizer_singleton_iff.mp (hKbCw hvK)⟩
  exfalso
  have hcomm : Commute τ (MulAut.conj k) := by
    have h1 := mul_mulAutConj_mul_inv τ k
    rw [hτk] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have h3 : (τ * (MulAut.conj k)⁻¹) ^ 3 = 1 := by
    rw [hcomm.inv_right.mul_pow, hτ3, one_mul, inv_pow, ← map_pow, hk3, map_one, inv_one]
  have hin : ¬ IsInnerAut (τ * (MulAut.conj k)⁻¹) := by
    rintro ⟨g, hg⟩
    exact hτin ⟨g * k, by rw [map_mul, hg, inv_mul_cancel_right]⟩
  have hle : Kb ≤ Sec4.autFix (τ * (MulAut.conj k)⁻¹) := by
    intro x hx
    rw [Sec4.mem_autFix, MulAut.mul_apply, MulAut.conj_inv_apply,
      hact _ (Kb.mul_mem (Kb.mul_mem (Kb.inv_mem hkK) hx) hkK)]
    group
  exact not_injective_projSL_autFix hm hK hG2 hN h3 hin
    ((Subgroup.inclusion hle).comp ψ₀.symm.toMonoidHom)
    ((Subgroup.inclusion_injective hle).comp ψ₀.symm.injective)

end Item8KFacts3D4

open Item8KFacts3D4

theorem kF89D4FixInvEven_holds :
    KF89D4FixInvEven := by
  intro m hev K _ _ σ hK hσ τ w hτ3 hτin hτw _ hφ
  obtain ⟨φ⟩ := hφ
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK] at h1
      norm_num at h1
    · exact hm
  have hm2 : 2 ≤ m := by
    obtain ⟨r, hr⟩ := hev
    omega
  refine exists_involution_of_trialityD4 hm hK
    (fun g => Item86ResProof.orderOf_ne_of_two_le _ hm2 (card_fixSubfield_of_cube hm hK hσ) g)
    (fun α hα3 hαin hstd => ?_) hτ3 hτin hτw φ
  rw [Item812Res8.card_of_isoPGLThree hm
    (kF89D4SecondCentEven_holds m hev hm K σ hK hσ α hα3 hαin hstd)]
  exact Item812Res8.not_dvd_linear (Item812Res8.two_le_two_pow hm)

theorem kF89D4FixInv_holds :
    KF89D4FixInv := by
  intro m hodd K _ _ σ hK hσ τ w hτ3 hτin hτw _ hφ
  obtain ⟨φ⟩ := hφ
  have hm : 1 ≤ m := hodd.pos
  have hcard := card_fixSubfield_of_cube hm hK hσ
  refine exists_involution_of_trialityD4 hm hK (fun g => ?_) (fun α hα3 hαin hstd => ?_) hτ3
    hτin hτw φ
  · rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
    · exact Item86ResProof.kF83GTwoTwo_holds _ (by rw [hcard]; norm_num) g
    · exact Item86ResProof.orderOf_ne_of_two_le _ hm2 hcard g
  · rcases inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds m hodd K σ hK hσ
      α hα3 hαin with hs | ⟨-, -, -, -, -, -, hP⟩
    · exact absurd hs hstd
    · rw [Item812Res8.card_of_isoPGUThree hm hP]
      exact Item812Res8.not_dvd_unitary (Item812Res8.two_le_two_pow hm)

end CFSG.RankThree.PartTwo.Sec8
