module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTenCommutant

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix

variable {W : Type} [CommGroup W]

private theorem s16h_endo_of_natReal {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {K : Type} [Field K] [Finite K]
    {X : Subgroup (MulAut W)} {U Z : Subgroup W}
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {π : ↥Γ →* ↥X}
    (R : CFSG.Quasithin.SzN15.NatReal X U Z Γ π)
    (HSC : CFSG.Quasithin.H.HasScalarCommutant Γ)
    (hcard : Nat.card K = 2) :
    ∀ f : Sec U Z →* Sec U Z,
      (∀ g ∈ autSec X U Z, ∀ x : Sec U Z, f (g x) = g (f x)) →
        f = 1 ∨ f = MonoidHom.id (Sec U Z) := by
  obtain ⟨β, hβs, hβk, hβe⟩ := R.exists_β
  haveI : Fintype K := Fintype.ofFinite K
  have hker : β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, hβk u, Subgroup.mem_subgroupOf]
  let e : Sec U Z ≃* Multiplicative (ι → K) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (φ := β) hβs)
  have he_mk : ∀ u : ↥U, e (QuotientGroup.mk u) = β u := by
    intro u
    simp only [e, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  intro f hf
  let f' : Multiplicative (ι → K) →* Multiplicative (ι → K) :=
    e.toMonoidHom.comp (f.comp e.symm.toMonoidHom)
  have hf'_nat : ∀ (γ : ↥Γ) (x : Multiplicative (ι → K)),
      f' (natAct Γ γ x) = natAct Γ γ (f' x) := by
    intro γ x
    have hUinv : ∀ u ∈ U, (π γ : MulAut W) u ∈ U := R.U_inv (π γ)
    have hUinv' : ∀ u ∈ U, (π γ : MulAut W)⁻¹ u ∈ U := R.U_inv (π γ)⁻¹
    have hUstab : (π γ : MulAut W) ∈ stabSub U :=
      mem_stabSub_of_invariant hUinv hUinv'
    let hγ : stabSub U := ⟨(π γ : MulAut W), hUstab⟩
    have hXZ : X ≤ stabSub Z := by
      intro h hh
      exact mem_stabSub_of_invariant (fun z hz => R.Z_inv ⟨h, hh⟩ z hz)
        (fun z hz => R.Z_inv ⟨h, hh⟩⁻¹ z hz)
    have hmem_aut : resHom U hγ ∈ autSub X U := mem_autSub.2 ⟨hγ, (π γ).2, rfl⟩
    have hZstab : resHom U hγ ∈ stabSub (Z.subgroupOf U) :=
      autSub_le_stabSub_subgroupOf (W := U) (U := Z) hXZ hmem_aut
    let ψ : MulAut (Sec U Z) := quotHom (Z.subgroupOf U) ⟨resHom U hγ, hZstab⟩
    have hψmem : ψ ∈ autSec X U Z := by
      show ψ ∈ autQuot (autSub X U) (Z.subgroupOf U)
      exact mem_autQuot.2 ⟨⟨resHom U hγ, hZstab⟩, hmem_aut, rfl⟩
    have hψ_mk : ∀ u : ↥U, ψ (QuotientGroup.mk u) =
        QuotientGroup.mk ⟨(π γ : MulAut W) (u : W), hUinv (u : W) u.2⟩ := by
      intro u
      simp only [ψ, quotHom_mk]
      rfl
    have hψe : ∀ y : Sec U Z, e (ψ y) = natAct Γ γ (e y) := by
      intro y
      induction y using QuotientGroup.induction_on with
      | H u =>
        rw [hψ_mk u, he_mk, he_mk, hβe γ u (hUinv (u : W) u.2)]
    have hx : e.symm (natAct Γ γ x) = ψ (e.symm x) := by
      apply e.injective
      simp only [e.apply_symm_apply, hψe]
    calc f' (natAct Γ γ x)
        = e (f (e.symm (natAct Γ γ x))) := rfl
      _ = e (f (ψ (e.symm x))) := by rw [hx]
      _ = e (ψ (f (e.symm x))) := by rw [hf ψ hψmem]
      _ = natAct Γ γ (e (f (e.symm x))) := hψe _
      _ = natAct Γ γ (f' x) := rfl
  let g : (ι → K) →+ (ι → K) :=
    { toFun := fun v => Multiplicative.toAdd (f' (Multiplicative.ofAdd v))
      map_zero' := by simp
      map_add' := fun a b => by
        rw [ofAdd_add, map_mul, toAdd_mul] }
  have hgcomm : ∀ γ ∈ Γ, ∀ v : ι → K,
      g ((γ : Matrix ι ι K) *ᵥ v) = (γ : Matrix ι ι K) *ᵥ g v := by
    intro γ hγ v
    show Multiplicative.toAdd (f' (Multiplicative.ofAdd (((γ : Matrix ι ι K)) *ᵥ v))) =
      (γ : Matrix ι ι K) *ᵥ Multiplicative.toAdd (f' (Multiplicative.ofAdd v))
    rw [show Multiplicative.ofAdd (((γ : Matrix ι ι K)) *ᵥ v) =
        natAct Γ ⟨γ, hγ⟩ (Multiplicative.ofAdd v) from rfl, hf'_nat ⟨γ, hγ⟩]
    rfl
  obtain ⟨a, ha⟩ := HSC g hgcomm
  have hcardF : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have ha01 : a = 0 ∨ a = 1 := by
    by_cases ha0 : a = 0
    · exact Or.inl ha0
    · refine Or.inr ?_
      have h := FiniteField.pow_card_sub_one_eq_one a ha0
      rw [hcardF] at h
      simpa using h
  rcases ha01 with ha0 | ha1
  · left
    have hf'_one : f' = 1 := by
      refine MonoidHom.ext fun x => ?_
      apply Multiplicative.toAdd.injective
      have h := ha (Multiplicative.toAdd x)
      rw [ha0, zero_smul] at h
      exact h
    refine MonoidHom.ext fun x => ?_
    have h1 : e (f x) = 1 := by
      have h := congrArg (fun q : Multiplicative (ι → K) →* Multiplicative (ι → K) =>
        q (e x)) hf'_one
      simpa [f'] using h
    exact e.injective (h1.trans (map_one e).symm)
  · right
    have hf'_id : f' = MonoidHom.id (Multiplicative (ι → K)) := by
      refine MonoidHom.ext fun x => ?_
      apply Multiplicative.toAdd.injective
      have h := ha (Multiplicative.toAdd x)
      rw [ha1, one_smul] at h
      exact h
    refine MonoidHom.ext fun x => ?_
    have h1 : e (f x) = e x := by
      have h := congrArg (fun q : Multiplicative (ι → K) →* Multiplicative (ι → K) =>
        q (e x)) hf'_id
      simpa [f'] using h
    exact e.injective h1

theorem s16h_simpleScalar_natOmegaMinus4 [Finite W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hs : IsOmegaMinus ↥L 4 1) (h : NatOmegaMinus L U Z 4 1) :
    s16h_SimpleScalar L U Z := by
  have hN : NatOmegaMinus L U Z 4 1 := h
  obtain ⟨-, K, hKfield, hKfin, b, c, hKcard, hpoly, hReal⟩ := h
  letI := hKfield
  letI := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard2 : Nat.card K = 2 := by
    simpa using hKcard
  have hKcardF : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard2
  haveI : CharP K 2 := charP_of_card_eq_prime hKcardF
  obtain ⟨π, hπ⟩ := hReal
  have hZU : Z ≤ U := hπ.2.1
  constructor
  · refine SumOfNatShape.isIrrOn hq ⟨4, Or.inr (Or.inr (Or.inr (Or.inl ⟨hs, ?_⟩)))⟩
    refine ⟨fun _ => U, ?_, ?_, ?_, ?_⟩
    · intro i; exact hZU
    · intro i
      have hzero : (⨆ (j : Fin 1) (_ : j ≠ i), (U : Subgroup W)) = ⊥ :=
        eq_bot_iff.mpr (iSup_le fun j =>
          iSup_le fun hji => absurd (Subsingleton.elim j i) hji)
      rw [hzero, sup_bot_eq]
      exact inf_le_right
    · have hU : (⨆ _ : Fin 1, (U : Subgroup W)) = U := by
        refine le_antisymm (iSup_le fun _ => le_rfl) ?_
        exact le_iSup (fun _ : Fin 1 => (U : Subgroup W)) ⟨0, by norm_num⟩
      rw [hU, sup_eq_right.mpr hZU]
    · intro i; exact hN
  · refine s16h_endo_of_natReal (X := L) (U := U) (Z := Z)
      (Γ := StatedOmega (StatedQuadMinus (4 / 2) K b c)) (π := π)
      (CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ)
      (S18.hasScalarCommutant_statedOmegaMinus2 (K := K) (b := b) (c := c) hpoly) hKcard2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
