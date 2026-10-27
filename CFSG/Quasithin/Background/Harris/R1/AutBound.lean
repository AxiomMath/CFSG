module

public import CFSG.Quasithin.Background.Harris.R1.Defs
public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Quasithin CFSG.Open CFSG.GH74.Uniqueness.Bender

@[expose] def quotAut (X : Type) [Group X] : MulAut X →* MulAut (X ⧸ Subgroup.center X) where
  toFun σ := QuotientGroup.congr _ _ σ (Subgroup.map_center_eq σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem quotAut_injective (X : Type) [Group X] [Group.IsPerfect X] :
    Function.Injective (quotAut X) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hz : ∀ x : X, x⁻¹ * σ x ∈ Subgroup.center X := by
    intro x
    have h := congrArg (fun τ : MulAut (X ⧸ Subgroup.center X) => τ (QuotientGroup.mk x)) hσ
    have h' : (QuotientGroup.mk (σ x) : X ⧸ Subgroup.center X) = QuotientGroup.mk x := h
    exact (QuotientGroup.eq.mp h'.symm)
  let c : X →* Subgroup.center X :=
    { toFun := fun x => ⟨x⁻¹ * σ x, hz x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (hz x) y⁻¹
        change (x * y)⁻¹ * σ (x * y) = (x⁻¹ * σ x) * (y⁻¹ * σ y)
        rw [map_mul, mul_inv_rev, mul_assoc, mul_assoc, ← mul_assoc x⁻¹ (σ x) (σ y)]
        rw [show y⁻¹ * (x⁻¹ * σ x * σ y) = (y⁻¹ * (x⁻¹ * σ x)) * σ y by group, hc]
        group }
  have hker : c.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := X)]
    exact Abelianization.commutator_subset_ker c
  ext x
  have hx : c x = 1 := MonoidHom.mem_ker.mp (by rw [hker]; trivial)
  have := congrArg Subtype.val hx
  change x⁻¹ * σ x = 1 at this
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp this).symm

theorem card_le_of_central_cover {X K : Type} [Group X] [Finite X]
    [Group K] {n i e : ℕ} (π : X →* K) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) (hperf : Group.IsPerfect X) (hK : BenderType K n i e)
    (E : Subgroup (MulAut X)) (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 ^ (n + 1) := by
  have : Finite K := Finite.of_surjective π hπ
  have hcen : Subgroup.center X = π.ker := by
    refine le_antisymm (fun x hx => ?_) hker
    have h1 : π x ∈ Subgroup.center K := Subgroup.map_center_le_center hπ ⟨x, hx, rfl⟩
    rw [hK.center_eq_bot, Subgroup.mem_bot] at h1
    exact h1
  let Qe : X ⧸ Subgroup.center X ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have hK' : BenderType (X ⧸ Subgroup.center X) n i e := hK.of_mulEquiv Qe.symm
  have : Finite (X ⧸ Subgroup.center X) := inferInstance
  have hinj : Function.Injective (quotAut X) := quotAut_injective X
  have hsq' : ∀ x ∈ E.map (quotAut X), x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, hsq y hy, map_one]
  have hcard : Nat.card (E.map (quotAut X)) = Nat.card E :=
    Subgroup.card_map_of_injective hinj
  rw [← hcard]
  exact (hK'.card_le_of_sq_eq_one_aut _ hsq').1

theorem autBound_holds : AutBoundStmt := by
  intro X _ _ n hn hX E hsq
  rcases hX with ⟨⟨e⟩⟩ | ⟨a, rfl, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
  · exact ((BenderType.linear n hn e).card_le_of_sq_eq_one_aut E hsq).1
  · have hB : BenderType X (2 * a + 1) 2 1 :=
      BenderType.suzuki a (by omega)
        (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
    exact (hB.card_le_of_sq_eq_one_aut E hsq).1
  · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnq : (3, 2 ^ n) ≠ (3, 2) := fun h => by
      have h2 : 2 ^ n = 2 ^ 1 := by simpa using congrArg Prod.snd h
      have := Nat.pow_right_injective le_rfl h2
      omega
    have hperf : Group.IsPerfect (StatedSU 3 (2 ^ n) F) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF (n := 3) le_rfl hnq
    have : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
      e.symm.surjective
    refine card_le_of_central_cover
      ((QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F))).comp
        e.toMonoidHom)
      ((QuotientGroup.mk'_surjective _).comp e.surjective) ?_ inferInstance hB E hsq
    intro x hx
    have hx' : e x ∈ (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F) := by
      exact (QuotientGroup.eq_one_iff (e x)).mp (MonoidHom.mem_ker.mp hx)
    have hc : e x ∈ Subgroup.center (StatedSU 3 (2 ^ n) F) := statedSU_scalars_le_center hx'
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    exact hc (e g)
  · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    exact ((hB.of_mulEquiv e.symm).card_le_of_sq_eq_one_aut E hsq).1

end CFSG.Quasithin.Background.Harris.R1
