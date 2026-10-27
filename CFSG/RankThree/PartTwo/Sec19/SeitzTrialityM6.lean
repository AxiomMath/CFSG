module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityMax
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTau
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityFix
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec19

section M6


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem D4Par.charP_fix (P : D4Par n X σ) : CharP (fixSubfield σ) 2 :=
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
    P.one_le P.card_fix

theorem sl2_upper_lower_noncomm {F : Type} [Field F] :
    CFSG.LieType.Steinberg.sl2Upper (1 : F) * CFSG.LieType.Steinberg.sl2Lower 1 ≠
      CFSG.LieType.Steinberg.sl2Lower 1 * CFSG.LieType.Steinberg.sl2Upper 1 := by
  intro h
  have h0 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
    (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h0
  simp [CFSG.LieType.Steinberg.sl2Upper, CFSG.LieType.Steinberg.sl2Lower, Matrix.mul_apply,
    Fin.sum_univ_two] at h0

theorem centralizer_a_not_le_AB (P : D4Par n X σ) (hn : 2 ≤ n) {a : C0 σ} (ha : a ∈ Asub σ)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) :
    ¬ Subgroup.centralizer ({a} : Set (C0 σ)) ≤ Asub σ ⊔ Bsub σ := by
  haveI := P.charP
  haveI := P.charP_fix
  haveI : Finite (fixSubfield σ) := Nat.finite_of_card_ne_zero (by rw [P.card_fix]; positivity)
  have hk4 : 4 ≤ Nat.card (fixSubfield σ) := P.four_le_card_fix hn
  let e := bsubEquiv P
  have h3 : ¬ 3 ∣ 2 ^ n := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  refine core_not_centralizer_le_sup (A := Asub σ) (B := Bsub σ) (a := a) ?_ ?_ ?_ ?_ ?_ ?_
  · intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Asub_Bsub_commute ha hb).symm
  · intro g hg h hh
    have hgh : g * h = h * g := Asub_Bsub_commute hg hh
    rw [hgh, mul_inv_cancel_right]
    exact hh
  · haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ)) :=
      (KS11Lie4Proof.isQuasisimple_sl2 hk4).1
    haveI : Group.IsPerfect ↥(Bsub σ) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact Group.isPerfect_def.mp inferInstance
  · refine ⟨(e (CFSG.LieType.Steinberg.sl2Upper 1) : C0 σ), (e _).2,
      (e (CFSG.LieType.Steinberg.sl2Lower 1) : C0 σ), (e _).2, fun h => ?_⟩
    apply sl2_upper_lower_noncomm (F := fixSubfield σ)
    apply e.injective
    apply Subtype.ext
    simpa using h
  · intro x hx hcent _
    have hy : e (e.symm ⟨x, hx⟩) = ⟨x, hx⟩ := e.apply_symm_apply _
    have hyc : e.symm ⟨x, hx⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ)) := by
      rw [Subgroup.mem_center_iff]
      intro m
      apply e.injective
      apply Subtype.ext
      simp only [map_mul, hy]
      exact hcent (e m : C0 σ) (e m).2
    rw [CFSG.RankThree.PartOne.CTP.center_sl2_eq_bot, Subgroup.mem_bot] at hyc
    have : (⟨x, hx⟩ : ↥(Bsub σ)) = 1 := by rw [← hy, hyc, map_one]
    exact congrArg Subtype.val this
  · exact KS11Lie6Proof.d4ThreeACent_holds X (2 ^ n) σ P.card P.frob h3 a ha ha3 ha1


open CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ3
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint in
theorem Gsub_not_le_AB (P : D4Par n X σ) : ¬ Gsub σ ≤ Asub σ ⊔ Bsub σ := by
  haveI := P.charP
  intro hle
  have hσ3 := P.sigma_cube_hom
  have hmem : (xN (1 : X) : adjointGroup d4 X) ∈ twistedGroup σ.toRingHom :=
    twistedRootSubgroupD4_le_twistedGroup σ.toRingHom (isRoot_rt (by norm_num))
      ((mem_XN hσ3 _).2 ⟨1, map_one σ.toRingHom, rfl⟩)
  let y : twistedGroup σ.toRingHom := ⟨xN 1, hmem⟩
  let x : C0 σ := (eC P).symm y
  have hx : (x : ModGL TwistTag.D4.tag X) = ((xN (1 : X) : adjointGroup d4 X) : ModGL d4 X) := by
    have := coe_eC P x
    rw [(eC P).apply_symm_apply] at this
    exact this.symm
  have hxG : x ∈ Gsub σ := by
    show tauAut σ x = x
    apply Subtype.ext
    rw [coe_tauAut, hx]
    have := entrywise_xd (X := X) (p := 19) (by norm_num) σ.toRingHom 1
    rw [map_one] at this
    exact this
  have hxL : eC P x ∈ Lsub σ.toRingHom hσ3 := by
    have h1 := hle hxG
    have h2 : eC P x ∈ (Asub σ ⊔ Bsub σ).map (eC P).toMonoidHom := ⟨x, h1, rfl⟩
    rwa [Subgroup.map_sup, map_eC_Asub P, map_eC_Bsub P] at h2
  have htop : Lsub σ.toRingHom hσ3 = ⊤ :=
    eq_top_of_xN hσ3 le_rfl one_ne_zero (map_one σ.toRingHom)
      ⟨eC P x, hxL, by rw [(eC P).apply_symm_apply]⟩
  apply Asub_sup_Bsub_ne_top P
  have hinj : Function.Injective (eC P).toMonoidHom := (eC P).injective
  apply Subgroup.map_injective hinj
  rw [Subgroup.map_sup, map_eC_Asub P, map_eC_Bsub P, Subgroup.map_top_of_surjective _
    (eC P).surjective]
  exact htop

end M6

end CFSG.RankThree.PartTwo.Sec19
