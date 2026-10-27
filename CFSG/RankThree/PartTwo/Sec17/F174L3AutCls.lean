module

public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

open scoped MatrixGroups Matrix

public section

namespace CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Ring

theorem ringEquiv_pow_eq_one {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) (τ : F ≃+* F) : τ ^ n = 1 := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hfin : Module.finrank (ZMod 2) F = n := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [ZMod.card, hF] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hτ : ∀ c : ZMod 2, τ (algebraMap (ZMod 2) F c) = algebraMap (ZMod 2) F c := by
    intro c
    have hfg : τ.toRingHom.comp (algebraMap (ZMod 2) F) = algebraMap (ZMod 2) F :=
      RingHom.ext_zmod _ _
    exact congrArg (fun f : ZMod 2 →+* F => f c) hfg
  let sigma : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv hτ
  have hsigma : sigma ^ n = 1 := by
    have hcard : Nat.card (F ≃ₐ[ZMod 2] F) = n :=
      (IsGalois.card_aut_eq_finrank (ZMod 2) F).trans hfin
    rw [← hcard]
    exact pow_card_eq_one'
  have key : ∀ k : ℕ, ∀ y : F, (τ ^ k) y = (sigma ^ k) y := by
    intro k
    induction k with
    | zero => intro y; first | rfl | simp only [pow_zero, RingAut.one_apply, AlgEquiv.one_apply]
    | succ k ih =>
      intro y
      rw [pow_succ, pow_succ, RingAut.mul_apply, AlgEquiv.mul_apply]
      exact ih (τ y)
  refine RingEquiv.ext fun x => ?_
  have hx : (sigma ^ n) x = x :=
    (congrArg (fun g : F ≃ₐ[ZMod 2] F => g x) hsigma).trans (AlgEquiv.one_apply x)
  exact (key n x).trans (hx.trans rfl)

end CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Ring

namespace CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Cls

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem aut_two_element {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ} (hn : Odd n)
    (hF : Fintype.card F = 2 ^ n) (σ : MulAut (projectiveSL 3 F))
    (hσ : ∃ k : ℕ, σ ^ (2 ^ k) = 1) :
    ∃ (B : GL (Fin 3) F) (ε : ℕ), ε ≤ 1 ∧ σ = conjAut 3 F B * dualAut 3 F ^ ε := by
  classical
  obtain ⟨hTop, hgen⟩ := automorphism_generation (K := F) (n := 3) (le_refl 3)
  obtain ⟨A, τ, ε, hε, hσeq⟩ := hgen σ
  obtain ⟨k, hk⟩ := hσ
  have hk2 : σ ^ (2 ^ (k + 1)) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
  obtain ⟨-, -, hDn, -⟩ := standard_outer_quotients (n := 3) (K := F)
  have hDnorm : (linearAutGroup 3 F).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup 3 F := hTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup 3 F := hTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (Subgroup.mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact Subgroup.mem_subgroupOf.mp this
  let π := QuotientGroup.mk' (linearAutGroup 3 F)
  have hπc : ∀ C : GL (Fin 3) F, π (conjAut 3 F C) = 1 := fun C =>
    (QuotientGroup.eq_one_iff _).mpr (mem_linearAutGroup_iff.mpr ⟨C, rfl⟩)
  have hδδ : dualAut 3 F * dualAut 3 F = 1 :=
    (standard_automorphism_transport (K := F) (n := 3)).2.2.2.1
  have hcomm : Commute (π (fieldAut 3 F τ)) (π (dualAut 3 F)) :=
    Commute.map (show Commute (fieldAut 3 F τ) (dualAut 3 F) from
      (dualAut_mul_fieldAut τ).symm) π
  have hπσ : π σ = π (fieldAut 3 F τ) * π (dualAut 3 F) ^ ε := by
    rw [hσeq, map_mul, map_mul, hπc, one_mul, map_pow]
  have hpow : (π σ) ^ (2 ^ (k + 1)) = 1 := by rw [← map_pow, hk2, map_one]
  have hδπ : (π (dualAut 3 F)) ^ (2 ^ (k + 1)) = 1 := by
    have h2 : (π (dualAut 3 F)) ^ 2 = 1 := by rw [sq, ← map_mul, hδδ, map_one]
    rw [pow_succ', pow_mul, h2, one_pow]
  have hfτ2 : (π (fieldAut 3 F τ)) ^ (2 ^ (k + 1)) = 1 := by
    have h1 : (π σ) ^ (2 ^ (k + 1)) =
        (π (fieldAut 3 F τ)) ^ (2 ^ (k + 1)) * ((π (dualAut 3 F)) ^ ε) ^ (2 ^ (k + 1)) := by
      rw [hπσ]
      exact (hcomm.pow_right ε).mul_pow _
    have h2 : ((π (dualAut 3 F)) ^ ε) ^ (2 ^ (k + 1)) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hδπ, one_pow]
    rw [hpow, h2, mul_one] at h1
    exact h1.symm
  have hfτn : (π (fieldAut 3 F τ)) ^ n = 1 := by
    rw [← map_pow, ← map_pow, Ring.ringEquiv_pow_eq_one hF τ, map_one, map_one]
  have hcop : Nat.Coprime (2 ^ (k + 1)) n :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hn)
  have h1 : (π (fieldAut 3 F τ)) ^ Nat.gcd (2 ^ (k + 1)) n = 1 :=
    pow_gcd_eq_one.mpr ⟨hfτ2, hfτn⟩
  rw [hcop.gcd_eq_one, pow_one] at h1
  have hfD : fieldAut 3 F τ ∈ linearAutGroup 3 F := (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨C, hC⟩ := mem_linearAutGroup_iff.mp hfD
  refine ⟨A * C, ε, hε, ?_⟩
  rw [hσeq, ← hC, map_mul, mul_assoc]

end CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Cls

namespace CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Tr

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification

variable {F : Type} [Field F]

theorem scalars_eq_bot_of_cube (h : ∀ r : F, r ^ 3 = 1 → r = 1) : scalars 3 F = ⊥ := by
  rw [scalars_eq_center]
  exact CFSG.RankThree.PartTwo.Sec4.center_specialLinearGroup_eq_bot h

@[expose] noncomputable def projEquiv (h : ∀ r : F, r ^ 3 = 1 → r = 1) :
    SL(3, F) ≃* projectiveSL 3 F :=
  MulEquiv.ofBijective (proj 3 F) ⟨fun a b hab => by
    have h1 := (proj_eq_proj_iff (n := 3) (K := F)).mp hab
    rw [scalars_eq_bot_of_cube h, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1, proj_surjective 3 F⟩

theorem projEquiv_apply (h : ∀ r : F, r ^ 3 = 1 → r = 1) (s : SL(3, F)) :
    projEquiv h s = proj 3 F s := rfl

theorem congr_proj (h : ∀ r : F, r ^ 3 = 1 → r = 1) (σ : MulAut SL(3, F)) (s : SL(3, F)) :
    MulAut.congr (projEquiv h) σ (proj 3 F s) = proj 3 F (σ s) := by
  rw [← projEquiv_apply h, MulAut.congr_apply]
  simp
  exact projEquiv_apply h (σ s)

theorem formula_conj (h : ∀ r : F, r ^ 3 = 1 → r = 1) (σ : MulAut SL(3, F)) (B : GL (Fin 3) F)
    (hσ : MulAut.congr (projEquiv h) σ = conjAut 3 F B) (s : SL(3, F)) :
    ((σ s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (B : Matrix (Fin 3) (Fin 3) F) * (s : Matrix (Fin 3) (Fin 3) F) *
        ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have h1 : proj 3 F (σ s) = proj 3 F (CatalogueBHigherLinearAction.slConjugation 3 F B s) := by
    rw [← congr_proj h, hσ, conjAut_proj]
  have h2 : σ s = CatalogueBHigherLinearAction.slConjugation 3 F B s :=
    (projEquiv h).injective h1
  rw [h2, coe_slConjugation]

theorem formula_dual (h : ∀ r : F, r ^ 3 = 1 → r = 1) (σ : MulAut SL(3, F)) (B : GL (Fin 3) F)
    (hσ : MulAut.congr (projEquiv h) σ = conjAut 3 F B * dualAut 3 F) (s : SL(3, F)) :
    ((σ s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (B : Matrix (Fin 3) (Fin 3) F) * ((s⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).transpose *
        ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have h1 : proj 3 F (σ s) =
      proj 3 F (CatalogueBHigherLinearAction.slConjugation 3 F B (s⁻¹).transpose) := by
    rw [← congr_proj h, hσ, MulAut.mul_apply, dualAut_proj, conjAut_proj]
  have h2 : σ s = CatalogueBHigherLinearAction.slConjugation 3 F B (s⁻¹).transpose :=
    (projEquiv h).injective h1
  rw [h2, coe_slConjugation]
  rfl

theorem classification_sl [Fintype F] [CharP F 2] {n : ℕ} (hn : Odd n)
    (hF : Fintype.card F = 2 ^ n) (h : ∀ r : F, r ^ 3 = 1 → r = 1) (σ : MulAut SL(3, F))
    (hσ : ∃ k : ℕ, σ ^ (2 ^ k) = 1) :
    (∃ B : GL (Fin 3) F, ∀ s : SL(3, F), ((σ s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (B : Matrix (Fin 3) (Fin 3) F) * (s : Matrix (Fin 3) (Fin 3) F) *
        ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ∨
    (∃ B : GL (Fin 3) F, ∀ s : SL(3, F), ((σ s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (B : Matrix (Fin 3) (Fin 3) F) * ((s⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).transpose *
        ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
  obtain ⟨k, hk⟩ := hσ
  have hk' : (MulAut.congr (projEquiv h) σ) ^ (2 ^ k) = 1 := by
    rw [← map_pow, hk, map_one]
  obtain ⟨B, ε, hε, hσeq⟩ := Cls.aut_two_element hn hF (MulAut.congr (projEquiv h) σ) ⟨k, hk'⟩
  interval_cases ε
  · left
    exact ⟨B, formula_conj h σ B (by rw [hσeq, pow_zero, mul_one])⟩
  · right
    exact ⟨B, formula_dual h σ B (by rw [hσeq, pow_one])⟩

end CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Tr
