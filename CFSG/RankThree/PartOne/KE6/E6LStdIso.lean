module

public import CFSG.RankThree.PartOne.KE6.E6LStd
public import CFSG.RankThree.PartOne.KE6.E6LDescent
public import CFSG.RankThree.PartOne.KE6.E6LIso

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)
open CFSG.LieType.Steinberg.TwistedE6 (sigma fixedGroup mem_fixedGroup sigma_xm_single
  sigma_xm_neg_single rhoPerm fixedGroup_isQuasisimple_of_four_le_card)
open scoped Matrix MatrixGroups

theorem finite_quasisimple_of_range {G H : Type*} [Group G] [Group H] (ψ : G →* H)
    (hψ : Function.Injective ψ) {P : Subgroup H} (hP : P = ψ.range) (hG : Finite G)
    (hq : CFSG.IsQuasisimple G) : Finite P ∧ CFSG.IsQuasisimple P := by
  subst hP
  let e : G ≃* ψ.range := MonoidHom.ofInjective hψ
  exact ⟨Finite.of_equiv _ e.toEquiv, CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq⟩

section One

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem StdTwist6.stdLayer_eq_map_of_one [M27Ok τ] [E6Sub τ] {n₁ : ModGL τ L}
    {π : Equiv.Perm (Fin τ.rank)} (h : StdTwist6 n₁ π) (hπ : π = 1) :
    stdLayer τ ℓ f n₁ = (subsystemGroup τ (frobeniusFixedField L ℓ f) (e6Set τ)).map
      (baseChangeGL (frobeniusFixedField L ℓ f).subtype) := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgQ, hgfix⟩ := mem_stdLayer.1 hg
    have e := h.commute_of_one hπ (entrywiseFrob_mem (ℓ := ℓ) hgQ f)
    rw [e] at hgfix
    exact exists_mem_map_of_frobenius_fixed f hgQ hgfix
  · intro hg
    obtain ⟨q, hq, rfl⟩ := hg
    have hgQ := baseChangeGL_mem_subsystemGroup' (frobeniusFixedField L ℓ f).subtype hq
    have hfix := frobenius_fixed_of_mem_map f ⟨q, hq, rfl⟩
    refine mem_stdLayer.2 ⟨hgQ, ?_⟩
    rw [hfix]
    exact h.commute_of_one hπ hgQ

theorem card_frobeniusFixedField_pow {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (frobeniusFixedField L ℓ m) = ℓ ^ m := card_frobeniusFixedField (by omega)

theorem finite_frobeniusFixedField {m : ℕ} (hm : 1 ≤ m) : Finite (frobeniusFixedField L ℓ m) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_frobeniusFixedField_pow hm]
    exact pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)

theorem StdTwist6.finite_quasisimple_of_one [M27Ok τ] [E6Sub τ] {n₁ : ModGL τ L}
    {π : Equiv.Perm (Fin τ.rank)} (h : StdTwist6 n₁ π) (hπ : π = 1) (hf : 1 ≤ f) :
    Finite (stdLayer τ ℓ f n₁) ∧ CFSG.IsQuasisimple (stdLayer τ ℓ f n₁) := by
  set K := frobeniusFixedField L ℓ f with hK
  have : Finite K := finite_frobeniusFixedField hf
  let ψ : subsystemGroup τ K (e6Set τ) →* ModGL τ L :=
    (baseChangeGL K.subtype).comp (subsystemGroup τ K (e6Set τ)).subtype
  have hψ : Function.Injective ψ := (baseChangeGL_injective _).comp Subtype.val_injective
  have hrange : stdLayer τ ℓ f n₁ = ψ.range := by
    rw [h.stdLayer_eq_map_of_one hπ]
    ext g
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, q.2, rfl⟩
  have hfin : Finite (subsystemGroup τ K (e6Set τ)) := by
    have : Finite (ModGL τ K) := finite_modGL
    infer_instance
  exact finite_quasisimple_of_range ψ hψ hrange hfin
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (m27Equiv τ K).symm
      (CFSG.LieType.CurtisTits.isQuasisimple_e6 K))

end One

section Rho

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

abbrev K2 (L : Type) [Field L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ] : Type :=
  ↥(frobeniusFixedField L ℓ (2 * f))

@[expose] def theta2 (L : Type) [Field L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ] :
    K2 L ℓ f →+* K2 L ℓ f :=
  iterateFrobenius (K2 L ℓ f) ℓ f

omit [IsAlgClosed L] in
theorem theta2_apply (c : K2 L ℓ f) : ((theta2 L ℓ f c : K2 L ℓ f) : L) = (c : L) ^ ℓ ^ f := by
  change ((iterateFrobenius (K2 L ℓ f) ℓ f c : K2 L ℓ f) : L) = _
  rw [iterateFrobenius_def]
  rfl

omit [IsAlgClosed L] in
theorem theta2_theta2 (c : K2 L ℓ f) : theta2 L ℓ f (theta2 L ℓ f c) = c := by
  apply Subtype.ext
  rw [theta2_apply, theta2_apply, ← pow_mul, ← pow_add, ← two_mul]
  exact mem_frobeniusFixedField.1 c.2

theorem card_K2 (hf : 1 ≤ f) : Nat.card (K2 L ℓ f) = ℓ ^ (2 * f) :=
  card_frobeniusFixedField_pow (by omega)

@[expose] def psi2 (τ : Tag) [M27Ok τ] [E6Sub τ]
    (L : Type) [Field L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ] :
    fixedGroup (K2 L ℓ f) (theta2 L ℓ f) →* ModGL τ L :=
  (baseChangeGL (frobeniusFixedField L ℓ (2 * f)).subtype).comp
    ((subsystemGroup τ (K2 L ℓ f) (e6Set τ)).subtype.comp
      ((m27Equiv τ (K2 L ℓ f)).symm.toMonoidHom.comp (fixedGroup (K2 L ℓ f) (theta2 L ℓ f)).subtype))

@[expose] def theta2Q (τ : Tag) [M27Ok τ] [E6Sub τ]
    (L : Type) [Field L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ] :
    subsystemGroup τ (K2 L ℓ f) (e6Set τ) →* subsystemGroup τ (K2 L ℓ f) (e6Set τ) :=
  (m27Equiv τ (K2 L ℓ f)).symm.toMonoidHom.comp
    ((sigma (K2 L ℓ f) (theta2 L ℓ f)).comp (m27Equiv τ (K2 L ℓ f)).toMonoidHom)

omit [IsAlgClosed L] in
theorem psi2_apply [M27Ok τ] [E6Sub τ]
    (x : fixedGroup (K2 L ℓ f) (theta2 L ℓ f)) :
    psi2 τ L ℓ f x = baseChangeGL (frobeniusFixedField L ℓ (2 * f)).subtype
      (((m27Equiv τ (K2 L ℓ f)).symm x.1 : subsystemGroup τ (K2 L ℓ f) (e6Set τ)) :
        ModGL τ (K2 L ℓ f)) := rfl

omit [IsAlgClosed L] in
theorem theta2Q_apply [M27Ok τ] [E6Sub τ]
    (q : subsystemGroup τ (K2 L ℓ f) (e6Set τ)) :
    theta2Q τ L ℓ f q = (m27Equiv τ (K2 L ℓ f)).symm
      (sigma (K2 L ℓ f) (theta2 L ℓ f) (m27Equiv τ (K2 L ℓ f) q)) := rfl

omit [IsAlgClosed L] in
theorem theta2Q_xUnit [M27Ok τ] [E6Sub τ]
    (k : Fin Tag.E6.rank) (c : K2 L ℓ f) :
    theta2Q τ L ℓ f ⟨xUnit τ (K2 L ℓ f) (e6Idx k) c,
        xUnit_mem_subsystemGroup (e6Idx_mem_e6Set k) c⟩ =
      ⟨xUnit τ (K2 L ℓ f) (e6Idx (rho6 k)) (theta2 L ℓ f c),
        xUnit_mem_subsystemGroup (e6Idx_mem_e6Set (rho6 k)) _⟩ := by
  apply (m27Equiv τ (K2 L ℓ f)).injective
  simp only [theta2Q, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, m27Equiv_apply, m27ResMin_xUnit, sigma_xm_single,
    rhoPerm_eq_rho6]

omit [IsAlgClosed L] in
theorem theta2Q_yUnit [M27Ok τ] [E6Sub τ]
    (k : Fin Tag.E6.rank) (c : K2 L ℓ f) :
    theta2Q τ L ℓ f ⟨yUnit τ (K2 L ℓ f) (e6Idx k) c,
        yUnit_mem_subsystemGroup (e6Idx_mem_e6Set k) c⟩ =
      ⟨yUnit τ (K2 L ℓ f) (e6Idx (rho6 k)) (theta2 L ℓ f c),
        yUnit_mem_subsystemGroup (e6Idx_mem_e6Set (rho6 k)) _⟩ := by
  apply (m27Equiv τ (K2 L ℓ f)).injective
  simp only [theta2Q, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, m27Equiv_apply, m27ResMin_yUnit, sigma_xm_neg_single,
    rhoPerm_eq_rho6]

omit [IsAlgClosed L] in
theorem StdTwist6.theta_baseChange [M27Ok τ] [E6Sub τ]
    {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)} (h : StdTwist6 n₁ π) (hπ : π = rhoτ τ)
    (g : subsystemGroup τ (K2 L ℓ f) (e6Set τ)) :
    frobTwistGL τ L ℓ f n₁ (baseChangeGL (frobeniusFixedField L ℓ (2 * f)).subtype
        (g : ModGL τ (K2 L ℓ f))) =
      baseChangeGL (frobeniusFixedField L ℓ (2 * f)).subtype
        ((theta2Q τ L ℓ f g : subsystemGroup τ (K2 L ℓ f) (e6Set τ)) : ModGL τ (K2 L ℓ f)) := by
  have hext : (frobTwistGL τ L ℓ f n₁).comp ((baseChangeGL (frobeniusFixedField L ℓ (2 * f)).subtype).comp
        (subsystemGroup τ (K2 L ℓ f) (e6Set τ)).subtype) =
      (baseChangeGL (frobeniusFixedField L ℓ (2 * f)).subtype).comp
        ((subsystemGroup τ (K2 L ℓ f) (e6Set τ)).subtype.comp (theta2Q τ L ℓ f)) := by
    refine hom_ext_Q (fun k c => ?_) (fun k c => ?_)
    · show frobTwistGL τ L ℓ f n₁ (baseChangeGL (frobeniusFixedField L ℓ (2 * f)).subtype
          (xUnit τ (K2 L ℓ f) (e6Idx k) c)) =
        baseChangeGL (frobeniusFixedField L ℓ (2 * f)).subtype
          ((theta2Q τ L ℓ f ⟨xUnit τ (K2 L ℓ f) (e6Idx k) c,
            xUnit_mem_subsystemGroup (e6Idx_mem_e6Set k) c⟩ : subsystemGroup τ (K2 L ℓ f)
              (e6Set τ)) : ModGL τ (K2 L ℓ f))
      rw [theta2Q_xUnit, baseChangeGL_xUnit, baseChangeGL_xUnit,
        h.theta_xUnit (e6Idx_mem_e6Set k), hπ, rhoτ_e6Idx]
      exact congrArg (xUnit τ L (e6Idx (rho6 k))) (theta2_apply c).symm
    · show frobTwistGL τ L ℓ f n₁ (baseChangeGL (frobeniusFixedField L ℓ (2 * f)).subtype
          (yUnit τ (K2 L ℓ f) (e6Idx k) c)) =
        baseChangeGL (frobeniusFixedField L ℓ (2 * f)).subtype
          ((theta2Q τ L ℓ f ⟨yUnit τ (K2 L ℓ f) (e6Idx k) c,
            yUnit_mem_subsystemGroup (e6Idx_mem_e6Set k) c⟩ : subsystemGroup τ (K2 L ℓ f)
              (e6Set τ)) : ModGL τ (K2 L ℓ f))
      rw [theta2Q_yUnit, baseChangeGL_yUnit, baseChangeGL_yUnit,
        h.theta_yUnit (e6Idx_mem_e6Set k), hπ, rhoτ_e6Idx]
      exact congrArg (yUnit τ L (e6Idx (rho6 k))) (theta2_apply c).symm
  exact DFunLike.congr_fun hext g

theorem rhoτ_rhoτ {τ : Tag} [E6Sub τ] {i : Fin τ.rank} (hi : i ∈ e6Set τ) :
    rhoτ τ (rhoτ τ i) = i := by
  obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) (e6Set_lt hi)
  rw [rhoτ_e6Idx, rhoτ_e6Idx, rho6_rho6]

omit [IsAlgClosed L] in
theorem StdTwist6.theta_theta [E6Sub τ] {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (h : StdTwist6 n₁ π) (hπ : π = rhoτ τ) {g : ModGL τ L}
    (hg : g ∈ subsystemGroup τ L (e6Set τ)) :
    frobTwistGL τ L ℓ f n₁ (frobTwistGL τ L ℓ f n₁ g) =
      Units.map (entrywiseHom (iterateFrobenius L ℓ (2 * f))) g := by
  rw [subsystemGroup] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [h.theta_xUnit hi, hπ, h.theta_xUnit (rhoτ_mem hi), hπ,
        rhoτ_rhoτ hi, units_map_entrywiseHom_xUnit, iterateFrobenius_def]
      exact congrArg (xUnit τ L i) (by rw [← pow_mul, ← pow_add, ← two_mul])
    · rw [h.theta_yUnit hi, hπ, h.theta_yUnit (rhoτ_mem hi), hπ,
        rhoτ_rhoτ hi, units_map_entrywiseHom_yUnit, iterateFrobenius_def]
      exact congrArg (yUnit τ L i) (by rw [← pow_mul, ← pow_add, ← two_mul])
  | one => rw [map_one, map_one, map_one]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, map_mul, hx, hy]
  | inv x _ hx => rw [map_inv, map_inv, map_inv, hx]

theorem StdTwist6.stdLayer_eq_range_of_rho [M27Ok τ]
    [E6Sub τ] {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)} (h : StdTwist6 n₁ π)
    (hπ : π = rhoτ τ) : stdLayer τ ℓ f n₁ = (psi2 τ L ℓ f).range := by
  set ι := (frobeniusFixedField L ℓ (2 * f)).subtype with hι
  ext g
  constructor
  · intro hg
    obtain ⟨hgQ, hgfix⟩ := mem_stdLayer.1 hg
    have hΘ : frobTwistGL τ L ℓ f n₁ g = g := hgfix
    have hfix2 : Units.map (entrywiseHom (iterateFrobenius L ℓ (2 * f))) g = g := by
      rw [← h.theta_theta hπ hgQ, hΘ, hΘ]
    obtain ⟨q, hq, rfl⟩ := exists_mem_map_of_frobenius_fixed (2 * f) hgQ hfix2
    set q' : subsystemGroup τ (K2 L ℓ f) (e6Set τ) := ⟨q, hq⟩ with hq'
    have h1 := h.theta_baseChange hπ q'
    rw [hΘ] at h1
    have h2 : theta2Q τ L ℓ f q' = q' :=
      Subtype.ext (baseChangeGL_injective ι h1.symm)
    have h3 : sigma (K2 L ℓ f) (theta2 L ℓ f) (m27Equiv τ (K2 L ℓ f) q') =
        m27Equiv τ (K2 L ℓ f) q' := by
      have := congrArg (m27Equiv τ (K2 L ℓ f)) h2
      rw [theta2Q_apply, MulEquiv.apply_symm_apply] at this
      exact this
    refine ⟨⟨m27Equiv τ (K2 L ℓ f) q', (mem_fixedGroup _).2 h3⟩, ?_⟩
    rw [psi2_apply]
    simp only [MulEquiv.symm_apply_apply]
    rfl
  · rintro ⟨x, rfl⟩
    set q' : subsystemGroup τ (K2 L ℓ f) (e6Set τ) := (m27Equiv τ (K2 L ℓ f)).symm x.1 with hq'
    have hgQ : psi2 τ L ℓ f x ∈ subsystemGroup τ L (e6Set τ) :=
      baseChangeGL_mem_subsystemGroup' ι q'.2
    refine mem_stdLayer.2 ⟨hgQ, ?_⟩
    have h1 := h.theta_baseChange hπ q'
    have h2 : theta2Q τ L ℓ f q' = q' := by
      have hx : sigma (K2 L ℓ f) (theta2 L ℓ f) x.1 = x.1 := (mem_fixedGroup _).1 x.2
      rw [theta2Q_apply, hq', MulEquiv.apply_symm_apply, hx]
    rw [h2] at h1
    exact h1

theorem StdTwist6.finite_quasisimple_of_rho [M27Ok τ] [E6Sub τ] {n₁ : ModGL τ L}
    {π : Equiv.Perm (Fin τ.rank)} (h : StdTwist6 n₁ π) (hπ : π = rhoτ τ) (hf : 1 ≤ f) :
    Finite (stdLayer τ ℓ f n₁) ∧ CFSG.IsQuasisimple (stdLayer τ ℓ f n₁) := by
  have := certificate123_of_kernel
  have hK : Finite (K2 L ℓ f) := finite_frobeniusFixedField (by omega)
  have hcard : 4 ≤ Nat.card (K2 L ℓ f) := by
    rw [card_K2 hf]
    have h2 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left h2 2
      _ ≤ ℓ ^ (2 * f) := Nat.pow_le_pow_right (by omega) (by omega)
  have hq := fixedGroup_isQuasisimple_of_four_le_card (theta2 L ℓ f) theta2_theta2 hcard
  have hfin : Finite (fixedGroup (K2 L ℓ f) (theta2 L ℓ f)) := by
    have : Finite (ModGL τ (K2 L ℓ f)) := finite_modGL
    have : Finite (subsystemGroup τ (K2 L ℓ f) (e6Set τ)) := inferInstance
    have : Finite (e6Data_valid.minGroup (K2 L ℓ f)) :=
      Finite.of_equiv _ (m27Equiv τ (K2 L ℓ f)).toEquiv
    infer_instance
  have hψ : Function.Injective (psi2 τ L ℓ f) := by
    intro x y hxy
    apply Subtype.ext
    have h1 := baseChangeGL_injective _ hxy
    have h2 := (m27Equiv τ (K2 L ℓ f)).symm.injective (Subtype.ext h1)
    exact h2
  exact finite_quasisimple_of_range (psi2 τ L ℓ f) hψ (h.stdLayer_eq_range_of_rho hπ) hfin hq

theorem StdTwist6.finite_quasisimple [M27Ok τ] [E6Sub τ] {n₁ : ModGL τ L}
    {π : Equiv.Perm (Fin τ.rank)} (h : StdTwist6 n₁ π) (hf : 1 ≤ f) :
    Finite (stdLayer τ ℓ f n₁) ∧ CFSG.IsQuasisimple (stdLayer τ ℓ f n₁) := by
  rcases h.hπ with h1 | h1
  · exact h.finite_quasisimple_of_one h1 hf
  · exact h.finite_quasisimple_of_rho h1 hf

end Rho

end CFSG.RankThree.PartOne.KE6
