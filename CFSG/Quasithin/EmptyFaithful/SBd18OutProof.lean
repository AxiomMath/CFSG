module

public import CFSG.Quasithin.EmptyFaithful.SBd18Out
public import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2

public section

namespace CFSG.Quasithin.SBd18

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel (autFixed mem_autFixed)

variable {K : Type} [Field K]

section General

private theorem fixedSub_eq_autFixed {P : Type*} [Group P] (α : MulAut P) :
    fixedSub α = autFixed α :=
  Subgroup.ext fun _ => Iff.rfl

private theorem eq_of_mul_self_eq {G : Type*} [Group G] (h3 : ∀ x : G, x ^ 3 = 1) {y z : G}
    (h : y * y = z * z) : y = z := by
  calc y = y ^ 3 * y := by rw [h3 y, one_mul]
    _ = (y * y) * (y * y) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (z * z) * (z * z) := by rw [h]
    _ = z ^ 3 * z := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = z := by rw [h3 z, one_mul]

private theorem right_conj (Ψ : MulAut (projectiveSL 3 K) →* OutGrp K)
    (x g : MulAut (projectiveSL 3 K)) : (Ψ (x * g * x⁻¹)).right = (Ψ g).right := by
  rw [map_mul, map_mul, map_inv, SemidirectProduct.mul_right, SemidirectProduct.mul_right,
    SemidirectProduct.inv_right, mul_comm (Ψ x).right, mul_inv_cancel_right]

private theorem right_cases (r : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    r = 1 ∨ r = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0) ∨
      r = (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1) ∨
      r = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) := by
  revert r
  decide

private theorem isSimpleGroup_projectiveSL_three {F : Type} [Field F] :
    IsSimpleGroup (projectiveSL 3 F) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F).symm.isSimpleGroup

private theorem isSimpleGroup_statedSp_one {F : Type} [Field F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedSp 1 F) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have : IsSimpleGroup (projectiveSL 2 F) :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 F).symm.isSimpleGroup
  exact ((CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne F).symm.trans
    (LinearCover.projectiveSLTwoEquivSL F).symm).isSimpleGroup

private theorem isSimpleGroup_autFixed_conj {G : Type*} [Group G] {x g : MulAut G}
    (hg : IsSimpleGroup (autFixed g)) : IsSimpleGroup (autFixed (x * g * x⁻¹)) := by
  rw [autFixed_conj]
  exact (Subgroup.equivMapOfInjective (autFixed g) x.toMonoidHom x.injective).symm.isSimpleGroup

end General

section Classes

variable {σ : K ≃+* K}

private theorem isSimpleGroup_autFixed_fieldAut (hK : Nat.card K = 4) (hσ : ∀ a, σ a = a ^ 2) :
    IsSimpleGroup (autFixed (fieldAut 3 K σ)) := by
  obtain ⟨e⟩ := nonempty_autFixed_fieldAut_equiv hK hσ
  have : IsSimpleGroup (projectiveSL 3
      ↥(CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField K σ)) :=
    isSimpleGroup_projectiveSL_three
  exact e.isSimpleGroup

private theorem isSimpleGroup_autFixed_dualAut [CharP K 2] (hK : Nat.card K = 4) :
    IsSimpleGroup (autFixed (dualAut 3 K)) := by
  obtain ⟨e⟩ := nonempty_autFixed_dualAut_equiv hK
  have := isSimpleGroup_statedSp_one (F := K) (by omega)
  exact e.isSimpleGroup

private theorem graphField_data (hK : Nat.card K = 4) (hσ : ∀ a, σ a = a ^ 2)
    {α : MulAut (projectiveSL 3 K)} {H : GL (Fin 3) K}
    (hH : α = conjAut 3 K H * betaAut σ * (conjAut 3 K H)⁻¹) (hc : Nat.card ↥(autFixed α) = 72) :
    ∃ E : Subgroup (projectiveSL 3 K), Nat.card ↥E = 9 ∧ (∀ e ∈ E, α e = e) ∧
      fixedSub α = Subgroup.normalizer (E : Set (projectiveSL 3 K)) ∧
      ∀ x ∈ E, x ≠ 1 → Subgroup.centralizer ({x} : Set (projectiveSL 3 K)) = E := by
  have hE9 : Nat.card ↥((eZero K).map (conjAut 3 K H).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (f := (conjAut 3 K H).toMonoidHom) (conjAut 3 K H).injective,
      card_eZero hK]
  have hfix : ∀ e ∈ (eZero K).map (conjAut 3 K H).toMonoidHom, α e = e := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hH, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, betaAut_fixed hK hσ hx]
  refine ⟨_, hE9, hfix, ?_, fun x hx hx1 => centralizer_eq_of_card_eq_nine hK hE9 hx hx1⟩
  rw [fixedSub_eq_autFixed]
  exact eq_normalizer_of_card_eq hK hc hE9 fun e he => (mem_autFixed).2 (hfix e he)

private theorem exists_conj_of_det_eq (hK : Nat.card K = 4) (g : MulAut (projectiveSL 3 K))
    {H₁ H₂ : GL (Fin 3) K}
    (h : Matrix.GeneralLinearGroup.det H₁ = Matrix.GeneralLinearGroup.det H₂) :
    ∃ p : projectiveSL 3 K, MulAut.conj p * (conjAut 3 K H₁ * g * (conjAut 3 K H₁)⁻¹) *
      (MulAut.conj p)⁻¹ = conjAut 3 K H₂ * g * (conjAut 3 K H₂)⁻¹ := by
  obtain ⟨p, hp⟩ := (LinearThreeFourOuter.conjAut_mem_range_conj_iff hK (H₂ * H₁⁻¹)).2
    (by rw [map_mul, map_inv, h, mul_inv_cancel])
  refine ⟨p, ?_⟩
  rw [hp, map_mul, map_inv]
  group

private theorem conjAut_diagGL_mul_betaAut (hK : Nat.card K = 4) (hσ : ∀ a, σ a = a ^ 2) (y : Kˣ) :
    conjAut 3 K (LinearThreeFourOuter.diagGL y) * betaAut σ =
      betaAut σ * conjAut 3 K (LinearThreeFourOuter.diagGL y) := by
  have hff := LinearThreeFourOuter.fieldAut_sigma_mul_self hσ hK
  have hβnf : betaAut σ = LinearThreeFourOuter.nf σ 1 1 1 := by
    simp [betaAut, LinearThreeFourOuter.nf, LinearThreeFourOuter.val_one_two]
  have hDinv : Matrix.GeneralLinearGroup.map (σ : K →+* K)
      (Matrix.GeneralLinearGroup.inverseTranspose (LinearThreeFourOuter.diagGL y)) =
        LinearThreeFourOuter.diagGL y := by
    rw [LinearThreeFourOuter.inverseTranspose_diagGL, LinearThreeFourOuter.map_sigma_diagGL hσ hK,
      inv_inv]
  rw [hβnf, ← LinearThreeFourOuter.nf_zero_zero σ, LinearThreeFourOuter.nf_mul σ hff,
    LinearThreeFourOuter.nf_mul σ hff, LinearThreeFourOuter.twistD_one_eq,
    LinearThreeFourOuter.twistF_one_eq, hDinv, LinearThreeFourOuter.twistD_one,
    LinearThreeFourOuter.twistF_one, one_mul, mul_one, add_comm (1 : ZMod 2) 0]

private theorem exists_conj_graphField (hK : Nat.card K = 4) (hσ : ∀ a, σ a = a ^ 2)
    (H₁ H₂ : GL (Fin 3) K) :
    ∃ p : projectiveSL 3 K, MulAut.conj p * (conjAut 3 K H₁ * betaAut σ * (conjAut 3 K H₁)⁻¹) *
      (MulAut.conj p)⁻¹ = conjAut 3 K H₂ * betaAut σ * (conjAut 3 K H₂)⁻¹ := by
  set y : Kˣ := (Matrix.GeneralLinearGroup.det H₂)⁻¹ * Matrix.GeneralLinearGroup.det H₁ with hy
  have hdet : Matrix.GeneralLinearGroup.det H₁ =
      Matrix.GeneralLinearGroup.det (H₂ * LinearThreeFourOuter.diagGL y) := by
    rw [map_mul, LinearThreeFourOuter.det_diagGL, hy, mul_inv_cancel_left]
  obtain ⟨p, hp⟩ := exists_conj_of_det_eq hK (betaAut σ) hdet
  refine ⟨p, hp.trans ?_⟩
  have hc : conjAut 3 K (LinearThreeFourOuter.diagGL y) * betaAut σ *
      (conjAut 3 K (LinearThreeFourOuter.diagGL y))⁻¹ = betaAut σ :=
    mul_inv_eq_iff_eq_mul.2 (conjAut_diagGL_mul_betaAut hK hσ y)
  calc conjAut 3 K (H₂ * LinearThreeFourOuter.diagGL y) * betaAut σ *
        (conjAut 3 K (H₂ * LinearThreeFourOuter.diagGL y))⁻¹
      = conjAut 3 K H₂ * (conjAut 3 K (LinearThreeFourOuter.diagGL y) * betaAut σ *
          (conjAut 3 K (LinearThreeFourOuter.diagGL y))⁻¹) * (conjAut 3 K H₂)⁻¹ := by
        rw [map_mul]
        group
    _ = conjAut 3 K H₂ * betaAut σ * (conjAut 3 K H₂)⁻¹ := by rw [hc]

end Classes

section Outer

variable {σ : K ≃+* K} {Ψ : MulAut (projectiveSL 3 K) →* OutGrp K}
  (hΨ : ∀ (A : GL (Fin 3) K) (a b : ZMod 2), Ψ (LinearThreeFourOuter.nf σ A a b) =
    ⟨Matrix.GeneralLinearGroup.det A, (Multiplicative.ofAdd a, Multiplicative.ofAdd b)⟩)
include hΨ

private theorem psi_conjAut (A : GL (Fin 3) K) :
    Ψ (conjAut 3 K A) = SemidirectProduct.inl (Matrix.GeneralLinearGroup.det A) := by
  rw [← LinearThreeFourOuter.nf_zero_zero σ, hΨ]
  rfl

private theorem psi_fieldAut :
    Ψ (fieldAut 3 K σ) =
      SemidirectProduct.inr (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0) := by
  rw [← LinearThreeFourOuter.nf_one_zero σ, hΨ, map_one]
  rfl

private theorem psi_dualAut :
    Ψ (dualAut 3 K) =
      SemidirectProduct.inr (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1) := by
  rw [← LinearThreeFourOuter.nf_zero_one σ, hΨ, map_one]
  rfl

private theorem psi_betaAut :
    Ψ (betaAut σ) =
      SemidirectProduct.inr (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) := by
  rw [betaAut, map_mul, psi_fieldAut hΨ, psi_dualAut hΨ, ← map_mul]
  rfl

private theorem left_psi_conj {g : MulAut (projectiveSL 3 K)} {a b : ZMod 2} (hab : a + b ≠ 0)
    (hg : Ψ g = SemidirectProduct.inr (Multiplicative.ofAdd a, Multiplicative.ofAdd b))
    (H : GL (Fin 3) K) :
    (Ψ (conjAut 3 K H * g * (conjAut 3 K H)⁻¹)).left =
      Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det H := by
  rw [map_mul, map_mul, map_inv, psi_conjAut hΨ, hg]
  simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, OutGrp.act_apply, hab]

private theorem det_eq_of_psi_eq (hK : Nat.card K = 4) {g : MulAut (projectiveSL 3 K)}
    {a b : ZMod 2} (hab : a + b ≠ 0)
    (hg : Ψ g = SemidirectProduct.inr (Multiplicative.ofAdd a, Multiplicative.ofAdd b))
    {H₁ H₂ : GL (Fin 3) K}
    (h : Ψ (conjAut 3 K H₁ * g * (conjAut 3 K H₁)⁻¹) =
      Ψ (conjAut 3 K H₂ * g * (conjAut 3 K H₂)⁻¹)) :
    Matrix.GeneralLinearGroup.det H₁ = Matrix.GeneralLinearGroup.det H₂ :=
  eq_of_mul_self_eq (LinearThreeFourOuter.units_pow_three hK)
    ((left_psi_conj hΨ hab hg H₁).symm.trans
      ((congrArg SemidirectProduct.left h).trans (left_psi_conj hΨ hab hg H₂)))

private theorem involution_data (hK : Nat.card K = 4) (hσ : ∀ a, σ a = a ^ 2)
    {α : MulAut (projectiveSL 3 K)} (hα : α * α = 1) :
    ((Ψ α).right = 1 →
      α ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) ∧
    ((Ψ α).right = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0) →
      (∃ H : GL (Fin 3) K, α = conjAut 3 K H * fieldAut 3 K σ * (conjAut 3 K H)⁻¹) ∧
        Nat.card ↥(autFixed α) = 168) ∧
    ((Ψ α).right = (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1) →
      (∃ H : GL (Fin 3) K, α = conjAut 3 K H * dualAut 3 K * (conjAut 3 K H)⁻¹) ∧
        Nat.card ↥(autFixed α) = 60) ∧
    ((Ψ α).right = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) →
      (∃ H : GL (Fin 3) K, α = conjAut 3 K H * betaAut σ * (conjAut 3 K H)⁻¹) ∧
        Nat.card ↥(autFixed α) = 72) := by
  have hker := LinearThreeFourOuter.ker_eq_range_conj hσ hK hΨ
  rcases involution_cases_card hK hσ hα with h | ⟨⟨H, hH⟩, hc⟩ | ⟨⟨H, hH⟩, hc⟩ | ⟨⟨H, hH⟩, hc⟩
  · have h1 : (Ψ α).right = 1 := by
      have h0 : Ψ α = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact h
      exact congrArg SemidirectProduct.right h0
    exact ⟨fun _ => h, fun hr => absurd (h1.symm.trans hr) (by decide),
      fun hr => absurd (h1.symm.trans hr) (by decide),
      fun hr => absurd (h1.symm.trans hr) (by decide)⟩
  · have h1 : (Ψ α).right = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0) := by
      rw [hH, right_conj, psi_fieldAut hΨ]
      rfl
    exact ⟨fun hr => absurd (h1.symm.trans hr) (by decide), fun _ => ⟨⟨H, hH⟩, hc⟩,
      fun hr => absurd (h1.symm.trans hr) (by decide),
      fun hr => absurd (h1.symm.trans hr) (by decide)⟩
  · have h1 : (Ψ α).right = (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1) := by
      rw [hH, right_conj, psi_dualAut hΨ]
      rfl
    exact ⟨fun hr => absurd (h1.symm.trans hr) (by decide),
      fun hr => absurd (h1.symm.trans hr) (by decide), fun _ => ⟨⟨H, hH⟩, hc⟩,
      fun hr => absurd (h1.symm.trans hr) (by decide)⟩
  · have h1 : (Ψ α).right = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) := by
      rw [hH, right_conj, psi_betaAut hΨ]
      rfl
    exact ⟨fun hr => absurd (h1.symm.trans hr) (by decide),
      fun hr => absurd (h1.symm.trans hr) (by decide),
      fun hr => absurd (h1.symm.trans hr) (by decide), fun _ => ⟨⟨H, hH⟩, hc⟩⟩

end Outer

theorem outFacts {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) :
    OutFacts K := by
  have hσ : ∀ a, frobeniusEquiv K 2 a = a ^ 2 := fun a => frobeniusEquiv_apply K 2 a
  obtain ⟨Ψ, hΨ⟩ := LinearThreeFourOuter.exists_outerHom hσ hK
  refine ⟨⟨Ψ, LinearThreeFourOuter.surjective_of_nf hΨ,
    LinearThreeFourOuter.ker_eq_range_conj hσ hK hΨ, ?_, ?_⟩⟩
  · intro α hα
    obtain ⟨h0, hf, hd, hb⟩ := involution_data hΨ hK hσ hα
    refine ⟨h0, fun hr => ?_, fun hr => ?_, fun hr => ?_⟩
    · obtain ⟨⟨H, rfl⟩, hc⟩ := hf hr
      rw [fixedSub_eq_autFixed]
      exact ⟨hc, isSimpleGroup_autFixed_conj (isSimpleGroup_autFixed_fieldAut hK hσ)⟩
    · obtain ⟨⟨H, rfl⟩, hc⟩ := hd hr
      rw [fixedSub_eq_autFixed]
      exact ⟨hc, isSimpleGroup_autFixed_conj (isSimpleGroup_autFixed_dualAut hK)⟩
    · obtain ⟨⟨H, hH⟩, hc⟩ := hb hr
      exact graphField_data hK hσ hH hc
  · intro α α' hα hα' hΨeq hne
    have hrr : (Ψ α).right = (Ψ α').right := congrArg SemidirectProduct.right hΨeq
    obtain ⟨-, hf, hd, hb⟩ := involution_data hΨ hK hσ hα
    obtain ⟨-, hf', hd', hb'⟩ := involution_data hΨ hK hσ hα'
    rcases right_cases (Ψ α).right with h | h | h | h
    · exact absurd h hne
    · obtain ⟨⟨H₁, rfl⟩, -⟩ := hf h
      obtain ⟨⟨H₂, rfl⟩, -⟩ := hf' (hrr.symm.trans h)
      exact exists_conj_of_det_eq hK _
        (det_eq_of_psi_eq hΨ hK (a := 1) (b := 0) (by decide) (psi_fieldAut hΨ) hΨeq)
    · obtain ⟨⟨H₁, rfl⟩, -⟩ := hd h
      obtain ⟨⟨H₂, rfl⟩, -⟩ := hd' (hrr.symm.trans h)
      exact exists_conj_of_det_eq hK _
        (det_eq_of_psi_eq hΨ hK (a := 0) (b := 1) (by decide) (psi_dualAut hΨ) hΨeq)
    · obtain ⟨⟨H₁, rfl⟩, -⟩ := hb h
      obtain ⟨⟨H₂, rfl⟩, -⟩ := hb' (hrr.symm.trans h)
      exact exists_conj_graphField hK hσ H₁ H₂

end CFSG.Quasithin.SBd18
