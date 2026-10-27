module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts1
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts5
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Subgroup
  CFSG.Open

open scoped commutatorElement

local notation "GL3" => Matrix.GeneralLinearGroup (Fin 3) OmegaField
local notation "Gam3" => coordinateSemilinearGroup 3 OmegaField

private theorem s16h_e3_z3_inv_mul_inv_of_pow_three {G : Type*} [Group G] {a : G}
    (h : a ^ 3 = 1) : a⁻¹ * a⁻¹ = a := by
  have h2 : a * a * a = 1 := by rw [← pow_three']; exact h
  calc a⁻¹ * a⁻¹ = (a * a * a)⁻¹ * a := by group
    _ = a := by rw [h2]; group

private theorem s16h_e3_z3_commutator_eq_of_inverts {G : Type*} [Group G] {x g : G}
    (hx : x * g * x⁻¹ = g⁻¹) (hg : g ^ 3 = 1) : ⁅x, g⁆ = g := by
  rw [commutatorElement_def, hx]
  exact s16h_e3_z3_inv_mul_inv_of_pow_three hg

private theorem s16h_e3_z3_ringEquiv_pow_three_eq_one (σ : OmegaField ≃+* OmegaField)
    (hσ : σ ^ 3 = 1) : σ = 1 := by
  by_contra hne
  have hsq : ∀ x : OmegaField, σ x = x ^ 2 := s16h_e3_z3f5_ringEquiv_eq_sq σ hne
  have h2 : σ ^ 2 = 1 := by
    ext x
    change σ (σ x) = x
    rw [hsq x, map_pow, hsq x]
    rw [← pow_mul x 2 2]
    show x ^ 4 = x
    exact s16h_e3_z3f5_pow_four_eq_self x
  have h3 : σ ^ 3 = σ := by rw [pow_succ, h2, one_mul]
  rw [h3] at hσ
  exact hne hσ

private theorem s16h_e3_z3_rightHom_eq_one_of_pow_three (g : Gam3) (hg : g ^ 3 = 1) :
    SemidirectProduct.rightHom g = 1 := by
  refine s16h_e3_z3_ringEquiv_pow_three_eq_one (SemidirectProduct.rightHom g) ?_
  rw [← map_pow (SemidirectProduct.rightHom) g 3, hg, map_one]

private theorem s16h_e3_z3_mem_range_inl_of_pow_three (g : Gam3) (hg : g ^ 3 = 1) :
    g ∈ (SemidirectProduct.inl : GL3 →* Gam3).range := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  exact s16h_e3_z3_rightHom_eq_one_of_pow_three g hg

private theorem s16h_e3_z3_isElemAbelian_map_inl {P : Subgroup GL3}
    (hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP3 : ∀ a ∈ P, a ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) P) := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro x y
    obtain ⟨a, haP, ha⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨b, hbP, hb⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    change (x : Gam3) * (y : Gam3) = (y : Gam3) * (x : Gam3)
    calc (x : Gam3) * (y : Gam3) = SemidirectProduct.inl (a * b) := by rw [← ha, ← hb, map_mul]
      _ = SemidirectProduct.inl (b * a) := by rw [hPcomm a haP b hbP]
      _ = (y : Gam3) * (x : Gam3) := by rw [← hb, ← ha, map_mul]
  · intro x hx
    obtain ⟨a, haP, ha⟩ := Subgroup.mem_map.mp hx
    rw [← ha, ← map_pow, hP3 a haP, map_one]

private theorem s16h_e3_z3_mem_normalizer_of_normal {N : Subgroup Gam3} {F : Subgroup GL3}
    (hFnorm : ((Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) F).subgroupOf N).Normal)
    (hFleN : Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) F ≤ N)
    {a : GL3} (haN : (SemidirectProduct.inl a : Gam3) ∈ N) :
    a ∈ Subgroup.normalizer (F : Set GL3) := by
  have hconj : ∀ h k : Gam3, h ∈ Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) F →
      k ∈ N → k * h * k⁻¹ ∈ Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) F :=
    (Subgroup.normal_subgroupOf_iff hFleN).mp hFnorm
  rw [Subgroup.mem_normalizer_iff]
  intro f
  constructor
  · intro hf
    have hmem : (SemidirectProduct.inl a : Gam3) * SemidirectProduct.inl f *
        (SemidirectProduct.inl a)⁻¹ ∈ Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) F :=
      hconj (SemidirectProduct.inl f) (SemidirectProduct.inl a)
        (Subgroup.mem_map.mpr ⟨f, hf, rfl⟩) haN
    rcases Subgroup.mem_map.mp hmem with ⟨y, hy, hyx⟩
    have hy' : y = a * f * a⁻¹ := SemidirectProduct.inl_injective (by
      rw [hyx]; simp only [map_mul, map_inv])
    simpa [hy'] using hy
  · intro hf
    have haNin : (SemidirectProduct.inl a⁻¹ : Gam3) ∈ N := by
      have := inv_mem haN
      simpa [map_inv] using this
    have hmem : (SemidirectProduct.inl a⁻¹ : Gam3) *
        SemidirectProduct.inl (a * f * a⁻¹) * (SemidirectProduct.inl a⁻¹)⁻¹ ∈
        Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) F :=
      hconj (SemidirectProduct.inl (a * f * a⁻¹)) (SemidirectProduct.inl a⁻¹)
        (Subgroup.mem_map.mpr ⟨a * f * a⁻¹, hf, rfl⟩) haNin
    have h2 : (SemidirectProduct.inl a⁻¹ : Gam3) *
          SemidirectProduct.inl (a * f * a⁻¹) * (SemidirectProduct.inl a⁻¹)⁻¹ =
        SemidirectProduct.inl f := by
      simp only [map_mul, map_inv]
      group
    rw [h2] at hmem
    rcases Subgroup.mem_map.mp hmem with ⟨y, hy, hyx⟩
    have hy' : y = f := SemidirectProduct.inl_injective hyx
    simpa [hy'] using hy

theorem s16h_e3_z3_scalar_contra
    (N K : Subgroup (coordinateSemilinearGroup 3 OmegaField))
    (hKN : K ≤ N) (hKnorm : (K.subgroupOf N).Normal)
    (hno : ∀ P : Subgroup (coordinateSemilinearGroup 3 OmegaField), P ≤ K →
      IsElemAbelian 3 P → Nat.card ↥P < 9)
    {t : coordinateSemilinearGroup 3 OmegaField} (htK : t ∈ K) (ht2 : t ^ 2 = 1)
    (htn : SemidirectProduct.rightHom t ≠ 1)
    {Q : Subgroup (coordinateSemilinearGroup 3 OmegaField)} (hQN : Q ≤ N)
    (hQ : IsElemAbelian 3 Q) (hQ9 : 9 ≤ Nat.card ↥Q)
    (F : Subgroup (Matrix.GeneralLinearGroup (Fin 3) OmegaField))
    (hF : Nat.card ↥F = 5)
    (hFnorm : ((Subgroup.map (SemidirectProduct.inl :
      Matrix.GeneralLinearGroup (Fin 3) OmegaField →*
        coordinateSemilinearGroup 3 OmegaField) F).subgroupOf N).Normal)
    (hFleK : Subgroup.map (SemidirectProduct.inl :
      Matrix.GeneralLinearGroup (Fin 3) OmegaField →*
        coordinateSemilinearGroup 3 OmegaField) F ≤ K) :
    False := by
  classical
  obtain ⟨P, hPcard, hP3, hPcomm, hPmem, hPinv⟩ := s16h_e3_z3_order_five hF
  have hFleN : Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) F ≤ N := hFleK.trans hKN
  have hconjK : ∀ h k : Gam3, h ∈ K → k ∈ N → k * h * k⁻¹ ∈ K :=
    (Subgroup.normal_subgroupOf_iff hKN).mp hKnorm
  have hNle : N ≤ Subgroup.normalizer
      (Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) F : Set Gam3) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFleN).mp hFnorm
  have hsub : Q ≤ Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) P := by
    intro q hq
    have hq3 : q ^ 3 = 1 := hQ.2 q hq
    obtain ⟨a, ha⟩ := s16h_e3_z3_mem_range_inl_of_pow_three q hq3
    refine Subgroup.mem_map.mpr ⟨a, ?_, ha⟩
    have ha3 : a ^ 3 = 1 := by
      have h : (SemidirectProduct.inl (a ^ 3) : Gam3) = SemidirectProduct.inl 1 := by
        rw [map_pow, ha, hq3, map_one]
      exact SemidirectProduct.inl_injective h
    refine hPmem a ?_ ha3
    exact s16h_e3_z3_mem_normalizer_of_normal hFnorm hFleN (by rw [ha]; exact hQN hq)
  have hcardA : Nat.card ↥(Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) P) = 9 := by
    rw [Subgroup.card_map_of_injective SemidirectProduct.inl_injective, hPcard]
  haveI : Finite ↥(Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) P) :=
    Nat.finite_of_card_ne_zero (by rw [hcardA]; norm_num)
  have hQA : Q = Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) P :=
    Subgroup.eq_of_le_of_card_ge hsub (by rw [hcardA]; exact hQ9)
  have hAN : Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) P ≤ N := hQA ▸ hQN
  have hAK : Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) P ≤ K := by
    intro x hx
    obtain ⟨a, haP, ha⟩ := Subgroup.mem_map.mp hx
    rw [← ha]
    have hxA : (SemidirectProduct.inl a : Gam3) ∈
        Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) P :=
      Subgroup.mem_map.mpr ⟨a, haP, rfl⟩
    have haN : (SemidirectProduct.inl a : Gam3) ∈ N := hAN hxA
    have ha3 : (SemidirectProduct.inl a : Gam3) ^ 3 = 1 := by
      rw [← map_pow, hP3 a haP, map_one]
    have hinv : t * (SemidirectProduct.inl a : Gam3) * t⁻¹ = (SemidirectProduct.inl a)⁻¹ :=
      hPinv t (hNle (hKN htK)) htn a haP
    have hcomm : ⁅t, (SemidirectProduct.inl a : Gam3)⁆ = SemidirectProduct.inl a :=
      s16h_e3_z3_commutator_eq_of_inverts hinv ha3
    have hcommK : ⁅t, (SemidirectProduct.inl a : Gam3)⁆ ∈ K := by
      have hmem : (SemidirectProduct.inl a : Gam3) * t⁻¹ * (SemidirectProduct.inl a)⁻¹ ∈ K :=
        hconjK t⁻¹ (SemidirectProduct.inl a) (inv_mem htK) haN
      have h2 : t * (SemidirectProduct.inl a : Gam3) * t⁻¹ * (SemidirectProduct.inl a)⁻¹ =
          t * ((SemidirectProduct.inl a : Gam3) * t⁻¹ * (SemidirectProduct.inl a)⁻¹) := by
        group
      rw [commutatorElement_def, h2]
      exact mul_mem htK hmem
    rwa [hcomm] at hcommK
  have hA : IsElemAbelian 3 (Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) P) :=
    s16h_e3_z3_isElemAbelian_map_inl hPcomm hP3
  exact absurd (hno (Subgroup.map (SemidirectProduct.inl : GL3 →* Gam3) P) hAK hA)
    (by rw [hcardA]; norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
