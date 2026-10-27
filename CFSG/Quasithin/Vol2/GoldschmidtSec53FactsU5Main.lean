module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsDiagLie
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsDiagMap

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Open CFSG.QuasithinUnique
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.BA

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem u5_normal_form (α : MulAut (hypPSU hK 2 1))
    (hα : ∀ x, α x ∈ hypProjUnitriangular hK 2 1 ↔ x ∈ hypProjUnitriangular hK 2 1) :
    ∃ e ∈ Eext hK, ∃ σ ∈ MonoidHom.range (fieldP hK), α = e * σ := by
  obtain ⟨x₀, hx₀⟩ := Phi_surjective hK α
  obtain ⟨x, hxΦ, hxr, hxU⟩ := exists_unitary_rep hK (r := 2) (ε := 1) (by norm_num)
    (by norm_num) (by norm_num) x₀
  set A : GL (HypIndex 2 1) K := (x : SemiGL (HypIndex 2 1) K).left with hAdef
  set σ : K ≃+* K := (x : SemiGL (HypIndex 2 1) K).right with hσdef
  set δ : Kˣ := Matrix.GeneralLinearGroup.det A with hδdef
  have hδ : hK.norm (δ : K) = 1 := by
    rw [hδdef, Matrix.GeneralLinearGroup.val_det_apply]
    exact norm_det_eq_one hxU
  have hδ' : δ ∈ normOne hK := (mem_normOne hK).2 hδ
  have hδi : hK.norm ((δ⁻¹ : Kˣ) : K) = 1 := (mem_normOne hK).1 ((normOne hK).inv_mem hδ')
  have hgu : A * dGL hK δ⁻¹ ∈ hypUnitary hK 2 1 := mul_mem hxU (dGL_mem_hypUnitary hK hδi)
  have hgd : ((A * dGL hK δ⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K).det
      = 1 := by
    rw [Units.val_mul, Matrix.det_mul, det_dGL, ← Matrix.GeneralLinearGroup.val_det_apply,
      ← hδdef, Units.val_inv_eq_inv_val, mul_inv_cancel₀ δ.ne_zero]
  let g : hypSU hK 2 1 := ⟨A * dGL hK δ⁻¹, mem_gramSU.2 ⟨mem_hypUnitary.1 hgu, hgd⟩⟩
  have hA : (g : GL (HypIndex 2 1) K) * dGL hK δ = A := by
    change A * dGL hK δ⁻¹ * dGL hK δ = A
    rw [mul_assoc, ← dGL_mul, inv_mul_cancel, dGL_one, mul_one]
  have hx : x = inlG g * dGam hK δ hδ * inrGam hK σ := by
    refine Subtype.ext ?_
    rw [← SemidirectProduct.inl_left_mul_inr_right (x : SemiGL (HypIndex 2 1) K)]
    change SemidirectProduct.inl A * SemidirectProduct.inr σ =
      SemidirectProduct.inl (g : GL (HypIndex 2 1) K) * SemidirectProduct.inl (dGL hK δ) *
        SemidirectProduct.inr σ
    rw [← map_mul, hA]
  have hα' : α = innM hK g * dHom hK ⟨δ, hδ'⟩ * fieldP hK σ := by
    have h1 : Phi hK x = α := hxΦ.trans hx₀
    rw [← h1, hx, map_mul, map_mul, Phi_inlG]
    rfl
  have hstab : ∀ y, MulAut.conj (hypProj hK 2 1 g) y ∈ hypProjUnitriangular hK 2 1 ↔
      y ∈ hypProjUnitriangular hK 2 1 := by
    intro y
    have e1 : MulAut.conj (hypProj hK 2 1 g) = α * (fieldP hK σ)⁻¹ * (dHom hK ⟨δ, hδ'⟩)⁻¹ := by
      have : MulAut.conj (hypProj hK 2 1 g) = innM hK g := rfl
      rw [this, hα']
      group
    have h2 := dHom_stab hK ⟨δ, hδ'⟩ ((dHom hK ⟨δ, hδ'⟩)⁻¹ y)
    rw [MulAut.apply_inv_self] at h2
    have h3 := fieldP_stab_U hK σ ((fieldP hK σ)⁻¹ ((dHom hK ⟨δ, hδ'⟩)⁻¹ y))
    rw [MulAut.apply_inv_self] at h3
    rw [e1, MulAut.mul_apply, MulAut.mul_apply, hα]
    exact h3.symm.trans h2.symm
  have hgB : hypProj hK 2 1 g ∈ Subgroup.normalizer ((hypProjUnitriangular hK 2 1 :
      Subgroup (hypPSU hK 2 1)) : Set (hypPSU hK 2 1)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [← MulAut.conj_apply]
    exact (hstab y).symm
  refine ⟨MulAut.conj (hypProj hK 2 1 g) * dHom hK ⟨δ, hδ'⟩,
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, hgB, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩),
    fieldP hK σ, ⟨σ, rfl⟩, ?_⟩
  rw [hα']
  rfl

theorem borelAutDiag_u5 : BorelAutDiag (hypProjUnitriangular hK 2 1)
    ((hypTorus hK 2 1).map (hypProj hK 2 1)) (MonoidHom.range (fieldP hK)) (Eext hK) := by
  have := hK.finite
  exact
    { borelBase_u5 hK with
      F_U := by
        rintro _ ⟨τ, rfl⟩ x
        exact fieldP_stab_U hK τ x
      F_H := by
        rintro _ ⟨τ, rfl⟩ h hh
        exact (fieldP_stab_H hK τ h).2 hh
      F_solv := Group.isSolvable_of_comm fun a b => by
        obtain ⟨σ, hσ⟩ := a.2
        obtain ⟨τ, hτ⟩ := b.2
        apply Subtype.ext
        change (a : MulAut (hypPSU hK 2 1)) * b = b * a
        rw [← hσ, ← hτ]
        exact fieldP_comm hK σ τ
      F_faithful := by
        rintro _ ⟨τ, rfl⟩ hfix
        rw [eq_one_of_fieldP_fixes hK τ hfix, map_one]
      E_U := fun e he x => (Eext_le_trivSub hK he).1 x
      E_solv := Eext_solvable hK
      E_triv := fun e he b hb => (Eext_le_trivSub hK he).2 b hb
      E_two := Eext_two hK
      F_E := by
        rintro _ ⟨τ, rfl⟩ e he
        exact fieldP_conj_Eext hK τ he
      normal_form := fun α hα => u5_normal_form hK α hα }

end CFSG.Quasithin.H13.Sec53F.Unit

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

theorem lieBorelFactsDiag_u5 : LieBorelFactsDiag .PSU 5 := by
  intro Y _ _ f hpar hY U hU
  rcases hY with ⟨-, hc⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hc
    have hm : 1 ≤ f := hadm.2.1
    have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
    let e' : hypPSU h 2 1 ≃* Y :=
      (hypPSUEquivStatedProj h hR (by norm_num)).trans e.symm
    have := Unit.finite_hypPSU_five h
    exact (Unit.borelAutDiag_u5 h).exists_of_equiv e'.symm hU
  all_goals exact absurd hn (by norm_num)

theorem lieAutFacts_u5 : LieAutFacts .PSU 5 :=
  lieAutFacts_of_lieBorelFactsDiag lieBorelFactsDiag_u5

end CFSG.Quasithin.H13.Sec53F
