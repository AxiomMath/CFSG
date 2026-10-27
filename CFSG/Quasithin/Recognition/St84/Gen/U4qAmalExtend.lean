module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalRoots
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitAut
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitBorel
public import CFSG.RankThree.CentralLiftU.UnitaryBorelLift

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par
open CFSG.Quasithin.H13.Sec53F.Unit (fieldAut fieldAut_apply mat_fieldHom
  fieldAut_mem_unitriangular fieldAut_mem_torus)

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem coe_fieldAut_u4 (ρ : K ≃+* K) (g : hypSU h 2 0) :
    (((fieldAut h ρ g : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      ((g : GL Ix K) : Matrix Ix Ix K).map ρ := by
  rw [fieldAut_apply, mat_fieldHom]

theorem fieldAut_mem_parP_iff_u4 (ρ : K ≃+* K) (g : hypSU h 2 0) :
    fieldAut h ρ g ∈ parP h ↔ g ∈ parP h := by
  rw [mem_parP_iff, mem_parP_iff, coe_fieldAut_u4]
  simp only [map_apply, map_eq_zero]

theorem fieldAut_mem_parP2_iff_u4 (ρ : K ≃+* K) (g : hypSU h 2 0) :
    fieldAut h ρ g ∈ parP2 h ↔ g ∈ parP2 h := by
  rw [mem_parP2_iff, mem_parP2_iff, coe_fieldAut_u4]
  simp only [map_apply, map_eq_zero]

theorem fieldAut_syElt_u4 (ρ : K ≃+* K) (y : K) : fieldAut h ρ (syElt h y) = syElt h (ρ y) := by
  apply hypSU_ext h
  rw [coe_fieldAut_u4, coe_syElt, coe_syElt]
  ext i j
  rw [map_apply]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [sMat_apply, one_apply, UnitaryHigher.map_bar_comm h ρ]

theorem bar_ringEquiv_u4 (ρ : K ≃+* K) {t : K} (ht : h.bar t = t) : h.bar (ρ t) = ρ t := by
  rw [← UnitaryHigher.map_bar_comm h ρ, ht]

theorem fieldAut_u4xbElt (ρ : K ≃+* K) {t : K} (ht : h.bar t = t) :
    fieldAut h ρ (u4xbElt h ht) = u4xbElt h (bar_ringEquiv_u4 h ρ ht) := by
  apply hypSU_ext h
  rw [coe_fieldAut_u4, coe_u4xbElt, coe_u4xbElt]
  ext i j
  rw [map_apply]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [u4xbMat_apply, one_apply]

private theorem conj_mem_iff_u4 {G : Type*} [Group G] {S : Subgroup G} {d : G} (hd : d ∈ S)
    (x : G) : d * x * d⁻¹ ∈ S ↔ x ∈ S := by
  rw [Subgroup.mul_mem_cancel_right S (S.inv_mem hd), Subgroup.mul_mem_cancel_left S hd]

@[expose] noncomputable def u4StdAut (d : hypSU h 2 0) (ρ : K ≃+* K) : MulAut (hypSU h 2 0) :=
  MulAut.conj d * fieldAut h ρ

theorem u4StdAut_apply (d : hypSU h 2 0) (ρ : K ≃+* K) (g : hypSU h 2 0) :
    u4StdAut h d ρ g = d * fieldAut h ρ g * d⁻¹ :=
  rfl

theorem coe_stdAut_syElt_u4 {d : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) (ρ : K ≃+* K) (y : K) :
    (((u4StdAut h d ρ (syElt h y) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      sMat h 0 (q if2 * (q if1)⁻¹ * ρ y) 0 := by
  rw [u4StdAut_apply, fieldAut_syElt_u4, coe_conj_syElt_of_diag h hd]

theorem coe_stdAut_u4xbElt {d : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) (ρ : K ≃+* K) {t : K}
    (ht : h.bar t = t) :
    (((u4StdAut h d ρ (u4xbElt h ht) : hypSU h 2 0) : GL Ix K) :
      Matrix Ix Ix K) = u4xbMat (q ie2 * (q if2)⁻¹ * ρ t) := by
  rw [u4StdAut_apply, fieldAut_u4xbElt, coe_conj_u4xbElt_of_diag h hd]

theorem stdAut_mem_parP_iff_u4 {d : hypSU h 2 0} (hd : d ∈ parP h) (ρ : K ≃+* K)
    (g : hypSU h 2 0) : u4StdAut h d ρ g ∈ parP h ↔ g ∈ parP h := by
  rw [u4StdAut_apply, conj_mem_iff_u4 hd, fieldAut_mem_parP_iff_u4]

theorem stdAut_mem_parP2_iff_u4 {d : hypSU h 2 0} (hd : d ∈ parP2 h) (ρ : K ≃+* K)
    (g : hypSU h 2 0) : u4StdAut h d ρ g ∈ parP2 h ↔ g ∈ parP2 h := by
  rw [u4StdAut_apply, conj_mem_iff_u4 hd, fieldAut_mem_parP2_iff_u4]

theorem stdAut_mem_hypUnitriangular_iff_u4 {d : hypSU h 2 0} (hd : d ∈ hypBorel h 2 0)
    (ρ : K ≃+* K) (g : hypSU h 2 0) :
    u4StdAut h d ρ g ∈ hypUnitriangular h 2 0 ↔ g ∈ hypUnitriangular h 2 0 := by
  rw [u4StdAut_apply, ← fieldAut_mem_unitriangular h ρ g]
  constructor
  · intro hg
    have := CFSG.RankThree.CentralLiftU.conj_mem_hypUnitriangular_of_mem_hypBorel (by norm_num)
      ((hypBorel h 2 0).inv_mem hd) hg
    simpa [mul_assoc] using this
  · exact CFSG.RankThree.CentralLiftU.conj_mem_hypUnitriangular_of_mem_hypBorel (by norm_num) hd

theorem stdAut_mem_hypTorus_u4 {d : hypSU h 2 0} (hd : d ∈ hypTorus h 2 0) (ρ : K ≃+* K)
    {g : hypSU h 2 0} (hg : g ∈ hypTorus h 2 0) :
    u4StdAut h d ρ g ∈ hypTorus h 2 0 := by
  rw [u4StdAut_apply]
  exact (hypTorus h 2 0).mul_mem ((hypTorus h 2 0).mul_mem hd (fieldAut_mem_torus h ρ hg))
    ((hypTorus h 2 0).inv_mem hd)

theorem eq_of_agree_u4Roots {τ : MulAut ↥(parP h ⊓ parP2 h)} {Ψ : MulAut (hypSU h 2 0)}
    (hΨU : ∀ g, g ∈ hypUnitriangular h 2 0 ↔ Ψ g ∈ hypUnitriangular h 2 0)
    (hΨH : ∀ g ∈ hypTorus h 2 0, Ψ g ∈ hypTorus h 2 0)
    (hτH : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ hypTorus h 2 0 →
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ hypTorus h 2 0)
    (hA : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ u4RootA h →
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) = Ψ b)
    (hB : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ u4RootB h →
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) = Ψ b)
    (b : ↥(parP h ⊓ parP2 h)) : ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) = Ψ b := by
  let E : Subgroup ↥(parP h ⊓ parP2 h) :=
    MonoidHom.eqLocus ((parP h ⊓ parP2 h).subtype.comp τ.toMonoidHom)
      (Ψ.toMonoidHom.comp (parP h ⊓ parP2 h).subtype)
  let S : Subgroup (hypSU h 2 0) := E.map (parP h ⊓ parP2 h).subtype
  have hS : ∀ (g : hypSU h 2 0) (hg : g ∈ parP h ⊓ parP2 h),
      g ∈ S ↔ ((τ ⟨g, hg⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) = Ψ g := by
    intro g hg
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro H
      exact ⟨⟨g, hg⟩, H, rfl⟩
  have hUS : hypUnitriangular h 2 0 ≤ S :=
    hypUnitriangular_le_of_u4Roots h (fun g hg => (hS g (u4RootA_le_inf h hg)).mpr
      (hA ⟨g, u4RootA_le_inf h hg⟩ hg)) (fun g hg => (hS g (u4RootB_le_inf h hg)).mpr
      (hB ⟨g, u4RootB_le_inf h hg⟩ hg))
  have hHS : hypTorus h 2 0 ≤ S := by
    intro k hk
    have hkB : k ∈ parP h ⊓ parP2 h := hypTorus_le_inf_u4 h hk
    rw [hS k hkB]
    have hτk := hτH ⟨k, hkB⟩ hk
    have hcH : (Ψ k)⁻¹ * ((τ ⟨k, hkB⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ hypTorus h 2 0 :=
      (hypTorus h 2 0).mul_mem ((hypTorus h 2 0).inv_mem (hΨH k hk)) hτk
    have hcomm : ∀ v ∈ hypUnitriangular h 2 0,
        (Ψ k)⁻¹ * ((τ ⟨k, hkB⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) * Ψ v =
          Ψ v * ((Ψ k)⁻¹ * ((τ ⟨k, hkB⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0)) := by
      intro v hv
      have hvB : v ∈ parP h ⊓ parP2 h := hypUnitriangular_le_inf_u4 h hv
      have hkv : k * v * k⁻¹ ∈ hypUnitriangular h 2 0 :=
        CFSG.RankThree.CentralLiftU.conj_mem_hypUnitriangular_of_mem_hypBorel (by norm_num)
          (hypTorus_le_hypBorel h hk) hv
      have hkvB : k * v * k⁻¹ ∈ parP h ⊓ parP2 h := hypUnitriangular_le_inf_u4 h hkv
      have h1 := (hS _ hkvB).mp (hUS hkv)
      have h2 := (hS _ hvB).mp (hUS hv)
      have h3 : ((τ ⟨k * v * k⁻¹, hkvB⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) =
          ((τ ⟨k, hkB⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) *
            ((τ ⟨v, hvB⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) *
            ((τ ⟨k, hkB⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0)⁻¹ := by
        have e : (⟨k * v * k⁻¹, hkvB⟩ : ↥(parP h ⊓ parP2 h)) =
            ⟨k, hkB⟩ * ⟨v, hvB⟩ * (⟨k, hkB⟩ : ↥(parP h ⊓ parP2 h))⁻¹ := rfl
        rw [e, map_mul, map_mul, map_inv]
        rfl
      rw [h1, h2, map_mul, map_mul, map_inv] at h3
      calc (Ψ k)⁻¹ * ((τ ⟨k, hkB⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) * Ψ v
          = (Ψ k)⁻¹ * (((τ ⟨k, hkB⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) * Ψ v *
              ((τ ⟨k, hkB⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0)⁻¹) *
              ((τ ⟨k, hkB⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) := by group
        _ = (Ψ k)⁻¹ * (Ψ k * Ψ v * (Ψ k)⁻¹) *
              ((τ ⟨k, hkB⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) := by rw [h3]
        _ = Ψ v * ((Ψ k)⁻¹ * ((τ ⟨k, hkB⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0)) := by group
    have hcomm' : ∀ w ∈ hypUnitriangular h 2 0,
        (Ψ k)⁻¹ * ((τ ⟨k, hkB⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) * w =
          w * ((Ψ k)⁻¹ * ((τ ⟨k, hkB⟩ : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0)) := by
      intro w hw
      have hv : Ψ.symm w ∈ hypUnitriangular h 2 0 := by
        rw [hΨU, MulEquiv.apply_symm_apply]
        exact hw
      have := hcomm _ hv
      rwa [MulEquiv.apply_symm_apply] at this
    obtain ⟨q, hq⟩ := exists_diag_of_mem_hypTorus_u4 h hcH
    have hc1 := eq_one_of_comm_u4Roots h hq
      (hcomm' _ (radQ_le_hypUnitriangular_u4 h (syElt_mem 1)))
      (hcomm' _ (u4xbElt_mem_hypUnitriangular h (map_one h.bar)))
    exact (inv_mul_eq_one.mp hc1).symm
  have hBS : parP h ⊓ parP2 h ≤ S := by
    rw [parP_inf_parP2_eq_u4 h]
    exact (CFSG.RankThree.CentralLiftU.hypBorel_le_sup (by norm_num) (by norm_num)).trans
      (sup_le hUS hHS)
  exact (hS b b.2).mp (hBS b.2)

end CFSG.Quasithin.F112R.St84

end
