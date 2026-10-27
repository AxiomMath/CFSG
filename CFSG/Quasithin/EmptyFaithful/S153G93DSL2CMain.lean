module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCases
public import CFSG.Quasithin.EmptyFaithful.S153G93DSL2CCore
public import CFSG.Quasithin.EmptyFaithful.S153G93DSL2CSylow

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace SL2C

open SBc17 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

theorem exists_inner_of_fixes_sylow [Finite F] [CharP F 2] {P : Subgroup (SL2 F)}
    (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index) (α : MulAut (SL2 F)) (hα : ∀ x ∈ P, α x = x) :
    ∃ p ∈ P, ∀ g : SL2 F, α g = p * g * p⁻¹ := by
  obtain ⟨x, hx⟩ := exists_conj_upperSub hP hidx
  let β : MulAut (SL2 F) := (MulAut.conj x).trans (α.trans (MulAut.conj x⁻¹))
  have hβapp : ∀ y : SL2 F, β y = x⁻¹ * α (x * y * x⁻¹) * x := by
    intro y
    simp [β, MulAut.conj_apply]
  have hmemP : ∀ u ∈ upperSub F, x * u * x⁻¹ ∈ P := by
    intro u hu
    rw [hx]
    have h : x⁻¹ * (x * u * x⁻¹) * x = u := by group
    rwa [h]
  have hβ : ∀ u ∈ upperSub F, β u = u := by
    intro u hu
    rw [hβapp, hα _ (hmemP u hu)]
    group
  obtain ⟨e, he⟩ := exists_conj_uElt_of_fixes_upperSub β hβ
  refine ⟨x * uElt e * x⁻¹, hmemP _ (mem_upperSub_iff.2 ⟨e, rfl⟩), fun g => ?_⟩
  have h1 := he (x⁻¹ * g * x)
  rw [hβapp, show x * (x⁻¹ * g * x) * x⁻¹ = g by group] at h1
  calc α g = x * (x⁻¹ * α g * x) * x⁻¹ := by group
    _ = x * (uElt e * (x⁻¹ * g * x) * (uElt e)⁻¹) * x⁻¹ := by rw [h1]
    _ = x * uElt e * x⁻¹ * g * (x * uElt e * x⁻¹)⁻¹ := by group

theorem sl2Cent_holds : SL2Cent := by
  intro F _ _ _ P hP α hα
  let e := specialLinearGroupEquivStatedSL 2 F
  have hPidx : ¬ 2 ∣ P.index := by
    have h := hP.2.2
    rwa [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right P] at h
  have hP'2 : IsPGroup 2 (P.comap e.toMonoidHom) :=
    hP.2.1.comap_of_injective e.toMonoidHom e.injective
  have hP'idx : ¬ 2 ∣ (P.comap e.toMonoidHom).index := by
    rwa [Subgroup.index_comap_of_surjective P (f := e.toMonoidHom) e.surjective]
  let α' : MulAut (SL2 F) := e.trans (α.trans e.symm)
  have hα' : ∀ x ∈ P.comap e.toMonoidHom, α' x = x := by
    intro x hx
    have hx' : e x ∈ P := hx
    show e.symm (α (e x)) = x
    rw [hα _ hx', MulEquiv.symm_apply_apply]
  obtain ⟨p', hp'P, hp'⟩ := exists_inner_of_fixes_sylow hP'2 hP'idx α' hα'
  refine ⟨e p', hp'P, fun g => ?_⟩
  obtain ⟨g', rfl⟩ := e.surjective g
  have h1 : α' g' = p' * g' * p'⁻¹ := hp' g'
  have h2 : α (e g') = e (α' g') := by
    show α (e g') = e (e.symm (α (e g')))
    rw [MulEquiv.apply_symm_apply]
  rw [h2, h1, map_mul, map_mul, map_inv]

end SL2C

end S153G93D

end CFSG.Quasithin
