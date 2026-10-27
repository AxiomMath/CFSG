module

public import CFSG.Quasithin.Background.SmithB45HatA6Out

public section

namespace CFSG.Quasithin.H13.A6.Hat6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Setup.X3Aut
  CFSG.QuasithinUnique.A6Facts.Core CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.Quasithin.B45HatA6

theorem exists_inner_of_invol {Q : Type*} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (hZ : Nat.card (Subgroup.center Q) = 3)
    (φ : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) (α : MulAut Q)
    (hα2 : α * α = 1) (hαZ : ∀ c ∈ Subgroup.center Q, α c = c) :
    ∃ g : alternatingGroup (Fin 6), ∀ q : Q,
      φ (QuotientGroup.mk (α q)) = g * φ (QuotientGroup.mk q) * g⁻¹ := by
  classical
  obtain ⟨psi, -⟩ := DoubleA3.exists_psl_equiv
  set eQ : Q ⧸ Subgroup.center Q ≃* ↥A6Models.psl29 := φ.trans psi.symm with heQ
  set τ : MulAut ↥A6Models.psl29 := MulAut.congr eQ (centerQuotientHom Q α) with hτ
  have hτmk : ∀ q : Q, τ (eQ (QuotientGroup.mk q)) = eQ (QuotientGroup.mk (α q)) := by
    intro q
    show eQ (centerQuotientHom Q α (eQ.symm (eQ (QuotientGroup.mk q)))) = _
    rw [MulEquiv.symm_apply_apply]
    exact congrArg eQ (onCenterQuotient_apply_mk α q)
  obtain ⟨b, hb⟩ := DoubleA3.conjAut_surjective τ
  have hb2 : b * b = 1 := by
    apply DoubleA3.conjAut_injective
    rw [conjAut_mul, hb, conjAut_one, hτ, ← map_mul, ← map_mul, hα2, map_one, map_one]
  by_cases hbP : (b : P10) ∈ A6Models.psl29
  ·
    refine ⟨psi ⟨b, hbP⟩, fun q => ?_⟩
    have h1 : eQ (QuotientGroup.mk (α q)) =
        (⟨b, hbP⟩ : ↥A6Models.psl29) * eQ (QuotientGroup.mk q) *
          (⟨b, hbP⟩ : ↥A6Models.psl29)⁻¹ := by
      rw [← hτmk, ← hb, conjAut_of_mem hbP]
      rfl
    have h2 : φ (QuotientGroup.mk (α q)) = psi (eQ (QuotientGroup.mk (α q))) := by
      rw [heQ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have h3 : φ (QuotientGroup.mk q) = psi (eQ (QuotientGroup.mk q)) := by
      rw [heQ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [h2, h1, map_mul, map_mul, map_inv, ← h3]
  ·
    exfalso
    obtain ⟨s, hs, p, q, r, t, hx, hy, hdet⟩ := exists_det_witness b hb2 hbP
    obtain ⟨l, hl⟩ : ∃ l : Q, eQ (QuotientGroup.mk l) = ⟨s, hs⟩ := by
      obtain ⟨y, hy⟩ := eQ.surjective ⟨s, hs⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨l, hy⟩
    let π : Q →* ↥A6Models.psl29 := eQ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
    have hπ : Function.Surjective π := eQ.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = Subgroup.center Q := by
      ext x
      rw [MonoidHom.mem_ker]
      show eQ (QuotientGroup.mk x) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    let α' : MulAut Q := α * MulAut.conj l
    have hαβ : ∀ e, π (α' e) = DoubleA3.conjAut (b * s) (π e) := by
      intro e
      show eQ (QuotientGroup.mk (α (l * e * l⁻¹))) =
        DoubleA3.conjAut (b * s) (eQ (QuotientGroup.mk e))
      rw [← hτmk, ← hb, conjAut_mul, MulAut.mul_apply]
      congr 1
      rw [conjAut_of_mem hs, MulAut.conj_apply, ← hl]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
    have hαC : ∀ c ∈ π.ker, α' c = c := by
      intro c hc
      rw [hker] at hc
      show α (l * c * l⁻¹) = c
      have hlc : l * c * l⁻¹ = c := by
        rw [Subgroup.mem_center_iff.mp hc l]
        group
      rw [hlc, hαZ c hc]
    obtain ⟨Cp⟩ : Nonempty (Sylow 3 π.ker) := inferInstance
    have hbot := SectionRank.sylow_kernel_eq_bot_of_det π hπ hker.le sylowQ9
      (coe_sylowQ9 ▸ isElemAbelian_Q9) α' (DoubleA3.conjAut (b * s)) hαβ hαC
      (closure_xy_eq.trans coe_sylowQ9.symm) hx hy hdet Cp
    have hk3 : Nat.card π.ker = 3 := by rw [hker, hZ]
    have hCp := Sylow.card_eq_multiplicity Cp
    rw [hk3, hbot, Subgroup.card_bot, Nat.Prime.factorization_self Nat.prime_three] at hCp
    norm_num at hCp

end CFSG.Quasithin.H13.A6.Hat6
