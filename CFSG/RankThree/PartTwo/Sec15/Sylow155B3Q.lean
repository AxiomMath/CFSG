module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Six

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155B3Q

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
open CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

section Action

variable {Q : Type*} [Group Q]

@[expose] noncomputable def rhoQ (ψ6 : Q ⧸ Subgroup.center Q ≃* ↥A6Models.psl29) :
    MulAut Q →* ↥A6Models.autA6 :=
  conjEquiv6.symm.toMonoidHom.comp ((MulAut.congr ψ6).toMonoidHom.comp quotAutOfCentreHom)

theorem conjEquiv6_rhoQ (ψ6 : Q ⧸ Subgroup.center Q ≃* ↥A6Models.psl29) (σ : MulAut Q) :
    conjEquiv6 (rhoQ ψ6 σ) = MulAut.congr ψ6 (quotAutOfCentre σ) :=
  conjEquiv6.apply_symm_apply _

theorem rhoQ_spec (ψ6 : Q ⧸ Subgroup.center Q ≃* ↥A6Models.psl29) (σ : MulAut Q) (q : Q) :
    ((ψ6 (QuotientGroup.mk (σ q)) : ↥A6Models.psl29) : Equiv.Perm (Fin 10)) =
      (rhoQ ψ6 σ : Equiv.Perm (Fin 10)) * (ψ6 (QuotientGroup.mk q) : Equiv.Perm (Fin 10)) *
        (rhoQ ψ6 σ : Equiv.Perm (Fin 10))⁻¹ := by
  rw [← conjEquiv6_apply, conjEquiv6_rhoQ]
  simp [quotAutOfCentre_mk]

theorem rhoQ_conj (ψ6 : Q ⧸ Subgroup.center Q ≃* ↥A6Models.psl29) (q : Q) :
    (rhoQ ψ6 (MulAut.conj q) : Equiv.Perm (Fin 10)) =
      (ψ6 (QuotientGroup.mk q) : Equiv.Perm (Fin 10)) := by
  have h : rhoQ ψ6 (MulAut.conj q) =
      ⟨(ψ6 (QuotientGroup.mk q) : Equiv.Perm (Fin 10)),
        psl29_le_autA6 (ψ6 (QuotientGroup.mk q)).2⟩ := by
    refine conjEquiv6.injective (MulEquiv.ext fun x => Subtype.ext ?_)
    obtain ⟨y, rfl⟩ := ψ6.surjective x
    induction y using QuotientGroup.induction_on with
    | H _ =>
      rw [conjEquiv6_rhoQ, conjEquiv6_apply]
      simp [quotAutOfCentre_mk]
  exact congrArg Subtype.val h

theorem rhoQ_eq_one_iff (hperf : commutator Q = ⊤)
    (ψ6 : Q ⧸ Subgroup.center Q ≃* ↥A6Models.psl29) (σ : MulAut Q) :
    rhoQ ψ6 σ = 1 ↔ σ = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_one]⟩
  have h2 : quotAutOfCentre σ = 1 := by
    refine (MulAut.congr ψ6).injective ?_
    rw [← conjEquiv6_rhoQ, h, map_one, map_one]
  refine eq_one_of_forall_mk_eq_aut hperf σ fun x => ?_
  have h3 := congrArg (fun τ : MulAut (Q ⧸ Subgroup.center Q) => τ (QuotientGroup.mk x)) h2
  simpa [quotAutOfCentre_mk] using h3

theorem rhoQ_injective (hperf : commutator Q = ⊤)
    (ψ6 : Q ⧸ Subgroup.center Q ≃* ↥A6Models.psl29) : Function.Injective (rhoQ ψ6) :=
  (injective_iff_map_eq_one _).2 fun σ h => (rhoQ_eq_one_iff hperf ψ6 σ).1 h

end Action

section Three

variable {Q : Type} [Group Q]

theorem pow_three_eq_one_of_conj_inv (hZ : Nat.card (Subgroup.center Q) = 3) {q g : Q}
    (hq3 : q ^ 3 ∈ Subgroup.center Q) (hg : g * q * g⁻¹ * q ∈ Subgroup.center Q) : q ^ 3 = 1 := by
  have hgz : g * q ^ 3 * g⁻¹ = q ^ 3 := by
    rw [(Subgroup.mem_center_iff.1 hq3 g), mul_inv_cancel_right]
  have hcomm : Commute (g * q * g⁻¹ * q) q⁻¹ := (Subgroup.mem_center_iff.1 hg q⁻¹).symm
  have hconj : g * q * g⁻¹ = (g * q * g⁻¹ * q) * q⁻¹ := by group
  have hinv : q ^ 3 = (q ^ 3)⁻¹ := by
    calc q ^ 3 = g * q ^ 3 * g⁻¹ := hgz.symm
      _ = (g * q * g⁻¹) ^ 3 := conj_pow.symm
      _ = ((g * q * g⁻¹ * q) * q⁻¹) ^ 3 := by rw [← hconj]
      _ = (g * q * g⁻¹ * q) ^ 3 * (q⁻¹) ^ 3 := hcomm.mul_pow 3
      _ = (q ^ 3)⁻¹ := by rw [pow_three_of_mem_center hZ hg, one_mul, inv_pow]
  have hsq : q ^ 3 * q ^ 3 = 1 := mul_eq_one_iff_eq_inv.2 hinv
  calc q ^ 3 = (q ^ 3) ^ 3 * (q ^ 3 * q ^ 3)⁻¹ := by group
    _ = 1 := by rw [pow_three_of_mem_center hZ hq3, hsq]; simp

end Three

end CFSG.RankThree.PartTwo.Sec15.Sylow155B3Q
