module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVPComp
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem card_dvd_orderOf_of_ggTPNSelfCent_of_ggTPNKernel {p : ℕ} {X : Type*} [Group X]
    [Finite X] {A : Subgroup (MulAut X)} {σ : MulAut X} {J E : Subgroup X}
    (hZ : (Nat.card (Subgroup.center X)).Coprime p) (ha : GGTPNSelfCent p A)
    (hk : GGTPNKernel A σ J) (hEp : ∀ z ∈ E, z ^ p = 1) (hEA : ∀ z ∈ E, ∀ a ∈ A, a z = z)
    (hEJ : ∀ z ∈ E, ∀ j ∈ J, z * j = j * z) :
    Nat.card E ∣ orderOf σ := by
  have hmem : ∀ z : E, MulAut.conj (z : X) ∈ Subgroup.zpowers σ := by
    intro z
    refine hk (MulAut.conj (z : X))
      (ha (z : X) (fun a haA => hEA z z.2 a haA) (hEp z z.2)) ?_
    intro j hj
    rw [MulAut.conj_apply, hEJ z z.2 j hj]
    group
  let f : E →* Subgroup.zpowers σ :=
    (MulAut.conj.comp E.subtype).codRestrict (Subgroup.zpowers σ) hmem
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro z hz
    apply Subtype.ext
    have hconj : MulAut.conj (z : X) = 1 := congrArg Subtype.val hz
    have hcenter : (z : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h' := congrArg (fun e : MulAut X => e g) hconj
      simp only [MulAut.conj_apply, MulAut.one_apply] at h'
      calc g * (z : X) = ((z : X) * g * (z : X)⁻¹) * (z : X) := by rw [h']
        _ = (z : X) * g := by group
    have h1 : orderOf (z : X) ∣ Nat.card (Subgroup.center X) :=
      Subgroup.orderOf_dvd_natCard _ hcenter
    have h2 : orderOf (z : X) ∣ p := orderOf_dvd_of_pow_eq_one (hEp z z.2)
    have h3 : orderOf (z : X) ∣ Nat.gcd (Nat.card (Subgroup.center X)) p :=
      Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hZ] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hdvd := Subgroup.card_dvd_of_injective f hf_inj
  rwa [Nat.card_zpowers] at hdvd

theorem eq_of_isComponentOf_of_ggTPNOnlyComp {p : ℕ} [Fact p.Prime] {X : Type} [Group X]
    [Finite X] {σ : MulAut X} {J J' : Subgroup X} (h8 : GGTPNOnlyComp p σ J)
    (hJ' : IsComponentOf J' (ggAutFixedSubgroup σ)) (hp : p ∣ Nat.card J') : J' = J := by
  refine h8 J' ((ggLargeEvenPComponent_iff p (ggAutFixedSubgroup σ) J').mpr
    ⟨hJ'.1, ?_⟩)
  exact (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p
    (ggAutFixedSubgroup σ) J' hJ'.1).mpr
    (lBalanceIsPComponent_of_isComponentOf hJ' (not_le_lBalancePrimeCore_of_dvd hp))

end CFSG.StandardType
