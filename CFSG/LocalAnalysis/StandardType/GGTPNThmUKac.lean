module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmUClauses
public import CFSG.LocalAnalysis.StandardType.GGKacK0

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggKacDatum_rZ_le_one {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {σ : MulAut X} {J E : Subgroup X} {D : GGKacDatum}
    (hA : IsElemAbelian p A) (hσA : σ ∈ A) (hσne : σ ≠ 1)
    (ha : GGTPNSelfCent p A) (hk : GGTPNKernel A σ J)
    (hZ : (Nat.card (Subgroup.center X)).Coprime p)
    (hEp : ∀ z ∈ E, z ^ p = 1) (hEA : ∀ z ∈ E, ∀ a ∈ A, a z = z)
    (hEJ : ∀ z ∈ E, ∀ j ∈ J, z * j = j * z)
    (hcardE : Nat.card E = p ^ D.rZ) (hD2 : 2 ≤ D.rZ) : D.rZ ≤ 1 := by
  have hσp : σ ^ p = 1 := hA.2 σ hσA
  have horder : orderOf σ = p := orderOf_eq_prime hσp hσne
  have hdvdE : Nat.card E ∣ orderOf σ :=
    card_dvd_orderOf_of_ggTPNSelfCent_of_ggTPNKernel hZ ha hk hEp hEA hEJ
  rw [hcardE, horder] at hdvdE
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have h2dvd : p ^ 2 ∣ p ^ D.rZ := (Nat.pow_dvd_pow_iff_le_right hp1).2 hD2
  have hle : 2 ≤ 1 :=
    (Nat.pow_dvd_pow_iff_le_right hp1).1 (by simpa using h2dvd.trans hdvdE)
  omega

private theorem ggKacDatum_onlyComp_and_label
    {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    {σ : MulAut X} {J : Subgroup X} {D : GGKacDatum}
    (h8 : GGTPNOnlyComp p σ J)
    (hpdvd : ∀ J' : Subgroup X, IsComponentOf J' (ggFixSub σ) → p ∣ Nat.card J')
    (hcomp' : ∀ o ∈ D.orbits, o.qs = true → ∃ J' : Subgroup X,
      IsComponentOf J' (ggFixSub σ) ∧ GGHasLabel o.lab (↥J' ⧸ Subgroup.center ↥J')) :
    (∀ J' : Subgroup X, IsComponentOf J' (ggAutFixedSubgroup σ) → J' = J) ∧
      ∀ o ∈ D.orbits, o.qs = true → GGHasLabel o.lab (↥J ⧸ Subgroup.center ↥J) := by
  have hC : ∀ J' : Subgroup X, IsComponentOf J' (ggAutFixedSubgroup σ) → J' = J := by
    intro J' hJ'
    exact eq_of_isComponentOf_of_ggTPNOnlyComp h8 hJ' (hpdvd J' hJ')
  refine ⟨hC, ?_⟩
  intro o ho hqs
  obtain ⟨J', hJ', hhasJ⟩ := hcomp' o ho hqs
  rw [hC J' hJ'] at hhasJ
  exact hhasJ

theorem exists_ggKacDatum_of_ggK0Main
    {Gen : LargeEvenLabel → ℕ → Prop} {Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop}
    (hK0 : GGK0Main Gen Valid) (hS : GGK0Schur Gen)
    {p : ℕ} [Fact p.Prime] {S : ℕ → LargeEvenLabel → Prop} {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore p A σ J) (ha : GGTPNSelfCent p A) (hk : GGTPNKernel A σ J)
    (h8 : GGTPNOnlyComp p σ J) (hm : GGTPNMarked p S A)
    (hgen : ∀ lab, LargeEvenInLambda2 lab → GGHasLabel lab (X ⧸ Subgroup.center X) →
      Gen lab p) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ S p lab ∧ Gen lab p ∧
      GGHasLabel lab (X ⧸ Subgroup.center X) ∧
      ∃ D : GGKacDatum, Valid lab p D ∧ D.rZ ≤ 1 ∧
        (∀ J' : Subgroup X, IsComponentOf J' (ggAutFixedSubgroup σ) → J' = J) ∧
        (∀ o ∈ D.orbits, o.qs = true → GGHasLabel o.lab (↥J ⧸ Subgroup.center ↥J)) ∧
        ∃ o ∈ D.orbits, o.qs = true ∧ lab.n ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab := by
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hm
  have hhas : GGHasLabel lab (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hraw
  have hgenlab : Gen lab p := hgen lab hlab hhas
  have hraw' := largeEvenLabelAll_and (hK0 p lab hlab hgenlab) (hS p lab hlab hgenlab) _ hraw
  obtain ⟨R, hR, I, F, hP⟩ := largeEvenRawDatum_exists hraw'
  letI := hR
  obtain ⟨hQ, hPk, hPs⟩ := hP
  obtain ⟨-, -, θ, hSlab, -, hind⟩ := hQ
  let ψ : X →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψsurj : Function.Surjective ψ := by
    change Function.Surjective
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)))
    exact θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker ≤ Subgroup.center X := by
    change (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))).ker ≤
      Subgroup.center X
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center X)) θ.toMonoidHom
      θ.injective, QuotientGroup.ker_mk']
  have hσp : σ ^ p = 1 := hloc.1.2 σ hloc.2.1
  have hIndOf : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : X, φ (ψ l) = ψ (a l) := by
    intro a ha
    exact ⟨ggInducedAut θ a, hind a ha, fun l => by
      simpa [ψ, QuotientGroup.mk'_apply] using ggInducedAut_apply θ a l⟩
  have hInd : ∃ φ ∈ I, ∀ l : X, φ (ψ l) = ψ (σ l) := hIndOf σ hloc.2.1
  obtain ⟨D, hValid, hcomp, hcomp', hpdvd, hE⟩ :=
    hPk X ψ hψsurj hψker hcomm σ hσp hInd
  have hrZ : D.rZ ≤ 1 := by
    by_contra hle
    have hD2 : 2 ≤ D.rZ := by omega
    obtain ⟨E, hEelem, hEcard, -, hEcen, hEagree⟩ := hE hD2
    have hEp : ∀ z ∈ E, z ^ p = 1 := hEelem.2
    have hEA : ∀ z ∈ E, ∀ a ∈ A, a z = z := by
      intro z hz a ha
      exact hEagree A hloc.2.1 hloc.1 hIndOf z hz a ha
    have hEJ : ∀ z ∈ E, ∀ j ∈ J, z * j = j * z := by
      intro z hz j hj
      exact (hEcen z hz j (show j ∈ ggFixSub σ from (hloc.2.2.2.1).1 hj)).symm
    have hZ : (Nat.card (Subgroup.center X)).Coprime p := hPs X ψ hψsurj hψker hcomm
    have hle1 : D.rZ ≤ 1 :=
      ggKacDatum_rZ_le_one hloc.1 hloc.2.1 hloc.2.2.1 ha hk hZ hEp hEA hEJ hEcard hD2
    omega
  obtain ⟨hC, hlabJ⟩ := ggKacDatum_onlyComp_and_label h8 hpdvd hcomp'
  have hlast : ∃ o ∈ D.orbits, o.qs = true ∧ lab.n ∣ o.lab.n ∧
      LargeEvenInLambda2 o.lab := by
    obtain ⟨o, ho, hqs, hndvd, hΛ, -⟩ := hcomp J hloc.2.2.2.1
    exact ⟨o, ho, hqs, hndvd, hΛ⟩
  exact ⟨lab, hlab, hSlab, hgenlab, hhas, D, hValid, hrZ, hC, hlabJ, hlast⟩

end CFSG.StandardType
