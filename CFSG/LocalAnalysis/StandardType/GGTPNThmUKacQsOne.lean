module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmUKacV2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem exists_ggKacDatum_core
    {Gen : LargeEvenLabel → ℕ → Prop} {Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop}
    {p : ℕ} [Fact p.Prime] (hK0 : GGK0MainB Gen Valid) (hS : GGK0Schur Gen)
    {S : ℕ → LargeEvenLabel → Prop} {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore p A σ J) (h8 : GGTPNOnlyComp p σ J) (hm : GGTPNMarked p S A)
    (hgen : ∀ lab, LargeEvenInLambda2 lab → GGHasLabel lab (X ⧸ Subgroup.center X) →
      Gen lab p) :
    ∃ (R : Type) (_ : Group R) (I : Set (MulAut R)) (ψ : X →* R) (lab : LargeEvenLabel)
      (D : GGKacDatum),
      LargeEvenInLambda2 lab ∧ S p lab ∧ Gen lab p ∧
      GGHasLabel lab (X ⧸ Subgroup.center X) ∧
      (Nat.card (Subgroup.center X)).Coprime p ∧ Valid lab p D ∧
      (∀ J' : Subgroup X, IsComponentOf J' (ggAutFixedSubgroup σ) → J' = J) ∧
      (2 ≤ D.rZ → ∃ E : Subgroup X, IsElemAbelian p E ∧ Nat.card E = p ^ D.rZ ∧
        E ≤ ggFixSub σ ∧ (∀ z ∈ E, ∀ g ∈ ggFixSub σ, g * z = z * g) ∧
        ∀ A' : Subgroup (MulAut X), σ ∈ A' → IsElemAbelian p A' →
          (∀ a ∈ A', ∃ φ ∈ I, ∀ l : X, φ (ψ l) = ψ (a l)) →
            ∀ z ∈ E, ∀ a ∈ A', a z = z) ∧
      GGKacCompBij D X σ ∧
      (∃ o : GGKacOrbit, o ∈ D.orbits ∧ o.qs = true ∧ lab.n ∣ o.lab.n ∧
        LargeEvenInLambda2 o.lab ∧ GGHasLabel o.lab (↥J ⧸ Subgroup.center ↥J)) := by
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
  obtain ⟨D, hValid, hcomp, -, hpdvd, hE, hbij⟩ :=
    hPk X ψ hψsurj hψker hcomm σ hσp (hIndOf σ hloc.2.1)
  have hC : ∀ J' : Subgroup X, IsComponentOf J' (ggAutFixedSubgroup σ) → J' = J := by
    intro J' hJ'
    exact eq_of_isComponentOf_of_ggTPNOnlyComp h8 hJ' (hpdvd J' hJ')
  obtain ⟨o', ho', hqs', hndvd, hΛ, hlabJ⟩ := hcomp J hloc.2.2.2.1
  exact ⟨R, hR, I, ψ, lab, D, hlab, hSlab, hgenlab, hhas,
    hPs X ψ hψsurj hψker hcomm, hValid, hC, hE, hbij, o', ho', hqs', hndvd, hΛ, hlabJ⟩

private theorem eqs_exists_unique_qs_orbit
    {X : Type} [Group X] {σ : MulAut X} {J : Subgroup X} {D : GGKacDatum}
    (hbij : GGKacCompBij D X σ)
    (hJ : IsComponentOf J (ggAutFixedSubgroup σ))
    (hC : ∀ J' : Subgroup X, IsComponentOf J' (ggAutFixedSubgroup σ) → J' = J) :
    ∃ o : GGKacOrbit, o ∈ D.orbits ∧ o.qs = true ∧
      (∀ o' ∈ D.orbits, o'.qs = true → o' = o) := by
  obtain ⟨f, -⟩ := hbij
  have hcard_dom : Nat.card {J' : Subgroup X // IsComponentOf J' (ggFixSub σ)} = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨⟨J, hJ⟩, fun x =>
      Subtype.ext ((hC x.1 x.2).trans (hC J hJ).symm)⟩
  have hcard_cod : Nat.card {i : Fin D.orbits.length // D.orbits[i].qs = true} = 1 :=
    (Nat.card_congr f).symm.trans hcard_dom
  obtain ⟨x₀, hx₀⟩ := Nat.card_eq_one_iff_exists.mp hcard_cod
  refine ⟨D.orbits[x₀.1], List.get_mem _ _, x₀.2, ?_⟩
  intro o' ho' hqs'
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ho'
  have hqi : (D.orbits.get i).qs = true := hi ▸ hqs'
  have hix : (⟨i, hqi⟩ : {i : Fin D.orbits.length // D.orbits[i].qs = true}) = x₀ :=
    hx₀ ⟨i, hqi⟩
  rw [← hi]
  exact congrArg (fun j => D.orbits.get j) (congrArg Subtype.val hix)

theorem exists_ggKacDatum_of_ggK0MainB_qsOne
    {Gen : LargeEvenLabel → ℕ → Prop} {Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop}
    {p : ℕ} [Fact p.Prime] (hK0 : GGK0MainB Gen Valid) (hS : GGK0Schur Gen)
    {S : ℕ → LargeEvenLabel → Prop} {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore p A σ J) (h8 : GGTPNOnlyComp p σ J) (hm : GGTPNMarked p S A)
    (hgen : ∀ lab, LargeEvenInLambda2 lab → GGHasLabel lab (X ⧸ Subgroup.center X) →
      Gen lab p) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ S p lab ∧ Gen lab p ∧
      GGHasLabel lab (X ⧸ Subgroup.center X) ∧ (Nat.card (Subgroup.center X)).Coprime p ∧
      ∃ D : GGKacDatum, Valid lab p D ∧
        (∀ J' : Subgroup X, IsComponentOf J' (ggAutFixedSubgroup σ) → J' = J) ∧
        ∃ o : GGKacOrbit, o ∈ D.orbits ∧ o.qs = true ∧
          (∀ o' ∈ D.orbits, o'.qs = true → o' = o) ∧ lab.n ∣ o.lab.n ∧
          LargeEvenInLambda2 o.lab ∧ GGHasLabel o.lab (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨R, hR, I, ψ, lab, D, hrest⟩ :=
    exists_ggKacDatum_core hK0 hS hloc h8 hm hgen
  letI := hR
  obtain ⟨hlab, hSlab, hgenlab, hhas, hZ, hValid, hC, -, hbij, hrest⟩ := hrest
  obtain ⟨o', ho', hqs', hndvd, hΛ, hlabJ⟩ := hrest
  obtain ⟨o, horbits, hqs, huniq⟩ := eqs_exists_unique_qs_orbit hbij hloc.2.2.2.1 hC
  have ho'eq : o' = o := huniq o' ho' hqs'
  rw [ho'eq] at hndvd hΛ hlabJ
  exact ⟨lab, hlab, hSlab, hgenlab, hhas, hZ, D, hValid, hC, o, horbits, hqs,
    huniq, hndvd, hΛ, hlabJ⟩

end CFSG.StandardType

end
