module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmUClauses
public import CFSG.LocalAnalysis.StandardType.GGKacK0V2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggKacDatum_rZ_le_one
    {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X} {D : GGKacDatum}
    {R : Type} [Group R] {I : Set (MulAut R)} {ψ : X →* R}
    (hloc : GGTPNLocalCore p A σ J) (ha : GGTPNSelfCent p A) (hk : GGTPNKernel A σ J)
    (hZ : (Nat.card (Subgroup.center X)).Coprime p)
    (hE : 2 ≤ D.rZ → ∃ E : Subgroup X, IsElemAbelian p E ∧ Nat.card E = p ^ D.rZ ∧
      E ≤ ggFixSub σ ∧ (∀ z ∈ E, ∀ g ∈ ggFixSub σ, g * z = z * g) ∧
      ∀ A' : Subgroup (MulAut X), σ ∈ A' → IsElemAbelian p A' →
        (∀ a ∈ A', ∃ φ ∈ I, ∀ l : X, φ (ψ l) = ψ (a l)) →
          ∀ z ∈ E, ∀ a ∈ A', a z = z)
    (hInd : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : X, φ (ψ l) = ψ (a l)) :
    D.rZ ≤ 1 := by
  by_contra hle
  have hD2 : 2 ≤ D.rZ := by omega
  obtain ⟨E, hEelem, hEcard, -, hEcen, hEagree⟩ := hE hD2
  have hσp : σ ^ p = 1 := hloc.1.2 σ hloc.2.1
  have horder : orderOf σ = p := orderOf_eq_prime hσp hloc.2.2.1
  have hEp : ∀ z ∈ E, z ^ p = 1 := hEelem.2
  have hEA : ∀ z ∈ E, ∀ a ∈ A, a z = z := fun z hz a haA =>
    hEagree A hloc.2.1 hloc.1 hInd z hz a haA
  have hEJ : ∀ z ∈ E, ∀ j ∈ J, z * j = j * z := fun z hz j hj =>
    (hEcen z hz j (show j ∈ ggFixSub σ from (hloc.2.2.2.1).1 hj)).symm
  have hdvd := card_dvd_orderOf_of_ggTPNSelfCent_of_ggTPNKernel hZ ha hk hEp hEA hEJ
  rw [hEcard, horder] at hdvd
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have h2dvd : p ^ 2 ∣ p ^ D.rZ := (Nat.pow_dvd_pow_iff_le_right hp1).2 hD2
  have hle1 : 2 ≤ 1 :=
    (Nat.pow_dvd_pow_iff_le_right hp1).1 (by simpa using h2dvd.trans hdvd)
  omega

private theorem ggKacSigma_no_qs_false
    {p : ℕ} {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X} {D : GGKacDatum}
    {R : Type} [Group R] {I : Set (MulAut R)} {ψ : X →* R}
    (hσA : σ ∈ A) (hA : IsElemAbelian p A) (hJ : IsComponentOf J (ggAutFixedSubgroup σ))
    (hind : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : X, φ (ψ l) = ψ (a l))
    (ha : GGTPNSelfCent p A) (hk : GGTPNKernel A σ J)
    (hσ : GGKacSigmaClause p I D X ψ σ) :
    ∀ o ∈ D.orbits, o.qs = true := by
  intro o ho
  by_contra hqs
  have hfalse : o.qs = false := by
    cases hq : o.qs <;> simp_all
  obtain ⟨t, htp, hta, htc, hconj⟩ := hσ o ho hfalse A hσA hA hind
  have hmemA : MulAut.conj t ∈ A := ha t hta htp
  have htriv : ∀ j ∈ J, MulAut.conj t j = j := by
    intro j hj
    rw [MulAut.conj_apply, htc J hJ j hj]
    group
  exact hconj (hk (MulAut.conj t) hmemA htriv)

theorem ggKac_exists_single_orbit
    {X : Type} [Group X] {σ : MulAut X} {J : Subgroup X} {D : GGKacDatum}
    (hbij : GGKacCompBij D X σ)
    (hJ : IsComponentOf J (ggAutFixedSubgroup σ))
    (hC : ∀ J' : Subgroup X, IsComponentOf J' (ggAutFixedSubgroup σ) → J' = J)
    (hno : ∀ o ∈ D.orbits, o.qs = true) :
    ∃ o : GGKacOrbit, D.orbits = [o] ∧ o.qs = true := by
  obtain ⟨f, -⟩ := hbij
  have hcard_dom : Nat.card {J' : Subgroup X // IsComponentOf J' (ggFixSub σ)} = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨⟨J, hJ⟩, fun x =>
      Subtype.ext ((hC x.1 x.2).trans (hC J hJ).symm)⟩
  have hcard_cod : Nat.card {i : Fin D.orbits.length // D.orbits[i].qs = true} =
      D.orbits.length := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv
      (fun i => hno (D.orbits[i]) (List.get_mem D.orbits i))), Nat.card_fin]
  have hcard_cod1 : Nat.card {i : Fin D.orbits.length // D.orbits[i].qs = true} = 1 :=
    (Nat.card_congr f).symm.trans hcard_dom
  have hlen : D.orbits.length = 1 := by omega
  obtain ⟨o, ho⟩ := List.length_eq_one_iff.mp hlen
  exact ⟨o, ho, hno o (by rw [ho]; simp)⟩

theorem exists_ggKacDatum_of_ggK0MainBS
    {Gen : LargeEvenLabel → ℕ → Prop} {Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop}
    (hK0 : GGK0MainBS Gen Valid) (hS : GGK0Schur Gen)
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
        ∃ o : GGKacOrbit, D.orbits = [o] ∧ o.qs = true ∧ lab.n ∣ o.lab.n ∧
          LargeEvenInLambda2 o.lab ∧ GGHasLabel o.lab (↥J ⧸ Subgroup.center ↥J) := by
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
  obtain ⟨D, hValid, hcomp, hcomp', hpdvd, hE, hbij, hsigma⟩ :=
    hPk X ψ hψsurj hψker hcomm σ hσp (hIndOf σ hloc.2.1)
  have hrZ : D.rZ ≤ 1 :=
    ggKacDatum_rZ_le_one hloc ha hk (hPs X ψ hψsurj hψker hcomm) hE hIndOf
  have hC : ∀ J' : Subgroup X, IsComponentOf J' (ggAutFixedSubgroup σ) → J' = J := by
    intro J' hJ'
    exact eq_of_isComponentOf_of_ggTPNOnlyComp h8 hJ' (hpdvd J' hJ')
  have hno : ∀ o ∈ D.orbits, o.qs = true :=
    ggKacSigma_no_qs_false hloc.2.1 hloc.1 hloc.2.2.2.1 hIndOf ha hk hsigma
  obtain ⟨o, horbits, hqs⟩ :=
    ggKac_exists_single_orbit hbij hloc.2.2.2.1 hC hno
  obtain ⟨o', ho', -, hndvd, hΛ, hlabJ⟩ := hcomp J hloc.2.2.2.1
  have ho'eq : o' = o := by simpa [horbits] using ho'
  rw [ho'eq] at hndvd hΛ hlabJ
  exact ⟨lab, hlab, hSlab, hgenlab, hhas, D, hValid, hrZ, hC, o, horbits, hqs,
    hndvd, hΛ, hlabJ⟩

end CFSG.StandardType
