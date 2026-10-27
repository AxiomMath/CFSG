module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmUKacQsOne
public import CFSG.LocalAnalysis.StandardType.GGA2EightDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem eux_rZ_le_one_of_centJ
    {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X} {D : GGKacDatum}
    {R : Type} [Group R] {I : Set (MulAut R)} {ψ : X →* R}
    (hloc : GGTPNLocalCore p A σ J) (hcent : GGCentJRank p X J)
    (hZ : (Nat.card (Subgroup.center X)).Coprime p)
    (hE : 2 ≤ D.rZ → ∃ E : Subgroup X, IsElemAbelian p E ∧ Nat.card E = p ^ D.rZ ∧
      E ≤ ggFixSub σ ∧ (∀ z ∈ E, ∀ g ∈ ggFixSub σ, g * z = z * g) ∧
      ∀ A' : Subgroup (MulAut X), σ ∈ A' → IsElemAbelian p A' →
        (∀ a ∈ A', ∃ φ ∈ I, ∀ l : X, φ (ψ l) = ψ (a l)) →
          ∀ z ∈ E, ∀ a ∈ A', a z = z) :
    D.rZ ≤ 1 := by
  by_contra hle
  have hD2 : 2 ≤ D.rZ := by omega
  obtain ⟨E, hEelem, hEcard, -, hEcen, -⟩ := hE hD2
  have hEJ : ∀ z ∈ E, ∀ j ∈ J, z * j = j * z := fun z hz j hj =>
    (hEcen z hz j (show j ∈ ggFixSub σ from (hloc.2.2.2.1).1 hj)).symm
  have hcardle : Nat.card E ≤ p := hcent hZ E hEelem hEJ
  rw [hEcard] at hcardle
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hp2 : p ^ 2 ≤ p := le_trans (Nat.pow_le_pow_right hp1.le hD2) hcardle
  have hmul : p * p ≤ p * 1 := by simpa [pow_two] using hp2
  have hp_le_one : p ≤ 1 :=
    Nat.le_of_mul_le_mul_left hmul (Nat.Prime.pos (Fact.out : p.Prime))
  omega

theorem exists_ggKacDatum_of_ggK0MainB_centJ
    {Gen : LargeEvenLabel → ℕ → Prop} {Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop}
    {p : ℕ} [Fact p.Prime] (hK0 : GGK0MainB Gen Valid) (hS : GGK0Schur Gen)
    (hqs : ∀ (lab : LargeEvenLabel) (D : GGKacDatum), LargeEvenInLambda2 lab → Gen lab p →
      Valid lab p D → ∀ o ∈ D.orbits, o.qs = true)
    {S : ℕ → LargeEvenLabel → Prop} {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore p A σ J) (hcent : GGCentJRank p X J)
    (h8 : GGTPNOnlyComp p σ J) (hm : GGTPNMarked p S A)
    (hgen : ∀ lab, LargeEvenInLambda2 lab → GGHasLabel lab (X ⧸ Subgroup.center X) →
      Gen lab p) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ S p lab ∧ Gen lab p ∧
      GGHasLabel lab (X ⧸ Subgroup.center X) ∧
      ∃ D : GGKacDatum, Valid lab p D ∧ D.rZ ≤ 1 ∧
        (∀ J' : Subgroup X, IsComponentOf J' (ggAutFixedSubgroup σ) → J' = J) ∧
        ∃ o : GGKacOrbit, D.orbits = [o] ∧ o.qs = true ∧ lab.n ∣ o.lab.n ∧
          LargeEvenInLambda2 o.lab ∧ GGHasLabel o.lab (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨R, hR, I, ψ, lab, D, hrest⟩ :=
    exists_ggKacDatum_core hK0 hS hloc h8 hm hgen
  letI := hR
  obtain ⟨hlab, hSlab, hgenlab, hhas, hZ, hValid, hC, hE, hbij, hrest⟩ := hrest
  obtain ⟨o', ho', hqs', hndvd, hΛ, hlabJ⟩ := hrest
  have hrZ : D.rZ ≤ 1 := eux_rZ_le_one_of_centJ hloc hcent hZ hE
  have hno : ∀ o ∈ D.orbits, o.qs = true := hqs lab D hlab hgenlab hValid
  obtain ⟨o, horbits, hqs⟩ :=
    ggKac_exists_single_orbit hbij hloc.2.2.2.1 hC hno
  have ho'eq : o' = o := by simpa [horbits] using ho'
  rw [ho'eq] at hndvd hΛ hlabJ
  exact ⟨lab, hlab, hSlab, hgenlab, hhas, D, hValid, hrZ, hC, o, horbits, hqs,
    hndvd, hΛ, hlabJ⟩

end CFSG.StandardType

end
