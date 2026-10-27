module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1U3Rank

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem card_elemAbelian_mulAut_of_equiv_U3 {X : Type} [Group X] {K : Type} [Field K]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ 1) ^ 2)
    (e : X ≃* StatedProj (StatedSU 3 (p ^ 1) K)) (B : Subgroup (MulAut X))
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h2 : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 ^ 3 := by
  have h : UnitaryFieldData p 1 K := ⟨Fact.out, le_rfl, by rw [hK]; ring⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  let ψ : X ≃* hypPSU h 1 1 := e.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm
  let B' : Subgroup (MulAut (hypPSU h 1 1)) := B.map (MulAut.congr ψ).toMonoidHom
  have hB' : ∀ x ∈ B', x * x = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    change MulAut.congr ψ b * MulAut.congr ψ b = 1
    rw [← map_mul, h2 b hb, map_one]
  have hB'c : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    change MulAut.congr ψ a * MulAut.congr ψ b = MulAut.congr ψ b * MulAut.congr ψ a
    rw [← map_mul, ← map_mul, hc a ha b hb]
  have : CFSG.IsElementaryAbelian 2 B' :=
    { is_comm := ⟨fun a b => Subtype.ext (hB'c a.1 a.2 b.1 b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
        apply Subtype.ext
        simpa [pow_two] using hB' a.1 a.2 }
  have h8 := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1.u3_elemAbelian_le_eight h hp2 B' this
  calc Nat.card B = Nat.card B' :=
        Nat.card_congr (Subgroup.equivMapOfInjective _ (MulAut.congr ψ).toMonoidHom
          (MulAut.congr ψ).injective).toEquiv
    _ ≤ 2 ^ 3 := h8

theorem card_elemAbelian_mulAut_of_model_U3 {X : Type} [Group X] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (h : StatedClassicalModel X .PSU 3 p 1) (B : Subgroup (MulAut X))
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h2 : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 ^ 3 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact card_elemAbelian_mulAut_of_equiv_U3 hp2 hK e B hc h2

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent
