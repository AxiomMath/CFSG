module

public import CFSG.LieType.SeitzGeneration.HyperOuterFieldAut
public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract

public section

open CFSG.LieType.SeitzGeneration CFSG.Open CFSG.RankThree.PartOne.CTP

namespace CFSG.RankThree.PartTwo.Sec4.E27

theorem fixPlaneGen_of_standard {P : Type} [Group P] {p : ℕ} (D : Subgroup (MulAut P))
    (S : Set (MulAut P))
    (hdesc : ∀ α : MulAut P, IsOuterOfOrder p α → ∃ d ∈ D, ∃ f ∈ S, α = d * f * d⁻¹)
    (hS : ∀ f ∈ S, ∀ A : Subgroup P, A ≤ fixedSubgroup f → IsElemAbelian p A →
      Nat.card A = p ^ 2 →
      fixedSubgroup f ≤ Subgroup.closure
        {k | k ∈ fixedSubgroup f ∧ ∃ b ∈ A, b ≠ 1 ∧ k * b = b * k}) :
    FixPlaneGen P p := by
  intro σ hσ A hA hAa hAc
  obtain ⟨d, -, f, hf, rfl⟩ := hdesc σ hσ
  have hF := fixedSubgroup_conj d f
  rw [hF] at hA ⊢
  set A' : Subgroup P := A.map d⁻¹.toMonoidHom with hA'
  have hA'f : A' ≤ fixedSubgroup f := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨y, hy, hya⟩ := hA ha
    have : d⁻¹ a = y := by rw [← hya]; simp
    simpa [this] using hy
  have hA'a : IsElemAbelian p A' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hAa _
  have hA'c : Nat.card A' = p ^ 2 := by
    rw [Subgroup.card_map_of_injective d⁻¹.injective, hAc]
  have h1 := hS f hf A' hA'f hA'a hA'c
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' := h1 hy
  have h2 : d y ∈ (Subgroup.closure
      {k | k ∈ fixedSubgroup f ∧ ∃ b ∈ A', b ≠ 1 ∧ k * b = b * k}).map d.toMonoidHom :=
    ⟨y, hy', rfl⟩
  rw [MonoidHom.map_closure] at h2
  refine (Subgroup.closure_mono ?_) h2
  rintro _ ⟨k, ⟨hk, b, hb, hb1, hkb⟩, rfl⟩
  obtain ⟨a, ha, rfl⟩ := hb
  refine ⟨⟨k, hk, rfl⟩, d (d⁻¹ a), by simpa using ha, ?_, ?_⟩
  · intro h
    apply hb1
    have : d⁻¹ a = 1 := d.injective (by simpa using h)
    simpa using this
  · have := congrArg d hkb
    simpa [map_mul] using this

end CFSG.RankThree.PartTwo.Sec4.E27
