module

public import CFSG.RankThree.GF2n.Stroth80.Sec7SingularVectors

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sec7_exists_singular_of_card {K ι : Type*} [Field K] [Finite K] [Fintype ι]
    (Q' : QuadraticForm K (ι → K)) (S : Set (ι → K)) (h0 : (0 : ι → K) ∈ S)
    (hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) (hsmul : ∀ (c : K) (a : ι → K), a ∈ S → c • a ∈ S)
    (hcard : Nat.card K ^ 3 < Nat.card S) : ∃ u ∈ S, u ≠ 0 ∧ Q' u = 0 := by
  let D0 : Submodule K (ι → K) :=
    { carrier := S
      add_mem' := fun {a b} ha hb => hadd a ha b hb
      zero_mem' := h0
      smul_mem' := fun c {a} ha => hsmul c a ha }
  have hSD0 : Nat.card S = Nat.card D0 := rfl
  have hdim : Nat.card D0 = Nat.card K ^ Module.finrank K D0 := Module.natCard_eq_pow_finrank
  have hK : 1 < Nat.card K := Finite.one_lt_card
  have h3 : 3 ≤ Module.finrank K D0 := by
    by_contra hlt
    push Not at hlt
    have hpow : Nat.card K ^ Module.finrank K D0 ≤ Nat.card K ^ 3 :=
      Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hlt)
    rw [hSD0, hdim] at hcard
    exact absurd hcard (not_lt.mpr hpow)
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank h3
  have hg : LinearIndependent K (fun i => (f i : ι → K)) :=
    hf.map' D0.subtype (Submodule.ker_subtype D0)
  have hrank : Module.finrank K (Submodule.span K (Set.range fun i => (f i : ι → K))) = 3 := by
    rw [finrank_span_eq_card hg, Fintype.card_fin]
  have hle : Submodule.span K (Set.range fun i => (f i : ι → K)) ≤ D0 := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (f i).2
  obtain ⟨p, hpD, hp0, hQp⟩ :=
    sec7_exists_singular_of_finrank_three Q' (Submodule.span K (Set.range fun i => (f i : ι → K)))
      hrank
  exact ⟨p, hle hpD, hp0, hQp⟩

end CFSG.RankThree.GF2n.Stroth80
