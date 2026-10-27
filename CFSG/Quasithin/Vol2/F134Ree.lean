module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.F134

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem three_dvd_card_of_twistedF4
    {X : Type} [Group X] {n : ℕ}
    (h : ReeTitsModel X .twistedF4 2 n) : 3 ∣ Nat.card X := by
  obtain ⟨a, K, _, _, _, -, hn, -, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model h
  have : Finite (CFSG.Blueprint.Chevalley.ModGL CFSG.LieType.Ree.ReeTag.F4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hidx : ¬ 2 ∣ ((S : Subgroup X).subgroupOf ⊤).index := by
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup X) ⊤ := ⟨le_top, S.isPGroup', hidx⟩
  obtain ⟨-, -, -, hcov⟩ := CFSG.QuasithinUnique.Setup.X6.large_Ree_model_two_extensions h
  obtain ⟨P₁, -, -, -, -, -, h1, -⟩ := hcov S hS
  have hdvd : 2 ^ n + 1 ∣ Nat.card X := by
    rw [← h1]
    exact (Subgroup.relIndex_dvd_card _ _).trans (Subgroup.card_dvd_of_le le_top) |>.trans
      (Subgroup.card_top (G := X)).dvd
  refine (Nat.dvd_of_mod_eq_zero ?_).trans hdvd
  subst hn
  rw [Nat.add_mod, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

end CFSG.Quasithin.F134
