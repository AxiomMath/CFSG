module

public import CFSG.Quasithin.Background.E2TwoProofFam
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Cov
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace E2P

theorem subgroupOf_ne_top_of_ne {G : Type} [Group G] {P C : Subgroup G} (hP : P ≤ C)
    (hne : P ≠ C) : P.subgroupOf C ≠ ⊤ := fun h =>
  hne (le_antisymm hP (Subgroup.subgroupOf_eq_top.mp h))

theorem subgroupOf_sup_eq_top {G : Type} [Group G] {P₀ P₁ C : Subgroup G} (h₀ : P₀ ≤ C)
    (h₁ : P₁ ≤ C) (hgen : P₀ ⊔ P₁ = C) : P₀.subgroupOf C ⊔ P₁.subgroupOf C = ⊤ := by
  apply Subgroup.map_injective C.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le h₀,
    Subgroup.map_subgroupOf_eq_of_le h₁, hgen, Subgroup.map_top, Subgroup.range_subtype]

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X}

theorem ASHyp.not_g2
    (hX : ASHyp K T M) {f : ℕ} (h : IsG2 2 f ↥K) : False := by
  obtain ⟨hf, F, hF, hFin, hcp, hK, ⟨e⟩⟩ := Setup.X6.exists_mulEquiv_G2_model h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 F) := finite_modGL
  have hK4 : 4 ≤ Nat.card F := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨h0ne, h1ne, hgen⟩ := Vol2Native.L239.Lie.G2.parabolics_proper_generate (K := F)
  have hP₀C : parabolicSubgroup Tag.G2 F {Vol2Native.L239.Lie.G2.i0} ≤ adjointGroup Tag.G2 F :=
    parabolicSubgroup_le_adjointGroup _ _ _
  have hP₁C : parabolicSubgroup Tag.G2 F {Vol2Native.L239.Lie.G2.i1} ≤ adjointGroup Tag.G2 F :=
    parabolicSubgroup_le_adjointGroup _ _ _
  have hUsyl : IsSylowTwoOf (posUnipotent Tag.G2 F) (adjointGroup Tag.G2 F) :=
    Setup.X6.isSylowTwoOf_iff_isSylowOf.2
      (Setup.X6.unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := F) 2).1
  exact hX.false_of_invPair e (Setup.X6.isSylowTwoOf_subgroupOf_top hUsyl)
    (Subgroup.subgroupOf_mono _ (posUnipotent_le_parabolicSubgroup _))
    (Subgroup.subgroupOf_mono _ (posUnipotent_le_parabolicSubgroup _))
    (subgroupOf_ne_top_of_ne hP₀C h0ne) (subgroupOf_ne_top_of_ne hP₁C h1ne)
    (subgroupOf_sup_eq_top hP₀C hP₁C hgen)
    fun α hα => ⟨Setup.X6.G2_invariant_parabolic hK4 hα _,
      Setup.X6.G2_invariant_parabolic hK4 hα _⟩

theorem ASHyp.not_d4
    (hX : ASHyp K T M) {f : ℕ} (h : Is3D4 2 f ↥K) : False := by
  obtain ⟨hf, F, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := Setup.X6.exists_mulEquiv_triality_model h
  have : Finite (ModGL TwistTag.D4.tag F) := finite_modGL
  obtain ⟨hU, hcov, h₀, h₁, hgen, hi₀, hi₁⟩ :=
    Vol2Native.L239.Lie.D4.triality_named_covers hf σ hK hσ
  have hne : (2 ^ f) ^ 3 + 1 ≠ 2 ^ f + 1 := by
    intro h
    have h1 : (2 ^ f) ^ 3 = 2 ^ f := Nat.add_right_cancel h
    have h2 : 2 ^ f < (2 ^ f) ^ 3 := by
      have hq : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      calc 2 ^ f = (2 ^ f) ^ 1 := (pow_one _).symm
        _ < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  have hinv := Vol2Native.L239.Lie.D4.invariant_of_unequal_covers hcov
    (by rw [hi₀, hi₁]; exact hne)
  exact hX.false_of_invPair e hU (Subgroup.le_normalizer.trans ((hcov _).2 (Or.inl rfl)).le)
    (Subgroup.le_normalizer.trans ((hcov _).2 (Or.inr rfl)).le) h₀ h₁ hgen hinv

theorem ASHyp.not_f4
    (hX : ASHyp K T M) {f : ℕ} (h : Is2F4 f ↥K) : False := by
  obtain ⟨a, F, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ := Setup.X6.exists_mulEquiv_largeRee_model h
  have hK' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have : Finite (ModGL LieType.Ree.ReeTag.F4.tag F) := finite_modGL
  obtain ⟨hU, hcov, hn₀, hn₁, hgen, hi₀, hi₁⟩ :=
    Vol2Native.L239.Lie.F4.largeRee_named_covers a F hK'
  have hq : 2 ≤ Nat.card F := by
    rw [hK']
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hne : Nat.card F + 1 ≠ Nat.card F ^ 2 + 1 := by
    intro h
    have h1 : Nat.card F = Nat.card F ^ 2 := Nat.add_right_cancel h
    nlinarith
  have hinv := Vol2Native.L239.Lie.D4.invariant_of_unequal_covers hcov
    (by rw [hi₀, hi₁]; exact hne)
  exact hX.false_of_invPair e hU (Subgroup.le_normalizer.trans ((hcov _).2 (Or.inl rfl)).le)
    (Subgroup.le_normalizer.trans ((hcov _).2 (Or.inr rfl)).le) hn₀ hn₁ hgen hinv

theorem ASHyp.not_tits
    (hX : ASHyp K T M) (h : IsTits ↥K) : False := by
  obtain ⟨e⟩ := Sporadic.Schreier.Tits.titsModelEquiv ↥K 2 1 h
  obtain ⟨hHt, hNt⟩ := Setup.X6.ne_top_of_card Sporadic.Schreier.Tits.card_titsPointStab
    Sporadic.Schreier.Tits.card_titsLineStab
  exact hX.false_of_invPair e Setup.X6.TitsLat.isSylowTwoOf_flagStab
    Setup.X6.TitsLat.titsFlagStab_le_point Setup.X6.TitsLat.titsFlagStab_le_line hHt hNt
    (Setup.X6.generation_of_overgroup_lattice Sporadic.Schreier.Tits.card_titsPointStab
      Sporadic.Schreier.Tits.card_titsLineStab Setup.X6.TitsLat.titsFlagStab_le_point
      Sporadic.Schreier.Tits.card_titsFlagStab Setup.X6.TitsLat.tits_overgroups)
    fun α hα => Setup.X6.invariant_of_overgroup_lattice Sporadic.Schreier.Tits.card_titsFlagStab
      Sporadic.Schreier.Tits.card_titsPointStab Sporadic.Schreier.Tits.card_titsLineStab
      Setup.X6.TitsLat.titsFlagStab_le_point Setup.X6.TitsLat.titsFlagStab_le_line
      Setup.X6.TitsLat.tits_overgroups hα

theorem e22Char2ExcFam
    : E22Char2ExcFam := by
  intro X _ _ K T M hX h
  rcases h with ⟨f, -, h⟩ | ⟨f, -, h⟩ | ⟨f, -, -, h⟩ | h
  · exact hX.not_g2 h
  · exact hX.not_d4 h
  · exact hX.not_f4 h
  · exact hX.not_tits h

end E2P

end CFSG.Quasithin
