module

public import CFSG.Quasithin.EmptyFaithful.SBd8Mod
import CFSG.Quasithin.EmptyFaithful.SBc6Sl2
import CFSG.Quasithin.EmptyFaithful.SzN2Lin

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

namespace Psl2

theorem one_le_of_card_two_pow {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := Finite.one_lt_card_iff_nontrivial.2 (inferInstance : Nontrivial F)
    simp [hF] at this
  · exact hn

theorem isPSL_of_statedSL {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {X : Type} [Group X]
    (e : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F)) : IsPSL 2 2 n X := by
  have hchar : CharP F 2 := CFSG.Quasithin.R3c.charP_two_of_natCard_eq_two_pow hF
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, inferInstance, inferInstance, hF,
    ⟨e.trans ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm.trans
      CFSG.QuasithinUnique.Vol2Native.A312L.sl2EquivStatedProj)⟩⟩
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega

section Borel

variable {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {U K : Subgroup X}

theorem eq_normalizer_of_isPSL {n : ℕ} (h : IsPSL 2 2 n X) (d : OvgData X A U K) :
    K = Subgroup.normalizer (U : Set X) := by
  have hKle : K ≤ Subgroup.normalizer (U : Set X) := by
    rcases SBc6.overgroup_of_psl h d.U_syl d.U_le with h1 | h1
    · exact absurd h1 d.K_ne
    · exact h1
  have hNne : Subgroup.normalizer (U : Set X) ≠ ⊤ := fun h1 =>
    SBc6.not_normal_sylow_of_psl h d.U_syl (le_of_eq h1.symm)
  have hNinv : ∀ α ∈ A, (Subgroup.normalizer (U : Set X)).map α.toMonoidHom =
      Subgroup.normalizer (U : Set X) := by
    intro α hα
    rw [Subgroup.map_equiv_normalizer_eq U α, d.A_U α hα]
  exact le_antisymm hKle (d.K_max _ hKle hNne hNinv)

end Borel

section Even

open CFSG.Quasithin.SBc5SL2 CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem Tplus_le_upperTriangular {F : Type} [Field F] : Tplus F ≤ upperTriangular 2 F := by
  intro b hb i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  exact hb

theorem even_of_three_dvd_normalizer {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {X : Type} [Group X] [Finite X] (e : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F))
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    (h3 : 3 ∣ Nat.card ↥(Subgroup.normalizer (U : Set X))) : Even n := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hn : 1 ≤ n := one_le_of_card_two_pow hF
  have hchar : CharP F 2 := CFSG.Quasithin.R3c.charP_two_of_natCard_eq_two_pow hF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.normalizer (U : Set X))) 3 h3
  let φ : SL2 F ≃* X :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).trans e.symm
  let Q : Subgroup (SL2 F) := U.map φ.symm.toMonoidHom
  have hQ : IsSylowTwoOf Q ⊤ := by
    have := isSylowTwoOf_map' hU φ.symm.toMonoidHom
    rwa [Subgroup.map_top_of_surjective _ φ.symm.surjective] at this
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj (isSylowTwoOf_Uplus hn hF) hQ
  have hz : orderOf (φ.symm (y : X)) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy]
  have hzN : φ.symm (y : X) ∈ Subgroup.normalizer (Q : Set (SL2 F)) :=
    (SBd3T.map_mem_normalizer_iff φ.symm.toMonoidHom φ.symm.injective U y).2 y.2
  have hzT : g⁻¹ * φ.symm (y : X) * g ∈ Tplus F := by
    rw [← normalizer_Uplus]
    have h1 : Subgroup.normalizer (Q : Set (SL2 F)) =
        B6.conjSub g (Subgroup.normalizer (Uplus F : Set (SL2 F))) := by
      rw [hg]
      exact (Subgroup.map_equiv_normalizer_eq (Uplus F) (MulAut.conj g)).symm
    rw [h1, B6.mem_conjSub] at hzN
    exact hzN
  have hord : orderOf (g⁻¹ * φ.symm (y : X) * g) = 3 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) (φ.symm (y : X))
    rw [MulAut.conj_apply, inv_inv] at this
    rw [this, hz]
  exact SzN2.orderOf_ne_three_of_mem_upperTriangular ⟨n, hF⟩
    (by rw [hF]; exact SzN2.not_three_dvd_two_pow_sub_one hodd) (Tplus_le_upperTriangular hzT) hord

end Even

end Psl2

variable {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {U K : Subgroup X}

theorem famSL2 (d : OvgData X A U K) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (e : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F)) :
    (∃ m : ℕ, Even m ∧ IsPSL 2 2 m X) ∧ K = Subgroup.normalizer (U : Set X) := by
  have hn1 : 1 ≤ n := Psl2.one_le_of_card_two_pow hF
  have hn2 : 2 ≤ n := by
    by_contra h
    obtain rfl : n = 1 := by omega
    apply SBc3.false_of_card_dvd_six d.quasi
    have hX : Nat.card X = 6 := by
      rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow hF]
      norm_num
    rw [hX]
  have hPSL : IsPSL 2 2 n X := Psl2.isPSL_of_statedSL hn2 hF e
  have hKN : K = Subgroup.normalizer (U : Set X) := Psl2.eq_normalizer_of_isPSL hPSL d
  refine ⟨⟨n, ?_, hPSL⟩, hKN⟩
  exact Psl2.even_of_three_dvd_normalizer hF e d.U_syl (hKN ▸ d.three_dvd)

end SBd8

end CFSG.Quasithin
