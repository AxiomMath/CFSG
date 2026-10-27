module

public import CFSG.Quasithin.Recognition.GoldschmidtF112SSSp42Lattice
public import CFSG.Assembly.GL83LieDefs
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.Quasithin

open Equiv CFSG.Quasithin.F6.GoldAmS CFSG.QuasithinUnique.Borel252.A6

theorem S6K1_eq : S6K1 = S6G1 ⊓ alternatingGroup (Fin 6) := by
  ext g
  rw [mem_S6K1, Subgroup.mem_inf, mem_S6G1, Equiv.Perm.mem_alternatingGroup]

theorem S6K2_eq : S6K2 = S6G2 ⊓ alternatingGroup (Fin 6) := by
  ext g
  rw [mem_S6K2, Subgroup.mem_inf, mem_S6G2, Equiv.Perm.mem_alternatingGroup]

theorem S6K12_eq : S6K1 ⊓ S6K2 = (S6G1 ⊓ S6G2) ⊓ alternatingGroup (Fin 6) := by
  rw [S6K1_eq, S6K2_eq]
  ext g
  simp only [Subgroup.mem_inf]
  tauto

theorem s6e1_mem_T : s6e1 ∈ S6G1 ⊓ S6G2 := ⟨mem_S6G1.2 rfl, s6e1_mem_G2⟩

theorem sign_s6e1 : Equiv.Perm.sign s6e1 = -1 := Equiv.Perm.sign_swap (by decide)

theorem lattice_S6 (X : Subgroup S6) (hX : S6G1 ⊓ S6G2 ≤ X) :
    X = S6G1 ⊓ S6G2 ∨ X = S6G1 ∨ X = S6G2 ∨ X = ⊤ := by
  have hDT : S6K1 ⊓ S6K2 ≤ S6G1 ⊓ S6G2 := by
    rw [S6K12_eq]
    exact inf_le_left
  have hD : S6K1 ⊓ S6K2 ≤ X ⊓ A6s := le_inf (hDT.trans hX) S6K12_le_A6
  have hT0 : s6e1 ∈ X := hX s6e1_mem_T
  rcases lattice_A6 (X ⊓ A6s) hD inf_le_right with h | h | h | h
  · left
    exact eq_of_inf_alt_eq hT0 s6e1_mem_T sign_s6e1 (h.trans S6K12_eq)
  · right; left
    exact eq_of_inf_alt_eq hT0 (s6e1_mem_T.1) sign_s6e1 (h.trans S6K1_eq)
  · right; right; left
    exact eq_of_inf_alt_eq hT0 (s6e1_mem_T.2) sign_s6e1 (h.trans S6K2_eq)
  · right; right; right
    exact eq_of_inf_alt_eq hT0 (Subgroup.mem_top _) sign_s6e1 (by rw [h]; simp [A6s])

theorem G1_not_normalizes_T :
    ¬ S6G1 ≤ Subgroup.normalizer ((S6G1 ⊓ S6G2 : Subgroup S6) : Set S6) := by
  intro h
  have hg : swap 1 2 ∈ S6G1 := mem_S6G1.2 (by decide)
  have ht : swap 0 1 ∈ S6G1 ⊓ S6G2 := ⟨mem_S6G1.2 (by decide), mem_S6G2.2 (by decide)⟩
  have := (Subgroup.mem_normalizer_iff.1 (h hg) _).1 ht
  have hbad : swap 1 2 * swap 0 1 * (swap 1 2)⁻¹ ∉ S6G1 ⊓ S6G2 := by
    rintro ⟨_, h2⟩
    have := mem_S6G2.1 h2
    revert this
    decide
  exact hbad this

theorem G2_not_normalizes_T :
    ¬ S6G2 ≤ Subgroup.normalizer ((S6G1 ⊓ S6G2 : Subgroup S6) : Set S6) := by
  intro h
  have hg : swap 0 4 * swap 1 5 ∈ S6G2 := mem_S6G2.2 (by decide)
  have ht : swap 0 2 * swap 1 3 ∈ S6G1 ⊓ S6G2 := ⟨mem_S6G1.2 (by decide), mem_S6G2.2 (by decide)⟩
  have := (Subgroup.mem_normalizer_iff.1 (h hg) _).1 ht
  have hbad : (swap 0 4 * swap 1 5) * (swap 0 2 * swap 1 3) * (swap 0 4 * swap 1 5)⁻¹ ∉
      S6G1 ⊓ S6G2 := by
    rintro ⟨h1, _⟩
    have := mem_S6G1.1 h1
    revert this
    decide
  exact hbad this

theorem normalizer_S6T_le :
    Subgroup.normalizer ((S6G1 ⊓ S6G2 : Subgroup S6) : Set S6) ≤ S6G1 ⊓ S6G2 := by
  rcases lattice_S6 _ Subgroup.le_normalizer with h | h | h | h
  · exact h.le
  · exact absurd h.ge G1_not_normalizes_T
  · exact absurd h.ge G2_not_normalizes_T
  · exfalso
    have hN : (S6G1 ⊓ S6G2).Normal := Subgroup.normalizer_eq_top_iff.1 h
    obtain ⟨S, hS⟩ := exists_sylow_S6T
    have hS' : ∀ x ∈ (S : Subgroup S6), x ≠ 1 → ∃ g : S6, g * x * g⁻¹ ∉ (S : Subgroup S6) := by
      rw [hS]
      exact S6T_moved
    have hbot := eq_bot_of_normal_two S hS' (S6G1 ⊓ S6G2) (by rw [← hS]; exact S.isPGroup')
    have := card_S6T
    rw [hbot, Subgroup.card_bot] at this
    omega

theorem S6G1_not_le_G2 : ¬ S6G1 ≤ S6G2 := by
  intro h
  obtain ⟨g, hg1, hg2⟩ : ∃ g : S6, g ∈ S6G1 ∧ g ∉ S6G2 := by decide +kernel
  exact hg2 (h hg1)

theorem S6G2_not_le_G1 : ¬ S6G2 ≤ S6G1 := by
  intro h
  obtain ⟨g, hg2, hg1⟩ : ∃ g : S6, g ∈ S6G2 ∧ g ∉ S6G1 := by decide +kernel
  exact hg1 (h hg2)

theorem T_lt_G1 : S6G1 ⊓ S6G2 < S6G1 :=
  lt_of_le_of_ne inf_le_left fun h => by
    have := card_S6T
    rw [h, card_S6G1] at this
    omega

theorem T_lt_G2 : S6G1 ⊓ S6G2 < S6G2 :=
  lt_of_le_of_ne inf_le_right fun h => by
    have := card_S6T
    rw [h, card_S6G2] at this
    omega

theorem nonempty_mulEquiv_S6_of_isSp42 {W : Type} [Group W] (h : F6.IsSp42 W) :
    Nonempty (W ≃* S6) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by simpa using hcard)
  obtain ⟨e6⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm hcard
  have hbij : Function.Bijective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K) :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
  exact ⟨e.trans ((MulEquiv.ofBijective _ hbij).symm.trans e6)⟩

end CFSG.Quasithin
