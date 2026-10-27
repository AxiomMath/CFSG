module

public import CFSG.Quasithin.Vol2.Ch10SecC3S
public import CFSG.Quasithin.Vol2.Ch10SecC3F
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13
open scoped IsMulCommutative

namespace C3.Om

theorem not_isFFStarOffender_of_tensorPair {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hreal : (tensorPairModel (StatedSL 2 K) (StatedSL 2 K)).RealizesMod H)
    (A : Subgroup (MulAut V)) :
    ¬ IsFFStarOffender (Subgroup.normalizer (H : Set (MulAut V))) A := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  rintro ⟨hAN, hAne, hAel, hmax⟩
  obtain ⟨e, he⟩ := exists_model hreal
  have hV := hmax ⊥ bot_le
  rw [Subgroup.card_bot, one_mul, C3.fixV_bot, Subgroup.card_top] at hV
  have hN : A.map (congrHom e) ≤ norm K := by
    have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut (WM K))) :
          Set (MulAut (WM K))) :=
      Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
    have h4 := (Subgroup.map_mono (f := congrHom e) hAN).trans (le_of_eq h3)
    have h5 := congrArg (fun K' : Subgroup (MulAut (WM K)) => Subgroup.normalizer
      (K' : Set (MulAut (WM K)))) he
    exact h4.trans (le_of_eq h5)
  have hne : A.map (congrHom e) ≠ ⊥ := fun h =>
    hAne ((Subgroup.map_eq_bot_iff_of_injective A (congrHom_injective e)).mp h)
  have hlt := card_mul_card_fixV_lt hn hK hN ((isElemAbelian2_map_congrHom e).mpr hAel) hne
  have h1 : Nat.card ↥(A.map (congrHom e)) = Nat.card ↥A := card_map_congrHom e A
  have h2 : Nat.card ↥(fixV (A.map (congrHom e))) = Nat.card ↥(fixV A) :=
    (congrArg (fun K' : Subgroup (WM K) => Nat.card ↥K') (fixV_map_congrHom e A)).trans
      (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective)
  have key : Nat.card ↥A * Nat.card ↥(fixV A) < Nat.card K ^ 4 := by
    rw [← h1, ← h2]
    exact hlt
  have hcardV : Nat.card V = Nat.card K ^ 4 := by rw [Nat.card_congr e.toEquiv, card_WM]
  omega

end C3.Om

theorem not_concl701FF_of_omegaPlus {G : Type} [Group G] {T L I : Subgroup G}
    [IsMulCommutative ↥(fsuV T I)] {n : ℕ} (h : Row711OmegaPlus T L I n) :
    ¬ Concl701FF T L I := by
  obtain ⟨-, hn, K, _, _, hK, hreal⟩ := h
  rintro ⟨A, hA⟩
  exact C3.Om.not_isFFStarOffender_of_tensorPair hn hK hreal A hA

theorem as_p696_notFF_holds : AS_p696_notFF := by
  intro G _ _ T L I _ _ _ hrow
  rcases hrow with ⟨n, h⟩ | h
  · exact not_concl701FF_of_omegaPlus h
  · exact C3.not_concl701FF_of_l3Wreath h

end CFSG.Quasithin.Vol2.Ch10
