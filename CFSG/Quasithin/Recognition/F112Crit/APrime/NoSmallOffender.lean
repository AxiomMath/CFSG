module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.NoSmallOffenderSz
public import CFSG.Quasithin.Recognition.F112Crit.APrime.NoSmallOffenderU3
public import CFSG.Quasithin.Recognition.F112Crit.APrime.SuzukiGen

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Quasithin

theorem two_mul_card_lt_index_fixV_sz
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    {X L : Subgroup (MulAut V)} (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hperf : Group.IsPerfect ↥L) (hZ : Odd (Nat.card (Subgroup.center ↥L)))
    (hC : X ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L)
    {a : ℕ} (ha : 1 ≤ a) (α : ↥L ⧸ Subgroup.center ↥L ≃* CFSG.Open.Sz a)
    {A : Subgroup (MulAut V)} (hAX : A ≤ X) (hA : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    2 * Nat.card A < (fixV A).index :=
  two_mul_card_lt_index_fixV_sz_of
    (fun _ _ _ _ h => suzuki_exists_closure_three_involutions h)
    (fun _ _ _ _ h => suzuki_exists_sup_conj_eq_top h)
    (fun _ _ _ _ h => suzuki_exists_prime_dvd_card h)
    hV hLX hXL hperf hZ hC ha α hAX hA hAe

theorem two_mul_card_lt_index_fixV
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    {X L : Subgroup (MulAut V)} (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hperf : Group.IsPerfect ↥L) (hZ : Odd (Nat.card (Subgroup.center ↥L)))
    (hC : X ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L)
    (hLZ : (∃ a : ℕ, 1 ≤ a ∧ Nonempty (↥L ⧸ Subgroup.center ↥L ≃* CFSG.Open.Sz a)) ∨
      (∃ f : ℕ, 2 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ f) ^ 2 ∧
        Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
          CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ f) F))))
    {A : Subgroup (MulAut V)} (hAX : A ≤ X) (hA : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    2 * Nat.card A < (fixV A).index := by
  rcases hLZ with ⟨a, ha, ⟨α⟩⟩ | ⟨f, hf, F, _, _, hF, ⟨α⟩⟩
  · exact two_mul_card_lt_index_fixV_sz hV hLX hXL hperf hZ hC ha α hAX hA hAe
  · exact two_mul_card_lt_index_fixV_psu3 hV hLX hXL hperf hZ hC hf hF α hAX hA hAe

end CFSG.Quasithin.F112Crit.APrime

end
