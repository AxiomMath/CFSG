module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Frame
import CFSG.Quasithin.Recognition.Stroth.Str83G4Sec5M4

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender

theorem exists_galoisField_orderOf_eq {n : ℕ} (hn : n ≠ 0) :
    ∃ ζ : GaloisField 2 n, orderOf ζ = 2 ^ n - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField 2 n)ˣ)
  exact ⟨g, by rw [orderOf_units, hg, Nat.card_units, GaloisField.card 2 n hn]⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_zmod_pow_neg_val_mul_eq {N : ℕ} [NeZero N] {d₁ d₂ δ : G} (hd₁ : d₁ ^ N = 1)
    (hcomm : Commute d₁ d₂) (hδ : δ ∈ zpowers d₁) :
    ∃ m : ZMod N, d₁ ^ (-m).val * d₂ = d₂ * δ⁻¹ := by
  obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hδ)
  refine ⟨(j : ZMod N), ?_⟩
  have hdvd : N ∣ (-(j : ZMod N)).val + j := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id, neg_add_cancel]
  obtain ⟨k, hk⟩ := hdvd
  have h1 : d₁ ^ (-(j : ZMod N)).val * d₁ ^ j = 1 := by
    rw [← pow_add, hk, pow_mul, hd₁, one_pow]
  rw [eq_inv_of_mul_eq_one_left h1]
  exact ((hcomm.pow_left j).inv_left).eq

theorem hallTwoPrime_sup_of_data {L1 L2 S : Subgroup G} (d : Str83G4Data L1 L2 S)
    (hB : bigB L1 L2 S ≤ normalizer (S : Set G)) {k : ℕ} (hS : Nat.card S = 2 ^ k) :
    RonanF13.HallTwoPrime (d.D1 ⊔ d.D2) (bigB L1 L2 S) := by
  have hX : d.D1 ⊔ d.D2 ≤ bigB L1 L2 S := by
    rw [d.hBsplit]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  refine ⟨hX, str83G4Data_odd_card_sup d, ?_⟩
  have hsup : (d.D1 ⊔ d.D2) ⊔ S = bigB L1 L2 S := by
    rw [d.hBsplit, sup_assoc S d.D1 d.D2, sup_comm S]
  have h1 := C5.card_sup_mul_card_inf_of_le_normalizer (hX.trans hB)
  have h2 := relIndex_mul_card (H := d.D1 ⊔ d.D2) (K := (d.D1 ⊔ d.D2) ⊔ S)
  rw [inf_sup_self] at h2
  rw [← h2, hS] at h1
  have h3 : (d.D1 ⊔ d.D2).relIndex ((d.D1 ⊔ d.D2) ⊔ S) * Nat.card ↥((d.D1 ⊔ d.D2) ⊓ S) =
      2 ^ k := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(d.D1 ⊔ d.D2)))
    rw [← h1]
    ring
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ h3)
  exact ⟨j, by rw [← hsup]; exact hj⟩

theorem exists_lift_right_of_data {L1 L2 S : Subgroup G} {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) {x : G} (hx : x ∈ d.D1) :
    ∃ δ ∈ d.D2, ∀ l ∈ L2, (x * δ⁻¹) * l * (x * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L2 := by
  obtain ⟨hF, -, ha, -, hL2, -⟩ := hfr
  have hF' : F112HypW L2 L1 S := F112HypW.symm hF
  have hR' : Hyp111R L2 L1 S := Hyp111R.of_hyp111 rankOneListedFacts hF'.1
  have hBt2 : BenderType (oTwoQuot ↥L2) (2 * a + 1) 1 1 :=
    BenderType.linear (2 * a + 1) (by omega) (Classical.choice hL2)
  have hD1B : d.D1 ≤ bigB L2 L1 S := by
    rw [bigB_comm]
    exact d.hD1hall.1.trans (le_sup_left.trans le_sup_left)
  exact exists_commutator_lift hF'.1 hR' d.hD2hall d.hD2sup hD1B
    (fun y hy z hz => (d.hcomm z hz y hy).symm) hBt2
    (fun Q t ht htQ σ hσQ hσD => BenderType.aut_eq_conj_cartan_linear hBt2 Q ht htQ σ hσQ hσD) hx

end CFSG.Quasithin.Stroth.G5

end
