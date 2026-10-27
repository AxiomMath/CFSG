module

public import CFSG.Quasithin.MS93.S36SpESp
public import CFSG.Quasithin.MS93.S36SpEType
public import CFSG.Quasithin.MS93.S36SpECrd
public import CFSG.Quasithin.MS93.S36SpEHat

public section

namespace CFSG.Quasithin.MS93.S36E

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.VolI
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {S : Type} [CommGroup S] [Finite S]

theorem modLemma
    (h14 : MS14AS) (hS2 : ∀ s : S, s ^ 2 = 1) {X K E : Subgroup (MulAut S)} (hFF : FFHyp X K)
    (hEX : E ≤ X) (hE : IsElemAbelian2 E) {k : ℕ} (hk : 1 ≤ k)
    (hcount : 2 ^ k * Nat.card S ≤ Nat.card E * Nat.card (fixV E))
    (hE3 : Nat.card E ≤ (2 ^ k) ^ 3)
    (htype : (k = 1 ∧ Nat.card (↥K ⧸ Subgroup.center ↥K) = 360) ∨
      (2 ≤ k ∧ Nat.card (↥K ⧸ Subgroup.center ↥K) = ordBC 2 (2 ^ k)))
    (hkey : 2 ≤ k → E ≤ K) :
    Nat.card S = (2 ^ k) ^ 2 * Nat.card (fixV E) ∧ Nat.card E = (2 ^ k) ^ 3 ∧
      ∃ c : S, c ≠ 1 ∧ ∃ H : Subgroup S, H ≠ ⊤ ∧ ∀ s ∉ H, ∃ e ∈ E, e s = s * c := by
  have hEp : IsPGroup 2 E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 _ e.2)⟩
  obtain ⟨-, -, hcases, -⟩ := h14 S hS2 X K hFF
  have h360 : ∀ {n : ℕ}, 1 ≤ n → 2 ≤ k → ordBC 2 (2 ^ k) ≠ 360 := fun _ _ =>
    (S32.ordBC_two_ne (by omega)).2.1
  rcases hcases with hSL | hhat | hsp | hG2
  ·
    obtain ⟨n, F, iF, fF, -, hcard, ⟨eK⟩, -, -⟩ := hSL
    obtain ⟨hn, -, hc⟩ := isPSL_quot_of_equiv_statedSL_three hcard eK.symm
    rcases htype with ⟨-, h⟩ | ⟨hk2, h⟩
    · exact absurd (hc.symm.trans h) (S32.ordA_two_ne_360 hn)
    · exact absurd (hc.symm.trans h) (ordA_two_ne_ordBC_two hk2)
  ·
    have hc : Nat.card (↥K ⧸ Subgroup.center ↥K) = 360 := card_quot_of_isHat hhat.2.1
    rcases htype with ⟨rfl, -⟩ | ⟨hk2, h⟩
    · exfalso
      exact false_of_hat hS2 hFF.le_normalizer hEX hE (by simpa using hcount)
        (by simpa using hE3) hhat
    · exact absurd (h.symm.trans hc) (h360 le_rfl hk2)
  · rcases hsp with ⟨n, hn2, F, iF, fF, hcard, π, hπ⟩ | ⟨π, hπ⟩
    ·
      have hc : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordBC 2 (2 ^ n) :=
        card_quot_of_equiv_statedSp hcard hn2 (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ)
      rcases htype with ⟨rfl, h⟩ | ⟨hk2, h⟩
      · exact absurd (hc.symm.trans h) (S32.ordBC_two_ne (by omega)).2.1
      · have hnk : n = k := eq_of_ordBC_two_eq (by omega) (by omega) (hc.symm.trans h)
        subst hnk
        have : CharP F 2 := FFC.charP_two_of_card_pow hcard
        obtain ⟨φ, θ, hθ⟩ := coord_of_natSp4 hπ
        obtain ⟨h1, h2, h3⟩ := offender_coord φ θ hθ (hkey hk2) hEp (by rwa [hcard])
          (by rwa [hcard])
        rw [hcard] at h1 h2
        exact ⟨h1, h2, h3⟩
    ·
      have hc : Nat.card (↥K ⧸ Subgroup.center ↥K) = 360 :=
        card_quot_of_equiv_alt6 (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ)
      rcases htype with ⟨rfl, -⟩ | ⟨hk2, h⟩
      · obtain ⟨φ, θ, hθ⟩ := coord_of_altDn hπ hFF.le_normalizer
        have hF : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
        obtain ⟨h1, h2, h3⟩ := offender_coord φ θ hθ hEX hEp (by rw [hF]; simpa using hcount)
          (by rw [hF]; simpa using hE3)
        rw [hF] at h1 h2
        exact ⟨by simpa using h1, by simpa using h2, h3⟩
      · exact absurd (h.symm.trans hc) (h360 le_rfl hk2)
  ·
    rcases hG2 with ⟨n, hn2, F, iF, fF, hcard, π, hπ⟩ | ⟨⟨F, iF, fF, hcard, π, hπ⟩, -⟩
    · have : CharP F 2 := FFC.charP_two_of_card_pow hcard
      have hc : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordG2 (2 ^ n) :=
        card_quot_of_equiv_quasithinG2 hcard hn2
          (FFC.equivOfRealizes (FFC.zornQ_faithful _ le_rfl) hπ)
      rcases htype with ⟨-, h⟩ | ⟨hk2, h⟩
      · exact absurd (hc.symm.trans h) (S32.ordG2_ne (by omega)).2.1
      · exact absurd (hc.symm.trans h) (ordG2_ne_ordBC_two (by omega) (by omega))
    · have hcard' : Nat.card F = 2 := by rw [hcard]; norm_num
      have : CharP F 2 := FFC.charP_two_of_card_pow hcard
      have hc : Nat.card (↥K ⧸ Subgroup.center ↥K) = 6048 :=
        (card_quot_of_equiv_g2Derived hcard'
          (FFC.equivOfRealizes (FFC.zornQ_faithful _ (Subgroup.commutator_le_self _)) hπ)).2
      rcases htype with ⟨-, h⟩ | ⟨hk2, h⟩
      · rw [hc] at h
        norm_num at h
      · exact absurd (h.symm.trans hc) (S32.ordBC_two_ne (by omega)).2.2

end CFSG.Quasithin.MS93.S36E
