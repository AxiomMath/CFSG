module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoOffender24

public section

namespace CFSG.ASVolI.AppH

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1
  CFSG.Monster.Code

theorem chain_shape24 {V : Type*} [CommGroup V] [Finite V] (e : V ≃* W11)
    {A : Subgroup (MulAut V)} (hAR : A.map (congrHom e) ≤ rhoM24.range)
    (hA2 : IsElemAbelian2 A) (hA1 : A ≠ ⊥) (hF : rkIdx (fixV A) ≤ rk ↥A + 1) :
    ∃ (g : ↥AutPerm) (l : List T24s2.Elem), IndepList l ∧ l.length = 4 ∧
      (∀ s ∈ l, fixesOff24 s = true) ∧ IsChainSub (chainAut e rhoM24 phi24 g) l A := by
  haveI : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) fun _ _ h => MulEquiv.ext (congrFun h)
  have hpg : IsPGroup 2 A := isPGroup_two_of_sq_eq_one fun a => Subtype.ext (hA2.2 a a.2)
  have hcard : Nat.card A = 2 ^ rk ↥A := card_eq_two_pow_of_isPGroup hpg
  have hk6 : rk ↥A ≤ 6 := by
    by_contra hk
    push Not at hk
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (G := A) (n := 7)
      (by rw [hcard]; exact Nat.pow_dvd_pow 2 (by omega))
    set B := K.map A.subtype
    have hBA : B ≤ A := Subgroup.map_subtype_le K
    have hB : Nat.card B = 2 ^ 7 := by
      rw [Subgroup.card_map_of_injective A.subtype_injective, hK]
    have hBe : IsElemAbelian2 B :=
      ⟨fun a ha b hb => hA2.1 a (hBA ha) b (hBA hb), fun a ha => hA2.2 a (hBA ha)⟩
    obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel rhoM24 (rho11_injective _ _) phi24
      (T24s2.toSub_injective _ _) card_T24s2 (fun _ h1 h2 => T24s2.mem_invols h1 h2)
      (greedyOff24 (k := 7) le_rfl) e
      ((Subgroup.map_mono (f := congrHom e) hBA).trans hAR) hBe hB
    have hlen : l.length = 7 := by
      have hc := (card_of_chainSub hchain (chainAut24_injective e g) hind).symm.trans hB
      exact Nat.pow_right_injective (le_refl 2) hc
    have hle6 : l.length ≤ 6 := by
      rw [predOff24] at hpred
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
      exact hpred.1
    omega
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel rhoM24 (rho11_injective _ _) phi24
    (T24s2.toSub_injective _ _) card_T24s2 (fun _ h1 h2 => T24s2.mem_invols h1 h2)
    (greedyOff24 (k := rk ↥A) (by omega)) e hAR hA2 hcard
  have hlen : l.length = rk ↥A := by
    have hc := (card_of_chainSub hchain (chainAut24_injective e g) hind).symm.trans hcard
    exact Nat.pow_right_injective (le_refl 2) hc
  have hinv : ∀ a ∈ l, a * a = 1 := (isCommInvol_of_indepList hind).1
  have hd : 11 - Nat.log 2 (fixMasks 11 act24s2 l).length ≤ l.length + 1 := by
    have h1 : rkIdx (fixV A) = 11 - Nat.log 2 (fixMasks 11 act24s2 l).length :=
      (MaskCoords.ofEquiv (twistEquiv e rhoM24 g)).rkIdx_of_card
        (card_fixV (chainAct24 e g) hchain)
    rw [h1] at hF
    rwa [← hlen] at hF
  rw [predOff24, fixMasks24_eq hinv] at hpred
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, bne_iff_ne, ne_eq, beq_iff_eq] at hpred
  have hk0 : l.length ≠ 0 := by
    intro h0
    apply hA1
    have hcA : Nat.card A = 1 := by rw [hcard, ← hlen, h0, pow_zero]
    exact Subgroup.card_eq_one.1 hcA
  have hlast : l.length = 4 ∧ l.all fixesOff24 = true :=
    hpred.2.elim
      (fun hleft => hleft.elim (fun h0 => absurd h0 hk0) (fun hmid => absurd hd hmid))
      id
  obtain ⟨h4, hall⟩ := hlast
  exact ⟨g, l, hind, h4, fun s hs => List.all_eq_true.1 hall s hs, hchain⟩

end CFSG.ASVolI.AppH

